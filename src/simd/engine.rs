use crate::{GoLEngine, Pattern, PatternFormat, Topology};
use anyhow::{Result, anyhow};
use num_bigint::BigInt;

/// A fast, SIMD-optimized engine for Conway's Game of Life that uses bitwise operations
/// for efficient cell state updates. Its performance is pattern-oblivious.
///
/// # Limitations
///
/// - Only supports torus topology (wrapping boundaries)
/// - Requires patterns with `size_log2` of at least 7 (128×128 cells)
///
/// # Example
///
/// ```rust
/// use gol_engines::{GoLEngine, Pattern, PatternFormat, SIMDEngine, Topology};
///
/// // Load a 16x16 pattern
/// let pattern = Pattern::random(4, None).unwrap();
/// let mut expanded_pattern = pattern.clone();
/// expanded_pattern.expand(7); // Expand to at least 128×128
///
/// // Create the SIMD engine
/// let mut engine = SIMDEngine::new(1, 1);
/// engine.load_pattern(&expanded_pattern, Topology::Torus).unwrap();
///
/// // Run for 2^10 = 1024 generations
/// engine.update(10);
///
/// // Get the current state
/// let result = engine.current_state();
/// ```
pub struct SIMDEngine {
    /// The packed cell data, where each bit represents a cell and 64 cells are stored in each u64
    data: Vec<u64>,
    /// Reusable double-buffer for the next generation
    scratch: Vec<u64>,
    /// The side length of the square grid (must be a power of 2)
    n: usize,
    /// The memory limit in MiB
    mem_limit_mib: u32,
}

#[derive(Clone, Copy)]
enum SimdBackend {
    Scalar,
    #[cfg(target_arch = "x86_64")]
    Avx2,
    #[cfg(target_arch = "x86_64")]
    Avx512,
}

impl SIMDEngine {
    const CELLS_IN_CHUNK: usize = 64;

    #[inline]
    fn select_backend(w: usize) -> SimdBackend {
        #[cfg(target_arch = "x86_64")]
        {
            if w >= 8 && std::arch::is_x86_feature_detected!("avx512f") {
                return SimdBackend::Avx512;
            }
            if w >= 4 && std::arch::is_x86_feature_detected!("avx2") {
                return SimdBackend::Avx2;
            }
        }
        let _ = w;
        SimdBackend::Scalar
    }

    #[inline(always)]
    fn step_word(
        prev_l: u64,
        prev_c: u64,
        prev_r: u64,
        curr_l: u64,
        curr_c: u64,
        curr_r: u64,
        next_l: u64,
        next_c: u64,
        next_r: u64,
    ) -> u64 {
        const SHIFT: u32 = 63;
        let b = prev_c;
        let a = (b << 1) | (prev_l >> SHIFT);
        let c = (b >> 1) | (prev_r << SHIFT);

        let i = curr_c;
        let h = (i << 1) | (curr_l >> SHIFT);
        let d = (i >> 1) | (curr_r << SHIFT);

        let f = next_c;
        let g = (f << 1) | (next_l >> SHIFT);
        let e = (f >> 1) | (next_r << SHIFT);

        // Full adder on (a, b, c)
        let s0 = a ^ b ^ c;
        let c0 = (a & b) | (c & (a ^ b));
        // Full adder on (g, f, e)
        let s1 = g ^ f ^ e;
        let c1 = (g & f) | (e & (g ^ f));
        // Half adder on (h, d)
        let s2 = h ^ d;
        let c2 = h & d;
        // Full adder on weight-1 bits (s0, s1, s2)
        let bit0 = s0 ^ s1 ^ s2;
        let c3 = (s0 & s1) | (s2 & (s0 ^ s1));
        // Exactly one of (c0, c1, c2, c3) is 1
        let u = c0 ^ c1 ^ c2;
        let v = (c0 & c1) | (c2 & (c0 ^ c1));
        let one_carry = !v & (u ^ c3);
        (i | bit0) & one_carry
    }

    fn update_row_scalar(row_prev: &[u64], row_curr: &[u64], row_next: &[u64], dst: &mut [u64]) {
        let w = row_prev.len();
        dst[0] = Self::step_word(
            row_prev[w - 1],
            row_prev[0],
            row_prev[1],
            row_curr[w - 1],
            row_curr[0],
            row_curr[1],
            row_next[w - 1],
            row_next[0],
            row_next[1],
        );
        for x in 1..w - 1 {
            dst[x] = Self::step_word(
                row_prev[x - 1],
                row_prev[x],
                row_prev[x + 1],
                row_curr[x - 1],
                row_curr[x],
                row_curr[x + 1],
                row_next[x - 1],
                row_next[x],
                row_next[x + 1],
            );
        }
        dst[w - 1] = Self::step_word(
            row_prev[w - 2],
            row_prev[w - 1],
            row_prev[0],
            row_curr[w - 2],
            row_curr[w - 1],
            row_curr[0],
            row_next[w - 2],
            row_next[w - 1],
            row_next[0],
        );
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "avx2")]
    unsafe fn update_row_avx2(
        row_prev: &[u64],
        row_curr: &[u64],
        row_next: &[u64],
        dst: &mut [u64],
    ) {
        use std::arch::x86_64::*;
        let w = row_prev.len();
        debug_assert!(w >= 4 && w.is_multiple_of(4));

        #[inline(always)]
        unsafe fn load_neighbors(row: &[u64], x: usize, w: usize) -> (__m256i, __m256i, __m256i) {
            unsafe {
                let ptr = row.as_ptr();
                let mid = _mm256_loadu_si256(ptr.add(x).cast());
                let left_src = if x > 0 {
                    _mm256_loadu_si256(ptr.add(x - 1).cast())
                } else {
                    let tmp = [*row.get_unchecked(w - 1), *ptr, *ptr.add(1), *ptr.add(2)];
                    _mm256_loadu_si256(tmp.as_ptr().cast())
                };
                let right_src = if x + 4 < w {
                    _mm256_loadu_si256(ptr.add(x + 1).cast())
                } else {
                    let tmp = [
                        *ptr.add(x + 1),
                        *ptr.add(x + 2),
                        *ptr.add(x + 3),
                        *row.get_unchecked(0),
                    ];
                    _mm256_loadu_si256(tmp.as_ptr().cast())
                };
                let left = _mm256_or_si256(_mm256_slli_epi64(mid, 1), _mm256_srli_epi64(left_src, 63));
                let right =
                    _mm256_or_si256(_mm256_srli_epi64(mid, 1), _mm256_slli_epi64(right_src, 63));
                (left, mid, right)
            }
        }

        let mut x = 0;
        while x < w {
            unsafe {
                let (a, b, c) = load_neighbors(row_prev, x, w);
                let (h, i, d) = load_neighbors(row_curr, x, w);
                let (g, f, e) = load_neighbors(row_next, x, w);

                let ab_xor = _mm256_xor_si256(a, b);
                let s0 = _mm256_xor_si256(ab_xor, c);
                let c0 = _mm256_or_si256(_mm256_and_si256(a, b), _mm256_and_si256(c, ab_xor));

                let gf_xor = _mm256_xor_si256(g, f);
                let s1 = _mm256_xor_si256(gf_xor, e);
                let c1 = _mm256_or_si256(_mm256_and_si256(g, f), _mm256_and_si256(e, gf_xor));

                let s2 = _mm256_xor_si256(h, d);
                let c2 = _mm256_and_si256(h, d);

                let s01_xor = _mm256_xor_si256(s0, s1);
                let bit0 = _mm256_xor_si256(s01_xor, s2);
                let c3 = _mm256_or_si256(_mm256_and_si256(s0, s1), _mm256_and_si256(s2, s01_xor));

                let c01_xor = _mm256_xor_si256(c0, c1);
                let u = _mm256_xor_si256(c01_xor, c2);
                let v = _mm256_or_si256(_mm256_and_si256(c0, c1), _mm256_and_si256(c2, c01_xor));

                let one_carry = _mm256_andnot_si256(v, _mm256_xor_si256(u, c3));
                let res = _mm256_and_si256(_mm256_or_si256(i, bit0), one_carry);
                _mm256_storeu_si256(dst.as_mut_ptr().add(x).cast(), res);
            }
            x += 4;
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "avx512f")]
    unsafe fn update_row_avx512(
        row_prev: &[u64],
        row_curr: &[u64],
        row_next: &[u64],
        dst: &mut [u64],
    ) {
        use std::arch::x86_64::*;
        let w = row_prev.len();
        debug_assert!(w >= 8 && w.is_multiple_of(8));

        #[inline(always)]
        unsafe fn load_neighbors(row: &[u64], x: usize, w: usize) -> (__m512i, __m512i, __m512i) {
            unsafe {
                let ptr = row.as_ptr();
                let mid = _mm512_loadu_si512(ptr.add(x).cast());
                let left_src = if x > 0 {
                    _mm512_loadu_si512(ptr.add(x - 1).cast())
                } else {
                    let mut tmp = [0u64; 8];
                    tmp[0] = *row.get_unchecked(w - 1);
                    std::ptr::copy_nonoverlapping(ptr, tmp.as_mut_ptr().add(1), 7);
                    _mm512_loadu_si512(tmp.as_ptr().cast())
                };
                let right_src = if x + 8 < w {
                    _mm512_loadu_si512(ptr.add(x + 1).cast())
                } else {
                    let mut tmp = [0u64; 8];
                    std::ptr::copy_nonoverlapping(ptr.add(x + 1), tmp.as_mut_ptr(), 7);
                    tmp[7] = *row.get_unchecked(0);
                    _mm512_loadu_si512(tmp.as_ptr().cast())
                };
                let left = _mm512_or_si512(_mm512_slli_epi64(mid, 1), _mm512_srli_epi64(left_src, 63));
                let right =
                    _mm512_or_si512(_mm512_srli_epi64(mid, 1), _mm512_slli_epi64(right_src, 63));
                (left, mid, right)
            }
        }

        let mut x = 0;
        while x < w {
            unsafe {
                let (a, b, c) = load_neighbors(row_prev, x, w);
                let (h, i, d) = load_neighbors(row_curr, x, w);
                let (g, f, e) = load_neighbors(row_next, x, w);

                // Full adder: sum = A^B^C (0x96), carry = maj(A,B,C) (0xE8)
                let s0 = _mm512_ternarylogic_epi64(a, b, c, 0x96);
                let c0 = _mm512_ternarylogic_epi64(a, b, c, 0xE8);

                let s1 = _mm512_ternarylogic_epi64(g, f, e, 0x96);
                let c1 = _mm512_ternarylogic_epi64(g, f, e, 0xE8);

                let s2 = _mm512_xor_si512(h, d);
                let c2 = _mm512_and_si512(h, d);

                let bit0 = _mm512_ternarylogic_epi64(s0, s1, s2, 0x96);
                let c3 = _mm512_ternarylogic_epi64(s0, s1, s2, 0xE8);

                let u = _mm512_ternarylogic_epi64(c0, c1, c2, 0x96);
                let v = _mm512_ternarylogic_epi64(c0, c1, c2, 0xE8);

                // (!v) & (u ^ c3) -> imm8 = 0x06
                let one_carry = _mm512_ternarylogic_epi64(v, u, c3, 0x06);
                // (i | bit0) & one_carry -> imm8 = 0xA8
                let res = _mm512_ternarylogic_epi64(i, bit0, one_carry, 0xA8);
                _mm512_storeu_si512(dst.as_mut_ptr().add(x).cast(), res);
            }
            x += 8;
        }
    }

    fn update_inner(&mut self, backend: SimdBackend) {
        let w = self.n >> Self::CELLS_IN_CHUNK.ilog2();
        let h = self.n;
        let src = self.data.as_slice();
        let dst_buf = self.scratch.as_mut_slice();

        for y in 0..h {
            let y_prev = if y == 0 { h - 1 } else { y - 1 };
            let y_next = if y + 1 == h { 0 } else { y + 1 };
            let row_prev = &src[y_prev * w..(y_prev + 1) * w];
            let row_curr = &src[y * w..(y + 1) * w];
            let row_next = &src[y_next * w..(y_next + 1) * w];
            let dst = &mut dst_buf[y * w..(y + 1) * w];
            match backend {
                SimdBackend::Scalar => Self::update_row_scalar(row_prev, row_curr, row_next, dst),
                #[cfg(target_arch = "x86_64")]
                SimdBackend::Avx2 => unsafe {
                    Self::update_row_avx2(row_prev, row_curr, row_next, dst);
                },
                #[cfg(target_arch = "x86_64")]
                SimdBackend::Avx512 => unsafe {
                    Self::update_row_avx512(row_prev, row_curr, row_next, dst);
                },
            }
        }
        std::mem::swap(&mut self.data, &mut self.scratch);
    }
}

impl GoLEngine for SIMDEngine {
    fn new(mem_limit_mib: u32, _threads_cnt: usize) -> Self {
        let len = 128 * 128 / Self::CELLS_IN_CHUNK;
        Self {
            data: vec![0; len],
            scratch: vec![0; len],
            n: 128,
            mem_limit_mib,
        }
    }

    fn load_pattern(&mut self, pattern: &Pattern, topology: Topology) -> Result<()> {
        if topology != Topology::Torus {
            return Err(anyhow!("Only torus topology is supported by SIMDEngine"));
        }
        if pattern.get_size_log2() < 7 {
            return Err(anyhow!("Pattern is too small for SIMDEngine"));
        }

        // `mem_limit_mib` must be at least twice the size of the pattern
        // to fit the conversion/scratch buffer and the pattern itself
        if (BigInt::from(self.mem_limit_mib) << 20)
            < (BigInt::from(2) << (pattern.get_size_log2() * 2)) / 8
        {
            return Err(anyhow!("Pattern is too large for SIMDEngine"));
        }

        let packed_cells = pattern.to_format(PatternFormat::PackedCells)?;
        let n = 1 << pattern.get_size_log2();
        let words = n * n / Self::CELLS_IN_CHUNK;
        let mut data = Vec::with_capacity(words);
        for chunk in packed_cells.chunks_exact(8) {
            data.push(u64::from_le_bytes(chunk.try_into().unwrap()));
        }

        self.data = data;
        self.scratch.resize(words, 0);
        self.n = n;
        Ok(())
    }

    fn current_state(&self) -> Pattern {
        let packed_cells = self
            .data
            .iter()
            .flat_map(|&chunk| chunk.to_le_bytes())
            .collect::<Vec<u8>>();
        Pattern::from_format(PatternFormat::PackedCells, &packed_cells)
            .expect("A bug in SIMDEngine")
    }

    fn update(&mut self, generations_log2: u32) -> Result<[BigInt; 2]> {
        if generations_log2 >= 64 {
            return Err(anyhow!(
                "Generation count 2^{} is insanely large for SIMDEngine",
                generations_log2
            ));
        }
        let w = self.n >> Self::CELLS_IN_CHUNK.ilog2();
        let backend = Self::select_backend(w);
        for _ in 0..1u64 << generations_log2 {
            self.update_inner(backend);
        }
        Ok([BigInt::ZERO; 2])
    }

    fn bytes_total(&self) -> usize {
        (self.data.capacity() + self.scratch.capacity()) * size_of::<u64>()
    }
}
