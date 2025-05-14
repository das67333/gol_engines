use crate::VERSION;
use ahash::AHashMap as HashMap;
use anyhow::{anyhow, Context, Result};
use flate2::{
    read::{GzDecoder, GzEncoder},
    Compression,
};
use num_bigint::BigInt;
use rand::{Rng, SeedableRng};
use std::io::Read;

/// Nodes typically have size of about 32 bytes, so 2^32 (128 GiB) nodes
/// is generally enough.
type NodeIdx = u32;
/// A type for measuring the depth of the quadtree.
type SizeLog2 = u32;

/// Represents a Game of Life pattern using a memory-efficient quadtree structure.
///
/// # Overview
///
/// This struct implements a quadtree where each node represents a square region
/// of the pattern. Leaf nodes represent 8x8 cell blocks ([`PatternNode::Leaf`]),
/// while internal nodes ([`PatternNode::Node`]) subdivide their region into four
/// smaller quadrants (nw, ne, sw, se).
///
/// This structure allows for significant memory savings for large or sparse patterns
/// through node deduplication (via `KIVMap`), making it ideal for compact
/// checkpoints in Game of Life engines.
///
/// # Features
///
/// *   **Quadtree Representation:** Efficiently stores patterns with regularities.
///     Hovewer, even randomly-filled patterns are stored with insignificant overhead
///     compared to a flat packed array.
/// *   **Power-of-2 Sizes:** Supports square patterns with side lengths that are
///     powers of 2 (e.g., 1x1, 2x2, 8x8, 16x16...).
/// *   **Serialization:** Can be serialized to and deserialized from various
///     standard formats (see [`PatternFormat`]):
///     *   `PackedCells`
///     *   `Macrocell`
///     *   `CompressedMacrocell`
///     *   `RLE`
/// *   **Precise Population Count:** Accurately computes the total number of
///     live cells in the pattern using arbitrary-precision arithmetic. This method
///     guarantees precise results even for extremely large patterns where cell counts
///     might exceed the limits of fixed-size integers.
/// *   **Metafy Expansion:** Recursively expands the pattern by replacing each cell
///     with the corresponding base metacell from the provided `metacells`. This approach
///     delivers higher performance than Golly scripts and enables efficient creation
///     of multi-level metapatterns.
///
/// # Format Recommendations
///
/// For best performance and memory efficiency, prefer [`PatternFormat::Macrocell`] or
/// [`PatternFormat::CompressedMacrocell`] over other formats. These formats:
///
/// * Best align with the internal quadtree representation used by `Pattern`
/// * Provide faster loading and saving for large patterns
/// * Handle sparse patterns more efficiently
/// * Support patterns of virtually unlimited size
///
/// If you encounter issues loading patterns that work in Golly and should work here,
/// the file might not conform to the format specifications detailed at
/// https://golly.sourceforge.io/Help/formats.html.
/// Try opening the problematic pattern in a modern version of Golly and saving it again
/// to ensure it meets the expected format requirements.
///
/// # Limitations
///
/// *   **Two-State Only:** Currently supports only standard two-state
///     (dead/alive) cells.
/// *   **B3/S23 Rule:** Assumes Conway's standard B3/S23 rule for format conversions
///     (like RLE and Macrocell) and engine operations.
/// *   **Size Limitations:** While the theoretical maximum dimension is about
///     `2^(2^32) x 2^(2^32)` (limited by `SizeLog2`), the practical size is
///     constrained by the `NodeIdx` limit of `2^32` unique nodes.
///     Dense or random patterns may exhaust node indices much sooner;
///     the maximum size guaranteed to fit regardless of pattern content is
///     `2^18 x 2^18`. Highly repetitive patterns can achieve much larger sizes.
/// *   **Memory Allocation:** Relies on Rust's default allocator. If memory allocation
///     fails (e.g., due to insufficient system memory), functions will typically
///     panic and terminate rather than return an error.
#[derive(Clone)]
pub struct Pattern {
    /// The root node of the quadtree, has size of
    /// `(1 << size_log2) x (1 << size_log2)`.
    root: NodeIdx,
    /// `size_log2` is the log2(side length of the square).
    /// For example, a 16x16 pattern has `size_log2` of 4.
    size_log2: SizeLog2,
    /// Storage for the quadtree nodes.
    kiv: KIVMap,
    /// Caches blank nodes for faster search.
    blank_nodes: Vec<NodeIdx>,
}

impl Pattern {
    /// Returns the root node index of the pattern.
    ///
    /// The root node represents the top-level quadtree node covering the entire pattern.
    pub fn get_root(&self) -> NodeIdx {
        self.root
    }

    /// Changes the root node of the pattern to a new node with a specified size.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it requires the caller to ensure:
    /// - `root` is a valid node index that exists in the pattern's KIVMap
    /// - `size_log2` correctly represents the size of the new root node
    ///
    /// # Arguments
    ///
    /// * `root` - The index of the new root node
    /// * `size_log2` - The log base 2 of the new root's side length
    pub unsafe fn change_root(&mut self, root: NodeIdx, size_log2: SizeLog2) {
        self.root = root;
        self.size_log2 = size_log2;
    }

    /// Finds an existing node with the given content or creates a new one.
    ///
    /// This method delegates to the internal KIVMap to find or create a node,
    /// maintaining the pattern's node deduplication property.
    ///
    /// # Arguments
    ///
    /// * `node` - The pattern node content to find or create
    ///
    /// # Returns
    ///
    /// A `NodeIdx` that uniquely identifies the node with the specified content
    pub fn find_or_create_node(&mut self, node: PatternNode) -> NodeIdx {
        self.kiv.find_or_create_node(node)
    }

    /// Returns the log base 2 of the pattern's side length.
    ///
    /// The pattern is always square with side length of `2^size_log2`.
    /// For example, a pattern with `size_log2 = 3` is 8x8 cells.
    pub fn get_size_log2(&self) -> SizeLog2 {
        self.size_log2
    }

    /// Retrieves a node from the pattern by its index.
    ///
    /// # Arguments
    ///
    /// * `idx` - The index of the node to retrieve.
    ///
    /// # Returns
    ///
    /// A reference to the requested `PatternNode`.
    pub fn get_node(&self, idx: NodeIdx) -> &PatternNode {
        self.kiv.get_node(idx)
    }

    /// Computes a 64-bit hash of the entire pattern. Intended for fast
    /// probabilistic pattern comparison.
    ///
    /// This method recursively traverses the quadtree and combines hashes
    /// of each node using a non-cryptographic hash function. The hash is
    /// consistent for identical patterns regardless of their internal
    /// representation.
    ///
    /// # Returns
    ///
    /// A 64-bit hash value for the pattern.
    pub fn hash(&self) -> u64 {
        fn inner(idx: NodeIdx, cache: &mut HashMap<NodeIdx, u64>, kiv: &KIVMap) -> u64 {
            if let Some(&val) = cache.get(&idx) {
                return val;
            }

            let combine = |x: u64, y: u64| -> u64 {
                x ^ y
                    .wrapping_add(0x9e3779b9)
                    .wrapping_add(x << 6)
                    .wrapping_add(x >> 2)
            };

            match kiv.get_node(idx) {
                PatternNode::Leaf(cells) => *cells,
                PatternNode::Node { nw, ne, sw, se } => {
                    let mut result = 0;
                    for x in [*nw, *ne, *sw, *se] {
                        result = combine(result, inner(x, cache, kiv));
                    }
                    cache.insert(idx, result);
                    result
                }
            }
        }

        let mut cache = HashMap::new();
        inner(self.root, &mut cache, &self.kiv)
    }

    /// Counts the total number of alive cells in the pattern.
    ///
    /// This method efficiently traverses the quadtree structure and
    /// memoizes intermediate results to avoid redundant calculations.
    ///
    /// # Returns
    ///
    /// A `BigInt` representing the total number of alive cells, which can
    /// be arbitrarily large for very large patterns.
    pub fn population(&self) -> BigInt {
        fn inner<'a>(idx: NodeIdx, cache: &'a mut HashMap<NodeIdx, BigInt>, kiv: &'a KIVMap) {
            let result = match kiv.get_node(idx) {
                PatternNode::Leaf(cells) => BigInt::from(cells.count_ones()),
                PatternNode::Node { nw, ne, sw, se } => {
                    let mut result = BigInt::ZERO;
                    for x in [*nw, *ne, *sw, *se] {
                        if !cache.contains_key(&x) {
                            inner(x, cache, kiv);
                        }
                        result += cache.get(&x).unwrap();
                    }
                    result
                }
            };
            cache.insert(idx, result);
        }

        let mut cache = HashMap::new();
        inner(self.root, &mut cache, &self.kiv);
        cache.remove(&self.root).unwrap()
    }

    /// Expands the pattern to a larger size by adding dead cells to the right and bottom.
    ///
    /// This function increases the `size_log2` of the pattern to the requested value, effectively
    /// making the pattern's dimensions larger. The original pattern content remains in the top-left
    /// corner, with dead cells filling the newly added space.
    ///
    /// # Arguments
    ///
    /// * `size_log2` - The desired log base 2 of the new pattern size.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use gol_engines::{Pattern, PatternFormat};
    ///
    /// let mut pattern = gol_engines::Pattern::random(2, None).unwrap();
    /// assert_eq!(pattern.get_size_log2(), 2); // 4x4 pattern
    ///
    /// // Expand to 256x256
    /// pattern.expand(8);
    /// assert_eq!(pattern.get_size_log2(), 8);
    /// ```
    ///
    /// # Note
    ///
    /// If `size_log2` is less than or equal to the current size, this function does nothing.
    pub fn expand(&mut self, size_log2: SizeLog2) {
        if self.size_log2 >= size_log2 {
            return;
        }
        if size_log2 <= 3 {
            self.size_log2 = size_log2;
            return;
        }
        self.size_log2 = self.size_log2.max(3);
        while self.size_log2 < size_log2 {
            let blank = Self::find_or_create_blank_node(
                self.size_log2,
                &mut self.kiv,
                &mut self.blank_nodes,
            );

            self.root = self.kiv.find_or_create_node(PatternNode::Node {
                nw: self.root,
                ne: blank,
                sw: blank,
                se: blank,
            });
            self.size_log2 += 1;
        }
    }

    /// Creates a random pattern of the specified size.
    ///
    /// # Arguments
    ///
    /// * `size_log2` - Log base 2 of the pattern's side length.
    /// * `seed` - Optional seed for the random number generator.
    ///   If None, seeds from the OS.
    ///
    /// # Returns
    ///
    /// A `Result` containing either the created random `Pattern` or an error.
    ///
    /// # Errors
    ///
    /// Returns an error if `size_log2` is too large (would cause overflow).
    pub fn random(size_log2: SizeLog2, seed: Option<u64>) -> Result<Self> {
        if 1usize.checked_shl(size_log2 * 2).is_none() {
            return Err(anyhow!("size_log2 {} is too large", size_log2));
        }
        let n = 1usize << size_log2;
        let mut cells = vec![0u8; (n * n).div_ceil(8).max(n)];
        if let Some(x) = seed {
            rand_chacha::ChaCha8Rng::seed_from_u64(x)
        } else {
            rand_chacha::ChaCha8Rng::from_os_rng()
        }
        .fill(&mut cells[..]);
        if size_log2 < 3 {
            // clear the upper bits
            for x in cells.iter_mut() {
                *x &= ((1u32 << n) - 1) as u8;
            }
        }
        Self::from_packed_cells(&cells)
    }

    /// Recursively expands a pattern by replacing cells with `metacells` multiple times.
    /// Optimized for building huge multi-level metacells.
    ///
    /// This function treats the current pattern (`self`) as a high-level layout.
    /// It performs `level` steps of expansion. In each step, every 'alive' cell
    /// is replaced by the `metacells[1]` pattern (ON state), and every 'dead' cell
    /// is replaced by the `metacells[0]` pattern (OFF state).
    ///
    /// For example, if `level = 1`, each cell in `self` is directly replaced by the
    /// corresponding pattern from `metacells`. If `level = 2`, each cell in `self` is
    /// replaced by a meta-pattern, which itself is constructed by replacing *its*
    /// cells with the patterns from `metacells`.
    ///
    /// # Arguments
    ///
    /// * `self` - The pattern representing the initial high-level layout.
    /// * `metacells` - An array containing two `Pattern`s defining the base unit cells:
    ///   `metacells[0]` for the OFF state and `metacells[1]` for the ON state.
    ///   These patterns must have the same `size_log2`.
    /// * `level` - The number of recursive expansion level to perform.
    ///   Zero means doing nothing.
    ///
    /// # Returns
    ///
    /// A `Result` containing the expanded `Pattern`. The final size exponent will be
    /// `self.size_log2 + level * base_size_log2`, where `base_size_log2` is the
    /// `size_log2` of the patterns in `metacells`.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - `metacells[0].size_log2` does not equal `metacells[1].size_log2`
    /// - metacells are smaller than 8x8
    pub fn metafy(&self, metacells: &[Pattern; 2], level: u32) -> Result<Self> {
        if metacells[0].size_log2 != metacells[1].size_log2 {
            return Err(anyhow!(
                "Metacells must have the same size_log2: {} != {}",
                metacells[0].size_log2,
                metacells[1].size_log2
            ));
        }
        if metacells[0].size_log2 < 3 {
            return Err(anyhow!(
                "Metacell size_log2 must be at least 3: {}",
                metacells[0].size_log2
            ));
        }

        if level == 0 {
            return Ok(self.clone());
        }

        fn copy_from_pattern(
            idx: NodeIdx,
            pattern: &Pattern,
            kiv: &mut KIVMap,
            cache: &mut HashMap<NodeIdx, NodeIdx>,
        ) -> NodeIdx {
            if let Some(&x) = cache.get(&idx) {
                return x;
            }
            let result = match pattern.get_node(idx) {
                PatternNode::Leaf(cells) => kiv.find_or_create_node(PatternNode::Leaf(*cells)),
                PatternNode::Node { nw, ne, sw, se } => {
                    let nw = copy_from_pattern(*nw, pattern, kiv, cache);
                    let ne = copy_from_pattern(*ne, pattern, kiv, cache);
                    let sw = copy_from_pattern(*sw, pattern, kiv, cache);
                    let se = copy_from_pattern(*se, pattern, kiv, cache);
                    kiv.find_or_create_node(PatternNode::Node { nw, ne, sw, se })
                }
            };
            cache.insert(idx, result);
            result
        }

        let mut kiv = KIVMap::new();
        let mut cache = HashMap::new();
        let mut metacell_idx = [0; 2];
        for (src, dst) in metacells.iter().zip(metacell_idx.iter_mut()) {
            *dst = copy_from_pattern(src.root, src, &mut kiv, &mut cache);
            cache.clear();
        }

        fn build_pattern_from_metacells(
            pattern: &Pattern,
            metacells: [NodeIdx; 2],
            idx: NodeIdx,
            kiv: &mut KIVMap,
            cache: &mut HashMap<NodeIdx, NodeIdx>,
        ) -> NodeIdx {
            if let Some(&x) = cache.get(&idx) {
                return x;
            }
            let result = match pattern.get_node(idx) {
                PatternNode::Leaf(cells) => {
                    let mut a = [[0; 8]; 8];
                    for y in 0..8 {
                        for x in 0..8 {
                            a[y][x] = metacells[(cells >> (x + y * 8)) as usize & 1];
                        }
                    }
                    if pattern.size_log2 == 0 {
                        return a[0][0];
                    }
                    let mut b = [[0; 4]; 4];
                    for y in 0..4 {
                        for x in 0..4 {
                            b[y][x] = kiv.find_or_create_node(PatternNode::Node {
                                nw: a[y * 2][x * 2],
                                ne: a[y * 2][x * 2 + 1],
                                sw: a[y * 2 + 1][x * 2],
                                se: a[y * 2 + 1][x * 2 + 1],
                            });
                        }
                    }
                    if pattern.size_log2 == 1 {
                        return b[0][0];
                    }
                    let mut c = [[0; 2]; 2];
                    for y in 0..2 {
                        for x in 0..2 {
                            c[y][x] = kiv.find_or_create_node(PatternNode::Node {
                                nw: b[y * 2][x * 2],
                                ne: b[y * 2][x * 2 + 1],
                                sw: b[y * 2 + 1][x * 2],
                                se: b[y * 2 + 1][x * 2 + 1],
                            });
                        }
                    }
                    if pattern.size_log2 == 2 {
                        return c[0][0];
                    }
                    kiv.find_or_create_node(PatternNode::Node {
                        nw: c[0][0],
                        ne: c[0][1],
                        sw: c[1][0],
                        se: c[1][1],
                    })
                }
                PatternNode::Node { nw, ne, sw, se } => {
                    let nw = build_pattern_from_metacells(pattern, metacells, *nw, kiv, cache);
                    let ne = build_pattern_from_metacells(pattern, metacells, *ne, kiv, cache);
                    let sw = build_pattern_from_metacells(pattern, metacells, *sw, kiv, cache);
                    let se = build_pattern_from_metacells(pattern, metacells, *se, kiv, cache);
                    kiv.find_or_create_node(PatternNode::Node { nw, ne, sw, se })
                }
            };
            cache.insert(idx, result);
            result
        }

        for _ in 0..level - 1 {
            metacell_idx = [0, 1].map(|i| {
                let result = build_pattern_from_metacells(
                    &metacells[i],
                    metacell_idx,
                    metacells[i].root,
                    &mut kiv,
                    &mut cache,
                );
                cache.clear();
                result
            });
        }

        let root =
            build_pattern_from_metacells(self, metacell_idx, self.root, &mut kiv, &mut cache);
        Ok(Self {
            root,
            size_log2: self.size_log2 + level * metacells[0].size_log2,
            kiv,
            blank_nodes: vec![],
        })
    }

    /// Creates a pattern from data in the specified format.
    ///
    /// # Arguments
    ///
    /// * `format` - The format of the provided data.
    /// * `data` - The bytes containing the pattern data.
    ///
    /// # Returns
    ///
    /// A `Result` containing either the created `Pattern` or an error.
    ///
    /// # Errors
    ///
    /// Returns format-specific errors:
    /// - `PackedCells`: If the data does not represent a square with a side that is a power of 2
    /// - `Macrocell` or `RLE`: If data is invalid, uses more than two states, or specifies
    ///   non-B3/S23 rules
    /// - `CompressedMacrocell`: If decompression fails or macrocell parsing errors occur
    ///
    /// # Performance Considerations
    ///
    /// For large or highly non-square patterns, the tree-based formats (`Macrocell` and
    /// `CompressedMacrocell`) generally provide better performance and memory efficiency than
    /// the flat array-based formats (`PackedCells` and `RLE`).
    pub fn from_format(format: PatternFormat, data: &[u8]) -> Result<Self> {
        match format {
            PatternFormat::PackedCells => Self::from_packed_cells(data),
            PatternFormat::Macrocell => Self::from_macrocell(data),
            PatternFormat::CompressedMacrocell => Self::from_compressed_macrocell(data),
            PatternFormat::RLE => Self::from_rle(data),
        }
    }

    /// Converts the pattern to the specified format.
    ///
    /// # Arguments
    ///
    /// * `format` - The desired output format.
    ///
    /// # Returns
    ///
    /// A `Result` containing either the bytes of the pattern in the requested format
    /// or an error.
    ///
    /// # Errors
    ///
    /// Returns format-specific errors:
    /// - `PackedCells` or `RLE`: If `size_log2` is too large (would cause overflow)
    /// - `Macrocell` or `CompressedMacrocell`: If the pattern is blank (contains no alive cells)
    pub fn to_format(&self, format: PatternFormat) -> Result<Vec<u8>> {
        match format {
            PatternFormat::PackedCells => self.to_packed_cells(),
            PatternFormat::Macrocell => self.to_macrocell(),
            PatternFormat::CompressedMacrocell => self.to_compressed_macrocell(),
            PatternFormat::RLE => self.to_rle(),
        }
    }

    /// Creates a pattern from packed cell data. See [`PatternFormat::PackedCells`].
    ///
    /// # Arguments
    ///
    /// * `data` - Bytes containing the packed cell data.
    ///
    /// # Returns
    ///
    /// A `Result` containing either the created `Pattern` or an error.
    ///
    /// # Errors
    ///
    /// Returns an error if the data does not represent a square with a side that is a power of 2.
    fn from_packed_cells(data: &[u8]) -> Result<Self> {
        if data.is_empty() {
            return Err(anyhow!("Packed cells are empty"));
        }
        let size_log2 = data.len().ilog2().min((data.len().ilog2() + 3) / 2);
        let n = 1usize << size_log2;
        if data.len() != (n * n).div_ceil(8).max(n) {
            return Err(anyhow!(
                "Packed cells don't represent a square with a power of 2 side"
            ));
        }

        if size_log2 < 3 {
            for x in data.iter() {
                if *x & !((1u32 << n) - 1) as u8 != 0 {
                    return Err(anyhow!("Found cells out of bounds"));
                }
            }
        }

        let mut kiv = KIVMap::new();
        let (mut nodes_curr, mut nodes_next) = (vec![], vec![]);

        let stride = n.max(8);
        for y in (0..n).step_by(8) {
            for x in (0..n).step_by(8) {
                let mut leaf = [0; 8];
                for dy in 0..8.min(n) {
                    leaf[dy] = data[(x + (dy + y) * stride) / 8];
                }
                nodes_curr
                    .push(kiv.find_or_create_node(PatternNode::Leaf(u64::from_le_bytes(leaf))));
            }
        }
        let mut t = stride / 8;
        while t != 1 {
            for y in (0..t).step_by(2) {
                for x in (0..t).step_by(2) {
                    let nw = nodes_curr[x + y * t];
                    let ne = nodes_curr[(x + 1) + y * t];
                    let sw = nodes_curr[x + (y + 1) * t];
                    let se = nodes_curr[(x + 1) + (y + 1) * t];
                    nodes_next.push(kiv.find_or_create_node(PatternNode::Node { nw, ne, sw, se }));
                }
            }
            std::mem::swap(&mut nodes_curr, &mut nodes_next);
            nodes_next.clear();
            t >>= 1;
        }
        assert_eq!(nodes_curr.len(), 1);
        Ok(Self {
            root: nodes_curr[0],
            size_log2,
            kiv,
            blank_nodes: vec![],
        })
    }

    /// Converts the pattern to packed cell data. See [`PatternFormat::PackedCells`].
    ///
    /// # Returns
    ///
    /// A `Result` containing either the bytes of the packed cells representation
    /// or an error.
    ///
    /// # Errors
    ///
    /// Returns an error if `self.size_log2` is too large (would cause overflow).
    fn to_packed_cells(&self) -> Result<Vec<u8>> {
        fn inner(
            this: &Pattern,
            idx: NodeIdx,
            size_log2: SizeLog2,
            cells: &mut Vec<u8>,
            stride: usize,
            x: usize,
            y: usize,
        ) {
            match this.get_node(idx) {
                PatternNode::Leaf(cells_data) => {
                    for dy in 0..1 << size_log2 {
                        cells[(x + (dy + y) * stride) / 8] |= cells_data.to_le_bytes()[dy];
                    }
                }
                PatternNode::Node { nw, ne, sw, se } => {
                    let half = 1 << (size_log2 - 1);
                    inner(this, *nw, size_log2 - 1, cells, stride, x, y);
                    inner(this, *ne, size_log2 - 1, cells, stride, x + half, y);
                    inner(this, *sw, size_log2 - 1, cells, stride, x, y + half);
                    inner(this, *se, size_log2 - 1, cells, stride, x + half, y + half);
                }
            }
        }

        if 1usize.checked_shl(self.size_log2 * 2).is_none() {
            return Err(anyhow!("size_log2 {} is too large", self.size_log2));
        }
        let n = 1usize << self.size_log2;
        let mut cells = vec![0; (n * n).div_ceil(8).max(n)];
        inner(self, self.root, self.size_log2, &mut cells, n.max(8), 0, 0);
        Ok(cells)
    }

    /// Creates a pattern from data in the macrocell format. See [`PatternFormat::Macrocell`].
    ///
    /// # Arguments
    ///
    /// * `data` - The bytes containing the macrocell data.
    ///
    /// # Returns
    ///
    /// A `Result` containing either the created `Pattern` or an error.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Data is invalid
    /// - Algorithm has more than two states
    /// - A rule other than B3/S23 is specified
    fn from_macrocell(data: &[u8]) -> Result<Self> {
        let mut kiv = KIVMap::new();
        let mut blank_nodes = vec![];
        let mut codes_and_sizes = HashMap::<u32, (NodeIdx, SizeLog2)>::new();
        let mut last_code_and_size = None;

        let mut lines = data
            .split(|&x| x == b'\n')
            .map(|x| x.strip_suffix(b"\r").unwrap_or(x))
            .filter(|x| !x.is_empty());
        if !lines
            .next()
            .ok_or_else(|| anyhow!("Missing format identifier"))?
            .starts_with(b"[M2]")
        {
            return Err(anyhow!("Invalid format identifier"));
        }

        for s in lines {
            if s[0] == b'#' {
                if s.starts_with(b"#R") && &s[2..] != b" B3/S23" {
                    return Err(anyhow!("Only B3/S23 rule is supported"));
                }
                continue;
            }

            let idx = (codes_and_sizes.len() + 1).try_into().with_context(|| {
                format!("Failed to convert {} to NodeIdx", codes_and_sizes.len() + 1)
            })?;

            let code_and_size = if s[0].is_ascii_digit() {
                // non-leaf
                let numbers: Vec<u32> = s
                    .split(|&x| x == b' ')
                    .map(|part| {
                        std::str::from_utf8(part)
                            .with_context(|| format!("Invalid UTF-8 sequence in {:?}", part))
                            .and_then(|s| {
                                s.parse::<u32>().with_context(|| {
                                    format!("Failed to parse integer from '{}'", s)
                                })
                            })
                    })
                    .collect::<Result<_>>()?;
                if numbers.len() != 5 {
                    return Err(anyhow!("Expected 5 numbers, got {}", numbers.len()));
                }
                if numbers[0] < 4 {
                    return Err(anyhow!(
                        "Node {} has size_log2 {}, expected >= 4",
                        idx,
                        numbers[0],
                    ));
                }

                let mut resolve = |x: u32| -> Result<NodeIdx> {
                    if x == 0 {
                        Ok(Self::find_or_create_blank_node(
                            numbers[0] - 1,
                            &mut kiv,
                            &mut blank_nodes,
                        ))
                    } else {
                        let (code, size_log2) =
                            codes_and_sizes.get(&x).copied().ok_or_else(|| {
                                anyhow!("Reference to undeclared node with code {}", x)
                            })?;
                        if size_log2 != numbers[0] - 1 {
                            return Err(anyhow!(
                                "Node {} has size_log2 {}, expected {}",
                                x,
                                size_log2,
                                numbers[0] - 1
                            ));
                        }
                        Ok(code)
                    }
                };

                let nw = resolve(numbers[1])?;
                let ne = resolve(numbers[2])?;
                let sw = resolve(numbers[3])?;
                let se = resolve(numbers[4])?;
                let code = kiv.find_or_create_node(PatternNode::Node { nw, ne, sw, se });
                (code, numbers[0])
            } else {
                // is leaf
                let mut cells = 0u64;
                let (mut i, mut j) = (0, 0);
                for &c in s {
                    match c {
                        b'$' => (i, j) = (i + 1, 0),
                        b'*' => {
                            if i >= 8 || j >= 8 {
                                return Err(anyhow!(
                                    "Leaf {} does not fit in 8x8",
                                    String::from_utf8_lossy(s)
                                ));
                            }
                            cells |= 1 << (i * 8 + j);
                            j += 1;
                        }
                        b'.' => {
                            j += 1;
                        }
                        _ => {
                            return Err(anyhow!(
                                "Invalid symbol '{}' in leaf {}",
                                c as char,
                                String::from_utf8_lossy(s)
                            ))
                        }
                    }
                }
                let code = kiv.find_or_create_node(PatternNode::Leaf(cells));
                (code, 3)
            };
            last_code_and_size = Some(code_and_size);
            codes_and_sizes.insert(idx, code_and_size);
        }
        let (root, size_log2) =
            last_code_and_size.ok_or_else(|| anyhow!("No nodes found in the pattern"))?;
        Ok(Self {
            root,
            size_log2,
            kiv,
            blank_nodes,
        })
    }

    /// Converts the pattern to the macrocell format. See [`PatternFormat::Macrocell`].
    ///
    /// # Returns
    ///
    /// A `Result` containing either the bytes of the macrocell representation
    /// or an error.
    ///
    /// # Errors
    ///
    /// Returns an error if the pattern is blank (contains no alive cells).
    fn to_macrocell(&self) -> Result<Vec<u8>> {
        fn inner(
            this: &Pattern,
            idx: NodeIdx,
            size_log2: SizeLog2,
            codes: &mut HashMap<NodeIdx, usize>,
            blank_nodes: &mut Vec<NodeIdx>,
            result: &mut Vec<u8>,
        ) -> usize {
            // if already serialized
            if let Some(&x) = codes.get(&idx) {
                return x;
            }
            // if node is blank
            if let Some(x) = Pattern::find_blank_node(size_log2, &this.kiv, blank_nodes) {
                if x == idx {
                    return 0;
                }
            }

            match *this.get_node(idx) {
                PatternNode::Leaf(x) => {
                    for t in x.to_le_bytes() {
                        for i in 0..8 {
                            if (t >> i) & 1 != 0 {
                                result.push(b'*');
                            } else {
                                result.push(b'.');
                            }
                        }
                        while result.ends_with(b".") {
                            result.pop();
                        }
                        result.push(b'$');
                    }
                    while result.ends_with(b"$$") {
                        result.pop();
                    }
                    result.push(b'\n');
                }
                PatternNode::Node { nw, ne, sw, se } => {
                    let new_line = format!(
                        "{} {} {} {} {}\n",
                        size_log2,
                        inner(this, nw, size_log2 - 1, codes, blank_nodes, result),
                        inner(this, ne, size_log2 - 1, codes, blank_nodes, result),
                        inner(this, sw, size_log2 - 1, codes, blank_nodes, result),
                        inner(this, se, size_log2 - 1, codes, blank_nodes, result),
                    );
                    result.extend_from_slice(new_line.as_bytes());
                }
            }
            codes.insert(idx, codes.len() + 1);
            codes.len()
        }

        let mut blank_nodes = self.blank_nodes.clone();
        if let Some(x) = Self::find_blank_node(self.size_log2, &self.kiv, &mut blank_nodes) {
            if x == self.root {
                return Err(anyhow!("Cannot serialize blank pattern"));
            }
        }

        let mut codes = HashMap::new();
        let mut result = format!("[M2] (gol_engines {})\n#R B3/S23\n", VERSION).into_bytes();
        inner(
            self,
            self.root,
            self.size_log2,
            &mut codes,
            &mut blank_nodes,
            &mut result,
        );

        Ok(result)
    }

    /// Creates a pattern from gzip-compressed macrocell data.
    /// See [`PatternFormat::CompressedMacrocell`].
    ///
    /// This method decompresses the input data and then parses it using
    /// the standard macrocell format parser.
    ///
    /// # Arguments
    ///
    /// * `compressed_data` - The gzip-compressed bytes containing macrocell data.
    ///
    /// # Returns
    ///
    /// A `Result` containing either the created `Pattern` or an error.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The input data is not valid gzip-compressed data
    /// - Other errors from `from_macrocell` occur
    fn from_compressed_macrocell(compressed_data: &[u8]) -> Result<Self> {
        // Create a gzip decoder
        let mut decoder = GzDecoder::new(compressed_data);
        let mut decompressed_data = Vec::new();
        decoder
            .read_to_end(&mut decompressed_data)
            .context("Failed to decompress macrocell data")?;
        Self::from_macrocell(&decompressed_data)
    }

    /// Converts the pattern to gzip-compressed macrocell format.
    /// See [`PatternFormat::CompressedMacrocell`].
    ///
    /// This method first converts the pattern to macrocell format using
    /// `to_macrocell`, then compresses the result using gzip.
    ///
    /// # Returns
    ///
    /// A `Result` containing either the gzip-compressed bytes of the
    /// macrocell representation or an error.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The pattern is blank (contains no alive cells)
    /// - Compression fails
    fn to_compressed_macrocell(&self) -> Result<Vec<u8>> {
        let macrocell_data = self.to_macrocell()?;
        let mut encoder = GzEncoder::new(&macrocell_data[..], Compression::default());
        let mut compressed_data = Vec::new();
        encoder
            .read_to_end(&mut compressed_data)
            .context("Failed to compress macrocell data")?;
        Ok(compressed_data)
    }

    /// Creates a pattern from data in the Extended RLE format. See [`PatternFormat::RLE`].
    ///
    /// # Arguments
    ///
    /// * `data` - The bytes containing the Extended RLE data.
    ///
    /// # Returns
    ///
    /// A `Result` containing either the created `Pattern` or an error.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Data is invalid
    /// - Algorithm has more than two states
    /// - Rule is not B3/S23
    ///
    /// # Performance Considerations
    ///
    /// The current implementation struggles with highly non-square patterns
    /// (like very long and narrow ones), as it fills a square grid based on the
    /// maximum dimension. This can lead to excessive memory usage for patterns
    /// with disparate dimensions. Consider using [`PatternFormat::Macrocell`]
    /// or [`PatternFormat::CompressedMacrocell`] instead.
    fn from_rle(data: &[u8]) -> Result<Self> {
        let mut lines = data
            .split(|&b| b == b'\n')
            .map(|x| x.strip_suffix(b"\r").unwrap_or(x))
            .filter(|x| !x.is_empty() && x[0] != b'#');
        let width: usize;
        let height: usize;

        // Parse header
        if let Some(line) = lines.next() {
            // Parse x, y and rule
            let mut parts = line.split(|&b| b == b',').map(|x| x.trim_ascii());

            let extract_value = |part: &[u8], expected_key: &[u8]| {
                let mut items = part.split(|&b| b == b'=');
                let key = items.next().unwrap_or(&[]).trim_ascii_end();
                if key != expected_key {
                    return Err(anyhow!(
                        "Invalid header: expected {}, got {}",
                        String::from_utf8_lossy(expected_key),
                        String::from_utf8_lossy(key)
                    ));
                }
                let value = items.next().unwrap_or(&[]).trim_ascii_start();
                if items.next().is_some() {
                    return Err(anyhow!("Invalid header: missing ',' between '='"));
                }
                Ok(value.to_vec())
            };

            let value = extract_value(
                parts
                    .next()
                    .ok_or_else(|| anyhow!("Invalid header: missing \"x\""))?,
                b"x",
            )?;
            width = std::str::from_utf8(&value)?.parse()?;

            let value = extract_value(
                parts
                    .next()
                    .ok_or_else(|| anyhow!("Invalid header: missing \"y\""))?,
                b"y",
            )?;
            height = std::str::from_utf8(&value)?.parse()?;

            // rule is optional
            if let Some(rule) = parts.next().map(|part| extract_value(part, b"rule")) {
                match rule {
                    Ok(rule) => {
                        if rule != b"B3/S23" {
                            return Err(anyhow!("Only B3/S23 rule is supported"));
                        }
                    }
                    Err(err) => return Err(err),
                }
            }
        } else {
            return Err(anyhow!("Missing header"));
        }

        // Calculate size and prepare cells array
        let size_log2 = (width.max(height)).next_power_of_two().ilog2();
        let n = 1usize << size_log2;
        let stride = n.max(8);
        let mut cells = vec![0u8; (n * n).div_ceil(8).max(n)];

        // Parse pattern data
        let mut x = 0;
        let mut y = 0;
        let mut count = 0;

        for line in lines {
            for &b in line {
                match b {
                    b'0'..=b'9' => count = count * 10 + (b - b'0') as usize,
                    b'b' => {
                        x += if count == 0 { 1 } else { count };
                        count = 0;
                    }
                    b'o' => {
                        let c = if count == 0 { 1 } else { count };
                        for i in 0..c {
                            if x + i >= width || y >= height {
                                return Err(anyhow!(
                                    "Pattern data out of bounds: x = {}, y = {}",
                                    x + i,
                                    y
                                ));
                            }
                            let pos = x + i + y * stride;
                            cells[pos / 8] |= 1 << (pos % 8);
                        }
                        x += c;
                        count = 0;
                    }
                    b'$' => {
                        y += if count == 0 { 1 } else { count };
                        x = 0;
                        count = 0;
                    }
                    b'!' => break,
                    b' ' => continue,
                    _ => return Err(anyhow!("Invalid RLE character: '{}'", b as char)),
                }
                if x > width {
                    return Err(anyhow!("Pattern data out of bounds: x = {}, y = {}", x, y));
                }
            }
        }

        Self::from_packed_cells(&cells)
    }

    /// Converts the pattern to the RLE format. See [`PatternFormat::RLE`].
    ///
    /// # Returns
    ///
    /// A `Result` containing either the bytes of the RLE representation
    /// or an error.
    ///
    /// # Errors
    ///
    /// Returns an error if pattern is too large.
    ///
    /// # Performance Considerations
    ///
    /// The current implementation struggles with highly non-square patterns
    /// (like very long and narrow ones), as it fills a square grid based on the
    /// maximum dimension. This can lead to excessive memory usage for patterns
    /// with disparate dimensions. Consider using [`PatternFormat::Macrocell`]
    /// or [`PatternFormat::CompressedMacrocell`] instead.
    fn to_rle(&self) -> Result<Vec<u8>> {
        let cells_data = self.to_packed_cells()?;
        let n = 1usize << self.size_log2;
        let stride = n.max(8);

        // Find the bounding box
        let mut min_x = n;
        let mut max_x = 0;
        let mut min_y = n;
        let mut max_y = 0;
        for y in 0..n {
            for x in 0..n {
                let pos = x + y * stride;
                if cells_data[pos / 8] & (1 << (pos % 8)) != 0 {
                    min_x = min_x.min(x);
                    max_x = max_x.max(x);
                    min_y = min_y.min(y);
                    max_y = max_y.max(y);
                }
            }
        }

        // Empty pattern
        if min_x > max_x || min_y > max_y {
            return Ok(b"x = 0, y = 0, rule = B3/S23\n!".to_vec());
        }

        let mut result = format!(
            "x = {}, y = {}, rule = B3/S23\n",
            max_x - min_x + 1,
            max_y - min_y + 1
        )
        .into_bytes();
        // Encode the pattern
        let mut line_length = 0;

        for y in min_y..=max_y {
            let mut run_length = 0u32;
            let mut last_state = false;

            for x in min_x..=max_x {
                let pos = x + y * stride;
                let current_state = (cells_data[pos / 8] & (1 << (pos % 8))) != 0;

                if x == min_x || current_state != last_state {
                    if run_length > 0 {
                        let mut run = Vec::new();
                        if run_length > 1 {
                            run.extend_from_slice(run_length.to_string().as_bytes());
                        }
                        run.push(if last_state { b'o' } else { b'b' });

                        if line_length + run.len() > 70 {
                            result.push(b'\n');
                            line_length = 0;
                        }

                        result.extend_from_slice(&run);
                        line_length += run.len();
                    }

                    run_length = 1;
                    last_state = current_state;
                } else {
                    run_length += 1;
                }
            }

            if run_length > 0 {
                let mut run = Vec::new();
                if run_length > 1 {
                    run.extend_from_slice(run_length.to_string().as_bytes());
                }
                run.push(if last_state { b'o' } else { b'b' });
                if line_length + run.len() + 1 > 70 {
                    // +1 for the $ we'll add
                    result.push(b'\n');
                    line_length = 0;
                }
                result.extend_from_slice(&run);
                line_length += run.len();
            }

            if y < max_y {
                result.push(b'$');
                line_length += 1;
            } else {
                result.push(b'!');
            }
        }

        Ok(result)
    }

    /// Finds or creates a blank node (containing all dead cells) of the
    /// specified size.
    ///
    /// This is an internal utility method used to efficiently represent empty
    /// regions in the quadtree.
    ///
    /// # Arguments
    ///
    /// * `size_log2` - Log base 2 of the node's side length.
    /// * `kiv` - The key-index-value map storing the pattern nodes.
    /// * `blank_nodes` - Cache of previously created blank nodes of different sizes.
    ///
    /// # Returns
    ///
    /// The index of the found or newly created blank node.
    fn find_or_create_blank_node(
        size_log2: SizeLog2,
        kiv: &mut KIVMap,
        blank_nodes: &mut Vec<NodeIdx>,
    ) -> NodeIdx {
        let i = (size_log2.max(3) - 3) as usize;
        while blank_nodes.len() <= i {
            let next = if let Some(&b) = blank_nodes.last() {
                PatternNode::Node {
                    nw: b,
                    ne: b,
                    sw: b,
                    se: b,
                }
            } else {
                PatternNode::Leaf(0)
            };
            blank_nodes.push(kiv.find_or_create_node(next));
        }
        blank_nodes[i]
    }

    /// Finds a blank node (containing all dead cells) of the specified size.
    ///
    /// Similar to `find_or_create_blank_node`, but returns `None` if the node doesn't
    /// already exist in the provided `kiv`. This allows the function to take a
    /// const reference to `KIVMap` rather than requiring a mutable reference.
    ///
    /// # Arguments
    ///
    /// * `size_log2` - Log base 2 of the node's side length.
    /// * `kiv` - The key-index-value map storing the pattern nodes (immutable).
    /// * `blank_nodes` - Cache of previously created blank nodes of different sizes.
    ///
    /// # Returns
    ///
    /// An `Option` containing the index of the found blank node, or `None` if
    /// the requested blank node doesn't exist in the `kiv`.
    fn find_blank_node(
        size_log2: SizeLog2,
        kiv: &KIVMap,
        blank_nodes: &mut Vec<NodeIdx>,
    ) -> Option<NodeIdx> {
        let i = (size_log2.max(3) - 3) as usize;
        if let Some(&b) = blank_nodes.get(i) {
            return Some(b);
        }
        let i = (size_log2.max(3) - 3) as usize;
        while blank_nodes.len() <= i {
            let next = if let Some(&b) = blank_nodes.last() {
                PatternNode::Node {
                    nw: b,
                    ne: b,
                    sw: b,
                    se: b,
                }
            } else {
                PatternNode::Leaf(0)
            };
            if let Some(k) = kiv.find_node(next) {
                blank_nodes.push(k);
            } else {
                return None;
            }
        }
        Some(blank_nodes[i])
    }
}

impl Default for Pattern {
    /// Creates a new empty pattern with the following properties:
    /// - An 8x8 empty grid (size_log2 = 3)
    fn default() -> Self {
        let mut kiv = KIVMap::new();
        Self {
            root: kiv.find_or_create_node(PatternNode::Leaf(0)),
            size_log2: 3,
            kiv: KIVMap::new(),
            blank_nodes: vec![],
        }
    }
}

/// A node is either a leaf (8x8 cells) or a non-leaf (4x4 nodes).
/// Cells in the leaf are stored as a 64-bit integer in row-major order.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PatternNode {
    Leaf(u64),
    Node {
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
    },
}

impl PatternNode {
    /// Fast yet effective hash function.
    /// It is used for indexing nodes in the KIVMap.
    fn hash(&self) -> u32 {
        let h = match self {
            PatternNode::Leaf(cells) => (cells ^ (cells >> 32)) as u32,
            PatternNode::Node { nw, ne, sw, se } => 0u32
                .wrapping_add((nw).wrapping_mul(5))
                .wrapping_add((ne).wrapping_mul(17))
                .wrapping_add((sw).wrapping_mul(257))
                .wrapping_add((se).wrapping_mul(65537)),
        };
        h.wrapping_add(h.rotate_right(11))
    }
}

/// Key-Index-Value map: growable hashtable with linked list chains.
///
/// This data structure efficiently stores pattern nodes with two key access methods:
/// 1. By index: retrieve a node by its unique integer ID
/// 2. By content: find a node with specific content orcreate a new one if
///    it doesn't exist
///
/// KIVMap is an essential component of the Pattern's quadtree implementation,
/// providing node deduplication to reduce memory usage in large patterns.
///
/// # Implementation Details
///
/// - Uses open addressing with chained linked lists for collision resolution
/// - Stores nodes contiguously in a vector for cache-friendly access
/// - Maintains separate array of hash table chains for fast lookups
/// - Automatically grows the hash table when load factor exceeds 1.0
/// - Uses a non-cryptographic hash function optimized for pattern nodes
///
/// # Panics
///
/// Panics on running out of indexes (when the number of nodes exceeds
/// the maximum value of NodeIdx).
#[derive(Clone)]
struct KIVMap {
    hashmap_chains: Vec<NodeIdx>,
    storage: Vec<NodeAndNext>,
    capacity_log2: u32,
}

#[derive(Clone, Copy)]
struct NodeAndNext {
    node: PatternNode,
    next: NodeIdx,
}

impl KIVMap {
    const INITIAL_CAPACITY_LOG2: u32 = 4;

    fn new() -> Self {
        let mut storage = Vec::with_capacity(1 << Self::INITIAL_CAPACITY_LOG2);
        // index 0 is reserved
        storage.push(NodeAndNext {
            node: PatternNode::Leaf(0),
            next: 0,
        });
        KIVMap {
            hashmap_chains: vec![0; 1 << Self::INITIAL_CAPACITY_LOG2],
            storage,
            capacity_log2: Self::INITIAL_CAPACITY_LOG2,
        }
    }

    fn get_node(&self, idx: NodeIdx) -> &PatternNode {
        &self.storage[idx as usize].node
    }

    fn find_node(&self, node: PatternNode) -> Option<NodeIdx> {
        let i = node.hash() as usize & (self.hashmap_chains.len() - 1);
        let mut curr = self.hashmap_chains[i];
        // search for the node in the linked list
        while curr != 0 {
            if self.storage[curr as usize].node == node {
                return Some(curr);
            }
            curr = self.storage[curr as usize].next;
        }
        None
    }

    fn find_or_create_node(&mut self, node: PatternNode) -> NodeIdx {
        let i = node.hash() as usize & (self.hashmap_chains.len() - 1);
        let mut curr = self.hashmap_chains[i];
        // search for the node in the linked list
        while curr != 0 {
            if self.storage[curr as usize].node == node {
                return curr;
            }
            curr = self.storage[curr as usize].next;
        }

        self.storage.push(NodeAndNext {
            node,
            next: self.hashmap_chains[i],
        });
        let idx = (self.storage.len() - 1).try_into().expect("Index overflow");
        self.hashmap_chains[i] = idx;
        if self.storage.len() > self.hashmap_chains.len() && self.capacity_log2 != u32::BITS {
            self.rehash();
        }
        idx
    }

    fn rehash(&mut self) {
        self.capacity_log2 += 1;
        let new_size = self.hashmap_chains.len() * 2;
        let mut new_chains = vec![0; new_size];
        for &chain in &self.hashmap_chains {
            let mut curr = chain as usize;
            while curr != 0 {
                let hash = self.storage[curr].node.hash() as usize;
                let next = self.storage[curr].next as usize;
                let index = hash & (new_size - 1);
                self.storage[curr].next = new_chains[index];
                new_chains[index] = curr as NodeIdx;
                curr = next;
            }
        }
        self.hashmap_chains = new_chains;
    }
}

/// Supported formats for pattern serialization and deserialization.
///
/// Notice that only two-state patterns and B3/S23 rules are supported.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PatternFormat {
    /// Packed cells format: a flat array of bytes where each bit represents one cell.
    /// Cells are stored in row-major order with minimal stride of 8 cells per row.
    PackedCells,

    /// [Macrocell](https://golly.sourceforge.io/Help/formats.html#mc) format:
    /// a text-based format that efficiently represents large and sparse patterns.
    ///
    /// This format does not support blank patterns (patterns with no alive cells) and
    /// extends tiny patterns to 8x8 cells.
    ///
    /// Only two-state patterns and B3/S23 rules are supported.
    Macrocell,

    /// Gzip-compressed macrocell format for more efficient storage.
    CompressedMacrocell,

    /// [Extended RLE](https://golly.sourceforge.io/Help/formats.html#rle) format:
    /// a text-based format that efficiently encodes patterns using run-length encoding.
    ///
    /// This implementation supports the extended RLE format with header and comments,
    /// but only for two-state patterns with B3/S23 rules.
    RLE,
}

#[cfg(test)]
mod tests {
    use super::*;
    const SEED: u64 = 42;
    // for simple patterns
    const HUGE_SIZE_LOG2_LIMIT: SizeLog2 = 300;
    // for conversions from/to packed cells
    const MEDIUM_SIZE_LOG2_LIMIT: SizeLog2 = 10;

    fn repeat_leaf(leaf: u64, size_log2: SizeLog2) -> Pattern {
        let mut kiv = KIVMap::new();
        let cells = if size_log2 >= 3 {
            leaf
        } else {
            let mut x = leaf.to_le_bytes();
            for i in 0..1 << size_log2 {
                x[i] &= ((1u32 << (1 << size_log2)) - 1) as u8;
            }
            for i in (1 << size_log2)..8 {
                x[i] = 0;
            }
            u64::from_le_bytes(x)
        };
        let mut node = kiv.find_or_create_node(PatternNode::Leaf(cells));
        for _ in 3..size_log2 {
            node = kiv.find_or_create_node(PatternNode::Node {
                nw: node,
                ne: node,
                sw: node,
                se: node,
            });
        }
        Pattern {
            root: node,
            size_log2,
            kiv,
            blank_nodes: vec![],
        }
    }

    #[test]
    fn test_population_blank() {
        for size_log2 in 0..HUGE_SIZE_LOG2_LIMIT {
            // all cells are dead
            let pattern = repeat_leaf(0, size_log2);
            assert_eq!(pattern.population(), BigInt::ZERO);
        }
    }

    #[test]
    fn test_population_sparse() {
        for size_log2 in 0..HUGE_SIZE_LOG2_LIMIT {
            // one alive cell per leaf
            let pattern = repeat_leaf(1, size_log2);
            assert_eq!(
                pattern.population(),
                BigInt::from(1u64) << (size_log2.max(3) - 3) * 2
            );
        }
    }

    #[test]
    fn test_population_full() {
        for size_log2 in 0..HUGE_SIZE_LOG2_LIMIT {
            // all cells are alive
            let pattern = repeat_leaf(u64::MAX, size_log2);
            assert_eq!(pattern.population(), BigInt::from(1u64) << (size_log2 * 2));
        }
    }

    #[test]
    fn test_metafy_glider() {
        // Create a glider pattern (4x4)
        let glider = Pattern::from_rle(b"x = 3, y = 3, rule = B3/S23\nbo$2bo$3o!").unwrap();

        // Create metacells where ON is a smaller glider and OFF is empty
        let off_metacell = repeat_leaf(0, 3); // All dead cells
        let on_metacell =
            Pattern::from_packed_cells(&[0b00100000, 0b00010000, 0b01110000, 0, 0, 0, 0, 0])
                .unwrap();

        // Metafy with level 1
        let metafied = glider.metafy(&[off_metacell, on_metacell], 1).unwrap();

        // The metafied pattern should have 5 gliders (one for each ON cell in the original glider)
        assert_eq!(metafied.size_log2, 5);
        assert_eq!(metafied.population(), BigInt::from(5 * 5)); // 5 gliders with 5 cells each
    }

    #[test]
    fn test_metafy_simple() {
        // Create a simple pattern (2x2)
        let pattern = Pattern::from_packed_cells(&[0b11, 0b10]).unwrap();

        // Create simple metacells (8x8)
        let off_metacell = repeat_leaf(1, 3); // 1 alive cell
        let on_metacell = repeat_leaf(u64::MAX, 3); // All alive cells

        let mut off_population = BigInt::from(0);
        let mut on_population = BigInt::from(1);
        let mut level = 0;
        let size_log2 = |level: u32| 1 + level * 3;
        while size_log2(level) < HUGE_SIZE_LOG2_LIMIT {
            let metafied = pattern
                .metafy(&[off_metacell.clone(), on_metacell.clone()], level)
                .unwrap();

            assert_eq!(metafied.size_log2, size_log2(level));
            assert_eq!(
                metafied.population(),
                off_population.clone() + on_population.clone() * 3
            );
            (off_population, on_population) = (
                off_population * 63 + on_population.clone(),
                on_population * 64,
            );
            level += 1;
        }
    }

    #[test]
    fn test_metafy_random() {
        for pattern_size_log2 in 0..6 {
            let pattern_total_count = BigInt::from(1) << pattern_size_log2 * 2;
            let pattern = Pattern::random(pattern_size_log2, Some(SEED)).unwrap();
            for metacell_size_log2 in 3..6 {
                let metacell_total_count = BigInt::from(1) << metacell_size_log2 * 2;
                let metacells =
                    [1, 2].map(|x| Pattern::random(metacell_size_log2, Some(SEED + x)).unwrap());

                let mut populations = [BigInt::from(0), BigInt::from(1)];
                let mut total_count = BigInt::from(1);
                for level in 0..10 {
                    let metafied = pattern.metafy(&metacells, level).unwrap();

                    assert_eq!(
                        metafied.size_log2,
                        pattern_size_log2 + metacell_size_log2 * level
                    );
                    assert_eq!(
                        metafied.population(),
                        pattern.population() * &populations[1]
                            + (&pattern_total_count - pattern.population()) * &populations[0]
                    );
                    populations = [
                        &populations[0] * metacells[1].population()
                            + (&total_count - &populations[0]) * &metacells[0].population(),
                        &populations[1] * metacells[1].population()
                            + (&total_count - &populations[1]) * &metacells[0].population(),
                    ];
                    total_count *= &metacell_total_count;
                }
            }
        }
    }

    #[test]
    fn test_expand() {
        let mut pattern = repeat_leaf(1, 0);
        for size_log2 in 0..HUGE_SIZE_LOG2_LIMIT {
            pattern.expand(size_log2);
            assert_eq!(pattern.size_log2, size_log2);
            assert_eq!(pattern.population(), BigInt::from(1));
        }
    }

    #[test]
    fn test_packed_cells_roundtrip_blank() {
        for size_log2 in 0..MEDIUM_SIZE_LOG2_LIMIT {
            let pattern = repeat_leaf(0, size_log2);
            let data = pattern.to_packed_cells().unwrap();
            let deserialized = Pattern::from_packed_cells(&data).unwrap();

            assert_eq!(pattern.size_log2, deserialized.size_log2);
            assert_eq!(pattern.population(), deserialized.population());
            assert_eq!(pattern.hash(), deserialized.hash());
        }
    }

    #[test]
    fn test_packed_cells_roundtrip_sparse() {
        for size_log2 in 0..MEDIUM_SIZE_LOG2_LIMIT {
            let pattern = repeat_leaf(1, size_log2);
            let data = pattern.to_packed_cells().unwrap();
            let deserialized = Pattern::from_packed_cells(&data).unwrap();

            assert_eq!(pattern.size_log2, deserialized.size_log2);
            assert_eq!(pattern.population(), deserialized.population());
            assert_eq!(pattern.hash(), deserialized.hash());
        }
    }

    #[test]
    fn test_packed_cells_roundtrip_full() {
        for size_log2 in 0..MEDIUM_SIZE_LOG2_LIMIT {
            let pattern = repeat_leaf(u64::MAX, size_log2);
            let data = pattern.to_packed_cells().unwrap();
            let deserialized = Pattern::from_packed_cells(&data).unwrap();

            assert_eq!(pattern.size_log2, deserialized.size_log2);
            assert_eq!(pattern.population(), deserialized.population());
            assert_eq!(pattern.hash(), deserialized.hash());
        }
    }

    #[test]
    fn test_packed_cells_roundtrip_random() {
        for size_log2 in 0..MEDIUM_SIZE_LOG2_LIMIT {
            let pattern = Pattern::random(size_log2, Some(SEED)).unwrap();
            let data = pattern.to_packed_cells().unwrap();
            let deserialized = Pattern::from_packed_cells(&data).unwrap();

            assert_eq!(pattern.size_log2, deserialized.size_log2);
            assert_eq!(pattern.population(), deserialized.population());
            assert_eq!(pattern.hash(), deserialized.hash());
        }
    }

    #[test]
    fn test_macrocell_roundtrip_sparse() {
        for size_log2 in 0..HUGE_SIZE_LOG2_LIMIT {
            let pattern = repeat_leaf(1, size_log2);
            let data = pattern.to_macrocell().unwrap();
            let deserialized = Pattern::from_macrocell(&data).unwrap();

            assert_eq!(pattern.size_log2.max(3), deserialized.size_log2);
            assert_eq!(pattern.population(), deserialized.population());
            assert_eq!(pattern.hash(), deserialized.hash());
        }
    }

    #[test]
    fn test_macrocell_roundtrip_full() {
        for size_log2 in 0..HUGE_SIZE_LOG2_LIMIT {
            let pattern = repeat_leaf(u64::MAX, size_log2);
            let data = pattern.to_macrocell().unwrap();
            let deserialized = Pattern::from_macrocell(&data).unwrap();

            assert_eq!(pattern.size_log2.max(3), deserialized.size_log2);
            assert_eq!(pattern.population(), deserialized.population());
            assert_eq!(pattern.hash(), deserialized.hash());
        }
    }

    #[test]
    fn test_macrocell_roundtrip_random() {
        for size_log2 in 0..MEDIUM_SIZE_LOG2_LIMIT {
            let pattern = Pattern::random(size_log2, Some(SEED)).unwrap();
            // Be careful: blank patterns are not supported
            let data = pattern.to_macrocell().unwrap();
            let deserialized = Pattern::from_macrocell(&data).unwrap();

            assert_eq!(pattern.size_log2.max(3), deserialized.size_log2);
            assert_eq!(pattern.population(), deserialized.population());
            assert_eq!(pattern.hash(), deserialized.hash());
        }
    }

    #[test]
    fn test_compressed_macrocell_roundtrip_random() {
        for size_log2 in 0..MEDIUM_SIZE_LOG2_LIMIT {
            let pattern = Pattern::random(size_log2, Some(SEED)).unwrap();
            // Be careful: blank patterns are not supported
            let data = pattern.to_compressed_macrocell().unwrap();
            let deserialized = Pattern::from_compressed_macrocell(&data).unwrap();

            assert_eq!(pattern.size_log2.max(3), deserialized.size_log2);
            assert_eq!(pattern.population(), deserialized.population());
            assert_eq!(pattern.hash(), deserialized.hash());
        }
    }

    #[test]
    fn test_rle_roundtrip_random() {
        for size_log2 in 0..MEDIUM_SIZE_LOG2_LIMIT {
            let pattern = Pattern::random(size_log2, Some(SEED)).unwrap();
            // Be careful: empty rows/columns at the top/left of the original pattern are trimmed
            let data = pattern.to_rle().unwrap();
            let deserialized = Pattern::from_rle(&data).unwrap();

            assert_eq!(pattern.size_log2, deserialized.size_log2);
            assert_eq!(pattern.population(), deserialized.population());
            assert_eq!(pattern.hash(), deserialized.hash());
        }
    }

    #[test]
    fn test_conversions_glider() {
        let packed = Pattern::from_packed_cells(&[0b010, 0b100, 0b111, 0]).unwrap();
        let rle = Pattern::from_rle(b"x = 3, y = 3, rule = B3/S23\nbo$2bo$3o!").unwrap();
        let macrocell = Pattern::from_macrocell(b"[M2]\n#R B3/S23\n.*.$..*$***$").unwrap();

        assert_eq!(packed.hash(), rle.hash());
        assert_eq!(packed.hash(), macrocell.hash());
    }
}
