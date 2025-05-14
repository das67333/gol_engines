use super::{
    BlankNodes, MemoryManager, NodeIdx, PrefetchedNode, QuadTreeNode, LEAF_SIZE, LEAF_SIZE_LOG2,
};
use crate::{GoLEngine, Pattern, PatternNode, Topology};
use ahash::AHashMap as HashMap;
use anyhow::{anyhow, Result};
use num_bigint::BigInt;

/// Implementation of [HashLife algorithm](https://conwaylife.com/wiki/HashLife)
pub struct HashLifeEngineSync<Extra> {
    pub(super) size_log2: u32,
    pub(super) root: NodeIdx,
    pub(super) mem: MemoryManager<Extra>,
    pub(super) generations_per_update_log2: Option<u32>,
    pub(super) topology: Topology,
    pub(super) blank_nodes: BlankNodes,
}

impl<Extra: Clone + Default> HashLifeEngineSync<Extra> {
    fn update_row(row_prev: u16, row_curr: u16, row_next: u16) -> u16 {
        let b = row_prev;
        let a = b << 1;
        let c = b >> 1;
        let i = row_curr;
        let h = i << 1;
        let d = i >> 1;
        let f = row_next;
        let g = f << 1;
        let e = f >> 1;

        let ab0 = a ^ b;
        let ab1 = a & b;
        let cd0 = c ^ d;
        let cd1 = c & d;

        let ef0 = e ^ f;
        let ef1 = e & f;
        let gh0 = g ^ h;
        let gh1 = g & h;

        let ad0 = ab0 ^ cd0;
        let ad1 = (ab1 ^ cd1) ^ (ab0 & cd0);
        let ad2 = ab1 & cd1;

        let eh0 = ef0 ^ gh0;
        let eh1 = (ef1 ^ gh1) ^ (ef0 & gh0);
        let eh2 = ef1 & gh1;

        let ah0 = ad0 ^ eh0;
        let xx = ad0 & eh0;
        let yy = ad1 ^ eh1;
        let ah1 = xx ^ yy;
        let ah23 = (ad2 | eh2) | (ad1 & eh1) | (xx & yy);
        let z = !ah23 & ah1;
        let i2 = !ah0 & z;
        let i3 = ah0 & z;
        (i & i2) | i3
    }

    /// `nw`, `ne`, `sw`, `se` must be leaves
    pub(super) fn update_leaves(
        &self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
        steps: u64,
    ) -> NodeIdx {
        let [nw, ne, sw, se] = [nw, ne, sw, se].map(|x| self.mem.get(x).leaf_cells());

        let mut src = [0; 16];
        for i in 0..8 {
            src[i] = u16::from_le_bytes([nw[i], ne[i]]);
            src[i + 8] = u16::from_le_bytes([sw[i], se[i]]);
        }
        let mut dst = [0; 16];

        for t in 1..=steps as usize {
            for y in t..16 - t {
                dst[y] = Self::update_row(src[y - 1], src[y], src[y + 1]);
            }
            std::mem::swap(&mut src, &mut dst);
        }

        let arr: [u16; 8] = src[4..12].try_into().unwrap();
        self.mem
            .find_or_create_leaf_from_u64(u64::from_le_bytes(arr.map(|x| (x >> 4) as u8)))
    }

    fn nine_children_disjoint(
        &self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
        size_log2: u32,
    ) -> [NodeIdx; 9] {
        let [[nwnw, nwne, nwsw, nwse], [nenw, nene, nesw, nese], [swnw, swne, swsw, swse], [senw, sene, sesw, sese]] =
            [nw, ne, sw, se].map(|x| self.mem.get(x).parts().map(|y| self.mem.get(y)));

        [
            [nwnw, nwne, nwsw, nwse],
            [nwne, nenw, nwse, nesw],
            [nenw, nene, nesw, nese],
            [nwsw, nwse, swnw, swne],
            [nwse, nesw, swne, senw],
            [nesw, nese, senw, sene],
            [swnw, swne, swsw, swse],
            [swne, senw, swse, sesw],
            [senw, sene, sesw, sese],
        ]
        .map(|[nw, ne, sw, se]| {
            if size_log2 >= LEAF_SIZE_LOG2 + 2 {
                self.mem.find_or_create_node(nw.se, ne.sw, sw.ne, se.nw)
            } else {
                self.mem.find_or_create_leaf_from_parts(
                    nw.leaf_se(),
                    ne.leaf_sw(),
                    sw.leaf_ne(),
                    se.leaf_nw(),
                )
            }
        })
    }

    #[inline]
    pub(super) fn four_children_overlapping(&self, arr: &[NodeIdx; 9]) -> [NodeIdx; 4] {
        [
            self.mem.find_or_create_node(arr[0], arr[1], arr[3], arr[4]),
            self.mem.find_or_create_node(arr[1], arr[2], arr[4], arr[5]),
            self.mem.find_or_create_node(arr[3], arr[4], arr[6], arr[7]),
            self.mem.find_or_create_node(arr[4], arr[5], arr[7], arr[8]),
        ]
    }

    /// `size_log2` is related to `nw`, `ne`, `sw`, `se` and return value
    fn update_nodes_single(
        &self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
        size_log2: u32,
    ) -> NodeIdx {
        let arr9 = self.nine_children_disjoint(nw, ne, sw, se, size_log2);

        let mut arr4 = self.four_children_overlapping(&arr9);
        for x in arr4.iter_mut() {
            *x = self.update_node(*x, size_log2);
        }
        let [nw, ne, sw, se] = arr4;
        self.mem.find_or_create_node(nw, ne, sw, se)
    }

    /// `size_log2` is related to `nw`, `ne`, `sw`, `se` and return value
    fn update_nodes_double(
        &self,
        nw: NodeIdx,
        ne: NodeIdx,
        sw: NodeIdx,
        se: NodeIdx,
        size_log2: u32,
    ) -> NodeIdx {
        let [nw_, ne_, sw_, se_] = [nw, ne, sw, se].map(|x| self.mem.get(x));

        // First stage
        let p11 = PrefetchedNode::new(&self.mem, nw_.se, ne_.sw, sw_.ne, se_.nw, size_log2);
        let p01 = PrefetchedNode::new(&self.mem, nw_.ne, ne_.nw, nw_.se, ne_.sw, size_log2);
        let p12 = PrefetchedNode::new(&self.mem, ne_.sw, ne_.se, se_.nw, se_.ne, size_log2);
        let p10 = PrefetchedNode::new(&self.mem, nw_.sw, nw_.se, sw_.nw, sw_.ne, size_log2);
        let p21 = PrefetchedNode::new(&self.mem, sw_.ne, se_.nw, sw_.se, se_.sw, size_log2);

        let t00 = self.update_node(nw, size_log2);
        let t01 = self.update_node(p01.find_or_create(), size_log2);
        let t02 = self.update_node(ne, size_log2);
        let t12 = self.update_node(p12.find_or_create(), size_log2);
        let t11 = self.update_node(p11.find_or_create(), size_log2);
        let t10 = self.update_node(p10.find_or_create(), size_log2);
        let t20 = self.update_node(sw, size_log2);
        let t21 = self.update_node(p21.find_or_create(), size_log2);
        let t22 = self.update_node(se, size_log2);

        // Second stage
        let pse = PrefetchedNode::new(&self.mem, t11, t12, t21, t22, size_log2);
        let psw = PrefetchedNode::new(&self.mem, t10, t11, t20, t21, size_log2);
        let pnw = PrefetchedNode::new(&self.mem, t00, t01, t10, t11, size_log2);
        let pne = PrefetchedNode::new(&self.mem, t01, t02, t11, t12, size_log2);
        let t_se = self.update_node(pse.find_or_create(), size_log2);
        let t_sw = self.update_node(psw.find_or_create(), size_log2);
        let t_nw = self.update_node(pnw.find_or_create(), size_log2);
        let t_ne = self.update_node(pne.find_or_create(), size_log2);
        self.mem.find_or_create_node(t_nw, t_ne, t_sw, t_se)
    }

    /// Recursively updates nodes in graph.
    ///
    /// `size_log2` is related to `node`
    #[inline]
    pub(super) fn update_node(&self, node: NodeIdx, size_log2: u32) -> NodeIdx {
        fn inner<Extra: Clone + Default>(
            this: &HashLifeEngineSync<Extra>,
            n: &mut QuadTreeNode<Extra>,
            size_log2: u32,
        ) -> NodeIdx {
            let generations_log2 = this.generations_per_update_log2.unwrap();
            let both_stages = generations_log2 + 2 >= size_log2;
            let cache = if size_log2 == LEAF_SIZE_LOG2 + 1 {
                let steps = if both_stages {
                    LEAF_SIZE / 2
                } else {
                    1 << generations_log2
                };
                this.update_leaves(n.nw, n.ne, n.sw, n.se, steps)
            } else if both_stages {
                this.update_nodes_double(n.nw, n.ne, n.sw, n.se, size_log2 - 1)
            } else {
                this.update_nodes_single(n.nw, n.ne, n.sw, n.se, size_log2 - 1)
            };
            n.cache = cache;
            n.has_cache = true;
            cache
        }

        let n = self.mem.get_mut(node);
        if n.has_cache {
            return n.cache;
        }
        inner(self, n, size_log2)
    }

    /// Add a frame around the field: if `self.topology` is Unbounded, frame is blank,
    /// and if `self.topology` is Torus, frame mirrors the field.
    /// The field becomes two times bigger.
    pub(super) fn with_frame(&mut self, idx: NodeIdx, size_log2: u32) -> NodeIdx {
        let n = self.mem.get(idx);
        let b = self.blank_nodes.get(size_log2 - 1, &self.mem);
        let [nw, ne, sw, se] = match self.topology {
            Topology::Torus => [self.mem.find_or_create_node(n.se, n.sw, n.ne, n.nw); 4],
            Topology::Unbounded => [
                self.mem.find_or_create_node(b, b, b, n.nw),
                self.mem.find_or_create_node(b, b, n.ne, b),
                self.mem.find_or_create_node(b, n.sw, b, b),
                self.mem.find_or_create_node(n.se, b, b, b),
            ],
        };
        self.mem.find_or_create_node(nw, ne, sw, se)
    }

    /// Remove a frame around the field, making it two times smaller.
    pub(super) fn without_frame(&self, idx: NodeIdx) -> NodeIdx {
        let [nw, ne, sw, se] = self.mem.get(idx).parts().map(|x| self.mem.get(x));
        self.mem.find_or_create_node(nw.se, ne.sw, sw.ne, se.nw)
    }

    pub(super) fn has_blank_frame(&mut self) -> bool {
        if self.size_log2 <= LEAF_SIZE_LOG2 + 1 {
            return false;
        }

        let b = self.blank_nodes.get(self.size_log2 - 2, &self.mem);

        let root = self.mem.get(self.root);
        let [nw, ne, sw, se] = [
            self.mem.get(root.nw),
            self.mem.get(root.ne),
            self.mem.get(root.sw),
            self.mem.get(root.se),
        ];
        let frame_parts = [
            nw.sw, nw.nw, nw.ne, ne.nw, ne.ne, ne.se, se.ne, se.se, se.sw, sw.se, sw.sw, sw.nw,
        ];
        frame_parts.iter().all(|&x| x == b)
    }

    pub(super) fn add_frame(&mut self, dx: &mut BigInt, dy: &mut BigInt) {
        self.root = self.with_frame(self.root, self.size_log2);
        *dx += BigInt::from(1) << (self.size_log2 - 1);
        *dy += BigInt::from(1) << (self.size_log2 - 1);
        self.size_log2 += 1;
    }

    pub(super) fn pop_frame(&mut self, dx: &mut BigInt, dy: &mut BigInt) {
        self.root = self.without_frame(self.root);
        *dx -= BigInt::from(1) << (self.size_log2 - 2);
        *dy -= BigInt::from(1) << (self.size_log2 - 2);
        self.size_log2 -= 1;
    }

    pub(super) fn from_pattern_recursive(
        idx: u32,
        pattern: &Pattern,
        mem: &MemoryManager<Extra>,
        cache: &mut HashMap<u32, NodeIdx>,
    ) -> NodeIdx {
        if let Some(&cached) = cache.get(&idx) {
            return cached;
        }
        let result = match pattern.get_node(idx) {
            PatternNode::Leaf(cells) => mem.find_or_create_leaf_from_u64(*cells),
            PatternNode::Node { nw, ne, sw, se } => mem.find_or_create_node(
                Self::from_pattern_recursive(*nw, pattern, mem, cache),
                Self::from_pattern_recursive(*ne, pattern, mem, cache),
                Self::from_pattern_recursive(*sw, pattern, mem, cache),
                Self::from_pattern_recursive(*se, pattern, mem, cache),
            ),
        };
        cache.insert(idx, result);
        result
    }
}

impl<Extra: Clone + Default> GoLEngine for HashLifeEngineSync<Extra> {
    fn new(mem_limit_mib: u32) -> Self {
        let nodes =
            ((mem_limit_mib as u64) << 20) / std::mem::size_of::<QuadTreeNode<Extra>>() as u64;
        // previous power of two
        let cap_log2 = (nodes / 2 + 1)
            .checked_next_power_of_two()
            .unwrap()
            .trailing_zeros();
        let mem = MemoryManager::with_capacity(cap_log2);
        Self {
            size_log2: LEAF_SIZE_LOG2,
            root: mem.find_or_create_leaf_from_u64(0),
            mem,
            generations_per_update_log2: None,
            topology: Topology::Unbounded,
            blank_nodes: BlankNodes::new(),
        }
    }

    fn load_pattern(&mut self, pattern: &Pattern, topology: Topology) -> Result<()> {
        let size_log2 = pattern.get_size_log2();
        if size_log2 < LEAF_SIZE_LOG2 {
            return Err(anyhow!("Pattern is too small"));
        }
        self.size_log2 = size_log2;
        self.mem.clear();
        self.blank_nodes.clear();
        let mut cache = HashMap::new();
        self.root =
            Self::from_pattern_recursive(pattern.get_root(), pattern, &self.mem, &mut cache);
        self.generations_per_update_log2 = None;
        self.topology = topology;
        Ok(())
    }

    fn current_state(&self) -> Pattern {
        fn inner<Extra: Clone + Default>(
            idx: NodeIdx,
            size_log2: u32,
            mem: &MemoryManager<Extra>,
            pattern: &mut Pattern,
            cache: &mut HashMap<NodeIdx, u32>,
        ) -> u32 {
            if let Some(&cached) = cache.get(&idx) {
                return cached;
            }
            let n = mem.get(idx);
            let result = if size_log2 == LEAF_SIZE_LOG2 {
                let cells = u64::from_le_bytes(n.leaf_cells());
                pattern.find_or_create_node(PatternNode::Leaf(cells))
            } else {
                let [nw, ne, sw, se] = n
                    .parts()
                    .map(|x| inner(x, size_log2 - 1, mem, pattern, cache));
                pattern.find_or_create_node(PatternNode::Node { nw, ne, sw, se })
            };
            cache.insert(idx, result);
            result
        }

        let mut cache = HashMap::new();
        let mut pattern = Pattern::default();
        let root = inner(
            self.root,
            self.size_log2,
            &self.mem,
            &mut pattern,
            &mut cache,
        );
        unsafe { pattern.change_root(root, self.size_log2) };
        pattern
    }

    fn update(&mut self, generations_log2: u32) -> Result<[BigInt; 2]> {
        if let Some(cached_generations_log2) = self.generations_per_update_log2 {
            if cached_generations_log2 != generations_log2 {
                self.run_gc();
            }
        }
        let backup = self.current_state();
        self.generations_per_update_log2 = Some(generations_log2);

        let frames_cnt = (generations_log2 + 2).max(self.size_log2 + 1) - self.size_log2;
        let (mut dx, mut dy) = (BigInt::ZERO, BigInt::ZERO);
        for _ in 0..frames_cnt {
            self.add_frame(&mut dx, &mut dy);
        }

        self.root = self.update_node(self.root, self.size_log2);
        if self.mem.poisoned() {
            self.load_pattern(&backup, self.topology)?;
            return Err(anyhow!(
                "HashLifeSync: overfilled MemoryManager, try smaller step"
            ));
        }

        self.size_log2 -= 1;
        dx -= BigInt::from(1) << (self.size_log2 - 1);
        dy -= BigInt::from(1) << (self.size_log2 - 1);

        match self.topology {
            Topology::Torus => {
                for _ in 0..frames_cnt - 1 {
                    self.pop_frame(&mut dx, &mut dy);
                }
            }
            Topology::Unbounded => {
                while self.has_blank_frame() {
                    self.pop_frame(&mut dx, &mut dy);
                }
            }
        }

        Ok([dx, dy])
    }

    fn run_gc(&mut self) {
        let pattern = self.current_state();
        self.mem.clear();
        self.blank_nodes.clear();
        let mut cache = HashMap::new();
        self.root =
            Self::from_pattern_recursive(pattern.get_root(), &pattern, &self.mem, &mut cache);
        self.generations_per_update_log2 = None;
    }

    fn bytes_total(&self) -> usize {
        self.mem.bytes_total()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const SEED: u64 = 42;

    #[test]
    fn test_pattern_roundtrip() {
        for size_log2 in 3..10 {
            let original = Pattern::random(size_log2, Some(SEED)).unwrap();
            let mut engine = HashLifeEngineSync::<()>::new(1);
            engine.load_pattern(&original, Topology::Unbounded).unwrap();
            let converted = engine.current_state();

            assert_eq!(
                original.hash(),
                converted.hash(),
                "Pattern roundtrip failed for size 2^{}",
                size_log2
            );
        }
    }
}
