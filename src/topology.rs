/// Describes the strategy of updating the field.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Topology {
    /// Opposite bounds of the field are stitched together.
    Torus,
    /// Field is unbounded and can grow infinitely.
    Unbounded,
}
