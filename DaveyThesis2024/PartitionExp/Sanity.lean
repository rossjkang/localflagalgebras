import DaveyThesis2024.PentagonQRooted

/-! Shared definitions for the partitioned bridge check.

`ok` is the per-flag predicate of
`PentagonQWeightsBridge.rootedCount_eq_cRootedCount`, as a `Bool`; `chunkOK`
is its conjunction over a range of basis indices. `Chunk0..3` discharge four
ranges by `native_decide` and `Combine` recombines them.

`sanity` below covers 8 flags and is kept as a fast smoke check: if the chunk
shape ever stops elaborating, this fails in seconds rather than in hours. -/

namespace Davey2024.PartitionExp
open Davey2024.PentagonQBasis Davey2024.PentagonQWeights Davey2024.PentagonQRooted

/-- The bridge predicate at one basis index, as a `Bool`. -/
def ok (k : Fin basisSize) : Bool :=
  let g := flagBasisCGraph k
  (rootedCount g tau1 == cRootedCount (patC tau1 4) g) &&
  (rootedCount g tau2 == cRootedCount (patC tau2 5) g) &&
  (rootedCount g tau3 == cRootedCount (patC tau3 5) g)

/-- All indices in `[lo, lo+len)` that are in range. -/
def chunkOK (lo len : Nat) : Bool :=
  (List.range' lo len).all (fun k =>
    if h : k < basisSize then ok ⟨k, h⟩ else true)

set_option linter.style.nativeDecide false in
theorem sanity : chunkOK 0 8 = true := by native_decide

end Davey2024.PartitionExp
