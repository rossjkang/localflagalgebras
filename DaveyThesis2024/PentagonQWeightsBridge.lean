import DaveyThesis2024.PartitionExp.Combine

/-!
# The enumerator agrees with the `Finset` shape

Split from `PentagonQRooted` so that proof work there does not re-elaborate
this check, which ranges over 9295 x (8^4 + 2*8^5) maps.

**Since 2026-10-05 the check is partitioned.**  As a single `native_decide` it
was too slow to fit a CI ceiling.  Split into four independent chunks
(`PartitionExp.Chunk0..3`) Lake builds them concurrently, so a cold build pays
roughly one chunk rather than all four.  Measured figures belong downstream,
in `PentagonQAssembleA`.

The theorem below is a restatement of
`PartitionExp.rootedCount_eq_cRootedCount_partitioned`, which has the same type
and the same axioms as the single-`native_decide` version it replaces; see that
module for how the chunks are recombined and for what the evidence actually is.
-/

namespace Davey2024
namespace PentagonQWeightsBridge

open Davey2024.PentagonQBasis Davey2024.PentagonQWeights Davey2024.PentagonQRooted

/-- **The enumerator computes the `Finset` count**, at every basis flag and for
each of the three types.  This is what `O_Q_weight_eq_combinatorial` needed and
did not have: its `nᵢ` are now equal to a count over the same function space
`cInducedCount` ranges over, which `cInducedCount_eq_genInducedCount'` bridges
to `genInducedCount`.

Proved in four parallel chunks; see the module docstring. -/
theorem rootedCount_eq_cRootedCount :
    ∀ k : Fin basisSize,
      rootedCount (flagBasisCGraph k) tau1 = cRootedCount (patC tau1 4) (flagBasisCGraph k) ∧
      rootedCount (flagBasisCGraph k) tau2 = cRootedCount (patC tau2 5) (flagBasisCGraph k) ∧
      rootedCount (flagBasisCGraph k) tau3 = cRootedCount (patC tau3 5) (flagBasisCGraph k) :=
  PartitionExp.rootedCount_eq_cRootedCount_partitioned

#print axioms rootedCount_eq_cRootedCount

end PentagonQWeightsBridge
end Davey2024
