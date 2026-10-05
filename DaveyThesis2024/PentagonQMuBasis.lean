import DaveyThesis2024.PentagonQMuFlag
import DaveyThesis2024.PentagonQWeightsBridge
import DaveyThesis2024.PentagonQPatFacts

/-!
# `μ` at a basis flag is the certificate's weight

The regrouping step needs `μ(Fⱼ) = μⱼ`, and this supplies it, through four
links — each of which exists for its own reason:

* `genRootedCount_eq_rootedCountG` moves from the flag-side count to the
  `CGraph`-side one (needs the basis flags symmetric and loopless — finding H);
* `cRootedCount_eq_genRootedCount` is obligation (a0)'s *proof* half (needs the
  τ patterns symmetric and loopless too — finding D);
* `rootedCount_eq_cRootedCount` is obligation (a0)'s `native_decide` half, and
  **this is the one place it is valid**: it is stated `∀ k : Fin basisSize`, at
  the basis flags, which is exactly what is being used here.

That last point is the whole reason `μ` was defined through `rootedCountG`
rather than `rootedCount`.  The enumerator identity is used where it holds — on
the 69 — and nowhere near an arbitrary 8-subset of a host.
-/

namespace Davey2024
namespace PentagonQMuBasis

open Davey2024.PentagonQBasis Davey2024.PentagonQWeights
open Davey2024.PentagonQRooted Davey2024.PentagonQMuFlag
open Davey2024.PentagonQIsoInvariance Davey2024.PentagonQPatFacts
open Davey2024.PentagonQWeightsBridge

/-- The τ₁ rooted count at a basis flag is `n₁`.  Extracted from `muG_flagBasis`
so that the **per-pattern** sums — which `(a2a)` and `(a2b)` consume, and which
the combined `μ` does not expose — can be built from it. -/
theorem rootedCountG_tau1_flagBasis (j : Fin basisSize) :
    rootedCountG (tauFlag tau1 4) (flagBasisCGraph j).toGenFlag
      ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩ = n1 j := by
  simp only [tauFlag]
  rw [← genRootedCount_eq_rootedCountG (patC tau1 4) (flagBasisCGraph j)
    (basis_adj_symm j) (basis_adj_irrefl j),
    ← cRootedCount_eq_genRootedCount (patC tau1 4) (flagBasisCGraph j)
      patC_tau1_symm patC_tau1_irrefl (basis_adj_symm j) (basis_adj_irrefl j),
    ← (rootedCount_eq_cRootedCount j).1]
  rfl

theorem rootedCountG_tau2_flagBasis (j : Fin basisSize) :
    rootedCountG (tauFlag tau2 5) (flagBasisCGraph j).toGenFlag
      ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩ = n2 j := by
  simp only [tauFlag]
  rw [← genRootedCount_eq_rootedCountG (patC tau2 5) (flagBasisCGraph j)
    (basis_adj_symm j) (basis_adj_irrefl j),
    ← cRootedCount_eq_genRootedCount (patC tau2 5) (flagBasisCGraph j)
      patC_tau2_symm patC_tau2_irrefl (basis_adj_symm j) (basis_adj_irrefl j),
    ← (rootedCount_eq_cRootedCount j).2.1]
  rfl

theorem rootedCountG_tau3_flagBasis (j : Fin basisSize) :
    rootedCountG (tauFlag tau3 5) (flagBasisCGraph j).toGenFlag
      ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩ = n3 j := by
  simp only [tauFlag]
  rw [← genRootedCount_eq_rootedCountG (patC tau3 5) (flagBasisCGraph j)
    (basis_adj_symm j) (basis_adj_irrefl j),
    ← cRootedCount_eq_genRootedCount (patC tau3 5) (flagBasisCGraph j)
      patC_tau3_symm patC_tau3_irrefl (basis_adj_symm j) (basis_adj_irrefl j),
    ← (rootedCount_eq_cRootedCount j).2.2]
  rfl

/-- **`μ` at a basis flag**, now assembled from the three. -/
theorem muG_flagBasis (j : Fin basisSize) :
    muG (flagBasisCGraph j).toGenFlag = 4 * n1 j + n2 j + 2 * n3 j := by
  unfold muG
  rw [rootedCountG_tau1_flagBasis, rootedCountG_tau2_flagBasis,
    rootedCountG_tau3_flagBasis]

#print axioms rootedCountG_tau1_flagBasis
#print axioms muG_flagBasis

end PentagonQMuBasis
end Davey2024
