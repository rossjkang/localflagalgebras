import DaveyThesis2024.PentagonQDistinct
import DaveyThesis2024.PentagonQWeights

/-!
# Item D, the enumeration: the 69 contributing flags are pairwise distinct

`PentagonQDistinct.cInducedCount_eq_cPermCount` cuts the function space down to
the permutations, which is what brings this within reach: `8⁸ = 1.7·10⁷` maps per
pair becomes `8! = 40320`.

Costed before running.  A Python run with the same short-circuit structure
examined `9.46·10⁷` permutations over the `2346` unordered pairs in `36.6 s` and
found **no** pair admitting an isomorphism; `native_decide` at 0.3's measured
6.6x, over ordered pairs, extrapolated to roughly eight minutes.

**It took 1341 s — 22 minutes, 2.8x that.**  0.3 measured the 6.6x on `Nat` bit
operations; enumerating `Equiv.Perm (Fin 8)` allocates rather than computes, so
the true factor here is nearer 18x.  Worth carrying into any later estimate:
`native_decide`'s penalty over CPython is not one number, it depends on what the
code allocates.

**In the default build since 2026-10-01**, when `PentagonQBridge` began
importing the item-(a) proof chain; it was kept out before that.
-/

namespace Davey2024
namespace PentagonQDistinctCheck

open Davey2024.PentagonQBasis Davey2024.PentagonQWeights Davey2024.PentagonQDistinct

/-- μ, from the rooted counts rather than from the certificate. -/
def muW (k : Fin basisSize) : ℕ := 4 * n1 k + n2 k + 2 * n3 k

/-- The indices with `μ ≠ 0` — the 69. -/
def nzIdx : List (Fin basisSize) :=
  (List.finRange basisSize).filter (fun k => muW k != 0)

theorem nzIdx_length : nzIdx.length = 69 := by native_decide

/-- **D, discharged.**  No two of the 69 admit a colour- and adjacency-preserving
permutation, so their flag classes are pairwise distinct — which is what the
basis bridge needs to sum over them without double counting. -/
theorem basis_nz_pairwise_distinct :
    (nzIdx.all (fun j => nzIdx.all (fun k =>
      j == k || cPermCount (flagBasisCGraph j) (flagBasisCGraph k) == 0))) = true := by
  native_decide

end PentagonQDistinctCheck
end Davey2024
