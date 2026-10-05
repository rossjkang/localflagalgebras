import DaveyThesis2024.PentagonQComplete
import DaveyThesis2024.PentagonQDistinctCheck
import DaveyThesis2024.PentagonQPatFacts

/-!
# The two `nzIdx` are the same list

Finding G of the second seam audit.  `PentagonQComplete.nzIdx` filters on
`4 * n1 k + n2 k + 2 * n3 k != 0`; `PentagonQDistinctCheck.nzIdx` filters on
`muW k != 0`, with `muW` that same expression.  C2 hands out membership in the
first, item D's distinctness is about the second, and **neither module imports
the other**, so nothing said they agree.

They are definitionally equal, so this is `rfl` — but stating it is what stops
the two drifting apart silently under a later edit.  This module is also the
first thing to import both, so building it re-checks
`basis_nz_pairwise_distinct` against the `PentagonQDistinct` that fix B changed.
-/

namespace Davey2024
namespace PentagonQNzIdx

/-- **G.**  The two definitions of "the 69" coincide. -/
theorem nzIdx_eq : PentagonQComplete.nzIdx = PentagonQDistinctCheck.nzIdx := rfl

/-! ## At most one of the 69 can match

The regrouping needs each 8-subset to contribute to **one** term, so two of the
69 must never share a flag class.  Item D's enumeration says their permutation
counts vanish pairwise; `genClass_ne_of_cPermCount_eq_zero` (fix B) turns that
into distinct classes, using the basis flags' symmetry and irreflexivity
(finding H). -/

theorem nz_class_injective {j k : Fin PentagonQBasis.basisSize}
    (hj : j ∈ PentagonQComplete.nzIdx) (hk : k ∈ PentagonQComplete.nzIdx)
    (h : GenFlagClass.mk (PentagonQBasis.flagBasisCGraph j).toGenFlag
       = GenFlagClass.mk (PentagonQBasis.flagBasisCGraph k).toGenFlag) : j = k := by
  by_contra hne
  have hall := PentagonQDistinctCheck.basis_nz_pairwise_distinct
  simp only [List.all_eq_true] at hall
  rw [nzIdx_eq] at hj hk
  have hjk := hall j hj k hk
  simp only [Bool.or_eq_true, beq_iff_eq] at hjk
  rcases hjk with h1 | h2
  · exact hne h1
  · exact PentagonQDistinct.genClass_ne_of_cPermCount_eq_zero _ _
      (PentagonQPatFacts.basis_adj_symm j) (PentagonQPatFacts.basis_adj_irrefl j)
      (PentagonQPatFacts.basis_adj_symm k) (PentagonQPatFacts.basis_adj_irrefl k)
      h2 h

#print axioms nz_class_injective
#print axioms nzIdx_eq

end PentagonQNzIdx
end Davey2024
