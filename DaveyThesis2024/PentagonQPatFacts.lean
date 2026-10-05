import DaveyThesis2024.PentagonQRooted

/-!
# The τ patterns are symmetric and loopless

`comap_iff_of_injective` — obligation (a0)'s lemma, which turns a
`GenInducedEmbedding` into elementwise colour and adjacency equations — asks that
both graphs be symmetric and irreflexive.  For `patC tauᵢ` both hold by
construction, and neither was proved; the seam audit recorded it as finding D.

**Why this is its own module.**  `decide` cannot do it: `patC` reads its
adjacency out of an `Array` built by `Array.map` over `Array.range`, and the
kernel does not reduce that, so the `Decidable` instance gets stuck rather than
answering.  `native_decide` evaluates it instead — which adds `ofReduceBool` and
`trustCompiler`, axioms `pentagon_bound_full` already carries but
`PentagonQRelabel` does not, so these live here and that file stays kernel-only.
-/

namespace Davey2024
namespace PentagonQPatFacts

open Davey2024.PentagonQBasis Davey2024.PentagonQWeights Davey2024.PentagonQRooted

set_option linter.style.nativeDecide false in
theorem patC_tau1_symm : ∀ i j, (patC tau1 4).adj i j = (patC tau1 4).adj j i := by
  native_decide

set_option linter.style.nativeDecide false in
theorem patC_tau1_irrefl : ∀ i, (patC tau1 4).adj i i = false := by native_decide

set_option linter.style.nativeDecide false in
theorem patC_tau2_symm : ∀ i j, (patC tau2 5).adj i j = (patC tau2 5).adj j i := by
  native_decide

set_option linter.style.nativeDecide false in
theorem patC_tau2_irrefl : ∀ i, (patC tau2 5).adj i i = false := by native_decide

set_option linter.style.nativeDecide false in
theorem patC_tau3_symm : ∀ i j, (patC tau3 5).adj i j = (patC tau3 5).adj j i := by
  native_decide

set_option linter.style.nativeDecide false in
theorem patC_tau3_irrefl : ∀ i, (patC tau3 5).adj i i = false := by native_decide

/-! ## The basis flags, likewise

Finding H.  `genClass_eq_of_cPermCount_ne_zero` and every use of
`basis_nz_pairwise_distinct` need the basis flags symmetric and irreflexive, and
nothing proved it.  The four such facts in the repository are for
`flagBasisCGraph4` — the **SEC four-vertex** basis — so they look like a hit and
are about a different object.

Same reason for `native_decide` as above: the decoder reads adjacency out of a
packed hex string. -/

set_option linter.style.nativeDecide false in
theorem basis_adj_symm :
    ∀ k : Fin basisSize, ∀ i j, (flagBasisCGraph k).adj i j = (flagBasisCGraph k).adj j i := by
  native_decide

set_option linter.style.nativeDecide false in
theorem basis_adj_irrefl :
    ∀ k : Fin basisSize, ∀ i, (flagBasisCGraph k).adj i i = false := by
  native_decide

#print axioms basis_adj_symm
#print axioms basis_adj_irrefl

end PentagonQPatFacts
end Davey2024
