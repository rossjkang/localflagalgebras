import DaveyThesis2024.PentagonQFamily
import DaveyThesis2024.PentagonQDistinct

/-!
# Item C2: every `μ ≠ 0` member of the family is one of the 69

With the family pinned (`PentagonQFamily.famCounts_eq`) and the function space
cut down to the permutations (`PentagonQDistinct.cInducedCount_eq_cPermCount`),
completeness over the family is a finite check: each of the `331` survivors
admits a colour- and adjacency-preserving permutation onto some basis flag of
non-zero weight.

`cPermCount ≠ 0` is exactly such a permutation, so a match is a genuine
isomorphism witness rather than an invariant coincidence.

**Costed first, after item D overran.**  A brute search over all 69 candidates
would be `331 × 69 × 8! ≈ 4.6·10⁸` permutations, and D's measured rate puts that
near an hour.  A colour-degree fingerprint is an isomorphism invariant, so a
candidate failing it cannot be the match and may be skipped — skipping can only
make the check fail, never pass falsely, so soundness does not depend on the
fingerprint being any good.
-/

namespace Davey2024
namespace PentagonQComplete

open Davey2024.PentagonQBasis Davey2024.PentagonQWeights
open Davey2024.PentagonQFamily Davey2024.PentagonQDistinct

/-- The indices of non-zero weight — the 69. -/
def nzIdx : List (Fin basisSize) :=
  (List.finRange basisSize).filter (fun k =>
    4 * n1 k + n2 k + 2 * n3 k != 0)

/-- Sorted `(colour, degree)` pairs: an isomorphism invariant, used only to skip
candidates that cannot match. -/
def fingerprint (g : CGraph 8) : List (Nat × Nat) :=
  ((List.finRange 8).map (fun v =>
    ((g.col v).val, ((List.finRange 8).filter (fun u => g.adj v u)).length))).mergeSort
    (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2))

/-- Every family member that is triangle-free and black-independent admits a
colour- and adjacency-preserving permutation onto one of the 69 basis flags of
non-zero weight.

**`μ ≠ 0` is deliberately absent from the hypothesis**, and that is what makes
C3 work.  `rootedCount_eq_cRootedCount` — obligation (a0) — is stated only at the
9295 basis flags, which is all obligation (b) needed; the graph C3 hands this
theorem comes from an 8-subset of an abstract host and is not a basis flag, so
`μ ≠ 0` could not be discharged there without proving the `embeds` enumerator
correct in general.

It does not have to be.  `μ` is automatic on the family: every member carries its
own τ-pattern at `0 … k-1` with vertex `0` joined to everything outside, which is
itself a rooted embedding, so the corresponding `nᵢ ≥ 1`.  Measured: of the 1728
triangle-free members **none** has `μ = 0`, and the drop to 331 is entirely
black-independence.  So the weaker hypothesis is the same statement, and it asks
only for the two predicates `PentagonQRelabel` transports.

**Stated as nested `List.all`, not as an `Id.run do` accumulator.**  The first
version was the latter, and `famAllMatch = true` then says only what the *final
accumulator* is: extracting "for **this** `p`, `mask`, `cm` the match holds"
would mean reasoning about an imperative fold, which is the very thing the
`famPacked` refactor removed from the definitions.  `List.all_eq_true` unpacks
this form elementwise, which is what the assembly consumes. -/
def famAllMatch : Bool :=
  let targets := nzIdx.map (fun j =>
    let t := flagBasisCGraph j
    (t, fingerprint t))
  [tau1, tau2, tau3].all (fun p =>
    (List.range (2 ^ (freePairs p.n).length)).all (fun mask =>
      (List.range (2 ^ (8 - p.n))).all (fun cm =>
        let g := famGraph p mask cm
        !(triangleFreeC g && blackIndepC g) ||
          targets.any (fun tf => tf.2 == fingerprint g && cPermCount g tf.1 != 0))))

/-- **C2.**  Completeness over the τ-anchored family. -/
theorem famAllMatch_true : famAllMatch = true := by native_decide

end PentagonQComplete
end Davey2024
