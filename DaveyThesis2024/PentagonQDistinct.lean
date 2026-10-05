import DaveyThesis2024.CGraphBridge

/-!
# Phase 1 item D: distinctness of the 69, within reach of `native_decide`

`cFlags_noniso_implies_genClass_ne` (`CGraphBridge.lean:189`) turns
`cInducedCount F G = 0` into `GenFlagClass.mk F ≠ GenFlagClass.mk G`, which is
the direction distinctness needs.  Its hypothesis is the problem:
`cInducedCount` filters over the whole function space `Fin n₁ → Fin n₂`
(`CGraphBridge.lean:37`), so at `n = 8` that is `8⁸ = 1.7·10⁷` maps per pair and
`3.9·10¹⁰` over the `C(69,2) = 2346` pairs — out of reach.

An injective self-map of a finite type is a bijection, so for equal sizes the
filter may range over `Equiv.Perm (Fin n)` instead: `40320` per pair, `9.5·10⁷`
in total, which `native_decide` does comfortably.  That is this file.
-/

namespace Davey2024
namespace PentagonQDistinct

open Finset

/-- `cInducedCount` with the function space cut down to the permutations, which
is all it can contain when source and target have the same size. -/
def cPermCount {n : Nat} (F G : CGraph n) : Nat :=
  (univ : Finset (Equiv.Perm (Fin n))).filter (fun p =>
    (∀ i : Fin n, F.col i = G.col (p i)) ∧
    (∀ i j : Fin n, F.adj i j = G.adj (p i) (p j))) |>.card

/-- **D.**  For equal sizes the two counts agree: injectivity on a finite type
is bijectivity, so every map the larger filter keeps is a permutation. -/
theorem cInducedCount_eq_cPermCount {n : Nat} (F G : CGraph n) :
    cInducedCount F G = cPermCount F G := by
  classical
  unfold cInducedCount cPermCount
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  refine Fintype.card_congr {
    toFun := fun x =>
      ⟨Equiv.ofBijective x.1
        (Finite.injective_iff_bijective.mp (fun a b h => x.2.1 a b h)),
       x.2.2.1, x.2.2.2⟩
    invFun := fun y =>
      ⟨⇑y.1, fun a b h => y.1.injective h, y.2.1, y.2.2⟩
    left_inv := fun x => rfl
    right_inv := fun y => Subtype.ext (Equiv.ext fun _ => rfl) }

/-- The distinctness criterion, in the form an enumeration can discharge. -/
theorem genClass_ne_of_cPermCount_eq_zero {n : Nat} (F G : CGraph n)
    (hFs : ∀ i j, F.adj i j = F.adj j i) (hFi : ∀ i, F.adj i i = false)
    (hGs : ∀ i j, G.adj i j = G.adj j i) (hGi : ∀ i, G.adj i i = false)
    (h : cPermCount F G = 0) :
    GenFlagClass.mk F.toGenFlag ≠ GenFlagClass.mk G.toGenFlag :=
  cFlags_noniso_implies_genClass_ne F G hFs hFi hGs hGi
    (by rw [cInducedCount_eq_cPermCount]; exact h)

/-! ## The positive direction

`cFlags_noniso_implies_genClass_ne` gives distinctness from a *zero* count.  The
assembly needs the converse: a non-zero count means the classes coincide.  The
argument is the one `PentagonQOrbit.autEquiv` makes at `F → F` — an induced
embedding between flags of equal size is injective on a finite type, hence
bijective, hence an isomorphism. -/

/-- An induced embedding between same-size flags is an isomorphism. -/
theorem genFlagIso_of_genInducedCount_pos {n : Nat} (F G : CGraph n)
    (h : 0 < genInducedCount CG2 (GenFlagType.empty CG2) F.toGenFlag G.toGenFlag) :
    GenFlagIso (GenFlagType.empty CG2) F.toGenFlag G.toGenFlag := by
  obtain ⟨e⟩ := Fintype.card_pos_iff.mp h
  exact ⟨Equiv.ofBijective e.toFun (Finite.injective_iff_bijective.mp e.injective),
    e.isInduced, fun i => i.elim0⟩

/-- **B.**  A non-zero permutation count identifies the two flag classes. -/
theorem genClass_eq_of_cPermCount_ne_zero {n : Nat} (F G : CGraph n)
    (hFs : ∀ i j, F.adj i j = F.adj j i) (hFi : ∀ i, F.adj i i = false)
    (hGs : ∀ i j, G.adj i j = G.adj j i) (hGi : ∀ i, G.adj i i = false)
    (h : cPermCount F G ≠ 0) :
    GenFlagClass.mk F.toGenFlag = GenFlagClass.mk G.toGenFlag := by
  have hpos : 0 < cInducedCount F G := by
    rw [cInducedCount_eq_cPermCount]; omega
  rw [cInducedCount_eq_genInducedCount' F G hFs hFi hGs hGi] at hpos
  exact Quotient.sound (genFlagIso_of_genInducedCount_pos F G hpos)

#print axioms genFlagIso_of_genInducedCount_pos
#print axioms genClass_eq_of_cPermCount_ne_zero
#print axioms cInducedCount_eq_cPermCount
#print axioms genClass_ne_of_cPermCount_eq_zero

end PentagonQDistinct
end Davey2024
