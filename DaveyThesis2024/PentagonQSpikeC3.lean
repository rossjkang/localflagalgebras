import DaveyThesis2024.PentagonQRooted

/-!
# C3 spike: does the τ-anchored WLOG construct in Lean?

`PHASE1.md` names C3 the one step in Phase 1 with neither a measurement nor a
proof behind it: from an abstract host and an 8-subset with `μ ≠ 0`, produce the
packed mask the enumeration ranges over.  Its crux, per PLAN 1.4, is
"constructing a permutation, not deciding a finite fact" — the τ-anchored WLOG
must move the τ-image to positions `0 … k-1`, and the τ-embedding that `μ ≠ 0`
supplies is exactly the injection to extend.

This file is the spike: build that extension.

**Result: it constructs, on `[propext, Classical.choice, Quot.sound]`, in twenty
lines of Mathlib plumbing** — `Equiv.ofInjective` on the range, an
`Fintype.equivFinOfCardEq` on the complement, and `Equiv.sumCompl` against
`finSumFinEquiv` to compare the two ways of splitting `Fin n`.  Two iterations.

**What the spike settles, and what it does not.**  It settles the step PLAN 1.4
singles out as neither a finite decision nor routine `Finset` work.  It does not
do the rest of C3: that the relabelled graph's packed encoding lands in the
enumerated family, that `decode mask` is isomorphic to the relabelled subflag,
and that triangle-freeness, black-independence and `μ ≠ 0` transport along `π`.
Those are bookkeeping — the decode round trip is already proved in
`Delta4/Transport.lean` (`packD`, `digit_packD`), and once `π` puts the τ-image
at `0 … k-1` the family membership is reading off the free bits.  So what the
spike removes is C3's *risk*, more than C's days.
-/

namespace Davey2024
namespace PentagonQSpikeC3

open Finset

/-- **The C3 crux.**  An injective map `Fin k → Fin n` extends to a permutation
of `Fin n` carrying the first `k` positions onto its image, in order.

Applied at `k = 4` or `5` and `n = 8`, this is the τ-anchored relabelling: `f` is
the τ-embedding `μ ≠ 0` hands you, and `π` is the WLOG that puts its image at
`0 … k-1` so the residual freedom is a mask over the remaining slots. -/
theorem exists_perm_extending {n k : ℕ} (hk : k ≤ n) (f : Fin k → Fin n)
    (hf : Function.Injective f) :
    ∃ π : Equiv.Perm (Fin n), ∀ i : Fin k, π (Fin.castLE hk i) = f i := by
  classical
  -- the range and its complement, as subtypes
  have hrange : Fintype.card {x : Fin n // x ∈ Set.range f} = k :=
    (Fintype.card_congr (Equiv.ofInjective f hf)).symm.trans (Fintype.card_fin k)
  have hcompl : Fintype.card {x : Fin n // x ∉ Set.range f} = n - k := by
    rw [Fintype.card_subtype_compl, hrange, Fintype.card_fin]
  -- Fin k ⊕ Fin (n-k) ≃ Fin n, two ways: by position, and by range/complement
  let e₁ : Fin k ≃ {x : Fin n // x ∈ Set.range f} := Equiv.ofInjective f hf
  let e₂ : Fin (n - k) ≃ {x : Fin n // x ∉ Set.range f} :=
    (Fintype.equivFinOfCardEq hcompl).symm
  let byPos : Fin k ⊕ Fin (n - k) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (by omega))
  let byRange : Fin k ⊕ Fin (n - k) ≃ Fin n :=
    (Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl _)
  refine ⟨byPos.symm.trans byRange, fun i => ?_⟩
  -- the first k positions are exactly the `inl` side
  have hpos : byPos (Sum.inl i) = Fin.castLE hk i := by
    apply Fin.ext; simp [byPos]
  rw [Equiv.trans_apply, ← hpos, Equiv.symm_apply_apply]
  simp [byRange, e₁]

/-- The specialisation the enumeration consumes. -/
theorem exists_perm_extending_eight {k : ℕ} (hk : k ≤ 8) (f : Fin k → Fin 8)
    (hf : Function.Injective f) :
    ∃ π : Equiv.Perm (Fin 8), ∀ i : Fin k, π (Fin.castLE hk i) = f i :=
  exists_perm_extending hk f hf

/-- **E.**  A permutation extending `f` on the first `k` positions carries every
later position outside `f`'s image.  `FamShape.root` needs exactly this: the
vertices the family leaves free are the ones the τ-embedding does not use. -/
theorem perm_outside {n k : ℕ} (hk : k ≤ n) (f : Fin k → Fin n)
    (π : Equiv.Perm (Fin n)) (hπ : ∀ i : Fin k, π (Fin.castLE hk i) = f i)
    (j : Fin n) (hj : k ≤ j.val) : π j ∉ Set.range f := by
  rintro ⟨i, hi⟩
  have heq : π j = π (Fin.castLE hk i) := by rw [hπ i, hi]
  have hji : j = Fin.castLE hk i := π.injective heq
  have : j.val = i.val := congrArg Fin.val hji
  omega

#print axioms perm_outside
#print axioms exists_perm_extending

end PentagonQSpikeC3
end Davey2024
