import DaveyThesis2024.LocalFlagAlgebra

/-!
# Orbit–stabiliser for induced embeddings: the two group-action lemmas

`(a1)` needs `genInducedCount F G = genFlagAutCount F * #{S : G[S] ≅ F}`, which
the development does not state.  Its proof is a free, transitive action of
`Aut F` on the fibres of `e ↦ Set.range e.toFun`.  Three of the four ingredients
already existed: `GenInducedEmbedding.mapIso` (`FlagIso.lean:539`) is the action,
`range_mapIso` (`LocalFlagAlgebra.lean:6396`) says it fixes the image, and
`genInducedSubflag` (`Basic.lean:2951`) builds `G[S]`.

This file supplies the two that did not: the action is **free**, and it is
**transitive** on each fibre.  What remains is the fibre-counting bookkeeping.

Written to cost the `(a1)` estimate rather than to guess at it — see
the development notes.  It became reachable from the root module
when the item-(a) chain entered the default build.
-/

namespace Davey2024
namespace PentagonQOrbit

/-- Two induced embeddings with the same image differ by a flag automorphism. -/
theorem sameRange_mapIso {R : RelUniverse} {σ : GenFlagType R} {F G : GenFlag R σ}
    (e₁ e₂ : GenInducedEmbedding R σ F G)
    (h : Set.range e₁.toFun = Set.range e₂.toFun) :
    ∃ (φ : Fin F.size ≃ Fin F.size) (hstr : R.comap φ F.str = F.str)
      (hcompat : ∀ i : Fin σ.size, φ (F.embedding i) = F.embedding i),
      GenInducedEmbedding.mapIso φ hstr hcompat e₂ = e₁ := by
  classical
  set φ : Fin F.size ≃ Fin F.size :=
    (Equiv.ofInjective e₁.toFun e₁.injective).trans
      ((Equiv.setCongr h).trans (Equiv.ofInjective e₂.toFun e₂.injective).symm) with hφ
  -- the defining property: e₂ ∘ φ = e₁
  have key : ∀ x, e₂.toFun (φ x) = e₁.toFun x := by
    intro x
    have h2 := Equiv.apply_ofInjective_symm e₂.injective
      ((Equiv.setCongr h) (Equiv.ofInjective e₁.toFun e₁.injective x))
    simpa [hφ, Equiv.setCongr] using h2
  have hcomp : e₂.toFun ∘ (φ : Fin F.size → Fin F.size) = e₁.toFun := funext key
  have hstr : R.comap φ F.str = F.str := by
    calc R.comap φ F.str = R.comap φ (R.comap e₂.toFun G.str) := by rw [e₂.isInduced]
      _ = R.comap (e₂.toFun ∘ (φ : Fin F.size → Fin F.size)) G.str :=
            (R.comap_comp _ _ _).symm
      _ = R.comap e₁.toFun G.str := by rw [hcomp]
      _ = F.str := e₁.isInduced
  have hcompat : ∀ i : Fin σ.size, φ (F.embedding i) = F.embedding i := by
    intro i
    exact e₂.injective (by rw [key, e₁.compat, e₂.compat])
  exact ⟨φ, hstr, hcompat, by
    cases e₁; cases e₂
    simp only [GenInducedEmbedding.mapIso, GenInducedEmbedding.mk.injEq]
    exact hcomp⟩

/-- The action is free. -/
theorem mapIso_free {R : RelUniverse} {σ : GenFlagType R} {F G : GenFlag R σ}
    (φ : Fin F.size ≃ Fin F.size) (hstr : R.comap φ F.str = F.str)
    (hcompat : ∀ i : Fin σ.size, φ (F.embedding i) = F.embedding i)
    (e : GenInducedEmbedding R σ F G)
    (h : GenInducedEmbedding.mapIso φ hstr hcompat e = e) :
    φ = Equiv.refl _ := by
  have : ∀ x, e.toFun (φ x) = e.toFun x := fun x => congrFun (congrArg GenInducedEmbedding.toFun h) x
  exact Equiv.ext fun x => e.injective (this x)

/-! ## A1 — the automorphism count is the order of the acting group

`genFlagAutCount F` is *defined* as `genInducedCount F F`
(`LocalFlagAlgebra.lean:6308`), a count of induced embeddings.  The two lemmas
above act by `Equiv`s.  Without this the two are merely numerically equal. -/

/-- The flag automorphisms of `F`: the equivs `mapIso` acts by. -/
def FlagAut {R : RelUniverse} {σ : GenFlagType R} (F : GenFlag R σ) : Type :=
  {φ : Fin F.size ≃ Fin F.size //
    R.comap φ F.str = F.str ∧ ∀ i : Fin σ.size, φ (F.embedding i) = F.embedding i}

/-- An induced self-embedding is an automorphism: injective on a finite type is
bijective, and `isInduced`/`compat` are exactly the two side conditions. -/
noncomputable def autEquiv {R : RelUniverse} {σ : GenFlagType R} (F : GenFlag R σ) :
    GenInducedEmbedding R σ F F ≃ FlagAut F where
  toFun e := ⟨Equiv.ofBijective e.toFun (Finite.injective_iff_bijective.mp e.injective),
              e.isInduced, e.compat⟩
  invFun a := { toFun := a.1, injective := a.1.injective,
                isInduced := a.2.1, compat := a.2.2 }
  left_inv e := by cases e; rfl
  right_inv a := Subtype.ext (Equiv.ext fun _ => rfl)

noncomputable instance {R : RelUniverse} {σ : GenFlagType R} (F : GenFlag R σ) :
    Fintype (FlagAut F) := Fintype.ofEquiv _ (autEquiv F)

theorem card_flagAut {R : RelUniverse} {σ : GenFlagType R} (F : GenFlag R σ) :
    Fintype.card (FlagAut F) = genFlagAutCount R σ F :=
  (Fintype.card_congr (autEquiv F)).symm

/-! ## A2 — the fibres of `e ↦ range e` are `FlagAut F`-torsors -/

open Finset in
/-- The image of an embedding, as a `Finset`. -/
def rangeFinset {R : RelUniverse} {σ : GenFlagType R} {F G : GenFlag R σ}
    (e : GenInducedEmbedding R σ F G) : Finset (Fin G.size) :=
  Finset.image e.toFun Finset.univ

theorem coe_rangeFinset {R : RelUniverse} {σ : GenFlagType R} {F G : GenFlag R σ}
    (e : GenInducedEmbedding R σ F G) :
    (↑(rangeFinset e) : Set (Fin G.size)) = Set.range e.toFun := by
  simp [rangeFinset, Finset.coe_image]

theorem rangeFinset_eq_iff {R : RelUniverse} {σ : GenFlagType R} {F G : GenFlag R σ}
    (e₁ e₂ : GenInducedEmbedding R σ F G) :
    rangeFinset e₁ = rangeFinset e₂ ↔ Set.range e₁.toFun = Set.range e₂.toFun := by
  rw [← coe_rangeFinset, ← coe_rangeFinset]
  exact ⟨fun h => by rw [h], fun h => Finset.coe_injective h⟩

/-- **The fibre is an `Aut`-torsor.**  `φ ↦ mapIso φ e₀` is a bijection from the
automorphisms onto the embeddings with the same image as `e₀`: injective because
the action is free, surjective because it is transitive. -/
noncomputable def fibreEquiv {R : RelUniverse} {σ : GenFlagType R} {F G : GenFlag R σ}
    (e₀ : GenInducedEmbedding R σ F G) :
    FlagAut F ≃ {e : GenInducedEmbedding R σ F G // rangeFinset e = rangeFinset e₀} :=
  Equiv.ofBijective
    (fun a => ⟨GenInducedEmbedding.mapIso a.1 a.2.1 a.2.2 e₀, by
      rw [rangeFinset_eq_iff]; exact GenInducedEmbedding.range_mapIso ..⟩)
    ⟨by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      have h' : e₀.toFun ∘ (a : Fin F.size → Fin F.size) = e₀.toFun ∘ b :=
        congrArg GenInducedEmbedding.toFun (Subtype.ext_iff.mp h)
      exact Subtype.ext (Equiv.ext fun x => e₀.injective (congrFun h' x)),
     by
      rintro ⟨e, he⟩
      obtain ⟨φ, hstr, hcompat, hφ⟩ := sameRange_mapIso e e₀ ((rangeFinset_eq_iff e e₀).mp he)
      exact ⟨⟨φ, hstr, hcompat⟩, Subtype.ext hφ⟩⟩

/-! ## A3 — orbit–stabiliser -/

/-- The number of **images** of embeddings of `F` into `G` — the paper's
`c(F;G)`, a count of subsets rather than of maps. -/
noncomputable def copies {R : RelUniverse} (σ : GenFlagType R) (F G : GenFlag R σ) : ℕ :=
  (Finset.univ.image (fun e : GenInducedEmbedding R σ F G => rangeFinset e)).card

/-- **Orbit–stabiliser for induced embeddings.**  `genInducedCount` counts maps;
the paper's `c(F;G)` counts images; they differ by exactly `|Aut F|`. -/
theorem genInducedCount_eq_autCount_mul_copies {R : RelUniverse} {σ : GenFlagType R}
    (F G : GenFlag R σ) :
    genInducedCount R σ F G = genFlagAutCount R σ F * copies σ F G := by
  have key : ∀ S ∈ (Finset.univ.image
      (fun e : GenInducedEmbedding R σ F G => rangeFinset e)),
      (Finset.univ.filter (fun e : GenInducedEmbedding R σ F G => rangeFinset e = S)).card
        = genFlagAutCount R σ F := by
    intro S hS
    obtain ⟨e₀, -, he₀⟩ := Finset.mem_image.mp hS
    subst he₀
    rw [← Fintype.card_subtype, Fintype.card_congr (fibreEquiv e₀).symm, card_flagAut]
  unfold genInducedCount copies
  rw [← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise
        (fun e _ => Finset.mem_image_of_mem
          (fun e : GenInducedEmbedding R σ F G => rangeFinset e) (Finset.mem_univ e)),
      Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul, mul_comm]

/-! ## Towards E: the images are the 8-subsets

`copies` counts *images*; E sums over *subsets*.  Three lemmas bridge them: an
image has the source's size, an embedding between flags of equal size is an
isomorphism, and the inclusion of an induced subflag has that subflag's vertex
set as its range.

The last was proved once already, as a local `have` among 123 others inside
`genOrbit_counting_factoring` (`LocalFlagAlgebra.lean:7018`, the `have` itself
about a hundred lines further in).  Lifting it out is the pattern obligation
(a0) used for `comap_iff_of_injective`. -/

theorem card_rangeFinset {R : RelUniverse} {σ : GenFlagType R} {F G : GenFlag R σ}
    (e : GenInducedEmbedding R σ F G) : (rangeFinset e).card = F.size := by
  unfold rangeFinset
  rw [Finset.card_image_of_injective _ e.injective, Finset.card_univ, Fintype.card_fin]

/-- An induced embedding between flags of **equal size** is an isomorphism.  The
general form of `PentagonQDistinct.genFlagIso_of_genInducedCount_pos`, which was
stated only for `CGraph`s. -/
theorem genFlagIso_of_embedding_sameSize {R : RelUniverse} {σ : GenFlagType R}
    {F G : GenFlag R σ} (e : GenInducedEmbedding R σ F G) (h : F.size = G.size) :
    GenFlagIso σ F G := by
  refine ⟨Equiv.ofBijective e.toFun ?_, e.isInduced, e.compat⟩
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨e.injective, by simp [h]⟩

/-- **Lifted out of `genOrbit_counting_factoring`.**  The inclusion of an induced
subflag ranges over exactly that subflag's vertex set. -/
theorem range_genInducedSubflag_incl {R : RelUniverse} {σ : GenFlagType R}
    (G : GenFlag R σ) (S : Finset (Fin G.size))
    (hS : ∀ i : Fin σ.size, G.embedding i ∈ S) (hσ : σ.size ≤ S.card) :
    Set.range (G.genInducedSubflag_incl S hS hσ).toFun = ↑S := by
  ext v
  simp only [Set.mem_range, Finset.mem_coe]
  constructor
  · rintro ⟨z, rfl⟩; exact Finset.orderEmbOfFin_mem _ rfl z
  · intro hv
    exact ⟨(S.orderIsoOfFin rfl).symm ⟨v, hv⟩, by
      change ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨v, hv⟩)) = v
      simp [OrderIso.apply_symm_apply]⟩

/-! ## `copies` is a count of subsets

The bridge E needs: the images of embeddings of `F` into `G` are exactly the
vertex sets `S` whose induced subflag is isomorphic to `F`.  No cardinality side
condition is needed — an isomorphism forces `S.card = F.size` — and for the
`∅` type the subflag's two hypotheses are vacuous, so `G[S]` is defined for
*every* `S`. -/

/-- The paper's `c(F;G)`: the vertex sets whose induced subflag is `F`. -/
noncomputable def subsetCopies {R : RelUniverse}
    (F G : GenFlag R (GenFlagType.empty R)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun S : Finset (Fin G.size) =>
    GenFlagClass.mk (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
      = GenFlagClass.mk F)).card

/-- **E's subset bridge.**  Counting images is counting subsets. -/
theorem copies_eq_subsetCopies {R : RelUniverse}
    (F G : GenFlag R (GenFlagType.empty R)) :
    copies (GenFlagType.empty R) F G = subsetCopies F G := by
  classical
  unfold copies subsetCopies
  congr 1
  ext S
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨e, rfl⟩
    -- restrict `e` to its own image, then compare sizes
    have himg : ∀ x, e.toFun x ∈ rangeFinset e := by
      intro x; simp [rangeFinset]
    have hcard : (rangeFinset e).card = F.size := card_rangeFinset e
    refine (genFlagIso_of_embedding_sameSize
      (e.genRestrictToSubflag (rangeFinset e) (fun i => i.elim0) (Nat.zero_le _) himg)
      (by simpa using hcard.symm)).symm |> Quotient.sound
  · intro hS
    obtain ⟨φ, hstr, hcompat⟩ := Quotient.exact hS
    -- the isomorphism, as an embedding into the subflag, composed with inclusion
    have hsymm : R.comap φ.symm
        (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)).str = F.str := by
      rw [← hstr, ← R.comap_comp, φ.self_comp_symm, R.comap_id]
    let emb : GenInducedEmbedding R (GenFlagType.empty R) F
        (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)) :=
      { toFun := φ.symm
        injective := φ.symm.injective
        isInduced := hsymm
        compat := fun i => i.elim0 }
    refine ⟨(G.genInducedSubflag_incl S (fun i => i.elim0) (Nat.zero_le _)).comp emb, ?_⟩
    -- its range is the inclusion's range, since `emb` is onto
    have hsurj : Function.Surjective emb.toFun := φ.symm.surjective
    apply Finset.coe_injective
    rw [coe_rangeFinset]
    have : Set.range ((G.genInducedSubflag_incl S (fun i => i.elim0) (Nat.zero_le _)).comp emb).toFun
        = Set.range (G.genInducedSubflag_incl S (fun i => i.elim0) (Nat.zero_le _)).toFun := by
      have hc : ((G.genInducedSubflag_incl S (fun i => i.elim0) (Nat.zero_le _)).comp
            emb).toFun
          = (G.genInducedSubflag_incl S (fun i => i.elim0) (Nat.zero_le _)).toFun ∘
            emb.toFun := rfl
      rw [hc, Set.range_comp, hsurj.range_eq, Set.image_univ]
    rw [this, range_genInducedSubflag_incl]

/-! ## What A3 buys: the density is a count of subsets

`genUnlabelledDensity` divides the *embedding* count by `C(Δ, f)` and by the
automorphism count.  Orbit–stabiliser collapses that to the *subset* count over
`C(Δ, f)` — which is the paper's `ρ(F;G') = c(F;G')/C(Δ,8)`, the form item E
sums over.

The identity is unconditional: when `C(Δ, f) = 0` both sides are `0`, and the
automorphism count is never `0`. -/
theorem genUnlabelledDensity_eq_copies_div {R : RelUniverse} {σ : GenFlagType R}
    (F G : GenFlag R σ) (Δ : GenFlag R (GenFlagType.empty R) → ℕ) :
    genUnlabelledDensity R σ F G Δ
      = (copies σ F G : ℝ) / (Nat.choose (Δ G.forget) (F.size - σ.size) : ℝ) := by
  unfold genUnlabelledDensity
  rw [genInducedCount_eq_autCount_mul_copies F G]
  have haut : (genFlagAutCount R σ F : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (genFlagAutCount_pos σ F).ne'
  push_cast
  rw [mul_comm ((Nat.choose (Δ G.forget) (F.size - σ.size) : ℝ)) _]
  exact mul_div_mul_left _ _ haut

#print axioms genUnlabelledDensity_eq_copies_div
#print axioms copies_eq_subsetCopies
#print axioms card_rangeFinset
#print axioms genFlagIso_of_embedding_sameSize
#print axioms range_genInducedSubflag_incl
#print axioms sameRange_mapIso
#print axioms mapIso_free
#print axioms autEquiv
#print axioms fibreEquiv
#print axioms genInducedCount_eq_autCount_mul_copies

end PentagonQOrbit
end Davey2024
