import DaveyThesis2024.PentagonQOrbit

/-!
# Phase 1 item B: `μ` depends only on the isomorphism class

`(a1)` needs `μ(G'[S]) = μⱼ` whenever `G'[S] ≅ Fⱼ`, so `μ` must be invariant
under isomorphism of the **target**.  `FlagIso.lean:549` gives invariance in the
source (`genInducedCount_flagIso`); the target-side statement does not exist,
though the construction it needs, `mapIsoTarget`, does
(`PentagonConjecture.lean:5754`).  That file is far downstream, so the eight-line
construction is repeated here rather than imported.

`μ` is a weighted sum of *rooted* counts — embeddings whose every out-of-image
vertex is adjacent to the image of the root — so the root clause has to transport
too.  It does, because an isomorphism is a bijection on vertices: it preserves
both "outside the image" and "adjacent to the root's image".
-/

namespace Davey2024
namespace PentagonQIsoInvariance

open Davey2024.PentagonQOrbit

/-- `CG2` itself is an abbrev in `PentagonConjecture`, far downstream of this
file; this is the same universe, definitionally, so the two unify on use. -/
local notation "CG2'" => colouredGraphUniverse 2

/-! ## B1 — target-side invariance of `genInducedCount` -/

/-- Transport an induced embedding along an isomorphism of the **target**. -/
def mapIsoTgt {R : RelUniverse} {σ : GenFlagType R} {F G G' : GenFlag R σ}
    (ψ : Fin G.size ≃ Fin G'.size)
    (hstr : R.comap ψ G'.str = G.str)
    (hcompat : ∀ i : Fin σ.size, ψ (G.embedding i) = G'.embedding i)
    (e : GenInducedEmbedding R σ F G) : GenInducedEmbedding R σ F G' where
  toFun := ψ ∘ e.toFun
  injective := ψ.injective.comp e.injective
  isInduced := by rw [R.comap_comp, hstr, e.isInduced]
  compat i := by simp [Function.comp, e.compat, hcompat]

/-- The inverse data of a flag isomorphism. -/
theorem iso_symm_data {R : RelUniverse} {σ : GenFlagType R} {G G' : GenFlag R σ}
    {ψ : Fin G.size ≃ Fin G'.size} (hstr : R.comap ψ G'.str = G.str)
    (hcompat : ∀ i : Fin σ.size, ψ (G.embedding i) = G'.embedding i) :
    R.comap ψ.symm G.str = G'.str ∧
      ∀ i : Fin σ.size, ψ.symm (G'.embedding i) = G.embedding i := by
  refine ⟨?_, fun i => by rw [← hcompat i, Equiv.symm_apply_apply]⟩
  rw [← hstr, ← R.comap_comp, ψ.self_comp_symm, R.comap_id]

/-- **B1.**  `genInducedCount` is invariant under isomorphism of the target. -/
theorem genInducedCount_flagIso_target {R : RelUniverse} {σ : GenFlagType R}
    {F G G' : GenFlag R σ} (h : GenFlagIso σ G G') :
    genInducedCount R σ F G = genInducedCount R σ F G' := by
  obtain ⟨ψ, hstr, hcompat⟩ := h
  obtain ⟨hsymm, hcompat_symm⟩ := iso_symm_data hstr hcompat
  unfold genInducedCount
  refine Fintype.card_congr {
    toFun := mapIsoTgt ψ hstr hcompat
    invFun := mapIsoTgt ψ.symm hsymm hcompat_symm
    left_inv := fun e => by
      cases e; simp only [mapIsoTgt, GenInducedEmbedding.mk.injEq]
      ext x; simp [Function.comp]
    right_inv := fun e => by
      cases e; simp only [mapIsoTgt, GenInducedEmbedding.mk.injEq]
      ext x; simp [Function.comp] }

/-! ## B2 — the rooted count, and its invariance

`μ` counts embeddings of a rooted pattern whose every out-of-image vertex is
adjacent to the image of the root.  Stated at the `GenFlag` level over `CG2`,
where `str.1` is the graph and `str.2` the colouring. -/

/-- Induced embeddings of `F` into `G` whose every out-of-image vertex is
adjacent to the image of `root`.  This is `μ`'s summand, at the flag level. -/
noncomputable def rootedCountG (F G : GenFlag CG2' (GenFlagType.empty CG2'))
    (root : Fin F.size) : ℕ :=
  Nat.card {e : GenInducedEmbedding CG2' (GenFlagType.empty CG2') F G //
    ∀ w : Fin G.size, (∀ i, e.toFun i ≠ w) → (G.str.1).Adj (e.toFun root) w}

/-- **B2.**  The rooted count is invariant under isomorphism of the target: an
isomorphism is a bijection on vertices, so it preserves both "outside the image"
and "adjacent to the root's image". -/
theorem rootedCountG_flagIso_target {F G G' : GenFlag CG2' (GenFlagType.empty CG2')}
    (root : Fin F.size) (h : GenFlagIso (GenFlagType.empty CG2') G G') :
    rootedCountG F G root = rootedCountG F G' root := by
  obtain ⟨ψ, hstr, hcompat⟩ := h
  obtain ⟨hsymm, hcompat_symm⟩ := iso_symm_data hstr hcompat
  -- the isomorphism carries adjacency in `G` to adjacency in `G'`
  have hadj : ∀ u v : Fin G.size, (G.str.1).Adj u v ↔ (G'.str.1).Adj (ψ u) (ψ v) := by
    intro u v
    have : (G'.str.1).comap ψ = G.str.1 := congrArg Prod.fst hstr
    rw [← this]; rfl
  unfold rootedCountG
  refine Nat.card_congr {
    toFun := fun x => ⟨mapIsoTgt ψ hstr hcompat x.1, ?_⟩
    invFun := fun y => ⟨mapIsoTgt ψ.symm hsymm hcompat_symm y.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · -- forward: an outside vertex of `G'` is `ψ` of an outside vertex of `G`
    intro w hw
    have hw' : ∀ i, x.1.toFun i ≠ ψ.symm w := by
      intro i hi
      exact hw i (by rw [show (mapIsoTgt ψ hstr hcompat x.1).toFun i = ψ (x.1.toFun i) from rfl,
        hi, Equiv.apply_symm_apply])
    have := x.2 (ψ.symm w) hw'
    rw [hadj] at this
    simpa [mapIsoTgt, Function.comp] using this
  · intro w hw
    have hw' : ∀ i, y.1.toFun i ≠ ψ w := by
      intro i hi
      exact hw i (by rw [show (mapIsoTgt ψ.symm hsymm hcompat_symm y.1).toFun i
        = ψ.symm (y.1.toFun i) from rfl, hi, Equiv.symm_apply_apply])
    have h2 := y.2 (ψ w) hw'
    show (G.str.1).Adj ((mapIsoTgt ψ.symm hsymm hcompat_symm y.1).toFun root) w
    rw [show (mapIsoTgt ψ.symm hsymm hcompat_symm y.1).toFun root
          = ψ.symm (y.1.toFun root) from rfl, hadj, Equiv.apply_symm_apply]
    exact h2
  · rintro ⟨e, he⟩
    refine Subtype.ext ?_
    cases e; simp only [mapIsoTgt, GenInducedEmbedding.mk.injEq]
    ext x; simp [Function.comp]
  · rintro ⟨e, he⟩
    refine Subtype.ext ?_
    cases e; simp only [mapIsoTgt, GenInducedEmbedding.mk.injEq]
    ext x; simp [Function.comp]

/-! ## B3 — hence `μ` itself -/

/-- **B3.**  Any `ℤ`-weighted sum of rooted counts over a fixed list of rooted
patterns is a target-side isomorphism invariant.  `μ = 4·n₁ + n₂ + 2·n₃` is the
instance at the three τ patterns, so `μ(G'[S]) = μⱼ` whenever `G'[S] ≅ Fⱼ` —
which is what `(a1)` consumes. -/
theorem weighted_rootedCountG_flagIso_target
    (ps : List ((F : GenFlag CG2' (GenFlagType.empty CG2')) × Fin F.size × ℤ))
    {G G' : GenFlag CG2' (GenFlagType.empty CG2')}
    (h : GenFlagIso (GenFlagType.empty CG2') G G') :
    (ps.map (fun p => p.2.2 * (rootedCountG p.1 G p.2.1 : ℤ))).sum
      = (ps.map (fun p => p.2.2 * (rootedCountG p.1 G' p.2.1 : ℤ))).sum := by
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  rw [rootedCountG_flagIso_target p.2.1 h]

#print axioms weighted_rootedCountG_flagIso_target
#print axioms genInducedCount_flagIso_target
#print axioms rootedCountG_flagIso_target

end PentagonQIsoInvariance
end Davey2024
