import DaveyThesis2024.SecAsymReduction

/-!
# High-side completion for the asymmetric strong chromatic index (Phase HS)

The asymmetric thesis-tight headline `sec_asym_thesis_tight_biregular`
(`StrongChromaticIndex` §8) is proved for exactly `(Δ, ⌊pΔ⌋)`-biregular hosts
and widened to `IsAsymmetricBipartite p G` (high side **exactly** `Δ`-regular)
by `asym_biregular_reduction` (`SecAsymReduction`).

This file supplies the *further* widening to the paper's full **max-degree**
statement `IsAsymmetricBipartiteMaxDeg p G`, where the high side `S` is only
constrained by `deg ≤ p·Δ` on the low side and bipartite opposition — the
high-side vertices are **at most** `Δ`-regular (paper "side maximum degrees
`Δ_A, Δ_B = p·Δ_A`").

**Construction (`highSideCompletion G S`).** Take `Δ = maxDegree G`. For each
high-side vertex `a ∈ S` with `deg_G(a) < Δ`, add `Δ − deg_G(a)` fresh degree-1
vertices, each adjacent only to `a`. This makes every high-side vertex exactly
`Δ`-regular while leaving `G` induced on `V(G)`, so `χ'ₛ` is monotone along the
inclusion. The vertex set decodes to
```
V(H) = Fin G.size ⊕ (Σ a : Fin G.size, Fin (Δ − deg_G a))
```
with a fresh vertex `(a, j)` adjacent to `a` **only when `a ∈ S`** (fresh
vertices attached to `a ∉ S` would inflate the low side and are therefore left
isolated — degree `0`, harmlessly low). No fresh–fresh edges. Fresh vertices
have degree `1` (or `0`), so no divisibility / block reasoning is needed.

`highSide_reduction` packages this as `IsAsymmetricBipartite p H` with
`Δ(H) = Δ(G)` and `χ'ₛ(G) ≤ χ'ₛ(H)`.
-/

namespace Davey2024.SecAsymHighSide

open Davey2024 Davey2024.SecAsymBiregularCompletion Davey2024.SecAsymmetricBipartiteBridge
  Davey2024.SecAsymReduction
open Finset Classical

set_option linter.unusedVariables false

noncomputable section

/-! ## §0. The paper max-degree predicate -/

/-- **Asymmetric bipartite hypothesis at ratio `p`, max-degree form** (paper's
"side maximum degrees `Δ_A, Δ_B = p·Δ_A`"): bipartite opposition across `S`,
with the low side `Sᶜ` of degree `≤ p·Δ`. The high side `S` is **only**
max-degree bounded — weaker than `IsAsymmetricBipartite`, which additionally
forces `∀ u ∈ S, deg u = Δ`. -/
def IsAsymmetricBipartiteMaxDeg (p : ℝ) (G : Flag emptyType) : Prop :=
  ∃ S : Finset (Fin G.size),
    (∀ u v, G.graph.Adj u v → (u ∈ S ↔ v ∉ S)) ∧
    (∀ u, u ∉ S → ((univ.filter (fun v => G.graph.Adj u v)).card : ℝ) ≤ p * (maxDegree G : ℝ))

/-- Every `IsAsymmetricBipartite p G` is in particular
`IsAsymmetricBipartiteMaxDeg p G` (drop the high-side degree-equality clause). -/
theorem IsAsymmetricBipartite.toMaxDeg {p : ℝ} {G : Flag emptyType}
    (h : IsAsymmetricBipartite p G) : IsAsymmetricBipartiteMaxDeg p G :=
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.2⟩

/-! ## §1. Vertex type and adjacency of the completion -/

/-- Vertex type of the high-side completion: `V(G)` plus a bundle of `Δ − deg_G a`
fresh vertices per vertex `a` (the bundle is used only when `a ∈ S`). -/
abbrev HSVtx (G : Flag emptyType) (S : Finset (Fin G.size)) : Type :=
  Fin G.size ⊕ (Σ a : Fin G.size, Fin (maxDegree G - vertexDegree G a))

/-- Adjacency of the completion on the sigma type. Fresh vertices `(a, j)` attach
to `a` only when `a ∈ S`; no fresh–fresh edges. -/
def hsAdj (G : Flag emptyType) (S : Finset (Fin G.size)) :
    HSVtx G S → HSVtx G S → Prop
  | Sum.inl u, Sum.inl v => G.graph.Adj u v
  | Sum.inl u, Sum.inr ⟨a, _⟩ => u = a ∧ a ∈ S
  | Sum.inr ⟨a, _⟩, Sum.inl v => v = a ∧ a ∈ S
  | Sum.inr _, Sum.inr _ => False

/-- The completion as a `SimpleGraph` on the sigma type. -/
def hsSimpleGraph (G : Flag emptyType) (S : Finset (Fin G.size)) :
    SimpleGraph (HSVtx G S) where
  Adj := hsAdj G S
  symm := by
    rintro (u | ⟨a, j⟩) (v | ⟨b, k⟩) h
    · exact G.graph.symm h
    · exact h
    · exact h
    · exact h
  loopless := ⟨by
    rintro (u | ⟨a, j⟩) h
    · exact G.graph.loopless.irrefl u h
    · exact h⟩

/-! ## §2. The completion as a `Flag emptyType` -/

/-- The **high-side completion** of `G`, packaged as a `Flag emptyType` on
`Fin (Fintype.card (HSVtx …))`, adjacency transported along `Fintype.equivFin`. -/
def highSideCompletion (G : Flag emptyType) (S : Finset (Fin G.size)) :
    Flag emptyType where
  size := Fintype.card (HSVtx G S)
  graph :=
    { Adj := fun i j => (hsSimpleGraph G S).Adj
        ((Fintype.equivFin (HSVtx G S)).symm i) ((Fintype.equivFin (HSVtx G S)).symm j)
      symm := fun {_ _} h => (hsSimpleGraph G S).symm h
      loopless := ⟨fun i h => (hsSimpleGraph G S).loopless.irrefl _ h⟩ }
  embedding := ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
  hsize := Nat.zero_le _

/-- Adjacency in the completion flag decodes to `hsAdj` of the originals. -/
lemma highSideCompletion_adj (G : Flag emptyType) (S : Finset (Fin G.size))
    (i j : Fin (highSideCompletion G S).size) :
    (highSideCompletion G S).graph.Adj i j ↔
      hsAdj G S ((Fintype.equivFin (HSVtx G S)).symm i)
        ((Fintype.equivFin (HSVtx G S)).symm j) := Iff.rfl

/-! ## §3. Neighbourhood cardinalities on the sigma type -/

/-- Neighbourhood card of a high-side old-vertex `u ∈ S`: `deg_G u` original
edges plus `Δ − deg_G u` fresh edges. -/
lemma hs_nbhd_inl_mem (G : Flag emptyType) (S : Finset (Fin G.size))
    (u : Fin G.size) (hu : u ∈ S) :
    (univ.filter (fun y : HSVtx G S => hsAdj G S (Sum.inl u) y)).card
      = vertexDegree G u + (maxDegree G - vertexDegree G u) := by
  have hinjA : Function.Injective (fun v => (Sum.inl v : HSVtx G S)) := by
    intro v1 v2 h; simpa using h
  have hinjB : Function.Injective
      (fun j => (Sum.inr ⟨u, j⟩ : HSVtx G S)) := by
    intro j1 j2 h
    simp only [Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h
    exact h
  have hset : (univ.filter (fun y : HSVtx G S => hsAdj G S (Sum.inl u) y))
      = ((univ.filter (fun v => G.graph.Adj u v)).image (fun v => (Sum.inl v : HSVtx G S)))
        ∪ ((univ : Finset (Fin (maxDegree G - vertexDegree G u))).image
            (fun j => (Sum.inr ⟨u, j⟩ : HSVtx G S))) := by
    ext y
    constructor
    · intro hy
      rw [mem_filter] at hy
      obtain (v | ⟨a, j⟩) := y
      · rw [mem_union]; left
        rw [mem_image]
        exact ⟨v, mem_filter.mpr ⟨mem_univ v, hy.2⟩, rfl⟩
      · obtain ⟨hua, _⟩ := hy.2
        rw [mem_union]; right
        rw [mem_image]
        subst hua
        exact ⟨j, mem_univ j, rfl⟩
    · intro hy
      rw [mem_union] at hy
      rw [mem_filter]
      refine ⟨mem_univ y, ?_⟩
      rcases hy with hy | hy
      · rw [mem_image] at hy
        obtain ⟨v, hv, rfl⟩ := hy
        rw [mem_filter] at hv
        exact hv.2
      · rw [mem_image] at hy
        obtain ⟨j, _, rfl⟩ := hy
        exact ⟨rfl, hu⟩
  have hdisj : Disjoint
      ((univ.filter (fun v => G.graph.Adj u v)).image (fun v => (Sum.inl v : HSVtx G S)))
      ((univ : Finset (Fin (maxDegree G - vertexDegree G u))).image
        (fun j => (Sum.inr ⟨u, j⟩ : HSVtx G S))) := by
    rw [Finset.disjoint_left]
    intro y h1 h2
    rw [mem_image] at h1 h2
    obtain ⟨v, _, rfl⟩ := h1
    obtain ⟨j, _, hj⟩ := h2
    exact Sum.inl_ne_inr hj.symm
  rw [hset, card_union_of_disjoint hdisj, card_image_of_injective _ hinjA,
    card_image_of_injective _ hinjB, Finset.card_univ, Fintype.card_fin]
  rfl

/-- Neighbourhood card of a low-side old-vertex `u ∉ S`: exactly `deg_G u`
(no fresh vertices attach to `u`). -/
lemma hs_nbhd_inl_notmem (G : Flag emptyType) (S : Finset (Fin G.size))
    (u : Fin G.size) (hu : u ∉ S) :
    (univ.filter (fun y : HSVtx G S => hsAdj G S (Sum.inl u) y)).card
      = vertexDegree G u := by
  have hinjA : Function.Injective (fun v => (Sum.inl v : HSVtx G S)) := by
    intro v1 v2 h; simpa using h
  have hset : (univ.filter (fun y : HSVtx G S => hsAdj G S (Sum.inl u) y))
      = (univ.filter (fun v => G.graph.Adj u v)).image (fun v => (Sum.inl v : HSVtx G S)) := by
    ext y
    constructor
    · intro hy
      rw [mem_filter] at hy
      obtain (v | ⟨a, j⟩) := y
      · rw [mem_image]
        exact ⟨v, mem_filter.mpr ⟨mem_univ v, hy.2⟩, rfl⟩
      · obtain ⟨hua, haS⟩ := hy.2
        subst hua
        exact absurd haS hu
    · intro hy
      rw [mem_image] at hy
      obtain ⟨v, hv, rfl⟩ := hy
      rw [mem_filter] at hv ⊢
      exact ⟨mem_univ _, hv.2⟩
  rw [hset, card_image_of_injective _ hinjA]
  rfl

/-- Neighbourhood card of a fresh vertex `(a, j)`: at most `1` (exactly the copy
`a` when `a ∈ S`, otherwise none). -/
lemma hs_nbhd_inr_le (G : Flag emptyType) (S : Finset (Fin G.size))
    (a : Fin G.size) (j : Fin (maxDegree G - vertexDegree G a)) :
    (univ.filter (fun y : HSVtx G S => hsAdj G S (Sum.inr ⟨a, j⟩) y)).card ≤ 1 := by
  have hsub : (univ.filter (fun y : HSVtx G S => hsAdj G S (Sum.inr ⟨a, j⟩) y))
      ⊆ ({(Sum.inl a : HSVtx G S)} : Finset (HSVtx G S)) := by
    intro y hy
    rw [mem_filter] at hy
    obtain (v | ⟨b, k⟩) := y
    · obtain ⟨hva, _⟩ := hy.2
      rw [mem_singleton, hva]
    · exact (hy.2 : False).elim
  calc (univ.filter (fun y : HSVtx G S => hsAdj G S (Sum.inr ⟨a, j⟩) y)).card
      ≤ ({(Sum.inl a : HSVtx G S)} : Finset (HSVtx G S)).card := card_le_card hsub
    _ = 1 := card_singleton _

/-! ## §4. Degree reindexing to the flag layer -/

/-- Reindex the flag-neighbourhood filter through `Fintype.equivFin`. -/
lemma hs_degree_reindex (G : Flag emptyType) (S : Finset (Fin G.size))
    (i : Fin (highSideCompletion G S).size) :
    (univ.filter (fun j => (highSideCompletion G S).graph.Adj i j)).card
      = (univ.filter (fun y : HSVtx G S =>
          hsAdj G S ((Fintype.equivFin (HSVtx G S)).symm i) y)).card :=
  card_filter_comp_equiv (Fintype.equivFin (HSVtx G S)).symm
    (fun y => hsAdj G S ((Fintype.equivFin (HSVtx G S)).symm i) y)

/-! ## §5. High side and completion degree bounds -/

/-- The "high" predicate on the sigma type: old high-side vertices only. -/
def hsIsHigh (G : Flag emptyType) (S : Finset (Fin G.size)) : HSVtx G S → Prop
  | Sum.inl u => u ∈ S
  | Sum.inr _ => False

/-- The high side `S'` of the completion (the image of `S`). -/
def hsHighSet (G : Flag emptyType) (S : Finset (Fin G.size)) :
    Finset (Fin (highSideCompletion G S).size) :=
  univ.filter (fun i => hsIsHigh G S ((Fintype.equivFin (HSVtx G S)).symm i))

/-- Per-vertex degree bound: every vertex of the completion has degree `≤ Δ`. -/
lemma hs_vertex_degree_le (G : Flag emptyType) (S : Finset (Fin G.size))
    (hΔ1 : 1 ≤ maxDegree G) (i : Fin (highSideCompletion G S).size) :
    (univ.filter (fun j => (highSideCompletion G S).graph.Adj i j)).card ≤ maxDegree G := by
  rw [hs_degree_reindex]
  obtain (w | ⟨a, j⟩) := (Fintype.equivFin (HSVtx G S)).symm i
  · by_cases hw : w ∈ S
    · rw [hs_nbhd_inl_mem G S w hw]
      have := vertexDegree_le_maxDegree G w; omega
    · rw [hs_nbhd_inl_notmem G S w hw]
      exact vertexDegree_le_maxDegree G w
  · exact le_trans (hs_nbhd_inr_le G S a j) hΔ1

/-- **High-side vertices are exactly `Δ`-regular** in the completion. -/
lemma highSideCompletion_high_deg (G : Flag emptyType) (S : Finset (Fin G.size)) :
    ∀ u ∈ hsHighSet G S,
      (univ.filter (fun j => (highSideCompletion G S).graph.Adj u j)).card = maxDegree G := by
  intro u hu
  rw [hs_degree_reindex]
  simp only [hsHighSet, mem_filter, mem_univ, true_and] at hu
  obtain ⟨x, hx⟩ : ∃ x, (Fintype.equivFin (HSVtx G S)).symm u = x := ⟨_, rfl⟩
  rw [hx] at hu ⊢
  obtain (w | ⟨a, j⟩) := x
  · simp only [hsIsHigh] at hu
    rw [hs_nbhd_inl_mem G S w hu]
    have := vertexDegree_le_maxDegree G w; omega
  · exact absurd hu (by simp [hsIsHigh])

/-- **Low-side / fresh vertices have degree `≤ p·Δ`** in the completion.
For old low vertices this is `hlo`; for fresh vertices the degree is `≤ 1 ≤ p·Δ`
(via `hpΔ1`). -/
lemma highSideCompletion_low_le (p : ℝ) (G : Flag emptyType) (S : Finset (Fin G.size))
    (hlo : ∀ u, u ∉ S →
      ((univ.filter (fun v => G.graph.Adj u v)).card : ℝ) ≤ p * (maxDegree G : ℝ))
    (hpΔ1 : (1 : ℝ) ≤ p * (maxDegree G : ℝ)) :
    ∀ u, u ∉ hsHighSet G S →
      ((univ.filter (fun j => (highSideCompletion G S).graph.Adj u j)).card : ℝ)
        ≤ p * (maxDegree G : ℝ) := by
  intro u hu
  rw [hs_degree_reindex]
  simp only [hsHighSet, mem_filter, mem_univ, true_and] at hu
  obtain ⟨x, hx⟩ : ∃ x, (Fintype.equivFin (HSVtx G S)).symm u = x := ⟨_, rfl⟩
  rw [hx] at hu ⊢
  obtain (w | ⟨a, j⟩) := x
  · simp only [hsIsHigh] at hu
    rw [hs_nbhd_inl_notmem G S w hu]
    exact hlo w hu
  · calc ((univ.filter (fun y : HSVtx G S => hsAdj G S (Sum.inr ⟨a, j⟩) y)).card : ℝ)
        ≤ (1 : ℝ) := by exact_mod_cast hs_nbhd_inr_le G S a j
      _ ≤ p * (maxDegree G : ℝ) := hpΔ1

/-- **`maxDegree (highSideCompletion G S) = maxDegree G`** (needs `Δ ≥ 1`):
high-side vertices attain `Δ`, fresh vertices have degree `≤ 1 ≤ Δ`, and the
original max-degree vertex still attains `Δ`. -/
lemma highSideCompletion_maxDegree (G : Flag emptyType) (S : Finset (Fin G.size))
    (hΔ1 : 1 ≤ maxDegree G) :
    maxDegree (highSideCompletion G S) = maxDegree G := by
  refine le_antisymm (Finset.sup_le fun i _ => hs_vertex_degree_le G S hΔ1 i) ?_
  -- Lower bound: the original max-degree vertex still has degree `Δ`.
  have hmaxle : maxDegree G ≤ G.size := by
    apply Finset.sup_le
    intro v _
    calc (univ.filter (fun u => G.graph.Adj v u)).card
          ≤ (univ : Finset (Fin G.size)).card := card_filter_le _ _
      _ = G.size := by rw [card_univ, Fintype.card_fin]
  have hsz : 0 < G.size := lt_of_lt_of_le hΔ1 hmaxle
  have hne : (univ : Finset (Fin G.size)).Nonempty :=
    univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hsz)
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin G.size)) hne
    (fun w => (univ.filter (fun u => G.graph.Adj w u)).card)
  have hvdeg : vertexDegree G v = maxDegree G := hv.symm
  have hdeg0 : (univ.filter (fun j => (highSideCompletion G S).graph.Adj
      (Fintype.equivFin (HSVtx G S) (Sum.inl v)) j)).card = maxDegree G := by
    rw [hs_degree_reindex, Equiv.symm_apply_apply]
    by_cases hv' : v ∈ S
    · rw [hs_nbhd_inl_mem G S v hv']
      have := vertexDegree_le_maxDegree G v; omega
    · rw [hs_nbhd_inl_notmem G S v hv']; exact hvdeg
  calc maxDegree G
      = (univ.filter (fun j => (highSideCompletion G S).graph.Adj
          (Fintype.equivFin (HSVtx G S) (Sum.inl v)) j)).card := hdeg0.symm
    _ ≤ maxDegree (highSideCompletion G S) :=
        Finset.le_sup (f := fun i => (univ.filter
          (fun j => (highSideCompletion G S).graph.Adj i j)).card) (mem_univ _)

/-! ## §6. Bipartiteness -/

/-- **Bipartiteness.** Every edge of the completion crosses `S' = hsHighSet`
(the high side stays `S`; fresh vertices are low). -/
lemma highSideCompletion_bipartite (G : Flag emptyType) (S : Finset (Fin G.size))
    (hbip : ∀ u v, G.graph.Adj u v → (u ∈ S ↔ v ∉ S)) :
    ∀ u v, (highSideCompletion G S).graph.Adj u v →
      (u ∈ hsHighSet G S ↔ v ∉ hsHighSet G S) := by
  intro u v hadj
  rw [highSideCompletion_adj] at hadj
  simp only [hsHighSet, mem_filter, mem_univ, true_and]
  obtain ⟨x, hx⟩ : ∃ x, (Fintype.equivFin (HSVtx G S)).symm u = x := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, (Fintype.equivFin (HSVtx G S)).symm v = y := ⟨_, rfl⟩
  rw [hx, hy] at hadj ⊢
  obtain (p | ⟨a, j⟩) := x <;> obtain (q | ⟨b, k⟩) := y
  · exact hbip p q hadj
  · obtain ⟨hpb, hbS⟩ := hadj
    subst hpb
    exact iff_of_true hbS not_false
  · obtain ⟨hqa, haS⟩ := hadj
    subst hqa
    exact iff_of_false not_false (not_not_intro haS)
  · exact (hadj : False).elim

/-! ## §7. Inclusion embedding (`G` is induced on `V(G)`) -/

/-- The inclusion embedding `G ↪ highSideCompletion G S` at the `Fin`-index layer. -/
def hsEmb (G : Flag emptyType) (S : Finset (Fin G.size)) :
    Fin G.size → Fin (highSideCompletion G S).size :=
  fun u => Fintype.equivFin (HSVtx G S) (Sum.inl u)

lemma hsEmb_injective (G : Flag emptyType) (S : Finset (Fin G.size)) :
    Function.Injective (hsEmb G S) := by
  intro u v h
  unfold hsEmb at h
  have h2 := (Fintype.equivFin (HSVtx G S)).injective h
  simpa using h2

/-- The inclusion embedding is **induced** on `V(G)`: fresh vertices carry no
edges among `V(G)`. -/
lemma hsEmb_adj_iff (G : Flag emptyType) (S : Finset (Fin G.size)) :
    ∀ u v, u ≠ v →
      ((highSideCompletion G S).graph.Adj (hsEmb G S u) (hsEmb G S v)
        ↔ G.graph.Adj u v) := by
  intro u v _
  unfold hsEmb
  rw [highSideCompletion_adj, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact Iff.rfl

/-! ## §8. The high-side reduction -/

/-- **High-side completion reduction (asymmetric χ'ₛ).** Every
`IsAsymmetricBipartiteMaxDeg p G` (with `1 ≤ p·Δ`) has an
`IsAsymmetricBipartite p`-completion `G'` (high side **exactly** `Δ`-regular)
with the same max degree and no smaller strong chromatic index. Widens the
paper max-degree hypothesis to the high-side-regular headline. -/
theorem highSide_reduction (p : ℝ) (hp1 : 0 < p) (hp2 : p ≤ 1) (G : Flag emptyType)
    (hMax : IsAsymmetricBipartiteMaxDeg p G) (hpΔ1 : (1 : ℝ) ≤ p * (maxDegree G : ℝ)) :
    ∃ G' : Flag emptyType, IsAsymmetricBipartite p G' ∧ maxDegree G' = maxDegree G ∧
      strongChromaticIndex G ≤ strongChromaticIndex G' := by
  obtain ⟨S, hbip, hlo⟩ := hMax
  have hΔ1 : 1 ≤ maxDegree G := by
    have hle : p * (maxDegree G : ℝ) ≤ (maxDegree G : ℝ) :=
      mul_le_of_le_one_left (Nat.cast_nonneg _) hp2
    have : (1 : ℝ) ≤ (maxDegree G : ℝ) := le_trans hpΔ1 hle
    exact_mod_cast this
  have hmax : maxDegree (highSideCompletion G S) = maxDegree G :=
    highSideCompletion_maxDegree G S hΔ1
  refine ⟨highSideCompletion G S, ?_, hmax, ?_⟩
  · refine ⟨hsHighSet G S, highSideCompletion_bipartite G S hbip, ?_, ?_⟩
    · intro u hu
      rw [hmax]
      exact highSideCompletion_high_deg G S u hu
    · intro u hu
      rw [hmax]
      exact highSideCompletion_low_le p G S hlo hpΔ1 u hu
  · exact strongChromaticIndex_le_of_inducedEmbedding G (highSideCompletion G S)
      (hsEmb G S) (hsEmb_injective G S) (hsEmb_adj_iff G S)

end

end Davey2024.SecAsymHighSide
