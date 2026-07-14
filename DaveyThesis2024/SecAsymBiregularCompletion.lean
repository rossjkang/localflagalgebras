import DaveyThesis2024.Basic
import DaveyThesis2024.PentagonConjecture
import DaveyThesis2024.SecAsymmetricBipartiteBridge

/-!
# Exact `(Δ, a)`-biregular completion (Phase K)

Given a bipartite `G : Flag emptyType` with high side `S` that is exactly
`Δ`-regular (`Δ = maxDegree G`) and low side of degree `≤ a`, we build a
`Flag emptyType` `biregularCompletion G S a ⊇ G` (induced on `V(G)`) that is
exactly `(Δ, a)`-biregular with `maxDegree = Δ`.

**Construction (kernel-spike §2, complete-bipartite blocks by deficiency).**
The vertex set decodes to
```
V(H) = (Fin Δ × Fin G.size)              -- Δ disjoint copies of G; copy 0 = distinguished
     ⊕ (Σ b : Fin G.size, Fin (a - deg_G b))   -- fresh high vertices
```
The deficiency `a - deg_G b` is `0` for high vertices `b ∈ S` (there `deg_G b = Δ ≥ a`),
so no fresh vertices attach to them.  Each low vertex `b` gets `a - deg_G b` fresh
high partners, each of which forms a complete-bipartite block `K_{Δ, a-deg_G b}` with
the `Δ` copies `{(c, b) : c ∈ Fin Δ}`.  Complete-bipartite blocks make multi-edge /
distinctness reasoning free; no matching/greedy argument is needed.
-/

namespace Davey2024.SecAsymBiregularCompletion

open Davey2024 Finset Classical

set_option linter.unusedVariables false

noncomputable section

/-! ## §0. Generic reindexing helper -/

/-- The cardinality of a `univ`-filter is invariant under precomposition with an
equivalence. -/
lemma card_filter_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (p : β → Prop) :
    (univ.filter (fun a => p (e a))).card = (univ.filter p).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

/-! ## §1. Vertex type and adjacency of the completion -/

/-- Vertex type of the completion: `Δ` disjoint copies of `G`, plus fresh high
vertices `(b, j)` (one bundle of `a - deg_G b` per vertex `b`).  The `S` argument
is retained for a uniform interface even though the vertex type does not use it. -/
abbrev HVtx (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ) : Type :=
  (Fin (maxDegree G) × Fin G.size) ⊕
    (Σ b : Fin G.size, Fin (a - vertexDegree G b))

/-- Adjacency of the completion on the sigma type. -/
def hAdj (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ) :
    HVtx G S a → HVtx G S a → Prop
  | Sum.inl (c, u), Sum.inl (c', v) => c = c' ∧ G.graph.Adj u v
  | Sum.inl (_, u), Sum.inr ⟨b, _⟩ => u = b
  | Sum.inr ⟨b, _⟩, Sum.inl (_, v) => v = b
  | Sum.inr _, Sum.inr _ => False

/-- The completion as a `SimpleGraph` on the sigma type. -/
def hSimpleGraph (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ) :
    SimpleGraph (HVtx G S a) where
  Adj := hAdj G S a
  symm := by
    rintro (⟨c, u⟩ | ⟨b, j⟩) (⟨c', v⟩ | ⟨b', j'⟩) h
    · exact ⟨h.1.symm, h.2.symm⟩
    · exact h
    · exact h
    · exact h
  loopless := ⟨by
    rintro (⟨c, u⟩ | ⟨b, j⟩) h
    · exact G.graph.loopless.irrefl u h.2
    · exact h⟩

/-! ## §2. The completion as a `Flag emptyType` -/

/-- The **exact `(Δ, a)`-biregular completion** of `G`, packaged as a
`Flag emptyType` on `Fin (Fintype.card (HVtx …))`, with adjacency transported
along `Fintype.equivFin`. -/
def biregularCompletion (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ) :
    Flag emptyType where
  size := Fintype.card (HVtx G S a)
  graph :=
    { Adj := fun i j => (hSimpleGraph G S a).Adj
        ((Fintype.equivFin (HVtx G S a)).symm i) ((Fintype.equivFin (HVtx G S a)).symm j)
      symm := fun {_ _} h => (hSimpleGraph G S a).symm h
      loopless := ⟨fun i h => (hSimpleGraph G S a).loopless.irrefl _ h⟩ }
  embedding := ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
  hsize := Nat.zero_le _

/-- Adjacency in the completion flag decodes to `hAdj` of the originals. -/
lemma biregularCompletion_adj (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ)
    (i j : Fin (biregularCompletion G S a).size) :
    (biregularCompletion G S a).graph.Adj i j ↔
      hAdj G S a ((Fintype.equivFin (HVtx G S a)).symm i)
        ((Fintype.equivFin (HVtx G S a)).symm j) := Iff.rfl

/-- `biregularCompletion_size`: the size is the cardinality of the vertex type. -/
lemma biregularCompletion_size (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ) :
    (biregularCompletion G S a).size = Fintype.card (HVtx G S a) := rfl

/-! ## §3. Neighbourhood cardinalities on the sigma type -/

/-- Neighbourhood card of an old-vertex `(c, p)`: `deg_G p` copy edges plus
`a - deg_G p` block edges. -/
lemma hAdj_neighbourhood_inl (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ)
    (c : Fin (maxDegree G)) (p : Fin G.size) :
    (univ.filter (fun y : HVtx G S a => hAdj G S a (Sum.inl (c, p)) y)).card
      = vertexDegree G p + (a - vertexDegree G p) := by
  have hinjA : Function.Injective (fun v => (Sum.inl (c, v) : HVtx G S a)) := by
    intro v1 v2 h; simpa using h
  have hinjB : Function.Injective
      (fun j => (Sum.inr ⟨p, j⟩ : HVtx G S a)) := by
    intro j1 j2 h
    simp only [Sum.inr.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h
    exact h
  have hset : (univ.filter (fun y : HVtx G S a => hAdj G S a (Sum.inl (c, p)) y))
      = ((univ.filter (fun v => G.graph.Adj p v)).image (fun v => (Sum.inl (c, v) : HVtx G S a)))
        ∪ ((univ : Finset (Fin (a - vertexDegree G p))).image
            (fun j => (Sum.inr ⟨p, j⟩ : HVtx G S a))) := by
    ext y
    constructor
    · intro hy
      rw [mem_filter] at hy
      obtain (⟨c', v⟩ | ⟨b, j⟩) := y
      · obtain ⟨hcc, hadj⟩ := hy.2
        rw [mem_union]; left
        rw [mem_image]
        exact ⟨v, mem_filter.mpr ⟨mem_univ v, hadj⟩, by rw [← hcc]⟩
      · have hpb : p = b := hy.2
        rw [mem_union]; right
        rw [mem_image]
        subst hpb
        exact ⟨j, mem_univ j, rfl⟩
    · intro hy
      rw [mem_union] at hy
      rw [mem_filter]
      refine ⟨mem_univ y, ?_⟩
      rcases hy with hy | hy
      · rw [mem_image] at hy
        obtain ⟨v, hv, rfl⟩ := hy
        rw [mem_filter] at hv
        exact ⟨rfl, hv.2⟩
      · rw [mem_image] at hy
        obtain ⟨j, _, rfl⟩ := hy
        exact rfl
  have hdisj : Disjoint
      ((univ.filter (fun v => G.graph.Adj p v)).image (fun v => (Sum.inl (c, v) : HVtx G S a)))
      ((univ : Finset (Fin (a - vertexDegree G p))).image
        (fun j => (Sum.inr ⟨p, j⟩ : HVtx G S a))) := by
    rw [Finset.disjoint_left]
    intro y h1 h2
    rw [mem_image] at h1 h2
    obtain ⟨v, _, rfl⟩ := h1
    obtain ⟨j, _, hj⟩ := h2
    exact Sum.inl_ne_inr hj.symm
  rw [hset, card_union_of_disjoint hdisj, card_image_of_injective _ hinjA,
    card_image_of_injective _ hinjB, Finset.card_univ, Fintype.card_fin]
  rfl

/-- Neighbourhood card of a fresh-high vertex `(b, j)`: exactly `Δ` (the `Δ`
copies of `b`). -/
lemma hAdj_neighbourhood_inr (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ)
    (b : Fin G.size) (j : Fin (a - vertexDegree G b)) :
    (univ.filter (fun y : HVtx G S a => hAdj G S a (Sum.inr ⟨b, j⟩) y)).card
      = maxDegree G := by
  have hinj : Function.Injective (fun c => (Sum.inl (c, b) : HVtx G S a)) := by
    intro c1 c2 h; simpa using h
  have hset : (univ.filter (fun y : HVtx G S a => hAdj G S a (Sum.inr ⟨b, j⟩) y))
      = (univ : Finset (Fin (maxDegree G))).image (fun c => (Sum.inl (c, b) : HVtx G S a)) := by
    ext y
    constructor
    · intro hy
      rw [mem_filter] at hy
      obtain (⟨c, v⟩ | ⟨b', j'⟩) := y
      · have hvb : v = b := hy.2
        rw [mem_image]
        exact ⟨c, mem_univ c, by rw [hvb]⟩
      · exact absurd hy.2 (by simp [hAdj])
    · intro hy
      rw [mem_image] at hy
      obtain ⟨c, _, rfl⟩ := hy
      rw [mem_filter]
      exact ⟨mem_univ _, rfl⟩
  rw [hset, card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-! ## §4. Degree reindexing to the flag layer -/

/-- Reindex the flag-neighbourhood filter through `Fintype.equivFin`. -/
lemma bc_degree_reindex (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ)
    (i : Fin (biregularCompletion G S a).size) :
    (univ.filter (fun j => (biregularCompletion G S a).graph.Adj i j)).card
      = (univ.filter (fun y : HVtx G S a =>
          hAdj G S a ((Fintype.equivFin (HVtx G S a)).symm i) y)).card :=
  card_filter_comp_equiv (Fintype.equivFin (HVtx G S a)).symm
    (fun y => hAdj G S a ((Fintype.equivFin (HVtx G S a)).symm i) y)

/-! ## §5. High side and biregularity -/

/-- The "high" predicate on the sigma type: old-high copies plus all fresh vertices. -/
def isHigh (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ) : HVtx G S a → Prop
  | Sum.inl (_, u) => u ∈ S
  | Sum.inr _ => True

/-- The high side `S'` of the completion. -/
def bcHighSet (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ) :
    Finset (Fin (biregularCompletion G S a).size) :=
  univ.filter (fun i => isHigh G S a ((Fintype.equivFin (HVtx G S a)).symm i))

/-- Per-vertex degree bound: every vertex has degree `≤ Δ`. -/
lemma bc_vertex_degree_le (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ)
    (haΔ : a ≤ maxDegree G) (i : Fin (biregularCompletion G S a).size) :
    (univ.filter (fun j => (biregularCompletion G S a).graph.Adj i j)).card ≤ maxDegree G := by
  rw [bc_degree_reindex]
  obtain (⟨c, p⟩ | ⟨b, j⟩) := (Fintype.equivFin (HVtx G S a)).symm i
  · rw [hAdj_neighbourhood_inl]
    have := vertexDegree_le_maxDegree G p
    omega
  · exact le_of_eq (hAdj_neighbourhood_inr G S a b j)

/-- **K7: `maxDegree (biregularCompletion G S a) = maxDegree G`.** -/
lemma biregularCompletion_maxDegree (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ)
    (ha : 1 ≤ a) (haΔ : a ≤ maxDegree G) :
    maxDegree (biregularCompletion G S a) = maxDegree G := by
  have hΔpos : 0 < maxDegree G := lt_of_lt_of_le ha haΔ
  refine le_antisymm (Finset.sup_le fun i _ => bc_vertex_degree_le G S a haΔ i) ?_
  -- Lower bound: exhibit a copy-0 vertex of degree Δ.
  have hmaxle : maxDegree G ≤ G.size := by
    apply Finset.sup_le
    intro v _
    calc (univ.filter (fun u => G.graph.Adj v u)).card
          ≤ (univ : Finset (Fin G.size)).card := card_filter_le _ _
      _ = G.size := by rw [card_univ, Fintype.card_fin]
  have hsz : 0 < G.size := lt_of_lt_of_le hΔpos hmaxle
  have hne : (univ : Finset (Fin G.size)).Nonempty :=
    univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hsz)
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin G.size)) hne
    (fun w => (univ.filter (fun u => G.graph.Adj w u)).card)
  have hvdeg : vertexDegree G v = maxDegree G := hv.symm
  set i0 := (Fintype.equivFin (HVtx G S a)) (Sum.inl (⟨0, hΔpos⟩, v)) with hi0
  have hdeg0 : (univ.filter (fun j => (biregularCompletion G S a).graph.Adj i0 j)).card
      = maxDegree G := by
    rw [bc_degree_reindex]
    rw [hi0, Equiv.symm_apply_apply]
    rw [hAdj_neighbourhood_inl]
    omega
  calc maxDegree G = (univ.filter (fun j => (biregularCompletion G S a).graph.Adj i0 j)).card :=
        hdeg0.symm
    _ ≤ maxDegree (biregularCompletion G S a) :=
        Finset.le_sup (f := fun i => (univ.filter
          (fun j => (biregularCompletion G S a).graph.Adj i j)).card) (mem_univ i0)

/-- **K5: bipartiteness.** Every edge of the completion crosses `S' = bcHighSet`. -/
lemma biregularCompletion_bipartite (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ)
    (hbip : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (hhi : ∀ u ∈ S, (univ.filter (fun v => G.graph.Adj u v)).card = maxDegree G)
    (haΔ : a ≤ maxDegree G) :
    ∀ u v, (biregularCompletion G S a).graph.Adj u v →
      (u ∈ bcHighSet G S a ↔ v ∉ bcHighSet G S a) := by
  intro u v hadj
  rw [biregularCompletion_adj] at hadj
  simp only [bcHighSet, mem_filter, mem_univ, true_and]
  obtain ⟨x, hx⟩ : ∃ x, (Fintype.equivFin (HVtx G S a)).symm u = x := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, (Fintype.equivFin (HVtx G S a)).symm v = y := ⟨_, rfl⟩
  rw [hx, hy] at hadj ⊢
  clear hx hy
  obtain (⟨c, p⟩ | ⟨b, j⟩) := x <;> obtain (⟨c', q⟩ | ⟨b', j'⟩) := y
  · -- inl-inl
    exact hbip p q hadj.2
  · -- inl-inr
    have hpb : p = b' := hadj
    subst hpb
    have hpS : p ∉ S := by
      intro hpS
      have hvd : vertexDegree G p = maxDegree G := hhi p hpS
      have := j'.isLt
      omega
    simp only [isHigh, not_true, iff_false]
    exact hpS
  · -- inr-inl
    have hqb : q = b := hadj
    subst hqb
    have hqS : q ∉ S := by
      intro hqS
      have hvd : vertexDegree G q = maxDegree G := hhi q hqS
      have := j.isLt
      omega
    simp only [isHigh, true_iff]
    exact hqS
  · -- inr-inr : no edge
    simp only [hAdj] at hadj

/-- **K2/K4: high vertices have degree exactly `Δ`.** -/
lemma biregularCompletion_high_deg (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ)
    (hhi : ∀ u ∈ S, (univ.filter (fun v => G.graph.Adj u v)).card = maxDegree G)
    (haΔ : a ≤ maxDegree G) :
    ∀ u ∈ bcHighSet G S a,
      (univ.filter (fun j => (biregularCompletion G S a).graph.Adj u j)).card = maxDegree G := by
  intro u hu
  rw [bc_degree_reindex]
  simp only [bcHighSet, mem_filter, mem_univ, true_and] at hu
  obtain ⟨x, hx⟩ : ∃ x, (Fintype.equivFin (HVtx G S a)).symm u = x := ⟨_, rfl⟩
  rw [hx] at hu ⊢
  clear hx
  obtain (⟨c, p⟩ | ⟨b, j⟩) := x
  · rw [hAdj_neighbourhood_inl]
    have hvd : vertexDegree G p = maxDegree G := hhi p hu
    omega
  · exact hAdj_neighbourhood_inr G S a b j

/-- **K3: low vertices have degree exactly `a`.** -/
lemma biregularCompletion_low_deg (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ)
    (hlo : ∀ u, u ∉ S → (univ.filter (fun v => G.graph.Adj u v)).card ≤ a) :
    ∀ u, u ∉ bcHighSet G S a →
      (univ.filter (fun j => (biregularCompletion G S a).graph.Adj u j)).card = a := by
  intro u hu
  rw [bc_degree_reindex]
  simp only [bcHighSet, mem_filter, mem_univ, true_and] at hu
  obtain ⟨x, hx⟩ : ∃ x, (Fintype.equivFin (HVtx G S a)).symm u = x := ⟨_, rfl⟩
  rw [hx] at hu ⊢
  clear hx
  obtain (⟨c, p⟩ | ⟨b, j⟩) := x
  · rw [hAdj_neighbourhood_inl]
    have hle : vertexDegree G p ≤ a := hlo p hu
    omega
  · exact absurd trivial hu

/-! ## §6. Copy-0 embedding (K6) -/

/-- The copy-0 embedding `G ↪ biregularCompletion G S a` at the `Fin`-index layer. -/
def bcEmb0 (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ)
    (ha : 1 ≤ a) (haΔ : a ≤ maxDegree G) :
    Fin G.size → Fin (biregularCompletion G S a).size :=
  fun u => Fintype.equivFin (HVtx G S a) (Sum.inl (⟨0, by omega⟩, u))

lemma biregularCompletion_emb0_injective (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ)
    (ha : 1 ≤ a) (haΔ : a ≤ maxDegree G) :
    Function.Injective (bcEmb0 G S a ha haΔ) := by
  intro u v h
  unfold bcEmb0 at h
  have h2 := (Fintype.equivFin (HVtx G S a)).injective h
  simpa using h2

/-- **K6: the copy-0 embedding is induced on `V(G)`.** -/
lemma biregularCompletion_emb0_adj_iff (G : Flag emptyType) (S : Finset (Fin G.size)) (a : ℕ)
    (ha : 1 ≤ a) (haΔ : a ≤ maxDegree G) :
    ∀ u v, u ≠ v →
      ((biregularCompletion G S a).graph.Adj
          (bcEmb0 G S a ha haΔ u) (bcEmb0 G S a ha haΔ v) ↔ G.graph.Adj u v) := by
  intro u v _
  unfold bcEmb0
  rw [biregularCompletion_adj, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨rfl, h⟩

end

end Davey2024.SecAsymBiregularCompletion
