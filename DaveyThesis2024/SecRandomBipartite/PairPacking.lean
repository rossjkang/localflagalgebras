/-
Copyright (c) 2026 Ross Kang.
Released under Apache 2.0 license.

# Phase C-CN.2 — Per-pair edge packing (bipartite)

Bipartite-adapted Czygrinow–Nagle nibble: for each pair `(A_i, B_j)` of
blocks in the partition, pack edges of `G[A_i, B_j]` into induced
matchings of size `k ≈ log_b(n_A n_B)`.

This file builds the bipartite-specific infrastructure on top of the
generic `CN.Setup` (induced matchings, block partition, nibble-output
spec) and the random-graph machinery in `BipartiteRandomGraph`.

## Status
Phase C-CN.2 cycle 8 (2026-06-02): cross-block edge set + basic API.
-/

import DaveyThesis2024.SecRandomBipartite.Setup
import DaveyThesis2024.BipartiteRandomGraph

namespace DaveyThesis2024.SecRandomBipartite

open SimpleGraph SECRandomBipartite

/-! ## Cross-block edges

In the bipartite graph `G` on vertex set `Fin n_A ⊕ Fin n_B`, the
*cross-block edges* between an `A`-block `S ⊆ Fin n_A` and a `B`-block
`T ⊆ Fin n_B` are the edges of `G` with one endpoint `Sum.inl a, a ∈ S`
and the other `Sum.inr b, b ∈ T`. -/

variable {n_A n_B : ℕ}

/-- Predicate on `Fin n_A × Fin n_B`: the pair `(a, b)` represents an
edge of `G` lying between `S` and `T`. -/
def IsCrossBlockEdge (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    (S : Finset (Fin n_A)) (T : Finset (Fin n_B))
    (ab : Fin n_A × Fin n_B) : Prop :=
  ab.1 ∈ S ∧ ab.2 ∈ T ∧ G.Adj (Sum.inl ab.1) (Sum.inr ab.2)

/-- The Finset of `(a, b)` pairs giving cross-block edges between `S` and
`T`. We parameterise by `Fin n_A × Fin n_B` (rather than `G.edgeSet`) so
that pairs survive even when `G.Adj` becomes non-decidable; downstream we
filter by `G.Adj` itself. -/
noncomputable def crossBlockPairs (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T : Finset (Fin n_B)) :
    Finset (Fin n_A × Fin n_B) :=
  (S ×ˢ T).filter (fun ab => G.Adj (Sum.inl ab.1) (Sum.inr ab.2))

@[simp] lemma mem_crossBlockPairs (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T : Finset (Fin n_B))
    (ab : Fin n_A × Fin n_B) :
    ab ∈ crossBlockPairs G S T ↔
      ab.1 ∈ S ∧ ab.2 ∈ T ∧ G.Adj (Sum.inl ab.1) (Sum.inr ab.2) := by
  unfold crossBlockPairs
  simp [Finset.mem_filter, Finset.mem_product, and_assoc]

/-- Cross-block pairs are bounded by `|S| · |T|`. -/
lemma crossBlockPairs_card_le (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T : Finset (Fin n_B)) :
    (crossBlockPairs G S T).card ≤ S.card * T.card := by
  unfold crossBlockPairs
  calc ((S ×ˢ T).filter _).card
      ≤ (S ×ˢ T).card := Finset.card_filter_le _ _
    _ = S.card * T.card := Finset.card_product _ _

/-! ## Bipartite induced matching

In the bipartite graph `G` on `Fin n_A ⊕ Fin n_B`, a *bipartite induced
matching* on `Fin n_A × Fin n_B` pairs is a set `M` of cross-pair edges
such that any two distinct pairs in `M` are:

* vertex-disjoint (different `A`-endpoint AND different `B`-endpoint), and
* not bridged by another `G`-edge — equivalently, since bridges between
  bipartite edges are themselves bipartite edges, the two "diagonal"
  pairs are non-edges of `G`.

This is the bipartite specialisation of `IsInducedMatching` from
`CN.Setup`, working at the pair level rather than the edge-set level. -/

/-- A set of cross-pair edges `M ⊆ Fin n_A × Fin n_B` is a *bipartite
induced matching* in `G`: vertex-disjoint pairs with no bridging edges. -/
def IsBipartiteInducedMatching
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (M : Finset (Fin n_A × Fin n_B)) : Prop :=
  ∀ ab₁ ∈ M, ∀ ab₂ ∈ M, ab₁ ≠ ab₂ →
    ab₁.1 ≠ ab₂.1 ∧ ab₁.2 ≠ ab₂.2 ∧
    ¬ G.Adj (Sum.inl ab₁.1) (Sum.inr ab₂.2) ∧
    ¬ G.Adj (Sum.inl ab₂.1) (Sum.inr ab₁.2)

/-- The empty set is a bipartite induced matching. -/
lemma isBipartiteInducedMatching_empty
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj] :
    IsBipartiteInducedMatching G ∅ := by
  intro ab₁ h; simp at h

/-- A singleton is always a bipartite induced matching. -/
lemma isBipartiteInducedMatching_singleton
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (ab : Fin n_A × Fin n_B) :
    IsBipartiteInducedMatching G {ab} := by
  intro ab₁ h₁ ab₂ h₂ hne
  rw [Finset.mem_singleton] at h₁ h₂
  exact absurd (h₁.trans h₂.symm) hne

/-- Closure under subset: a subset of a bipartite induced matching is
itself a bipartite induced matching. -/
lemma IsBipartiteInducedMatching.subset
    {G : SimpleGraph (Fin n_A ⊕ Fin n_B)} [DecidableRel G.Adj]
    {M N : Finset (Fin n_A × Fin n_B)} (hMN : M ⊆ N)
    (hN : IsBipartiteInducedMatching G N) :
    IsBipartiteInducedMatching G M := by
  intro ab₁ h₁ ab₂ h₂ hne
  exact hN ab₁ (hMN h₁) ab₂ (hMN h₂) hne

/-! ## Bipartite structure predicate

For our random bipartite graphs `G ← boolToBipartiteGraph f`, no edge has
both endpoints in `inl _` (`A`-side) or both in `inr _` (`B`-side). This
is a structural fact used by the bridge from
`IsBipartiteInducedMatching` (working on pairs) to the generic
`IsInducedMatching` (working on `G.edgeSet`). -/

/-- `G : SimpleGraph (Fin n_A ⊕ Fin n_B)` is *bipartite-on-sum* if no edge
has both endpoints on the same side. (A more concrete notion than
Mathlib's `G.Colorable 2`; works at the structural level via the `Sum`
constructors directly.) -/
def IsBipartiteOnSum (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) : Prop :=
  (∀ a a' : Fin n_A, ¬ G.Adj (Sum.inl a) (Sum.inl a')) ∧
  (∀ b b' : Fin n_B, ¬ G.Adj (Sum.inr b) (Sum.inr b'))

/-- Every graph constructed via `boolToBipartiteGraph` is bipartite-on-sum. -/
lemma boolToBipartiteGraph_isBipartiteOnSum
    (f : Fin n_A × Fin n_B → Bool) :
    IsBipartiteOnSum (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph f) :=
  ⟨fun a a' => DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_not_adj_inl_inl f a a',
   fun b b' => DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_not_adj_inr_inr f b b'⟩

/-! ## crossPairToEdge: bipartite-pair → G.edgeSet -/

/-- The `G`-edge associated to a cross-block pair `(a, b)` with adjacency
proof `h : G.Adj (inl a) (inr b)`. -/
def crossPairToEdge
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    (ab : Fin n_A × Fin n_B)
    (h : G.Adj (Sum.inl ab.1) (Sum.inr ab.2)) :
    G.edgeSet :=
  ⟨s(Sum.inl ab.1, Sum.inr ab.2), G.mem_edgeSet.mpr h⟩

@[simp] lemma crossPairToEdge_val
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    (ab : Fin n_A × Fin n_B)
    (h : G.Adj (Sum.inl ab.1) (Sum.inr ab.2)) :
    (crossPairToEdge G ab h : Sym2 (Fin n_A ⊕ Fin n_B)) = s(Sum.inl ab.1, Sum.inr ab.2) :=
  rfl

/-- **Helper (share-vertex case)**: two cross-pair edges with disjoint
`A`-coordinates and disjoint `B`-coordinates have no shared vertex. -/
private lemma cross_edges_no_shared_vertex
    {a₁ a₂ : Fin n_A} {b₁ b₂ : Fin n_B}
    (h_a : a₁ ≠ a₂) (h_b : b₁ ≠ b₂) :
    ¬ ((s(Sum.inl a₁, Sum.inr b₁) : Set (Fin n_A ⊕ Fin n_B)) ∩
       (s(Sum.inl a₂, Sum.inr b₂) : Set (Fin n_A ⊕ Fin n_B))).Nonempty := by
  rintro ⟨x, hx₁, hx₂⟩
  rw [Sym2.coe_mk] at hx₁ hx₂
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx₁ hx₂
  rcases hx₁ with h₁ | h₁ <;> rcases hx₂ with h₂ | h₂
  · exact h_a (Sum.inl.inj (h₁.symm.trans h₂))
  · exact Sum.inl_ne_inr (h₁.symm.trans h₂)
  · exact Sum.inl_ne_inr (h₂.symm.trans h₁)
  · exact h_b (Sum.inr.inj (h₁.symm.trans h₂))

/-- **Helper (bridge case)**: under bipartite-on-sum and matching
hypotheses, no `G`-edge `e₃` bridges between two cross-pair edges. -/
private lemma cross_edges_no_bridge
    {G : SimpleGraph (Fin n_A ⊕ Fin n_B)}
    (h_bip : IsBipartiteOnSum G)
    {a₁ a₂ : Fin n_A} {b₁ b₂ : Fin n_B}
    (h_a : a₁ ≠ a₂) (h_b : b₁ ≠ b₂)
    (h_diag1 : ¬ G.Adj (Sum.inl a₁) (Sum.inr b₂))
    (h_diag2 : ¬ G.Adj (Sum.inl a₂) (Sum.inr b₁))
    (e₃ : G.edgeSet) :
    ¬ (((s(Sum.inl a₁, Sum.inr b₁) : Set (Fin n_A ⊕ Fin n_B)) ∩
          ((e₃ : Sym2 (Fin n_A ⊕ Fin n_B)) : Set _)).Nonempty ∧
       (((e₃ : Sym2 (Fin n_A ⊕ Fin n_B)) : Set _) ∩
          (s(Sum.inl a₂, Sum.inr b₂) : Set (Fin n_A ⊕ Fin n_B))).Nonempty) := by
  rintro ⟨⟨x, hx_e1, hx_e3⟩, ⟨y, hy_e3, hy_e2⟩⟩
  by_cases hxy : x = y
  · refine cross_edges_no_shared_vertex h_a h_b ⟨x, hx_e1, ?_⟩
    exact hxy ▸ hy_e2
  · have h_e3_eq : (e₃ : Sym2 (Fin n_A ⊕ Fin n_B)) = s(x, y) :=
      (Sym2.mem_and_mem_iff hxy).mp ⟨hx_e3, hy_e3⟩
    have h_adj_xy : G.Adj x y := by
      have h_in : (e₃ : Sym2 _) ∈ G.edgeSet := e₃.property
      rw [h_e3_eq] at h_in
      exact G.mem_edgeSet.mp h_in
    rw [Sym2.coe_mk, Set.mem_insert_iff, Set.mem_singleton_iff] at hx_e1 hy_e2
    rcases hx_e1 with hx | hx <;> rcases hy_e2 with hy | hy
    · exact h_bip.1 a₁ a₂ (hx ▸ hy ▸ h_adj_xy)
    · exact h_diag1 (hx ▸ hy ▸ h_adj_xy)
    · exact h_diag2 (hy ▸ hx ▸ h_adj_xy.symm)
    · exact h_bip.2 b₁ b₂ (hx ▸ hy ▸ h_adj_xy)

/-- Different cross-pairs yield different edges (in any graph — the
edge encoding `s(inl a, inr b)` uniquely identifies `(a, b)`). -/
lemma crossPairToEdge_injective
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    {ab₁ ab₂ : Fin n_A × Fin n_B}
    {h₁ : G.Adj (Sum.inl ab₁.1) (Sum.inr ab₁.2)}
    {h₂ : G.Adj (Sum.inl ab₂.1) (Sum.inr ab₂.2)}
    (heq : crossPairToEdge G ab₁ h₁ = crossPairToEdge G ab₂ h₂) :
    ab₁ = ab₂ := by
  have hsym2 : s(Sum.inl ab₁.1, Sum.inr ab₁.2)
             = s(Sum.inl ab₂.1, Sum.inr ab₂.2) := Subtype.mk_eq_mk.mp heq
  rw [Sym2.eq_iff] at hsym2
  rcases hsym2 with ⟨h_a, h_b⟩ | ⟨h_x, _⟩
  · exact Prod.ext (Sum.inl.inj h_a) (Sum.inr.inj h_b)
  · exact (Sum.inl_ne_inr h_x).elim

/-! ## Bridge: bipartite-pair induced matching → generic induced matching -/

/-- **Main bridge (cycle 14)**: under `IsBipartiteOnSum G`, a
`IsBipartiteInducedMatching G M` (on cross-pairs) lifts to a generic
`IsInducedMatching G` on the corresponding image in `G.edgeSet`. -/
theorem IsBipartiteInducedMatching.toIsInducedMatching
    {G : SimpleGraph (Fin n_A ⊕ Fin n_B)} [DecidableRel G.Adj]
    (h_bip : IsBipartiteOnSum G)
    {M : Finset (Fin n_A × Fin n_B)}
    (h_adj : ∀ ab ∈ M, G.Adj (Sum.inl ab.1) (Sum.inr ab.2))
    (h_M : IsBipartiteInducedMatching G M) :
    IsInducedMatching G
      { e : G.edgeSet | ∃ ab : Fin n_A × Fin n_B,
          ∃ h_in : ab ∈ M, e = crossPairToEdge G ab (h_adj ab h_in) } := by
  intro e₁ he₁ e₂ he₂ h_ne h_adj_e
  obtain ⟨ab₁, h_in_1, h_e1⟩ := he₁
  obtain ⟨ab₂, h_in_2, h_e2⟩ := he₂
  subst h_e1; subst h_e2
  have h_ab_ne : ab₁ ≠ ab₂ := by
    intro h_eq
    apply h_ne
    apply Subtype.ext
    change s(Sum.inl ab₁.1, Sum.inr ab₁.2) = s(Sum.inl ab₂.1, Sum.inr ab₂.2)
    rw [h_eq]
  obtain ⟨h_a, h_b, h_diag1, h_diag2⟩ := h_M ab₁ h_in_1 ab₂ h_in_2 h_ab_ne
  obtain ⟨_, h_or⟩ := h_adj_e
  -- Rewrite the Sym2 coercions of the crossPairToEdge values.
  simp only [crossPairToEdge_val] at h_or
  rcases h_or with h_share | ⟨e₃, h_e3_e1, h_e3_e2⟩
  · exact cross_edges_no_shared_vertex h_a h_b h_share
  · exact cross_edges_no_bridge h_bip h_a h_b h_diag1 h_diag2 e₃ ⟨h_e3_e1, h_e3_e2⟩

/-! ## Lifting pair-finsets to edge-finsets

Convert a `Finset (Fin n_A × Fin n_B)` of cross-pairs (with adjacency
proofs) to a `Finset G.edgeSet` via `crossPairToEdge`. The image
preserves `IsBipartiteInducedMatching` → `IsInducedMatching` (cycle 14
bridge) and has the same cardinality (cycle 11 injectivity). -/

/-- Lift a Finset of cross-pairs (with adjacency proofs) to a
`Finset G.edgeSet`. -/
noncomputable def pairsToEdges
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    (M : Finset (Fin n_A × Fin n_B))
    (h_adj : ∀ ab ∈ M, G.Adj (Sum.inl ab.1) (Sum.inr ab.2)) :
    Finset G.edgeSet :=
  M.attach.image (fun p => crossPairToEdge G p.val (h_adj p.val p.property))

/-- Membership: `e ∈ pairsToEdges G M h_adj` iff `e` arises from some
`ab ∈ M` via `crossPairToEdge`. -/
lemma mem_pairsToEdges
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    (M : Finset (Fin n_A × Fin n_B))
    (h_adj : ∀ ab ∈ M, G.Adj (Sum.inl ab.1) (Sum.inr ab.2))
    (e : G.edgeSet) :
    e ∈ pairsToEdges G M h_adj ↔
      ∃ ab : Fin n_A × Fin n_B, ∃ h_in : ab ∈ M,
        e = crossPairToEdge G ab (h_adj ab h_in) := by
  unfold pairsToEdges
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨ab, h_in⟩, _, h_eq⟩
    exact ⟨ab, h_in, h_eq.symm⟩
  · rintro ⟨ab, h_in, h_eq⟩
    exact ⟨⟨ab, h_in⟩, Finset.mem_attach _ _, h_eq.symm⟩

/-- `pairsToEdges` preserves cardinality (since `crossPairToEdge` is
injective). -/
lemma pairsToEdges_card
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    (M : Finset (Fin n_A × Fin n_B))
    (h_adj : ∀ ab ∈ M, G.Adj (Sum.inl ab.1) (Sum.inr ab.2)) :
    (pairsToEdges G M h_adj).card = M.card := by
  unfold pairsToEdges
  rw [Finset.card_image_of_injOn, Finset.card_attach]
  intro p _ q _ h
  apply Subtype.ext
  exact crossPairToEdge_injective G h

/-- Under `IsBipartiteOnSum G`, every edge of `G` factors uniquely through
`crossPairToEdge`. This is the structural surjectivity statement
complementing cycle-11's injectivity. -/
lemma edge_eq_crossPairToEdge
    {G : SimpleGraph (Fin n_A ⊕ Fin n_B)}
    (h_bip : IsBipartiteOnSum G)
    (e : G.edgeSet) :
    ∃ ab : Fin n_A × Fin n_B, ∃ h : G.Adj (Sum.inl ab.1) (Sum.inr ab.2),
      e = crossPairToEdge G ab h := by
  obtain ⟨u, v, h_e_val⟩ : ∃ u v, (e : Sym2 (Fin n_A ⊕ Fin n_B)) = s(u, v) := by
    obtain ⟨⟨u, v⟩, hr⟩ := Quot.exists_rep (e.val)
    exact ⟨u, v, hr.symm⟩
  have h_adj_uv : G.Adj u v := by
    have h_in : (e : Sym2 _) ∈ G.edgeSet := e.property
    rw [h_e_val] at h_in
    exact G.mem_edgeSet.mp h_in
  rcases u with a | b <;> rcases v with a' | b'
  · exact absurd h_adj_uv (h_bip.1 a a')
  · refine ⟨(a, b'), h_adj_uv, ?_⟩
    apply Subtype.ext
    exact h_e_val
  · refine ⟨(a', b), h_adj_uv.symm, ?_⟩
    apply Subtype.ext
    rw [h_e_val, Sym2.eq_swap]
    rfl
  · exact absurd h_adj_uv (h_bip.2 b b')

/-- Under `IsBipartiteOnSum G`, the cross-block pairs across all `(i, j)`
block indices cover all of `G.edgeSet`: every edge arises from a pair
in some `crossBlockPairs G (block A i) (block B j)` (via the canonical
block assignment `blockOf`). -/
theorem cover_blockPairs
    {G : SimpleGraph (Fin n_A ⊕ Fin n_B)} [DecidableRel G.Adj]
    (h_bip : IsBipartiteOnSum G)
    {s_A s_B : ℕ} (hsA : 0 < s_A) (hsB : 0 < s_B) (e : G.edgeSet) :
    ∃ i : Fin s_A, ∃ j : Fin s_B,
      ∃ ab : Fin n_A × Fin n_B,
        ab ∈ crossBlockPairs G (DaveyThesis2024.SecRandomBipartite.block n_A s_A hsA i)
                                (DaveyThesis2024.SecRandomBipartite.block n_B s_B hsB j) ∧
        ∃ h : G.Adj (Sum.inl ab.1) (Sum.inr ab.2), e = crossPairToEdge G ab h := by
  obtain ⟨ab, h_adj, h_eq⟩ := edge_eq_crossPairToEdge h_bip e
  refine ⟨DaveyThesis2024.SecRandomBipartite.blockOf n_A s_A hsA ab.1,
          DaveyThesis2024.SecRandomBipartite.blockOf n_B s_B hsB ab.2, ab, ?_, h_adj, h_eq⟩
  simp [mem_crossBlockPairs, DaveyThesis2024.SecRandomBipartite.mem_block, h_adj]

/-- Under `IsBipartiteOnSum G`, every edge factors through `crossPairToEdge`
via a **unique** pair (combining cycles 11 + 16). -/
theorem edge_uniquePair
    {G : SimpleGraph (Fin n_A ⊕ Fin n_B)}
    (h_bip : IsBipartiteOnSum G)
    (e : G.edgeSet) :
    ∃! ab : Fin n_A × Fin n_B,
      ∃ h : G.Adj (Sum.inl ab.1) (Sum.inr ab.2), e = crossPairToEdge G ab h := by
  obtain ⟨ab, h_adj, h_eq⟩ := edge_eq_crossPairToEdge h_bip e
  refine ⟨ab, ⟨h_adj, h_eq⟩, ?_⟩
  rintro ab' ⟨h_adj', h_eq'⟩
  exact crossPairToEdge_injective G (h_eq'.symm.trans h_eq)

/-- Under bipartite-on-sum, a `IsBipartiteInducedMatching` on pairs lifts
to a generic `IsInducedMatching` on the corresponding edges. (Cycle 14
bridge, packaged for the lifted edge set.) -/
lemma pairsToEdges_isInducedMatching
    {G : SimpleGraph (Fin n_A ⊕ Fin n_B)} [DecidableRel G.Adj]
    (h_bip : IsBipartiteOnSum G)
    {M : Finset (Fin n_A × Fin n_B)}
    (h_adj : ∀ ab ∈ M, G.Adj (Sum.inl ab.1) (Sum.inr ab.2))
    (h_M : IsBipartiteInducedMatching G M) :
    IsInducedMatching G ((pairsToEdges G M h_adj : Finset G.edgeSet) : Set G.edgeSet) := by
  intro e₁ he₁ e₂ he₂ h_ne h_adj_e
  rw [Finset.mem_coe, mem_pairsToEdges] at he₁ he₂
  exact IsBipartiteInducedMatching.toIsInducedMatching h_bip h_adj h_M
    e₁ he₁ e₂ he₂ h_ne h_adj_e

/-! ## Global combination: per-pair packings → chiPrimeS bound

Combine per-pair covers across all `(i, j)` block pairs to get a global
strong-edge-colouring bound. This is the C-CN.3 combination step. -/

/-- **Cycle 19 (combination)**: per-pair covers over all `(A_i, B_j)`
block pairs yield a `chiPrimeS G ≤ ∑ ij, |cover_pair ij|` bound. -/
theorem chiPrimeS_le_of_perPair_covers
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (h_bip : IsBipartiteOnSum G)
    {s_A s_B : ℕ} (hsA : 0 < s_A) (hsB : 0 < s_B)
    (cover_pair : Fin s_A → Fin s_B → Finset (Finset (Fin n_A × Fin n_B)))
    (h_subset : ∀ i j, ∀ M ∈ cover_pair i j,
        M ⊆ crossBlockPairs G
            (DaveyThesis2024.SecRandomBipartite.block n_A s_A hsA i)
            (DaveyThesis2024.SecRandomBipartite.block n_B s_B hsB j))
    (h_match : ∀ i j, ∀ M ∈ cover_pair i j, IsBipartiteInducedMatching G M)
    (h_covers : ∀ i j, ∀ ab ∈ crossBlockPairs G
            (DaveyThesis2024.SecRandomBipartite.block n_A s_A hsA i)
            (DaveyThesis2024.SecRandomBipartite.block n_B s_B hsB j),
        ∃ M ∈ cover_pair i j, ab ∈ M) :
    chiPrimeS G ≤
      ∑ ij : Fin s_A × Fin s_B, ((cover_pair ij.1 ij.2).card : ℕ∞) := by
  classical
  -- Adjacency-extractor: a pair `ab ∈ M ∈ cover_pair i j` yields `G.Adj ...`
  let adj_of : ∀ i j, ∀ (M : Finset (Fin n_A × Fin n_B)), M ∈ cover_pair i j →
      ∀ ab ∈ M, G.Adj (Sum.inl ab.1) (Sum.inr ab.2) := fun i j M h_M ab h_ab =>
    ((mem_crossBlockPairs G _ _ ab).mp (h_subset i j M h_M h_ab)).2.2
  -- Per-pair edge-cover from a single matching M with membership proof
  let lift : ∀ i j, ∀ M : {M' // M' ∈ cover_pair i j}, Finset G.edgeSet := fun i j ⟨M, h_M⟩ =>
    pairsToEdges G M (adj_of i j M h_M)
  -- Global cover: union over (i, j) and over each per-pair Finset
  let global : Finset (Finset G.edgeSet) :=
    (Finset.univ : Finset (Fin s_A × Fin s_B)).biUnion (fun ij =>
      (cover_pair ij.1 ij.2).attach.image (lift ij.1 ij.2))
  -- Each member of `global` is an induced matching
  have h_global_match : ∀ N ∈ global, IsInducedMatching G (N : Set G.edgeSet) := by
    intro N hN
    simp only [global, Finset.mem_biUnion, Finset.mem_univ, true_and,
               Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hN
    obtain ⟨ij, M, h_M_in, h_N_eq⟩ := hN
    rw [← h_N_eq]
    exact pairsToEdges_isInducedMatching h_bip (adj_of ij.1 ij.2 M h_M_in)
      (h_match ij.1 ij.2 M h_M_in)
  -- Every edge is covered
  have h_global_covers : ∀ e : G.edgeSet, ∃ N ∈ global, e ∈ N := by
    intro e
    obtain ⟨i, j, ab, h_ab_in_cross, h_adj_ab, h_e_eq⟩ :=
      cover_blockPairs h_bip hsA hsB e
    obtain ⟨M, h_M_in, h_ab_in_M⟩ := h_covers i j ab h_ab_in_cross
    refine ⟨lift i j ⟨M, h_M_in⟩, ?_, ?_⟩
    · simp only [global, Finset.mem_biUnion, Finset.mem_univ, true_and,
                 Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨(i, j), M, h_M_in, rfl⟩
    · rw [show lift i j ⟨M, h_M_in⟩ = pairsToEdges G M (adj_of i j M h_M_in) from rfl,
          mem_pairsToEdges]
      refine ⟨ab, h_ab_in_M, ?_⟩
      apply Subtype.ext
      exact congrArg Subtype.val h_e_eq
  -- Cardinality bound: global.card ≤ ∑ ij, (cover_pair ij.1 ij.2).card
  have h_global_card : global.card ≤
      ∑ ij : Fin s_A × Fin s_B, (cover_pair ij.1 ij.2).card := by
    calc global.card
        ≤ ∑ ij ∈ (Finset.univ : Finset (Fin s_A × Fin s_B)),
            ((cover_pair ij.1 ij.2).attach.image (lift ij.1 ij.2)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ ij ∈ (Finset.univ : Finset (Fin s_A × Fin s_B)),
            (cover_pair ij.1 ij.2).attach.card := by
          apply Finset.sum_le_sum
          intros ij _
          exact Finset.card_image_le
      _ = ∑ ij : Fin s_A × Fin s_B, (cover_pair ij.1 ij.2).card := by
          simp [Finset.card_attach]
  -- Combine via chiPrimeS_le_of_indMatchingCover (cycle 6)
  calc chiPrimeS G
      ≤ (global.card : ℕ∞) :=
        DaveyThesis2024.SecRandomBipartite.chiPrimeS_le_of_indMatchingCover G global h_global_match h_global_covers
    _ ≤ ((∑ ij : Fin s_A × Fin s_B, (cover_pair ij.1 ij.2).card : ℕ) : ℕ∞) := by
        exact_mod_cast h_global_card
    _ = ∑ ij : Fin s_A × Fin s_B, ((cover_pair ij.1 ij.2).card : ℕ∞) := by
        push_cast; rfl

/-- **Per-pair cover spec**: a `Finset (Finset (Fin n_A × Fin n_B))` that
is an induced-matching cover of `crossBlockPairs G S T`, sized ≤ `k`.

The probabilistic content of the bipartite CN nibble (FKS Lemma 7) is
precisely: a.a.s. over random bipartite `G`, such a `PerPairCover`
exists for the block-partition pair `(block A i, block B j)` with
`k = ⌈C · |A_i| · |B_j| · p / log(n_A · n_B)⌉`. -/
structure PerPairCover
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T : Finset (Fin n_B)) (k : ℕ) where
  cover : Finset (Finset (Fin n_A × Fin n_B))
  cover_size : cover.card ≤ k
  subset_cross : ∀ M ∈ cover, M ⊆ crossBlockPairs G S T
  is_matching : ∀ M ∈ cover, IsBipartiteInducedMatching G M
  covers : ∀ ab ∈ crossBlockPairs G S T, ∃ M ∈ cover, ab ∈ M

/-- **Cycle 20 (uniform corollary)**: if every per-pair cover is bounded
by a single `k`, then `chiPrimeS G ≤ s_A · s_B · k`. -/
theorem chiPrimeS_le_of_uniform_perPair_bound
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (h_bip : IsBipartiteOnSum G)
    {s_A s_B : ℕ} (hsA : 0 < s_A) (hsB : 0 < s_B)
    (cover_pair : Fin s_A → Fin s_B → Finset (Finset (Fin n_A × Fin n_B)))
    (h_subset : ∀ i j, ∀ M ∈ cover_pair i j,
        M ⊆ crossBlockPairs G
            (DaveyThesis2024.SecRandomBipartite.block n_A s_A hsA i)
            (DaveyThesis2024.SecRandomBipartite.block n_B s_B hsB j))
    (h_match : ∀ i j, ∀ M ∈ cover_pair i j, IsBipartiteInducedMatching G M)
    (h_covers : ∀ i j, ∀ ab ∈ crossBlockPairs G
            (DaveyThesis2024.SecRandomBipartite.block n_A s_A hsA i)
            (DaveyThesis2024.SecRandomBipartite.block n_B s_B hsB j),
        ∃ M ∈ cover_pair i j, ab ∈ M)
    (k : ℕ) (h_k : ∀ i j, (cover_pair i j).card ≤ k) :
    chiPrimeS G ≤ (s_A * s_B * k : ℕ∞) := by
  calc chiPrimeS G
      ≤ ∑ ij : Fin s_A × Fin s_B, ((cover_pair ij.1 ij.2).card : ℕ∞) :=
        chiPrimeS_le_of_perPair_covers G h_bip hsA hsB cover_pair
          h_subset h_match h_covers
    _ ≤ ∑ _ : Fin s_A × Fin s_B, (k : ℕ∞) :=
        Finset.sum_le_sum (fun ij _ => by exact_mod_cast h_k ij.1 ij.2)
    _ = (s_A * s_B * k : ℕ∞) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
              mul_assoc]

/-- **Trivial per-pair cover (cycle 22)**: each cross-pair gets its own
singleton matching. The resulting `PerPairCover` has size exactly
`|crossBlockPairs G S T|`, giving the loose deterministic bound
`chiPrimeS G ≤ |E(G)|`.

This is a sanity check that the `PerPairCover` API can be instantiated
constructively, and it provides the trivial baseline against which
the future FKS-Lemma-7 construction's improvement is measured. -/
noncomputable def trivialPerPairCover
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T : Finset (Fin n_B)) :
    PerPairCover G S T (crossBlockPairs G S T).card where
  cover := (crossBlockPairs G S T).image (fun ab => ({ab} : Finset (Fin n_A × Fin n_B)))
  cover_size := Finset.card_image_le
  subset_cross := by
    intro M hM
    rcases Finset.mem_image.mp hM with ⟨ab, h_ab, rfl⟩
    rwa [Finset.singleton_subset_iff]
  is_matching := by
    intro M hM
    rcases Finset.mem_image.mp hM with ⟨ab, _, rfl⟩
    exact isBipartiteInducedMatching_singleton G ab
  covers := by
    intro ab h_ab
    refine ⟨{ab}, ?_, Finset.mem_singleton_self ab⟩
    exact Finset.mem_image.mpr ⟨ab, h_ab, rfl⟩

/-- **Structural wrapper of cycle 20**: a collection of `PerPairCover`
objects (one per block-pair `(i, j)`, all of size ≤ `k`) yields
`chiPrimeS G ≤ s_A · s_B · k`. -/
theorem chiPrimeS_le_of_perPairCover_family
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (h_bip : IsBipartiteOnSum G)
    {s_A s_B : ℕ} (hsA : 0 < s_A) (hsB : 0 < s_B) (k : ℕ)
    (cov : ∀ (i : Fin s_A) (j : Fin s_B), PerPairCover G
        (DaveyThesis2024.SecRandomBipartite.block n_A s_A hsA i)
        (DaveyThesis2024.SecRandomBipartite.block n_B s_B hsB j) k) :
    chiPrimeS G ≤ (s_A * s_B * k : ℕ∞) :=
  chiPrimeS_le_of_uniform_perPair_bound G h_bip hsA hsB
    (fun i j => (cov i j).cover)
    (fun i j M h_M => (cov i j).subset_cross M h_M)
    (fun i j M h_M => (cov i j).is_matching M h_M)
    (fun i j ab h_ab => (cov i j).covers ab h_ab)
    k
    (fun i j => (cov i j).cover_size)

end DaveyThesis2024.SecRandomBipartite

/-! ## Relocated content

The atomic axiom `SECRandomBipartite.perPairCover_fks_aas_axiom` together
with its three direct consumers
(`perPair_packing_aas_FKS`, `chiPrimeS_nibble_quantitative_bound`,
`secRandomBipartite_aas`) were **relocated to**
`DaveyThesis2024/CN/Closure.lean` during F.7 Option A Phase α (2026-06-03).

The relocation puts them downstream of `PerPairAssembly`, `SlotAssignment`,
`GreedyTransversal`, and `FKSArith`, enabling subsequent phases of F.7
Option A to eliminate the axiom by composing Step A
(`keptSet_concentration_joint_aas`) with the marginalisation bridges.

Fully-qualified names (`SECRandomBipartite.*`) are preserved; downstream
consumers do not need to change. -/
