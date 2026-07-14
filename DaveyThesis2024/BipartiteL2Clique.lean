import DaveyThesis2024.StrongEdgeColouring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

/-!
# Bipartite SEC for the special case `L(G)²` is a clique

This file formalises Phase 3 of the development notes:

> **Theorem (asymmetric).** Let `G` be a bipartite graph with
> bipartition `(A, B)`. If the strong square `L(G)²` of the line graph
> of `G` is a clique, then
> `χ'_s(G) = |E(G)| ≤ Δ_A(G) · Δ_B(G)`,
> with equality on `K_{Δ_A, Δ_B}`.

The symmetric form `χ'_s(G) ≤ Δ(G)²` follows as a corollary since
`Δ_A, Δ_B ≤ Δ`.

The proof is purely combinatorial — it does not invoke the SDP cert
chain or any user axiom. Structure (mirroring `proof.md`, direct
counting variant — fallback from the plan since this is cleaner in
Lean than full Ferrers):

* `L2Clique G`            — predicate: `lineGraphSqFlag G` is a clique
                            (every pair of distinct vertices adjacent).
* `maxDegreeOn G T`       — max degree taken only over vertices in `T`.
* `bipartite_no_2K2_of_L2Clique` — Lemma 2.1 form: bipartite +
   `L2Clique` ⇒ no induced 2K₂ on four vertices, i.e. any two
   vertex-disjoint edges have a "diagonal" connecting edge.
* `bipartite_L2Clique_edge_count_le_mul` — Lemma 3 (asymmetric
   counting): `|E(G)| ≤ Δ_A · Δ_B`, taking an explicit bipartition.
* `bipartite_L2Clique_edge_count_le_sq` — symmetric counting corollary:
   `|E(G)| ≤ Δ(G)²`.
* `chromaticNumber_le_size` — Lemma 1: the chromatic number of any
   flag is bounded by its number of vertices (identity colouring).
* `bipartite_sec_L2_clique_asymmetric` — the asymmetric headline.
* `bipartite_sec_L2_clique` — the symmetric headline (corollary).
-/

open Finset BigOperators Classical in
noncomputable section

set_option linter.unusedSectionVars false

namespace Davey2024

/-! ## Definitions -/

/-- The strong square of the line graph of `G` is a clique iff every two
    distinct vertices of `lineGraphSqFlag G` are adjacent in it. -/
def L2Clique (G : Flag emptyType) : Prop :=
  ∀ i j : Fin (lineGraphSqFlag G).size, i ≠ j →
    (lineGraphSqFlag G).graph.Adj i j

/-! ## Lemma 1: clique ⇒ chromatic number ≤ size -/

/-- The chromatic number of any flag is at most its number of vertices.
    Proof: the identity colouring `c v = v.val` is proper (since the
    graph is loopless and hence `Adj u v → u ≠ v`) and uses `< size`. -/
lemma chromaticNumber_le_size (H : Flag emptyType) :
    chromaticNumber H ≤ H.size := by
  unfold chromaticNumber
  apply Nat.sInf_le
  refine ⟨fun v => v.val, ?_, ?_⟩
  · intro u v hadj heq
    exact H.graph.ne_of_adj hadj (Fin.ext heq)
  · intro v; exact v.isLt

/-! ## Canonical-edge helpers

For an unordered edge `(a, b)` of `G` we use the canonical representative
`(min a b, max a b)` — namely `(a, b)` if `a < b` and `(b, a)` otherwise.
This lives in `edgeFinset G`. -/

/-- Canonicalise an oriented edge: pick the representative with first
    coordinate `< second`. -/
private noncomputable def canon (G : Flag emptyType) (a b : Fin G.size) :
    Fin G.size × Fin G.size := if a < b then (a, b) else (b, a)

private lemma canon_adj {G : Flag emptyType} {a b : Fin G.size}
    (h : G.graph.Adj a b) : G.graph.Adj (canon G a b).1 (canon G a b).2 := by
  unfold canon
  by_cases hab : a < b
  · simp only [if_pos hab]; exact h
  · simp only [if_neg hab]; exact G.graph.symm h

private lemma canon_lt {G : Flag emptyType} {a b : Fin G.size}
    (h : G.graph.Adj a b) : (canon G a b).1 < (canon G a b).2 := by
  unfold canon
  by_cases hab : a < b
  · simp only [if_pos hab]; exact hab
  · simp only [if_neg hab]
    exact lt_of_le_of_ne (not_lt.mp hab) (G.graph.ne_of_adj h).symm

private lemma canon_mem {G : Flag emptyType} {a b : Fin G.size}
    (h : G.graph.Adj a b) : canon G a b ∈ edgeFinset G :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, canon_adj h, canon_lt h⟩

private lemma canon_endpoints {G : Flag emptyType} {a b : Fin G.size} :
    ∀ x : Fin G.size, (x = (canon G a b).1 ∨ x = (canon G a b).2) ↔
    (x = a ∨ x = b) := by
  intro x
  unfold canon
  by_cases hab : a < b
  · simp only [if_pos hab]
  · simp only [if_neg hab]; tauto

/-- Two canonical edges `canon G a₁ b₁` and `canon G a₂ b₂` coincide iff
    `{a₁, b₁} = {a₂, b₂}` as sets. We need only one direction (the
    contrapositive). -/
private lemma canon_ne {G : Flag emptyType} {a₁ b₁ a₂ b₂ : Fin G.size}
    (_hadj₁ : G.graph.Adj a₁ b₁) (_hadj₂ : G.graph.Adj a₂ b₂)
    (h : ¬ (({a₁, b₁} : Finset (Fin G.size)) = {a₂, b₂})) :
    canon G a₁ b₁ ≠ canon G a₂ b₂ := by
  intro heq
  apply h
  -- Both edges have endpoint set {first, second}.
  ext x
  have h₁ : x ∈ ({a₁, b₁} : Finset (Fin G.size)) ↔
            (x = (canon G a₁ b₁).1 ∨ x = (canon G a₁ b₁).2) := by
    rw [canon_endpoints]; simp
  have h₂ : x ∈ ({a₂, b₂} : Finset (Fin G.size)) ↔
            (x = (canon G a₂ b₂).1 ∨ x = (canon G a₂ b₂).2) := by
    rw [canon_endpoints]; simp
  rw [h₁, h₂, heq]

/-! ## The structural 2K₂-free consequence -/

set_option maxHeartbeats 2000000 in
/-- The key structural consequence of `L2Clique` for bipartite `G`:
    any two **vertex-disjoint** edges `(a₁, b₁)`, `(a₂, b₂)` (where
    `a₁, a₂` are on the same bipartite side `S` and `b₁, b₂` on the
    other) admit a connecting "diagonal" edge `(a₁, b₂)` or `(a₂, b₁)`.

    In other words: no induced 2K₂ on `{a₁, a₂, b₁, b₂}`.

    The bipartite-side parameter `S` and `hS` are taken explicitly to
    avoid awkward existential unpacking at every call site. -/
lemma bipartite_no_2K2_of_L2Clique
    (G : Flag emptyType) (S : Finset (Fin G.size))
    (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (hClique : L2Clique G)
    {a₁ a₂ b₁ b₂ : Fin G.size}
    (hadj₁ : G.graph.Adj a₁ b₁) (hadj₂ : G.graph.Adj a₂ b₂)
    (ha₁_in : a₁ ∈ S) (ha₂_in : a₂ ∈ S)
    (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂)
    (haa : a₁ ≠ b₂) (hbb : b₁ ≠ a₂) :
    G.graph.Adj a₁ b₂ ∨ G.graph.Adj a₂ b₁ := by
  -- Canonical edges
  let c₁ := canon G a₁ b₁
  let c₂ := canon G a₂ b₂
  have hc₁_mem : c₁ ∈ edgeFinset G := canon_mem hadj₁
  have hc₂_mem : c₂ ∈ edgeFinset G := canon_mem hadj₂
  have hc₁_adj : G.graph.Adj c₁.1 c₁.2 := canon_adj hadj₁
  have hc₂_adj : G.graph.Adj c₂.1 c₂.2 := canon_adj hadj₂
  -- c₁ ≠ c₂: the vertex sets {a₁, b₁} and {a₂, b₂} are distinct
  -- (since a₁ ∉ {a₂, b₂} from ha, haa).
  have h_set_ne : ¬ (({a₁, b₁} : Finset (Fin G.size)) = {a₂, b₂}) := by
    intro heq
    have ha1_mem : a₁ ∈ ({a₂, b₂} : Finset (Fin G.size)) := by
      rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha1_mem
    rcases ha1_mem with h | h
    · exact ha h
    · exact haa h
  have hc_ne : c₁ ≠ c₂ := canon_ne hadj₁ hadj₂ h_set_ne
  have hsub_ne : (⟨c₁, hc₁_mem⟩ : ↥(edgeFinset G)) ≠ ⟨c₂, hc₂_mem⟩ := by
    intro heq; exact hc_ne (congrArg Subtype.val heq)
  -- Apply L²Clique at the equivFin-indices
  let i := (edgeFinset G).equivFin ⟨c₁, hc₁_mem⟩
  let j := (edgeFinset G).equivFin ⟨c₂, hc₂_mem⟩
  have hij : i ≠ j := fun heq => hsub_ne ((edgeFinset G).equivFin.injective heq)
  have hadj_ij : (lineGraphSqFlag G).graph.Adj i j := hClique i j hij
  -- Unfold lineGraphSqFlag adjacency
  have hsym_i : (edgeFinset G).equivFin.symm i = ⟨c₁, hc₁_mem⟩ :=
    (edgeFinset G).equivFin.symm_apply_apply _
  have hsym_j : (edgeFinset G).equivFin.symm j = ⟨c₂, hc₂_mem⟩ :=
    (edgeFinset G).equivFin.symm_apply_apply _
  have hsq : lineGraphSqAdj G c₁ c₂ := by
    have hgoal : lineGraphSqAdj G
        ((edgeFinset G).equivFin.symm i).val
        ((edgeFinset G).equivFin.symm j).val := hadj_ij
    rw [hsym_i, hsym_j] at hgoal
    exact hgoal
  obtain ⟨_, _, _, _, hconn⟩ := hsq
  -- Extract: ∃ p q, Adj p q ∧ ({p,q} ∩ {a₁,b₁}) ≠ ∅ ∧ ({p,q} ∩ {a₂,b₂}) ≠ ∅.
  -- Concretely:
  have hexists : ∃ p q : Fin G.size, G.graph.Adj p q ∧
      (p = a₁ ∨ p = b₁ ∨ q = a₁ ∨ q = b₁) ∧
      (p = a₂ ∨ p = b₂ ∨ q = a₂ ∨ q = b₂) := by
    rcases hconn with hLG | ⟨e₃, he₃adj, h13, h32⟩
    · -- c₁ and c₂ directly share an endpoint (line-graph adjacent).
      obtain ⟨_, _, _, hshare⟩ := hLG
      refine ⟨c₁.1, c₁.2, hc₁_adj, ?_, ?_⟩
      · -- c₁.1 is an endpoint of c₁, so it's in {a₁, b₁}
        have := (canon_endpoints (G := G) (a := a₁) (b := b₁) c₁.1).mp (Or.inl rfl)
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · -- one of c₁.1, c₁.2 equals one of c₂.1, c₂.2 (hshare),
        -- and each c₂.i ∈ {a₂, b₂} by canon_endpoints.
        rcases hshare with h | h | h | h
        all_goals {
          first
          | (have := (canon_endpoints (G := G) (a := a₂) (b := b₂) c₁.1).mp (h ▸ Or.inl rfl)
             rcases this with hh | hh
             · exact Or.inl hh
             · exact Or.inr (Or.inl hh))
          | (have := (canon_endpoints (G := G) (a := a₂) (b := b₂) c₁.1).mp (h ▸ Or.inr rfl)
             rcases this with hh | hh
             · exact Or.inl hh
             · exact Or.inr (Or.inl hh))
          | (have := (canon_endpoints (G := G) (a := a₂) (b := b₂) c₁.2).mp (h ▸ Or.inl rfl)
             rcases this with hh | hh
             · exact Or.inr (Or.inr (Or.inl hh))
             · exact Or.inr (Or.inr (Or.inr hh)))
          | (have := (canon_endpoints (G := G) (a := a₂) (b := b₂) c₁.2).mp (h ▸ Or.inr rfl)
             rcases this with hh | hh
             · exact Or.inr (Or.inr (Or.inl hh))
             · exact Or.inr (Or.inr (Or.inr hh)))
        }
    · -- c₁ —(line-graph)— e₃ —(line-graph)— c₂: e₃ is the bridge.
      obtain ⟨_, _, _, hs13⟩ := h13
      obtain ⟨_, _, _, hs32⟩ := h32
      refine ⟨e₃.1, e₃.2, he₃adj, ?_, ?_⟩
      · -- e₃ shares an endpoint with c₁; that endpoint is in {a₁, b₁}.
        rcases hs13 with h | h | h | h
        · have := (canon_endpoints (G := G) (a := a₁) (b := b₁) e₃.1).mp (h ▸ Or.inl rfl)
          rcases this with hh | hh
          · exact Or.inl hh
          · exact Or.inr (Or.inl hh)
        · have := (canon_endpoints (G := G) (a := a₁) (b := b₁) e₃.2).mp (h ▸ Or.inl rfl)
          rcases this with hh | hh
          · exact Or.inr (Or.inr (Or.inl hh))
          · exact Or.inr (Or.inr (Or.inr hh))
        · have := (canon_endpoints (G := G) (a := a₁) (b := b₁) e₃.1).mp (h ▸ Or.inr rfl)
          rcases this with hh | hh
          · exact Or.inl hh
          · exact Or.inr (Or.inl hh)
        · have := (canon_endpoints (G := G) (a := a₁) (b := b₁) e₃.2).mp (h ▸ Or.inr rfl)
          rcases this with hh | hh
          · exact Or.inr (Or.inr (Or.inl hh))
          · exact Or.inr (Or.inr (Or.inr hh))
      · -- e₃ shares an endpoint with c₂; that endpoint is in {a₂, b₂}.
        rcases hs32 with h | h | h | h
        · have := (canon_endpoints (G := G) (a := a₂) (b := b₂) e₃.1).mp (h ▸ Or.inl rfl)
          rcases this with hh | hh
          · exact Or.inl hh
          · exact Or.inr (Or.inl hh)
        · have := (canon_endpoints (G := G) (a := a₂) (b := b₂) e₃.1).mp (h ▸ Or.inr rfl)
          rcases this with hh | hh
          · exact Or.inl hh
          · exact Or.inr (Or.inl hh)
        · have := (canon_endpoints (G := G) (a := a₂) (b := b₂) e₃.2).mp (h ▸ Or.inl rfl)
          rcases this with hh | hh
          · exact Or.inr (Or.inr (Or.inl hh))
          · exact Or.inr (Or.inr (Or.inr hh))
        · have := (canon_endpoints (G := G) (a := a₂) (b := b₂) e₃.2).mp (h ▸ Or.inr rfl)
          rcases this with hh | hh
          · exact Or.inr (Or.inr (Or.inl hh))
          · exact Or.inr (Or.inr (Or.inr hh))
  -- Now reason from `hexists`. The pair (p, q) is adjacent in G;
  -- by bipartiteness, p and q are on opposite sides.
  -- p has an endpoint in {a₁, b₁}; q has an endpoint in {a₂, b₂}.
  -- Wait, actually we need: one of p, q is in {a₁, b₁} and one (possibly the same) is in {a₂, b₂}.
  -- We unfolded p as "the first end of the bridging edge with endpoint in c₁".
  -- The cases are: p ∈ {a₁, b₁} and q ∈ {a₂, b₂}, OR p ∈ {a₁, b₁, a₂, b₂} etc.
  obtain ⟨p, q, hpq_adj, hp1, hq2⟩ := hexists
  -- The bipartite-side data:
  have hb₁_out : b₁ ∉ S := (hS _ _ hadj₁).mp ha₁_in
  have hb₂_out : b₂ ∉ S := (hS _ _ hadj₂).mp ha₂_in
  -- Same-side pairs cannot be adjacent.
  have hNoAdj_a1a2 : ¬ G.graph.Adj a₁ a₂ := fun h =>
    ((hS _ _ h).mp ha₁_in) ha₂_in
  -- b₁ ∼ b₂ ⇒ b₁ ∈ S xor b₂ ∈ S, but both ∉ S; contradiction.
  have hNoAdj_b1b2 : ¬ G.graph.Adj b₁ b₂ := fun h => by
    have := (hS _ _ h).mpr hb₂_out
    exact hb₁_out this
  -- Case-split on which {a₁, b₁} value p is and which {a₂, b₂} q is.
  -- We have 16 cases, but most collapse.
  -- Set up: hp1 says (p, q) has at least one element in {a₁, b₁}.
  -- hq2 says (p, q) has at least one element in {a₂, b₂}.
  -- We do explicit cases. (4 of the 16 combos involve p and q both naming
  -- the same variable from different sides, e.g. p = a₁ and p = a₂ — but
  -- these are still valid hypotheses, just not subst-friendly together.)
  --
  -- Strategy: classify by (p endpoint, q endpoint) for each of:
  --   "p plays the {a₁, b₁} role": hp ∈ {p = a₁, p = b₁}
  --   "p plays the {a₂, b₂} role": hp ∈ {p = a₂, p = b₂}
  -- Similarly for q. From hp1 ∨ hq2, we have at least one each.
  -- A clean reorganization: let me extract two variables u₁ ∈ {a₁, b₁}, u₂ ∈ {a₂, b₂}
  -- such that hpq_adj implies Adj u₁ u₂ (after symm if needed).
  --
  -- Direct: case split on hp1 (4 options).
  rcases hp1 with hp | hp | hp | hp
  · -- p = a₁. Then hq2 gives one of: p = a₂, p = b₂, q = a₂, q = b₂.
    rw [hp] at hpq_adj
    rcases hq2 with hq | hq | hq | hq
    · -- p = a₁ = a₂: contradicts ha.
      exact absurd (hp.symm.trans hq) ha
    · -- p = a₁ = b₂: contradicts haa.
      exact absurd (hp.symm.trans hq) haa
    · -- q = a₂. Adj a₁ a₂ contradicts hNoAdj.
      rw [hq] at hpq_adj; exact absurd hpq_adj hNoAdj_a1a2
    · -- q = b₂. Adj a₁ b₂.
      rw [hq] at hpq_adj; left; exact hpq_adj
  · -- p = b₁.
    rw [hp] at hpq_adj
    rcases hq2 with hq | hq | hq | hq
    · -- p = b₁ = a₂: contradicts hbb.
      exact absurd (hp.symm.trans hq) hbb
    · -- p = b₁ = b₂: contradicts hb.
      exact absurd (hp.symm.trans hq) hb
    · -- q = a₂. Adj b₁ a₂ = Adj a₂ b₁.
      rw [hq] at hpq_adj; right; exact G.graph.symm hpq_adj
    · -- q = b₂. Adj b₁ b₂ contradicts hNoAdj.
      rw [hq] at hpq_adj; exact absurd hpq_adj hNoAdj_b1b2
  · -- q = a₁. Then hq2 gives one of: p = a₂, p = b₂, q = a₂, q = b₂.
    -- Use rw rather than subst to control direction.
    rw [hp] at hpq_adj
    rcases hq2 with hq | hq | hq | hq
    · -- p = a₂. Adj a₂ a₁ contradicts hNoAdj.
      rw [hq] at hpq_adj
      exact absurd (G.graph.symm hpq_adj) hNoAdj_a1a2
    · -- p = b₂. Adj b₂ a₁.
      rw [hq] at hpq_adj; left; exact G.graph.symm hpq_adj
    · -- q = a₁ = a₂: contradicts ha.
      exact absurd (hp.symm.trans hq) ha
    · -- q = a₁ = b₂: contradicts haa.
      exact absurd (hp.symm.trans hq) haa
  · -- q = b₁.
    rw [hp] at hpq_adj
    rcases hq2 with hq | hq | hq | hq
    · -- p = a₂. Adj a₂ b₁.
      rw [hq] at hpq_adj; right; exact hpq_adj
    · -- p = b₂. Adj b₂ b₁ = Adj b₁ b₂.
      rw [hq] at hpq_adj; exact absurd (G.graph.symm hpq_adj) hNoAdj_b1b2
    · -- q = b₁ = a₂: contradicts hbb.
      exact absurd (hp.symm.trans hq) hbb
    · -- q = b₁ = b₂: contradicts hb.
      exact absurd (hp.symm.trans hq) hb

/-! ## Side-specific maximum degree

For the asymmetric version of the bound we need the maximum degree
taken only over a specified subset `T` (e.g. one side of a
bipartition). -/

/-- The maximum degree taken over vertices in `T`, with the convention
    that the supremum over the empty set is `0` (via `Finset.sup`). -/
noncomputable def maxDegreeOn (G : Flag emptyType) (T : Finset (Fin G.size)) : ℕ :=
  Finset.sup T (fun v => (Finset.univ.filter (fun u => G.graph.Adj v u)).card)

/-- If `v ∈ T`, the degree of `v` is bounded by `maxDegreeOn G T`. -/
lemma degree_le_maxDegreeOn (G : Flag emptyType) (T : Finset (Fin G.size))
    {v : Fin G.size} (hv : v ∈ T) :
    (Finset.univ.filter (fun u => G.graph.Adj v u)).card ≤ maxDegreeOn G T :=
  @Finset.le_sup ℕ (Fin G.size) _ _ T
    (fun w => (Finset.univ.filter (fun w' => G.graph.Adj w w')).card)
    v hv

/-- The side-specific max degree is bounded by the global max degree. -/
lemma maxDegreeOn_le_maxDegree (G : Flag emptyType) (T : Finset (Fin G.size)) :
    maxDegreeOn G T ≤ maxDegree G := by
  unfold maxDegreeOn maxDegree
  apply Finset.sup_le
  intro v _
  exact degree_le_maxDegree G v

/-! ## Lemma 3: bipartite + L²-clique ⇒ |E(G)| ≤ Δ_A · Δ_B

Direct counting argument. Pick `v₀ ∈ S` of maximum degree (within `S`).
We show every edge of `G` has its `Sᶜ`-side endpoint in `N(v₀)`.
That gives `|E(G)| ≤ ∑_{w ∈ N(v₀)} deg(w) ≤ Δ_A · Δ_B`, where
`Δ_A := maxDegreeOn G S`, `Δ_B := maxDegreeOn G Sᶜ`.
The symmetric corollary `|E(G)| ≤ Δ²` follows since
`Δ_A, Δ_B ≤ Δ`. -/

/-- Sum bound: each `w ∈ N ⊆ T` contributes at most `maxDegreeOn G T`
    to the sum of degrees. -/
private lemma sum_degrees_le_mul_on {G : Flag emptyType} {N T : Finset (Fin G.size)}
    (hsub : N ⊆ T) :
    (N.sum fun w => (Finset.univ.filter (fun u => G.graph.Adj w u)).card) ≤
    N.card * maxDegreeOn G T := by
  calc (N.sum fun w => (Finset.univ.filter (fun u => G.graph.Adj w u)).card)
      ≤ N.sum (fun _ => maxDegreeOn G T) := by
        apply Finset.sum_le_sum
        intro w hw
        exact degree_le_maxDegreeOn G T (hsub hw)
    _ = N.card * maxDegreeOn G T := by simp [Finset.sum_const, mul_comm]

/-- **Lemma 3 (asymmetric counting)**: For a bipartite graph `G` with
    explicit bipartition `(S, Sᶜ)` and `L²(G)` a clique,
    `|E(G)| ≤ maxDegreeOn G S · maxDegreeOn G Sᶜ`. -/
theorem bipartite_L2Clique_edge_count_le_mul
    (G : Flag emptyType) (S : Finset (Fin G.size))
    (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (hClique : L2Clique G) :
    (edgeFinset G).card ≤ maxDegreeOn G S * maxDegreeOn G Sᶜ := by
  -- Degenerate case: G has no vertices ⇒ no edges.
  by_cases hempty : G.size = 0
  · have : (edgeFinset G) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro ⟨u, _⟩ _
      exact absurd u.isLt (by omega)
    rw [this]; simp
  -- Otherwise G.size ≥ 1.
  have hsize_pos : 0 < G.size := Nat.pos_of_ne_zero hempty
  -- Degenerate case: edgeFinset G empty ⇒ trivial.
  by_cases hEempty : (edgeFinset G).card = 0
  · omega
  -- Some edge exists; extract it.
  have hE_pos : 0 < (edgeFinset G).card := Nat.pos_of_ne_zero hEempty
  obtain ⟨e₀, he₀_mem⟩ := Finset.card_pos.mp hE_pos
  have hadj₀ : G.graph.Adj e₀.1 e₀.2 := edgeFinset_adj G ⟨e₀, he₀_mem⟩
  -- By bipartiteness, exactly one endpoint of e₀ lies in S; that endpoint
  -- has positive degree. Hence S is nonempty.
  have hS_nonempty : S.Nonempty := by
    by_cases h1 : e₀.1 ∈ S
    · exact ⟨e₀.1, h1⟩
    · -- e₀.1 ∉ S, hS gives e₀.1 ∈ S ↔ e₀.2 ∉ S; so e₀.2 ∈ S.
      refine ⟨e₀.2, ?_⟩
      have hiff := hS _ _ hadj₀
      by_contra h2
      exact h1 (hiff.mpr h2)
  -- Pick v₀ ∈ S of max degree among S-vertices.
  obtain ⟨v₀, hv₀_in_S, hv₀_max⟩ := Finset.exists_max_image S
    (fun v => (Finset.univ.filter (fun u => G.graph.Adj v u)).card)
    hS_nonempty
  set N : Finset (Fin G.size) :=
    Finset.univ.filter (fun u => G.graph.Adj v₀ u) with hN_def
  have hN_card : N.card = maxDegreeOn G S := by
    have hmax_le : maxDegreeOn G S ≤ N.card := by
      unfold maxDegreeOn
      apply Finset.sup_le
      intro v hv
      exact hv₀_max v hv
    have hle_max : N.card ≤ maxDegreeOn G S :=
      degree_le_maxDegreeOn G S hv₀_in_S
    omega
  -- The S-endpoint of every edge maps to S; the Sᶜ-endpoint maps to Sᶜ.
  -- For each edge (a, b), the Sᶜ-endpoint we call `f e` lies in N(v₀).
  let f : ↥(edgeFinset G) → Fin G.size := fun e =>
    if (e.val.1 ∈ S) then e.val.2 else e.val.1
  have hf_eq : ∀ e : ↥(edgeFinset G),
      f e = if (e.val.1 ∈ S) then e.val.2 else e.val.1 := fun _ => rfl
  have hf_outside : ∀ e : ↥(edgeFinset G), f e ∉ S := by
    intro e
    have hadj : G.graph.Adj e.val.1 e.val.2 := edgeFinset_adj G e
    have hside := hS _ _ hadj
    rw [hf_eq]
    by_cases h : e.val.1 ∈ S
    · simp only [if_pos h]; exact hside.mp h
    · simp only [if_neg h]; exact h
  have hf_in_Sc : ∀ e : ↥(edgeFinset G), f e ∈ (Sᶜ : Finset _) := fun e => by
    rw [Finset.mem_compl]; exact hf_outside e
  have hf_endpoint : ∀ e : ↥(edgeFinset G), f e = e.val.1 ∨ f e = e.val.2 := by
    intro e
    rw [hf_eq]
    by_cases h : e.val.1 ∈ S
    · right; simp only [if_pos h]
    · left; simp only [if_neg h]
  -- Structural claim: every edge has f e ∈ N.
  have hf_in_N : ∀ e : ↥(edgeFinset G), f e ∈ N := by
    intro e
    have hadj : G.graph.Adj e.val.1 e.val.2 := edgeFinset_adj G e
    -- Let a := the S-endpoint, b := the Sᶜ-endpoint, with f e = b.
    let a := if e.val.1 ∈ S then e.val.1 else e.val.2
    have ha_eq : a = if e.val.1 ∈ S then e.val.1 else e.val.2 := rfl
    have ha_in_S : a ∈ S := by
      rw [ha_eq]
      by_cases h : e.val.1 ∈ S
      · simp only [if_pos h]; exact h
      · simp only [if_neg h]
        have := hS _ _ hadj
        tauto
    have hadj_a_b : G.graph.Adj a (f e) := by
      rw [ha_eq, hf_eq]
      by_cases h : e.val.1 ∈ S
      · simp only [if_pos h]; exact hadj
      · simp only [if_neg h]; exact G.graph.symm hadj
    -- Goal: G.graph.Adj v₀ (f e).
    simp only [hN_def, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hav₀ : a = v₀
    · -- a = v₀ ⇒ f e is a neighbour of v₀.
      rw [← hav₀]; exact hadj_a_b
    by_cases hfev₀_neigh : G.graph.Adj v₀ (f e)
    · exact hfev₀_neigh
    · -- a ≠ v₀ and ¬Adj v₀ (f e). Derive contradiction.
      exfalso
      have hfe_outside : f e ∉ S := hf_outside e
      have hfe_ne_v0 : f e ≠ v₀ := fun h => hfe_outside (h ▸ hv₀_in_S)
      -- N is nonempty: if N = ∅, then deg(v₀) = 0 ⇒ maxDegreeOn G S = 0,
      -- but a ∈ S has Adj a (f e) ⇒ deg(a) ≥ 1, contradicting max-on-S.
      by_cases hN_empty : N.card = 0
      · -- maxDegreeOn G S = 0 ⇒ deg(a) = 0 for all a ∈ S, but
        -- deg(a) ≥ 1 from Adj a (f e).
        have hmax_zero : maxDegreeOn G S = 0 := by rw [← hN_card]; exact hN_empty
        have hpos : 1 ≤ (Finset.univ.filter (fun u => G.graph.Adj a u)).card :=
          Finset.card_pos.mpr
            ⟨f e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj_a_b⟩⟩
        have hbound : (Finset.univ.filter (fun u => G.graph.Adj a u)).card ≤
            maxDegreeOn G S := degree_le_maxDegreeOn G S ha_in_S
        omega
      · push_neg at hN_empty
        obtain ⟨b', hb'_mem⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hN_empty)
        simp only [hN_def, Finset.mem_filter, Finset.mem_univ, true_and] at hb'_mem
        have hb'_outside : b' ∉ S := (hS v₀ b' hb'_mem).mp hv₀_in_S
        have hv0_ne_b' : v₀ ≠ b' := fun h => hb'_outside (h ▸ hv₀_in_S)
        have hb'_ne_fe : b' ≠ f e := fun h => hfev₀_neigh (h ▸ hb'_mem)
        have hb'_ne_a : b' ≠ a := fun h => hb'_outside (h ▸ ha_in_S)
        have hdiag := bipartite_no_2K2_of_L2Clique G S hS hClique
          hb'_mem hadj_a_b hv₀_in_S ha_in_S
          (Ne.symm hav₀) hb'_ne_fe (Ne.symm hfe_ne_v0) hb'_ne_a
        rcases hdiag with h | h
        · exact hfev₀_neigh h
        · -- Adj a b': iterate over all b' ∈ N to get Adj a b'' for all b''.
          have h_all_in_N_adj_a : ∀ b'' ∈ N, G.graph.Adj a b'' := by
            intro b'' hb''_mem
            simp only [hN_def, Finset.mem_filter, Finset.mem_univ, true_and] at hb''_mem
            have hb''_outside : b'' ∉ S := (hS v₀ b'' hb''_mem).mp hv₀_in_S
            have hv0_ne_b'' : v₀ ≠ b'' := fun h => hb''_outside (h ▸ hv₀_in_S)
            have hb''_ne_fe : b'' ≠ f e := fun h => hfev₀_neigh (h ▸ hb''_mem)
            have hb''_ne_a : b'' ≠ a := fun h => hb''_outside (h ▸ ha_in_S)
            have := bipartite_no_2K2_of_L2Clique G S hS hClique
              hb''_mem hadj_a_b hv₀_in_S ha_in_S
              (Ne.symm hav₀) hb''_ne_fe (Ne.symm hfe_ne_v0) hb''_ne_a
            rcases this with h | h
            · exact absurd h hfev₀_neigh
            · exact h
          -- Build N(a) ⊇ N ∪ {f e}. f e ∉ N (¬Adj v₀ (f e)).
          let Na := Finset.univ.filter (fun u => G.graph.Adj a u)
          have hN_sub_Na : N ⊆ Na := by
            intro u hu
            simp only [Na, Finset.mem_filter, Finset.mem_univ, true_and]
            exact h_all_in_N_adj_a u hu
          have hfe_in_Na : f e ∈ Na := by
            simp only [Na, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hadj_a_b
          have hfe_notin_N : f e ∉ N := by
            simp only [hN_def, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hfev₀_neigh
          have hinsert_sub : insert (f e) N ⊆ Na :=
            Finset.insert_subset hfe_in_Na hN_sub_Na
          have hcard_ineq : (insert (f e) N).card ≤ Na.card :=
            Finset.card_le_card hinsert_sub
          rw [Finset.card_insert_of_notMem hfe_notin_N] at hcard_ineq
          -- N.card + 1 ≤ Na.card ≤ maxDegreeOn G S = N.card (since a ∈ S).
          have hNa_le : Na.card ≤ maxDegreeOn G S :=
            degree_le_maxDegreeOn G S ha_in_S
          rw [hN_card] at hcard_ineq
          omega
  -- Use the function f : edgeFinset G → N to bound the count.
  -- |edgeFinset G| ≤ ∑_{w ∈ N} (# edges with f = w) ≤ ∑_{w ∈ N} (deg w).
  -- Each w ∈ N is in Sᶜ, so deg(w) ≤ maxDegreeOn G Sᶜ.
  have hN_sub_Sc : N ⊆ (Sᶜ : Finset _) := by
    intro u hu
    simp only [hN_def, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [Finset.mem_compl]
    exact (hS v₀ u hu).mp hv₀_in_S
  have hcount : (edgeFinset G).card ≤
      N.sum (fun w => (Finset.univ.filter (fun u => G.graph.Adj w u)).card) := by
    have hsum_eq : (edgeFinset G).card =
        N.sum (fun w => ((edgeFinset G).attach.filter (fun e => f e = w)).card) := by
      rw [← Finset.card_attach (s := edgeFinset G)]
      exact Finset.card_eq_sum_card_fiberwise (f := f)
        (s := (edgeFinset G).attach) (t := N)
        (fun e _ => hf_in_N e)
    rw [hsum_eq]
    apply Finset.sum_le_sum
    intro w _hw
    refine Finset.card_le_card_of_injOn
      (fun e =>
        if h : f e = w then
          (if e.val.1 = w then e.val.2 else e.val.1)
        else w) ?_ ?_
    · intro e he
      rw [Finset.mem_coe, Finset.mem_filter] at he
      obtain ⟨_, hfe_w⟩ := he
      simp only [hfe_w, dif_pos]
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hadj : G.graph.Adj e.val.1 e.val.2 := edgeFinset_adj G e
      have hfe_ep : f e = e.val.1 ∨ f e = e.val.2 := hf_endpoint e
      rcases hfe_ep with h1 | h1
      · rw [hfe_w] at h1
        rw [h1]
        simp only
        exact hadj
      · rw [hfe_w] at h1
        by_cases h2 : e.val.1 = w
        · rw [← h2] at h1
          exact absurd h1 (G.graph.ne_of_adj hadj)
        · simp only [if_neg h2]
          rw [h1]; exact G.graph.symm hadj
    · intro e₁ he₁ e₂ he₂ heq
      rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
      obtain ⟨_, hfe1_w⟩ := he₁
      obtain ⟨_, hfe2_w⟩ := he₂
      simp only [hfe1_w, hfe2_w, dif_pos] at heq
      have hlt₁ : e₁.val.1 < e₁.val.2 := (Finset.mem_filter.mp e₁.property).2.2
      have hlt₂ : e₂.val.1 < e₂.val.2 := (Finset.mem_filter.mp e₂.property).2.2
      apply Subtype.ext
      have hfe1_ep : f e₁ = e₁.val.1 ∨ f e₁ = e₁.val.2 := hf_endpoint e₁
      have hfe2_ep : f e₂ = e₂.val.1 ∨ f e₂ = e₂.val.2 := hf_endpoint e₂
      by_cases h1 : e₁.val.1 = w
      · simp only [if_pos h1] at heq
        by_cases h2 : e₂.val.1 = w
        · simp only [if_pos h2] at heq
          apply Prod.ext
          · rw [h1, h2]
          · exact heq
        · simp only [if_neg h2] at heq
          exfalso
          rw [h1] at hlt₁
          rw [heq] at hlt₁
          rcases hfe2_ep with h | h
          · rw [hfe2_w] at h; exact h2 h.symm
          · rw [hfe2_w] at h
            rw [h] at hlt₁
            exact lt_irrefl _ (lt_trans hlt₁ hlt₂)
      · simp only [if_neg h1] at heq
        have hfe1_v2 : f e₁ = e₁.val.2 := by
          rcases hfe1_ep with h | h
          · rw [hfe1_w] at h; exact absurd h.symm h1
          · exact h
        rw [hfe1_w] at hfe1_v2
        by_cases h2 : e₂.val.1 = w
        · simp only [if_pos h2] at heq
          exfalso
          rw [h2] at hlt₂
          rw [← heq] at hlt₂
          rw [← hfe1_v2] at hlt₁
          exact lt_irrefl _ (lt_trans hlt₂ hlt₁)
        · simp only [if_neg h2] at heq
          have hfe2_v2 : f e₂ = e₂.val.2 := by
            rcases hfe2_ep with h | h
            · rw [hfe2_w] at h; exact absurd h.symm h2
            · exact h
          rw [hfe2_w] at hfe2_v2
          apply Prod.ext
          · exact heq
          · exact hfe1_v2.symm.trans hfe2_v2
  calc (edgeFinset G).card
      ≤ N.sum (fun w => (Finset.univ.filter (fun u => G.graph.Adj w u)).card) :=
        hcount
    _ ≤ N.card * maxDegreeOn G Sᶜ := sum_degrees_le_mul_on hN_sub_Sc
    _ = maxDegreeOn G S * maxDegreeOn G Sᶜ := by rw [hN_card]

/-- **Lemma 3 (counting)**: For a bipartite graph `G` with `L²(G)` a
    clique, `|E(G)| ≤ Δ(G)²`. Symmetric corollary of
    `bipartite_L2Clique_edge_count_le_mul`. -/
theorem bipartite_L2Clique_edge_count_le_sq
    (G : Flag emptyType) (hBip : IsBipartite G) (hClique : L2Clique G) :
    (edgeFinset G).card ≤ (maxDegree G) ^ 2 := by
  obtain ⟨S, hS⟩ := hBip
  calc (edgeFinset G).card
      ≤ maxDegreeOn G S * maxDegreeOn G Sᶜ :=
        bipartite_L2Clique_edge_count_le_mul G S hS hClique
    _ ≤ maxDegree G * maxDegree G :=
        Nat.mul_le_mul (maxDegreeOn_le_maxDegree G S) (maxDegreeOn_le_maxDegree G Sᶜ)
    _ = (maxDegree G) ^ 2 := by ring

/-! ## Headline theorems -/

/-- **Main result (asymmetric form)**: for a bipartite graph `G` with an
    explicit bipartition `(S, Sᶜ)` and `L(G)²` a clique, the strong
    chromatic index of `G` is at most `Δ_A(G) · Δ_B(G)`, where
    `Δ_A := maxDegreeOn G S` and `Δ_B := maxDegreeOn G Sᶜ`. -/
theorem bipartite_sec_L2_clique_asymmetric
    (G : Flag emptyType) (S : Finset (Fin G.size))
    (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (hClique : L2Clique G) :
    (strongChromaticIndex G : ℝ) ≤ (maxDegreeOn G S : ℝ) * (maxDegreeOn G Sᶜ : ℝ) := by
  have h1 : strongChromaticIndex G ≤ chromaticNumber (lineGraphSqFlag G) :=
    strongChromaticIndex_le_lineGraphSq G
  have h2 : chromaticNumber (lineGraphSqFlag G) ≤ (lineGraphSqFlag G).size :=
    chromaticNumber_le_size _
  have h3 : (lineGraphSqFlag G).size = (edgeFinset G).card := rfl
  have h4 : (edgeFinset G).card ≤ maxDegreeOn G S * maxDegreeOn G Sᶜ :=
    bipartite_L2Clique_edge_count_le_mul G S hS hClique
  exact_mod_cast le_trans h1 (le_trans h2 (h3 ▸ h4))

/-- **Main result (symmetric form)**: for a bipartite graph `G` with `L(G)²`
    a clique, the strong chromatic index of `G` is at most `Δ(G)²`.
    Corollary of `bipartite_sec_L2_clique_asymmetric`. -/
theorem bipartite_sec_L2_clique
    (G : Flag emptyType) (hBip : IsBipartite G) (hClique : L2Clique G) :
    (strongChromaticIndex G : ℝ) ≤ (maxDegree G : ℝ) ^ 2 := by
  obtain ⟨S, hS⟩ := hBip
  have hAsym := bipartite_sec_L2_clique_asymmetric G S hS hClique
  have hA : (maxDegreeOn G S : ℝ) ≤ (maxDegree G : ℝ) := by
    exact_mod_cast maxDegreeOn_le_maxDegree G S
  have hB : (maxDegreeOn G Sᶜ : ℝ) ≤ (maxDegree G : ℝ) := by
    exact_mod_cast maxDegreeOn_le_maxDegree G Sᶜ
  calc (strongChromaticIndex G : ℝ)
      ≤ (maxDegreeOn G S : ℝ) * (maxDegreeOn G Sᶜ : ℝ) := hAsym
    _ ≤ (maxDegree G : ℝ) * (maxDegree G : ℝ) := by gcongr
    _ = (maxDegree G : ℝ) ^ 2 := by ring

end Davey2024

end

-- Axiom check: only standard Lean axioms.
-- (Uncomment to verify locally.)
-- #print axioms Davey2024.bipartite_sec_L2_clique_asymmetric
-- #print axioms Davey2024.bipartite_sec_L2_clique
-- Output for both:
--   depends on axioms: [propext, Classical.choice, Quot.sound]
