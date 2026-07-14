import DaveyThesis2024.BipartiteL2Clique

/-!
# Asymmetric induced-matching lower bound for bipartite graphs

This file formalises the **asymmetric reading of
Faudree--Gyárfás--Schelp--Tuza 1989, Theorem 1**:

> **Theorem.** Let `G` be a bipartite graph with bipartition `(A, B)` and
> side max degrees `Δ_A := maxDegreeOn G A` and `Δ_B := maxDegreeOn G B`.
> Then there exists an induced matching `M ⊆ E(G)` such that
> `|E(G)| ≤ |M| · Δ_A · Δ_B`.

Equivalently, the induced matching number satisfies
`ν_s(G) ≥ |E(G)| / (Δ_A · Δ_B)`.

The published FGST 1989 statement uses the symmetric max degree
`Δ = max(Δ_A, Δ_B)`. Reading their proof asymmetrically shows that
the two `Δ`-factors in inequality (1) of the paper correspond to two
**different** max-degree applications: `|B| ≤ p · Δ_A` (one factor per
`A`-vertex) and `|E| ≤ |B| · Δ_B` (one factor per `B`-vertex). The
proof never uses `Δ_A = Δ_B`.

## Strategy

The FGST proof in asymmetric form:

1. Pick `X ⊆ A` minimal with `Γ(X) = B \ Iso` (where `Iso` are
   `B`-vertices with no neighbours).
2. By minimality, for each `x ∈ X` there exists `y_x ∈ Γ(x)` with
   `y_x ∉ Γ(X \ {x})`. The set `{(x, y_x) : x ∈ X}` is an induced
   matching.
3. Inequality chain:
   `|E(G)| ≤ |Γ(X)| · Δ_B ≤ (Σ_{x ∈ X} |Γ(x)|) · Δ_B ≤ |X| · Δ_A · Δ_B`.

**Status (2026-05-23)**: Definitions + statement landed; proof in progress.
-/

open Finset BigOperators Classical in
noncomputable section

set_option linter.unusedSectionVars false

namespace Davey2024

/-! ## Induced matchings -/

/-- An **induced matching** of `G`: a finset of (canonical) edges of `G`
    that are pairwise non-adjacent in `L(G)²`. Equivalently, an
    independent set in `L(G)²`.

    The conditions:
    - every element is a valid canonical edge of `G`;
    - distinct edges are pairwise non-adjacent in `L(G)²`.

    Compare `IsAntimatching` (BipartiteOmegaL2.lean), which is the
    *clique* version (pairwise L²-adjacent).
-/
def IsInducedMatching (G : Flag emptyType)
    (M : Finset (Fin G.size × Fin G.size)) : Prop :=
  (∀ e ∈ M, G.graph.Adj e.1 e.2 ∧ e.1 < e.2) ∧
  (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ¬ lineGraphSqAdj G e₁ e₂)

/-- The **induced matching number** `ν_s(G)`: the maximum size of an
    induced matching of `G`. Equivalently, the independence number
    `α(L(G)²)`.

    Defined as the supremum of `k` such that there exists an induced
    matching of size `k`. The empty set is always an induced matching,
    so the supremum is well-defined and `≥ 0`. The set is bounded above
    by `(edgeFinset G).card`, so the `sSup` is attained.
-/
noncomputable def inducedMatchingNumber (G : Flag emptyType) : ℕ :=
  sSup {k : ℕ | ∃ M : Finset (Fin G.size × Fin G.size),
    M.card = k ∧ IsInducedMatching G M}

/-- The empty set is an induced matching (vacuously). -/
lemma isInducedMatching_empty (G : Flag emptyType) :
    IsInducedMatching G ∅ := by
  refine ⟨?_, ?_⟩ <;> intro e he <;> simp at he

/-- An induced matching has card at most the total edge count. -/
lemma isInducedMatching_card_le_edges
    (G : Flag emptyType) {M : Finset (Fin G.size × Fin G.size)}
    (hM : IsInducedMatching G M) :
    M.card ≤ (edgeFinset G).card := by
  apply Finset.card_le_card
  intro e he
  simp only [edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hM.1 e he

/-- The set of induced-matching cards is bounded above. -/
private lemma inducedMatchingNumber_bddAbove (G : Flag emptyType) :
    BddAbove {k : ℕ | ∃ M : Finset (Fin G.size × Fin G.size),
      M.card = k ∧ IsInducedMatching G M} := by
  refine ⟨(edgeFinset G).card, ?_⟩
  rintro k ⟨M, rfl, hM⟩
  exact isInducedMatching_card_le_edges G hM

/-- A specific induced matching `M` witnesses `ν_s(G) ≥ |M|`. -/
lemma le_inducedMatchingNumber_of_isInducedMatching
    (G : Flag emptyType) {M : Finset (Fin G.size × Fin G.size)}
    (hM : IsInducedMatching G M) :
    M.card ≤ inducedMatchingNumber G := by
  unfold inducedMatchingNumber
  exact le_csSup (inducedMatchingNumber_bddAbove G) ⟨M, rfl, hM⟩

/-! ## Main theorem: FGST 1989 asymmetric reading -/

/-! ### Helper lemmas for the main theorem -/

/-- Sum bound: each `w ∈ N ⊆ T` contributes at most `maxDegreeOn G T`
    to the sum of degrees. Duplicated from `BipartiteL2Clique.lean`
    (where it is private). -/
private lemma sum_degrees_le_mul_on_im {G : Flag emptyType}
    {N T : Finset (Fin G.size)} (hsub : N ⊆ T) :
    (N.sum fun w => (Finset.univ.filter (fun u => G.graph.Adj w u)).card) ≤
    N.card * maxDegreeOn G T := by
  calc (N.sum fun w => (Finset.univ.filter (fun u => G.graph.Adj w u)).card)
      ≤ N.sum (fun _ => maxDegreeOn G T) :=
        Finset.sum_le_sum (fun w hw => degree_le_maxDegreeOn G T (hsub hw))
    _ = N.card * maxDegreeOn G T := by simp [Finset.sum_const, mul_comm]

/-- Neighbours of a set `X ⊆ V(G)`: union of `N(x)` for `x ∈ X`. -/
private noncomputable def neighboursOf (G : Flag emptyType)
    (X : Finset (Fin G.size)) : Finset (Fin G.size) :=
  Finset.univ.filter (fun v => ∃ x ∈ X, G.graph.Adj x v)

private lemma mem_neighboursOf {G : Flag emptyType}
    {X : Finset (Fin G.size)} {v : Fin G.size} :
    v ∈ neighboursOf G X ↔ ∃ x ∈ X, G.graph.Adj x v := by
  simp [neighboursOf]

/-- The set of non-isolated `Sᶜ`-vertices: those with at least one neighbour in `S`. -/
private noncomputable def nonIsolatedSc (G : Flag emptyType)
    (S : Finset (Fin G.size)) : Finset (Fin G.size) :=
  (Sᶜ : Finset _).filter (fun b => ∃ a ∈ S, G.graph.Adj a b)

private lemma mem_nonIsolatedSc {G : Flag emptyType}
    {S : Finset (Fin G.size)} {b : Fin G.size} :
    b ∈ nonIsolatedSc G S ↔ b ∉ S ∧ ∃ a ∈ S, G.graph.Adj a b := by
  simp [nonIsolatedSc]

/-- Choose `X ⊆ S` of minimum cardinality such that `nonIsolatedSc G S ⊆ neighboursOf G X`. -/
private lemma exists_minimal_cover (G : Flag emptyType) (S : Finset (Fin G.size)) :
    ∃ X : Finset (Fin G.size),
      X ⊆ S ∧ nonIsolatedSc G S ⊆ neighboursOf G X ∧
      (∀ Y : Finset (Fin G.size),
        Y ⊆ S → nonIsolatedSc G S ⊆ neighboursOf G Y → X.card ≤ Y.card) := by
  classical
  let powS : Finset (Finset (Fin G.size)) :=
    S.powerset.filter (fun X => nonIsolatedSc G S ⊆ neighboursOf G X)
  have hS_self_cover : nonIsolatedSc G S ⊆ neighboursOf G S := fun b hb => by
    obtain ⟨_, a, haS, hadj⟩ := mem_nonIsolatedSc.mp hb
    exact mem_neighboursOf.mpr ⟨a, haS, hadj⟩
  have hne : powS.Nonempty :=
    ⟨S, by simp [powS, hS_self_cover]⟩
  obtain ⟨X, hXmem, hXmin⟩ :=
    Finset.exists_min_image powS (fun X => X.card) hne
  rw [Finset.mem_filter, Finset.mem_powerset] at hXmem
  refine ⟨X, hXmem.1, hXmem.2, fun Y hYsub hYcov =>
    hXmin Y (by simp [powS, hYsub, hYcov])⟩

/-- **Key minimality consequence**: if `X` is a minimum-cardinality cover,
    then for each `x ∈ X` there is a private witness `b` with `Adj x b`,
    `b ∉ S`, and no other `y ∈ X` adjacent to `b`. -/
private lemma exists_private_witness {G : Flag emptyType}
    {S : Finset (Fin G.size)} {X : Finset (Fin G.size)}
    (hXsub : X ⊆ S) (hXcov : nonIsolatedSc G S ⊆ neighboursOf G X)
    (hXmin : ∀ Y : Finset (Fin G.size), Y ⊆ S →
      nonIsolatedSc G S ⊆ neighboursOf G Y → X.card ≤ Y.card)
    {x : Fin G.size} (hx : x ∈ X) :
    ∃ b, G.graph.Adj x b ∧ b ∉ S ∧ ∀ y ∈ X, y ≠ x → ¬ G.graph.Adj y b := by
  classical
  by_contra hno
  push_neg at hno
  have hcov' : nonIsolatedSc G S ⊆ neighboursOf G (X.erase x) := fun b hb => by
    obtain ⟨y, hyX, hadj⟩ := mem_neighboursOf.mp (hXcov hb)
    by_cases hyx : y = x
    · -- `b` is reachable from `x`; use `hno` to get a witness `y' ∈ X.erase x`.
      have hbNS : b ∉ S := (mem_nonIsolatedSc.mp hb).1
      obtain ⟨y', hy'X, hy'ne, hy'adj⟩ := hno b (hyx ▸ hadj) hbNS
      exact mem_neighboursOf.mpr
        ⟨y', Finset.mem_erase.mpr ⟨hy'ne, hy'X⟩, hy'adj⟩
    · exact mem_neighboursOf.mpr
        ⟨y, Finset.mem_erase.mpr ⟨hyx, hyX⟩, hadj⟩
  have hcard := hXmin (X.erase x)
    (fun u hu => hXsub (Finset.mem_of_mem_erase hu)) hcov'
  rw [Finset.card_erase_of_mem hx] at hcard
  have hpos : 0 < X.card := Finset.card_pos.mpr ⟨x, hx⟩
  omega

/-- Canonicalise an edge by ordering. Generic over the carrier. -/
private noncomputable def canonEdge {n : ℕ} (u v : Fin n) : Fin n × Fin n :=
  if u < v then (u, v) else (v, u)

/-- Endpoints of `canonEdge u v` are `{u, v}` (in either order). -/
private lemma canonEdge_endpoints {n : ℕ} (u v : Fin n) :
    (canonEdge u v).1 = u ∧ (canonEdge u v).2 = v ∨
    (canonEdge u v).1 = v ∧ (canonEdge u v).2 = u := by
  unfold canonEdge
  by_cases h : u < v <;> simp [h]

/-- If `canonEdge u₁ v₁ = canonEdge u₂ v₂`, then either `(u₁, v₁) = (u₂, v₂)`
    or `(u₁, v₁) = (v₂, u₂)` (as unordered pairs). -/
private lemma canonEdge_eq_iff {n : ℕ} {u₁ v₁ u₂ v₂ : Fin n}
    (heq : canonEdge u₁ v₁ = canonEdge u₂ v₂) :
    (u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ = v₂ ∧ v₁ = u₂) := by
  unfold canonEdge at heq
  by_cases h1 : u₁ < v₁ <;> by_cases h2 : u₂ < v₂ <;>
    simp only [h1, h2, if_true, if_false, Prod.mk.injEq] at heq <;>
    first | exact Or.inl heq | exact Or.inr heq
          | exact Or.inr ⟨heq.2, heq.1⟩ | exact Or.inl ⟨heq.2, heq.1⟩

/-- A `canonEdge u v` (with `Adj u v` and `u ≠ v`) is a valid canonical edge. -/
private lemma canonEdge_isEdge {G : Flag emptyType} {u v : Fin G.size}
    (hadj : G.graph.Adj u v) (hne : u ≠ v) :
    G.graph.Adj (canonEdge u v).1 (canonEdge u v).2 ∧
      (canonEdge u v).1 < (canonEdge u v).2 := by
  unfold canonEdge
  by_cases hlt : u < v
  · simp [hlt, hadj]
  · simp only [if_neg hlt]
    push_neg at hlt
    exact ⟨G.graph.symm hadj, lt_of_le_of_ne hlt (Ne.symm hne)⟩

/-- **Non-adjacency in `L(G)²` for two bipartite edges with disjoint
    endpoints and no bridges.** If `x_i ∈ S`, `y_i ∉ S`, `Adj x_i y_i`,
    the `x_i` are distinct, the `y_i` are distinct, and there are no
    bridge edges `Adj x₁ y₂` or `Adj x₂ y₁`, then `canonEdge x₁ y₁` and
    `canonEdge x₂ y₂` are non-adjacent in `L(G)²`. -/
private lemma not_lineGraphSqAdj_bipartite
    {G : Flag emptyType} {S : Finset (Fin G.size)}
    (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    {x₁ y₁ x₂ y₂ : Fin G.size}
    (hx₁S : x₁ ∈ S) (hy₁S : y₁ ∉ S) (hadj₁ : G.graph.Adj x₁ y₁)
    (hx₂S : x₂ ∈ S) (hy₂S : y₂ ∉ S) (hadj₂ : G.graph.Adj x₂ y₂)
    (hxx : x₁ ≠ x₂) (hyy : y₁ ≠ y₂)
    (hnoadj₁₂ : ¬ G.graph.Adj x₁ y₂)
    (hnoadj₂₁ : ¬ G.graph.Adj x₂ y₁) :
    ¬ lineGraphSqAdj G (canonEdge x₁ y₁) (canonEdge x₂ y₂) := by
  intro hL2
  have hx₁_ne_y₂ : x₁ ≠ y₂ := fun h => hy₂S (h ▸ hx₁S)
  have hx₂_ne_y₁ : x₂ ≠ y₁ := fun h => hy₁S (h ▸ hx₂S)
  -- Endpoints of canonEdge x_i y_i lie in {x_i, y_i}.
  have eps : ∀ (u v : Fin G.size),
      ((canonEdge u v).1 = u ∨ (canonEdge u v).1 = v) ∧
      ((canonEdge u v).2 = u ∨ (canonEdge u v).2 = v) :=
    fun u v => (canonEdge_endpoints u v).elim
      (fun ⟨ha, hb⟩ => ⟨Or.inl ha, Or.inr hb⟩)
      (fun ⟨ha, hb⟩ => ⟨Or.inr ha, Or.inl hb⟩)
  obtain ⟨ep1a, ep1b⟩ := eps x₁ y₁
  obtain ⟨ep2a, ep2b⟩ := eps x₂ y₂
  -- Bridge: an endpoint-of-e_i-equals-{x_i,y_i} label forces False.
  have bridge : ∀ (u u' : Fin G.size),
      (u = x₁ ∨ u = y₁) → (u' = x₂ ∨ u' = y₂) → u = u' → False := by
    rintro u u' (hu | hu) (hu' | hu') heq <;> subst hu <;> subst hu' <;>
      [exact hxx heq; exact hx₁_ne_y₂ heq;
       exact hx₂_ne_y₁ heq.symm; exact hyy heq]
  obtain ⟨_, _, _, _, hconn⟩ := hL2
  rcases hconn with hLine | ⟨f, hadj_f, hL13, hL32⟩
  · -- Direct line-graph adjacency.
    obtain ⟨_, _, _, hshare⟩ := hLine
    rcases hshare with h | h | h | h
    · exact bridge _ _ ep1a ep2a h
    · exact bridge _ _ ep1a ep2b h
    · exact bridge _ _ ep1b ep2a h
    · exact bridge _ _ ep1b ep2b h
  · -- Path via edge f.
    obtain ⟨_, _, _, hshare₁⟩ := hL13
    obtain ⟨_, _, _, hshare₂⟩ := hL32
    have hf_bip := hS f.1 f.2 hadj_f
    have f_e1 : (f.1 = x₁ ∨ f.1 = y₁) ∨ (f.2 = x₁ ∨ f.2 = y₁) := by
      rcases hshare₁ with h | h | h | h <;>
        [exact Or.inl (h ▸ ep1a); exact Or.inr (h ▸ ep1a);
         exact Or.inl (h ▸ ep1b); exact Or.inr (h ▸ ep1b)]
    have f_e2 : (f.1 = x₂ ∨ f.1 = y₂) ∨ (f.2 = x₂ ∨ f.2 = y₂) := by
      rcases hshare₂ with h | h | h | h <;>
        [exact Or.inl (h.symm ▸ ep2a); exact Or.inl (h.symm ▸ ep2b);
         exact Or.inr (h.symm ▸ ep2a); exact Or.inr (h.symm ▸ ep2b)]
    have wlog_bridge : ∀ (fS fnS : Fin G.size), fS ∈ S → fnS ∉ S →
        G.graph.Adj fS fnS →
        (fS = x₁ ∨ fnS = y₁) → (fS = x₂ ∨ fnS = y₂) → False := by
      rintro fS fnS hfSin hfnSout hadj (hfx₁ | hfy₁) (hfx₂ | hfy₂)
      · exact hxx (hfx₁.symm.trans hfx₂)
      · exact hnoadj₁₂ (by rw [← hfx₁, ← hfy₂]; exact hadj)
      · exact hnoadj₂₁ (by rw [← hfx₂, ← hfy₁]; exact hadj)
      · exact hyy (hfy₁.symm.trans hfy₂)
    by_cases hf1S : f.1 ∈ S
    · have hf2_notS : f.2 ∉ S := hf_bip.mp hf1S
      refine wlog_bridge f.1 f.2 hf1S hf2_notS hadj_f ?_ ?_
      · rcases f_e1 with (h | h) | (h | h)
        · exact Or.inl h
        · exact (hy₁S (h ▸ hf1S)).elim
        · exact (hf2_notS (h.symm ▸ hx₁S)).elim
        · exact Or.inr h
      · rcases f_e2 with (h | h) | (h | h)
        · exact Or.inl h
        · exact (hy₂S (h ▸ hf1S)).elim
        · exact (hf2_notS (h.symm ▸ hx₂S)).elim
        · exact Or.inr h
    · have hf2_inS : f.2 ∈ S := not_not.mp (fun h => hf1S (hf_bip.mpr h))
      refine wlog_bridge f.2 f.1 hf2_inS hf1S (G.graph.symm hadj_f) ?_ ?_
      · rcases f_e1 with (h | h) | (h | h)
        · exact (hf1S (h.symm ▸ hx₁S)).elim
        · exact Or.inr h
        · exact Or.inl h
        · exact (hy₁S (h ▸ hf2_inS)).elim
      · rcases f_e2 with (h | h) | (h | h)
        · exact (hf1S (h.symm ▸ hx₂S)).elim
        · exact Or.inr h
        · exact Or.inl h
        · exact (hy₂S (h ▸ hf2_inS)).elim

/-- **Build an induced matching from `X` with private witnesses.** Given
    `X ⊆ S` in a bipartite graph and a private witness `b` for each
    `x ∈ X` (with `b ∉ S`, `Adj x b`, and no other `y ∈ X` adjacent to
    `b`), the set `{canonEdge x b_x : x ∈ X}` is an induced matching of
    size `|X|`. -/
private lemma induced_matching_from_minimal_cover
    {G : Flag emptyType} {S X : Finset (Fin G.size)}
    (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (hXsub : X ⊆ S)
    (hwit : ∀ x ∈ X, ∃ b : Fin G.size,
      G.graph.Adj x b ∧ b ∉ S ∧ ∀ y ∈ X, y ≠ x → ¬ G.graph.Adj y b) :
    ∃ M : Finset (Fin G.size × Fin G.size),
      IsInducedMatching G M ∧ M.card = X.card := by
  classical
  let bx : ∀ x ∈ X, Fin G.size := fun x hx => (hwit x hx).choose
  have hbx_adj : ∀ x (hx : x ∈ X), G.graph.Adj x (bx x hx) :=
    fun x hx => (hwit x hx).choose_spec.1
  have hbx_notS : ∀ x (hx : x ∈ X), bx x hx ∉ S :=
    fun x hx => (hwit x hx).choose_spec.2.1
  have hbx_no_other : ∀ x (hx : x ∈ X) y, y ∈ X → y ≠ x →
      ¬ G.graph.Adj y (bx x hx) :=
    fun x hx => (hwit x hx).choose_spec.2.2
  let M : Finset (Fin G.size × Fin G.size) :=
    X.attach.image (fun ⟨x, hx⟩ => canonEdge x (bx x hx))
  -- Injectivity.
  have hinj : Set.InjOn (fun (p : {x // x ∈ X}) => canonEdge p.val (bx p.val p.property))
      X.attach := by
    rintro ⟨x₁, hx₁⟩ _ ⟨x₂, hx₂⟩ _ heq
    apply Subtype.ext
    change x₁ = x₂
    rcases canonEdge_eq_iff heq with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd (h ▸ hXsub hx₁) (hbx_notS x₂ hx₂)
  have hM_card : M.card = X.card := by
    change (X.attach.image _).card = X.card
    rw [Finset.card_image_of_injOn hinj, Finset.card_attach]
  refine ⟨M, ⟨?_, ?_⟩, hM_card⟩
  · -- Each e ∈ M is a canonical edge.
    intro e he
    simp only [M, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at he
    obtain ⟨x, hx, hxeq⟩ := he
    subst hxeq
    exact canonEdge_isEdge (hbx_adj x hx)
      (fun h => hbx_notS x hx (h ▸ hXsub hx))
  · -- Pairwise non-L²-adjacency via not_lineGraphSqAdj_bipartite.
    intro e₁ he₁ e₂ he₂ hne₁₂ hL2
    simp only [M, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at he₁ he₂
    obtain ⟨x₁, hx₁, h1eq⟩ := he₁
    obtain ⟨x₂, hx₂, h2eq⟩ := he₂
    have hxne : x₁ ≠ x₂ := fun hxx => hne₁₂ (by
      rw [← h1eq, ← h2eq]; subst hxx; rfl)
    subst h1eq h2eq
    exact not_lineGraphSqAdj_bipartite hS
      (hXsub hx₁) (hbx_notS x₁ hx₁) (hbx_adj x₁ hx₁)
      (hXsub hx₂) (hbx_notS x₂ hx₂) (hbx_adj x₂ hx₂)
      hxne
      (fun h => hbx_no_other x₁ hx₁ x₂ hx₂ (Ne.symm hxne) (h ▸ hbx_adj x₂ hx₂))
      (hbx_no_other x₂ hx₂ x₁ hx₁ hxne)
      (hbx_no_other x₁ hx₁ x₂ hx₂ (Ne.symm hxne))
      hL2

/-- **Main theorem (FGST 1989 Thm 1, asymmetric form).** For a bipartite
    graph `G` with bipartition `(S, Sᶜ)` and side-specific max degrees
    `Δ_A := maxDegreeOn G S` and `Δ_B := maxDegreeOn G Sᶜ`, the edge
    count satisfies
    `|E(G)| ≤ ν_s(G) · Δ_A · Δ_B`.

    Equivalently, `ν_s(G) ≥ |E(G)| / (Δ_A · Δ_B)`. -/
theorem edges_le_nu_s_mul_mul_bipartite
    (G : Flag emptyType) (S : Finset (Fin G.size))
    (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S)) :
    (edgeFinset G).card ≤
      inducedMatchingNumber G * maxDegreeOn G S * maxDegreeOn G Sᶜ := by
  classical
  -- Step 1: pick a minimum cover X ⊆ S of nonIsolatedSc G S.
  obtain ⟨X, hXsub, hXcov, hXmin⟩ := exists_minimal_cover G S
  -- Step 2: produce the induced matching M with |M| = |X| via the private-
  -- witness oracle.
  obtain ⟨M, hM_isMatch, hM_card⟩ :=
    induced_matching_from_minimal_cover hS hXsub
      (fun x hx => exists_private_witness hXsub hXcov hXmin hx)
  -- Step 3: edge-counting chain.
  have hM_le_nu : M.card ≤ inducedMatchingNumber G :=
    le_inducedMatchingNumber_of_isInducedMatching G hM_isMatch
  -- Step 3a: B' := neighbours of X in Sᶜ. Each edge has its Sᶜ-endpoint in B'.
  set B' : Finset (Fin G.size) := (neighboursOf G X).filter (fun b => b ∉ S) with hB'_def
  have hB'_sub_Sc : B' ⊆ (Sᶜ : Finset _) := fun b hb =>
    Finset.mem_compl.mpr (Finset.mem_filter.mp hb).2
  -- scSide picks the Sᶜ-endpoint of an edge.
  let scSide : ↥(edgeFinset G) → Fin G.size :=
    fun e => if e.val.1 ∈ S then e.val.2 else e.val.1
  -- Joint property: scSide e is in nonIsolatedSc G S, hence in B'.
  have hscSide_in_B' : ∀ e : ↥(edgeFinset G), scSide e ∈ B' := by
    intro e
    have hadj : G.graph.Adj e.val.1 e.val.2 := edgeFinset_adj G e
    have hiff := hS _ _ hadj
    rw [hB'_def, Finset.mem_filter]
    -- One by_cases handles both the "∉ S" goal and the "∃ a ∈ S, Adj a (scSide e)" goal.
    by_cases h : e.val.1 ∈ S
    · simp only [scSide, if_pos h]
      refine ⟨hXcov ?_, hiff.mp h⟩
      exact mem_nonIsolatedSc.mpr ⟨hiff.mp h, e.val.1, h, hadj⟩
    · simp only [scSide, if_neg h]
      have hother : e.val.2 ∈ S := not_not.mp fun h2 => h (hiff.mpr h2)
      refine ⟨hXcov ?_, h⟩
      exact mem_nonIsolatedSc.mpr ⟨h, e.val.2, hother, G.graph.symm hadj⟩
  -- Count edges via fibers of scSide over B'.
  have hsum_eq : (edgeFinset G).card =
      B'.sum (fun b => ((edgeFinset G).attach.filter (fun e => scSide e = b)).card) := by
    rw [← Finset.card_attach (s := edgeFinset G)]
    exact Finset.card_eq_sum_card_fiberwise (fun e _ => hscSide_in_B' e)
  have hedge_lt : ∀ e : ↥(edgeFinset G), e.val.1 < e.val.2 := fun e =>
    (Finset.mem_filter.mp e.property).2.2
  -- For a fiber e ↦ b, the *other* endpoint of e (the one ≠ b) determines e uniquely
  -- (given b is fixed and e.1 < e.2). Inject via "other endpoint".
  have hfiber_le_deg : ∀ b ∈ B',
      ((edgeFinset G).attach.filter (fun e => scSide e = b)).card ≤
      (Finset.univ.filter (fun u => G.graph.Adj b u)).card := by
    intro b hb
    have hb_notS : b ∉ S := (Finset.mem_filter.mp hb).2
    -- For e in the fiber: scSide e = b. So e.val.1 = b or e.val.2 = b
    -- (depending on whether e.val.1 ∈ S).
    have hep : ∀ e ∈ (edgeFinset G).attach.filter (fun e => scSide e = b),
        (e : ↥(edgeFinset G)).val.1 = b ∨ (e : ↥(edgeFinset G)).val.2 = b := by
      intro e he
      have hfe := (Finset.mem_filter.mp he).2
      by_cases h : e.val.1 ∈ S
      · right; simpa [scSide, if_pos h] using hfe
      · left; simpa [scSide, if_neg h] using hfe
    -- Inject by "the endpoint that isn't b" (using e.1 < e.2 to break ties).
    refine Finset.card_le_card_of_injOn
      (fun e => if e.val.1 = b then e.val.2 else e.val.1) ?_ ?_
    · intro e he
      have hadj : G.graph.Adj e.val.1 e.val.2 := edgeFinset_adj G e
      rw [Finset.mem_coe, Finset.mem_filter] at he ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only []
      rcases hep e (by simpa using he) with h1 | h1
      · rw [if_pos h1, ← h1]; exact hadj
      · have hne : e.val.1 ≠ b := fun h' =>
          absurd (hedge_lt e) (by rw [h', h1]; exact lt_irrefl _)
        rw [if_neg hne, ← h1]; exact G.graph.symm hadj
    · intro e₁ he₁ e₂ he₂ heq
      have hlt₁ := hedge_lt e₁
      have hlt₂ := hedge_lt e₂
      have hep₁ := hep e₁ (by simpa using he₁)
      have hep₂ := hep e₂ (by simpa using he₂)
      simp only [] at heq
      -- Helper: from "e.2 = b" derive "e.1 ≠ b" using e.1 < e.2.
      have ne_of_snd : ∀ (e : Fin G.size × Fin G.size), e.1 < e.2 → e.2 = b → e.1 ≠ b :=
        fun e hlt hes h' => absurd hlt (by rw [h', hes]; exact lt_irrefl _)
      apply Subtype.ext
      have : e₁.val = e₂.val := by
        rcases hep₁ with h1 | h1 <;> rcases hep₂ with h2 | h2
        · rw [if_pos h1, if_pos h2] at heq
          exact Prod.ext (h1.trans h2.symm) heq
        · rw [if_pos h1, if_neg (ne_of_snd _ hlt₂ h2)] at heq
          -- heq : e₁.2 = e₂.1; hlt₁ has b < e₁.2 (via h1), hlt₂ has e₂.1 < b (via h2).
          exact absurd (h1 ▸ hlt₁) (lt_asymm (h2 ▸ heq ▸ hlt₂))
        · rw [if_neg (ne_of_snd _ hlt₁ h1), if_pos h2] at heq
          -- heq : e₁.1 = e₂.2; hlt₁ : e₁.1 < b (via h1), hlt₂ : b < e₁.1 (via h2, heq).
          exact absurd (h1 ▸ hlt₁) (lt_asymm (heq ▸ h2 ▸ hlt₂))
        · rw [if_neg (ne_of_snd _ hlt₁ h1), if_neg (ne_of_snd _ hlt₂ h2)] at heq
          exact Prod.ext heq (h1.trans h2.symm)
      exact this
  -- Step 3b: |B'| ≤ |X| * Δ_A via B' ⊆ X.biUnion (N ·).
  have hB'_le : B'.card ≤ X.card * maxDegreeOn G S := by
    let N : Fin G.size → Finset (Fin G.size) :=
      fun x => Finset.univ.filter (fun u => G.graph.Adj x u)
    have hsub : B' ⊆ X.biUnion N := fun b hb => by
      have hneigh : b ∈ neighboursOf G X := (Finset.mem_filter.mp hb).1
      obtain ⟨x, hxX, hadj⟩ := mem_neighboursOf.mp hneigh
      exact Finset.mem_biUnion.mpr ⟨x, hxX, by simp [N, hadj]⟩
    calc B'.card
        ≤ (X.biUnion N).card := Finset.card_le_card hsub
      _ ≤ X.sum (fun x => (N x).card) := Finset.card_biUnion_le
      _ ≤ X.card * maxDegreeOn G S := sum_degrees_le_mul_on_im hXsub
  -- Step 4: chain everything.
  calc (edgeFinset G).card
      = B'.sum (fun b => ((edgeFinset G).attach.filter (fun e => scSide e = b)).card) :=
        hsum_eq
    _ ≤ B'.sum (fun b => (Finset.univ.filter (fun u => G.graph.Adj b u)).card) :=
        Finset.sum_le_sum fun b hb => hfiber_le_deg b hb
    _ ≤ B'.card * maxDegreeOn G Sᶜ := sum_degrees_le_mul_on_im hB'_sub_Sc
    _ ≤ (X.card * maxDegreeOn G S) * maxDegreeOn G Sᶜ :=
        Nat.mul_le_mul_right _ hB'_le
    _ = M.card * maxDegreeOn G S * maxDegreeOn G Sᶜ := by rw [hM_card]
    _ ≤ inducedMatchingNumber G * maxDegreeOn G S * maxDegreeOn G Sᶜ :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hM_le_nu)

/-- **Symmetric corollary (FGST 1989 Theorem 1 as published).**
    For a bipartite graph `G`,
    `|E(G)| ≤ ν_s(G) · Δ(G)²`.

    Follows from the asymmetric form via
    `maxDegreeOn G S ≤ maxDegree G` and `maxDegreeOn G Sᶜ ≤ maxDegree G`. -/
theorem edges_le_nu_s_mul_sq_bipartite
    (G : Flag emptyType) (hBip : IsBipartite G) :
    (edgeFinset G).card ≤ inducedMatchingNumber G * (maxDegree G) ^ 2 := by
  obtain ⟨S, hS⟩ := hBip
  calc (edgeFinset G).card
      ≤ inducedMatchingNumber G * maxDegreeOn G S * maxDegreeOn G Sᶜ :=
        edges_le_nu_s_mul_mul_bipartite G S hS
    _ ≤ inducedMatchingNumber G * maxDegree G * maxDegree G := by
        gcongr <;> apply maxDegreeOn_le_maxDegree
    _ = inducedMatchingNumber G * (maxDegree G) ^ 2 := by ring

end Davey2024

end
