import DaveyThesis2024.BipartiteL2Clique

/-!
# Asymmetric bipartite clique-number bound on `L(G)²`

This file formalises Phase 3 of the development notes:

> **Theorem.** Let `G` be a bipartite graph with bipartition `(A, B)`.
> Then `ω(L(G)²) ≤ Δ_A(G) · Δ_B(G)`.

Companion symmetric corollary:

> **Corollary (FGST 1990 / Śleszyńska-Nowak 2016).** For bipartite `G`,
> `ω(L(G)²) ≤ Δ(G)²`.

**Status (2026-05-23, simplified)**: FULLY CLOSED. The main theorem
`omega_lineGraphSq_le_mul_bipartite` is proved sorry-free, depending
only on `[propext, Classical.choice, Quot.sound]`.

The simplified §2.8 proof drops the auxiliary `x*` pivot vertex entirely.
Pick `z* ∈ S^c` with maximum H-degree `s` on the `S^c` side, set
`X' := N_G(z*) ∩ S` (so `|X'| ≤ Δ_B`), and let `S_super := {b ∈ S^c :
N_G(b) ∩ S ⊇ N_H(z*)}` (so `z* ∈ S_super` and `|S_super| ≤ Δ_A`).

**Key Lemma** (replaces the 4-class partition machinery):
If `b ∈ S^c \ S_super`, then every H-edge `(a, b)` has `a ∈ X'`. Proved
by bridge dichotomy at the pair (H-edge `(c, z*)` for some `c ∈ N_H(z*)`
with `c ∉ N_G(b)`, edge `(a, b)`).

**3-class partition** of `E(H)` by B-endpoint:
- (a) `b = z*`: contributes `s`.
- (b) `b ∈ S_super \ {z*}`: total `≤ (|S_super| - 1) · s`.
- (c) `b ∉ S_super`: by Key Lemma `a ∈ X'`; split into `N_H(z*)` (cost
  `s·(Δ_A - |S_super|)`) and `X' \ N_H(z*)` (cost `(Δ_B - s)(Δ_A - 1)`).

**Cancellation**: `(|S_super| - 1)·s + s·(Δ_A - |S_super|) = s·(Δ_A - 1)`.
Total: `|E(H)| ≤ s + (Δ_A - 1)·Δ_B ≤ Δ_A · Δ_B`.
-/

open Finset BigOperators Classical in
noncomputable section

set_option linter.unusedSectionVars false

namespace Davey2024

/-! ## Clique number on `Flag emptyType` -/

/-- The **clique number** ω(G): the maximum size of a clique in `G`.

    Defined as the supremum of `k` such that there exists a `Finset T`
    of size `k` with all pairs distinct ⇒ adjacent. The empty clique
    (`T = ∅`) has size 0, so the supremum is well-defined and `≥ 0`.
    The set is bounded above by `G.size` (any clique sits in `Fin G.size`),
    so the `sSup` is attained. -/
noncomputable def cliqueNumber (G : Flag emptyType) : ℕ :=
  sSup {k : ℕ | ∃ T : Finset (Fin G.size),
    T.card = k ∧ ∀ u ∈ T, ∀ v ∈ T, u ≠ v → G.graph.Adj u v}

/-- The clique number is bounded by the number of vertices. -/
lemma cliqueNumber_le_size (G : Flag emptyType) :
    cliqueNumber G ≤ G.size := by
  unfold cliqueNumber
  refine csSup_le ⟨0, ∅, by simp, fun u hu => absurd hu (by simp)⟩ ?_
  rintro k ⟨T, hcard, _⟩
  rw [← hcard]
  exact (Finset.card_le_univ T).trans_eq (by simp)

/-- The clique number is at most the chromatic number: any clique of size
    `k` requires `≥ k` colours. -/
lemma cliqueNumber_le_chromaticNumber (G : Flag emptyType) :
    cliqueNumber G ≤ chromaticNumber G := by
  unfold cliqueNumber chromaticNumber
  refine csSup_le ⟨0, ∅, by simp, fun u hu => absurd hu (by simp)⟩ ?_
  rintro k ⟨T, hcard, hT⟩
  refine le_csInf ⟨G.size, fun v => v.val,
    fun u v hadj heq => G.graph.ne_of_adj hadj (Fin.ext heq),
    fun v => v.isLt⟩ ?_
  rintro m ⟨c, hproper, hbound⟩
  rw [← hcard]
  have h_image_card : (T.image c).card = T.card :=
    Finset.card_image_of_injOn fun u hu v hv h => by
      by_contra hne; exact hproper u v (hT u hu v hv hne) h
  have h_image_sub : T.image c ⊆ Finset.range m := fun x hx => by
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hbound v)
  calc T.card = (T.image c).card := h_image_card.symm
    _ ≤ (Finset.range m).card := Finset.card_le_card h_image_sub
    _ = m := Finset.card_range m

/-! ## Antimatching infrastructure -/

/-- An **antimatching** of `G`: a finset of (canonical) edges of `G` such
    that any two are at distance `≤ 2` in `L(G)`, i.e., pairwise
    `lineGraphSqAdj`. Equivalently, the L²-clique condition on the
    selected edges. -/
def IsAntimatching (G : Flag emptyType) (H : Finset (Fin G.size × Fin G.size)) : Prop :=
  (∀ e ∈ H, G.graph.Adj e.1 e.2 ∧ e.1 < e.2) ∧
  (∀ e₁ ∈ H, ∀ e₂ ∈ H, e₁ ≠ e₂ → lineGraphSqAdj G e₁ e₂)

/-- The **H-degree** of a vertex `v` in antimatching `H`: number of edges
    of `H` incident to `v`. -/
noncomputable def hDegree {G : Flag emptyType}
    (H : Finset (Fin G.size × Fin G.size)) (v : Fin G.size) : ℕ :=
  (H.filter (fun e => e.1 = v ∨ e.2 = v)).card

/-- A clique `T` in `lineGraphSqFlag G` yields an antimatching: the image
    of `T` under the canonical-edge bijection. -/
private noncomputable def antimatchingOfClique (G : Flag emptyType)
    (T : Finset (Fin (lineGraphSqFlag G).size)) : Finset (Fin G.size × Fin G.size) :=
  T.image (fun i => ((edgeFinset G).equivFin.symm i).val)

private lemma antimatchingOfClique_card (G : Flag emptyType)
    (T : Finset (Fin (lineGraphSqFlag G).size)) :
    (antimatchingOfClique G T).card = T.card :=
  Finset.card_image_of_injOn fun _i _ _j _ heq =>
    (edgeFinset G).equivFin.symm.injective (Subtype.val_injective heq)

private lemma antimatchingOfClique_is_antimatching (G : Flag emptyType)
    (T : Finset (Fin (lineGraphSqFlag G).size))
    (hT : ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (lineGraphSqFlag G).graph.Adj u v) :
    IsAntimatching G (antimatchingOfClique G T) := by
  refine ⟨?_, ?_⟩
  · intro e he
    unfold antimatchingOfClique at he
    rw [Finset.mem_image] at he
    obtain ⟨i, _, rfl⟩ := he
    exact ⟨edgeFinset_adj G _,
      (Finset.mem_filter.mp ((edgeFinset G).equivFin.symm i).property).2.2⟩
  · intro e₁ he₁ e₂ he₂ hne
    unfold antimatchingOfClique at he₁ he₂
    rw [Finset.mem_image] at he₁ he₂
    obtain ⟨i, hiT, rfl⟩ := he₁
    obtain ⟨j, hjT, rfl⟩ := he₂
    exact hT i hiT j hjT (fun heq => hne (by rw [heq]))

/-! ## Auxiliary lemmas: edge-side decomposition -/

/-- For a bipartite graph `G` with bipartition `(S, Sᶜ)`, every edge of `G`
    has exactly one endpoint in `S` and one in `Sᶜ`. In particular, each
    edge of an antimatching is incident to exactly one `S`-vertex. -/
private lemma antimatching_edge_endpoints {G : Flag emptyType}
    {S : Finset (Fin G.size)}
    (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    {H : Finset (Fin G.size × Fin G.size)}
    (hH : IsAntimatching G H) (e : Fin G.size × Fin G.size) (he : e ∈ H) :
    (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S) := by
  have hiff := hS _ _ (hH.1 e he).1
  by_cases h : e.1 ∈ S
  · exact Or.inl ⟨h, hiff.mp h⟩
  · exact Or.inr ⟨h, not_not.mp fun h2 => h (hiff.mpr h2)⟩

/-- The `S`-endpoint extractor for edges in an antimatching of bipartite `G`. -/
private noncomputable def sEndpoint {G : Flag emptyType}
    (S : Finset (Fin G.size)) (e : Fin G.size × Fin G.size) : Fin G.size :=
  if e.1 ∈ S then e.1 else e.2

/-- The `Sᶜ`-endpoint extractor. -/
private noncomputable def scEndpoint {G : Flag emptyType}
    (S : Finset (Fin G.size)) (e : Fin G.size × Fin G.size) : Fin G.size :=
  if e.1 ∈ S then e.2 else e.1

private lemma sEndpoint_mem {G : Flag emptyType} {S : Finset (Fin G.size)}
    (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    {H : Finset (Fin G.size × Fin G.size)} (hH : IsAntimatching G H)
    {e : Fin G.size × Fin G.size} (he : e ∈ H) :
    sEndpoint S e ∈ S := by
  rcases antimatching_edge_endpoints hS hH e he with ⟨h1, _⟩ | ⟨h1, h2⟩ <;>
    simp [sEndpoint, *]

private lemma scEndpoint_notMem {G : Flag emptyType} {S : Finset (Fin G.size)}
    (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    {H : Finset (Fin G.size × Fin G.size)} (hH : IsAntimatching G H)
    {e : Fin G.size × Fin G.size} (he : e ∈ H) :
    scEndpoint S e ∉ S := by
  rcases antimatching_edge_endpoints hS hH e he with ⟨h1, h2⟩ | ⟨h1, _⟩ <;>
    simp [scEndpoint, *]

/-- The canonical sEndpoint–scEndpoint pair of an H-edge is adjacent in G.
    (Just `(hH.1 e he).1` reoriented via the `sEndpoint`/`scEndpoint` if-case.) -/
private lemma adj_sEndpoint_scEndpoint {G : Flag emptyType} {S : Finset (Fin G.size)}
    {H : Finset (Fin G.size × Fin G.size)} (hH : IsAntimatching G H)
    {e : Fin G.size × Fin G.size} (he : e ∈ H) :
    G.graph.Adj (sEndpoint S e) (scEndpoint S e) := by
  have hadj_e : G.graph.Adj e.1 e.2 := (hH.1 e he).1
  by_cases h1 : e.1 ∈ S
  · simpa [sEndpoint, scEndpoint, h1] using hadj_e
  · simpa [sEndpoint, scEndpoint, h1] using G.graph.symm hadj_e

/-- For `ys ∉ S`, an H-edge `e` with `e.1 = ys ∨ e.2 = ys` has `scEndpoint S e = ys`. -/
private lemma scEndpoint_eq_of_incident
    {G : Flag emptyType} {S : Finset (Fin G.size)}
    (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    {H : Finset (Fin G.size × Fin G.size)} (hH : IsAntimatching G H)
    {ys : Fin G.size} (hys_notin : ys ∉ S)
    {e : Fin G.size × Fin G.size} (he : e ∈ H)
    (hinc : e.1 = ys ∨ e.2 = ys) : scEndpoint S e = ys := by
  unfold scEndpoint
  by_cases h1 : e.1 ∈ S
  · simp only [if_pos h1]
    rcases hinc with h | h
    · exact absurd (h ▸ h1) hys_notin
    · exact h
  · simp only [if_neg h1]
    rcases hinc with h | h
    · exact h
    · have h_sep_mem : sEndpoint S e ∈ S := sEndpoint_mem hS hH he
      have h_sep_eq : sEndpoint S e = e.2 := by unfold sEndpoint; simp only [if_neg h1]
      exact absurd (h ▸ h_sep_eq ▸ h_sep_mem) hys_notin

/-- The `H`-degree of `v` is bounded by the `G`-degree of `v`. -/
private lemma hDegree_le_degree {G : Flag emptyType}
    {H : Finset (Fin G.size × Fin G.size)} (hH : IsAntimatching G H)
    (v : Fin G.size) :
    hDegree H v ≤ (Finset.univ.filter (fun u => G.graph.Adj v u)).card := by
  -- Each edge e ∈ H incident to v gives a unique G-neighbour u of v
  -- (the other endpoint). Bijection-via-injection.
  unfold hDegree
  refine Finset.card_le_card_of_injOn
    (fun e => if e.1 = v then e.2 else e.1) ?_ ?_
  · intro e he
    rw [Finset.mem_coe, Finset.mem_filter] at he
    obtain ⟨he_H, hep⟩ := he
    have hadj : G.graph.Adj e.1 e.2 := (hH.1 e he_H).1
    have hlt : e.1 < e.2 := (hH.1 e he_H).2
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hep with h | h
    · simp only [if_pos h]; rw [← h]; exact hadj
    · by_cases h1 : e.1 = v
      · simp only [if_pos h1]; rw [← h1]; exact hadj
      · simp only [if_neg h1]; rw [← h]; exact G.graph.symm hadj
  · intro e₁ he₁ e₂ he₂ heq
    rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
    obtain ⟨he₁_H, hep₁⟩ := he₁
    obtain ⟨he₂_H, hep₂⟩ := he₂
    have hlt₁ : e₁.1 < e₁.2 := (hH.1 e₁ he₁_H).2
    have hlt₂ : e₂.1 < e₂.2 := (hH.1 e₂ he₂_H).2
    apply Prod.ext
    · by_cases h1 : e₁.1 = v <;> by_cases h2 : e₂.1 = v
      · rw [h1, h2]
      · simp only [if_pos h1, if_neg h2] at heq
        rcases hep₂ with h | h
        · exact absurd h h2
        · exfalso; omega
      · simp only [if_neg h1, if_pos h2] at heq
        rcases hep₁ with h | h
        · exact absurd h h1
        · exfalso; omega
      · simpa only [if_neg h1, if_neg h2] using heq
    · by_cases h1 : e₁.1 = v <;> by_cases h2 : e₂.1 = v
      · simpa only [if_pos h1, if_pos h2] using heq
      · simp only [if_pos h1, if_neg h2] at heq
        rcases hep₂ with h | h
        · exact absurd h h2
        · exfalso; omega
      · simp only [if_neg h1, if_pos h2] at heq
        rcases hep₁ with h | h
        · exact absurd h h1
        · exfalso; omega
      · rcases hep₁ with h | h
        · exact absurd h h1
        · rcases hep₂ with h' | h'
          · exact absurd h' h2
          · rw [h, h']

/-- For `v ∈ S`, `hDegree H v ≤ maxDegreeOn G S`. -/
private lemma hDegree_le_maxDegreeOn {G : Flag emptyType}
    (S : Finset (Fin G.size))
    {H : Finset (Fin G.size × Fin G.size)} (hH : IsAntimatching G H)
    {v : Fin G.size} (hv : v ∈ S) :
    hDegree H v ≤ maxDegreeOn G S :=
  (hDegree_le_degree hH v).trans (degree_le_maxDegreeOn G S hv)

/-! ## Bridge dichotomy (Lemma 2.1 of proof.md §2.1)

The key structural fact behind the §2.8 partition argument: for any two
distinct antimatching edges, with sides decided by the bipartition, the
two edges must either share a vertex or be connected by a "bridge" edge.

Specialised here to the canonical form: given two H-edges with explicit
side data `a_i ∈ S, b_i ∉ S` and no vertex shared, there is a cross-edge
`Adj a₁ b₂ ∨ Adj a₂ b₁` in `G`. This is the antimatching-version of
`bipartite_no_2K2_of_L2Clique` from `BipartiteL2Clique.lean`. -/

/-- **Bridge dichotomy at arbitrary H-edges.** Given two distinct H-edges
    in bipartite `G` with named side-endpoints (`a_i := sEndpoint S e_i`,
    `b_i := scEndpoint S e_i`) and the four side-disequalities, derive
    the cross-bridge `Adj a₁ b₂ ∨ Adj a₂ b₁`.

    Argument: `hsq := hH.2 e₁ e₂ hne : lineGraphSqAdj G e₁ e₂` unfolds
    to either direct line-graph adjacency (impossible without shared
    vertex) or a bridging third edge `e₃` whose endpoints touch both `e₁`
    and `e₂`. By bipartiteness + same-side non-adjacency, the bridge
    must run between `{a₁, b₁}` and `{a₂, b₂}` cross-side. -/
private lemma bridge_dichotomy_of_antimatching''
    {G : Flag emptyType} {S : Finset (Fin G.size)}
    (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    {H : Finset (Fin G.size × Fin G.size)} (hH : IsAntimatching G H)
    {e₁ e₂ : Fin G.size × Fin G.size}
    (he₁ : e₁ ∈ H) (he₂ : e₂ ∈ H) (hne : e₁ ≠ e₂)
    (ha : sEndpoint S e₁ ≠ sEndpoint S e₂)
    (hb : scEndpoint S e₁ ≠ scEndpoint S e₂)
    (haa : sEndpoint S e₁ ≠ scEndpoint S e₂)
    (hbb : scEndpoint S e₁ ≠ sEndpoint S e₂) :
    G.graph.Adj (sEndpoint S e₁) (scEndpoint S e₂) ∨
    G.graph.Adj (sEndpoint S e₂) (scEndpoint S e₁) := by
  set a₁ := sEndpoint S e₁ with ha₁_def
  set b₁ := scEndpoint S e₁ with hb₁_def
  set a₂ := sEndpoint S e₂ with ha₂_def
  set b₂ := scEndpoint S e₂ with hb₂_def
  have ha₁_in : a₁ ∈ S := sEndpoint_mem hS hH he₁
  have ha₂_in : a₂ ∈ S := sEndpoint_mem hS hH he₂
  have hb₁_out : b₁ ∉ S := scEndpoint_notMem hS hH he₁
  have hb₂_out : b₂ ∉ S := scEndpoint_notMem hS hH he₂
  have hadj₁ : G.graph.Adj a₁ b₁ := adj_sEndpoint_scEndpoint hH he₁
  have hadj₂ : G.graph.Adj a₂ b₂ := adj_sEndpoint_scEndpoint hH he₂
  have hsq : lineGraphSqAdj G e₁ e₂ := hH.2 e₁ he₁ e₂ he₂ hne
  obtain ⟨_, _, _, _, hconn⟩ := hsq
  -- Extract bridge: each endpoint of the bridge edge is in {e₁.1, e₁.2}
  -- and {e₂.1, e₂.2} respectively. Both sets equal {a_i, b_i}.
  have h_e₁_eq : ∀ x, x = e₁.1 ∨ x = e₁.2 ↔ x = a₁ ∨ x = b₁ := by
    intro x
    change _ ↔ x = sEndpoint S e₁ ∨ x = scEndpoint S e₁
    unfold sEndpoint scEndpoint
    by_cases h1 : e₁.1 ∈ S
    · simp only [if_pos h1]
    · simp only [if_neg h1]; tauto
  have h_e₂_eq : ∀ x, x = e₂.1 ∨ x = e₂.2 ↔ x = a₂ ∨ x = b₂ := by
    intro x
    change _ ↔ x = sEndpoint S e₂ ∨ x = scEndpoint S e₂
    unfold sEndpoint scEndpoint
    by_cases h1 : e₂.1 ∈ S
    · simp only [if_pos h1]
    · simp only [if_neg h1]; tauto
  -- Repackage hconn into ∃ p q...
  have hexists : ∃ p q : Fin G.size, G.graph.Adj p q ∧
      (p = a₁ ∨ p = b₁ ∨ q = a₁ ∨ q = b₁) ∧
      (p = a₂ ∨ p = b₂ ∨ q = a₂ ∨ q = b₂) := by
    have hadj_e₁ : G.graph.Adj e₁.1 e₁.2 := (hH.1 e₁ he₁).1
    rcases hconn with hLG | ⟨e₃, he₃adj, h13, h32⟩
    · obtain ⟨_, _, _, hshare⟩ := hLG
      refine ⟨e₁.1, e₁.2, hadj_e₁, ?_, ?_⟩
      · rcases (h_e₁_eq e₁.1).mp (Or.inl rfl) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases hshare with h | h | h | h
        · rcases (h_e₂_eq e₁.1).mp (Or.inl h) with hh | hh
          · exact Or.inl hh
          · exact Or.inr (Or.inl hh)
        · rcases (h_e₂_eq e₁.1).mp (Or.inr h) with hh | hh
          · exact Or.inl hh
          · exact Or.inr (Or.inl hh)
        · rcases (h_e₂_eq e₁.2).mp (Or.inl h) with hh | hh
          · exact Or.inr (Or.inr (Or.inl hh))
          · exact Or.inr (Or.inr (Or.inr hh))
        · rcases (h_e₂_eq e₁.2).mp (Or.inr h) with hh | hh
          · exact Or.inr (Or.inr (Or.inl hh))
          · exact Or.inr (Or.inr (Or.inr hh))
    · obtain ⟨_, _, _, hs13⟩ := h13
      obtain ⟨_, _, _, hs32⟩ := h32
      refine ⟨e₃.1, e₃.2, he₃adj, ?_, ?_⟩
      · rcases hs13 with h | h | h | h
        · rcases (h_e₁_eq e₃.1).mp (Or.inl h.symm) with hh | hh
          · exact Or.inl hh
          · exact Or.inr (Or.inl hh)
        · rcases (h_e₁_eq e₃.2).mp (Or.inl h.symm) with hh | hh
          · exact Or.inr (Or.inr (Or.inl hh))
          · exact Or.inr (Or.inr (Or.inr hh))
        · rcases (h_e₁_eq e₃.1).mp (Or.inr h.symm) with hh | hh
          · exact Or.inl hh
          · exact Or.inr (Or.inl hh)
        · rcases (h_e₁_eq e₃.2).mp (Or.inr h.symm) with hh | hh
          · exact Or.inr (Or.inr (Or.inl hh))
          · exact Or.inr (Or.inr (Or.inr hh))
      · rcases hs32 with h | h | h | h
        · rcases (h_e₂_eq e₃.1).mp (Or.inl h) with hh | hh
          · exact Or.inl hh
          · exact Or.inr (Or.inl hh)
        · rcases (h_e₂_eq e₃.1).mp (Or.inr h) with hh | hh
          · exact Or.inl hh
          · exact Or.inr (Or.inl hh)
        · rcases (h_e₂_eq e₃.2).mp (Or.inl h) with hh | hh
          · exact Or.inr (Or.inr (Or.inl hh))
          · exact Or.inr (Or.inr (Or.inr hh))
        · rcases (h_e₂_eq e₃.2).mp (Or.inr h) with hh | hh
          · exact Or.inr (Or.inr (Or.inl hh))
          · exact Or.inr (Or.inr (Or.inr hh))
  obtain ⟨p, q, hpq_adj, hp1, hq2⟩ := hexists
  have hNoAdj_a1a2 : ¬ G.graph.Adj a₁ a₂ := fun h => ((hS _ _ h).mp ha₁_in) ha₂_in
  have hNoAdj_b1b2 : ¬ G.graph.Adj b₁ b₂ := fun h => hb₁_out ((hS _ _ h).mpr hb₂_out)
  rcases hp1 with hp | hp | hp | hp
  · rw [hp] at hpq_adj
    rcases hq2 with hq | hq | hq | hq
    · exact absurd (hp.symm.trans hq) ha
    · exact absurd (hp.symm.trans hq) haa
    · rw [hq] at hpq_adj; exact absurd hpq_adj hNoAdj_a1a2
    · rw [hq] at hpq_adj; exact Or.inl hpq_adj
  · rw [hp] at hpq_adj
    rcases hq2 with hq | hq | hq | hq
    · exact absurd (hp.symm.trans hq) hbb
    · exact absurd (hp.symm.trans hq) hb
    · rw [hq] at hpq_adj; exact Or.inr (G.graph.symm hpq_adj)
    · rw [hq] at hpq_adj; exact absurd hpq_adj hNoAdj_b1b2
  · rw [hp] at hpq_adj
    rcases hq2 with hq | hq | hq | hq
    · rw [hq] at hpq_adj; exact absurd (G.graph.symm hpq_adj) hNoAdj_a1a2
    · rw [hq] at hpq_adj; exact Or.inl (G.graph.symm hpq_adj)
    · exact absurd (hp.symm.trans hq) ha
    · exact absurd (hp.symm.trans hq) haa
  · rw [hp] at hpq_adj
    rcases hq2 with hq | hq | hq | hq
    · rw [hq] at hpq_adj; exact Or.inr hpq_adj
    · rw [hq] at hpq_adj; exact absurd (G.graph.symm hpq_adj) hNoAdj_b1b2
    · exact absurd (hp.symm.trans hq) hbb
    · exact absurd (hp.symm.trans hq) hb

/-- For `b ∈ Sᶜ`, `hDegree H b ≤ maxDegreeOn G Sᶜ`.
    Symmetric version of `hDegree_le_maxDegreeOn`. -/
private lemma hDegree_le_maxDegreeOn_Sc {G : Flag emptyType}
    (S : Finset (Fin G.size))
    {H : Finset (Fin G.size × Fin G.size)} (hH : IsAntimatching G H)
    {v : Fin G.size} (hv : v ∈ (Sᶜ : Finset _)) :
    hDegree H v ≤ maxDegreeOn G Sᶜ :=
  (hDegree_le_degree hH v).trans (degree_le_maxDegreeOn G Sᶜ hv)

/-! ## §2.8 super-vertex argument helpers

These lemmas factor out the Phase B★ partition steps. -/

/-- Per-vertex hDegree sum bound on a subset of `Sᶜ`, using a fixed
    upper bound `s` per vertex (rather than the global `maxDegreeOn G Sᶜ`).
    Used in §2.8 with `s = hDegree H ys`. -/
private lemma sum_hDegree_le_card_mul_const {G : Flag emptyType}
    {T : Finset (Fin G.size)}
    {H : Finset (Fin G.size × Fin G.size)} (s : ℕ)
    (hbound : ∀ v ∈ T, hDegree H v ≤ s) :
    T.sum (fun v => hDegree H v) ≤ T.card * s := by
  calc T.sum (fun v => hDegree H v)
      ≤ T.sum (fun _ => s) := Finset.sum_le_sum hbound
    _ = T.card * s := by simp [Finset.sum_const, mul_comm]

/-- The unordered-pair structure of a canonical H-edge: for any edge `e ∈ H`,
    `(e.1, e.2)` is either `(sEndpoint S e, scEndpoint S e)` or
    `(scEndpoint S e, sEndpoint S e)`. -/
private lemma H_edge_pair_form
    {G : Flag emptyType} (S : Finset (Fin G.size))
    (e : Fin G.size × Fin G.size) :
    (e.1 = sEndpoint S e ∧ e.2 = scEndpoint S e) ∨
    (e.1 = scEndpoint S e ∧ e.2 = sEndpoint S e) := by
  by_cases h : e.1 ∈ S
  · exact Or.inl ⟨by simp [sEndpoint, h], by simp [scEndpoint, h]⟩
  · exact Or.inr ⟨by simp [scEndpoint, h], by simp [sEndpoint, h]⟩

/-- **Two H-edges with equal endpoints are equal.** The unordered pair
    `{sEndpoint, scEndpoint}` determines `e` since `sEndpoint ∈ S`,
    `scEndpoint ∉ S`, and `e.1 < e.2` pins the order. -/
private lemma H_edge_determined_by_endpoints
    {G : Flag emptyType} {S : Finset (Fin G.size)}
    (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    {H : Finset (Fin G.size × Fin G.size)} (hH : IsAntimatching G H)
    {e₁ e₂ : Fin G.size × Fin G.size}
    (he₁ : e₁ ∈ H) (he₂ : e₂ ∈ H)
    (hsep : sEndpoint S e₁ = sEndpoint S e₂)
    (hscep : scEndpoint S e₁ = scEndpoint S e₂) : e₁ = e₂ := by
  have hlt₁ : e₁.1 < e₁.2 := (hH.1 e₁ he₁).2
  have hlt₂ : e₂.1 < e₂.2 := (hH.1 e₂ he₂).2
  have h_pair₁ := H_edge_pair_form S e₁
  have h_pair₂ := H_edge_pair_form S e₂
  rw [hsep, hscep] at h_pair₁
  -- After rewriting, sEndpoint S e₁ becomes sEndpoint S e₂ (and similarly scEndpoint).
  have h_sep_ne_sc : sEndpoint S e₂ ≠ scEndpoint S e₂ := fun heq =>
    (scEndpoint_notMem hS hH he₂) (heq ▸ sEndpoint_mem hS hH he₂)
  rcases h_pair₁ with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
    rcases h_pair₂ with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
  · exact Prod.ext (h1a.trans h2a.symm) (h1b.trans h2b.symm)
  · exfalso
    have h1 : sEndpoint S e₂ < scEndpoint S e₂ := by rw [← h1a, ← h1b]; exact hlt₁
    have h2 : scEndpoint S e₂ < sEndpoint S e₂ := by rw [← h2a, ← h2b]; exact hlt₂
    exact absurd h2 (not_lt.mpr (le_of_lt h1))
  · exfalso
    have h1 : scEndpoint S e₂ < sEndpoint S e₂ := by rw [← h1a, ← h1b]; exact hlt₁
    have h2 : sEndpoint S e₂ < scEndpoint S e₂ := by rw [← h2a, ← h2b]; exact hlt₂
    exact absurd h2 (not_lt.mpr (le_of_lt h1))
  · exact Prod.ext (h1a.trans h2a.symm) (h1b.trans h2b.symm)

/-- For two H-edges with `scEndpoint = ys` and equal `sEndpoint`, the edges
    are equal. (Used to prove that the sEndpoint-image of `H`-edges at `ys`
    has the same cardinality as those edges.) Specialisation of
    `H_edge_determined_by_endpoints`. -/
private lemma H_edge_determined_by_sEndpoint_at_ys
    {G : Flag emptyType} {S : Finset (Fin G.size)}
    (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    {H : Finset (Fin G.size × Fin G.size)} (hH : IsAntimatching G H)
    {ys : Fin G.size} (_hys_notin : ys ∉ S)
    {e₁ e₂ : Fin G.size × Fin G.size}
    (he₁ : e₁ ∈ H) (he₂ : e₂ ∈ H)
    (hys₁ : scEndpoint S e₁ = ys) (hys₂ : scEndpoint S e₂ = ys)
    (hsep_eq : sEndpoint S e₁ = sEndpoint S e₂) : e₁ = e₂ :=
  H_edge_determined_by_endpoints hS hH he₁ he₂ hsep_eq (hys₁.trans hys₂.symm)

/-! ## Main combinatorial lemma: antimatching size bound

This is the §2.8 statement, separated as a standalone lemma. -/

/-- **Antimatching bound** (simplified §2.8 of
    the development notes):
    Every antimatching `H` of a bipartite graph `G` satisfies
    `|H| ≤ Δ_A · Δ_B`.

    Pick `z* ∈ Sᶜ` with maximum H-degree `s` on the `Sᶜ` side, set
    `X' := N_G(z*) ∩ S` (so `|X'| ≤ Δ_B`) and `S_super := {b ∈ Sᶜ :
    N_G(b) ∩ S ⊇ N_H(z*)}` (so `z* ∈ S_super, |S_super| ≤ Δ_A`).

    2-class partition by `scEndpoint` membership in `S_super`:
    - `F_super := {e : scEnd ∈ S_super}`, bounded `|S_super|·s`
      (each `b ∈ S_super ⊆ Sᶜ` has `hDegree H b ≤ s` by pivot maximality).
    - `F_outside := {e : scEnd ∉ S_super}`, split by `sEnd ∈ N_H(z*) ∩ S`
      vs `X' \ N_H(z*)` via the super-vertex implication
      (`scEnd ∉ S_super ⟹ sEnd ∈ X'` by bridge dichotomy).

    Cancellation: `|S_super|·s + s·(Δ_A - |S_super|) = s·Δ_A`,
    so `|H| ≤ s·Δ_A + (Δ_B - s)·(Δ_A - 1) ≤ Δ_A · Δ_B`. -/
theorem antimatching_card_le_mul
    (G : Flag emptyType) (S : Finset (Fin G.size))
    (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (H : Finset (Fin G.size × Fin G.size))
    (hH : IsAntimatching G H) :
    H.card ≤ maxDegreeOn G S * maxDegreeOn G Sᶜ := by
  -- §2.8 simplified proof (drops the `x*` pivot vertex entirely):
  -- pick `ys ∈ Sᶜ` maximising H-degree; `s := hDegree H ys`. Then partition
  -- H by scEndpoint into two classes (b ∈ S_super; b ∉ S_super), with the
  -- second class sub-split by whether sEndpoint ∈ N_H_ys_S.
  -- (1) Trivial case: H is empty.
  by_cases hHempty : H.card = 0
  · rw [hHempty]; exact Nat.zero_le _
  -- (2) Otherwise pick max-H-degree pivot ys on Sᶜ side.
  have hH_pos : 0 < H.card := Nat.pos_of_ne_zero hHempty
  obtain ⟨e_seed, he_seed_mem⟩ := Finset.card_pos.mp hH_pos
  have hys_seed_in_Sc : scEndpoint S e_seed ∈ (Sᶜ : Finset _) :=
    Finset.mem_compl.mpr (scEndpoint_notMem hS hH he_seed_mem)
  have hSc_nonempty : (Sᶜ : Finset _).Nonempty := ⟨_, hys_seed_in_Sc⟩
  -- Pick ys ∈ Sᶜ maximising hDegree H ys.
  obtain ⟨ys, hys_in_Sc, hys_max⟩ :=
    Finset.exists_max_image (Sᶜ : Finset _) (fun v => hDegree H v) hSc_nonempty
  have hys_notin : ys ∉ S := by
    rw [← Finset.mem_compl]; exact hys_in_Sc
  -- Set s := hDegree H ys ; bound s ≤ maxDegreeOn G Sᶜ.
  set s : ℕ := hDegree H ys
  have hs_max : ∀ v ∈ (Sᶜ : Finset _), hDegree H v ≤ s := hys_max
  have hs_le_Δ_B : s ≤ maxDegreeOn G Sᶜ := hDegree_le_maxDegreeOn_Sc S hH hys_in_Sc
  -- s > 0 (from the seed edge: scEndpoint S e_seed ∈ Sᶜ has hDegree ≥ 1 ≤ s).
  have hs_pos : 0 < s := by
    have hseed : 0 < hDegree H (scEndpoint S e_seed) := by
      refine Finset.card_pos.mpr ⟨e_seed, Finset.mem_filter.mpr ⟨he_seed_mem, ?_⟩⟩
      show e_seed.1 = scEndpoint S e_seed ∨ e_seed.2 = scEndpoint S e_seed
      unfold scEndpoint; by_cases h1 : e_seed.1 ∈ S
      · simp only [if_pos h1]; tauto
      · simp only [if_neg h1]; tauto
    have := hs_max _ hys_seed_in_Sc; omega
  -- (3) Define X' := S ∩ N_G(ys); set Δ_A, Δ_B.
  set Xp : Finset (Fin G.size) :=
    S.filter (fun v => G.graph.Adj v ys) with hXp_def
  set Δ_A : ℕ := maxDegreeOn G S
  set Δ_B : ℕ := maxDegreeOn G Sᶜ
  have hXp_card_le : Xp.card ≤ Δ_B := by
    have hsub : Xp ⊆ Finset.univ.filter (fun u => G.graph.Adj ys u) := fun v hv => by
      rw [Finset.mem_filter] at hv ⊢
      exact ⟨Finset.mem_univ v, G.graph.symm hv.2⟩
    exact (Finset.card_le_card hsub).trans (degree_le_maxDegreeOn G Sᶜ hys_in_Sc)
  -- (4) §2.8 set-up: N_H_ys = H-edges incident to ys; N_H_ys_S = their S-endpoints;
  -- S_super = b ∈ Sᶜ with N_H_ys_S ⊆ N_G(b).
  set N_H_ys : Finset (Fin G.size × Fin G.size) :=
    H.filter (fun e => e.1 = ys ∨ e.2 = ys) with hN_H_ys_def
  set N_H_ys_S : Finset (Fin G.size) := N_H_ys.image (sEndpoint S) with hN_H_ys_S_def
  set S_super : Finset (Fin G.size) :=
    (Sᶜ : Finset _).filter (fun b => ∀ a ∈ N_H_ys_S, G.graph.Adj a b)
    with hS_super_def
  -- Every a ∈ N_H_ys_S has a ∈ S and G.Adj a ys.
  have hN_H_ys_S_prop : ∀ a ∈ N_H_ys_S, a ∈ S ∧ G.graph.Adj a ys := by
    intro a ha
    rw [hN_H_ys_S_def, Finset.mem_image] at ha
    obtain ⟨e, he_in_N, he_sep⟩ := ha
    rw [hN_H_ys_def, Finset.mem_filter] at he_in_N
    obtain ⟨he_in_H, he_inc⟩ := he_in_N
    have ha_in_S : sEndpoint S e ∈ S := sEndpoint_mem hS hH he_in_H
    rw [he_sep] at ha_in_S
    refine ⟨ha_in_S, ?_⟩
    rw [← he_sep, (scEndpoint_eq_of_incident hS hH hys_notin he_in_H he_inc).symm]
    exact adj_sEndpoint_scEndpoint hH he_in_H
  -- N_H_ys is nonempty (since s = N_H_ys.card > 0).
  obtain ⟨e₀_seed, he₀_seed_mem⟩ : N_H_ys.Nonempty := by
    rw [hN_H_ys_def]; exact Finset.card_pos.mp hs_pos
  have hN_H_ys_S_nonempty : N_H_ys_S.Nonempty := by
    refine ⟨sEndpoint S e₀_seed, ?_⟩
    rw [hN_H_ys_S_def, Finset.mem_image]; exact ⟨e₀_seed, he₀_seed_mem, rfl⟩
  have hys_in_S_super : ys ∈ S_super := by
    rw [hS_super_def, Finset.mem_filter]
    exact ⟨hys_in_Sc, fun a ha => (hN_H_ys_S_prop a ha).2⟩
  have hS_super_pos : 1 ≤ S_super.card := Finset.card_pos.mpr ⟨ys, hys_in_S_super⟩
  have hS_super_le_Δ_A : S_super.card ≤ Δ_A := by
    obtain ⟨a, ha_in⟩ := hN_H_ys_S_nonempty
    have ha_in_S : a ∈ S := (hN_H_ys_S_prop a ha_in).1
    have hsub : S_super ⊆ Finset.univ.filter (fun u => G.graph.Adj a u) := fun b hb => by
      rw [hS_super_def, Finset.mem_filter] at hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb.2 a ha_in⟩
    exact (Finset.card_le_card hsub).trans (degree_le_maxDegreeOn G S ha_in_S)
  -- Lemma 2.8.1 (per-super-vertex degree sum, 2-class form):
  --   Σ_{b ∈ S_super} hDegree H b ≤ |S_super| · s.
  -- Each b ∈ S_super lies in Sᶜ, so the pivot's maximality (hs_max) gives
  -- hDegree H b ≤ s. Apply the existing helper `sum_hDegree_le_card_mul_const`.
  have h_lemma_2_8_1 :
      S_super.sum (fun b => hDegree H b) ≤ S_super.card * s := by
    apply sum_hDegree_le_card_mul_const s
    intro b hb
    -- b ∈ S_super ⇒ b ∈ Sᶜ ⇒ hDegree H b ≤ s.
    have hb_in_Sc : b ∈ (Sᶜ : Finset _) := by
      rw [hS_super_def, Finset.mem_filter] at hb
      exact hb.1
    exact hs_max b hb_in_Sc
  -- Lemma 2.8.2 (extra-G-neighbour bound):
  --   |{e ∈ H : sEndpoint e ∈ N_H_ys_S, scEndpoint e ∈ Sᶜ \ S_super}|
  --     ≤ |N_H_ys_S| · (Δ_A - |S_super|).
  -- Proof: fiber-decompose by sEndpoint. For each a ∈ N_H_ys_S:
  --   (a) The map e ↦ scEndpoint S e injects the a-fiber into N_G(a) ∩ (Sᶜ \ S_super).
  --   (b) S_super ⊆ N_G(a) (by definition of S_super) and N_G(a) ∩ Sᶜ ⊆ N_G(a)
  --       has cardinality ≤ Δ_A.
  --   (c) So |N_G(a) ∩ (Sᶜ \ S_super)| ≤ Δ_A - |S_super|.
  have h_lemma_2_8_2 :
      (H.filter (fun e =>
        sEndpoint S e ∈ N_H_ys_S ∧
        scEndpoint S e ∈ (Sᶜ : Finset _) \ S_super)).card ≤
      N_H_ys_S.card * (Δ_A - S_super.card) := by
    -- Set the filter set explicitly.
    set F : Finset (Fin G.size × Fin G.size) :=
      H.filter (fun e =>
        sEndpoint S e ∈ N_H_ys_S ∧
        scEndpoint S e ∈ (Sᶜ : Finset _) \ S_super)
      with hF_def
    -- Fiber-decompose by sEndpoint, valued in N_H_ys_S.
    have h_card_eq :
        F.card = N_H_ys_S.sum (fun a =>
          (F.filter (fun e => sEndpoint S e = a)).card) := by
      rw [← Finset.card_attach (s := F)]
      rw [Finset.card_eq_sum_card_fiberwise (f := fun e => sEndpoint S e.val)
        (s := F.attach) (t := N_H_ys_S)
        (fun e _ => by exact (Finset.mem_filter.mp e.property).2.1)]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.card_bij (fun e _ => e.val) ?_ (fun _ _ _ _ heq => Subtype.ext heq) ?_
      · intro e he
        rw [Finset.mem_filter] at he ⊢
        exact ⟨e.property, he.2⟩
      · intro b hb
        rw [Finset.mem_filter] at hb
        refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
        rw [Finset.mem_filter]; exact ⟨Finset.mem_attach _ _, hb.2⟩
    -- Per-fiber bound: for each a ∈ N_H_ys_S,
    --   (F.filter (sEndpoint = a)).card ≤ Δ_A - S_super.card.
    have h_fiber_bound : ∀ a ∈ N_H_ys_S,
        (F.filter (fun e => sEndpoint S e = a)).card ≤ Δ_A - S_super.card := by
      intro a ha
      -- a ∈ S and Adj a ys (from hN_H_ys_S_prop).
      have ha_prop := hN_H_ys_S_prop a ha
      have ha_in_S : a ∈ S := ha_prop.1
      -- The fiber maps via scEndpoint into N_G(a) ∩ (Sᶜ \ S_super).
      -- Define the target finset.
      set NGa_outside : Finset (Fin G.size) :=
        (Finset.univ.filter (fun u => G.graph.Adj a u)) \ S_super
        with hNGa_outside_def
      -- Injection F_a → NGa_outside via scEndpoint.
      have h_inj_card :
          (F.filter (fun e => sEndpoint S e = a)).card ≤ NGa_outside.card := by
        refine Finset.card_le_card_of_injOn (fun e => scEndpoint S e) ?_ ?_
        · intro e he
          rw [Finset.mem_coe, Finset.mem_filter] at he
          obtain ⟨he_F, hsep_eq⟩ := he
          rw [hF_def, Finset.mem_filter] at he_F
          obtain ⟨he_H, _ha_in_N, hb_in_Sc_diff⟩ := he_F
          -- scEndpoint S e ∈ Sᶜ \ S_super.
          -- Need: scEndpoint S e ∈ N_G(a) ∩ Sᶜ \ S_super, i.e. Adj a (scEndpoint S e)
          --      and ¬ scEndpoint S e ∈ S_super.
          have hadj_a_sc : G.graph.Adj a (scEndpoint S e) := by
            rw [← hsep_eq]
            exact adj_sEndpoint_scEndpoint hH he_H
          -- Goal: (fun e ↦ scEndpoint S e) e ∈ ↑NGa_outside (Set coercion).
          rw [Finset.mem_coe]
          rw [hNGa_outside_def, Finset.mem_sdiff, Finset.mem_filter]
          refine ⟨⟨Finset.mem_univ _, hadj_a_sc⟩, ?_⟩
          -- ¬ scEndpoint S e ∈ S_super because scEndpoint S e ∈ Sᶜ \ S_super.
          rw [Finset.mem_sdiff] at hb_in_Sc_diff
          exact hb_in_Sc_diff.2
        · -- Injection: edges with same sEndpoint = a and same scEndpoint are equal.
          intro e₁ he₁ e₂ he₂ heq
          rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
          obtain ⟨he₁_F, hsep₁⟩ := he₁
          obtain ⟨he₂_F, hsep₂⟩ := he₂
          rw [hF_def, Finset.mem_filter] at he₁_F he₂_F
          exact H_edge_determined_by_endpoints hS hH he₁_F.1 he₂_F.1
            (hsep₁.trans hsep₂.symm) heq
      -- Now bound |NGa_outside| ≤ Δ_A - |S_super|.
      -- S_super ⊆ N_G(a) ∩ Sᶜ ⊆ N_G(a). So |NGa_outside| = |N_G(a)| - |N_G(a) ∩ S_super|
      -- ≤ Δ_A - |S_super| since S_super ⊆ N_G(a).
      have h_Ssuper_sub : S_super ⊆ Finset.univ.filter (fun u => G.graph.Adj a u) := by
        intro b hb
        rw [hS_super_def, Finset.mem_filter] at hb
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hb.2 a ha⟩
      have hNGa_card_le_ΔA :
          (Finset.univ.filter (fun u => G.graph.Adj a u)).card ≤ Δ_A :=
        degree_le_maxDegreeOn G S ha_in_S
      have hNGa_outside_card :
          NGa_outside.card =
            (Finset.univ.filter (fun u => G.graph.Adj a u)).card - S_super.card := by
        rw [hNGa_outside_def]
        rw [Finset.card_sdiff_of_subset h_Ssuper_sub]
      calc (F.filter (fun e => sEndpoint S e = a)).card
          ≤ NGa_outside.card := h_inj_card
        _ = (Finset.univ.filter (fun u => G.graph.Adj a u)).card - S_super.card :=
            hNGa_outside_card
        _ ≤ Δ_A - S_super.card := Nat.sub_le_sub_right hNGa_card_le_ΔA _
    -- Aggregate the fiber bounds.
    calc F.card
        = N_H_ys_S.sum (fun a =>
            (F.filter (fun e => sEndpoint S e = a)).card) := h_card_eq
      _ ≤ N_H_ys_S.sum (fun _ => Δ_A - S_super.card) := by
          apply Finset.sum_le_sum
          intro a ha
          exact h_fiber_bound a ha
      _ = N_H_ys_S.card * (Δ_A - S_super.card) := by
          simp [Finset.sum_const]
  -- §2.8 closure: combine A + L1_set + L2_set + C_outside.
  -- Phase 1: prove |N_H_ys_S| = s.
  -- The sEndpoint map injects N_H_ys into N_H_ys_S (and surjects by image).
  have hN_H_ys_S_card : N_H_ys_S.card = s := by
    have hs_eq : s = N_H_ys.card := rfl
    rw [hs_eq, hN_H_ys_S_def]
    refine Finset.card_image_of_injOn fun e₁ he₁ e₂ he₂ heq => ?_
    rw [Finset.mem_coe, hN_H_ys_def, Finset.mem_filter] at he₁ he₂
    exact H_edge_determined_by_sEndpoint_at_ys hS hH hys_notin he₁.1 he₂.1
      (scEndpoint_eq_of_incident hS hH hys_notin he₁.1 he₁.2)
      (scEndpoint_eq_of_incident hS hH hys_notin he₂.1 he₂.2) heq
  -- Phase 2: super-vertex implication.
  -- For every e ∈ H with scEnd ∉ S_super, sEnd ∈ Xp (Key Lemma).
  have h_super_vertex_implication : ∀ e ∈ H,
      scEndpoint S e ∈ (Sᶜ : Finset _) \ S_super →
      sEndpoint S e ∈ Xp := by
    intro e he hb_out
    rw [Finset.mem_sdiff] at hb_out
    obtain ⟨hb_in_Sc, hb_notin_super⟩ := hb_out
    -- Since scEnd e ∉ S_super, ∃ a* ∈ N_H_ys_S with ¬ Adj a* (scEnd e).
    obtain ⟨a_star, ha_star_in_N, ha_star_not_adj⟩ :
        ∃ aS ∈ N_H_ys_S, ¬ G.graph.Adj aS (scEndpoint S e) := by
      by_contra h_all
      push_neg at h_all
      exact hb_notin_super (by rw [hS_super_def, Finset.mem_filter]; exact ⟨hb_in_Sc, h_all⟩)
    -- Pick ep* ∈ N_H_ys with sEnd ep* = a_star (image preimage).
    obtain ⟨ep_star, hep_star_in_N, hep_star_sep⟩ :
        ∃ ep_star ∈ N_H_ys, sEndpoint S ep_star = a_star := by
      have : a_star ∈ N_H_ys.image (sEndpoint S) := by
        rw [← hN_H_ys_S_def]; exact ha_star_in_N
      exact Finset.mem_image.mp this
    have hep_star_mem := Finset.mem_filter.mp (hN_H_ys_def ▸ hep_star_in_N)
    have hep_star_H : ep_star ∈ H := hep_star_mem.1
    have hep_star_inc : ep_star.1 = ys ∨ ep_star.2 = ys := hep_star_mem.2
    have hep_star_scep : scEndpoint S ep_star = ys :=
      scEndpoint_eq_of_incident hS hH hys_notin hep_star_H hep_star_inc
    have ha_e_in_S : sEndpoint S e ∈ S := sEndpoint_mem hS hH he
    have hb_e_notin_S : scEndpoint S e ∉ S := scEndpoint_notMem hS hH he
    have h_sep_ne_a : sEndpoint S e ≠ a_star := fun hsep_eq =>
      ha_star_not_adj (hsep_eq ▸ adj_sEndpoint_scEndpoint hH he)
    have hne : ep_star ≠ e := fun hep_eq =>
      ha_star_not_adj (by rw [← hep_star_sep, hep_eq]; exact adj_sEndpoint_scEndpoint hH he)
    have h_scep_ne_ys : scEndpoint S e ≠ ys := fun h =>
      hb_notin_super (h ▸ hys_in_S_super)
    have h_sep_ne_ys : sEndpoint S e ≠ ys := fun h => hys_notin (h ▸ ha_e_in_S)
    have h_scep_ne_a : scEndpoint S e ≠ a_star := fun h =>
      hb_e_notin_S (h ▸ (hN_H_ys_S_prop a_star ha_star_in_N).1)
    -- Apply bridge_dichotomy_of_antimatching'' directly with e₁ := ep_star, e₂ := e.
    -- Hypothesis form: ha: sEnd e₁ ≠ sEnd e₂; hb: scEnd e₁ ≠ scEnd e₂;
    --                  haa: sEnd e₁ ≠ scEnd e₂; hbb: scEnd e₁ ≠ sEnd e₂.
    -- (Symmetric to the side-conditions; no `Ne.symm` wrapper needed.)
    have h_dich := bridge_dichotomy_of_antimatching'' hS hH hep_star_H he hne
      (by rw [hep_star_sep]; exact (Ne.symm h_sep_ne_a))
      (by rw [hep_star_scep]; exact (Ne.symm h_scep_ne_ys))
      (by rw [hep_star_sep]; exact (Ne.symm h_scep_ne_a))
      (by rw [hep_star_scep]; exact (Ne.symm h_sep_ne_ys))
    rw [hep_star_sep, hep_star_scep] at h_dich
    rcases h_dich with h_adj_a_scep | h_adj_sep_ys
    · exact absurd h_adj_a_scep ha_star_not_adj
    · rw [hXp_def, Finset.mem_filter]
      exact ⟨ha_e_in_S, h_adj_sep_ys⟩
  -- Phase 3 (σ2.8-G): Partition |H| by scEndpoint into super, outside (2-class), and combine.
  -- Define the two disjoint subsets of H:
  set F_super : Finset (Fin G.size × Fin G.size) :=
    H.filter (fun e => scEndpoint S e ∈ S_super) with hF_super_def
  set F_outside : Finset (Fin G.size × Fin G.size) :=
    H.filter (fun e => scEndpoint S e ∈ (Sᶜ : Finset _) \ S_super) with hF_outside_def
  -- |F_super| ≤ S_super.card * s via Lemma 2.8.1 (now over the whole S_super).
  have hF_super_card_eq :
      F_super.card = S_super.sum (fun b => hDegree H b) := by
    rw [hF_super_def, ← Finset.card_attach (s := H.filter (fun e => scEndpoint S e ∈ S_super))]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun e => scEndpoint S e.val)
      (s := (H.filter (fun e => scEndpoint S e ∈ S_super)).attach) (t := S_super)
      (fun e _ => by exact (Finset.mem_filter.mp e.property).2)]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb_notin : b ∉ S :=
      Finset.mem_compl.mp ((Finset.mem_filter.mp (hS_super_def ▸ hb)).1)
    unfold hDegree
    refine Finset.card_bij (fun e _ => e.val) ?_ (fun _ _ _ _ heq => Subtype.ext heq) ?_
    · intro e he
      rw [Finset.mem_filter] at he ⊢
      refine ⟨(Finset.mem_filter.mp e.property).1, ?_⟩
      have hscep_eq : scEndpoint S e.val = b := he.2
      unfold scEndpoint at hscep_eq
      by_cases h1 : e.val.1 ∈ S
      · simp only [if_pos h1] at hscep_eq; exact Or.inr hscep_eq
      · simp only [if_neg h1] at hscep_eq; exact Or.inl hscep_eq
    · intro a ha
      rw [Finset.mem_filter] at ha
      have h_scep_eq : scEndpoint S a = b :=
        scEndpoint_eq_of_incident hS hH hb_notin ha.1 ha.2
      refine ⟨⟨a, Finset.mem_filter.mpr ⟨ha.1, h_scep_eq ▸ hb⟩⟩, ?_, rfl⟩
      rw [Finset.mem_filter]; exact ⟨Finset.mem_attach _ _, h_scep_eq⟩
  -- |F_outside| bound. Split by sEndpoint ∈ N_H_ys_S vs ∉.
  set F_outside_B : Finset (Fin G.size × Fin G.size) :=
    H.filter (fun e =>
      sEndpoint S e ∈ N_H_ys_S ∧ scEndpoint S e ∈ (Sᶜ : Finset _) \ S_super)
    with hF_outside_B_def
  set F_outside_C : Finset (Fin G.size × Fin G.size) :=
    H.filter (fun e =>
      sEndpoint S e ∈ Xp \ N_H_ys_S ∧ scEndpoint S e ∈ (Sᶜ : Finset _) \ S_super)
    with hF_outside_C_def
  -- F_outside ⊆ F_outside_B ∪ F_outside_C (since sEnd ∈ Xp by super-vertex implication).
  have hF_outside_subset : F_outside ⊆ F_outside_B ∪ F_outside_C := by
    intro e he
    rw [hF_outside_def, Finset.mem_filter] at he
    obtain ⟨he_H, hb_out⟩ := he
    have hsep_in_Xp : sEndpoint S e ∈ Xp := h_super_vertex_implication e he_H hb_out
    rw [Finset.mem_union]
    by_cases h_sep_in_N : sEndpoint S e ∈ N_H_ys_S
    · left
      rw [hF_outside_B_def, Finset.mem_filter]
      exact ⟨he_H, h_sep_in_N, hb_out⟩
    · right
      rw [hF_outside_C_def, Finset.mem_filter]
      refine ⟨he_H, ?_, hb_out⟩
      rw [Finset.mem_sdiff]
      exact ⟨hsep_in_Xp, h_sep_in_N⟩
  -- |F_outside_C| ≤ (Δ_B - s) * (Δ_A - 1).
  have hF_outside_C_card :
      F_outside_C.card ≤ (Xp \ N_H_ys_S).card * (Δ_A - 1) := by
    have h_fiber_eq :
        F_outside_C.card = (Xp \ N_H_ys_S).sum (fun a =>
          (F_outside_C.filter (fun e => sEndpoint S e = a)).card) := by
      rw [← Finset.card_attach (s := F_outside_C)]
      rw [Finset.card_eq_sum_card_fiberwise (f := fun e => sEndpoint S e.val)
        (s := F_outside_C.attach) (t := Xp \ N_H_ys_S)
        (fun e _ => by exact (Finset.mem_filter.mp e.property).2.1)]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Finset.card_bij (fun e _ => e.val) ?_ (fun _ _ _ _ heq => Subtype.ext heq) ?_
      · intro e he
        rw [Finset.mem_filter] at he ⊢
        exact ⟨e.property, he.2⟩
      · intro x hx
        rw [Finset.mem_filter] at hx
        refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
        rw [Finset.mem_filter]; exact ⟨Finset.mem_attach _ _, hx.2⟩
    -- Per-fiber bound: for each a ∈ Xp \ N_H_ys_S, fiber card ≤ Δ_A - 1.
    have h_per_fiber : ∀ a ∈ Xp \ N_H_ys_S,
        (F_outside_C.filter (fun e => sEndpoint S e = a)).card ≤ Δ_A - 1 := by
      intro a ha
      rw [Finset.mem_sdiff] at ha
      obtain ⟨ha_in_Xp, ha_notin_N⟩ := ha
      rw [hXp_def, Finset.mem_filter] at ha_in_Xp
      obtain ⟨ha_in_S, hadj_a_ys⟩ := ha_in_Xp
      -- Set NGa_no_ys := N_G(a) \ {ys}.
      set NGa_no_ys : Finset (Fin G.size) :=
        (Finset.univ.filter (fun u => G.graph.Adj a u)).erase ys with hNGa_no_ys_def
      -- Injection F_C-fiber-at-a → NGa_no_ys via scEndpoint.
      -- scEnd e ∈ N_G(a) (by adjacency) and scEnd e ≠ ys (since scEnd ∈ Sᶜ \ S_super,
      -- ys ∈ S_super, so scEnd ≠ ys).
      have h_inj_card :
          (F_outside_C.filter (fun e => sEndpoint S e = a)).card ≤ NGa_no_ys.card := by
        refine Finset.card_le_card_of_injOn (fun e => scEndpoint S e) ?_ ?_
        · intro e he
          rw [Finset.mem_coe, Finset.mem_filter] at he
          obtain ⟨he_FC, hsep_eq⟩ := he
          rw [hF_outside_C_def, Finset.mem_filter] at he_FC
          obtain ⟨he_H, _, hscep_out⟩ := he_FC
          rw [Finset.mem_sdiff] at hscep_out
          have hscep_in_Sc : scEndpoint S e ∈ (Sᶜ : Finset _) := hscep_out.1
          have hscep_notin_super : scEndpoint S e ∉ S_super := hscep_out.2
          -- Goal: scEnd e ∈ NGa_no_ys = (univ.filter (Adj a)) \ {ys}.
          change scEndpoint S e ∈ NGa_no_ys
          rw [hNGa_no_ys_def, Finset.mem_erase, Finset.mem_filter]
          refine ⟨?_, ?_, ?_⟩
          · -- scEnd e ≠ ys.
            intro h
            apply hscep_notin_super
            rw [h]; exact hys_in_S_super
          · exact Finset.mem_univ _
          · -- Adj a (scEnd e).
            rw [← hsep_eq]
            exact adj_sEndpoint_scEndpoint hH he_H
        · -- Injection.
          intro e₁ he₁ e₂ he₂ heq
          rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
          obtain ⟨he₁_FC, hsep₁⟩ := he₁
          obtain ⟨he₂_FC, hsep₂⟩ := he₂
          rw [hF_outside_C_def, Finset.mem_filter] at he₁_FC he₂_FC
          exact H_edge_determined_by_endpoints hS hH he₁_FC.1 he₂_FC.1
            (hsep₁.trans hsep₂.symm) heq
      -- Now bound |NGa_no_ys| ≤ Δ_A - 1.
      have h_ys_in_NGa : ys ∈ Finset.univ.filter (fun u => G.graph.Adj a u) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hadj_a_ys⟩
      have hNGa_card_le_ΔA :
          (Finset.univ.filter (fun u => G.graph.Adj a u)).card ≤ Δ_A :=
        degree_le_maxDegreeOn G S ha_in_S
      have hNGa_no_ys_card :
          NGa_no_ys.card = (Finset.univ.filter (fun u => G.graph.Adj a u)).card - 1 := by
        rw [hNGa_no_ys_def]
        rw [Finset.card_erase_of_mem h_ys_in_NGa]
      calc (F_outside_C.filter (fun e => sEndpoint S e = a)).card
          ≤ NGa_no_ys.card := h_inj_card
        _ = (Finset.univ.filter (fun u => G.graph.Adj a u)).card - 1 := hNGa_no_ys_card
        _ ≤ Δ_A - 1 := Nat.sub_le_sub_right hNGa_card_le_ΔA _
    -- Aggregate.
    calc F_outside_C.card
        = (Xp \ N_H_ys_S).sum (fun a =>
            (F_outside_C.filter (fun e => sEndpoint S e = a)).card) := h_fiber_eq
      _ ≤ (Xp \ N_H_ys_S).sum (fun _ => Δ_A - 1) := Finset.sum_le_sum h_per_fiber
      _ = (Xp \ N_H_ys_S).card * (Δ_A - 1) := by simp [Finset.sum_const]
  -- |Xp \ N_H_ys_S| ≤ Δ_B - s.
  have hN_H_ys_S_sub_Xp : N_H_ys_S ⊆ Xp := fun a ha => by
    have := hN_H_ys_S_prop a ha
    rw [hXp_def, Finset.mem_filter]; exact ⟨this.1, this.2⟩
  have hXp_diff_le : (Xp \ N_H_ys_S).card ≤ Δ_B - s := by
    rw [Finset.card_sdiff_of_subset hN_H_ys_S_sub_Xp, hN_H_ys_S_card]
    exact Nat.sub_le_sub_right hXp_card_le _
  -- Partition: H = F_super ⊔ F_outside.
  have h_partition_disjoint_SO : Disjoint F_super F_outside := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    rw [hF_super_def, Finset.mem_filter] at he₁
    rw [hF_outside_def, Finset.mem_filter] at he₂
    exact (Finset.mem_sdiff.mp he₂.2).2 he₁.2
  have h_partition_union : H = F_super ∪ F_outside := by
    ext e
    rw [Finset.mem_union]
    refine ⟨fun he => ?_, ?_⟩
    · have hscep_in_Sc : scEndpoint S e ∈ (Sᶜ : Finset _) :=
        Finset.mem_compl.mpr (scEndpoint_notMem hS hH he)
      by_cases h_scep_super : scEndpoint S e ∈ S_super
      · exact Or.inl (Finset.mem_filter.mpr ⟨he, h_scep_super⟩)
      · exact Or.inr (Finset.mem_filter.mpr
          ⟨he, Finset.mem_sdiff.mpr ⟨hscep_in_Sc, h_scep_super⟩⟩)
    · rintro (h | h) <;> exact (Finset.mem_filter.mp h).1
  have h_card_partition : H.card = F_super.card + F_outside.card := by
    rw [h_partition_union, Finset.card_union_of_disjoint h_partition_disjoint_SO]
  have hF_outside_card_le : F_outside.card ≤ F_outside_B.card + F_outside_C.card :=
    (Finset.card_le_card hF_outside_subset).trans (Finset.card_union_le _ _)
  have hF_super_card_le : F_super.card ≤ S_super.card * s :=
    hF_super_card_eq ▸ h_lemma_2_8_1
  have hF_outside_B_card_le : F_outside_B.card ≤ s * (Δ_A - S_super.card) :=
    h_lemma_2_8_2.trans_eq (by rw [hN_H_ys_S_card])
  -- Now combine (2-class cancellation):
  -- |H| = |F_super| + |F_outside|
  --     ≤ S_super.card·s + (s·(Δ_A - S_super.card) + (Δ_B - s)·(Δ_A - 1))
  --     = s·Δ_A + (Δ_B - s)·(Δ_A - 1)
  --     ≤ Δ_A·Δ_B
  calc H.card
      = F_super.card + F_outside.card := h_card_partition
    _ ≤ S_super.card * s + (F_outside_B.card + F_outside_C.card) := by gcongr
    _ ≤ S_super.card * s + (s * (Δ_A - S_super.card) + (Δ_B - s) * (Δ_A - 1)) := by
        gcongr
        calc F_outside_C.card
            ≤ (Xp \ N_H_ys_S).card * (Δ_A - 1) := hF_outside_C_card
          _ ≤ (Δ_B - s) * (Δ_A - 1) := Nat.mul_le_mul_right _ hXp_diff_le
    _ ≤ Δ_A * Δ_B := by
        have h1 : S_super.card * s + s * (Δ_A - S_super.card) = s * Δ_A := by
          rw [Nat.mul_comm S_super.card s, ← Nat.mul_add, Nat.add_sub_cancel' hS_super_le_Δ_A]
        have h3 : s * Δ_A + (Δ_B - s) * Δ_A = Δ_A * Δ_B := by
          rw [← Nat.add_mul, Nat.add_sub_cancel' hs_le_Δ_B, Nat.mul_comm]
        have h4 : (Δ_B - s) * (Δ_A - 1) ≤ (Δ_B - s) * Δ_A :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        linarith [h1, h3, h4]

/-! ## Main theorem (asymmetric) -/

/-- **Theorem 2.8** (Phase B★ of the development notes):
    For a bipartite graph `G` with explicit bipartition `(S, Sᶜ)`,
    `ω(L(G)²) ≤ maxDegreeOn G S · maxDegreeOn G Sᶜ`.

    Reduces to `antimatching_card_le_mul` via the
    `cliqueNumber` → `antimatchingOfClique` translation.

    The inequality is unconditional in `G` — no L²-clique hypothesis. -/
theorem omega_lineGraphSq_le_mul_bipartite
    (G : Flag emptyType) (S : Finset (Fin G.size))
    (hS : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S)) :
    cliqueNumber (lineGraphSqFlag G) ≤ maxDegreeOn G S * maxDegreeOn G Sᶜ := by
  unfold cliqueNumber
  refine csSup_le ⟨0, ∅, by simp, fun u hu => absurd hu (by simp)⟩ ?_
  rintro k ⟨T, hcard, hT⟩
  have hH_card : (antimatchingOfClique G T).card = T.card := antimatchingOfClique_card G T
  have hH_le := antimatching_card_le_mul G S hS _
    (antimatchingOfClique_is_antimatching G T hT)
  omega

/-! ## Symmetric corollary (FGST 1990 / Śleszyńska-Nowak 2016 in Lean) -/

/-- **Symmetric corollary**: for bipartite `G`,
    `ω(L(G)²) ≤ Δ(G)²`.

    This is FGST 1990's Theorem 1 (also reproved by Śleszyńska-Nowak 2016
    as Theorem 2). Follows immediately from
    `omega_lineGraphSq_le_mul_bipartite` and
    `maxDegreeOn_le_maxDegree`. -/
theorem omega_lineGraphSq_le_sq_bipartite
    (G : Flag emptyType) (hBip : IsBipartite G) :
    cliqueNumber (lineGraphSqFlag G) ≤ (maxDegree G) ^ 2 := by
  obtain ⟨S, hS⟩ := hBip
  calc cliqueNumber (lineGraphSqFlag G)
      ≤ maxDegreeOn G S * maxDegreeOn G Sᶜ := omega_lineGraphSq_le_mul_bipartite G S hS
    _ ≤ maxDegree G * maxDegree G :=
        Nat.mul_le_mul (maxDegreeOn_le_maxDegree G S) (maxDegreeOn_le_maxDegree G Sᶜ)
    _ = (maxDegree G) ^ 2 := by ring

end Davey2024

end

-- Axiom check (uncomment to verify locally):
-- #print axioms Davey2024.antimatching_card_le_mul
-- #print axioms Davey2024.omega_lineGraphSq_le_mul_bipartite
-- #print axioms Davey2024.omega_lineGraphSq_le_sq_bipartite
-- Verified 2026-05-23 (σ2.8-G: 2-class partition by S_super membership):
--   antimatching_card_le_mul           : [propext, Classical.choice, Quot.sound]
--   omega_lineGraphSq_le_mul_bipartite : [propext, Classical.choice, Quot.sound]
--   omega_lineGraphSq_le_sq_bipartite  : [propext, Classical.choice, Quot.sound]
-- antimatching_card_le_mul is SORRY-FREE. The simplified proof closes via:
--   (a) Pick z* ∈ Sᶜ maximising hDegree; s := hDegree H z*; X' := N_G(z*) ∩ S.
--   (b) S_super := {b ∈ Sᶜ : N_G(b) ∩ S ⊇ N_H(z*)} contains z*, |S_super| ≤ Δ_A.
--   (c) Key Lemma (h_super_vertex_implication): b ∉ S_super ⟹ every H-edge (a,b)
--       has a ∈ X', by bridge dichotomy at (e_z*, e) for any c ∈ N_H(z*) ∩ S
--       with c ∉ N_G(b).
--   (d) 2-class partition H = F_super ⊎ F_outside by scEndpoint ∈ S_super,
--       split F_outside ⊆ F_outside_B ∪ F_outside_C by Key Lemma.
--   (e) |F_super| ≤ |S_super|·s (Lemma 2.8.1 over the whole S_super, since
--       z* ∈ S_super ⊆ Sᶜ and pivot maximality gives hDegree H b ≤ s for all
--       b ∈ Sᶜ), |F_outside_B| ≤ s·(Δ_A-|S_super|), |F_outside_C| ≤ (Δ_B-s)·(Δ_A-1).
--   (f) Cancellation: |S_super|·s + s·(Δ_A-|S_super|) = s·Δ_A, hence
--       |H| ≤ s·Δ_A + (Δ_B - s)·(Δ_A - 1) ≤ Δ_A · Δ_B.
