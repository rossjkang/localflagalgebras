import DaveyThesis2024.PentagonConjecture


/-!
# Pentagons in triangle-free graphs of maximum degree ≤ 3 (Δ = 3)

The per-vertex pentagon bound at Δ = 3: in a triangle-free graph with maximum degree
at most 3, every vertex lies on at most `6` pentagons, hence `P(G) ≤ 6·|G|/5`, i.e.
`5·P(G) ≤ 6·|G|`. Tight at the Petersen graph (`P = 12`, `n = 10`).

This mirrors the Δ = 5 development in `PentagonConjecture.lean`
(`pentagon_delta5_tight`): the fibre bound `pentagonCountAt_le_sum` and the averaging
identity `pentagonCount_sum` are degree-free and reused verbatim; only the degree
budgets and the dual certificate are retuned for Δ = 3. The certificate is
`certY3 = (0, 1, 4, …)` with `2pq ≤ certY3 p + certY3 q` for `p + q ≤ 3` and
`(3 − k)·certY3 k ≤ 2k`, yielding `2·Σ ≤ Σ_x (3−k_x)·certY3 k_x ≤ 2·Σ_x k_x ≤ 2·6`,
i.e. `P(v) ≤ 6`.
-/

namespace Davey2024

namespace PentagonLocal

open Finset
open scoped Classical

variable {G : Flag emptyType}

/-- Δ = 3 dual-certificate weights (the analogue of `certY` for the `p + q ≤ 3`
    regime): `certY3 = (0, 1, 4, 0, …)`. -/
def certY3 : ℕ → ℕ
  | 1 => 1
  | 2 => 4
  | _ => 0

lemma certY3_pair {p q : ℕ} (h : p + q ≤ 3) : 2 * (p * q) ≤ certY3 p + certY3 q := by
  have hp : p ≤ 3 := by omega
  have hq : q ≤ 3 := by omega
  interval_cases p <;> interval_cases q <;> revert h <;> decide

lemma certY3_token (k : ℕ) : (3 - k) * certY3 k ≤ 2 * k := by
  match k with
  | 0 | 1 | 2 | 3 => decide
  | n + 4 => have h : 3 - (n + 4) = 0 := by omega
             rw [h, Nat.zero_mul]; exact Nat.zero_le _

/-- On a shell edge, the two attachment counts sum to at most 3 (Δ = 3 budget). -/
lemma attach_card_add_le3 (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 3)
    {v x y : Fin G.size} (hxy : G.graph.Adj x y) :
    (attachSet G v x).card + (attachSet G v y).card ≤ 3 := by
  rw [← Finset.card_union_of_disjoint (attachSet_disjoint hTF hxy)]
  refine le_trans (Finset.card_le_card ?_) (deg_le_of_maxDegree_le hΔ v)
  intro a ha
  rw [Finset.mem_union, attachSet, attachSet, Finset.mem_filter, Finset.mem_filter] at ha
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ a, by tauto⟩

/-- Capacity: total attachment over the shell is at most `3 · 2 = 6` (Δ = 3 budget). -/
lemma sum_attach_card_le3 (hΔ : maxDegree G ≤ 3) (v : Fin G.size) :
    ∑ x ∈ shellSet G v, (attachSet G v x).card ≤ 6 := by
  have hswap : ∑ x ∈ shellSet G v, (attachSet G v x).card
      = ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
          ((shellSet G v).filter fun x => G.graph.Adj x a).card := by
    simp only [attachSet, Finset.card_filter]
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hva : G.graph.Adj v a <;> simp [hva]
  rw [hswap]
  have hbound : ∀ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
      ((shellSet G v).filter fun x => G.graph.Adj x a).card ≤ 2 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    have hsub : (shellSet G v).filter (fun x => G.graph.Adj x a)
        ⊆ (Finset.univ.filter fun w => G.graph.Adj a w).erase v := by
      intro x hx
      rw [Finset.mem_filter, shellSet, Finset.mem_filter] at hx
      rw [Finset.mem_erase, Finset.mem_filter]
      exact ⟨hx.1.2.1, Finset.mem_univ x, hx.2.symm⟩
    have hvmem : v ∈ Finset.univ.filter fun w => G.graph.Adj a w := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ v, ha.2.symm⟩
    calc ((shellSet G v).filter fun x => G.graph.Adj x a).card
        ≤ ((Finset.univ.filter fun w => G.graph.Adj a w).erase v).card :=
          Finset.card_le_card hsub
      _ = (Finset.univ.filter fun w => G.graph.Adj a w).card - 1 :=
          Finset.card_erase_of_mem hvmem
      _ ≤ 2 := by have := deg_le_of_maxDegree_le hΔ a; omega
  calc ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
        ((shellSet G v).filter fun x => G.graph.Adj x a).card
      ≤ ∑ _a ∈ Finset.univ.filter (fun a => G.graph.Adj v a), 2 :=
        Finset.sum_le_sum hbound
    _ = (Finset.univ.filter (fun a => G.graph.Adj v a)).card * 2 := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 3 * 2 := Nat.mul_le_mul_right 2 (deg_le_of_maxDegree_le hΔ v)

/-- Shell degree and attachment count fit in the Δ = 3 degree budget. -/
lemma shellDeg_add_attach_le3 (hΔ : maxDegree G ≤ 3) (v x : Fin G.size) :
    ((shellSet G v).filter fun y => G.graph.Adj x y).card + (attachSet G v x).card ≤ 3 := by
  have hdisj : Disjoint ((shellSet G v).filter fun y => G.graph.Adj x y)
      (attachSet G v x) := by
    rw [Finset.disjoint_left]
    intro u hu ha
    rw [Finset.mem_filter, shellSet, Finset.mem_filter] at hu
    rw [attachSet, Finset.mem_filter] at ha
    exact hu.1.2.2 ha.2.1
  rw [← Finset.card_union_of_disjoint hdisj]
  refine le_trans (Finset.card_le_card ?_) (deg_le_of_maxDegree_le hΔ x)
  intro u hu
  rw [Finset.mem_union, Finset.mem_filter, attachSet, Finset.mem_filter] at hu
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ u, ?_⟩
  rcases hu with h | h
  · exact h.2
  · exact h.2.2

/-- **The per-vertex pentagon bound at Δ ≤ 3**: every vertex of a triangle-free
    graph of maximum degree at most 3 lies on at most 6 pentagons. -/
theorem pentagonCountAt_le_six (G : Flag emptyType) (hTF : IsTriangleFree G)
    (hΔ : maxDegree G ≤ 3) (v : Fin G.size) : pentagonCountAt G v ≤ 6 := by
  have hfiber := pentagonCountAt_le_sum hTF (le_trans hΔ (by norm_num)) v
  set T := ∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card
    with hT
  have hchain : 2 * T ≤ 12 := by
    have h1 : 2 * T
        ≤ ∑ p ∈ shellPairsLt G v, (certY3 (attachSet G v p.1).card
            + certY3 (attachSet G v p.2).card) := by
      rw [hT, Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      have hadj : G.graph.Adj p.1 p.2 :=
        ((Finset.mem_filter.mp hp).2).2
      exact certY3_pair (attach_card_add_le3 hTF hΔ hadj)
    have h2 : ∑ p ∈ shellPairsLt G v, (certY3 (attachSet G v p.1).card
            + certY3 (attachSet G v p.2).card)
        = ∑ x ∈ shellSet G v, ((shellSet G v).filter fun y => G.graph.Adj x y).card
            * certY3 (attachSet G v x).card := by
      rw [sum_pairsLt_endpoints v (fun u => certY3 (attachSet G v u).card),
        sum_pairsAdj_eq v (fun u => certY3 (attachSet G v u).card)]
    have h3 : ∑ x ∈ shellSet G v, ((shellSet G v).filter fun y => G.graph.Adj x y).card
            * certY3 (attachSet G v x).card
        ≤ ∑ x ∈ shellSet G v, 2 * (attachSet G v x).card := by
      refine Finset.sum_le_sum fun x _ => ?_
      have hbudget := shellDeg_add_attach_le3 hΔ v x
      calc ((shellSet G v).filter fun y => G.graph.Adj x y).card
              * certY3 (attachSet G v x).card
          ≤ (3 - (attachSet G v x).card) * certY3 (attachSet G v x).card :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 * (attachSet G v x).card := certY3_token _
    have h4 : ∑ x ∈ shellSet G v, 2 * (attachSet G v x).card ≤ 12 := by
      rw [← Finset.mul_sum]
      have := sum_attach_card_le3 hΔ v
      omega
    omega
  omega

end PentagonLocal

/-- **Per-vertex pentagon bound at Δ ≤ 3.** -/
theorem pentagonCountAt_le_six_of_maxDegree_le_three :
    ∀ G : Flag emptyType, IsTriangleFree G → maxDegree G ≤ 3 →
      ∀ v : Fin G.size, pentagonCountAt G v ≤ 6 :=
  fun G hTF hd v => PentagonLocal.pentagonCountAt_le_six G hTF hd v

/-- **Pentagon density bound at Δ = 3**: every triangle-free graph of maximum degree
    at most 3 has `5·P(G) ≤ 6·|G|`, i.e. `P(G) ≤ 6|G|/5`. Tight at the Petersen graph
    (`P = 12`, `n = 10`). -/
theorem pentagon_bound_delta3 (G : Flag emptyType)
    (hTF : IsTriangleFree G) (hdeg : maxDegree G ≤ 3) :
    5 * pentagonCount G ≤ 6 * G.size := by
  rw [← pentagonCount_sum]
  calc ∑ v : Fin G.size, pentagonCountAt G v
      ≤ ∑ _v : Fin G.size, 6 :=
        Finset.sum_le_sum fun v _ =>
          pentagonCountAt_le_six_of_maxDegree_le_three G hTF hdeg v
    _ = 6 * G.size := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          Nat.mul_comm]

/-! ## Tightness: the Petersen graph attains `P = 6n/5`

The Petersen graph (`n = 10`, 3-regular, triangle-free, girth 5) has exactly `12`
pentagons, and `5 · 12 = 60 = 6 · 10`, so it attains `pentagon_bound_delta3` with
equality. We only need `P ≥ 12` (twelve explicit pentagons), since the bound supplies
`P ≤ 12`. -/

/-- The 15 edges of the Petersen graph (one orientation each; `fromRel` symmetrises):
    outer 5-cycle `0-1-2-3-4`, spokes `i-(i+5)`, inner pentagram `5-7-9-6-8`. -/
def petersenEdges : Finset (ℕ × ℕ) :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (0, 4),
   (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
   (5, 7), (7, 9), (6, 9), (6, 8), (5, 8)}

/-- The Petersen graph on `Fin 10`. -/
def petersenGraph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel (fun u v => (u.val, v.val) ∈ petersenEdges)

instance instDecRelPetersen : DecidableRel petersenGraph.Adj := by
  unfold petersenGraph
  intro u v
  rw [SimpleGraph.fromRel_adj]
  exact instDecidableAnd

/-- The Petersen graph as a `Flag emptyType` (unlabelled 10-vertex graph). -/
def petersenFlag : Flag emptyType where
  size := 10
  graph := petersenGraph
  embedding := ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
  hsize := Nat.zero_le _

instance : DecidableRel petersenFlag.graph.Adj := instDecRelPetersen

/-- Triangle-freeness of Petersen, by kernel `decide`. -/
lemma petersenFlag_triangleFree : IsTriangleFree petersenFlag := by
  unfold IsTriangleFree
  decide

/-- Degree bound for Petersen, by kernel `decide` after an instance swap. -/
lemma petersenFlag_maxDegree_le : maxDegree petersenFlag ≤ 3 := by
  rw [maxDegree]
  refine Finset.sup_le fun v _ => ?_
  rw [Finset.filter_congr_decidable]
  revert v
  decide

/-- The 12 pentagons of the Petersen graph, listed explicitly as vertex sets. -/
def petersenPentagons : Finset (Finset (Fin 10)) :=
  {{0, 1, 2, 3, 4}, {0, 1, 2, 5, 7}, {0, 1, 5, 6, 8}, {0, 1, 4, 6, 9},
   {0, 3, 4, 5, 8}, {0, 4, 5, 7, 9}, {1, 2, 3, 6, 8}, {1, 2, 6, 7, 9},
   {2, 3, 4, 7, 9}, {2, 3, 5, 7, 8}, {3, 4, 6, 8, 9}, {5, 6, 7, 8, 9}}

lemma petersenPentagons_card : petersenPentagons.card = 12 := by decide

open scoped Classical in
set_option maxRecDepth 4000 in
lemma petersenPentagons_sub :
    petersenPentagons ⊆ Finset.univ.filter (IsPentagon petersenFlag) := by
  intro S hS
  simp only [petersenPentagons, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (![0, 1, 2, 3, 4] : Fin 5 → Fin 10), by decide, by decide, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (![0, 1, 2, 7, 5] : Fin 5 → Fin 10), by decide, by decide, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (![0, 1, 6, 8, 5] : Fin 5 → Fin 10), by decide, by decide, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (![0, 1, 6, 9, 4] : Fin 5 → Fin 10), by decide, by decide, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (![0, 4, 3, 8, 5] : Fin 5 → Fin 10), by decide, by decide, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (![0, 4, 9, 7, 5] : Fin 5 → Fin 10), by decide, by decide, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (![1, 2, 3, 8, 6] : Fin 5 → Fin 10), by decide, by decide, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (![1, 2, 7, 9, 6] : Fin 5 → Fin 10), by decide, by decide, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (![2, 3, 4, 9, 7] : Fin 5 → Fin 10), by decide, by decide, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (![2, 3, 8, 5, 7] : Fin 5 → Fin 10), by decide, by decide, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (![3, 4, 9, 6, 8] : Fin 5 → Fin 10), by decide, by decide, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (![5, 7, 9, 6, 8] : Fin 5 → Fin 10), by decide, by decide, by decide⟩

/-- **The Petersen graph has exactly 12 pentagons.** `P ≤ 12` from
    `pentagon_bound_delta3` (`5·P ≤ 6·10`), `P ≥ 12` from the explicit list. -/
theorem pentagonCount_petersen : pentagonCount petersenFlag = 12 := by
  refine le_antisymm ?_ ?_
  · have hb := pentagon_bound_delta3 petersenFlag petersenFlag_triangleFree
      petersenFlag_maxDegree_le
    have hs : petersenFlag.size = 10 := rfl
    rw [hs] at hb
    omega
  · rw [pentagonCount]
    calc (12 : ℕ) = petersenPentagons.card := petersenPentagons_card.symm
      _ ≤ _ := Finset.card_le_card petersenPentagons_sub

/-- **Tightness of the Δ = 3 bound**: the Petersen graph is triangle-free with
    maximum degree 3 and attains `5·P = 6·|G|` (`5·12 = 60 = 6·10`). -/
theorem pentagon_bound_delta3_tight :
    ∃ G : Flag emptyType, IsTriangleFree G ∧ maxDegree G ≤ 3 ∧
      5 * pentagonCount G = 6 * G.size :=
  ⟨petersenFlag, petersenFlag_triangleFree, petersenFlag_maxDegree_le, by
    rw [pentagonCount_petersen]; decide⟩

end Davey2024
