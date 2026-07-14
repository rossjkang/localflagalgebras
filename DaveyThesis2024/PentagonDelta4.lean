import DaveyThesis2024.PentagonConjecture


/-!
# Pentagons in triangle-free graphs of maximum degree ≤ 4 (Δ = 4)

The per-vertex pentagon bound at Δ = 4: in a triangle-free graph with maximum degree
at most 4, every vertex lies on at most `24` pentagons, hence `5·P(G) ≤ 24·|G|`, i.e.
`P(G) ≤ 24|G|/5 = 4.8|G|`.

This is the honest *provable* bound from the local (per-vertex) certificate method, which
mirrors the Δ = 3 / Δ = 5 development (`pentagon_bound_delta3` / `pentagon_delta5_tight`).
It is NOT the conjectured Δ = 4 extremum `P ≤ 4|G|` (ratio `1/64`, attained by the
circulant `C₁₂(2,3)`, `pentagonCount = 48`): the per-vertex maximum decouples from the
density (the Chvátal graph has a vertex on `21 > 20` pentagons), so no per-vertex/per-edge
local-max argument can reach `4|G|`. The certificate here gives the best such bound,
`24` per vertex (`certY4 = (0,1,4,5,0)`: `2pq ≤ certY4 p + certY4 q` for `p+q ≤ 4` and
`(4−k)·certY4 k ≤ 4k`, so `2·Σ ≤ Σ_x (4−k_x)·certY4 k_x ≤ 4·Σ_x k_x ≤ 4·12`).
-/

namespace Davey2024

namespace PentagonLocal

open Finset
open scoped Classical

variable {G : Flag emptyType}

/-- Δ = 4 dual-certificate weights: `certY4 = (0, 1, 4, 5, 0, …)`. -/
def certY4 : ℕ → ℕ
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | _ => 0

lemma certY4_pair {p q : ℕ} (h : p + q ≤ 4) : 2 * (p * q) ≤ certY4 p + certY4 q := by
  have hp : p ≤ 4 := by omega
  have hq : q ≤ 4 := by omega
  interval_cases p <;> interval_cases q <;> revert h <;> decide

lemma certY4_token (k : ℕ) : (4 - k) * certY4 k ≤ 4 * k := by
  match k with
  | 0 | 1 | 2 | 3 => decide
  | n + 4 => rw [show 4 - (n + 4) = 0 by omega]; simp

/-- On a shell edge, the two attachment counts sum to at most 4 (Δ = 4 budget). -/
lemma attach_card_add_le4 (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 4)
    {v x y : Fin G.size} (hxy : G.graph.Adj x y) :
    (attachSet G v x).card + (attachSet G v y).card ≤ 4 := by
  rw [← Finset.card_union_of_disjoint (attachSet_disjoint hTF hxy)]
  refine le_trans (Finset.card_le_card ?_) (deg_le_of_maxDegree_le hΔ v)
  intro a ha
  rw [Finset.mem_union, attachSet, attachSet, Finset.mem_filter, Finset.mem_filter] at ha
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ a, by tauto⟩

/-- Capacity: total attachment over the shell is at most `4 · 3 = 12` (Δ = 4 budget). -/
lemma sum_attach_card_le4 (hΔ : maxDegree G ≤ 4) (v : Fin G.size) :
    ∑ x ∈ shellSet G v, (attachSet G v x).card ≤ 12 := by
  have hswap : ∑ x ∈ shellSet G v, (attachSet G v x).card
      = ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
          ((shellSet G v).filter fun x => G.graph.Adj x a).card := by
    simp only [attachSet, Finset.card_filter]
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hva : G.graph.Adj v a <;> simp [hva]
  rw [hswap]
  have hbound : ∀ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
      ((shellSet G v).filter fun x => G.graph.Adj x a).card ≤ 3 := by
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
      _ ≤ 3 := by have := deg_le_of_maxDegree_le hΔ a; omega
  calc ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
        ((shellSet G v).filter fun x => G.graph.Adj x a).card
      ≤ ∑ _a ∈ Finset.univ.filter (fun a => G.graph.Adj v a), 3 :=
        Finset.sum_le_sum hbound
    _ = (Finset.univ.filter (fun a => G.graph.Adj v a)).card * 3 := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 4 * 3 := Nat.mul_le_mul_right 3 (deg_le_of_maxDegree_le hΔ v)

/-- Shell degree and attachment count fit in the Δ = 4 degree budget. -/
lemma shellDeg_add_attach_le4 (hΔ : maxDegree G ≤ 4) (v x : Fin G.size) :
    ((shellSet G v).filter fun y => G.graph.Adj x y).card + (attachSet G v x).card ≤ 4 := by
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

/-- **The per-vertex pentagon bound at Δ ≤ 4**: every vertex of a triangle-free graph of
    maximum degree at most 4 lies on at most 24 pentagons. (Loose: the true per-vertex
    maximum is 21 (Chvátal); the certificate's fibre relaxation gives 24.) -/
theorem pentagonCountAt_le_24 (G : Flag emptyType) (hTF : IsTriangleFree G)
    (hΔ : maxDegree G ≤ 4) (v : Fin G.size) : pentagonCountAt G v ≤ 24 := by
  have hfiber := pentagonCountAt_le_sum hTF (le_trans hΔ (by norm_num)) v
  set T := ∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card
    with hT
  have hchain : 2 * T ≤ 48 := by
    have h1 : 2 * T
        ≤ ∑ p ∈ shellPairsLt G v, (certY4 (attachSet G v p.1).card
            + certY4 (attachSet G v p.2).card) := by
      rw [hT, Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      have hadj : G.graph.Adj p.1 p.2 :=
        ((Finset.mem_filter.mp hp).2).2
      exact certY4_pair (attach_card_add_le4 hTF hΔ hadj)
    have h2 : ∑ p ∈ shellPairsLt G v, (certY4 (attachSet G v p.1).card
            + certY4 (attachSet G v p.2).card)
        = ∑ x ∈ shellSet G v, ((shellSet G v).filter fun y => G.graph.Adj x y).card
            * certY4 (attachSet G v x).card := by
      rw [sum_pairsLt_endpoints v (fun u => certY4 (attachSet G v u).card),
        sum_pairsAdj_eq v (fun u => certY4 (attachSet G v u).card)]
    have h3 : ∑ x ∈ shellSet G v, ((shellSet G v).filter fun y => G.graph.Adj x y).card
            * certY4 (attachSet G v x).card
        ≤ ∑ x ∈ shellSet G v, 4 * (attachSet G v x).card := by
      refine Finset.sum_le_sum fun x _ => ?_
      have hbudget := shellDeg_add_attach_le4 hΔ v x
      calc ((shellSet G v).filter fun y => G.graph.Adj x y).card
              * certY4 (attachSet G v x).card
          ≤ (4 - (attachSet G v x).card) * certY4 (attachSet G v x).card :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 4 * (attachSet G v x).card := certY4_token _
    have h4 : ∑ x ∈ shellSet G v, 4 * (attachSet G v x).card ≤ 48 := by
      rw [← Finset.mul_sum]
      have := sum_attach_card_le4 hΔ v
      omega
    omega
  omega

end PentagonLocal

/-- **Per-vertex pentagon bound at Δ ≤ 4.** -/
theorem pentagonCountAt_le_24_of_maxDegree_le_four :
    ∀ G : Flag emptyType, IsTriangleFree G → maxDegree G ≤ 4 →
      ∀ v : Fin G.size, pentagonCountAt G v ≤ 24 :=
  fun G hTF hd v => PentagonLocal.pentagonCountAt_le_24 G hTF hd v

/-- **Pentagon density bound at Δ = 4** (honest local-method bound): every triangle-free
    graph of maximum degree at most 4 has `5·P(G) ≤ 24·|G|`, i.e. `P(G) ≤ 24|G|/5`.
    The conjectured (open) extremum is `P ≤ 4|G|` (ratio `1/64`, attained by `C₁₂(2,3)`);
    the gap reflects the per-vertex method's intrinsic looseness at Δ = 4. -/
theorem pentagon_bound_delta4 (G : Flag emptyType)
    (hTF : IsTriangleFree G) (hdeg : maxDegree G ≤ 4) :
    5 * pentagonCount G ≤ 24 * G.size := by
  rw [← pentagonCount_sum]
  calc ∑ v : Fin G.size, pentagonCountAt G v
      ≤ ∑ _v : Fin G.size, 24 :=
        Finset.sum_le_sum fun v _ =>
          pentagonCountAt_le_24_of_maxDegree_le_four G hTF hdeg v
    _ = 24 * G.size := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          Nat.mul_comm]

end Davey2024
