import DaveyThesis2024.PentagonDelta3
import DaveyThesis2024.PentagonUnique


/-!
# Uniqueness of the Δ = 3 pentagon extremum — the Petersen graph

Towards: a triangle-free graph with `Δ ≤ 3` attains `5·P = 6·|G|` (i.e. `P = 6n/5`) iff
every component is a Petersen graph. Mirrors the Δ = 5 development in `PentagonUnique.lean`
(`pentagon_delta5_extremal_iff`).

Structure:
* `pentagonCountAt_petersen_zero` : the Petersen graph has exactly 6 pentagons through
  vertex 0 (bound `≤ 6` + explicit list `≥ 6`).
* `pentagonCountAt_eq_six_of_extremal` : an extremal graph has `P(v) = 6` everywhere.
* `pentagon_delta3_extremal_of_petersen` : the reverse direction, via the degree-free
  `pentagonCountAt_transfer`.
* `exists_petersen_embedding` : the forward direction (SRG(10,3,0,1) reconstruction) —
  **the remaining work** (the single-6-ball shortcut fails, see `ICOfBaKF?`, so it uses
  the all-`P(v)=6` global structure).
* `pentagon_delta3_extremal_iff` : the characterisation.
-/

namespace Davey2024

open Finset
open scoped Classical

namespace PentagonLocal

variable {G : Flag emptyType}

/-- Each neighbour of `v` has at most 2 shell attachments (Δ = 3 analogue of
    `neighbor_attach_le_four`). -/
lemma neighbor_attach_le_two (hΔ : maxDegree G ≤ 3) {v a : Fin G.size}
    (ha : G.graph.Adj v a) :
    ((shellSet G v).filter fun x => G.graph.Adj x a).card ≤ 2 := by
  have hsub : (shellSet G v).filter (fun x => G.graph.Adj x a)
      ⊆ (Finset.univ.filter fun w => G.graph.Adj a w).erase v := by
    intro x hx
    rw [Finset.mem_filter, shellSet, Finset.mem_filter] at hx
    rw [Finset.mem_erase, Finset.mem_filter]
    exact ⟨hx.1.2.1, Finset.mem_univ x, hx.2.symm⟩
  have hvmem : v ∈ Finset.univ.filter fun w => G.graph.Adj a w := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ v, ha.symm⟩
  calc ((shellSet G v).filter fun x => G.graph.Adj x a).card
      ≤ ((Finset.univ.filter fun w => G.graph.Adj a w).erase v).card :=
        Finset.card_le_card hsub
    _ = (Finset.univ.filter fun w => G.graph.Adj a w).card - 1 :=
        Finset.card_erase_of_mem hvmem
    _ ≤ 2 := by have := deg_le_of_maxDegree_le hΔ a; omega

set_option maxHeartbeats 1600000 in
/-- **Equality structure at Δ = 3** (analogue of `eq_sixty_structure`): a vertex with
    exactly 6 pentagons through it, in a TF graph with `Δ ≤ 3`, has degree 3; each
    neighbour is attached to exactly 2 shell vertices; each shell vertex has attachment
    count `≤ 2`; a shell vertex with `k ≠ 0` has exactly `3 − k` shell neighbours; shell
    edges join equal attachment counts; and the total shell attachment is 6. -/
lemma eq_six_structure (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 3)
    {v : Fin G.size} (h6 : pentagonCountAt G v = 6) :
    (Finset.univ.filter fun w => G.graph.Adj v w).card = 3 ∧
    (∀ a, G.graph.Adj v a →
      ((shellSet G v).filter fun x => G.graph.Adj x a).card = 2) ∧
    (∀ x ∈ shellSet G v, (attachSet G v x).card ≤ 2) ∧
    (∀ x ∈ shellSet G v, (attachSet G v x).card ≠ 0 →
      ((shellSet G v).filter fun y => G.graph.Adj x y).card
        = 3 - (attachSet G v x).card) ∧
    (∀ p ∈ shellPairsLt G v,
      (attachSet G v p.1).card = (attachSet G v p.2).card) ∧
    ∑ x ∈ shellSet G v, (attachSet G v x).card = 6 := by
  have hfiber : 6 ≤ ∑ p ∈ shellPairsLt G v,
      (attachSet G v p.1).card * (attachSet G v p.2).card := by
    rw [← h6]; exact pentagonCountAt_le_sum hTF (le_trans hΔ (by norm_num)) v
  have h1le : ∀ p ∈ shellPairsLt G v,
      2 * ((attachSet G v p.1).card * (attachSet G v p.2).card)
        ≤ certY3 (attachSet G v p.1).card + certY3 (attachSet G v p.2).card := by
    intro p hp
    exact certY3_pair (attach_card_add_le3 hTF hΔ ((Finset.mem_filter.mp hp).2.2))
  have h1 : ∑ p ∈ shellPairsLt G v,
      2 * ((attachSet G v p.1).card * (attachSet G v p.2).card)
        ≤ ∑ p ∈ shellPairsLt G v,
            (certY3 (attachSet G v p.1).card + certY3 (attachSet G v p.2).card) :=
    Finset.sum_le_sum h1le
  have h1' : ∑ p ∈ shellPairsLt G v,
      2 * ((attachSet G v p.1).card * (attachSet G v p.2).card)
        = 2 * ∑ p ∈ shellPairsLt G v,
            (attachSet G v p.1).card * (attachSet G v p.2).card := by
    rw [Finset.mul_sum]
  have h2 : ∑ p ∈ shellPairsLt G v,
      (certY3 (attachSet G v p.1).card + certY3 (attachSet G v p.2).card)
        = ∑ x ∈ shellSet G v,
            ((shellSet G v).filter fun y => G.graph.Adj x y).card
              * certY3 (attachSet G v x).card := by
    rw [sum_pairsLt_endpoints v (fun u => certY3 (attachSet G v u).card),
      sum_pairsAdj_eq v (fun u => certY3 (attachSet G v u).card)]
  have h3ale : ∀ x ∈ shellSet G v,
      ((shellSet G v).filter fun y => G.graph.Adj x y).card
          * certY3 (attachSet G v x).card
        ≤ (3 - (attachSet G v x).card) * certY3 (attachSet G v x).card := by
    intro x _
    have := shellDeg_add_attach_le3 hΔ v x
    exact Nat.mul_le_mul_right _ (by omega)
  have h3a : ∑ x ∈ shellSet G v,
      ((shellSet G v).filter fun y => G.graph.Adj x y).card
          * certY3 (attachSet G v x).card
        ≤ ∑ x ∈ shellSet G v,
            (3 - (attachSet G v x).card) * certY3 (attachSet G v x).card :=
    Finset.sum_le_sum h3ale
  have h3ble : ∀ x ∈ shellSet G v,
      (3 - (attachSet G v x).card) * certY3 (attachSet G v x).card
        ≤ 2 * (attachSet G v x).card :=
    fun x _ => certY3_token _
  have h3b : ∑ x ∈ shellSet G v,
      (3 - (attachSet G v x).card) * certY3 (attachSet G v x).card
        ≤ ∑ x ∈ shellSet G v, 2 * (attachSet G v x).card :=
    Finset.sum_le_sum h3ble
  have h4 : ∑ x ∈ shellSet G v, 2 * (attachSet G v x).card
      = 2 * ∑ x ∈ shellSet G v, (attachSet G v x).card := by
    rw [Finset.mul_sum]
  have hK : ∑ x ∈ shellSet G v, (attachSet G v x).card ≤ 6 := sum_attach_card_le3 hΔ v
  have hKeq : ∑ x ∈ shellSet G v, (attachSet G v x).card = 6 := by omega
  have hCD : ∑ x ∈ shellSet G v,
      (3 - (attachSet G v x).card) * certY3 (attachSet G v x).card
        = ∑ x ∈ shellSet G v, 2 * (attachSet G v x).card := by omega
  have hBC : ∑ x ∈ shellSet G v,
      ((shellSet G v).filter fun y => G.graph.Adj x y).card
          * certY3 (attachSet G v x).card
        = ∑ x ∈ shellSet G v,
            (3 - (attachSet G v x).card) * certY3 (attachSet G v x).card := by omega
  have hTA : ∑ p ∈ shellPairsLt G v,
      2 * ((attachSet G v p.1).card * (attachSet G v p.2).card)
        = ∑ p ∈ shellPairsLt G v,
            (certY3 (attachSet G v p.1).card + certY3 (attachSet G v p.2).card) := by
    omega
  have hk3 : ∀ x : Fin G.size, (attachSet G v x).card ≤ 3 :=
    fun x => le_trans (attach_card_le_deg v x) (deg_le_of_maxDegree_le hΔ v)
  have hk012 : ∀ x ∈ shellSet G v, (attachSet G v x).card ≤ 2 := by
    intro x hx
    have heq := sum_squeeze h3ble hCD x hx
    have h3 := hk3 x
    have hcase : (attachSet G v x).card = 0 ∨ (attachSet G v x).card = 1 ∨
        (attachSet G v x).card = 2 ∨ (attachSet G v x).card = 3 := by omega
    rcases hcase with h | h | h | h <;> rw [h] at heq <;>
      simp only [certY3] at heq <;> omega
  have hshellDeg : ∀ x ∈ shellSet G v, (attachSet G v x).card ≠ 0 →
      ((shellSet G v).filter fun y => G.graph.Adj x y).card
        = 3 - (attachSet G v x).card := by
    intro x hx hne
    have heq := sum_squeeze h3ale hBC x hx
    have hle2 := hk012 x hx
    have hcase : (attachSet G v x).card = 1 ∨ (attachSet G v x).card = 2 := by omega
    rcases hcase with h | h <;> rw [h] at heq ⊢ <;> simp only [certY3] at heq <;> omega
  have hpair : ∀ p ∈ shellPairsLt G v,
      (attachSet G v p.1).card = (attachSet G v p.2).card := by
    intro p hp
    have heq := sum_squeeze h1le hTA p hp
    have hp12 := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have h1 := hk012 p.1 hp12.1
    have h2 := hk012 p.2 hp12.2
    rcases (show (attachSet G v p.1).card = 0 ∨ (attachSet G v p.1).card = 1 ∨
        (attachSet G v p.1).card = 2 by omega) with ha | ha | ha <;>
      rcases (show (attachSet G v p.2).card = 0 ∨ (attachSet G v p.2).card = 1 ∨
        (attachSet G v p.2).card = 2 by omega) with hb | hb | hb <;>
      rw [ha, hb] at heq ⊢ <;> simp only [certY3] at heq <;> omega
  have hb : ∀ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
      ((shellSet G v).filter fun x => G.graph.Adj x a).card ≤ 2 :=
    fun a ha => neighbor_attach_le_two hΔ (Finset.mem_filter.mp ha).2
  have hsw : ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
      ((shellSet G v).filter fun x => G.graph.Adj x a).card = 6 := by
    rw [← sum_attach_card_eq v]; exact hKeq
  have hup : ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
      ((shellSet G v).filter fun x => G.graph.Adj x a).card
        ≤ (Finset.univ.filter fun w => G.graph.Adj v w).card * 2 := by
    calc ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
          ((shellSet G v).filter fun x => G.graph.Adj x a).card
        ≤ ∑ _a ∈ Finset.univ.filter (fun a => G.graph.Adj v a), 2 :=
          Finset.sum_le_sum hb
      _ = (Finset.univ.filter fun w => G.graph.Adj v w).card * 2 := by
          rw [Finset.sum_const, smul_eq_mul]
  have hdle := deg_le_of_maxDegree_le hΔ v
  have hdeg3 : (Finset.univ.filter fun w => G.graph.Adj v w).card = 3 := by omega
  have ha2 : ∀ a, G.graph.Adj v a →
      ((shellSet G v).filter fun x => G.graph.Adj x a).card = 2 := by
    intro a ha
    have hmem : a ∈ Finset.univ.filter (fun a => G.graph.Adj v a) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ a, ha⟩
    have hconst : ∑ _a ∈ Finset.univ.filter (fun a => G.graph.Adj v a), 2 = 6 := by
      rw [Finset.sum_const, smul_eq_mul, hdeg3]
    exact sum_squeeze hb (hsw.trans hconst.symm) a hmem
  exact ⟨hdeg3, ha2, hk012, hshellDeg, hpair, hKeq⟩

/-- **No `k = 2` shell vertices**: at a 6-vertex, every shell vertex has attachment
    count `≤ 1`. (A `k = 2` vertex would have `shellDeg = 1`, hence a shell neighbour `y`
    with `k_y = 2` by the pair condition, but then `k_x + k_y = 4 > 3`.) So with the
    `μ = 1` shell, the Petersen ball structure is forced. -/
lemma attach_le_one_of_six (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 3)
    {v : Fin G.size} (h6 : pentagonCountAt G v = 6) :
    ∀ x ∈ shellSet G v, (attachSet G v x).card ≤ 1 := by
  obtain ⟨-, -, hk2, hsd, hpair, -⟩ := eq_six_structure hTF hΔ h6
  intro x hx
  by_contra hgt
  have hx2 : (attachSet G v x).card = 2 := by have := hk2 x hx; omega
  have hsd1 : ((shellSet G v).filter fun y => G.graph.Adj x y).card = 1 := by
    have h := hsd x hx (by omega)
    rw [hx2] at h
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rw [hsd1]; norm_num)
  rw [Finset.mem_filter] at hy
  obtain ⟨hyshell, hxy⟩ := hy
  have hxyne : x ≠ y := G.graph.ne_of_adj hxy
  have hky2 : (attachSet G v y).card = 2 := by
    rcases lt_or_gt_of_ne hxyne with hlt | hlt
    · have hp : (x, y) ∈ shellPairsLt G v := by
        rw [shellPairsLt, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hx, hyshell⟩, hlt, hxy⟩
      have hpe : (attachSet G v x).card = (attachSet G v y).card := hpair (x, y) hp
      omega
    · have hp : (y, x) ∈ shellPairsLt G v := by
        rw [shellPairsLt, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hyshell, hx⟩, hlt, hxy.symm⟩
      have hpe : (attachSet G v y).card = (attachSet G v x).card := hpair (y, x) hp
      omega
  have hsum := attach_card_add_le3 (v := v) hTF hΔ hxy
  omega

end PentagonLocal

/-- The 6 pentagons through vertex `0` of the Petersen graph. -/
def petersenPentagonsAtZero : Finset (Finset (Fin 10)) :=
  {{0, 1, 2, 3, 4}, {0, 1, 2, 5, 7}, {0, 1, 5, 6, 8},
   {0, 1, 4, 6, 9}, {0, 3, 4, 5, 8}, {0, 4, 5, 7, 9}}

lemma petersenPentagonsAtZero_card : petersenPentagonsAtZero.card = 6 := by decide

open scoped Classical in
set_option maxRecDepth 4000 in
lemma petersenPentagonsAtZero_sub : petersenPentagonsAtZero ⊆
    Finset.univ.filter fun S => IsPentagon petersenFlag S ∧ (0 : Fin 10) ∈ S := by
  intro S hS
  simp only [petersenPentagonsAtZero, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 2, 3, 4] : Fin 5 → Fin 10), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 2, 7, 5] : Fin 5 → Fin 10), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 6, 8, 5] : Fin 5 → Fin 10), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 6, 9, 4] : Fin 5 → Fin 10), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 4, 3, 8, 5] : Fin 5 → Fin 10), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 4, 9, 7, 5] : Fin 5 → Fin 10), by decide, by decide, by decide⟩, by decide⟩

/-- **The Petersen graph has exactly 6 pentagons through vertex 0.** -/
theorem pentagonCountAt_petersen_zero : pentagonCountAt petersenFlag (0 : Fin 10) = 6 := by
  refine le_antisymm
    (pentagonCountAt_le_six_of_maxDegree_le_three petersenFlag petersenFlag_triangleFree
      petersenFlag_maxDegree_le (0 : Fin 10)) ?_
  rw [pentagonCountAt]
  calc (6 : ℕ) = petersenPentagonsAtZero.card := petersenPentagonsAtZero_card.symm
    _ ≤ _ := Finset.card_le_card petersenPentagonsAtZero_sub

/-- **Averaging equality**: a triangle-free graph with `Δ ≤ 3` attaining `5·P = 6·|G|`
    has exactly 6 pentagons through every vertex. -/
theorem pentagonCountAt_eq_six_of_extremal (G : Flag emptyType)
    (hTF : IsTriangleFree G) (hdeg : maxDegree G ≤ 3)
    (hext : 5 * pentagonCount G = 6 * G.size) :
    ∀ v : Fin G.size, pentagonCountAt G v = 6 := by
  intro v
  by_contra hne
  have hub := fun u => pentagonCountAt_le_six_of_maxDegree_le_three G hTF hdeg u
  have hlt : pentagonCountAt G v < 6 := lt_of_le_of_ne (hub v) hne
  have hstrict : ∑ u : Fin G.size, pentagonCountAt G u < ∑ _u : Fin G.size, 6 :=
    Finset.sum_lt_sum (fun u _ => hub u) ⟨v, Finset.mem_univ v, hlt⟩
  rw [pentagonCount_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at hstrict
  omega

open PentagonLocal

/-- **μ ≤ 1**: in a triangle-free graph with `Δ ≤ 3` and `P(u) = 6` everywhere, two
    distinct non-adjacent vertices have at most one common neighbour. -/
lemma common_le_one {G : Flag emptyType} (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 3)
    (hall : ∀ u, pentagonCountAt G u = 6) {x y : Fin G.size}
    (hxy : x ≠ y) (hnadj : ¬G.graph.Adj x y) :
    (attachSet G x y).card ≤ 1 :=
  attach_le_one_of_six hTF hΔ (hall x) y (mem_shellSet.mpr ⟨hxy.symm, hnadj⟩)

/-- Common-neighbour uniqueness for distinct non-adjacent vertices (the `μ ≤ 1`
    consequence in elimination form). -/
lemma common_unique {G : Flag emptyType} (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 3)
    (hall : ∀ u, pentagonCountAt G u = 6) {x y w₁ w₂ : Fin G.size}
    (hxy : x ≠ y) (hnadj : ¬G.graph.Adj x y)
    (h1x : G.graph.Adj x w₁) (h1y : G.graph.Adj y w₁)
    (h2x : G.graph.Adj x w₂) (h2y : G.graph.Adj y w₂) : w₁ = w₂ :=
  Finset.card_le_one.mp (common_le_one hTF hΔ hall hxy hnadj)
    w₁ (mem_attachSet.mpr ⟨h1x, h1y⟩) w₂ (mem_attachSet.mpr ⟨h2x, h2y⟩)

set_option maxHeartbeats 1600000 in
/-- **Forward uniqueness (the SRG(10,3,0,1) reconstruction)** — in an all-`P(v)=6`
    triangle-free graph of maximum degree 3, every vertex lies in a closed induced copy
    of the Petersen graph (its connected component).

    REMAINING WORK. Unlike Δ=5, a single 6-ball does not force Petersen (the graph
    `ICOfBaKF?` has a lone `P(v)=6` vertex), so this uses the global all-`P(v)=6`
    structure: the equality squeeze gives, at every vertex, degree 3, a 6-vertex second
    shell with `μ = 1` attachments inducing a 6-cycle, and degree-saturation forces the
    radius-2 ball to be the whole component, which the Kneser `K(5,2)` labelling
    identifies with Petersen. -/
theorem exists_petersen_embedding {G : Flag emptyType} (hTF : IsTriangleFree G)
    (hΔ : maxDegree G ≤ 3) (hall : ∀ v, pentagonCountAt G v = 6) (v : Fin G.size) :
    ∃ φ : Fin 10 → Fin G.size, Function.Injective φ ∧ φ 0 = v ∧
      (∀ i j, petersenGraph.Adj i j ↔ G.graph.Adj (φ i) (φ j)) ∧
      (∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u) := by
  obtain ⟨hdeg3, ha2card, _hk2, hsd, hpair, _hKsum⟩ := eq_six_structure hTF hΔ (hall v)
  have hk1le' := attach_le_one_of_six hTF hΔ (hall v)
  set aF : Fin 3 → Fin G.size :=
    fun i => (Finset.univ.filter fun w => G.graph.Adj v w).orderEmbOfFin hdeg3 i with haFdef
  have haNv : ∀ i, aF i ∈ Finset.univ.filter fun w => G.graph.Adj v w :=
    fun i => Finset.orderEmbOfFin_mem _ hdeg3 i
  have hva : ∀ i, G.graph.Adj v (aF i) := fun i => (Finset.mem_filter.mp (haNv i)).2
  have haInj : Function.Injective aF := fun i j h =>
    (Finset.orderEmbOfFin _ hdeg3).injective h
  have haSurj : ∀ w, G.graph.Adj v w → ∃ i, aF i = w := by
    intro w hw
    have hmem : w ∈ Set.range ((Finset.univ.filter
        fun w => G.graph.Adj v w).orderEmbOfFin hdeg3) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩)
    exact hmem
  have hv_ne_a : ∀ i, v ≠ aF i := fun i heq => G.graph.irrefl (heq ▸ hva i)
  have hnaa : ∀ i j : Fin 3, i ≠ j → ¬G.graph.Adj (aF i) (aF j) :=
    fun i j _ hadj => hTF v (aF i) (aF j) (hva i) hadj (hva j)
  have hsame_class_nonadj : ∀ {x y : Fin G.size} {i : Fin 3},
      G.graph.Adj x (aF i) → G.graph.Adj y (aF i) → ¬G.graph.Adj x y :=
    fun {x y i} hxi hyi hxy => hTF (aF i) x y hxi.symm hxy hyi.symm
  have hk_of_adj : ∀ {a b : Fin G.size}, a ∈ shellSet G v → b ∈ shellSet G v →
      G.graph.Adj a b → (attachSet G v a).card = (attachSet G v b).card := by
    intro a b ha hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact hpair (a, b) (by
        rw [shellPairsLt, Finset.mem_filter, Finset.mem_product]; exact ⟨⟨ha, hb⟩, h, hab⟩)
    · exact absurd h (G.graph.ne_of_adj hab)
    · exact (hpair (b, a) (by
        rw [shellPairsLt, Finset.mem_filter, Finset.mem_product];
        exact ⟨⟨hb, ha⟩, h, hab.symm⟩)).symm
  have hsplit : ∀ (x : Fin G.size), x ∈ shellSet G v → ∀ (i : Fin 3),
      G.graph.Adj x (aF i) → ∀ (j : Fin 3), j ≠ i →
      ((shellSet G v).filter (fun y => G.graph.Adj x y ∧ G.graph.Adj y (aF j))).card = 1 := by
    intro x hxsh i hxi j hji
    have hmi : aF i ∈ attachSet G v x := mem_attachSet.mpr ⟨hva i, hxi⟩
    have hkx1 : (attachSet G v x).card = 1 :=
      le_antisymm (hk1le' x hxsh) (Finset.card_pos.mpr ⟨aF i, hmi⟩)
    have hNp2 : ((shellSet G v).filter (fun y => G.graph.Adj x y)).card = 2 := by
      have h := hsd x hxsh (by rw [hkx1]; exact one_ne_zero)
      rw [hkx1] at h; omega
    have hthird : ∀ a b : Fin 3, a ≠ i → b ≠ i → a ≠ j → b ≠ j → a = b := by
      intro a b hai hbi haj hbj
      have e1 : a.val ≠ i.val := fun h => hai (Fin.ext h)
      have e2 : b.val ≠ i.val := fun h => hbi (Fin.ext h)
      have e3 : a.val ≠ j.val := fun h => haj (Fin.ext h)
      have e4 : b.val ≠ j.val := fun h => hbj (Fin.ext h)
      have e5 : i.val ≠ j.val := fun h => hji (Fin.ext h).symm
      have ha3 := a.isLt; have hb3 := b.isLt; have hi3 := i.isLt; have hj3 := j.isLt
      exact Fin.ext (by omega)
    have hclass : ∀ z ∈ (shellSet G v).filter (fun y => G.graph.Adj x y),
        ∃ m : Fin 3, G.graph.Adj z (aF m) := by
      intro z hz
      have hzsh := (Finset.mem_filter.mp hz).1
      have hxz := (Finset.mem_filter.mp hz).2
      have hkz : (attachSet G v z).card = 1 := by
        have hh := hk_of_adj hxsh hzsh hxz; rw [hkx1] at hh; omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (by rw [hkz]; exact one_pos)
      obtain ⟨hvw, hzw⟩ := mem_attachSet.mp hw
      obtain ⟨m, hm⟩ := haSurj w hvw
      exact ⟨m, hm ▸ hzw⟩
    have hle : ((shellSet G v).filter
        (fun y => G.graph.Adj x y ∧ G.graph.Adj y (aF j))).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro y hy y' hy'
      obtain ⟨hysh, hxy, hyj⟩ := Finset.mem_filter.mp hy
      obtain ⟨hy'sh, hxy', hy'j⟩ := Finset.mem_filter.mp hy'
      by_contra hyne
      have he : aF j = x := common_unique hTF hΔ hall hyne (hsame_class_nonadj hyj hy'j)
        hyj hy'j hxy.symm hxy'.symm
      exact (mem_shellSet.mp hxsh).2 (he ▸ hva j)
    have hge : 1 ≤ ((shellSet G v).filter
        (fun y => G.graph.Adj x y ∧ G.graph.Adj y (aF j))).card := by
      rcases Finset.eq_empty_or_nonempty ((shellSet G v).filter
          (fun y => G.graph.Adj x y ∧ G.graph.Adj y (aF j))) with hE | hNE
      · exfalso
        obtain ⟨z₁, z₂, hz12, hNpeq⟩ := Finset.card_eq_two.mp hNp2
        have hz1Np : z₁ ∈ (shellSet G v).filter (fun y => G.graph.Adj x y) := by
          rw [hNpeq]; exact Finset.mem_insert_self _ _
        have hz2Np : z₂ ∈ (shellSet G v).filter (fun y => G.graph.Adj x y) := by
          rw [hNpeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        obtain ⟨m₁, hm₁⟩ := hclass z₁ hz1Np
        obtain ⟨m₂, hm₂⟩ := hclass z₂ hz2Np
        have hxz1 := (Finset.mem_filter.mp hz1Np).2
        have hxz2 := (Finset.mem_filter.mp hz2Np).2
        have hz1sh := (Finset.mem_filter.mp hz1Np).1
        have hz2sh := (Finset.mem_filter.mp hz2Np).1
        have hm1i : m₁ ≠ i := fun h => hsame_class_nonadj (h ▸ hm₁) hxi hxz1.symm
        have hm2i : m₂ ≠ i := fun h => hsame_class_nonadj (h ▸ hm₂) hxi hxz2.symm
        have hm1j : m₁ ≠ j := by
          intro h
          have hmem1 : z₁ ∈ (shellSet G v).filter
              (fun y => G.graph.Adj x y ∧ G.graph.Adj y (aF j)) :=
            Finset.mem_filter.mpr ⟨hz1sh, hxz1, h ▸ hm₁⟩
          rw [hE] at hmem1; exact Finset.notMem_empty _ hmem1
        have hm2j : m₂ ≠ j := by
          intro h
          have hmem2 : z₂ ∈ (shellSet G v).filter
              (fun y => G.graph.Adj x y ∧ G.graph.Adj y (aF j)) :=
            Finset.mem_filter.mpr ⟨hz2sh, hxz2, h ▸ hm₂⟩
          rw [hE] at hmem2; exact Finset.notMem_empty _ hmem2
        have hmm : m₁ = m₂ := hthird m₁ m₂ hm1i hm2i hm1j hm2j
        have heqx : aF m₁ = x := common_unique hTF hΔ hall hz12
          (hsame_class_nonadj hm₁ (hmm.symm ▸ hm₂)) hm₁ (hmm.symm ▸ hm₂) hxz1.symm hxz2.symm
        exact (mem_shellSet.mp hxsh).2 (heqx ▸ hva m₁)
      · exact hNE.card_pos
    omega
  obtain ⟨P0, P1, hP01ne, hS0eq⟩ := Finset.card_eq_two.mp (ha2card (aF 0) (hva 0))
  have hP0mem : P0 ∈ (shellSet G v).filter (fun x => G.graph.Adj x (aF 0)) := by
    rw [hS0eq]; exact Finset.mem_insert_self _ _
  have hP1mem : P1 ∈ (shellSet G v).filter (fun x => G.graph.Adj x (aF 0)) := by
    rw [hS0eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hP0sh := (Finset.mem_filter.mp hP0mem).1
  have hP0a0 := (Finset.mem_filter.mp hP0mem).2
  have hP1sh := (Finset.mem_filter.mp hP1mem).1
  have hP1a0 := (Finset.mem_filter.mp hP1mem).2
  obtain ⟨Q, hQeq⟩ := Finset.card_eq_one.mp (hsplit P0 hP0sh 0 hP0a0 1 (by decide))
  have hQmem : Q ∈ (shellSet G v).filter
      (fun y => G.graph.Adj P0 y ∧ G.graph.Adj y (aF 1)) := by
    rw [hQeq]; exact Finset.mem_singleton_self _
  obtain ⟨hQsh, hP0Q, hQa1⟩ := Finset.mem_filter.mp hQmem
  obtain ⟨R, hReq⟩ := Finset.card_eq_one.mp (hsplit P0 hP0sh 0 hP0a0 2 (by decide))
  have hRmem : R ∈ (shellSet G v).filter
      (fun y => G.graph.Adj P0 y ∧ G.graph.Adj y (aF 2)) := by
    rw [hReq]; exact Finset.mem_singleton_self _
  obtain ⟨hRsh, hP0R, hRa2⟩ := Finset.mem_filter.mp hRmem
  obtain ⟨Q1, hQ1eq⟩ := Finset.card_eq_one.mp (hsplit P1 hP1sh 0 hP1a0 1 (by decide))
  have hQ1mem : Q1 ∈ (shellSet G v).filter
      (fun y => G.graph.Adj P1 y ∧ G.graph.Adj y (aF 1)) := by
    rw [hQ1eq]; exact Finset.mem_singleton_self _
  obtain ⟨hQ1sh, hP1Q1, hQ1a1⟩ := Finset.mem_filter.mp hQ1mem
  obtain ⟨R1, hR1eq⟩ := Finset.card_eq_one.mp (hsplit P1 hP1sh 0 hP1a0 2 (by decide))
  have hR1mem : R1 ∈ (shellSet G v).filter
      (fun y => G.graph.Adj P1 y ∧ G.graph.Adj y (aF 2)) := by
    rw [hR1eq]; exact Finset.mem_singleton_self _
  obtain ⟨hR1sh, hP1R1, hR1a2⟩ := Finset.mem_filter.mp hR1mem
  have hnv_P0 : ¬G.graph.Adj v P0 := (mem_shellSet.mp hP0sh).2
  have hnv_Q : ¬G.graph.Adj v Q := (mem_shellSet.mp hQsh).2
  have hnv_P1 : ¬G.graph.Adj v P1 := (mem_shellSet.mp hP1sh).2
  have hnv_R : ¬G.graph.Adj v R := (mem_shellSet.mp hRsh).2
  have hnv_R1 : ¬G.graph.Adj v R1 := (mem_shellSet.mp hR1sh).2
  have hnv_Q1 : ¬G.graph.Adj v Q1 := (mem_shellSet.mp hQ1sh).2
  have hP0P1_nadj : ¬G.graph.Adj P0 P1 := hsame_class_nonadj hP0a0 hP1a0
  have hQne1 : Q ≠ Q1 := by
    intro h
    have he : aF 0 = Q :=
      common_unique hTF hΔ hall hP01ne hP0P1_nadj hP0a0 hP1a0 hP0Q (h.symm ▸ hP1Q1)
    exact hnv_Q (he ▸ hva 0)
  have hRne1 : R ≠ R1 := by
    intro h
    have he : aF 0 = R :=
      common_unique hTF hΔ hall hP01ne hP0P1_nadj hP0a0 hP1a0 hP0R (h.symm ▸ hP1R1)
    exact hnv_R (he ▸ hva 0)
  have hS1eq : (shellSet G v).filter (fun x => G.graph.Adj x (aF 1)) = {Q, Q1} :=
    (Finset.eq_of_subset_of_card_le
      (by
        intro w hw
        rw [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hQsh, hQa1⟩
        · exact Finset.mem_filter.mpr ⟨hQ1sh, hQ1a1⟩)
      (by rw [ha2card (aF 1) (hva 1)]; exact (Finset.card_pair hQne1).ge)).symm
  have hS2eq : (shellSet G v).filter (fun x => G.graph.Adj x (aF 2)) = {R, R1} :=
    (Finset.eq_of_subset_of_card_le
      (by
        intro w hw
        rw [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hRsh, hRa2⟩
        · exact Finset.mem_filter.mpr ⟨hR1sh, hR1a2⟩)
      (by rw [ha2card (aF 2) (hva 2)]; exact (Finset.card_pair hRne1).ge)).symm
  obtain ⟨RQ, hRQeq⟩ := Finset.card_eq_one.mp (hsplit Q hQsh 1 hQa1 2 (by decide))
  have hRQmem : RQ ∈ (shellSet G v).filter
      (fun y => G.graph.Adj Q y ∧ G.graph.Adj y (aF 2)) := by
    rw [hRQeq]; exact Finset.mem_singleton_self _
  obtain ⟨hRQsh, hQRQ, hRQa2⟩ := Finset.mem_filter.mp hRQmem
  have hQR1 : G.graph.Adj Q R1 := by
    have hRQneR : RQ ≠ R := fun h => hTF P0 Q R hP0Q (h ▸ hQRQ) hP0R
    have hRQS2 : RQ ∈ ({R, R1} : Finset (Fin G.size)) := by
      rw [← hS2eq]; exact Finset.mem_filter.mpr ⟨hRQsh, hRQa2⟩
    rcases Finset.mem_insert.mp hRQS2 with h | h
    · exact absurd h hRQneR
    · exact (Finset.mem_singleton.mp h) ▸ hQRQ
  obtain ⟨QR, hQReq⟩ := Finset.card_eq_one.mp (hsplit R hRsh 2 hRa2 1 (by decide))
  have hQRmem : QR ∈ (shellSet G v).filter
      (fun y => G.graph.Adj R y ∧ G.graph.Adj y (aF 1)) := by
    rw [hQReq]; exact Finset.mem_singleton_self _
  obtain ⟨hQRsh, hRQR, hQRa1⟩ := Finset.mem_filter.mp hQRmem
  have hRQ1 : G.graph.Adj R Q1 := by
    have hQRneQ : QR ≠ Q := fun h => hTF P0 R Q hP0R (h ▸ hRQR) hP0Q
    have hQRS1 : QR ∈ ({Q, Q1} : Finset (Fin G.size)) := by
      rw [← hS1eq]; exact Finset.mem_filter.mpr ⟨hQRsh, hQRa1⟩
    rcases Finset.mem_insert.mp hQRS1 with h | h
    · exact absurd h hQRneQ
    · exact (Finset.mem_singleton.mp h) ▸ hRQR
  have hattach_uniq : ∀ {x : Fin G.size}, x ∈ shellSet G v → ∀ {a b : Fin 3},
      G.graph.Adj x (aF a) → G.graph.Adj x (aF b) → a = b :=
    fun {x} hx {a b} hxa hxb => haInj (Finset.card_le_one.mp (hk1le' x hx) _
      (mem_attachSet.mpr ⟨hva a, hxa⟩) _ (mem_attachSet.mpr ⟨hva b, hxb⟩))
  have hcross_ne : ∀ {x y : Fin G.size} {a b : Fin 3}, x ∈ shellSet G v → y ∈ shellSet G v →
      G.graph.Adj x (aF a) → G.graph.Adj y (aF b) → a ≠ b → x ≠ y :=
    fun hx hy hxa hyb hab he => hab (hattach_uniq hx hxa (he.symm ▸ hyb))
  have hclosed3 : ∀ w : Fin G.size, ∀ s : Finset (Fin G.size), s.card = 3 →
      (∀ z ∈ s, G.graph.Adj w z) → ∀ u, G.graph.Adj w u → u ∈ s := by
    intro w s hcard hsub u hadj
    have hsubset : s ⊆ Finset.univ.filter (fun z => G.graph.Adj w z) := fun z hz =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ z, hsub z hz⟩
    have heq : s = Finset.univ.filter (fun z => G.graph.Adj w z) :=
      Finset.eq_of_subset_of_card_le hsubset
        (by rw [hcard]; exact deg_le_of_maxDegree_le hΔ w)
    rw [heq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hadj⟩
  have hcard3 : ∀ a b c : Fin G.size, a ≠ b → a ≠ c → b ≠ c →
      ({a, b, c} : Finset (Fin G.size)).card = 3 := by
    intro a b c hab hac hbc
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  -- non-adjacency facts (canonical orientation small<large)
  have n_0_2 : ¬G.graph.Adj (v) (P0) := hnv_P0
  have n_0_3 : ¬G.graph.Adj (v) (Q) := hnv_Q
  have n_0_6 : ¬G.graph.Adj (v) (P1) := hnv_P1
  have n_0_7 : ¬G.graph.Adj (v) (R) := hnv_R
  have n_0_8 : ¬G.graph.Adj (v) (R1) := hnv_R1
  have n_0_9 : ¬G.graph.Adj (v) (Q1) := hnv_Q1
  have n_1_3 : ¬G.graph.Adj (aF 0) (Q) := fun h => absurd (hattach_uniq hQsh hQa1 h.symm) (by decide)
  have n_1_4 : ¬G.graph.Adj (aF 0) (aF 1) := hnaa 0 1 (by decide)
  have n_1_5 : ¬G.graph.Adj (aF 0) (aF 2) := hnaa 0 2 (by decide)
  have n_1_7 : ¬G.graph.Adj (aF 0) (R) := fun h => absurd (hattach_uniq hRsh hRa2 h.symm) (by decide)
  have n_1_8 : ¬G.graph.Adj (aF 0) (R1) := fun h => absurd (hattach_uniq hR1sh hR1a2 h.symm) (by decide)
  have n_1_9 : ¬G.graph.Adj (aF 0) (Q1) := fun h => absurd (hattach_uniq hQ1sh hQ1a1 h.symm) (by decide)
  have n_2_4 : ¬G.graph.Adj (P0) (aF 1) := fun h => absurd (hattach_uniq hP0sh hP0a0 h) (by decide)
  have n_2_5 : ¬G.graph.Adj (P0) (aF 2) := fun h => absurd (hattach_uniq hP0sh hP0a0 h) (by decide)
  have n_2_6 : ¬G.graph.Adj (P0) (P1) := hP0P1_nadj
  have n_2_8 : ¬G.graph.Adj (P0) (R1) := fun h => absurd (common_unique hTF hΔ hall hRne1 (hsame_class_nonadj hRa2 hR1a2) hRa2 hR1a2 hP0R.symm h.symm) (fun he => hnv_P0 (he ▸ hva 2))
  have n_2_9 : ¬G.graph.Adj (P0) (Q1) := fun h => absurd (common_unique hTF hΔ hall hQne1 (hsame_class_nonadj hQa1 hQ1a1) hQa1 hQ1a1 hP0Q.symm h.symm) (fun he => hnv_P0 (he ▸ hva 1))
  have n_3_5 : ¬G.graph.Adj (Q) (aF 2) := fun h => absurd (hattach_uniq hQsh hQa1 h) (by decide)
  have n_3_6 : ¬G.graph.Adj (Q) (P1) := fun h => absurd (common_unique hTF hΔ hall hP01ne hP0P1_nadj hP0a0 hP1a0 hP0Q h.symm) (fun he => hnv_Q (he ▸ hva 0))
  have n_3_7 : ¬G.graph.Adj (Q) (R) := fun h => hTF P0 Q R hP0Q h hP0R
  have n_3_9 : ¬G.graph.Adj (Q) (Q1) := hsame_class_nonadj hQa1 hQ1a1
  have n_4_5 : ¬G.graph.Adj (aF 1) (aF 2) := hnaa 1 2 (by decide)
  have n_4_6 : ¬G.graph.Adj (aF 1) (P1) := fun h => absurd (hattach_uniq hP1sh hP1a0 h.symm) (by decide)
  have n_4_7 : ¬G.graph.Adj (aF 1) (R) := fun h => absurd (hattach_uniq hRsh hRa2 h.symm) (by decide)
  have n_4_8 : ¬G.graph.Adj (aF 1) (R1) := fun h => absurd (hattach_uniq hR1sh hR1a2 h.symm) (by decide)
  have n_5_6 : ¬G.graph.Adj (aF 2) (P1) := fun h => absurd (hattach_uniq hP1sh hP1a0 h.symm) (by decide)
  have n_5_9 : ¬G.graph.Adj (aF 2) (Q1) := fun h => absurd (hattach_uniq hQ1sh hQ1a1 h.symm) (by decide)
  have n_6_7 : ¬G.graph.Adj (P1) (R) := fun h => absurd (common_unique hTF hΔ hall hP01ne hP0P1_nadj hP0a0 hP1a0 hP0R h) (fun he => hnv_R (he ▸ hva 0))
  have n_7_8 : ¬G.graph.Adj (R) (R1) := hsame_class_nonadj hRa2 hR1a2
  have n_8_9 : ¬G.graph.Adj (R1) (Q1) := fun h => hTF P1 R1 Q1 hP1R1 h hP1Q1
  -- distinctness facts (canonical orientation small<large)
  have d_0_1 : (v) ≠ (aF 0) := hv_ne_a 0
  have d_0_2 : (v) ≠ (P0) := Ne.symm (mem_shellSet.mp hP0sh).1
  have d_0_3 : (v) ≠ (Q) := Ne.symm (mem_shellSet.mp hQsh).1
  have d_0_4 : (v) ≠ (aF 1) := hv_ne_a 1
  have d_0_5 : (v) ≠ (aF 2) := hv_ne_a 2
  have d_0_6 : (v) ≠ (P1) := Ne.symm (mem_shellSet.mp hP1sh).1
  have d_0_7 : (v) ≠ (R) := Ne.symm (mem_shellSet.mp hRsh).1
  have d_0_8 : (v) ≠ (R1) := Ne.symm (mem_shellSet.mp hR1sh).1
  have d_0_9 : (v) ≠ (Q1) := Ne.symm (mem_shellSet.mp hQ1sh).1
  have d_1_2 : (aF 0) ≠ (P0) := fun he => hnv_P0 (he ▸ hva 0)
  have d_1_3 : (aF 0) ≠ (Q) := fun he => hnv_Q (he ▸ hva 0)
  have d_1_4 : (aF 0) ≠ (aF 1) := fun he => absurd (haInj he) (by decide)
  have d_1_5 : (aF 0) ≠ (aF 2) := fun he => absurd (haInj he) (by decide)
  have d_1_6 : (aF 0) ≠ (P1) := fun he => hnv_P1 (he ▸ hva 0)
  have d_1_7 : (aF 0) ≠ (R) := fun he => hnv_R (he ▸ hva 0)
  have d_1_8 : (aF 0) ≠ (R1) := fun he => hnv_R1 (he ▸ hva 0)
  have d_1_9 : (aF 0) ≠ (Q1) := fun he => hnv_Q1 (he ▸ hva 0)
  have d_2_3 : (P0) ≠ (Q) := hcross_ne hP0sh hQsh hP0a0 hQa1 (by decide)
  have d_2_4 : (P0) ≠ (aF 1) := fun he => hnv_P0 (he.symm ▸ hva 1)
  have d_2_5 : (P0) ≠ (aF 2) := fun he => hnv_P0 (he.symm ▸ hva 2)
  have d_2_6 : (P0) ≠ (P1) := hP01ne
  have d_2_7 : (P0) ≠ (R) := hcross_ne hP0sh hRsh hP0a0 hRa2 (by decide)
  have d_2_8 : (P0) ≠ (R1) := hcross_ne hP0sh hR1sh hP0a0 hR1a2 (by decide)
  have d_2_9 : (P0) ≠ (Q1) := hcross_ne hP0sh hQ1sh hP0a0 hQ1a1 (by decide)
  have d_3_4 : (Q) ≠ (aF 1) := fun he => hnv_Q (he.symm ▸ hva 1)
  have d_3_5 : (Q) ≠ (aF 2) := fun he => hnv_Q (he.symm ▸ hva 2)
  have d_3_6 : (Q) ≠ (P1) := hcross_ne hQsh hP1sh hQa1 hP1a0 (by decide)
  have d_3_7 : (Q) ≠ (R) := hcross_ne hQsh hRsh hQa1 hRa2 (by decide)
  have d_3_8 : (Q) ≠ (R1) := hcross_ne hQsh hR1sh hQa1 hR1a2 (by decide)
  have d_3_9 : (Q) ≠ (Q1) := hQne1
  have d_4_5 : (aF 1) ≠ (aF 2) := fun he => absurd (haInj he) (by decide)
  have d_4_6 : (aF 1) ≠ (P1) := fun he => hnv_P1 (he ▸ hva 1)
  have d_4_7 : (aF 1) ≠ (R) := fun he => hnv_R (he ▸ hva 1)
  have d_4_8 : (aF 1) ≠ (R1) := fun he => hnv_R1 (he ▸ hva 1)
  have d_4_9 : (aF 1) ≠ (Q1) := fun he => hnv_Q1 (he ▸ hva 1)
  have d_5_6 : (aF 2) ≠ (P1) := fun he => hnv_P1 (he ▸ hva 2)
  have d_5_7 : (aF 2) ≠ (R) := fun he => hnv_R (he ▸ hva 2)
  have d_5_8 : (aF 2) ≠ (R1) := fun he => hnv_R1 (he ▸ hva 2)
  have d_5_9 : (aF 2) ≠ (Q1) := fun he => hnv_Q1 (he ▸ hva 2)
  have d_6_7 : (P1) ≠ (R) := hcross_ne hP1sh hRsh hP1a0 hRa2 (by decide)
  have d_6_8 : (P1) ≠ (R1) := hcross_ne hP1sh hR1sh hP1a0 hR1a2 (by decide)
  have d_6_9 : (P1) ≠ (Q1) := hcross_ne hP1sh hQ1sh hP1a0 hQ1a1 (by decide)
  have d_7_8 : (R) ≠ (R1) := hRne1
  have d_7_9 : (R) ≠ (Q1) := hcross_ne hRsh hQ1sh hRa2 hQ1a1 (by decide)
  have d_8_9 : (R1) ≠ (Q1) := hcross_ne hR1sh hQ1sh hR1a2 hQ1a1 (by decide)
  refine ⟨![v, aF 0, P0, Q, aF 1, aF 2, P1, R, R1, Q1], ?_, rfl, ?_, ?_⟩
  · -- injectivity
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hij (by assumption)
        | exact absurd hij (Ne.symm (by assumption))
  · -- induced adjacency
    intro i j
    have hva0 := hva 0; have hva1 := hva 1; have hva2 := hva 2
    fin_cases i <;> fin_cases j <;>
      first
        | exact iff_of_false (by decide) G.graph.irrefl
        | exact iff_of_true (by decide) (by assumption)
        | exact iff_of_true (by decide) (SimpleGraph.Adj.symm (by assumption))
        | exact iff_of_false (by decide) (by assumption)
        | exact iff_of_false (by decide) (fun h => absurd h.symm (by assumption))
  · -- closure
    intro i u hadj
    fin_cases i
    · have hu := hclosed3 (v) ({aF 0, aF 1, aF 2} : Finset (Fin G.size))
        (hcard3 (aF 0) (aF 1) (aF 2) (d_1_4) (d_1_5) (d_4_5))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> [exact hva 0; exact hva 1; exact hva 2]) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> [exact ⟨1, rfl⟩; exact ⟨4, rfl⟩; exact ⟨5, rfl⟩]
    · have hu := hclosed3 (aF 0) ({v, P0, P1} : Finset (Fin G.size))
        (hcard3 (v) (P0) (P1) (d_0_2) (d_0_6) (d_2_6))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> [exact (hva 0).symm; exact hP0a0.symm; exact hP1a0.symm]) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> [exact ⟨0, rfl⟩; exact ⟨2, rfl⟩; exact ⟨6, rfl⟩]
    · have hu := hclosed3 (P0) ({aF 0, Q, R} : Finset (Fin G.size))
        (hcard3 (aF 0) (Q) (R) (d_1_3) (d_1_7) (d_3_7))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> [exact hP0a0; exact hP0Q; exact hP0R]) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> [exact ⟨1, rfl⟩; exact ⟨3, rfl⟩; exact ⟨7, rfl⟩]
    · have hu := hclosed3 (Q) ({aF 1, P0, R1} : Finset (Fin G.size))
        (hcard3 (aF 1) (P0) (R1) ((Ne.symm d_2_4)) (d_4_8) (d_2_8))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> [exact hQa1; exact hP0Q.symm; exact hQR1]) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> [exact ⟨4, rfl⟩; exact ⟨2, rfl⟩; exact ⟨8, rfl⟩]
    · have hu := hclosed3 (aF 1) ({v, Q, Q1} : Finset (Fin G.size))
        (hcard3 (v) (Q) (Q1) (d_0_3) (d_0_9) (d_3_9))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> [exact (hva 1).symm; exact hQa1.symm; exact hQ1a1.symm]) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> [exact ⟨0, rfl⟩; exact ⟨3, rfl⟩; exact ⟨9, rfl⟩]
    · have hu := hclosed3 (aF 2) ({v, R, R1} : Finset (Fin G.size))
        (hcard3 (v) (R) (R1) (d_0_7) (d_0_8) (d_7_8))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> [exact (hva 2).symm; exact hRa2.symm; exact hR1a2.symm]) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> [exact ⟨0, rfl⟩; exact ⟨7, rfl⟩; exact ⟨8, rfl⟩]
    · have hu := hclosed3 (P1) ({aF 0, R1, Q1} : Finset (Fin G.size))
        (hcard3 (aF 0) (R1) (Q1) (d_1_8) (d_1_9) (d_8_9))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> [exact hP1a0; exact hP1R1; exact hP1Q1]) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> [exact ⟨1, rfl⟩; exact ⟨8, rfl⟩; exact ⟨9, rfl⟩]
    · have hu := hclosed3 (R) ({aF 2, P0, Q1} : Finset (Fin G.size))
        (hcard3 (aF 2) (P0) (Q1) ((Ne.symm d_2_5)) (d_5_9) (d_2_9))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> [exact hRa2; exact hP0R.symm; exact hRQ1]) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> [exact ⟨5, rfl⟩; exact ⟨2, rfl⟩; exact ⟨9, rfl⟩]
    · have hu := hclosed3 (R1) ({aF 2, Q, P1} : Finset (Fin G.size))
        (hcard3 (aF 2) (Q) (P1) ((Ne.symm d_3_5)) (d_5_6) (d_3_6))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> [exact hR1a2; exact hQR1.symm; exact hP1R1.symm]) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> [exact ⟨5, rfl⟩; exact ⟨3, rfl⟩; exact ⟨6, rfl⟩]
    · have hu := hclosed3 (Q1) ({aF 1, P1, R} : Finset (Fin G.size))
        (hcard3 (aF 1) (P1) (R) (d_4_6) (d_4_7) (d_6_7))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> [exact hQ1a1; exact hP1Q1.symm; exact hRQ1.symm]) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> [exact ⟨4, rfl⟩; exact ⟨6, rfl⟩; exact ⟨7, rfl⟩]

/-- **Reverse uniqueness**: if every vertex lies in a closed induced Petersen copy, then
    `5·P = 6·|G|`. Uses the degree-free `pentagonCountAt_transfer` and
    `pentagonCountAt_petersen_zero` (only vertex 0 is needed, since `φ 0 = v`). -/
theorem pentagon_delta3_extremal_of_petersen (G : Flag emptyType)
    (hcl : ∀ v : Fin G.size, ∃ φ : Fin 10 → Fin G.size, Function.Injective φ ∧ φ 0 = v ∧
      (∀ i j, petersenGraph.Adj i j ↔ G.graph.Adj (φ i) (φ j)) ∧
      (∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)) :
    5 * pentagonCount G = 6 * G.size := by
  have hall : ∀ v : Fin G.size, pentagonCountAt G v = 6 := by
    intro v
    obtain ⟨φ, hinj, h0, hiff, hclosed⟩ := hcl v
    have ht := pentagonCountAt_transfer (H := petersenFlag) (G := G) φ hinj hiff hclosed
      (0 : Fin 10)
    rw [h0, pentagonCountAt_petersen_zero] at ht
    exact ht
  calc 5 * pentagonCount G = ∑ v : Fin G.size, pentagonCountAt G v := (pentagonCount_sum G).symm
    _ = ∑ _v : Fin G.size, 6 := Finset.sum_congr rfl (fun v _ => hall v)
    _ = 6 * G.size := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]

/-- **Uniqueness of the Δ = 3 pentagon extremum**: a triangle-free graph with maximum
    degree at most 3 attains `5·P = 6·|G|` (i.e. `P = 6n/5`) iff every vertex lies in a
    closed induced copy of the Petersen graph — i.e. `G` is a disjoint union of Petersen
    graphs. -/
theorem pentagon_delta3_extremal_iff (G : Flag emptyType) (hTF : IsTriangleFree G)
    (hdeg : maxDegree G ≤ 3) :
    5 * pentagonCount G = 6 * G.size ↔
      ∀ v : Fin G.size, ∃ φ : Fin 10 → Fin G.size, Function.Injective φ ∧ φ 0 = v ∧
        (∀ i j, petersenGraph.Adj i j ↔ G.graph.Adj (φ i) (φ j)) ∧
        (∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u) := by
  refine ⟨fun hext v => ?_, pentagon_delta3_extremal_of_petersen G⟩
  exact exists_petersen_embedding hTF hdeg
    (pentagonCountAt_eq_six_of_extremal G hTF hdeg hext) v

end Davey2024
