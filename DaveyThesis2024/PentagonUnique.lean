import DaveyThesis2024.PentagonConjecture

/-! # Uniqueness of the Δ ≤ 5 pentagon extremum — stage U1 (equality analysis)

Towards: a TF graph with `Δ ≤ 5` attains `P = 12·|G|` iff every component is a Clebsch
graph. Source: the development notes §3.5 (enumeration-free
uniqueness). This module holds the equality analysis (Lemma 9): squeezing the dual
certificate of `PentagonLocal.pentagonCountAt_le_sixty` at value 60 forces, at every
vertex, the local SRG(16,5,0,2) structure (`eq_sixty_structure`), and an extremal graph
has `P(v) = 60` everywhere (`pentagonCountAt_eq_sixty_of_extremal`).

Remaining stages (next sessions, reduction note §3.5 Steps A–C): local attachment pairs,
global pair distinctness, Kneser adjacency forcing, and the explicit folded-5-cube
isomorphism — no graph enumeration is required anywhere. -/

namespace Davey2024

namespace PentagonLocal

open Finset
open scoped Classical

variable {G : Flag emptyType}

/-- Pointwise squeeze: a sum equality with pointwise `≤` forces pointwise equality. -/
lemma sum_squeeze {α : Type*} {s : Finset α} {f g : α → ℕ}
    (hle : ∀ i ∈ s, f i ≤ g i) (heq : ∑ i ∈ s, f i = ∑ i ∈ s, g i) :
    ∀ i ∈ s, f i = g i := by
  intro i hi
  by_contra hne
  have hlt : ∑ x ∈ s, f x < ∑ x ∈ s, g x :=
    Finset.sum_lt_sum hle ⟨i, hi, lt_of_le_of_ne (hle i hi) hne⟩
  omega

/-- The attachment count never exceeds the root degree. -/
lemma attach_card_le_deg (v x : Fin G.size) :
    (attachSet G v x).card ≤ (Finset.univ.filter fun w => G.graph.Adj v w).card := by
  refine Finset.card_le_card fun a ha => Finset.mem_filter.mpr ?_
  rw [attachSet, Finset.mem_filter] at ha
  exact ⟨Finset.mem_univ a, ha.2.1⟩

/-- Double counting: total shell attachment equals total neighbour attachment. -/
lemma sum_attach_card_eq (v : Fin G.size) :
    ∑ x ∈ shellSet G v, (attachSet G v x).card
      = ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
          ((shellSet G v).filter fun x => G.graph.Adj x a).card := by
  simp only [attachSet, Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hva : G.graph.Adj v a <;> simp [hva]

/-- Each neighbour of `v` has at most 4 shell attachments. -/
lemma neighbor_attach_le_four (hΔ : maxDegree G ≤ 5) {v a : Fin G.size}
    (ha : G.graph.Adj v a) :
    ((shellSet G v).filter fun x => G.graph.Adj x a).card ≤ 4 := by
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
    _ ≤ 4 := by have := deg_le_of_maxDegree_le hΔ a; omega

/-- **Equality structure (reduction note Lemma 9, per vertex)**: a vertex with exactly
    60 pentagons through it, in a TF graph with `Δ ≤ 5`, has degree 5; each of its
    neighbours is attached to exactly 4 shell vertices; its non-neighbours have
    attachment count 0 or 2; the `k = 2` ones have exactly 3 shell neighbours; and
    shell edges never mix `k = 2` with `k = 0`. -/
lemma eq_sixty_structure (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 5)
    {v : Fin G.size} (h60 : pentagonCountAt G v = 60) :
    (Finset.univ.filter fun w => G.graph.Adj v w).card = 5 ∧
    (∀ a, G.graph.Adj v a →
      ((shellSet G v).filter fun x => G.graph.Adj x a).card = 4) ∧
    (∀ x ∈ shellSet G v,
      (attachSet G v x).card = 0 ∨ (attachSet G v x).card = 2) ∧
    (∀ x ∈ shellSet G v, (attachSet G v x).card = 2 →
      ((shellSet G v).filter fun y => G.graph.Adj x y).card = 3) ∧
    (∀ p ∈ shellPairsLt G v,
      ((attachSet G v p.1).card = 2 ↔ (attachSet G v p.2).card = 2)) ∧
    ∑ x ∈ shellSet G v, (attachSet G v x).card = 20 := by
  -- the certificate chain with every node named (raw expressions throughout, so that
  -- `omega` can identify the sums as shared atoms)
  have hfiber : 60 ≤ ∑ p ∈ shellPairsLt G v,
      (attachSet G v p.1).card * (attachSet G v p.2).card := by
    rw [← h60]; exact pentagonCountAt_le_sum hTF hΔ v
  have h1le : ∀ p ∈ shellPairsLt G v,
      2 * ((attachSet G v p.1).card * (attachSet G v p.2).card)
        ≤ certY (attachSet G v p.1).card + certY (attachSet G v p.2).card := by
    intro p hp
    exact certY_pair (attach_card_add_le hTF hΔ ((Finset.mem_filter.mp hp).2.2))
  have h1 : ∑ p ∈ shellPairsLt G v,
      2 * ((attachSet G v p.1).card * (attachSet G v p.2).card)
        ≤ ∑ p ∈ shellPairsLt G v,
            (certY (attachSet G v p.1).card + certY (attachSet G v p.2).card) :=
    Finset.sum_le_sum h1le
  have h1' : ∑ p ∈ shellPairsLt G v,
      2 * ((attachSet G v p.1).card * (attachSet G v p.2).card)
        = 2 * ∑ p ∈ shellPairsLt G v,
            (attachSet G v p.1).card * (attachSet G v p.2).card := by
    rw [Finset.mul_sum]
  have h2 : ∑ p ∈ shellPairsLt G v,
      (certY (attachSet G v p.1).card + certY (attachSet G v p.2).card)
        = ∑ x ∈ shellSet G v,
            ((shellSet G v).filter fun y => G.graph.Adj x y).card
              * certY (attachSet G v x).card := by
    rw [sum_pairsLt_endpoints v (fun u => certY (attachSet G v u).card),
      sum_pairsAdj_eq v (fun u => certY (attachSet G v u).card)]
  have h3ale : ∀ x ∈ shellSet G v,
      ((shellSet G v).filter fun y => G.graph.Adj x y).card
          * certY (attachSet G v x).card
        ≤ (5 - (attachSet G v x).card) * certY (attachSet G v x).card := by
    intro x _
    have := shellDeg_add_attach_le hΔ v x
    exact Nat.mul_le_mul_right _ (by omega)
  have h3a : ∑ x ∈ shellSet G v,
      ((shellSet G v).filter fun y => G.graph.Adj x y).card
          * certY (attachSet G v x).card
        ≤ ∑ x ∈ shellSet G v,
            (5 - (attachSet G v x).card) * certY (attachSet G v x).card :=
    Finset.sum_le_sum h3ale
  have h3ble : ∀ x ∈ shellSet G v,
      (5 - (attachSet G v x).card) * certY (attachSet G v x).card
        ≤ 6 * (attachSet G v x).card :=
    fun x _ => certY_token _
  have h3b : ∑ x ∈ shellSet G v,
      (5 - (attachSet G v x).card) * certY (attachSet G v x).card
        ≤ ∑ x ∈ shellSet G v, 6 * (attachSet G v x).card :=
    Finset.sum_le_sum h3ble
  have h4 : ∑ x ∈ shellSet G v, 6 * (attachSet G v x).card
      = 6 * ∑ x ∈ shellSet G v, (attachSet G v x).card := by
    rw [Finset.mul_sum]
  have hK : ∑ x ∈ shellSet G v, (attachSet G v x).card ≤ 20 := sum_attach_card_le hΔ v
  -- squeeze: every node of the chain is pinned
  have hKeq : ∑ x ∈ shellSet G v, (attachSet G v x).card = 20 := by omega
  have hCD : ∑ x ∈ shellSet G v,
      (5 - (attachSet G v x).card) * certY (attachSet G v x).card
        = ∑ x ∈ shellSet G v, 6 * (attachSet G v x).card := by omega
  have hBC : ∑ x ∈ shellSet G v,
      ((shellSet G v).filter fun y => G.graph.Adj x y).card
          * certY (attachSet G v x).card
        = ∑ x ∈ shellSet G v,
            (5 - (attachSet G v x).card) * certY (attachSet G v x).card := by omega
  have hTA : ∑ p ∈ shellPairsLt G v,
      2 * ((attachSet G v p.1).card * (attachSet G v p.2).card)
        = ∑ p ∈ shellPairsLt G v,
            (certY (attachSet G v p.1).card + certY (attachSet G v p.2).card) := by
    omega
  -- pointwise extractions
  have hk5 : ∀ x : Fin G.size, (attachSet G v x).card ≤ 5 :=
    fun x => le_trans (attach_card_le_deg v x) (deg_le_of_maxDegree_le hΔ v)
  have hk02 : ∀ x ∈ shellSet G v,
      (attachSet G v x).card = 0 ∨ (attachSet G v x).card = 2 := by
    intro x hx
    have heq := sum_squeeze h3ble hCD x hx
    have h5 := hk5 x
    have hcase : (attachSet G v x).card = 0 ∨ (attachSet G v x).card = 1 ∨
        (attachSet G v x).card = 2 ∨ (attachSet G v x).card = 3 ∨
        (attachSet G v x).card = 4 ∨ (attachSet G v x).card = 5 := by omega
    rcases hcase with h | h | h | h | h | h <;> rw [h] at heq <;>
      simp [certY] at heq
    · exact Or.inl h
    · exact Or.inr h
  have hdeg3 : ∀ x ∈ shellSet G v, (attachSet G v x).card = 2 →
      ((shellSet G v).filter fun y => G.graph.Adj x y).card = 3 := by
    intro x hx h2x
    have heq := sum_squeeze h3ale hBC x hx
    rw [h2x] at heq
    simp [certY] at heq
    omega
  have hpair : ∀ p ∈ shellPairsLt G v,
      ((attachSet G v p.1).card = 2 ↔ (attachSet G v p.2).card = 2) := by
    intro p hp
    have heq := sum_squeeze h1le hTA p hp
    have hp12 := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    constructor
    · intro h1x
      rcases hk02 p.2 hp12.2 with h2x | h2x
      · rw [h1x, h2x] at heq; simp [certY] at heq
      · exact h2x
    · intro h2x
      rcases hk02 p.1 hp12.1 with h1x | h1x
      · rw [h1x, h2x] at heq; simp [certY] at heq
      · exact h1x
  -- degree 5 and per-neighbour saturation
  have hb : ∀ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
      ((shellSet G v).filter fun x => G.graph.Adj x a).card ≤ 4 :=
    fun a ha => neighbor_attach_le_four hΔ (Finset.mem_filter.mp ha).2
  have hsw : ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
      ((shellSet G v).filter fun x => G.graph.Adj x a).card = 20 := by
    rw [← sum_attach_card_eq v]; exact hKeq
  have hup : ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
      ((shellSet G v).filter fun x => G.graph.Adj x a).card
        ≤ (Finset.univ.filter fun w => G.graph.Adj v w).card * 4 := by
    calc ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
          ((shellSet G v).filter fun x => G.graph.Adj x a).card
        ≤ ∑ _a ∈ Finset.univ.filter (fun a => G.graph.Adj v a), 4 :=
          Finset.sum_le_sum hb
      _ = (Finset.univ.filter fun w => G.graph.Adj v w).card * 4 := by
          rw [Finset.sum_const, smul_eq_mul]
  have hdle := deg_le_of_maxDegree_le hΔ v
  have hdeg5 : (Finset.univ.filter fun w => G.graph.Adj v w).card = 5 := by omega
  have ha4 : ∀ a, G.graph.Adj v a →
      ((shellSet G v).filter fun x => G.graph.Adj x a).card = 4 := by
    intro a ha
    have hmem : a ∈ Finset.univ.filter (fun a => G.graph.Adj v a) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ a, ha⟩
    have hconst : ∑ _a ∈ Finset.univ.filter (fun a => G.graph.Adj v a), 4 = 20 := by
      rw [Finset.sum_const, smul_eq_mul, hdeg5]
    exact sum_squeeze hb (hsw.trans hconst.symm) a hmem
  exact ⟨hdeg5, ha4, hk02, hdeg3, hpair, hKeq⟩

/-! ## Stage U2: structure forcing (reduction note §3.5, Steps A–C)

Throughout, `hall : ∀ u, pentagonCountAt G u = 60` (an *all-60* graph). We work at a
fixed root `v` and show: the ten `k = 2` shell vertices carry pairwise distinct
attachment pairs, and shell adjacency is attachment-pair disjointness (Kneser). -/

/-- Attachment sets are sets of neighbours of the root. -/
lemma attachSet_subset_nbrs (v x : Fin G.size) :
    attachSet G v x ⊆ Finset.univ.filter fun w => G.graph.Adj v w := by
  intro a ha
  rw [attachSet, Finset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2.1⟩

/-- Membership in an attachment set, unfolded. -/
lemma mem_attachSet {v x a : Fin G.size} :
    a ∈ attachSet G v x ↔ G.graph.Adj v a ∧ G.graph.Adj x a := by
  simp [attachSet, Finset.mem_filter]

/-- Membership in the shell, unfolded. -/
lemma mem_shellSet {v x : Fin G.size} :
    x ∈ shellSet G v ↔ x ≠ v ∧ ¬G.graph.Adj v x := by
  simp [shellSet, Finset.mem_filter]

/-- The `k = 2` part of the shell. -/
noncomputable def kTwo (G : Flag emptyType) (v : Fin G.size) : Finset (Fin G.size) :=
  (shellSet G v).filter fun x => (attachSet G v x).card = 2

lemma mem_kTwo {v x : Fin G.size} :
    x ∈ kTwo G v ↔ x ∈ shellSet G v ∧ (attachSet G v x).card = 2 := by
  rw [kTwo, Finset.mem_filter]

section AllSixty

variable (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 5)
variable (hall : ∀ u : Fin G.size, pentagonCountAt G u = 60)

include hTF hΔ hall

/-- In an all-60 graph there are exactly ten `k = 2` shell vertices at every root. -/
lemma kTwo_card (v : Fin G.size) : (kTwo G v).card = 10 := by
  obtain ⟨-, -, hk02, -, -, hsum20⟩ := eq_sixty_structure hTF hΔ (hall v)
  have hsplit := Finset.sum_filter_add_sum_filter_not (shellSet G v)
    (fun x => (attachSet G v x).card = 2) (fun x => (attachSet G v x).card)
  have h2 : ∑ x ∈ (shellSet G v).filter (fun x => (attachSet G v x).card = 2),
      (attachSet G v x).card = 2 * (kTwo G v).card := by
    rw [Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2),
      Finset.sum_const, smul_eq_mul, kTwo, Nat.mul_comm]
  have h0 : ∑ x ∈ (shellSet G v).filter (fun x => ¬(attachSet G v x).card = 2),
      (attachSet G v x).card = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.mem_filter] at hx
    rcases hk02 x hx.1 with h | h
    · exact h
    · exact absurd h hx.2
  omega

/-- μ-condition: common neighbours of distinct non-adjacent vertices number 0 or 2. -/
lemma common_card_mem {u w : Fin G.size} (hne : w ≠ u) (hnadj : ¬G.graph.Adj u w) :
    (attachSet G u w).card = 0 ∨ (attachSet G u w).card = 2 := by
  obtain ⟨-, -, hk02, -, -, -⟩ := eq_sixty_structure hTF hΔ (hall u)
  exact hk02 w (mem_shellSet.mpr ⟨hne, hnadj⟩)

/-- Shell neighbours of a `k = 2` vertex are `k = 2` (no mixed shell edges). -/
lemma kTwo_of_shell_adj {v x z : Fin G.size} (hx : x ∈ kTwo G v)
    (hz : z ∈ shellSet G v) (hadj : G.graph.Adj x z) : z ∈ kTwo G v := by
  obtain ⟨-, -, -, -, hpair, -⟩ := eq_sixty_structure hTF hΔ (hall v)
  obtain ⟨hxsh, hx2⟩ := mem_kTwo.mp hx
  rcases lt_trichotomy x z with hlt | heq | hgt
  · have hp : (x, z) ∈ shellPairsLt G v := by
      rw [shellPairsLt, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hxsh, hz⟩, hlt, hadj⟩
    exact mem_kTwo.mpr ⟨hz, (hpair _ hp).mp hx2⟩
  · exact absurd heq (G.graph.ne_of_adj hadj)
  · have hp : (z, x) ∈ shellPairsLt G v := by
      rw [shellPairsLt, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hz, hxsh⟩, hgt, hadj.symm⟩
    exact mem_kTwo.mpr ⟨hz, (hpair _ hp).mpr hx2⟩

omit hΔ hall in
/-- Common neighbours of `x ∈ shell(v)` and `e ∈ N(v)` are exactly the shell
    neighbours of `x` attached to `e` (triangle-freeness keeps them off `N(v)`). -/
lemma common_eq_shell_attached {v x e : Fin G.size}
    (hx : x ∈ shellSet G v) (he : G.graph.Adj v e) :
    attachSet G e x = ((shellSet G v).filter fun z => G.graph.Adj x z).filter
      (fun z => e ∈ attachSet G v z) := by
  ext w
  rw [mem_attachSet, Finset.mem_filter, Finset.mem_filter, mem_shellSet, mem_attachSet]
  constructor
  · rintro ⟨hew, hxw⟩
    have hwv : w ≠ v := by rintro rfl; exact (mem_shellSet.mp hx).2 hxw.symm
    have hnvw : ¬G.graph.Adj v w := fun hvw => hTF v e w he hew hvw
    exact ⟨⟨⟨hwv, hnvw⟩, hxw⟩, he, hew.symm⟩
  · rintro ⟨⟨⟨hwv, hnvw⟩, hxw⟩, _, hwe⟩
    exact ⟨hwe.symm, hxw⟩

/-- **Local carrier (Step A)**: every 2-subset of `N(v) ∖ A_x` is the attachment pair
    of some shell neighbour of `x`. -/
lemma local_carrier {v x : Fin G.size} (hx : x ∈ kTwo G v)
    {Q : Finset (Fin G.size)}
    (hQsub : Q ⊆ (Finset.univ.filter fun w => G.graph.Adj v w) \ attachSet G v x)
    (hQcard : Q.card = 2) :
    ∃ z, z ∈ kTwo G v ∧ G.graph.Adj x z ∧ attachSet G v z = Q := by
  obtain ⟨hdeg5, -, -, hdeg3, -, -⟩ := eq_sixty_structure hTF hΔ (hall v)
  obtain ⟨hxsh, hx2⟩ := mem_kTwo.mp hx
  have hNF3 : ((shellSet G v).filter fun z => G.graph.Adj x z).card = 3 :=
    hdeg3 x hxsh hx2
  have hcomp3 : ((Finset.univ.filter fun w => G.graph.Adj v w) \ attachSet G v x).card
      = 3 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (attachSet_subset_nbrs v x),
      hdeg5, hx2]
  have he0card : (((Finset.univ.filter fun w => G.graph.Adj v w) \ attachSet G v x)
      \ Q).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hQsub, hcomp3, hQcard]
  obtain ⟨e0, he0⟩ := Finset.card_eq_one.mp he0card
  have he0mem : e0 ∈ (Finset.univ.filter fun w => G.graph.Adj v w) \ attachSet G v x := by
    have h : e0 ∈ ((Finset.univ.filter fun w => G.graph.Adj v w) \ attachSet G v x)
        \ Q := by
      rw [he0]; exact Finset.mem_singleton_self e0
    exact (Finset.mem_sdiff.mp h).1
  have hve0 : G.graph.Adj v e0 :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp he0mem).1).2
  have hnxe0 : ¬G.graph.Adj x e0 := fun hadj =>
    (Finset.mem_sdiff.mp he0mem).2 (mem_attachSet.mpr ⟨hve0, hadj⟩)
  have hQeq : ∀ a, a ∈ Q ↔
      (a ∈ (Finset.univ.filter fun w => G.graph.Adj v w) \ attachSet G v x ∧ a ≠ e0) := by
    intro a
    constructor
    · intro haQ
      refine ⟨hQsub haQ, fun h => ?_⟩
      have : e0 ∈ ((Finset.univ.filter fun w => G.graph.Adj v w) \ attachSet G v x)
          \ Q := by rw [he0]; exact Finset.mem_singleton_self e0
      exact (Finset.mem_sdiff.mp this).2 (h ▸ haQ)
    · rintro ⟨hamem, hane⟩
      by_contra haQ
      have : a ∈ ((Finset.univ.filter fun w => G.graph.Adj v w) \ attachSet G v x)
          \ Q := Finset.mem_sdiff.mpr ⟨hamem, haQ⟩
      rw [he0, Finset.mem_singleton] at this
      exact hane this
  have hzfacts : ∀ z ∈ (shellSet G v).filter (fun z => G.graph.Adj x z),
      z ∈ kTwo G v ∧ attachSet G v z
        ⊆ (Finset.univ.filter fun w => G.graph.Adj v w) \ attachSet G v x := by
    intro z hz
    rw [Finset.mem_filter] at hz
    refine ⟨kTwo_of_shell_adj hTF hΔ hall hx hz.1 hz.2, fun a ha => ?_⟩
    rw [Finset.mem_sdiff]
    refine ⟨attachSet_subset_nbrs v z ha, fun hax => ?_⟩
    exact (Finset.disjoint_left.mp (attachSet_disjoint hTF hz.2) hax) ha
  by_contra hno
  push_neg at hno
  have hall_e0 : ∀ z ∈ (shellSet G v).filter (fun z => G.graph.Adj x z),
      e0 ∈ attachSet G v z := by
    intro z hz
    obtain ⟨hzk2, hzsub⟩ := hzfacts z hz
    by_contra he0z
    have hsub' : attachSet G v z ⊆ Q := by
      intro a ha
      rw [hQeq a]
      exact ⟨hzsub ha, fun h => he0z (h ▸ ha)⟩
    have hzQ : attachSet G v z = Q :=
      Finset.eq_of_subset_of_card_le hsub' (by rw [hQcard, (mem_kTwo.mp hzk2).2])
    exact hno z hzk2 (Finset.mem_filter.mp hz).2 hzQ
  have hcommon3 : (attachSet G e0 x).card = 3 := by
    rw [common_eq_shell_attached hTF hxsh hve0, Finset.filter_true_of_mem hall_e0]
    exact hNF3
  have hxe0 : x ≠ e0 := by
    rintro rfl
    exact (mem_shellSet.mp hxsh).2 hve0
  have hμ := common_card_mem hTF hΔ hall hxe0 (fun h => hnxe0 h.symm)
  omega

end AllSixty

/-- The set of shell vertices carrying a given attachment pair. -/
noncomputable def carriers (G : Flag emptyType) (v : Fin G.size)
    (P : Finset (Fin G.size)) : Finset (Fin G.size) :=
  (shellSet G v).filter fun w => attachSet G v w = P

/-- Membership in a carrier set. -/
lemma mem_carriers {v w : Fin G.size} {P : Finset (Fin G.size)} :
    w ∈ carriers G v P ↔ w ∈ shellSet G v ∧ attachSet G v w = P := by
  rw [carriers, Finset.mem_filter]

/-- Carrier sets of distinct pairs are disjoint. -/
lemma carriers_disjoint {v : Fin G.size} {P Q : Finset (Fin G.size)} (h : P ≠ Q) :
    Disjoint (carriers G v P) (carriers G v Q) := by
  rw [Finset.disjoint_left]
  intro w hwP hwQ
  exact h ((mem_carriers.mp hwP).2.symm.trans (mem_carriers.mp hwQ).2)

section AllSixtyB

variable (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 5)
variable (hall : ∀ u : Fin G.size, pentagonCountAt G u = 60)

include hTF hΔ hall

/-- **Step B**: distinct `k = 2` shell vertices carry distinct attachment pairs. -/
lemma attach_injOn {v : Fin G.size} :
    ∀ x ∈ kTwo G v, ∀ y ∈ kTwo G v, attachSet G v x = attachSet G v y → x = y := by
  intro x hx y hy hAeq
  by_contra hne
  obtain ⟨hxsh, hx2⟩ := mem_kTwo.mp hx
  obtain ⟨hysh, hy2⟩ := mem_kTwo.mp hy
  obtain ⟨hdeg5, ha4, -, -, -, -⟩ := eq_sixty_structure hTF hΔ (hall v)
  -- x and y are non-adjacent, with common neighbourhood exactly `A_x`
  have hnadj : ¬G.graph.Adj x y := by
    intro hadj
    have hdisj := attachSet_disjoint hTF (v := v) hadj
    rw [hAeq, disjoint_self] at hdisj
    rw [hAeq, hdisj] at hx2
    simp at hx2
  have hAsub : attachSet G v x ⊆ attachSet G x y := by
    intro a ha
    have ha' : a ∈ attachSet G v y := hAeq ▸ ha
    exact mem_attachSet.mpr ⟨(mem_attachSet.mp ha).2, (mem_attachSet.mp ha').2⟩
  have hcommon2 : (attachSet G x y).card = 2 := by
    have hμ := common_card_mem hTF hΔ hall (Ne.symm hne) hnadj
    have hge : 2 ≤ (attachSet G x y).card := hx2 ▸ Finset.card_le_card hAsub
    omega
  have hcommon_eq : attachSet G v x = attachSet G x y :=
    Finset.eq_of_subset_of_card_le hAsub (by omega)
  -- no shell vertex is adjacent to both x and y
  have hNFdisj : ∀ z ∈ shellSet G v, G.graph.Adj x z → G.graph.Adj y z → False := by
    intro z hzsh hxz hyz
    have hz : z ∈ attachSet G v x := hcommon_eq ▸ mem_attachSet.mpr ⟨hxz, hyz⟩
    exact (mem_shellSet.mp hzsh).2 (mem_attachSet.mp hz).1
  -- every 2-subset of the complement has at least two carriers
  have htwo : ∀ Q : Finset (Fin G.size),
      Q ⊆ (Finset.univ.filter fun w => G.graph.Adj v w) \ attachSet G v x →
      Q.card = 2 → 2 ≤ (carriers G v Q).card := by
    intro Q hQsub hQcard
    obtain ⟨zx, hzxk2, hzxadj, hzxA⟩ := local_carrier hTF hΔ hall hx hQsub hQcard
    obtain ⟨zy, hzyk2, hzyadj, hzyA⟩ := local_carrier hTF hΔ hall hy
      (hAeq ▸ hQsub) hQcard
    have hzne : zx ≠ zy := by
      rintro rfl
      exact hNFdisj zx (mem_kTwo.mp hzxk2).1 hzxadj hzyadj
    exact Finset.one_lt_card.mpr
      ⟨zx, mem_carriers.mpr ⟨(mem_kTwo.mp hzxk2).1, hzxA⟩,
       zy, mem_carriers.mpr ⟨(mem_kTwo.mp hzyk2).1, hzyA⟩, hzne⟩
  -- carrier sets of pairs through q ∈ N(v) live inside q's shell neighbourhood
  have hcov : ∀ q, G.graph.Adj v q → ∀ P : Finset (Fin G.size), q ∈ P →
      carriers G v P ⊆ (shellSet G v).filter fun w => G.graph.Adj w q := by
    intro q _ P hqP w hw
    obtain ⟨hwsh, hwA⟩ := mem_carriers.mp hw
    rw [Finset.mem_filter]
    exact ⟨hwsh, (mem_attachSet.mp (by rw [hwA]; exact hqP)).2⟩
  have hcomp3 : ((Finset.univ.filter fun w => G.graph.Adj v w)
      \ attachSet G v x).card = 3 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (attachSet_subset_nbrs v x),
      hdeg5, hx2]
  -- mixed pairs {q, t} (q in the complement, t ∈ A_x) have no carriers
  have hmixed : ∀ q ∈ (Finset.univ.filter fun w => G.graph.Adj v w) \ attachSet G v x,
      ∀ t ∈ attachSet G v x, carriers G v {q, t} = ∅ := by
    intro q hq t ht
    have hqNv : G.graph.Adj v q := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hq).1).2
    have hqA : q ∉ attachSet G v x := (Finset.mem_sdiff.mp hq).2
    have hrscard : (((Finset.univ.filter fun w => G.graph.Adj v w)
        \ attachSet G v x).erase q).card = 2 := by
      rw [Finset.card_erase_of_mem hq, hcomp3]
    obtain ⟨r, s, hrs, hrseq⟩ := Finset.card_eq_two.mp hrscard
    have hrmem : r ∈ ((Finset.univ.filter fun w => G.graph.Adj v w)
        \ attachSet G v x).erase q := by rw [hrseq]; exact Finset.mem_insert_self r {s}
    have hsmem : s ∈ ((Finset.univ.filter fun w => G.graph.Adj v w)
        \ attachSet G v x).erase q := by
      rw [hrseq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self s)
    have hrcomp := Finset.mem_of_mem_erase hrmem
    have hscomp := Finset.mem_of_mem_erase hsmem
    have hrq : r ≠ q := Finset.ne_of_mem_erase hrmem
    have hsq : s ≠ q := Finset.ne_of_mem_erase hsmem
    have htq : t ≠ q := by rintro rfl; exact hqA ht
    have htr : t ≠ r := by rintro rfl; exact (Finset.mem_sdiff.mp hrcomp).2 ht
    have hts : t ≠ s := by rintro rfl; exact (Finset.mem_sdiff.mp hscomp).2 ht
    -- two comp-pairs through q, each with ≥ 2 carriers
    have h2P1 : 2 ≤ (carriers G v {q, r}).card := by
      refine htwo {q, r} ?_ (Finset.card_pair hrq.symm)
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hq, hrcomp⟩
    have h2P2 : 2 ≤ (carriers G v {q, s}).card := by
      refine htwo {q, s} ?_ (Finset.card_pair hsq.symm)
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hq, hscomp⟩
    -- the three pairs are distinct
    have h12 : ({q, r} : Finset (Fin G.size)) ≠ {q, s} := by
      intro h
      have : r ∈ ({q, s} : Finset (Fin G.size)) := h ▸ Finset.mem_insert_of_mem
        (Finset.mem_singleton_self r)
      rcases Finset.mem_insert.mp this with h' | h'
      · exact hrq h'
      · exact hrs (Finset.mem_singleton.mp h')
    have h1M : ({q, r} : Finset (Fin G.size)) ≠ {q, t} := by
      intro h
      have : t ∈ ({q, r} : Finset (Fin G.size)) := by
        rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self t)
      rcases Finset.mem_insert.mp this with h' | h'
      · exact htq h'
      · exact htr (Finset.mem_singleton.mp h')
    have h2M : ({q, s} : Finset (Fin G.size)) ≠ {q, t} := by
      intro h
      have : t ∈ ({q, s} : Finset (Fin G.size)) := by
        rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self t)
      rcases Finset.mem_insert.mp this with h' | h'
      · exact htq h'
      · exact hts (Finset.mem_singleton.mp h')
    -- pack into the size-4 cover
    have hsub3 : carriers G v {q, r} ∪ carriers G v {q, s} ∪ carriers G v {q, t}
        ⊆ (shellSet G v).filter fun w => G.graph.Adj w q := by
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_ <;>
        exact hcov q hqNv _ (Finset.mem_insert_self q _)
    have hdM : Disjoint (carriers G v {q, r} ∪ carriers G v {q, s})
        (carriers G v {q, t}) :=
      Finset.disjoint_union_left.mpr ⟨carriers_disjoint h1M, carriers_disjoint h2M⟩
    have hle := Finset.card_le_card hsub3
    rw [Finset.card_union_of_disjoint hdM,
      Finset.card_union_of_disjoint (carriers_disjoint h12), ha4 q hqNv] at hle
    exact Finset.card_eq_zero.mp (by omega)
  -- final contradiction: a carrier of a mixed pair must exist
  have hcompne : ((Finset.univ.filter fun w => G.graph.Adj v w)
      \ attachSet G v x).Nonempty := by
    rw [← Finset.card_pos, hcomp3]; norm_num
  obtain ⟨q0, hq0⟩ := hcompne
  have hQ0card : (((Finset.univ.filter fun w => G.graph.Adj v w)
      \ attachSet G v x).erase q0).card = 2 := by
    rw [Finset.card_erase_of_mem hq0, hcomp3]
  have hQ0sub : ((Finset.univ.filter fun w => G.graph.Adj v w)
      \ attachSet G v x).erase q0
      ⊆ (Finset.univ.filter fun w => G.graph.Adj v w) \ attachSet G v x :=
    Finset.erase_subset _ _
  obtain ⟨z, hzk2, hzadj, hzA⟩ := local_carrier hTF hΔ hall hx hQ0sub hQ0card
  obtain ⟨t0, ht0⟩ : (attachSet G v x).Nonempty := by
    rw [← Finset.card_pos, hx2]; norm_num
  have ht0q0 : t0 ≠ q0 := by
    rintro rfl; exact (Finset.mem_sdiff.mp hq0).2 ht0
  have hQ'sub : ({t0, q0} : Finset (Fin G.size))
      ⊆ (Finset.univ.filter fun w => G.graph.Adj v w) \ attachSet G v z := by
    rw [hzA, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    constructor
    · rw [Finset.mem_sdiff]
      refine ⟨attachSet_subset_nbrs v x ht0, fun h => ?_⟩
      exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase h)).2 ht0
    · rw [Finset.mem_sdiff]
      exact ⟨(Finset.mem_sdiff.mp hq0).1, Finset.notMem_erase q0 _⟩
  obtain ⟨w, hwk2, hwadj, hwA⟩ := local_carrier hTF hΔ hall hzk2 hQ'sub
    (Finset.card_pair ht0q0)
  have hwmem : w ∈ carriers G v {q0, t0} := by
    refine mem_carriers.mpr ⟨(mem_kTwo.mp hwk2).1, ?_⟩
    rw [hwA]
    exact Finset.pair_comm t0 q0
  rw [hmixed q0 hq0 t0 ht0] at hwmem
  exact absurd hwmem (Finset.notMem_empty w)

/-- **Step C (Kneser forcing)**: for distinct `k = 2` shell vertices, adjacency is
    exactly disjointness of attachment pairs. With Step B this makes the shell the
    Kneser graph `K(5,2)` = Petersen, and the ball the Clebsch graph. -/
lemma adj_iff_attach_disjoint {v x y : Fin G.size} (hx : x ∈ kTwo G v)
    (hy : y ∈ kTwo G v) (_hne : x ≠ y) :
    G.graph.Adj x y ↔ Disjoint (attachSet G v x) (attachSet G v y) := by
  constructor
  · exact fun hadj => attachSet_disjoint hTF hadj
  · intro hdisj
    have hsub : attachSet G v y
        ⊆ (Finset.univ.filter fun w => G.graph.Adj v w) \ attachSet G v x := by
      intro a ha
      rw [Finset.mem_sdiff]
      exact ⟨attachSet_subset_nbrs v y ha, fun h => Finset.disjoint_right.mp hdisj ha h⟩
    obtain ⟨z, hzk2, hzadj, hzA⟩ := local_carrier hTF hΔ hall hx hsub
      (mem_kTwo.mp hy).2
    have hz : z = y := attach_injOn hTF hΔ hall z hzk2 y hy hzA
    exact hz ▸ hzadj

set_option maxHeartbeats 3200000 in
-- Raised budget: the explicit 16-vertex Clebsch embedding discharges many
-- per-vertex adjacency obligations by `decide`, which is heavy over `Fin G.size`.
/-- **Forward uniqueness**: in an all-60 graph, every vertex lies in a closed induced
    copy of the Clebsch graph — which is therefore its connected component. The
    embedding sends `0 ↦ v`, the generators `{1,2,4,8,15} ↦ N(v)`, and each XOR of two
    generators to the carrier of the corresponding attachment pair (reduction note
    §3.5, Step C + the folded-5-cube labelling). -/
theorem exists_clebsch_embedding (v : Fin G.size) :
    ∃ φ : Fin 16 → Fin G.size, Function.Injective φ ∧ φ 0 = v ∧
      (∀ i j, clebschGraph.Adj i j ↔ G.graph.Adj (φ i) (φ j)) ∧
      (∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u) := by
  obtain ⟨hdeg5, -, -, -, -, -⟩ := eq_sixty_structure hTF hΔ (hall v)
  -- enumerate the five neighbours of v
  set aF : Fin 5 → Fin G.size :=
    fun i => (Finset.univ.filter fun w => G.graph.Adj v w).orderEmbOfFin hdeg5 i
    with haFdef
  have haNv : ∀ i, aF i ∈ Finset.univ.filter fun w => G.graph.Adj v w :=
    fun i => Finset.orderEmbOfFin_mem _ hdeg5 i
  have hva : ∀ i, G.graph.Adj v (aF i) := fun i => (Finset.mem_filter.mp (haNv i)).2
  have haInj : Function.Injective aF := fun i j h =>
    (Finset.orderEmbOfFin _ hdeg5).injective h
  have haSurj : ∀ w, G.graph.Adj v w → ∃ i, aF i = w := by
    intro w hw
    have hmem : w ∈ Set.range ((Finset.univ.filter
        fun w => G.graph.Adj v w).orderEmbOfFin hdeg5) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩)
    exact hmem
  -- carriers of all ten pairs exist (injectivity + counting)
  have hk2card := kTwo_card hTF hΔ hall v
  have hsurj : ∀ P ∈ (Finset.univ.filter fun w => G.graph.Adj v w).powersetCard 2,
      ∃ x, ∃ _ : x ∈ kTwo G v, P = attachSet G v x := by
    refine Finset.surj_on_of_inj_on_of_card_le (fun x _ => attachSet G v x)
      (fun x hx => ?_)
      (fun x₁ x₂ hx₁ hx₂ h => attach_injOn hTF hΔ hall x₁ hx₁ x₂ hx₂ h) ?_
    · rw [Finset.mem_powersetCard]
      exact ⟨attachSet_subset_nbrs v x, (mem_kTwo.mp hx).2⟩
    · rw [Finset.card_powersetCard, hdeg5, hk2card]
      decide
  have hxex : ∀ i j : Fin 5, i ≠ j →
      ∃ x, x ∈ kTwo G v ∧ attachSet G v x = {aF i, aF j} := by
    intro i j hij
    have hmem : ({aF i, aF j} : Finset (Fin G.size))
        ∈ (Finset.univ.filter fun w => G.graph.Adj v w).powersetCard 2 := by
      rw [Finset.mem_powersetCard]
      constructor
      · rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨haNv i, haNv j⟩
      · exact Finset.card_pair fun he => hij (haInj he)
    obtain ⟨x, hx, hPx⟩ := hsurj _ hmem
    exact ⟨x, hx, hPx.symm⟩
  choose xF hxk2 hxA using hxex
  -- structural facts
  have hxsh : ∀ i j (h : i ≠ j), xF i j h ∈ shellSet G v :=
    fun i j h => (mem_kTwo.mp (hxk2 i j h)).1
  have hnvx : ∀ i j (h : i ≠ j), ¬G.graph.Adj v (xF i j h) :=
    fun i j h => (mem_shellSet.mp (hxsh i j h)).2
  have hxa1 : ∀ i j (h : i ≠ j), G.graph.Adj (xF i j h) (aF i) := by
    intro i j h
    have : aF i ∈ attachSet G v (xF i j h) := by
      rw [hxA]; exact Finset.mem_insert_self _ _
    exact (mem_attachSet.mp this).2
  have hxa2 : ∀ i j (h : i ≠ j), G.graph.Adj (xF i j h) (aF j) := by
    intro i j h
    have : aF j ∈ attachSet G v (xF i j h) := by
      rw [hxA]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact (mem_attachSet.mp this).2
  have hnaa : ∀ i j, i ≠ j → ¬G.graph.Adj (aF i) (aF j) :=
    fun i j _ hadj => hTF v (aF i) (aF j) (hva i) hadj (hva j)
  have hnax : ∀ i j k (h : j ≠ k), i ≠ j → i ≠ k →
      ¬G.graph.Adj (aF i) (xF j k h) := by
    intro i j k h hij hik hadj
    have hmem : aF i ∈ attachSet G v (xF j k h) :=
      mem_attachSet.mpr ⟨hva i, hadj.symm⟩
    rw [hxA] at hmem
    rcases Finset.mem_insert.mp hmem with he | he
    · exact hij (haInj he)
    · exact hik (haInj (Finset.mem_singleton.mp he))
  have hx_ne : ∀ i j k l (hij : i ≠ j) (hkl : k ≠ l),
      (i ≠ k ∨ j ≠ l) → (i ≠ l ∨ j ≠ k) → xF i j hij ≠ xF k l hkl := by
    intro i j k l hij hkl h1 h2 heq
    have hAeq : ({aF i, aF j} : Finset (Fin G.size)) = {aF k, aF l} := by
      rw [← hxA i j hij, ← hxA k l hkl, heq]
    have hi : aF i ∈ ({aF k, aF l} : Finset (Fin G.size)) := by
      rw [← hAeq]; exact Finset.mem_insert_self _ _
    have hj : aF j ∈ ({aF k, aF l} : Finset (Fin G.size)) := by
      rw [← hAeq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rcases Finset.mem_insert.mp hi with he | he
    · -- i = k, so j must be l
      have hik := haInj he
      rcases Finset.mem_insert.mp hj with hf | hf
      · exact hij (hik.trans (haInj hf).symm)
      · have hjl := haInj (Finset.mem_singleton.mp hf)
        rcases h1 with h | h
        · exact h hik
        · exact h hjl
    · -- i = l, so j must be k
      have hil := haInj (Finset.mem_singleton.mp he)
      rcases Finset.mem_insert.mp hj with hf | hf
      · have hjk := haInj hf
        rcases h2 with h | h
        · exact h hil
        · exact h hjk
      · exact hij (hil.trans (haInj (Finset.mem_singleton.mp hf)).symm)
  have hxx_adj : ∀ i j k l (hij : i ≠ j) (hkl : k ≠ l),
      i ≠ k → i ≠ l → j ≠ k → j ≠ l → G.graph.Adj (xF i j hij) (xF k l hkl) := by
    intro i j k l hij hkl hik hil hjk hjl
    refine (adj_iff_attach_disjoint hTF hΔ hall (hxk2 i j hij) (hxk2 k l hkl)
      (hx_ne i j k l hij hkl (Or.inl hik) (Or.inl hil))).mpr ?_
    rw [hxA, hxA, Finset.disjoint_left]
    intro a ha ha'
    rcases Finset.mem_insert.mp ha with he | he <;>
      rcases Finset.mem_insert.mp ha' with hf | hf
    · exact hik (haInj (he.symm.trans hf))
    · exact hil (haInj (he.symm.trans (Finset.mem_singleton.mp hf)))
    · exact hjk (haInj ((Finset.mem_singleton.mp he).symm.trans hf))
    · exact hjl (haInj ((Finset.mem_singleton.mp he).symm.trans
        (Finset.mem_singleton.mp hf)))
  have hnxx : ∀ i j k l (hij : i ≠ j) (hkl : k ≠ l),
      (i = k ∨ i = l ∨ j = k ∨ j = l) → ¬G.graph.Adj (xF i j hij) (xF k l hkl) := by
    intro i j k l hij hkl hshare hadj
    have hdisj := attachSet_disjoint hTF (v := v) hadj
    rw [hxA, hxA, Finset.disjoint_left] at hdisj
    rcases hshare with h | h | h | h
    · exact hdisj (Finset.mem_insert_self _ _) (h ▸ Finset.mem_insert_self _ _)
    · exact hdisj (Finset.mem_insert_self _ _)
        (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · exact hdisj (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        (h ▸ Finset.mem_insert_self _ _)
    · exact hdisj (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hv_ne_a : ∀ i, v ≠ aF i := by
    intro i heq
    exact G.graph.irrefl (heq ▸ hva i)
  have hx_ne_v : ∀ i j (h : i ≠ j), xF i j h ≠ v :=
    fun i j h => (mem_shellSet.mp (hxsh i j h)).1
  have hx_ne_a : ∀ i j k (h : i ≠ j), xF i j h ≠ aF k := by
    intro i j k h heq
    exact hnvx i j h (heq ▸ hva k)
  -- cardinality of explicit 5-element sets
  have hcard5 : ∀ a b c d e : Fin G.size, a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c →
      b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
      ({a, b, c, d, e} : Finset (Fin G.size)).card = 5 := by
    intro a b c d e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3, h4]),
      Finset.card_insert_of_notMem (by simp [h5, h6, h7]),
      Finset.card_insert_of_notMem (by simp [h8, h9]),
      Finset.card_insert_of_notMem (by simp [h10]),
      Finset.card_singleton]
  -- the closure helper: five known neighbours exhaust a degree-5 neighbourhood
  have hclosed5 : ∀ w : Fin G.size, ∀ s : Finset (Fin G.size), s.card = 5 →
      (∀ z ∈ s, G.graph.Adj w z) → ∀ u, G.graph.Adj w u → u ∈ s := by
    intro w s hcard hsub u hadj
    have hsubset : s ⊆ Finset.univ.filter (fun z => G.graph.Adj w z) := fun z hz =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ z, hsub z hz⟩
    have heq : s = Finset.univ.filter (fun z => G.graph.Adj w z) :=
      Finset.eq_of_subset_of_card_le hsubset
        (by rw [hcard]; exact deg_le_of_maxDegree_le hΔ w)
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hadj⟩
  -- the embedding
  refine ⟨![v, aF 0, aF 1, xF 0 1 (by decide), aF 2, xF 0 2 (by decide),
    xF 1 2 (by decide), xF 3 4 (by decide), aF 3, xF 0 3 (by decide),
    xF 1 3 (by decide), xF 2 4 (by decide), xF 2 3 (by decide), xF 1 4 (by decide),
    xF 0 4 (by decide), aF 4], ?_, rfl, ?_, ?_⟩
  · -- injectivity
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij (hv_ne_a 0)
    · exact absurd hij (hv_ne_a 1)
    · exact absurd hij (Ne.symm (hx_ne_v 0 1 (by decide)))
    · exact absurd hij (hv_ne_a 2)
    · exact absurd hij (Ne.symm (hx_ne_v 0 2 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_v 1 2 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_v 3 4 (by decide)))
    · exact absurd hij (hv_ne_a 3)
    · exact absurd hij (Ne.symm (hx_ne_v 0 3 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_v 1 3 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_v 2 4 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_v 2 3 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_v 1 4 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_v 0 4 (by decide)))
    · exact absurd hij (hv_ne_a 4)
    · exact absurd hij (Ne.symm (hv_ne_a 0))
    · rfl
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (Ne.symm (hx_ne_a 0 1 0 (by decide)))
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (Ne.symm (hx_ne_a 0 2 0 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 1 2 0 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 3 4 0 (by decide)))
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (Ne.symm (hx_ne_a 0 3 0 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 1 3 0 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 2 4 0 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 2 3 0 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 1 4 0 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 0 4 0 (by decide)))
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (Ne.symm (hv_ne_a 1))
    · exact absurd (haInj hij) (by decide)
    · rfl
    · exact absurd hij (Ne.symm (hx_ne_a 0 1 1 (by decide)))
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (Ne.symm (hx_ne_a 0 2 1 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 1 2 1 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 3 4 1 (by decide)))
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (Ne.symm (hx_ne_a 0 3 1 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 1 3 1 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 2 4 1 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 2 3 1 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 1 4 1 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 0 4 1 (by decide)))
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (hx_ne_v 0 1 (by decide))
    · exact absurd hij (hx_ne_a 0 1 0 (by decide))
    · exact absurd hij (hx_ne_a 0 1 1 (by decide))
    · rfl
    · exact absurd hij (hx_ne_a 0 1 2 (by decide))
    · exact absurd hij (hx_ne 0 1 0 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 1 1 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 1 3 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 0 1 3 (by decide))
    · exact absurd hij (hx_ne 0 1 0 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 1 1 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 1 2 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 1 2 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 1 1 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 1 0 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 0 1 4 (by decide))
    · exact absurd hij (Ne.symm (hv_ne_a 2))
    · exact absurd (haInj hij) (by decide)
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (Ne.symm (hx_ne_a 0 1 2 (by decide)))
    · rfl
    · exact absurd hij (Ne.symm (hx_ne_a 0 2 2 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 1 2 2 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 3 4 2 (by decide)))
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (Ne.symm (hx_ne_a 0 3 2 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 1 3 2 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 2 4 2 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 2 3 2 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 1 4 2 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 0 4 2 (by decide)))
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (hx_ne_v 0 2 (by decide))
    · exact absurd hij (hx_ne_a 0 2 0 (by decide))
    · exact absurd hij (hx_ne_a 0 2 1 (by decide))
    · exact absurd hij (hx_ne 0 2 0 1 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 0 2 2 (by decide))
    · rfl
    · exact absurd hij (hx_ne 0 2 1 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 2 3 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 0 2 3 (by decide))
    · exact absurd hij (hx_ne 0 2 0 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 2 1 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 2 2 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 2 2 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 2 1 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 2 0 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 0 2 4 (by decide))
    · exact absurd hij (hx_ne_v 1 2 (by decide))
    · exact absurd hij (hx_ne_a 1 2 0 (by decide))
    · exact absurd hij (hx_ne_a 1 2 1 (by decide))
    · exact absurd hij (hx_ne 1 2 0 1 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 1 2 2 (by decide))
    · exact absurd hij (hx_ne 1 2 0 2 (by decide) (by decide) (by decide) (by decide))
    · rfl
    · exact absurd hij (hx_ne 1 2 3 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 1 2 3 (by decide))
    · exact absurd hij (hx_ne 1 2 0 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 1 2 1 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 1 2 2 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 1 2 2 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 1 2 1 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 1 2 0 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 1 2 4 (by decide))
    · exact absurd hij (hx_ne_v 3 4 (by decide))
    · exact absurd hij (hx_ne_a 3 4 0 (by decide))
    · exact absurd hij (hx_ne_a 3 4 1 (by decide))
    · exact absurd hij (hx_ne 3 4 0 1 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 3 4 2 (by decide))
    · exact absurd hij (hx_ne 3 4 0 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 3 4 1 2 (by decide) (by decide) (by decide) (by decide))
    · rfl
    · exact absurd hij (hx_ne_a 3 4 3 (by decide))
    · exact absurd hij (hx_ne 3 4 0 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 3 4 1 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 3 4 2 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 3 4 2 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 3 4 1 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 3 4 0 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 3 4 4 (by decide))
    · exact absurd hij (Ne.symm (hv_ne_a 3))
    · exact absurd (haInj hij) (by decide)
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (Ne.symm (hx_ne_a 0 1 3 (by decide)))
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (Ne.symm (hx_ne_a 0 2 3 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 1 2 3 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 3 4 3 (by decide)))
    · rfl
    · exact absurd hij (Ne.symm (hx_ne_a 0 3 3 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 1 3 3 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 2 4 3 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 2 3 3 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 1 4 3 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 0 4 3 (by decide)))
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (hx_ne_v 0 3 (by decide))
    · exact absurd hij (hx_ne_a 0 3 0 (by decide))
    · exact absurd hij (hx_ne_a 0 3 1 (by decide))
    · exact absurd hij (hx_ne 0 3 0 1 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 0 3 2 (by decide))
    · exact absurd hij (hx_ne 0 3 0 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 3 1 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 3 3 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 0 3 3 (by decide))
    · rfl
    · exact absurd hij (hx_ne 0 3 1 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 3 2 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 3 2 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 3 1 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 3 0 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 0 3 4 (by decide))
    · exact absurd hij (hx_ne_v 1 3 (by decide))
    · exact absurd hij (hx_ne_a 1 3 0 (by decide))
    · exact absurd hij (hx_ne_a 1 3 1 (by decide))
    · exact absurd hij (hx_ne 1 3 0 1 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 1 3 2 (by decide))
    · exact absurd hij (hx_ne 1 3 0 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 1 3 1 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 1 3 3 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 1 3 3 (by decide))
    · exact absurd hij (hx_ne 1 3 0 3 (by decide) (by decide) (by decide) (by decide))
    · rfl
    · exact absurd hij (hx_ne 1 3 2 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 1 3 2 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 1 3 1 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 1 3 0 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 1 3 4 (by decide))
    · exact absurd hij (hx_ne_v 2 4 (by decide))
    · exact absurd hij (hx_ne_a 2 4 0 (by decide))
    · exact absurd hij (hx_ne_a 2 4 1 (by decide))
    · exact absurd hij (hx_ne 2 4 0 1 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 2 4 2 (by decide))
    · exact absurd hij (hx_ne 2 4 0 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 2 4 1 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 2 4 3 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 2 4 3 (by decide))
    · exact absurd hij (hx_ne 2 4 0 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 2 4 1 3 (by decide) (by decide) (by decide) (by decide))
    · rfl
    · exact absurd hij (hx_ne 2 4 2 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 2 4 1 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 2 4 0 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 2 4 4 (by decide))
    · exact absurd hij (hx_ne_v 2 3 (by decide))
    · exact absurd hij (hx_ne_a 2 3 0 (by decide))
    · exact absurd hij (hx_ne_a 2 3 1 (by decide))
    · exact absurd hij (hx_ne 2 3 0 1 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 2 3 2 (by decide))
    · exact absurd hij (hx_ne 2 3 0 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 2 3 1 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 2 3 3 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 2 3 3 (by decide))
    · exact absurd hij (hx_ne 2 3 0 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 2 3 1 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 2 3 2 4 (by decide) (by decide) (by decide) (by decide))
    · rfl
    · exact absurd hij (hx_ne 2 3 1 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 2 3 0 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 2 3 4 (by decide))
    · exact absurd hij (hx_ne_v 1 4 (by decide))
    · exact absurd hij (hx_ne_a 1 4 0 (by decide))
    · exact absurd hij (hx_ne_a 1 4 1 (by decide))
    · exact absurd hij (hx_ne 1 4 0 1 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 1 4 2 (by decide))
    · exact absurd hij (hx_ne 1 4 0 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 1 4 1 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 1 4 3 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 1 4 3 (by decide))
    · exact absurd hij (hx_ne 1 4 0 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 1 4 1 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 1 4 2 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 1 4 2 3 (by decide) (by decide) (by decide) (by decide))
    · rfl
    · exact absurd hij (hx_ne 1 4 0 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 1 4 4 (by decide))
    · exact absurd hij (hx_ne_v 0 4 (by decide))
    · exact absurd hij (hx_ne_a 0 4 0 (by decide))
    · exact absurd hij (hx_ne_a 0 4 1 (by decide))
    · exact absurd hij (hx_ne 0 4 0 1 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 0 4 2 (by decide))
    · exact absurd hij (hx_ne 0 4 0 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 4 1 2 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 4 3 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne_a 0 4 3 (by decide))
    · exact absurd hij (hx_ne 0 4 0 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 4 1 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 4 2 4 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 4 2 3 (by decide) (by decide) (by decide) (by decide))
    · exact absurd hij (hx_ne 0 4 1 4 (by decide) (by decide) (by decide) (by decide))
    · rfl
    · exact absurd hij (hx_ne_a 0 4 4 (by decide))
    · exact absurd hij (Ne.symm (hv_ne_a 4))
    · exact absurd (haInj hij) (by decide)
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (Ne.symm (hx_ne_a 0 1 4 (by decide)))
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (Ne.symm (hx_ne_a 0 2 4 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 1 2 4 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 3 4 4 (by decide)))
    · exact absurd (haInj hij) (by decide)
    · exact absurd hij (Ne.symm (hx_ne_a 0 3 4 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 1 3 4 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 2 4 4 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 2 3 4 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 1 4 4 (by decide)))
    · exact absurd hij (Ne.symm (hx_ne_a 0 4 4 (by decide)))
    · rfl
  · -- induced adjacency
    intro i j
    fin_cases i <;> fin_cases j
    · exact iff_of_false (by decide) G.graph.irrefl
    · exact iff_of_true (by decide) (hva 0)
    · exact iff_of_true (by decide) (hva 1)
    · exact iff_of_false (by decide) (hnvx 0 1 (by decide))
    · exact iff_of_true (by decide) (hva 2)
    · exact iff_of_false (by decide) (hnvx 0 2 (by decide))
    · exact iff_of_false (by decide) (hnvx 1 2 (by decide))
    · exact iff_of_false (by decide) (hnvx 3 4 (by decide))
    · exact iff_of_true (by decide) (hva 3)
    · exact iff_of_false (by decide) (hnvx 0 3 (by decide))
    · exact iff_of_false (by decide) (hnvx 1 3 (by decide))
    · exact iff_of_false (by decide) (hnvx 2 4 (by decide))
    · exact iff_of_false (by decide) (hnvx 2 3 (by decide))
    · exact iff_of_false (by decide) (hnvx 1 4 (by decide))
    · exact iff_of_false (by decide) (hnvx 0 4 (by decide))
    · exact iff_of_true (by decide) (hva 4)
    · exact iff_of_true (by decide) ((hva 0).symm)
    · exact iff_of_false (by decide) G.graph.irrefl
    · exact iff_of_false (by decide) (hnaa 0 1 (by decide))
    · exact iff_of_true (by decide) ((hxa1 0 1 (by decide)).symm)
    · exact iff_of_false (by decide) (hnaa 0 2 (by decide))
    · exact iff_of_true (by decide) ((hxa1 0 2 (by decide)).symm)
    · exact iff_of_false (by decide) (hnax 0 1 2 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnax 0 3 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnaa 0 3 (by decide))
    · exact iff_of_true (by decide) ((hxa1 0 3 (by decide)).symm)
    · exact iff_of_false (by decide) (hnax 0 1 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnax 0 2 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnax 0 2 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnax 0 1 4 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) ((hxa1 0 4 (by decide)).symm)
    · exact iff_of_false (by decide) (hnaa 0 4 (by decide))
    · exact iff_of_true (by decide) ((hva 1).symm)
    · exact iff_of_false (by decide) (hnaa 1 0 (by decide))
    · exact iff_of_false (by decide) G.graph.irrefl
    · exact iff_of_true (by decide) ((hxa2 0 1 (by decide)).symm)
    · exact iff_of_false (by decide) (hnaa 1 2 (by decide))
    · exact iff_of_false (by decide) (hnax 1 0 2 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) ((hxa1 1 2 (by decide)).symm)
    · exact iff_of_false (by decide) (hnax 1 3 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnaa 1 3 (by decide))
    · exact iff_of_false (by decide) (hnax 1 0 3 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) ((hxa1 1 3 (by decide)).symm)
    · exact iff_of_false (by decide) (hnax 1 2 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnax 1 2 3 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) ((hxa1 1 4 (by decide)).symm)
    · exact iff_of_false (by decide) (hnax 1 0 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnaa 1 4 (by decide))
    · exact iff_of_false (by decide) (fun h => hnvx 0 1 (by decide) h.symm)
    · exact iff_of_true (by decide) (hxa1 0 1 (by decide))
    · exact iff_of_true (by decide) (hxa2 0 1 (by decide))
    · exact iff_of_false (by decide) G.graph.irrefl
    · exact iff_of_false (by decide) (fun h => hnax 2 0 1 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (hnxx 0 1 0 2 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 0 1 1 2 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 0 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 3 0 1 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (hnxx 0 1 0 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 0 1 1 3 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 0 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 0 1 1 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 0 1 0 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 4 0 1 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_true (by decide) ((hva 2).symm)
    · exact iff_of_false (by decide) (hnaa 2 0 (by decide))
    · exact iff_of_false (by decide) (hnaa 2 1 (by decide))
    · exact iff_of_false (by decide) (hnax 2 0 1 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) G.graph.irrefl
    · exact iff_of_true (by decide) ((hxa2 0 2 (by decide)).symm)
    · exact iff_of_true (by decide) ((hxa2 1 2 (by decide)).symm)
    · exact iff_of_false (by decide) (hnax 2 3 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnaa 2 3 (by decide))
    · exact iff_of_false (by decide) (hnax 2 0 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnax 2 1 3 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) ((hxa1 2 4 (by decide)).symm)
    · exact iff_of_true (by decide) ((hxa1 2 3 (by decide)).symm)
    · exact iff_of_false (by decide) (hnax 2 1 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnax 2 0 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnaa 2 4 (by decide))
    · exact iff_of_false (by decide) (fun h => hnvx 0 2 (by decide) h.symm)
    · exact iff_of_true (by decide) (hxa1 0 2 (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 1 0 2 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (hnxx 0 2 0 1 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxa2 0 2 (by decide))
    · exact iff_of_false (by decide) G.graph.irrefl
    · exact iff_of_false (by decide) (hnxx 0 2 1 2 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 0 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 3 0 2 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (hnxx 0 2 0 3 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 0 2 2 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 0 2 2 3 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 0 2 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 0 2 0 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 4 0 2 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (fun h => hnvx 1 2 (by decide) h.symm)
    · exact iff_of_false (by decide) (fun h => hnax 0 1 2 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_true (by decide) (hxa1 1 2 (by decide))
    · exact iff_of_false (by decide) (hnxx 1 2 0 1 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxa2 1 2 (by decide))
    · exact iff_of_false (by decide) (hnxx 1 2 0 2 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) G.graph.irrefl
    · exact iff_of_true (by decide) (hxx_adj 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 3 1 2 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_true (by decide) (hxx_adj 1 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 1 2 1 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 1 2 2 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 1 2 2 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 1 2 1 4 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 1 2 0 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 4 1 2 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (fun h => hnvx 3 4 (by decide) h.symm)
    · exact iff_of_false (by decide) (fun h => hnax 0 3 4 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (fun h => hnax 1 3 4 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_true (by decide) (hxx_adj 3 4 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 2 3 4 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_true (by decide) (hxx_adj 3 4 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 3 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) G.graph.irrefl
    · exact iff_of_true (by decide) (hxa1 3 4 (by decide))
    · exact iff_of_false (by decide) (hnxx 3 4 0 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 3 4 1 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 3 4 2 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 3 4 2 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 3 4 1 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 3 4 0 4 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxa2 3 4 (by decide))
    · exact iff_of_true (by decide) ((hva 3).symm)
    · exact iff_of_false (by decide) (hnaa 3 0 (by decide))
    · exact iff_of_false (by decide) (hnaa 3 1 (by decide))
    · exact iff_of_false (by decide) (hnax 3 0 1 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnaa 3 2 (by decide))
    · exact iff_of_false (by decide) (hnax 3 0 2 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnax 3 1 2 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) ((hxa1 3 4 (by decide)).symm)
    · exact iff_of_false (by decide) G.graph.irrefl
    · exact iff_of_true (by decide) ((hxa2 0 3 (by decide)).symm)
    · exact iff_of_true (by decide) ((hxa2 1 3 (by decide)).symm)
    · exact iff_of_false (by decide) (hnax 3 2 4 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) ((hxa2 2 3 (by decide)).symm)
    · exact iff_of_false (by decide) (hnax 3 1 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnax 3 0 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnaa 3 4 (by decide))
    · exact iff_of_false (by decide) (fun h => hnvx 0 3 (by decide) h.symm)
    · exact iff_of_true (by decide) (hxa1 0 3 (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 1 0 3 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (hnxx 0 3 0 1 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 2 0 3 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (hnxx 0 3 0 2 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 0 3 3 4 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxa2 0 3 (by decide))
    · exact iff_of_false (by decide) G.graph.irrefl
    · exact iff_of_false (by decide) (hnxx 0 3 1 3 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 0 3 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 0 3 2 3 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 0 3 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 0 3 0 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 4 0 3 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (fun h => hnvx 1 3 (by decide) h.symm)
    · exact iff_of_false (by decide) (fun h => hnax 0 1 3 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_true (by decide) (hxa1 1 3 (by decide))
    · exact iff_of_false (by decide) (hnxx 1 3 0 1 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 2 1 3 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_true (by decide) (hxx_adj 1 3 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 1 3 1 2 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 1 3 3 4 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxa2 1 3 (by decide))
    · exact iff_of_false (by decide) (hnxx 1 3 0 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) G.graph.irrefl
    · exact iff_of_true (by decide) (hxx_adj 1 3 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 1 3 2 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 1 3 1 4 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 1 3 0 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 4 1 3 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (fun h => hnvx 2 4 (by decide) h.symm)
    · exact iff_of_false (by decide) (fun h => hnax 0 2 4 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (fun h => hnax 1 2 4 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_true (by decide) (hxx_adj 2 4 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxa1 2 4 (by decide))
    · exact iff_of_false (by decide) (hnxx 2 4 0 2 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 2 4 1 2 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 2 4 3 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 3 2 4 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_true (by decide) (hxx_adj 2 4 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 2 4 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) G.graph.irrefl
    · exact iff_of_false (by decide) (hnxx 2 4 2 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 2 4 1 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 2 4 0 4 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxa2 2 4 (by decide))
    · exact iff_of_false (by decide) (fun h => hnvx 2 3 (by decide) h.symm)
    · exact iff_of_false (by decide) (fun h => hnax 0 2 3 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (fun h => hnax 1 2 3 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_true (by decide) (hxx_adj 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxa1 2 3 (by decide))
    · exact iff_of_false (by decide) (hnxx 2 3 0 2 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 2 3 1 2 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 2 3 3 4 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxa2 2 3 (by decide))
    · exact iff_of_false (by decide) (hnxx 2 3 0 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 2 3 1 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 2 3 2 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) G.graph.irrefl
    · exact iff_of_true (by decide) (hxx_adj 2 3 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 2 3 0 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 4 2 3 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (fun h => hnvx 1 4 (by decide) h.symm)
    · exact iff_of_false (by decide) (fun h => hnax 0 1 4 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_true (by decide) (hxa1 1 4 (by decide))
    · exact iff_of_false (by decide) (hnxx 1 4 0 1 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 2 1 4 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_true (by decide) (hxx_adj 1 4 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 1 4 1 2 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 1 4 3 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 3 1 4 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_true (by decide) (hxx_adj 1 4 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 1 4 1 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 1 4 2 4 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 1 4 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) G.graph.irrefl
    · exact iff_of_false (by decide) (hnxx 1 4 0 4 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxa2 1 4 (by decide))
    · exact iff_of_false (by decide) (fun h => hnvx 0 4 (by decide) h.symm)
    · exact iff_of_true (by decide) (hxa1 0 4 (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 1 0 4 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (hnxx 0 4 0 1 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 2 0 4 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (hnxx 0 4 0 2 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 0 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 0 4 3 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (fun h => hnax 3 0 4 (by decide) (by decide) (by decide) h.symm)
    · exact iff_of_false (by decide) (hnxx 0 4 0 3 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 0 4 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 0 4 2 4 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) (hxx_adj 0 4 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnxx 0 4 1 4 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) G.graph.irrefl
    · exact iff_of_true (by decide) (hxa2 0 4 (by decide))
    · exact iff_of_true (by decide) ((hva 4).symm)
    · exact iff_of_false (by decide) (hnaa 4 0 (by decide))
    · exact iff_of_false (by decide) (hnaa 4 1 (by decide))
    · exact iff_of_false (by decide) (hnax 4 0 1 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnaa 4 2 (by decide))
    · exact iff_of_false (by decide) (hnax 4 0 2 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnax 4 1 2 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) ((hxa2 3 4 (by decide)).symm)
    · exact iff_of_false (by decide) (hnaa 4 3 (by decide))
    · exact iff_of_false (by decide) (hnax 4 0 3 (by decide) (by decide) (by decide))
    · exact iff_of_false (by decide) (hnax 4 1 3 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) ((hxa2 2 4 (by decide)).symm)
    · exact iff_of_false (by decide) (hnax 4 2 3 (by decide) (by decide) (by decide))
    · exact iff_of_true (by decide) ((hxa2 1 4 (by decide)).symm)
    · exact iff_of_true (by decide) ((hxa2 0 4 (by decide)).symm)
    · exact iff_of_false (by decide) G.graph.irrefl
  · -- closure
    intro i u hadj
    fin_cases i
    · -- v: its neighbours are the aF's
      obtain ⟨m, rfl⟩ := haSurj u hadj
      fin_cases m
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨8, rfl⟩
      · exact ⟨15, rfl⟩
    · have hu := hclosed5 (aF 0)
        {v, xF 0 1 (by decide), xF 0 2 (by decide), xF 0 3 (by decide), xF 0 4 (by decide)}
        (hcard5 (v) (xF 0 1 (by decide)) (xF 0 2 (by decide)) (xF 0 3 (by decide)) (xF 0 4 (by decide))
          (Ne.symm (hx_ne_v 0 1 (by decide))) (Ne.symm (hx_ne_v 0 2 (by decide))) (Ne.symm (hx_ne_v 0 3 (by decide))) (Ne.symm (hx_ne_v 0 4 (by decide)))
          (hx_ne 0 1 0 2 (by decide) (by decide) (by decide) (by decide)) (hx_ne 0 1 0 3 (by decide) (by decide) (by decide) (by decide)) (hx_ne 0 1 0 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 0 2 0 3 (by decide) (by decide) (by decide) (by decide)) (hx_ne 0 2 0 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 0 3 0 4 (by decide) (by decide) (by decide) (by decide)))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact (hva 0).symm
          · exact (hxa1 0 1 (by decide)).symm
          · exact (hxa1 0 2 (by decide)).symm
          · exact (hxa1 0 3 (by decide)).symm
          · exact (hxa1 0 4 (by decide)).symm
          ) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨9, rfl⟩
      · exact ⟨14, rfl⟩
    · have hu := hclosed5 (aF 1)
        {v, xF 0 1 (by decide), xF 1 2 (by decide), xF 1 3 (by decide), xF 1 4 (by decide)}
        (hcard5 (v) (xF 0 1 (by decide)) (xF 1 2 (by decide)) (xF 1 3 (by decide)) (xF 1 4 (by decide))
          (Ne.symm (hx_ne_v 0 1 (by decide))) (Ne.symm (hx_ne_v 1 2 (by decide))) (Ne.symm (hx_ne_v 1 3 (by decide))) (Ne.symm (hx_ne_v 1 4 (by decide)))
          (hx_ne 0 1 1 2 (by decide) (by decide) (by decide) (by decide)) (hx_ne 0 1 1 3 (by decide) (by decide) (by decide) (by decide)) (hx_ne 0 1 1 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 1 2 1 3 (by decide) (by decide) (by decide) (by decide)) (hx_ne 1 2 1 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 1 3 1 4 (by decide) (by decide) (by decide) (by decide)))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact (hva 1).symm
          · exact (hxa2 0 1 (by decide)).symm
          · exact (hxa1 1 2 (by decide)).symm
          · exact (hxa1 1 3 (by decide)).symm
          · exact (hxa1 1 4 (by decide)).symm
          ) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨6, rfl⟩
      · exact ⟨10, rfl⟩
      · exact ⟨13, rfl⟩
    · have hu := hclosed5 (xF 0 1 (by decide))
        {aF 0, aF 1, xF 2 3 (by decide), xF 2 4 (by decide), xF 3 4 (by decide)}
        (hcard5 (aF 0) (aF 1) (xF 2 3 (by decide)) (xF 2 4 (by decide)) (xF 3 4 (by decide))
          (fun he => absurd (haInj he) (by decide)) (Ne.symm (hx_ne_a 2 3 0 (by decide))) (Ne.symm (hx_ne_a 2 4 0 (by decide))) (Ne.symm (hx_ne_a 3 4 0 (by decide)))
          (Ne.symm (hx_ne_a 2 3 1 (by decide))) (Ne.symm (hx_ne_a 2 4 1 (by decide))) (Ne.symm (hx_ne_a 3 4 1 (by decide)))
          (hx_ne 2 3 2 4 (by decide) (by decide) (by decide) (by decide)) (hx_ne 2 3 3 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 2 4 3 4 (by decide) (by decide) (by decide) (by decide)))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact hxa1 0 1 (by decide)
          · exact hxa2 0 1 (by decide)
          · exact hxx_adj 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 0 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 0 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          ) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨12, rfl⟩
      · exact ⟨11, rfl⟩
      · exact ⟨7, rfl⟩
    · have hu := hclosed5 (aF 2)
        {v, xF 0 2 (by decide), xF 1 2 (by decide), xF 2 3 (by decide), xF 2 4 (by decide)}
        (hcard5 (v) (xF 0 2 (by decide)) (xF 1 2 (by decide)) (xF 2 3 (by decide)) (xF 2 4 (by decide))
          (Ne.symm (hx_ne_v 0 2 (by decide))) (Ne.symm (hx_ne_v 1 2 (by decide))) (Ne.symm (hx_ne_v 2 3 (by decide))) (Ne.symm (hx_ne_v 2 4 (by decide)))
          (hx_ne 0 2 1 2 (by decide) (by decide) (by decide) (by decide)) (hx_ne 0 2 2 3 (by decide) (by decide) (by decide) (by decide)) (hx_ne 0 2 2 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 1 2 2 3 (by decide) (by decide) (by decide) (by decide)) (hx_ne 1 2 2 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 2 3 2 4 (by decide) (by decide) (by decide) (by decide)))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact (hva 2).symm
          · exact (hxa2 0 2 (by decide)).symm
          · exact (hxa2 1 2 (by decide)).symm
          · exact (hxa1 2 3 (by decide)).symm
          · exact (hxa1 2 4 (by decide)).symm
          ) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨6, rfl⟩
      · exact ⟨12, rfl⟩
      · exact ⟨11, rfl⟩
    · have hu := hclosed5 (xF 0 2 (by decide))
        {aF 0, aF 2, xF 1 3 (by decide), xF 1 4 (by decide), xF 3 4 (by decide)}
        (hcard5 (aF 0) (aF 2) (xF 1 3 (by decide)) (xF 1 4 (by decide)) (xF 3 4 (by decide))
          (fun he => absurd (haInj he) (by decide)) (Ne.symm (hx_ne_a 1 3 0 (by decide))) (Ne.symm (hx_ne_a 1 4 0 (by decide))) (Ne.symm (hx_ne_a 3 4 0 (by decide)))
          (Ne.symm (hx_ne_a 1 3 2 (by decide))) (Ne.symm (hx_ne_a 1 4 2 (by decide))) (Ne.symm (hx_ne_a 3 4 2 (by decide)))
          (hx_ne 1 3 1 4 (by decide) (by decide) (by decide) (by decide)) (hx_ne 1 3 3 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 1 4 3 4 (by decide) (by decide) (by decide) (by decide)))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact hxa1 0 2 (by decide)
          · exact hxa2 0 2 (by decide)
          · exact hxx_adj 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 0 2 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 0 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          ) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨10, rfl⟩
      · exact ⟨13, rfl⟩
      · exact ⟨7, rfl⟩
    · have hu := hclosed5 (xF 1 2 (by decide))
        {aF 1, aF 2, xF 0 3 (by decide), xF 0 4 (by decide), xF 3 4 (by decide)}
        (hcard5 (aF 1) (aF 2) (xF 0 3 (by decide)) (xF 0 4 (by decide)) (xF 3 4 (by decide))
          (fun he => absurd (haInj he) (by decide)) (Ne.symm (hx_ne_a 0 3 1 (by decide))) (Ne.symm (hx_ne_a 0 4 1 (by decide))) (Ne.symm (hx_ne_a 3 4 1 (by decide)))
          (Ne.symm (hx_ne_a 0 3 2 (by decide))) (Ne.symm (hx_ne_a 0 4 2 (by decide))) (Ne.symm (hx_ne_a 3 4 2 (by decide)))
          (hx_ne 0 3 0 4 (by decide) (by decide) (by decide) (by decide)) (hx_ne 0 3 3 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 0 4 3 4 (by decide) (by decide) (by decide) (by decide)))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact hxa1 1 2 (by decide)
          · exact hxa2 1 2 (by decide)
          · exact hxx_adj 1 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 1 2 0 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          ) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨2, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨9, rfl⟩
      · exact ⟨14, rfl⟩
      · exact ⟨7, rfl⟩
    · have hu := hclosed5 (xF 3 4 (by decide))
        {aF 3, aF 4, xF 0 1 (by decide), xF 0 2 (by decide), xF 1 2 (by decide)}
        (hcard5 (aF 3) (aF 4) (xF 0 1 (by decide)) (xF 0 2 (by decide)) (xF 1 2 (by decide))
          (fun he => absurd (haInj he) (by decide)) (Ne.symm (hx_ne_a 0 1 3 (by decide))) (Ne.symm (hx_ne_a 0 2 3 (by decide))) (Ne.symm (hx_ne_a 1 2 3 (by decide)))
          (Ne.symm (hx_ne_a 0 1 4 (by decide))) (Ne.symm (hx_ne_a 0 2 4 (by decide))) (Ne.symm (hx_ne_a 1 2 4 (by decide)))
          (hx_ne 0 1 0 2 (by decide) (by decide) (by decide) (by decide)) (hx_ne 0 1 1 2 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 0 2 1 2 (by decide) (by decide) (by decide) (by decide)))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact hxa1 3 4 (by decide)
          · exact hxa2 3 4 (by decide)
          · exact hxx_adj 3 4 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 3 4 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 3 4 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          ) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨8, rfl⟩
      · exact ⟨15, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨6, rfl⟩
    · have hu := hclosed5 (aF 3)
        {v, xF 0 3 (by decide), xF 1 3 (by decide), xF 2 3 (by decide), xF 3 4 (by decide)}
        (hcard5 (v) (xF 0 3 (by decide)) (xF 1 3 (by decide)) (xF 2 3 (by decide)) (xF 3 4 (by decide))
          (Ne.symm (hx_ne_v 0 3 (by decide))) (Ne.symm (hx_ne_v 1 3 (by decide))) (Ne.symm (hx_ne_v 2 3 (by decide))) (Ne.symm (hx_ne_v 3 4 (by decide)))
          (hx_ne 0 3 1 3 (by decide) (by decide) (by decide) (by decide)) (hx_ne 0 3 2 3 (by decide) (by decide) (by decide) (by decide)) (hx_ne 0 3 3 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 1 3 2 3 (by decide) (by decide) (by decide) (by decide)) (hx_ne 1 3 3 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 2 3 3 4 (by decide) (by decide) (by decide) (by decide)))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact (hva 3).symm
          · exact (hxa2 0 3 (by decide)).symm
          · exact (hxa2 1 3 (by decide)).symm
          · exact (hxa2 2 3 (by decide)).symm
          · exact (hxa1 3 4 (by decide)).symm
          ) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨9, rfl⟩
      · exact ⟨10, rfl⟩
      · exact ⟨12, rfl⟩
      · exact ⟨7, rfl⟩
    · have hu := hclosed5 (xF 0 3 (by decide))
        {aF 0, aF 3, xF 1 2 (by decide), xF 1 4 (by decide), xF 2 4 (by decide)}
        (hcard5 (aF 0) (aF 3) (xF 1 2 (by decide)) (xF 1 4 (by decide)) (xF 2 4 (by decide))
          (fun he => absurd (haInj he) (by decide)) (Ne.symm (hx_ne_a 1 2 0 (by decide))) (Ne.symm (hx_ne_a 1 4 0 (by decide))) (Ne.symm (hx_ne_a 2 4 0 (by decide)))
          (Ne.symm (hx_ne_a 1 2 3 (by decide))) (Ne.symm (hx_ne_a 1 4 3 (by decide))) (Ne.symm (hx_ne_a 2 4 3 (by decide)))
          (hx_ne 1 2 1 4 (by decide) (by decide) (by decide) (by decide)) (hx_ne 1 2 2 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 1 4 2 4 (by decide) (by decide) (by decide) (by decide)))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact hxa1 0 3 (by decide)
          · exact hxa2 0 3 (by decide)
          · exact hxx_adj 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 0 3 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 0 3 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          ) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨8, rfl⟩
      · exact ⟨6, rfl⟩
      · exact ⟨13, rfl⟩
      · exact ⟨11, rfl⟩
    · have hu := hclosed5 (xF 1 3 (by decide))
        {aF 1, aF 3, xF 0 2 (by decide), xF 0 4 (by decide), xF 2 4 (by decide)}
        (hcard5 (aF 1) (aF 3) (xF 0 2 (by decide)) (xF 0 4 (by decide)) (xF 2 4 (by decide))
          (fun he => absurd (haInj he) (by decide)) (Ne.symm (hx_ne_a 0 2 1 (by decide))) (Ne.symm (hx_ne_a 0 4 1 (by decide))) (Ne.symm (hx_ne_a 2 4 1 (by decide)))
          (Ne.symm (hx_ne_a 0 2 3 (by decide))) (Ne.symm (hx_ne_a 0 4 3 (by decide))) (Ne.symm (hx_ne_a 2 4 3 (by decide)))
          (hx_ne 0 2 0 4 (by decide) (by decide) (by decide) (by decide)) (hx_ne 0 2 2 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 0 4 2 4 (by decide) (by decide) (by decide) (by decide)))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact hxa1 1 3 (by decide)
          · exact hxa2 1 3 (by decide)
          · exact hxx_adj 1 3 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 1 3 0 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 1 3 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          ) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨2, rfl⟩
      · exact ⟨8, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨14, rfl⟩
      · exact ⟨11, rfl⟩
    · have hu := hclosed5 (xF 2 4 (by decide))
        {aF 2, aF 4, xF 0 1 (by decide), xF 0 3 (by decide), xF 1 3 (by decide)}
        (hcard5 (aF 2) (aF 4) (xF 0 1 (by decide)) (xF 0 3 (by decide)) (xF 1 3 (by decide))
          (fun he => absurd (haInj he) (by decide)) (Ne.symm (hx_ne_a 0 1 2 (by decide))) (Ne.symm (hx_ne_a 0 3 2 (by decide))) (Ne.symm (hx_ne_a 1 3 2 (by decide)))
          (Ne.symm (hx_ne_a 0 1 4 (by decide))) (Ne.symm (hx_ne_a 0 3 4 (by decide))) (Ne.symm (hx_ne_a 1 3 4 (by decide)))
          (hx_ne 0 1 0 3 (by decide) (by decide) (by decide) (by decide)) (hx_ne 0 1 1 3 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 0 3 1 3 (by decide) (by decide) (by decide) (by decide)))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact hxa1 2 4 (by decide)
          · exact hxa2 2 4 (by decide)
          · exact hxx_adj 2 4 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 2 4 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 2 4 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          ) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨4, rfl⟩
      · exact ⟨15, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨9, rfl⟩
      · exact ⟨10, rfl⟩
    · have hu := hclosed5 (xF 2 3 (by decide))
        {aF 2, aF 3, xF 0 1 (by decide), xF 0 4 (by decide), xF 1 4 (by decide)}
        (hcard5 (aF 2) (aF 3) (xF 0 1 (by decide)) (xF 0 4 (by decide)) (xF 1 4 (by decide))
          (fun he => absurd (haInj he) (by decide)) (Ne.symm (hx_ne_a 0 1 2 (by decide))) (Ne.symm (hx_ne_a 0 4 2 (by decide))) (Ne.symm (hx_ne_a 1 4 2 (by decide)))
          (Ne.symm (hx_ne_a 0 1 3 (by decide))) (Ne.symm (hx_ne_a 0 4 3 (by decide))) (Ne.symm (hx_ne_a 1 4 3 (by decide)))
          (hx_ne 0 1 0 4 (by decide) (by decide) (by decide) (by decide)) (hx_ne 0 1 1 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 0 4 1 4 (by decide) (by decide) (by decide) (by decide)))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact hxa1 2 3 (by decide)
          · exact hxa2 2 3 (by decide)
          · exact hxx_adj 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 2 3 0 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 2 3 1 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          ) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨4, rfl⟩
      · exact ⟨8, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨14, rfl⟩
      · exact ⟨13, rfl⟩
    · have hu := hclosed5 (xF 1 4 (by decide))
        {aF 1, aF 4, xF 0 2 (by decide), xF 0 3 (by decide), xF 2 3 (by decide)}
        (hcard5 (aF 1) (aF 4) (xF 0 2 (by decide)) (xF 0 3 (by decide)) (xF 2 3 (by decide))
          (fun he => absurd (haInj he) (by decide)) (Ne.symm (hx_ne_a 0 2 1 (by decide))) (Ne.symm (hx_ne_a 0 3 1 (by decide))) (Ne.symm (hx_ne_a 2 3 1 (by decide)))
          (Ne.symm (hx_ne_a 0 2 4 (by decide))) (Ne.symm (hx_ne_a 0 3 4 (by decide))) (Ne.symm (hx_ne_a 2 3 4 (by decide)))
          (hx_ne 0 2 0 3 (by decide) (by decide) (by decide) (by decide)) (hx_ne 0 2 2 3 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 0 3 2 3 (by decide) (by decide) (by decide) (by decide)))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact hxa1 1 4 (by decide)
          · exact hxa2 1 4 (by decide)
          · exact hxx_adj 1 4 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 1 4 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · exact hxx_adj 1 4 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          ) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨2, rfl⟩
      · exact ⟨15, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨9, rfl⟩
      · exact ⟨12, rfl⟩
    · have hu := hclosed5 (xF 0 4 (by decide))
        {aF 0, aF 4, xF 1 2 (by decide), xF 1 3 (by decide), xF 2 3 (by decide)}
        (hcard5 (aF 0) (aF 4) (xF 1 2 (by decide)) (xF 1 3 (by decide)) (xF 2 3 (by decide))
          (fun he => absurd (haInj he) (by decide)) (Ne.symm (hx_ne_a 1 2 0 (by decide))) (Ne.symm (hx_ne_a 1 3 0 (by decide))) (Ne.symm (hx_ne_a 2 3 0 (by decide)))
          (Ne.symm (hx_ne_a 1 2 4 (by decide))) (Ne.symm (hx_ne_a 1 3 4 (by decide))) (Ne.symm (hx_ne_a 2 3 4 (by decide)))
          (hx_ne 1 2 1 3 (by decide) (by decide) (by decide) (by decide)) (hx_ne 1 2 2 3 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 1 3 2 3 (by decide) (by decide) (by decide) (by decide)))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact hxa1 0 4 (by decide)
          · exact hxa2 0 4 (by decide)
          · exact hxx_adj 0 4 1 2 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide)
          · exact hxx_adj 0 4 1 3 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide)
          · exact hxx_adj 0 4 2 3 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide)
          ) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨15, rfl⟩
      · exact ⟨6, rfl⟩
      · exact ⟨10, rfl⟩
      · exact ⟨12, rfl⟩
    · have hu := hclosed5 (aF 4)
        {v, xF 0 4 (by decide), xF 1 4 (by decide), xF 2 4 (by decide), xF 3 4 (by decide)}
        (hcard5 (v) (xF 0 4 (by decide)) (xF 1 4 (by decide)) (xF 2 4 (by decide))
          (xF 3 4 (by decide))
          (Ne.symm (hx_ne_v 0 4 (by decide))) (Ne.symm (hx_ne_v 1 4 (by decide)))
          (Ne.symm (hx_ne_v 2 4 (by decide))) (Ne.symm (hx_ne_v 3 4 (by decide)))
          (hx_ne 0 4 1 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 0 4 2 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 0 4 3 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 1 4 2 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 1 4 3 4 (by decide) (by decide) (by decide) (by decide))
          (hx_ne 2 4 3 4 (by decide) (by decide) (by decide) (by decide)))
        (by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl | rfl | rfl
          · exact (hva 4).symm
          · exact (hxa2 0 4 (by decide)).symm
          · exact (hxa2 1 4 (by decide)).symm
          · exact (hxa2 2 4 (by decide)).symm
          · exact (hxa2 3 4 (by decide)).symm
          ) u hadj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨14, rfl⟩
      · exact ⟨13, rfl⟩
      · exact ⟨11, rfl⟩
      · exact ⟨7, rfl⟩

end AllSixtyB

end PentagonLocal

/-- **Pentagon transfer**: a closed induced injective map preserves the pentagon count
    through a vertex. Pentagons are connected, so closure keeps them inside the image,
    and induced-ness transports them both ways. -/
lemma pentagonCountAt_transfer {H G : Flag emptyType} (φ : Fin H.size → Fin G.size)
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (i₀ : Fin H.size) :
    pentagonCountAt G (φ i₀) = pentagonCountAt H i₀ := by
  classical
  rw [pentagonCountAt, pentagonCountAt]
  refine (Finset.card_bij (fun S _ => S.image φ) ?_ ?_ ?_).symm
  · -- pentagons through i₀ push forward
    intro S hS
    rw [Finset.mem_filter] at hS ⊢
    obtain ⟨-, ⟨f, finj, fimg, fadj⟩, hi₀⟩ := hS
    refine ⟨Finset.mem_univ _, ⟨φ ∘ f, hinj.comp finj, ?_, ?_⟩, ?_⟩
    · change Finset.image (φ ∘ f) Finset.univ = Finset.image φ S
      rw [← Finset.image_image, fimg]
    · intro a b
      rw [fadj a b, hiff (f a) (f b)]
      rfl
    · exact Finset.mem_image_of_mem φ hi₀
  · -- injectivity on subsets
    intro S₁ h₁ S₂ h₂ heq
    exact Finset.image_injective hinj heq
  · -- pentagons through φ i₀ pull back
    intro T hT
    rw [Finset.mem_filter] at hT
    obtain ⟨-, ⟨f, finj, fimg, fadj⟩, hmem⟩ := hT
    -- locate φ i₀ on the cycle
    have hi₀T : φ i₀ ∈ Finset.image f Finset.univ := fimg ▸ hmem
    obtain ⟨m₀, -, hm₀⟩ := Finset.mem_image.mp hi₀T
    -- cycle adjacency facts
    have cA : ∀ j : Fin 5, cycleGraph5.Adj j (j + 1) := by decide
    have cB : ∀ j : Fin 5, cycleGraph5.Adj (j + 1) (j + 2) := by decide
    have cD : ∀ j : Fin 5, cycleGraph5.Adj (j + 3) (j + 4) := by decide
    have cE : ∀ j : Fin 5, cycleGraph5.Adj j (j + 4) := by decide
    -- walk the cycle: every pentagon vertex is in the image of φ
    have h0 : ∃ j, φ j = f m₀ := ⟨i₀, hm₀.symm⟩
    have hstep : ∀ a b : Fin 5, cycleGraph5.Adj a b → (∃ j, φ j = f a) →
        ∃ j, φ j = f b := by
      rintro a b hab ⟨j, hj⟩
      exact hclosed j (f b) (by rw [hj]; exact (fadj a b).mp hab)
    have h1 : ∃ j, φ j = f (m₀ + 1) := hstep _ _ (cA m₀) h0
    have h2 : ∃ j, φ j = f (m₀ + 2) := hstep _ _ (cB m₀) h1
    have h4 : ∃ j, φ j = f (m₀ + 4) := hstep _ _ (cE m₀) h0
    have h3 : ∃ j, φ j = f (m₀ + 3) := by
      rcases h4 with ⟨j, hj⟩
      exact hclosed j (f (m₀ + 3)) (by rw [hj]; exact ((fadj _ _).mp (cD m₀)).symm)
    have hoffs : ∀ k : Fin 5, ∃ j, φ j = f (m₀ + k) := by
      intro k
      fin_cases k
      · simpa using h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    have hcover : ∀ m' m : Fin 5, ∃ k : Fin 5, m' + k = m := by decide
    have hrange : ∀ m : Fin 5, ∃ j, φ j = f m := by
      intro m
      obtain ⟨k, hk⟩ := hcover m₀ m
      exact hk ▸ hoffs k
    choose g hg using hrange
    have ginj : Function.Injective g := by
      intro m₁ m₂ h
      exact finj (by rw [← hg m₁, ← hg m₂, h])
    refine ⟨Finset.image g Finset.univ, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨g, ginj, rfl, ?_⟩, ?_⟩, ?_⟩
    · intro a b
      rw [fadj a b, ← hg a, ← hg b]
      exact (hiff (g a) (g b)).symm
    · -- i₀ lands in the preimage
      have : φ (g m₀) = φ i₀ := by rw [hg m₀, hm₀]
      have hgm₀ : g m₀ = i₀ := hinj this
      exact hgm₀ ▸ Finset.mem_image_of_mem g (Finset.mem_univ m₀)
    · -- the image recovers T
      change Finset.image φ (Finset.image g Finset.univ) = T
      rw [Finset.image_image, ← fimg]
      refine Finset.image_congr ?_
      intro m _
      exact hg m

/-- **Averaging equality**: a TF graph with `Δ ≤ 5` attaining `P = 12·|G|` has exactly
    60 pentagons through every vertex. -/
theorem pentagonCountAt_eq_sixty_of_extremal (G : Flag emptyType)
    (hTF : IsTriangleFree G) (hdeg : maxDegree G ≤ 5)
    (hext : pentagonCount G = 12 * G.size) :
    ∀ v : Fin G.size, pentagonCountAt G v = 60 := by
  intro v
  by_contra hne
  have hub := fun u => pentagonCountAt_le_sixty_of_maxDegree_le_five G hTF hdeg u
  have hlt : pentagonCountAt G v < 60 := lt_of_le_of_ne (hub v) hne
  have hstrict : ∑ u : Fin G.size, pentagonCountAt G u < ∑ _u : Fin G.size, 60 :=
    Finset.sum_lt_sum (fun u _ => hub u) ⟨v, Finset.mem_univ v, hlt⟩
  rw [sum_pentagonCountAt_eq_five_mul, hext, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hstrict
  omega

/-- **Uniqueness of the Δ ≤ 5 pentagon extremum (forward direction)**: a triangle-free
    graph with maximum degree at most 5 attaining `P = 12·|G|` is a disjoint union of
    Clebsch graphs — every vertex lies in a closed induced copy of the Clebsch graph,
    which is therefore its connected component. Equality analysis + structure forcing,
    the development notes §3.5; tightness witness:
    `clebsch_attains_delta5_bound`. -/
theorem pentagon_delta5_extremal_clebsch (G : Flag emptyType) (hTF : IsTriangleFree G)
    (hdeg : maxDegree G ≤ 5) (hext : pentagonCount G = 12 * G.size) :
    ∀ v : Fin G.size, ∃ φ : Fin 16 → Fin G.size, Function.Injective φ ∧ φ 0 = v ∧
      (∀ i j, clebschGraph.Adj i j ↔ G.graph.Adj (φ i) (φ j)) ∧
      (∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u) :=
  fun v => PentagonLocal.exists_clebsch_embedding hTF hdeg
    (pentagonCountAt_eq_sixty_of_extremal G hTF hdeg hext) v



/-- The 60 pentagons through vertex `0` of the Clebsch graph, listed explicitly
    (cycle order `0–a–x–y–b–0`; generated and cross-verified computationally). -/
def clebschPentagonsAtZero : Finset (Finset (Fin 16)) :=
  {{0, 1, 9, 13, 2},
   {0, 1, 9, 6, 2},
   {0, 1, 5, 10, 2},
   {0, 1, 5, 13, 2},
   {0, 1, 14, 10, 2},
   {0, 1, 14, 6, 2},
   {0, 1, 9, 11, 4},
   {0, 1, 9, 6, 4},
   {0, 1, 3, 11, 4},
   {0, 1, 3, 12, 4},
   {0, 1, 14, 12, 4},
   {0, 1, 14, 6, 4},
   {0, 1, 3, 12, 8},
   {0, 1, 3, 7, 8},
   {0, 1, 5, 10, 8},
   {0, 1, 5, 7, 8},
   {0, 1, 14, 10, 8},
   {0, 1, 14, 12, 8},
   {0, 1, 9, 11, 15},
   {0, 1, 9, 13, 15},
   {0, 1, 3, 11, 15},
   {0, 1, 3, 7, 15},
   {0, 1, 5, 13, 15},
   {0, 1, 5, 7, 15},
   {0, 2, 10, 11, 4},
   {0, 2, 10, 5, 4},
   {0, 2, 3, 11, 4},
   {0, 2, 3, 12, 4},
   {0, 2, 13, 12, 4},
   {0, 2, 13, 5, 4},
   {0, 2, 3, 12, 8},
   {0, 2, 3, 7, 8},
   {0, 2, 13, 9, 8},
   {0, 2, 13, 12, 8},
   {0, 2, 6, 9, 8},
   {0, 2, 6, 7, 8},
   {0, 2, 10, 11, 15},
   {0, 2, 10, 14, 15},
   {0, 2, 3, 11, 15},
   {0, 2, 3, 7, 15},
   {0, 2, 6, 14, 15},
   {0, 2, 6, 7, 15},
   {0, 4, 11, 9, 8},
   {0, 4, 11, 10, 8},
   {0, 4, 5, 10, 8},
   {0, 4, 5, 7, 8},
   {0, 4, 6, 9, 8},
   {0, 4, 6, 7, 8},
   {0, 4, 12, 13, 15},
   {0, 4, 12, 14, 15},
   {0, 4, 5, 13, 15},
   {0, 4, 5, 7, 15},
   {0, 4, 6, 14, 15},
   {0, 4, 6, 7, 15},
   {0, 8, 9, 11, 15},
   {0, 8, 9, 13, 15},
   {0, 8, 10, 11, 15},
   {0, 8, 10, 14, 15},
   {0, 8, 12, 13, 15},
   {0, 8, 12, 14, 15}}

set_option maxRecDepth 8000 in
lemma clebschPentagonsAtZero_card : clebschPentagonsAtZero.card = 60 := by decide

open scoped Classical in
set_option maxHeartbeats 1600000 in
-- 60 explicit pentagon witnesses, each discharged by `decide`; the kernel
-- reduction of `IsPentagon` over `Fin 16` is heavy, so the default budget is raised.
set_option maxRecDepth 8000 in
lemma clebschPentagonsAtZero_sub : clebschPentagonsAtZero ⊆
    Finset.univ.filter fun S => IsPentagon clebschFlag S ∧ (0 : Fin 16) ∈ S := by
  intro S hS
  simp only [clebschPentagonsAtZero, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 9, 13, 2] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 9, 6, 2] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 5, 10, 2] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 5, 13, 2] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 14, 10, 2] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 14, 6, 2] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 9, 11, 4] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 9, 6, 4] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 3, 11, 4] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 3, 12, 4] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 14, 12, 4] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 14, 6, 4] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 3, 12, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 3, 7, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 5, 10, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 5, 7, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 14, 10, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 14, 12, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 9, 11, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 9, 13, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 3, 11, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 3, 7, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 5, 13, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 1, 5, 7, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 10, 11, 4] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 10, 5, 4] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 3, 11, 4] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 3, 12, 4] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 13, 12, 4] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 13, 5, 4] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 3, 12, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 3, 7, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 13, 9, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 13, 12, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 6, 9, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 6, 7, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 10, 11, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 10, 14, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 3, 11, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 3, 7, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 6, 14, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 2, 6, 7, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 4, 11, 9, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 4, 11, 10, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 4, 5, 10, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 4, 5, 7, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 4, 6, 9, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 4, 6, 7, 8] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 4, 12, 13, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 4, 12, 14, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 4, 5, 13, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 4, 5, 7, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 4, 6, 14, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 4, 6, 7, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 8, 9, 11, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 8, 9, 13, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 8, 10, 11, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 8, 10, 14, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 8, 12, 13, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨(![0, 8, 12, 14, 15] : Fin 5 → Fin 16), by decide, by decide, by decide⟩, by decide⟩

/-- Triangle-freeness of Clebsch, by kernel `decide` (no compiler axioms). -/
lemma clebschFlag_triangleFree : IsTriangleFree clebschFlag := by
  unfold IsTriangleFree
  decide

/-- Degree bound for Clebsch, by kernel `decide` after an instance swap. -/
lemma clebschFlag_maxDegree_le : maxDegree clebschFlag ≤ 5 := by
  rw [maxDegree]
  refine Finset.sup_le fun v _ => ?_
  rw [Finset.filter_congr_decidable]
  revert v
  decide

/-- XOR-translation of the Clebsch graph's vertex set (an automorphism). -/
def clebschTranslate (a : Fin 16) (u : Fin 16) : Fin 16 :=
  ⟨Nat.xor u.val a.val % 16, Nat.mod_lt _ (by norm_num)⟩

/-- Every Clebsch vertex lies on exactly 60 pentagons: translations act transitively,
    the per-vertex bound caps the count at 60, and the explicit list
    `clebschPentagonsAtZero` attains it — no compiler axioms involved. -/
lemma clebsch_pentagonCountAt (w : Fin 16) :
    pentagonCountAt clebschFlag w = 60 := by
  have hinj : ∀ a : Fin 16, Function.Injective (clebschTranslate a) := by
    intro a u₁ u₂ h
    revert h
    revert u₁ u₂
    revert a
    decide
  have hiff : ∀ a i j : Fin 16, clebschGraph.Adj i j ↔
      clebschGraph.Adj (clebschTranslate a i) (clebschTranslate a j) := by decide
  have hinvol : ∀ a u : Fin 16, clebschTranslate a (clebschTranslate a u) = u := by decide
  have htr0 : ∀ a : Fin 16, clebschTranslate a 0 = a := by decide
  have hconst : ∀ a : Fin 16, pentagonCountAt clebschFlag a
      = pentagonCountAt clebschFlag (0 : Fin 16) := by
    intro a
    have ht := pentagonCountAt_transfer (H := clebschFlag) (G := clebschFlag)
      (clebschTranslate a) (hinj a) (hiff a)
      (fun _ u _ => ⟨clebschTranslate a u, hinvol a u⟩) (0 : Fin 16)
    exact htr0 a ▸ ht
  rw [hconst w]
  refine le_antisymm
    (pentagonCountAt_le_sixty_of_maxDegree_le_five clebschFlag clebschFlag_triangleFree
      clebschFlag_maxDegree_le (0 : Fin 16)) ?_
  rw [pentagonCountAt]
  calc (60 : ℕ) = clebschPentagonsAtZero.card := clebschPentagonsAtZero_card.symm
    _ ≤ _ := Finset.card_le_card clebschPentagonsAtZero_sub

/-- The Clebsch pentagon count, on standard axioms only (the former `native_decide`
    proxy-bridge proof was removed as redundant): `16 · 60 = 5 · 192` by averaging. -/
theorem clebsch_pentagonCount_pure : pentagonCount clebschFlag = 192 := by
  have hsum := sum_pentagonCountAt_eq_five_mul clebschFlag
  rw [Finset.sum_congr rfl (fun a _ => clebsch_pentagonCountAt a), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-- **Clebsch blow-up tightness**: There exist triangle-free graphs G with
    arbitrarily large Δ(G) such that `P(G) * 625 = |G| * Δ(G)^4 * 12`, i.e.,
    the conjectural extremum ratio `12/625` is attained.

    The witnessing family is the k-blow-up of the Clebsch graph for k chosen
    so that `5k ≥ D₀`. -/
theorem clebsch_blowup_tight :
    ∀ D₀ : ℕ, ∃ G : Flag emptyType,
      IsTriangleFree G ∧ D₀ ≤ maxDegree G ∧
      pentagonCount G * 625 = G.size * maxDegree G ^ 4 * 12 := by
  intro D₀
  set k := D₀ + 1
  have hk : 0 < k := Nat.succ_pos D₀
  refine ⟨blowupFlag clebschFlag k hk, ?_, ?_, ?_⟩
  · exact blowup_triangle_free _ clebsch_triangleFree k hk
  · -- maxDegree (blowupFlag clebschFlag k hk) ≥ k * maxDegree clebschFlag = 5k ≥ D₀
    calc D₀ ≤ 5 * k := by omega
      _ = k * 5 := Nat.mul_comm _ _
      _ = k * maxDegree clebschFlag := by rw [clebsch_maxDegree]
      _ ≤ maxDegree (blowupFlag clebschFlag k hk) :=
          blowup_maxDegree_lb _ k hk
  · -- maxDegree exact = 5k; pentagonCount exact = 192 k^5; size = 16k
    have hmaxdeg : maxDegree (blowupFlag clebschFlag k hk) = 5 * k := by
      apply le_antisymm
      · calc maxDegree (blowupFlag clebschFlag k hk)
            ≤ k * maxDegree clebschFlag :=
              blowup_maxDegree_ub _ k hk
          _ = k * 5 := by rw [clebsch_maxDegree]
          _ = 5 * k := Nat.mul_comm _ _
      · calc 5 * k = k * 5 := Nat.mul_comm _ _
          _ = k * maxDegree clebschFlag := by rw [clebsch_maxDegree]
          _ ≤ maxDegree (blowupFlag clebschFlag k hk) :=
              blowup_maxDegree_lb _ k hk
    rw [hmaxdeg, blowupFlag_size, blowup_pentagonCount_eq, clebsch_pentagonCount_pure,
      clebsch_size]
    ring

/-- The Clebsch graph attains the Δ=5 bound exactly: `192 = 12 · 16`. -/
theorem clebsch_attains_delta5_bound :
    pentagonCount clebschFlag = 12 * clebschFlag.size := by
  rw [clebsch_pentagonCount_pure, clebsch_size]


/-- **Converse**: a graph all of whose vertices lie in closed induced Clebsch copies
    attains `P = 12·|G|` (no triangle-freeness or degree hypotheses needed). -/
theorem pentagon_delta5_extremal_of_clebsch (G : Flag emptyType)
    (h : ∀ v : Fin G.size, ∃ φ : Fin 16 → Fin G.size, Function.Injective φ ∧ φ 0 = v ∧
      (∀ i j, clebschGraph.Adj i j ↔ G.graph.Adj (φ i) (φ j)) ∧
      (∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)) :
    pentagonCount G = 12 * G.size := by
  have h60 : ∀ v, pentagonCountAt G v = 60 := by
    intro v
    obtain ⟨φ, hinj, hphi0, hiff, hclosed⟩ := h v
    have ht := pentagonCountAt_transfer (H := clebschFlag) φ hinj hiff hclosed
      (0 : Fin 16)
    rw [hphi0] at ht
    rw [ht]
    exact clebsch_pentagonCountAt (0 : Fin 16)
  have hsum := sum_pentagonCountAt_eq_five_mul G
  rw [Finset.sum_congr rfl (fun v _ => h60 v), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-- **The Δ ≤ 5 pentagon extremum, characterised**: a triangle-free graph with maximum
    degree at most 5 attains `P = 12·|G|` (the tight constant `12/625·|G|·Δ⁴` at
    `Δ = 5`, cf. `pentagon_delta5_tight`) **iff** it is a disjoint union of Clebsch
    graphs — every vertex lies in a closed induced copy of the Clebsch graph, which is
    then its connected component. -/
theorem pentagon_delta5_extremal_iff (G : Flag emptyType) (hTF : IsTriangleFree G)
    (hdeg : maxDegree G ≤ 5) :
    pentagonCount G = 12 * G.size ↔
      ∀ v : Fin G.size, ∃ φ : Fin 16 → Fin G.size, Function.Injective φ ∧ φ 0 = v ∧
        (∀ i j, clebschGraph.Adj i j ↔ G.graph.Adj (φ i) (φ j)) ∧
        (∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u) :=
  ⟨pentagon_delta5_extremal_clebsch G hTF hdeg, pentagon_delta5_extremal_of_clebsch G⟩

end Davey2024
