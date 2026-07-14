/-
Copyright (c) 2026 Ross Kang.
Released under Apache 2.0 license.

# Phase F.7.3 — Per-edge slot assignment + slot concentration

The third piece of the FKS-Lemma-7.B bipartite nibble (after F.7.1
per-pair edge-count concentration and F.7.2 k-subset family
existence). Constructs the random edge-to-slot assignment and proves
the per-slot concentration `|T(a, l)| ≈ n*_0 · p · ρ / t` for
`ρ = (1-p)^{k-1}` and `t = |𝓘|`.

## Status
Phase F.7.3 cycle 35 (2026-06-02): foundational definitions opened.
The probabilistic content (conditional Chernoff) is deferred to
future cycles per the plan estimate (2-3 weeks total).

## Math reference
the development notes, "Bipartite
induced matching construction".
-/

import DaveyThesis2024.SecRandomBipartite.PairPackingConcentration

namespace DaveyThesis2024.SecRandomBipartite

variable {n_A n_B : ℕ}

/-! ## `R(a, u)` — valid slots for edge `(a, u)`

Given a k-subset family `𝓘 ⊆ powersetCard k A_i` and an edge `(a, u)
∈ E(G) ∩ A_i × B_j`, the *valid slots* `R(a, u)` are those slots
`I_l ∈ 𝓘` such that:
* `a ∈ I_l`, and
* `u` is NOT adjacent (in `G`) to any vertex of `I_l \ {a}`.

The kept-probability calculation (FKS): for fixed `I_l ∋ a`,
`Pr[I_l ∈ R(a, u) | G.Adj (inl a) (inr u)] = (1-p)^{k-1}`. This is
the probabilistic ingredient that drives the per-slot concentration. -/

/-- The valid slots `R(a, u)` for assigning the edge `(a, u)` to a slot
in `family`. -/
noncomputable def validSlots (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    [DecidableRel G.Adj]
    (family : Finset (Finset (Fin n_A)))
    (a : Fin n_A) (u : Fin n_B) : Finset (Finset (Fin n_A)) :=
  family.filter (fun I_l => a ∈ I_l ∧
    ∀ a' ∈ I_l, a' ≠ a → ¬ G.Adj (Sum.inl a') (Sum.inr u))

@[simp] lemma mem_validSlots
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (family : Finset (Finset (Fin n_A)))
    (a : Fin n_A) (u : Fin n_B) (I : Finset (Fin n_A)) :
    I ∈ validSlots G family a u ↔
      I ∈ family ∧ a ∈ I ∧ ∀ a' ∈ I, a' ≠ a → ¬ G.Adj (Sum.inl a') (Sum.inr u) := by
  unfold validSlots
  simp [Finset.mem_filter]

/-- `validSlots` is monotone in `family`: shrinking the family shrinks `R(a, u)`. -/
lemma validSlots_subset (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    {family₁ family₂ : Finset (Finset (Fin n_A))} (h_sub : family₁ ⊆ family₂)
    (a : Fin n_A) (u : Fin n_B) :
    validSlots G family₁ a u ⊆ validSlots G family₂ a u := by
  intro I hI
  rw [mem_validSlots] at hI ⊢
  exact ⟨h_sub hI.1, hI.2⟩

/-- `validSlots G family a u ⊆ family`: every valid slot is in the source family. -/
lemma validSlots_subset_family (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (family : Finset (Finset (Fin n_A))) (a : Fin n_A) (u : Fin n_B) :
    validSlots G family a u ⊆ family :=
  Finset.filter_subset _ _

/-- An edge `(a, u)` is *assignable* if at least one slot `I_l ∈ 𝓘`
contains `a` and has no `I_l \ {a}` neighbour of `u` in `G`. The FKS
"every edge is assignable whp" claim translates to:
`validSlots G family a u` is nonempty whp. -/
def isAssignable (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (family : Finset (Finset (Fin n_A)))
    (a : Fin n_A) (u : Fin n_B) : Prop :=
  (validSlots G family a u).Nonempty

noncomputable instance (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (family : Finset (Finset (Fin n_A))) (a : Fin n_A) (u : Fin n_B) :
    Decidable (isAssignable G family a u) := by
  unfold isAssignable
  exact Finset.decidableNonempty

/-! ## `candidateSlot` — pre-assignment "kept" set for a slot

For a fixed slot `I_l ∈ 𝓘` and `a ∈ I_l`, the **candidate set**
`candidateSlot G family I_l a` is the set of `u ∈ B_j` such that:
* `(a, u) ∈ E(G)`, AND
* No other vertex of `I_l \ {a}` is adjacent to `u` in `G`
  (i.e., `I_l ∈ validSlots G family a u`).

This is the pre-randomness object: edges `(a, u)` with `u ∈
candidateSlot` are eligible to be assigned to slot `I_l`. The actual
assigned set `T(a, l) ⊆ candidateSlot` depends on the random
assignment that chooses *which* of multiple valid slots an edge is
assigned to.

For random `G ~ G(n_A, n_B, p)`, each `u` is in `candidateSlot` with
probability `p · (1-p)^{|I_l|-1}` (the kept-probability `ρ` of FKS).
The events across distinct `u` are independent (they depend on
disjoint coordinate sets of the edge selector). So Chernoff applies
to `|candidateSlot|` analogously to F.7.1's per-pair edge count. -/

/-- The candidate set for slot `I_l` and vertex `a ∈ I_l`: vertices `u`
such that `(a, u) ∈ E(G)` and `I_l ∈ validSlots G family a u`. -/
noncomputable def candidateSlot
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (family : Finset (Finset (Fin n_A)))
    (I_l : Finset (Fin n_A)) (a : Fin n_A) : Finset (Fin n_B) :=
  (Finset.univ : Finset (Fin n_B)).filter (fun u =>
    G.Adj (Sum.inl a) (Sum.inr u) ∧ I_l ∈ validSlots G family a u)

@[simp] lemma mem_candidateSlot
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (family : Finset (Finset (Fin n_A)))
    (I_l : Finset (Fin n_A)) (a : Fin n_A) (u : Fin n_B) :
    u ∈ candidateSlot G family I_l a ↔
      G.Adj (Sum.inl a) (Sum.inr u) ∧ I_l ∈ validSlots G family a u := by
  unfold candidateSlot
  simp [Finset.mem_filter]

/-- Alternative characterisation: `u ∈ candidateSlot G family I_l a` iff
`(a, u)` is an edge AND no other vertex of `I_l` is adjacent to `u`. -/
lemma mem_candidateSlot_iff_no_extra_adj
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (family : Finset (Finset (Fin n_A)))
    (I_l : Finset (Fin n_A)) (h_mem : I_l ∈ family) (a : Fin n_A) (h_a : a ∈ I_l)
    (u : Fin n_B) :
    u ∈ candidateSlot G family I_l a ↔
      G.Adj (Sum.inl a) (Sum.inr u) ∧
        ∀ a' ∈ I_l, a' ≠ a → ¬ G.Adj (Sum.inl a') (Sum.inr u) := by
  rw [mem_candidateSlot, mem_validSlots]
  constructor
  · rintro ⟨h_adj, _, _, h_iso⟩
    exact ⟨h_adj, h_iso⟩
  · rintro ⟨h_adj, h_iso⟩
    exact ⟨h_adj, h_mem, h_a, h_iso⟩

/-- The candidate set is bounded by `n_B`. -/
lemma candidateSlot_card_le
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (family : Finset (Finset (Fin n_A)))
    (I_l : Finset (Fin n_A)) (a : Fin n_A) :
    (candidateSlot G family I_l a).card ≤ n_B := by
  calc (candidateSlot G family I_l a).card
      ≤ (Finset.univ : Finset (Fin n_B)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = n_B := by simp [Finset.card_univ, Fintype.card_fin]

/-! ## Selector-side translation: `slotIndicator` per `u`

Per-vertex indicator on selectors: for fixed slot `I_l`, vertex `a ∈ I_l`,
and `u ∈ Fin n_B`, the indicator `slotIndicator I_l a u f` evaluates to
`1` if `f(a, u) = true` (i.e., `(a, u) ∈ E(G)`) AND `f(a', u) = false`
for all other `a' ∈ I_l` (no bridging edges from `I_l \ {a}` to `u`).

For independent Bernoulli selectors, the events `slotIndicator … u = 1`
across distinct `u` are MUTUALLY INDEPENDENT (they depend on disjoint
coordinate sets `{(a', u) : a' ∈ I_l}`). Each event has probability
`p · (1-p)^{|I_l|-1}` — the FKS kept-probability `ρ`. -/

/-- Per-vertex slot-validity indicator on selectors. -/
noncomputable def slotIndicator
    (I_l : Finset (Fin n_A)) (a : Fin n_A) (u : Fin n_B) :
    (Fin n_A × Fin n_B → Bool) → ℝ :=
  fun f =>
    if f (a, u) = true ∧ ∀ a' ∈ I_l, a' ≠ a → f (a', u) = false then 1 else 0

@[simp] lemma slotIndicator_apply
    (I_l : Finset (Fin n_A)) (a : Fin n_A) (u : Fin n_B)
    (f : Fin n_A × Fin n_B → Bool) :
    slotIndicator I_l a u f =
      if f (a, u) = true ∧ ∀ a' ∈ I_l, a' ≠ a → f (a', u) = false then 1 else 0 := rfl

lemma slotIndicator_indicator
    (I_l : Finset (Fin n_A)) (a : Fin n_A) (u : Fin n_B)
    (f : Fin n_A × Fin n_B → Bool) :
    slotIndicator I_l a u f = 0 ∨ slotIndicator I_l a u f = 1 := by
  unfold slotIndicator
  split_ifs <;> simp

/-- `slotIndicator I_l a u` is measurable (source is finite ⟹ discrete
σ-algebra ⟹ all functions measurable). Mirror of
`measurable_edgeIndicator`. -/
lemma measurable_slotIndicator
    (I_l : Finset (Fin n_A)) (a : Fin n_A) (u : Fin n_B) :
    Measurable (slotIndicator I_l a u) := Measurable.of_discrete

/-! ## Product factorisation of `slotIndicator`

`slotIndicator I_l a u f = (edge ind a u) * ∏_(a' ∈ I_l.erase a) (1 - edge ind a' u)`

This factorisation reduces the expectation calculation to expectations of
each factor (each a Bernoulli or "complement Bernoulli" indicator). The
factors are independent under the product Bernoulli measure (different
coordinates of the selector). -/

open DaveyThesis2024.BipartiteRandomGraph in
/-- `slotIndicator` factors as `edgeIndicator a u * ∏_(a' ∈ I_l.erase a) (1 - edgeIndicator a' u)`. -/
lemma slotIndicator_eq_prod
    (I_l : Finset (Fin n_A)) (a : Fin n_A) (u : Fin n_B) (_h_a : a ∈ I_l)
    (f : Fin n_A × Fin n_B → Bool) :
    slotIndicator I_l a u f
      = edgeIndicator a u f *
          ∏ a' ∈ I_l.erase a, (1 - edgeIndicator a' u f) := by
  unfold slotIndicator
  simp only [edgeIndicator_apply]
  by_cases h_au : f (a, u) = true
  · rw [if_pos h_au]
    by_cases h_others : ∀ a' ∈ I_l, a' ≠ a → f (a', u) = false
    · rw [if_pos ⟨h_au, h_others⟩, one_mul]
      refine (Finset.prod_eq_one ?_).symm
      intro a' ha'
      rw [Finset.mem_erase] at ha'
      have h_false : f (a', u) = false := h_others a' ha'.2 ha'.1
      simp [h_false]
    · rw [if_neg (fun h => h_others h.2)]
      push_neg at h_others
      obtain ⟨a', ha'_mem, hne, h_ne_false⟩ := h_others
      have h_true : f (a', u) = true := by
        cases hf : f (a', u) with
        | true => rfl
        | false => exact absurd hf h_ne_false
      have h_factor_zero :
          (1 - if f (a', u) = true then (1 : ℝ) else 0) = 0 := by
        rw [if_pos h_true]; ring
      rw [show (∏ x ∈ I_l.erase a, (1 - if f (x, u) = true then (1 : ℝ) else 0)) = 0 from
          Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, ha'_mem⟩) h_factor_zero]
      ring
  · rw [if_neg h_au, if_neg (fun h => h_au h.1), zero_mul]

/-- Expectation of the **complement** edge indicator `1 - edgeIndicator a u f`
under the bipartite edge-choice PMF equals `1 - p.toReal`. -/
lemma integral_complementEdgeIndicator_eq
    (p : ENNReal) (hp : p ≤ 1) (a : Fin n_A) (u : Fin n_B) :
    ∫ f, (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a u f)
      ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      = 1 - p.toReal := by
  have h_int_one : MeasureTheory.Integrable
      (fun _ : Fin n_A × Fin n_B → Bool => (1 : ℝ))
      ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure) :=
    MeasureTheory.integrable_const _
  have h_int_edge : MeasureTheory.Integrable
      (DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a u)
      ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure) := by
    refine h_int_one.mono'
      (DaveyThesis2024.BipartiteRandomGraph.measurable_edgeIndicator a u).aestronglyMeasurable
      ?_
    filter_upwards with f
    rcases DaveyThesis2024.BipartiteRandomGraph.edgeIndicator_indicator a u f with h | h
    · rw [h]; simp
    · rw [h]; simp
  rw [MeasureTheory.integral_sub h_int_one h_int_edge,
      MeasureTheory.integral_const,
      DaveyThesis2024.BipartiteRandomGraph.integral_edgeIndicator_eq]
  simp

/-- **Base case** of the slotIndicator expectation: for `I_l = {a}` (a
singleton), the slotIndicator collapses to `edgeIndicator a u`, with
expectation `p.toReal`. Matches the FKS kept-probability `p · (1-p)^0 = p`. -/
lemma integral_slotIndicator_singleton
    (p : ENNReal) (hp : p ≤ 1) (a : Fin n_A) (u : Fin n_B) :
    ∫ f, slotIndicator ({a} : Finset (Fin n_A)) a u f
      ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      = p.toReal := by
  -- For I_l = {a}, no other a' ∈ I_l, so slotIndicator collapses to edgeIndicator a u.
  have h_eq : (fun f => slotIndicator ({a} : Finset (Fin n_A)) a u f)
              = (fun f => DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a u f) := by
    funext f
    unfold slotIndicator DaveyThesis2024.BipartiteRandomGraph.edgeIndicator
    congr 1
    simp [Finset.mem_singleton]
  rw [show (fun f => slotIndicator ({a} : Finset (Fin n_A)) a u f)
        = (fun f => DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a u f) from h_eq]
  exact DaveyThesis2024.BipartiteRandomGraph.integral_edgeIndicator_eq p hp a u

/-! ## Bounds on `∫ slotIndicator`

Loose but useful bounds: the slotIndicator expectation lies in `[0, p]`
(upper bounded by edgeIndicator's expectation `p`, since slotIndicator
constraints are a superset of edgeIndicator's). -/

/-- Pointwise bound: `slotIndicator I_l a u f ≤ edgeIndicator a u f`. -/
lemma slotIndicator_le_edgeIndicator
    (I_l : Finset (Fin n_A)) (a : Fin n_A) (u : Fin n_B)
    (f : Fin n_A × Fin n_B → Bool) :
    slotIndicator I_l a u f ≤ DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a u f := by
  unfold slotIndicator DaveyThesis2024.BipartiteRandomGraph.edgeIndicator
  split_ifs with h_slot h_edge h_edge
  · exact le_refl _
  · -- slotIndicator = 1 implies f(a, u) = true, contradicting h_edge
    exact absurd h_slot.1 h_edge
  · -- 0 ≤ 1
    norm_num
  · exact le_refl _

/-- Integrability of `slotIndicator I_l a u`. -/
lemma integrable_slotIndicator
    (p : ENNReal) (hp : p ≤ 1) (I_l : Finset (Fin n_A))
    (a : Fin n_A) (u : Fin n_B) :
    MeasureTheory.Integrable (slotIndicator I_l a u)
      ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure) := by
  refine (MeasureTheory.integrable_const (1 : ℝ)).mono'
    (measurable_slotIndicator I_l a u).aestronglyMeasurable ?_
  filter_upwards with f
  rcases slotIndicator_indicator I_l a u f with h | h
  · rw [h]; simp
  · rw [h]; simp

/-- Upper bound: `∫ slotIndicator I_l a u ≤ p.toReal`. -/
lemma integral_slotIndicator_le
    (p : ENNReal) (hp : p ≤ 1)
    (I_l : Finset (Fin n_A)) (a : Fin n_A) (u : Fin n_B) :
    ∫ f, slotIndicator I_l a u f
      ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      ≤ p.toReal := by
  calc ∫ f, slotIndicator I_l a u f
        ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      ≤ ∫ f, DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a u f
          ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure) := by
        apply MeasureTheory.integral_mono (integrable_slotIndicator p hp I_l a u)
        · refine (MeasureTheory.integrable_const (1 : ℝ)).mono'
            (DaveyThesis2024.BipartiteRandomGraph.measurable_edgeIndicator a u).aestronglyMeasurable ?_
          filter_upwards with f
          rcases DaveyThesis2024.BipartiteRandomGraph.edgeIndicator_indicator a u f with h | h
          · rw [h]; simp
          · rw [h]; simp
        · intro f
          exact slotIndicator_le_edgeIndicator I_l a u f
    _ = p.toReal :=
        DaveyThesis2024.BipartiteRandomGraph.integral_edgeIndicator_eq p hp a u

/-! ## Pair-case exact expectation (stepping stone to general case) -/

/-- For `I_l = {a, a'}` with `a ≠ a'`: the exact slotIndicator
expectation is `p · (1-p)`. Uses cycle-39 factorisation +
`IndepFun.comp` + `IndepFun.integral_fun_mul_eq_mul_integral`. -/
lemma integral_slotIndicator_pair
    (p : ENNReal) (hp : p ≤ 1) (a a' : Fin n_A) (hne : a ≠ a') (u : Fin n_B) :
    ∫ f, slotIndicator ({a, a'} : Finset (Fin n_A)) a u f
      ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      = p.toReal * (1 - p.toReal) := by
  have h_a_in : a ∈ ({a, a'} : Finset (Fin n_A)) := by simp
  -- Apply cycle-39 factorisation; the product collapses to a single factor.
  have h_erase : ({a, a'} : Finset (Fin n_A)).erase a = {a'} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxa, rfl | rfl⟩
      · exact absurd rfl hxa
      · rfl
    · rintro rfl
      exact ⟨hne.symm, Or.inr rfl⟩
  have h_factor : (fun f => slotIndicator ({a, a'} : Finset (Fin n_A)) a u f)
                = fun f => DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a u f *
                            (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a' u f) := by
    funext f
    rw [slotIndicator_eq_prod _ a u h_a_in f, h_erase]
    simp [Finset.prod_singleton]
  rw [h_factor]
  -- IndepFun via the full-product iIndepFun + .indepFun + .comp.
  have h_coord_ne : ((a, u) : Fin n_A × Fin n_B) ≠ (a', u) := by
    intro h
    have := (Prod.mk.injEq _ _ _ _).mp h
    exact hne this.1
  have h_iIndep := edgeIndicator_full_iIndepFun (n_A := n_A) (n_B := n_B) p hp
  have h_indep_edges := h_iIndep.indepFun h_coord_ne
  have h_indep :
      ProbabilityTheory.IndepFun
        (DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a u)
        (fun f => 1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a' u f)
        ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure) := by
    have h_meas : Measurable (fun x : ℝ => 1 - x) := by fun_prop
    exact h_indep_edges.comp measurable_id h_meas
  -- Integrability inputs for integral_fun_mul_eq_mul_integral.
  have h_X_aestrong :
      MeasureTheory.AEStronglyMeasurable
        (DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a u)
        ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure) :=
    (DaveyThesis2024.BipartiteRandomGraph.measurable_edgeIndicator a u).aestronglyMeasurable
  have h_Y_aestrong :
      MeasureTheory.AEStronglyMeasurable
        (fun f => 1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a' u f)
        ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure) := by
    refine ((continuous_const.sub continuous_id).measurable.comp
      (DaveyThesis2024.BipartiteRandomGraph.measurable_edgeIndicator a' u)).aestronglyMeasurable
  rw [h_indep.integral_fun_mul_eq_mul_integral h_X_aestrong h_Y_aestrong]
  rw [DaveyThesis2024.BipartiteRandomGraph.integral_edgeIndicator_eq p hp a u]
  rw [integral_complementEdgeIndicator_eq p hp a' u]

/-! ## Inductive rewrite: peel off one factor

For `a' ∈ I_l.erase a` (so `a' ≠ a` and `a' ∈ I_l`), the slotIndicator
factors as:
  `slotIndicator I_l a u f
     = slotIndicator (I_l.erase a') a u f · (1 - edgeIndicator a' u f)`.

This is the pointwise step that the inductive expectation proof uses:
combined with `IndepFun.integral_fun_mul_eq_mul_integral` (cycle 43
pattern) and the inductive hypothesis on `(I_l.erase a').card < I_l.card`,
it yields the general formula `p · (1-p)^{|I_l|-1}`. -/

open DaveyThesis2024.BipartiteRandomGraph in
lemma slotIndicator_eq_smaller_mul_complement
    (I_l : Finset (Fin n_A)) (a a' : Fin n_A)
    (h_a : a ∈ I_l) (h_a'_in : a' ∈ I_l) (h_ne : a' ≠ a) (u : Fin n_B)
    (f : Fin n_A × Fin n_B → Bool) :
    slotIndicator I_l a u f
      = slotIndicator (I_l.erase a') a u f * (1 - edgeIndicator a' u f) := by
  have h_a_in_erase : a ∈ I_l.erase a' :=
    Finset.mem_erase.mpr ⟨fun h => h_ne h.symm, h_a⟩
  -- Use cycle-39 factorisation on I_l and on I_l.erase a'.
  rw [slotIndicator_eq_prod I_l a u h_a f]
  rw [slotIndicator_eq_prod (I_l.erase a') a u h_a_in_erase f]
  -- Now we have:
  --   edge a u f · ∏_(I_l.erase a), (1 - edge a'' u f)
  -- vs
  --   (edge a u f · ∏_((I_l.erase a').erase a), (1 - edge a'' u f)) · (1 - edge a' u f)
  -- After ring rearrangement: need
  --   ∏_(I_l.erase a) ... = (1 - edge a' u f) · ∏_((I_l.erase a').erase a) ...
  -- Use Finset.erase_comm: (I_l.erase a').erase a = (I_l.erase a).erase a'.
  have h_erase_comm : (I_l.erase a').erase a = (I_l.erase a).erase a' := by
    ext x; simp [Finset.mem_erase]; tauto
  rw [h_erase_comm]
  -- Now: edge a u f · ∏_(I_l.erase a), ... = edge a u f · ∏_((I_l.erase a).erase a'), ... · (1 - edge a' u f)
  -- Use Finset.prod_erase + Finset.mul_prod_erase:
  have h_a'_in_erase_a : a' ∈ I_l.erase a := Finset.mem_erase.mpr ⟨h_ne, h_a'_in⟩
  have h_prod_split :
      ∏ a'' ∈ I_l.erase a, (1 - edgeIndicator a'' u f)
        = (1 - edgeIndicator a' u f) *
            ∏ a'' ∈ (I_l.erase a).erase a', (1 - edgeIndicator a'' u f) := by
    rw [← Finset.mul_prod_erase _ _ h_a'_in_erase_a]
  rw [h_prod_split]
  ring

/-- Sum-of-indicators identity: `|candidateSlot|` is the sum of
`slotIndicator` across `u`. Mirrors `crossBlockPairs_card_eq_sum_edgeIndicator`
(cycle 24) for the F.7.3 quantity. -/
lemma candidateSlot_card_eq_sum_slotIndicator
    (family : Finset (Finset (Fin n_A)))
    (I_l : Finset (Fin n_A)) (h_mem : I_l ∈ family)
    (a : Fin n_A) (h_a : a ∈ I_l)
    (f : Fin n_A × Fin n_B → Bool) :
    ((candidateSlot (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph f)
        family I_l a).card : ℝ)
      = ∑ u : Fin n_B, slotIndicator I_l a u f := by
  classical
  set G := DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph f
  -- The membership condition mem_candidateSlot_iff_no_extra_adj simplifies via boolToBipartiteGraph_adj.
  have h_eq :
      candidateSlot G family I_l a
        = (Finset.univ : Finset (Fin n_B)).filter
            (fun u => f (a, u) = true ∧ ∀ a' ∈ I_l, a' ≠ a → f (a', u) = false) := by
    ext u
    rw [mem_candidateSlot_iff_no_extra_adj G family I_l h_mem a h_a u]
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rintro ⟨h_adj, h_no_extra⟩
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr f a u).mp h_adj
      · intro a' ha' hne
        have h_not_adj := h_no_extra a' ha' hne
        rw [DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr] at h_not_adj
        cases hf : f (a', u) with
        | true => exact absurd hf h_not_adj
        | false => rfl
    · rintro ⟨_, h_adj_bool, h_no_extra_bool⟩
      refine ⟨?_, ?_⟩
      · exact (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr f a u).mpr h_adj_bool
      · intro a' ha' hne
        rw [DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr]
        rw [h_no_extra_bool a' ha' hne]; simp
  rw [h_eq, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro u _
  unfold slotIndicator
  split_ifs <;> simp

/-! ## General expectation: `∫ slotIndicator = p · (1-p)^{|I_l|-1}`

The FKS kept-probability formula. Proof via Route A: express slotIndicator
as a product over `↥I_l` of independent factors, apply
`iIndepFun.integral_fun_prod_eq_prod_integral`, and evaluate each factor. -/

open DaveyThesis2024.BipartiteRandomGraph in
lemma integral_slotIndicator_eq
    (p : ENNReal) (hp : p ≤ 1)
    (I_l : Finset (Fin n_A)) (a : Fin n_A) (h_a : a ∈ I_l) (u : Fin n_B) :
    ∫ f, slotIndicator I_l a u f
      ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      = p.toReal * (1 - p.toReal)^(I_l.card - 1) := by
  classical
  set μ := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure
    with hμ
  -- Per-index function on ℝ: identity on the `a` index, complement elsewhere.
  let g : ↥I_l → ℝ → ℝ := fun i x => if i.val = a then x else 1 - x
  -- Per-index function on selectors: the edgeIndicator at (i.val, u).
  let X : ↥I_l → (Fin n_A × Fin n_B → Bool) → ℝ :=
    fun i f => DaveyThesis2024.BipartiteRandomGraph.edgeIndicator i.val u f
  have h_g_meas : ∀ i, Measurable (g i) := fun i => by
    by_cases h : i.val = a
    · simp only [g, h, if_true]; exact measurable_id
    · simp only [g, h, if_false]; fun_prop
  have h_X_meas : ∀ i, Measurable (X i) := fun i =>
    DaveyThesis2024.BipartiteRandomGraph.measurable_edgeIndicator i.val u
  -- Step 1: pointwise factorisation
  -- slotIndicator I_l a u f = ∏ i : ↥I_l, g i (X i f).
  have h_prod_eq : ∀ f,
      slotIndicator I_l a u f = ∏ i : ↥I_l, g i (X i f) := by
    intro f
    -- Use cycle 39 factorisation, then convert to attach-product.
    rw [slotIndicator_eq_prod I_l a u h_a f]
    -- Goal: edgeIndicator a u f * ∏ a' ∈ I_l.erase a, (1 - edgeIndicator a' u f)
    --       = ∏ i : ↥I_l, g i (X i f)
    -- Convert RHS to a Finset product via prod_attach.
    have h_univ : (Finset.univ : Finset ↥I_l) = I_l.attach := rfl
    rw [h_univ, Finset.prod_attach I_l
      (fun a' => if a' = a then DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a' u f
                 else 1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a' u f)]
    -- Now: edgeIndicator a u f * ∏ a' ∈ I_l.erase a, (1 - edgeIndicator a' u f)
    --      = ∏ a' ∈ I_l, (if a' = a then edgeIndicator a' u f else 1 - edgeIndicator a' u f)
    -- Express RHS by splitting I_l = insert a (I_l.erase a).
    conv_rhs => rw [← Finset.insert_erase h_a]
    rw [Finset.prod_insert (Finset.notMem_erase a I_l)]
    rw [if_pos rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro a' ha'
    have h_ne : a' ≠ a := (Finset.mem_erase.mp ha').1
    rw [if_neg h_ne]
  -- Step 2: independence of the product factors.
  -- First: iIndepFun X via .precomp on the full iIndepFun.
  have h_inj : Function.Injective (fun i : ↥I_l => ((i.val, u) : Fin n_A × Fin n_B)) := by
    intro x y h
    apply Subtype.ext
    exact ((Prod.mk.injEq _ _ _ _).mp h).1
  have h_iIndep_X : ProbabilityTheory.iIndepFun X μ := by
    have h_full := edgeIndicator_full_iIndepFun (n_A := n_A) (n_B := n_B) p hp
    exact h_full.precomp h_inj
  -- Apply .comp to get iIndepFun (g i ∘ X i) — which equals (fun f => g i (X i f)).
  have h_iIndep_gX :
      ProbabilityTheory.iIndepFun (fun i f => g i (X i f)) μ := by
    have := h_iIndep_X.comp g h_g_meas
    -- (g i ∘ X i) f = g i (X i f), definitionally
    exact this
  -- AEStronglyMeasurable of each composite.
  have h_aestrong : ∀ i, MeasureTheory.AEStronglyMeasurable (fun f => g i (X i f)) μ := fun i =>
    ((h_g_meas i).comp (h_X_meas i)).aestronglyMeasurable
  -- Step 3: apply integral_fun_prod_eq_prod_integral.
  have h_int_pointwise : ∀ f, slotIndicator I_l a u f = ∏ i : ↥I_l, g i (X i f) := h_prod_eq
  have h_int_eq :
      ∫ f, slotIndicator I_l a u f ∂μ
        = ∫ f, ∏ i : ↥I_l, g i (X i f) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with f using h_int_pointwise f
  rw [h_int_eq]
  rw [h_iIndep_gX.integral_fun_prod_eq_prod_integral h_aestrong]
  -- Step 4: evaluate each factor's integral.
  -- ∫ g i (X i f) ∂μ = if i.val = a then p.toReal else 1 - p.toReal.
  have h_each : ∀ i : ↥I_l,
      ∫ f, g i (X i f) ∂μ
        = if i.val = a then p.toReal else 1 - p.toReal := by
    intro i
    by_cases h : i.val = a
    · simp only [g, h, if_true, X, hμ]
      exact DaveyThesis2024.BipartiteRandomGraph.integral_edgeIndicator_eq p hp a u
    · simp only [g, h, if_false, X, hμ]
      exact integral_complementEdgeIndicator_eq p hp i.val u
  -- Rewrite each factor.
  rw [Finset.prod_congr rfl (fun i _ => h_each i)]
  -- Step 5: ∏ i : ↥I_l, (if i.val = a then p else 1-p) = p * (1-p)^{|I_l|-1}.
  -- Convert ↥I_l-product back to Finset I_l product via prod_attach.
  have h_univ : (Finset.univ : Finset ↥I_l) = I_l.attach := rfl
  rw [h_univ]
  rw [Finset.prod_attach I_l (fun a' : Fin n_A => if a' = a then p.toReal else 1 - p.toReal)]
  -- Split via insert_erase, scoped to LHS so RHS's I_l.card stays intact.
  conv_lhs => rw [← Finset.insert_erase h_a]
  rw [Finset.prod_insert (Finset.notMem_erase a I_l)]
  rw [if_pos rfl]
  -- Each factor in the erase-product is (1 - p.toReal): constant.
  rw [Finset.prod_congr rfl (fun a' ha' =>
        if_neg (Finset.mem_erase.mp ha').1)]
  rw [Finset.prod_const]
  -- Now: p.toReal * (1 - p.toReal)^(I_l.erase a).card = p.toReal * (1 - p.toReal)^(I_l.card - 1).
  rw [Finset.card_erase_of_mem h_a]

/-! ## Cycle 46 — Independence of `slotIndicator` across `u`

For fixed `I_l, a`, the family `{slotIndicator I_l a u}_(u : Fin n_B)` is
mutually independent under the bipartite edge-choice measure.

Reason: `slotIndicator I_l a u f` depends only on the coordinates
`{(a', u) : a' ∈ I_l}` of `f`, which for distinct `u` are disjoint.
Proof: rewrite the bipartite measure as a `Measure.pi` over `Fin n_A × Fin n_B`,
then split the index `(a', u)` by `u`, using the curry equivalence
`(Fin n_A × Fin n_B → Bool) ≃ (Fin n_B → Fin n_A → Bool)`. Under the iterated
`Measure.pi`, each `slotIndicator I_l a u` factors through the `u`-th
coordinate, so `iIndepFun_pi` over `Fin n_B` applies. -/

open DaveyThesis2024.BipartiteRandomGraph in
theorem slotIndicator_iIndepFun_across_u
    (p : ENNReal) (hp : p ≤ 1)
    (I_l : Finset (Fin n_A)) (a : Fin n_A) :
    ProbabilityTheory.iIndepFun (fun u : Fin n_B => slotIndicator I_l a u)
      ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure) := by
  classical
  set μ := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure
    with hμ
  -- Step 1: per-row indicator `h_row : (Fin n_A → Bool) → ℝ`.
  let h_row : (Fin n_A → Bool) → ℝ := fun row =>
    if row a = true ∧ ∀ a' ∈ I_l, a' ≠ a → row a' = false then 1 else 0
  have h_row_meas : Measurable h_row := Measurable.of_discrete
  -- Step 2: per-`u` projection: `proj u f := fun a' => f (a', u)`.
  let proj : Fin n_B → (Fin n_A × Fin n_B → Bool) → (Fin n_A → Bool) :=
    fun u f a' => f (a', u)
  have h_proj_meas : ∀ u, Measurable (proj u) := fun u => Measurable.of_discrete
  -- Pointwise: slotIndicator I_l a u = h_row ∘ proj u.
  have h_factor : ∀ u f,
      slotIndicator I_l a u f = h_row (proj u f) := by
    intro u f
    unfold slotIndicator
    rfl
  -- Step 3: the curry equivalence `e : (Fin n_A × Fin n_B → Bool) ≃ᵐ (Fin n_B → Fin n_A → Bool)`.
  let e : (Fin n_A × Fin n_B → Bool) ≃ᵐ (Fin n_B → Fin n_A → Bool) :=
    { toFun := fun f u a' => f (a', u),
      invFun := fun g p => g p.2 p.1,
      left_inv := fun f => by funext ⟨a', u⟩; rfl,
      right_inv := fun g => by funext u a'; rfl,
      measurable_toFun := Measurable.of_discrete,
      measurable_invFun := Measurable.of_discrete }
  -- Step 4: prove `μ.map e = Measure.pi (fun u => Measure.pi (fun a => slotPMF))`.
  set νₐ := (DaveyThesis2024.BipartiteRandomGraph.slotPMF p hp).toMeasure
  set ν₂ := MeasureTheory.Measure.pi (fun _ : Fin n_B =>
              MeasureTheory.Measure.pi (fun _ : Fin n_A => νₐ)) with hν₂_def
  haveI h_νₐ_prob : MeasureTheory.IsProbabilityMeasure νₐ :=
    PMF.toMeasure.isProbabilityMeasure _
  haveI h_νA_pi_prob : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.pi (fun _ : Fin n_A => νₐ)) :=
    MeasureTheory.Measure.pi.instIsProbabilityMeasure _
  haveI h_ν₂_prob : MeasureTheory.IsProbabilityMeasure ν₂ := by
    change MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.pi _)
    exact MeasureTheory.Measure.pi.instIsProbabilityMeasure _
  haveI h_μ_prob : MeasureTheory.IsProbabilityMeasure μ := by
    rw [hμ]; infer_instance
  have h_map_e : μ.map e = ν₂ := by
    refine MeasureTheory.Measure.ext_of_singleton ?_
    intro g
    -- LHS: μ.map e {g} = μ (e ⁻¹' {g}) = μ {f | e f = g} = μ {e.symm g} = μ {(fun p => g p.2 p.1)}.
    have h_singleton_pre : e ⁻¹' {g} = {e.symm g} := by
      ext f
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      refine ⟨fun h => by rw [← h]; exact (e.left_inv f).symm, ?_⟩
      intro h; rw [h]; exact e.right_inv g
    rw [MeasureTheory.Measure.map_apply e.measurable (measurableSet_singleton g)]
    rw [h_singleton_pre]
    rw [hμ, DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice_toMeasure_eq_pi p hp]
    rw [MeasureTheory.Measure.pi_singleton]
    -- RHS: ν₂ {g} via iterated pi-singleton.
    rw [hν₂_def, MeasureTheory.Measure.pi_singleton]
    -- ∏ u, (Measure.pi (fun _ : Fin n_A => νₐ)) {g u} = ∏ u, ∏ a, νₐ {g u a}.
    have h_inner : ∀ u : Fin n_B,
        (MeasureTheory.Measure.pi (fun _ : Fin n_A => νₐ)) {g u}
          = ∏ a : Fin n_A, νₐ {g u a} := by
      intro u
      rw [MeasureTheory.Measure.pi_singleton]
    simp only [h_inner]
    -- Now: ∏ (a', u) : Fin n_A × Fin n_B, νₐ {e.symm g (a', u)} = ∏ u, ∏ a, νₐ {g u a}.
    -- e.symm g (a', u) = g u a'.
    have h_lhs_eq : ∀ p : Fin n_A × Fin n_B,
        νₐ ({e.symm g p} : Set Bool) = νₐ ({g p.2 p.1} : Set Bool) := by intro p; rfl
    conv_lhs => rw [Finset.prod_congr (rfl : (Finset.univ : Finset (Fin n_A × Fin n_B))
      = Finset.univ) (fun p _ => h_lhs_eq p)]
    rw [show (Finset.univ : Finset (Fin n_A × Fin n_B))
          = (Finset.univ : Finset (Fin n_A)) ×ˢ (Finset.univ : Finset (Fin n_B)) by
        rw [Finset.univ_product_univ]]
    rw [Finset.prod_product_right]
  -- Step 5: independence via `iIndepFun_pi` applied at `ν₂`.
  -- Family `Y u g := h_row (g u)`.
  have h_iIndep_Y : ProbabilityTheory.iIndepFun
      (fun (u : Fin n_B) (g : Fin n_B → Fin n_A → Bool) => h_row (g u)) ν₂ := by
    change ProbabilityTheory.iIndepFun _
      (MeasureTheory.Measure.pi (fun _ : Fin n_B =>
        MeasureTheory.Measure.pi (fun _ : Fin n_A => νₐ)))
    -- iIndepFun_pi with X u := h_row : (Fin n_A → Bool) → ℝ.
    exact ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin n_B => MeasureTheory.Measure.pi (fun _ : Fin n_A => νₐ))
      (X := fun _ : Fin n_B => h_row)
      (fun _ => h_row_meas.aemeasurable)
  -- Step 6: transport via iIndepFun_iff_map_fun_eq_pi_map.
  -- Family on μ: slotInd u f = h_row (proj u f) = h_row ((e f) u) = Y u (e f).
  have h_slot_meas : ∀ u : Fin n_B, AEMeasurable (slotIndicator I_l a u) μ :=
    fun u => (measurable_slotIndicator I_l a u).aemeasurable
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map h_slot_meas]
  have h_lhs_compose :
      (fun f : Fin n_A × Fin n_B → Bool => fun u : Fin n_B => slotIndicator I_l a u f)
        = (fun g : Fin n_B → Fin n_A → Bool => fun u : Fin n_B => h_row (g u)) ∘ e := by
    funext f u
    simp only [Function.comp]
    exact h_factor u f
  rw [h_lhs_compose]
  rw [← MeasureTheory.Measure.map_map (by exact Measurable.of_discrete) e.measurable]
  rw [h_map_e]
  -- Goal: ν₂.map (fun g u => h_row (g u)) = Measure.pi (fun u => μ.map (slotIndicator I_l a u)).
  -- By iIndepFun_pi via iIndepFun_iff_map_fun_eq_pi_map:
  -- ν₂.map (fun g u => h_row (g u)) = Measure.pi (fun u => ν₂.map (fun g => h_row (g u))).
  have h_iIndep_Y_meas : ∀ u : Fin n_B,
      AEMeasurable (fun g : Fin n_B → Fin n_A → Bool => h_row (g u)) ν₂ := by
    intro u
    exact (h_row_meas.comp (measurable_pi_apply u)).aemeasurable
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map h_iIndep_Y_meas).mp h_iIndep_Y]
  -- Goal: Measure.pi (fun u => ν₂.map (fun g => h_row (g u)))
  --     = Measure.pi (fun u => μ.map (slotIndicator I_l a u))
  refine congrArg MeasureTheory.Measure.pi ?_
  funext u
  -- ν₂.map (fun g => h_row (g u)) = μ.map (slotIndicator I_l a u).
  symm
  have h_eq : slotIndicator I_l a u =
      (fun g : Fin n_B → Fin n_A → Bool => h_row (g u)) ∘ e := by
    funext f
    simp only [Function.comp]
    exact h_factor u f
  rw [h_eq]
  rw [← MeasureTheory.Measure.map_map
        (f := (e : (Fin n_A × Fin n_B → Bool) → Fin n_B → Fin n_A → Bool))
        (g := fun g : Fin n_B → Fin n_A → Bool => h_row (g u))
        (h_row_meas.comp (measurable_pi_apply u)) e.measurable]
  rw [h_map_e]

/-! ## Cycle 46 — Selector-side Chernoff for ∑ slotIndicator

Apply `chernoff_A2_upper` to the family `{slotIndicator I_l a u}_(u : Fin n_B)`,
using `slotIndicator_iIndepFun_across_u` for independence and cycle 45's
`integral_slotIndicator_eq` for the expectation. -/

open DaveyThesis2024.Concentration in
open DaveyThesis2024.BipartiteRandomGraph in
lemma slotIndicator_sum_selector_upper_tail
    (p : ENNReal) (hp : p ≤ 1) (hp_pos : 0 < p.toReal)
    (I_l : Finset (Fin n_A)) (a : Fin n_A) (h_a : a ∈ I_l)
    (t : ℝ) (ht : 0 ≤ t)
    (h_μ_pos : 0 < (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1))) :
    ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
      {f | (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1)) + t
            ≤ ∑ u : Fin n_B, slotIndicator I_l a u f}
    ≤ Real.exp (- t ^ 2 /
        (2 * ((n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1)) + t / 3))) := by
  set μ := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure
  set ρ : ℝ := p.toReal * (1 - p.toReal) ^ (I_l.card - 1) with hρ_def
  have hp_le_one : p.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal (by norm_num)
    (by rw [ENNReal.ofReal_one]; exact hp)
  have h_1mp_nn : 0 ≤ 1 - p.toReal := by linarith
  have h_1mp_le_one : 1 - p.toReal ≤ 1 := by linarith [ENNReal.toReal_nonneg (a := p)]
  have hρ_nn : 0 ≤ ρ := by
    rw [hρ_def]; exact mul_nonneg hp_pos.le (pow_nonneg h_1mp_nn _)
  have hρ_le_one : ρ ≤ 1 := by
    rw [hρ_def]
    calc p.toReal * (1 - p.toReal)^(I_l.card - 1)
        ≤ 1 * 1^(I_l.card - 1) := by
          apply mul_le_mul hp_le_one (pow_le_pow_left₀ h_1mp_nn h_1mp_le_one _)
            (pow_nonneg h_1mp_nn _) (by norm_num)
      _ = 1 := by ring
  have h_sum_ρ : (∑ _u : Fin n_B, ρ) = (n_B : ℝ) * ρ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h_μ_pos_sum : 0 < ∑ _u : Fin n_B, ρ := by
    rw [h_sum_ρ]; exact h_μ_pos
  have h_chernoff := chernoff_A2_upper (μ := μ) (s := (Finset.univ : Finset (Fin n_B)))
    (X := fun u : Fin n_B => slotIndicator I_l a u)
    (slotIndicator_iIndepFun_across_u p hp I_l a)
    (fun u => measurable_slotIndicator I_l a u)
    (fun u f => slotIndicator_indicator I_l a u f)
    (fun _ => ρ)
    (fun _ => ⟨hρ_nn, hρ_le_one⟩)
    (fun u => by
      rw [hρ_def]
      exact integral_slotIndicator_eq p hp I_l a h_a u)
    t ht h_μ_pos_sum
  -- Rewrite the set + ρ-sum to the desired form.
  rw [h_sum_ρ] at h_chernoff
  exact h_chernoff

/-! ## Cycle 47 — Graph-side lift + a.a.s. headline (F.7.3 closure)

Mirrors `crossBlockPairs_graph_upper_tail` + `crossBlockPairs_concentration_aas`
(F.7.1) for the per-slot quantity `|candidateSlot G family I_l a|`. -/

/-- `candidateSlot G family I_l a` is independent of the `DecidableRel G.Adj`
instance: any two instances give the same Finset (and hence the same
cardinality). Standard instance-uniqueness for `Decidable`. Mirror of
`crossBlockPairs_inst_indep`. -/
lemma candidateSlot_inst_indep
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    (family : Finset (Finset (Fin n_A)))
    (I_l : Finset (Fin n_A)) (a : Fin n_A)
    (inst1 inst2 : DecidableRel G.Adj) :
    @candidateSlot n_A n_B G inst1 family I_l a
      = @candidateSlot n_A n_B G inst2 family I_l a := by
  have : inst1 = inst2 := Subsingleton.elim _ _
  subst this; rfl

open DaveyThesis2024.BipartiteRandomGraph in
/-- Graph-side Chernoff upper tail for `|candidateSlot G family I_l a|`.
Mirror of `crossBlockPairs_graph_upper_tail`. -/
lemma candidateSlot_graph_upper_tail
    (p : ENNReal) (hp : p ≤ 1) (hp_pos : 0 < p.toReal)
    (family : Finset (Finset (Fin n_A)))
    (I_l : Finset (Fin n_A)) (h_mem : I_l ∈ family) (a : Fin n_A) (h_a : a ∈ I_l)
    (t : ℝ) (ht : 0 ≤ t)
    (h_μ_pos : 0 < (n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1))) :
    (DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B p hp).real
      {G : SimpleGraph (Fin n_A ⊕ Fin n_B) | ∃ inst : DecidableRel G.Adj,
        (n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1)) + t
          ≤ ((@candidateSlot n_A n_B G inst family I_l a).card : ℝ)}
    ≤ Real.exp (- t^2 /
        (2 * ((n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1)) + t / 3))) := by
  set μ := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure
  set ν := DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B p hp
  set badG : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) :=
    {G | ∃ inst : DecidableRel G.Adj,
      (n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1)) + t
        ≤ ((@candidateSlot n_A n_B G inst family I_l a).card : ℝ)} with hbadG_def
  have hbadG_meas : MeasurableSet badG := MeasurableSet.of_discrete
  set selBad : Set (Fin n_A × Fin n_B → Bool) :=
    {f | (n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1)) + t
          ≤ ((candidateSlot
                (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph f)
                family I_l a).card : ℝ)}
    with hselBad_def
  have h_preimage_sub :
      DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph ⁻¹' badG ⊆ selBad := by
    intro f hf
    simp only [Set.mem_preimage, hbadG_def, Set.mem_setOf_eq] at hf
    obtain ⟨inst, hf_inst⟩ := hf
    simp only [hselBad_def, Set.mem_setOf_eq]
    rwa [candidateSlot_inst_indep
      (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph f) family I_l a
      (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_decidableAdj f) inst]
  -- Translate selBad to the sum-of-slotIndicators form via cycle 37.
  have h_selBad_eq :
      selBad = {f | (n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1)) + t
                  ≤ ∑ u : Fin n_B, slotIndicator I_l a u f} := by
    ext f
    simp only [hselBad_def, Set.mem_setOf_eq]
    rw [candidateSlot_card_eq_sum_slotIndicator family I_l h_mem a h_a f]
  calc ν.real badG
      = μ.real (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph ⁻¹' badG) := by
        unfold MeasureTheory.Measure.real
        rw [DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure_eq_preimage
          p hp hbadG_meas]
    _ ≤ μ.real selBad := by
        unfold MeasureTheory.Measure.real
        exact ENNReal.toReal_mono (MeasureTheory.measure_lt_top _ _).ne
          (MeasureTheory.measure_mono h_preimage_sub)
    _ ≤ Real.exp _ := by
        rw [h_selBad_eq]
        exact slotIndicator_sum_selector_upper_tail p hp hp_pos I_l a h_a t ht h_μ_pos

open DaveyThesis2024.BipartiteRandomGraph in
/-- Good-event (complement) form: the **good event** that
`|candidateSlot G family I_l a|` stays below the Chernoff threshold
has probability ≥ `1 - exp(...)`. Mirror of
`crossBlockPairs_graph_concentration_lower`. -/
lemma candidateSlot_graph_concentration_lower
    (p : ENNReal) (hp : p ≤ 1) (hp_pos : 0 < p.toReal)
    (family : Finset (Finset (Fin n_A)))
    (I_l : Finset (Fin n_A)) (h_mem : I_l ∈ family) (a : Fin n_A) (h_a : a ∈ I_l)
    (t : ℝ) (ht : 0 ≤ t)
    (h_μ_pos : 0 < (n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1))) :
    (DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B p hp).real
      {G : SimpleGraph (Fin n_A ⊕ Fin n_B) | ∀ [inst : DecidableRel G.Adj],
        ((@candidateSlot n_A n_B G inst family I_l a).card : ℝ)
          < (n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1)) + t}
    ≥ 1 - Real.exp (- t^2 /
        (2 * ((n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1)) + t / 3))) := by
  set ν := DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B p hp
  set badG : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) :=
    {G | ∃ inst : DecidableRel G.Adj,
      (n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1)) + t
        ≤ ((@candidateSlot n_A n_B G inst family I_l a).card : ℝ)} with hbadG_def
  set goodG : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) :=
    {G | ∀ [inst : DecidableRel G.Adj],
      ((@candidateSlot n_A n_B G inst family I_l a).card : ℝ)
        < (n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1)) + t} with hgoodG_def
  have h_good_compl : goodG = badGᶜ := by
    ext G
    simp only [hgoodG_def, hbadG_def, Set.mem_setOf_eq, Set.mem_compl_iff,
               not_exists, not_le]
  have h_bad_meas : MeasurableSet badG := MeasurableSet.of_discrete
  have h_good_compl_eq : ν goodG = 1 - ν badG := by
    rw [h_good_compl]; exact MeasureTheory.prob_compl_eq_one_sub h_bad_meas
  have h_bad_le_one : ν badG ≤ 1 := by
    rw [show (1 : ENNReal) = ν Set.univ from (MeasureTheory.measure_univ).symm]
    exact MeasureTheory.measure_mono (Set.subset_univ _)
  have h_good_toReal : (ν goodG).toReal = 1 - (ν badG).toReal := by
    rw [h_good_compl_eq, ENNReal.toReal_sub_of_le h_bad_le_one ENNReal.one_ne_top]; simp
  have h_bad_le : ν.real badG
      ≤ Real.exp (- t^2 /
          (2 * ((n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1)) + t / 3))) :=
    candidateSlot_graph_upper_tail p hp hp_pos family I_l h_mem a h_a t ht h_μ_pos
  change (ν goodG).toReal ≥ _
  rw [h_good_toReal]
  unfold MeasureTheory.Measure.real at h_bad_le
  linarith

open DaveyThesis2024.BipartiteRandomGraph in
/-- F.7.3 a.a.s. headline: `|candidateSlot G family I_l a|` concentrates
within additive `δ·n_B` of the mean `n_B · p · (1-p)^{|I_l|-1}`, a.a.s.
as `n_B → ∞`. Mirror of `crossBlockPairs_concentration_aas`.

We require `p.toReal < 1` so that the kept-probability `ρ := p · (1-p)^{k-1}`
is strictly positive (it appears in the Chernoff denominator). -/
theorem candidateSlot_concentration_aas
    (p : ENNReal) (hp : p ≤ 1) (hp_pos : 0 < p.toReal) (hp_lt : p.toReal < 1)
    (family : Finset (Finset (Fin n_A)))
    (I_l : Finset (Fin n_A)) (h_mem : I_l ∈ family) (a : Fin n_A) (h_a : a ∈ I_l)
    (δ : ℝ) (hδ_pos : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, N ≤ n_B →
      (DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B p hp).real
        {G : SimpleGraph (Fin n_A ⊕ Fin n_B) | ∀ [inst : DecidableRel G.Adj],
          ((@candidateSlot n_A n_B G inst family I_l a).card : ℝ)
            < (n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1) + δ)}
        ≥ 1 - ε := by
  classical
  set ρ : ℝ := p.toReal * (1 - p.toReal)^(I_l.card - 1) with hρ_def
  have h_1mp_pos : 0 < 1 - p.toReal := by linarith
  have hρ_pos : 0 < ρ := by
    rw [hρ_def]; exact mul_pos hp_pos (pow_pos h_1mp_pos _)
  -- Chernoff coefficient: c := δ² / (2(ρ + δ/3))
  set c : ℝ := δ^2 / (2 * (ρ + δ/3)) with hc_def
  have hρ_plus_δ_third_pos : 0 < ρ + δ/3 := by linarith
  have hc_pos : 0 < c := by rw [hc_def]; positivity
  -- N₀ such that for n ≥ N₀, exp(-c·n) ≤ ε
  obtain ⟨N₀, hN₀⟩ := SECRandomBipartite.exists_N_exp_neg_le_eps c ε hc_pos hε
  refine ⟨max N₀ 1, ?_⟩
  intro hN
  have hN₀_le : N₀ ≤ n_B := le_trans (le_max_left _ _) hN
  have hone_le : 1 ≤ n_B := le_trans (le_max_right _ _) hN
  set M : ℝ := (n_B : ℝ) with hM_def
  have h_M_pos : 0 < M := by
    have h1 : 0 < n_B := by omega
    rw [hM_def]; exact_mod_cast h1
  set t : ℝ := M * δ with ht_def
  have h_t_nn : 0 ≤ t := by rw [ht_def]; positivity
  have h_μ_pos : 0 < M * ρ := mul_pos h_M_pos hρ_pos
  -- Apply the graph-side lower bound.
  have h_conc := candidateSlot_graph_concentration_lower p hp hp_pos family I_l h_mem
    a h_a t h_t_nn (by rw [← hρ_def, ← hM_def]; exact h_μ_pos)
  -- Rewrite the event: M·ρ + t = M·(ρ + δ) (using t = M·δ).
  have h_set_eq :
    {G : SimpleGraph (Fin n_A ⊕ Fin n_B) | ∀ [inst : DecidableRel G.Adj],
      ((@candidateSlot n_A n_B G inst family I_l a).card : ℝ)
        < (n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1)) + t}
    = {G | ∀ [inst : DecidableRel G.Adj],
      ((@candidateSlot n_A n_B G inst family I_l a).card : ℝ)
        < (n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1) + δ)} := by
    have h_arith : M * ρ + t = M * (ρ + δ) := by rw [ht_def]; ring
    ext G
    simp only [Set.mem_setOf_eq]
    rw [show ((n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1)) + t)
              = M * ρ + t from by rw [hM_def, hρ_def],
        h_arith,
        show M * (ρ + δ) = ((n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1) + δ)) from by
          rw [hM_def, hρ_def]]
  rw [h_set_eq] at h_conc
  -- Simplify the exp: -t²/(2(M·ρ + t/3)) = -c·M
  have h_exp_eq : Real.exp (-t^2 /
                  (2 * ((n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1)) + t / 3)))
                = Real.exp (-(c * M)) := by
    congr 1
    rw [show ((n_B : ℝ) * (p.toReal * (1 - p.toReal)^(I_l.card - 1)) + t / 3)
            = M * ρ + t / 3 from by rw [hM_def, hρ_def]]
    rw [ht_def, hc_def]
    have hM_ne : M ≠ 0 := ne_of_gt h_M_pos
    have h_denom_ne : (2 : ℝ) * (ρ + δ/3) ≠ 0 := by positivity
    field_simp
  rw [h_exp_eq] at h_conc
  -- Apply hN₀ to bound exp by ε
  have h_exp_le_eps : Real.exp (-(c * M)) ≤ ε := by
    have h_cast : (-(c * M) : ℝ) = -(c * n_B) := by rw [hM_def]
    rw [h_cast]
    exact hN₀ n_B hN₀_le
  linarith

end DaveyThesis2024.SecRandomBipartite
