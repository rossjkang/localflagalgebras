/-
Copyright (c) 2026 Ross Kang.
Released under Apache 2.0 license.

# F.7.4.A — Per-edge slot-assignment probability space

The **per-edge slot-assignment** for the bipartite Czygrinow–Nagle nibble.
For each cross-pair `(a, u) : Fin n_A × Fin n_B`, independently sample a
slot-index `σ (a, u) : Fin t` uniformly from `Fin t`, where `t : ℕ` (the
slot-index range, `t = family.card` in the F.7.4 application).

**Critical** (per the development notes
doublecheck Correction 2): the slot assignment `σ` is sampled
**independently of the graph**, on `Fin t` itself (NOT on `validSlots`,
which would couple to the graph and break independence). The factorisation
of the kept event for edge `(a, u) → I_l` into three independent indicators
- `1[(a, u) ∈ E(G)]`
- `1[I_l ∈ validSlots G family a u]`
- `1[σ (a, u) = I_l_idx]`

is established at the joint `(graph × σ)` product space via `Measure.prod`.

This file builds the per-coord uniform PMF on `Fin t`, the product PMF over
all cross-pairs, the bridge to `Measure.pi`, the combined joint measure
`combinedMeasure` (graph × σ via `Measure.prod`), and the two foundational
theorems used by F.7.4.B:

- `slotAssignment_indep_of_graph` — graph projection is independent of the
  σ-indicator under `combinedMeasure`.
- `integral_slotIndicator_eq_one_over_t` — expected value of the σ-indicator
  is `1 / t`.

## Status

F.7.4.A — open the slot-assignment probability space (cycle 50, 2026-06-02).

This is the foundation for F.7.4.B (kept-edges concentration), F.7.4.C
(greedy transversal), F.7.4.D (PerPairCover assembly), and F.7.5 (final
synthesis of `perPair_packing_aas_FKS`).
-/
import DaveyThesis2024.BipartiteRandomGraph
import DaveyThesis2024.SecRandomBipartite.SlotConcentration
import Mathlib.Probability.Distributions.Uniform

namespace DaveyThesis2024.SecRandomBipartite.SlotAssignment

open scoped ENNReal
open MeasureTheory ProbabilityTheory DaveyThesis2024.BipartiteRandomGraph

variable {n_A n_B t : ℕ}

/-! ## Step 1: per-coord uniform PMF on `Fin t` -/

/-- The per-coord uniform PMF on `Fin t`: each `i : Fin t` has mass `1/t`.
The `0 < t` hypothesis ensures the carrier is nonempty (so the uniform PMF
is well-defined). -/
noncomputable def slotIndexPMF (t : ℕ) (ht : 0 < t) : PMF (Fin t) :=
  PMF.uniformOfFinset (Finset.univ : Finset (Fin t))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, ht⟩⟩)

@[simp] lemma slotIndexPMF_apply (t : ℕ) (ht : 0 < t) (i : Fin t) :
    slotIndexPMF t ht i = (t : ℝ≥0∞)⁻¹ := by
  unfold slotIndexPMF
  rw [PMF.uniformOfFinset_apply_of_mem _ (Finset.mem_univ i)]
  simp

lemma sum_slotIndexPMF_eq_one (t : ℕ) (ht : 0 < t) :
    (∑ i : Fin t, slotIndexPMF t ht i) = 1 := by
  haveI : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
  have h := (slotIndexPMF t ht).tsum_coe
  rw [tsum_eq_sum (s := (Finset.univ : Finset (Fin t)))
        (fun a ha => absurd (Finset.mem_univ a) ha)] at h
  exact h

/-! ## Step 2: product PMF for the slot-assignment selector

Sum-to-one lemma analogous to `sum_prod_edgeWeight_eq_one`. -/

lemma sum_prod_slotIndexPMF_eq_one (t : ℕ) (ht : 0 < t) (n_A n_B : ℕ) :
    (∑ σ : Fin n_A × Fin n_B → Fin t,
      ∏ ab : Fin n_A × Fin n_B, slotIndexPMF t ht (σ ab)) = 1 := by
  classical
  rw [← Fintype.prod_sum (κ := fun _ : Fin n_A × Fin n_B => Fin t)
        (fun _ i => slotIndexPMF t ht i)]
  rw [Finset.prod_congr rfl (fun e _ => sum_slotIndexPMF_eq_one t ht)]
  exact Finset.prod_const_one

/-- The product uniform PMF over `Fin n_A × Fin n_B → Fin t`. Each
coordinate independently draws from `slotIndexPMF t ht`. -/
noncomputable def slotAssignmentChoice (n_A n_B t : ℕ) (ht : 0 < t) :
    PMF (Fin n_A × Fin n_B → Fin t) :=
  PMF.ofFintype (fun σ => ∏ ab : Fin n_A × Fin n_B, slotIndexPMF t ht (σ ab))
    (sum_prod_slotIndexPMF_eq_one t ht n_A n_B)

@[simp] theorem slotAssignmentChoice_apply {n_A n_B t : ℕ} (ht : 0 < t)
    (σ : Fin n_A × Fin n_B → Fin t) :
    slotAssignmentChoice n_A n_B t ht σ =
      ∏ ab : Fin n_A × Fin n_B, slotIndexPMF t ht (σ ab) :=
  PMF.ofFintype_apply _ _

/-! ## Step 3: bridge to `Measure.pi`

Mirror of `bipartiteEdgeChoice_toMeasure_eq_pi`. -/

/-- The probability measure on `Fin n_A × Fin n_B → Fin t` underlying
`slotAssignmentChoice` is the `Measure.pi` of independent per-coord uniform
measures on `Fin t`. -/
lemma slotAssignmentChoice_toMeasure_eq_pi (t : ℕ) (ht : 0 < t)
    (n_A n_B : ℕ) :
    (slotAssignmentChoice n_A n_B t ht).toMeasure
      = Measure.pi (fun _ : Fin n_A × Fin n_B => (slotIndexPMF t ht).toMeasure) := by
  refine Measure.ext_of_singleton ?_
  intro σ
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton σ)]
  rw [slotAssignmentChoice_apply]
  rw [Measure.pi_singleton]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (σ e))]

/-! ## Step 4: `IsProbabilityMeasure` instance on `slotAssignmentChoice` -/

instance slotAssignmentChoice_isProbabilityMeasure (n_A n_B t : ℕ) (ht : 0 < t) :
    IsProbabilityMeasure ((slotAssignmentChoice n_A n_B t ht).toMeasure) :=
  inferInstance

/-! ## Step 5: combined joint measure on `(graph selector) × (slot assignment)` -/

/-- The combined product measure on `(Fin n_A × Fin n_B → Bool) ×
(Fin n_A × Fin n_B → Fin t)`: the bipartite edge selector independent of the
slot assignment.

This is the joint probability space referenced in `plan/phase_F74_F75_closure_plan.md`
where the kept-event for edge `(a, u) → I_l` factorises into three independent
indicators (graph adjacency, valid-slot membership, σ-coord match), with the
σ-coord match depending only on the σ-factor of this product. -/
noncomputable def combinedMeasure (n_A n_B t : ℕ) (p : ENNReal) (hp : p ≤ 1)
    (ht : 0 < t) :
    Measure ((Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) :=
  (bipartiteEdgeChoice n_A n_B p hp).toMeasure.prod
    (slotAssignmentChoice n_A n_B t ht).toMeasure

instance combinedMeasure_isProbabilityMeasure (n_A n_B t : ℕ) (p : ENNReal)
    (hp : p ≤ 1) (ht : 0 < t) :
    IsProbabilityMeasure (combinedMeasure n_A n_B t p hp ht) := by
  unfold combinedMeasure
  infer_instance

/-! ## Step 6: slot-assignment indicator and independence from graph

The σ-projection at coord `(a, u)` is independent of the graph selector
under the joint product measure — this is `indepFun_prod` specialised to
our setting. -/

/-- The slot-assignment indicator for edge `(a, u)` and slot-index `j : Fin t`:
returns 1 if the random σ assigns `(a, u)` to slot `j`, else 0. -/
noncomputable def slotIndicator (n_A n_B t : ℕ) (a : Fin n_A) (u : Fin n_B)
    (j : Fin t) :
    (Fin n_A × Fin n_B → Fin t) → ℝ :=
  fun σ => if σ (a, u) = j then (1 : ℝ) else 0

@[simp] lemma slotIndicator_apply (n_A n_B t : ℕ) (a : Fin n_A) (u : Fin n_B)
    (j : Fin t) (σ : Fin n_A × Fin n_B → Fin t) :
    slotIndicator n_A n_B t a u j σ = if σ (a, u) = j then (1 : ℝ) else 0 :=
  rfl

/-- The slot indicator is measurable from `(Fin n_A × Fin n_B → Fin t)`
(discrete σ-algebra; source is finite) to `ℝ` (Borel). -/
lemma measurable_slotIndicator (n_A n_B t : ℕ) (a : Fin n_A) (u : Fin n_B)
    (j : Fin t) :
    Measurable (slotIndicator n_A n_B t a u j) :=
  Measurable.of_discrete

/-- **Independence of graph and slot-assignment under the joint measure.**

Under `combinedMeasure`, the graph-projection `gs.1` (an arbitrary function
of the bipartite selector) is independent of the slot-indicator
`1[σ (a, u) = j]` (a function of the σ-factor).

This is the joint-space independence step that lets F.7.4.B's kept-edges
event factor into a product of three independent indicators. -/
theorem slotAssignment_indep_of_graph
    (n_A n_B t : ℕ) (ht : 0 < t) (p : ENNReal) (hp : p ≤ 1)
    (a : Fin n_A) (u : Fin n_B) (j : Fin t) :
    IndepFun
      (fun gs : (Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t) => gs.1)
      (fun gs => slotIndicator n_A n_B t a u j gs.2)
      (combinedMeasure n_A n_B t p hp ht) := by
  unfold combinedMeasure
  -- `indepFun_prod` gives `(fun ω ↦ X ω.1) ⟂ᵢ[μ.prod ν] (fun ω ↦ Y ω.2)`
  -- for measurable `X` and `Y`. Take `X := id` and `Y := slotIndicator ...`.
  exact indepFun_prod (mX := measurable_id) (mY := measurable_slotIndicator n_A n_B t a u j)

/-! ## Step 7: expectation of the slot indicator equals `1/t` -/

/-- The slot-indicator equals the indicator of `{σ | σ (a, u) = j}`. -/
lemma slotIndicator_eq_indicator (n_A n_B t : ℕ) (a : Fin n_A) (u : Fin n_B)
    (j : Fin t) :
    slotIndicator n_A n_B t a u j
      = Set.indicator
          {σ : Fin n_A × Fin n_B → Fin t | σ (a, u) = j}
          (fun _ => (1 : ℝ)) := by
  funext σ
  unfold slotIndicator
  by_cases h : σ (a, u) = j <;> simp [h]

/-- The probability that `σ (a, u) = j` under `slotAssignmentChoice`
equals `1/t`. This is the per-coord marginal of the product PMF. -/
lemma slotAssignmentChoice_apply_at_eq (t : ℕ) (ht : 0 < t)
    (a : Fin n_A) (u : Fin n_B) (j : Fin t) :
    (slotAssignmentChoice n_A n_B t ht).toMeasure
      {σ : Fin n_A × Fin n_B → Fin t | σ (a, u) = j} = (t : ℝ≥0∞)⁻¹ := by
  classical
  have hms : MeasurableSet {σ : Fin n_A × Fin n_B → Fin t | σ (a, u) = j} :=
    MeasurableSet.of_discrete
  rw [(slotAssignmentChoice n_A n_B t ht).toMeasure_apply hms]
  rw [tsum_eq_sum (s := (Finset.univ : Finset (Fin n_A × Fin n_B → Fin t)))
        (fun σ hσ => absurd (Finset.mem_univ σ) hσ)]
  simp only [Set.indicator_apply, Set.mem_setOf_eq, slotAssignmentChoice_apply]
  rw [← Finset.sum_filter, Finset.sum_filter]
  -- Goal: ∑ σ, if σ(a,u)=j then ∏ ab, slotIndexPMF t ht (σ ab) else 0 = 1/t.
  -- Use the same per-slot indicator trick as `bipartiteEdgeChoice_apply_at_eq_true`.
  have key : ∀ σ : Fin n_A × Fin n_B → Fin t,
      (if σ (a, u) = j then ∏ ab : Fin n_A × Fin n_B, slotIndexPMF t ht (σ ab) else 0)
        = ∏ ab : Fin n_A × Fin n_B,
            slotIndexPMF t ht (σ ab) * (if ab = (a, u) ∧ σ ab ≠ j then 0 else 1) := by
    intro σ
    by_cases h : σ (a, u) = j
    · rw [if_pos h]
      refine Finset.prod_congr rfl (fun e _ => ?_)
      by_cases he : e = (a, u)
      · subst he; simp [h]
      · simp [he]
    · rw [if_neg h]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ (a, u))
      simp [h]
  simp_rw [key]
  rw [← Fintype.prod_sum (κ := fun _ : Fin n_A × Fin n_B => Fin t)
        (fun e v => slotIndexPMF t ht v * (if e = (a, u) ∧ v ≠ j then 0 else 1))]
  -- Per-coord evaluation: at (a,u), the sum collapses to `slotIndexPMF t ht j = 1/t`.
  -- Elsewhere, sum equals `∑ v, slotIndexPMF t ht v = 1`.
  have per_coord : ∀ e : Fin n_A × Fin n_B,
      (∑ v : Fin t, slotIndexPMF t ht v * (if e = (a, u) ∧ v ≠ j then 0 else 1))
        = if e = (a, u) then ((t : ℝ≥0∞)⁻¹) else 1 := by
    intro e
    by_cases he : e = (a, u)
    · -- Collapse to v = j term.
      subst he
      rw [Finset.sum_eq_single j]
      · simp
      · intro v _ hv
        simp [hv]
      · intro h; exact absurd (Finset.mem_univ j) h
    · -- All cases reduce to slotIndexPMF t ht v.
      simp only [he, false_and, if_false, mul_one]
      exact sum_slotIndexPMF_eq_one t ht
  rw [Finset.prod_congr rfl (fun e _ => per_coord e)]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  -- ⊢ (t⁻¹) ^ ((Finset.univ : Finset _).filter (· = (a, u))).card = t⁻¹
  have hcard : ((Finset.univ : Finset (Fin n_A × Fin n_B)).filter (· = (a, u))).card = 1 := by
    have : ((Finset.univ : Finset (Fin n_A × Fin n_B)).filter (· = (a, u))) = {(a, u)} := by
      ext x; simp
    rw [this]; rfl
  rw [hcard, pow_one]

/-- **Per-coord uniform expectation.**

The expected value of the slot-indicator `1[σ (a, u) = j]` under
`combinedMeasure` is exactly `1/t`. Independent of the graph distribution
(per Correction 2), since the σ-factor is uniform.

This is the basic input to F.7.4.B's kept-edges expectation calculation:
`E[|T(a, l)|] = n_B · p · (1-p)^(k-1) / t`, where the `1/t` factor comes
from this lemma. -/
theorem integral_slotIndicator_eq_one_over_t
    (n_A n_B t : ℕ) (ht : 0 < t) (p : ENNReal) (hp : p ≤ 1)
    (a : Fin n_A) (u : Fin n_B) (j : Fin t) :
    ∫ gs : (Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t),
        slotIndicator n_A n_B t a u j gs.2
      ∂(combinedMeasure n_A n_B t p hp ht) = 1 / (t : ℝ) := by
  classical
  -- Step 1: rewrite the integrand as `g ∘ snd` where `g = slotIndicator ...`.
  -- The function depends only on the second factor.
  unfold combinedMeasure
  -- Use Fubini (`integral_prod`) to reduce to an integral over the slot space.
  -- The integrand `gs ↦ slotIndicator ... gs.2` is bounded, measurable, hence integrable
  -- under a probability measure.
  have h_integrable :
      Integrable
        (fun gs : (Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t) =>
          slotIndicator n_A n_B t a u j gs.2)
        ((bipartiteEdgeChoice n_A n_B p hp).toMeasure.prod
          (slotAssignmentChoice n_A n_B t ht).toMeasure) := by
    apply MeasureTheory.Integrable.mono'
      (g := fun _ => (1 : ℝ))
      (MeasureTheory.integrable_const 1)
    · exact (Measurable.of_discrete).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun gs => ?_)
      unfold slotIndicator
      by_cases h : gs.2 (a, u) = j
      · simp [h]
      · simp [h]
  rw [integral_prod _ h_integrable]
  -- Inner integral: ∫ σ, slotIndicator ... σ ∂(slotAssignmentChoice).toMeasure = 1/t.
  -- This is independent of the graph selector f, so the outer integral evaluates to 1/t.
  have h_inner :
      ∫ σ, slotIndicator n_A n_B t a u j σ
          ∂((slotAssignmentChoice n_A n_B t ht).toMeasure) = 1 / (t : ℝ) := by
    rw [slotIndicator_eq_indicator]
    have h1 : (fun _ : Fin n_A × Fin n_B → Fin t => (1 : ℝ))
        = (1 : (Fin n_A × Fin n_B → Fin t) → ℝ) := by funext; rfl
    rw [h1]
    rw [MeasureTheory.integral_indicator_one MeasurableSet.of_discrete]
    unfold MeasureTheory.Measure.real
    rw [slotAssignmentChoice_apply_at_eq t ht a u j]
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp_rw [h_inner]
  rw [MeasureTheory.integral_const]
  rw [probReal_univ, one_smul]

/-! ## F.7.4.B — Kept-edges set `T(a, l)` and concentration

For a fixed slot `I_l` and `a ∈ I_l`, the **kept-set** `T(a, l) ⊆ Fin n_B`
is the set of `u` such that:
* `(a, u) ∈ E(G)` (graph adjacency),
* `I_l ∈ validSlots G family a u` (no bridging edges from `I_l \ {a}` to `u`),
* `slot_at (σ (a, u)) = I_l` (the random assignment lands on this slot).

The FKS kept-edges expectation:
  `E[|T(a, l)|] = n_B · p · (1-p)^{|I_l|-1} / t`,
where the `1/t` factor comes from the uniform slot assignment (per
Correction 3 of the plan's doublecheck addendum).

The kept-indicator factorises into:
* `1[(a, u) ∈ E(G) ∧ I_l ∈ validSlots]` — a function of `gs.1` (graph),
* `1[slot_at (σ (a, u)) = I_l]` — a function of `gs.2` (assignment).
The first factor's expectation is `p · (1-p)^{|I_l|-1}` (cycle 45's
`SlotConcentration.integral_slotIndicator_eq`); the second's expectation
is `1/t` when `slot_at` is injective (cycle F.7.4.A's
`integral_slotIndicator_eq_one_over_t`). Joint expectation factors via
`indepFun_prod` on the joint product measure. -/

/-- The **kept-set** `T(a, l)` for slot `I_l` and `a ∈ I_l`: vertices
`u ∈ Fin n_B` such that the edge `(a, u)` is in `G`, `I_l` is a valid
slot for that edge, and `σ` assigns `(a, u)` to (an index pointing to)
`I_l`. -/
noncomputable def keptSet
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (family : Finset (Finset (Fin n_A))) (t : ℕ)
    (slot_at : Fin t → Finset (Fin n_A))
    (I_l : Finset (Fin n_A)) (a : Fin n_A)
    (σ : Fin n_A × Fin n_B → Fin t) : Finset (Fin n_B) :=
  (Finset.univ : Finset (Fin n_B)).filter (fun u =>
    G.Adj (Sum.inl a) (Sum.inr u) ∧
    I_l ∈ DaveyThesis2024.SecRandomBipartite.validSlots G family a u ∧
    slot_at (σ (a, u)) = I_l)

@[simp] lemma mem_keptSet
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (family : Finset (Finset (Fin n_A))) (t : ℕ)
    (slot_at : Fin t → Finset (Fin n_A))
    (I_l : Finset (Fin n_A)) (a : Fin n_A)
    (σ : Fin n_A × Fin n_B → Fin t) (u : Fin n_B) :
    u ∈ keptSet G family t slot_at I_l a σ ↔
      G.Adj (Sum.inl a) (Sum.inr u) ∧
      I_l ∈ DaveyThesis2024.SecRandomBipartite.validSlots G family a u ∧
      slot_at (σ (a, u)) = I_l := by
  unfold keptSet
  simp [Finset.mem_filter]

/-- The kept-indicator for edge `(a, u)` and slot `I_l` on the joint
`(graph × σ)` product space. Returns 1 iff all three kept-event
conditions hold. -/
noncomputable def keptIndicator
    (family : Finset (Finset (Fin n_A))) (t : ℕ)
    (slot_at : Fin t → Finset (Fin n_A))
    (I_l : Finset (Fin n_A)) (a : Fin n_A) (u : Fin n_B) :
    ((Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) → ℝ :=
  fun gs =>
    if (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1).Adj
         (Sum.inl a) (Sum.inr u) ∧
       I_l ∈ DaveyThesis2024.SecRandomBipartite.validSlots
              (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1) family a u ∧
       slot_at (gs.2 (a, u)) = I_l
    then 1 else 0

@[simp] lemma keptIndicator_apply
    (family : Finset (Finset (Fin n_A))) (t : ℕ)
    (slot_at : Fin t → Finset (Fin n_A))
    (I_l : Finset (Fin n_A)) (a : Fin n_A) (u : Fin n_B)
    (gs : (Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) :
    keptIndicator family t slot_at I_l a u gs =
      if (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1).Adj
           (Sum.inl a) (Sum.inr u) ∧
         I_l ∈ DaveyThesis2024.SecRandomBipartite.validSlots
                (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1) family a u ∧
         slot_at (gs.2 (a, u)) = I_l
      then 1 else 0 := rfl

lemma keptIndicator_indicator
    (family : Finset (Finset (Fin n_A))) (t : ℕ)
    (slot_at : Fin t → Finset (Fin n_A))
    (I_l : Finset (Fin n_A)) (a : Fin n_A) (u : Fin n_B)
    (gs : (Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) :
    keptIndicator family t slot_at I_l a u gs = 0 ∨
      keptIndicator family t slot_at I_l a u gs = 1 := by
  unfold keptIndicator
  split_ifs <;> simp

lemma measurable_keptIndicator
    (family : Finset (Finset (Fin n_A))) (t : ℕ)
    (slot_at : Fin t → Finset (Fin n_A))
    (I_l : Finset (Fin n_A)) (a : Fin n_A) (u : Fin n_B) :
    Measurable (keptIndicator family t slot_at I_l a u) :=
  Measurable.of_discrete

/-- **Factorisation of `keptIndicator`** as a product of a graph-only factor
and a σ-only factor. The graph-only factor is
`SlotConcentration.slotIndicator I_l a u (gs.1)` and the σ-only factor is
`SlotAssignment.slotIndicator n_A n_B t a u j (gs.2)` for any `j` with
`slot_at j = I_l` (assuming `slot_at` is injective so there's a unique
such `j`). -/
lemma keptIndicator_eq_prod
    (family : Finset (Finset (Fin n_A))) (t : ℕ)
    (slot_at : Fin t → Finset (Fin n_A))
    (h_inj : Function.Injective slot_at)
    (I_l : Finset (Fin n_A)) (h_mem : I_l ∈ family) (a : Fin n_A) (h_a : a ∈ I_l)
    (u : Fin n_B) (j : Fin t) (h_slot : slot_at j = I_l)
    (gs : (Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) :
    keptIndicator family t slot_at I_l a u gs =
      DaveyThesis2024.SecRandomBipartite.slotIndicator I_l a u gs.1 *
        slotIndicator n_A n_B t a u j gs.2 := by
  classical
  unfold keptIndicator DaveyThesis2024.SecRandomBipartite.slotIndicator slotIndicator
  -- The graph-side condition `G.Adj ∧ I_l ∈ validSlots` is equivalent (under
  -- `mem_candidateSlot_iff_no_extra_adj`) to the boolean form
  -- `f (a, u) = true ∧ ∀ a' ∈ I_l, a' ≠ a → f (a', u) = false`.
  set f := gs.1
  set σ := gs.2
  set G := DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph f
  -- Translate the graph-side condition to the boolean form.
  have h_graph_iff :
      (G.Adj (Sum.inl a) (Sum.inr u) ∧
        I_l ∈ DaveyThesis2024.SecRandomBipartite.validSlots G family a u) ↔
      (f (a, u) = true ∧ ∀ a' ∈ I_l, a' ≠ a → f (a', u) = false) := by
    constructor
    · rintro ⟨h_adj, h_valid⟩
      rw [DaveyThesis2024.SecRandomBipartite.mem_validSlots] at h_valid
      obtain ⟨_, _, h_no_extra⟩ := h_valid
      refine ⟨?_, ?_⟩
      · exact (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr
                f a u).mp h_adj
      · intro a' ha' hne
        have h_not_adj := h_no_extra a' ha' hne
        rw [DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr] at h_not_adj
        cases hf : f (a', u) with
        | true => exact absurd hf h_not_adj
        | false => rfl
    · rintro ⟨h_adj_bool, h_no_extra_bool⟩
      refine ⟨?_, ?_⟩
      · exact (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr
                f a u).mpr h_adj_bool
      · rw [DaveyThesis2024.SecRandomBipartite.mem_validSlots]
        refine ⟨h_mem, h_a, ?_⟩
        intro a' ha' hne
        rw [DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr]
        rw [h_no_extra_bool a' ha' hne]; simp
  -- Now translate the σ-side condition.
  have h_sigma_iff : slot_at (σ (a, u)) = I_l ↔ σ (a, u) = j := by
    refine ⟨fun h => ?_, fun h => by rw [h]; exact h_slot⟩
    exact h_inj (h.trans h_slot.symm)
  -- Split into four cases.
  by_cases h1 : f (a, u) = true ∧ ∀ a' ∈ I_l, a' ≠ a → f (a', u) = false
  · -- Graph side holds.
    by_cases h2 : σ (a, u) = j
    · -- σ side also holds.
      rw [if_pos]
      · rw [if_pos h1, if_pos h2]; ring
      · refine ⟨h_graph_iff.mpr h1 |>.1, h_graph_iff.mpr h1 |>.2, h_sigma_iff.mpr h2⟩
    · -- σ side fails.
      rw [if_neg]
      · rw [if_pos h1, if_neg h2]; ring
      · rintro ⟨_, _, h_eq⟩
        exact h2 (h_sigma_iff.mp h_eq)
  · -- Graph side fails.
    rw [if_neg]
    · rw [if_neg h1]; ring
    · rintro ⟨h_adj, h_valid, _⟩
      exact h1 (h_graph_iff.mp ⟨h_adj, h_valid⟩)

/-! ### Theorem 1: Per-(u, l) kept-indicator expectation -/

/-- **Per-(u, l) kept-indicator expectation.** Under `combinedMeasure`, the
expected value of `keptIndicator family t slot_at I_l a u` equals
`p · (1-p)^{|I_l|-1} / t`. This combines (via `indepFun_prod` on the
joint product space):
* the graph-side `slotIndicator` expectation `p · (1-p)^{|I_l|-1}`
  (cycle 45's `SlotConcentration.integral_slotIndicator_eq`),
* the σ-side `slotIndicator` expectation `1/t`
  (F.7.4.A's `integral_slotIndicator_eq_one_over_t`).

The `slot_at` injectivity hypothesis ensures the σ-side event
`slot_at (σ(a,u)) = I_l` is exactly the singleton event `σ(a,u) = j`. -/
theorem integral_keptIndicator_eq
    (n_A n_B t : ℕ) (ht : 0 < t) (p : ENNReal) (hp : p ≤ 1)
    (family : Finset (Finset (Fin n_A))) (slot_at : Fin t → Finset (Fin n_A))
    (h_inj : Function.Injective slot_at)
    (I_l : Finset (Fin n_A)) (h_mem : I_l ∈ family) (a : Fin n_A) (h_a : a ∈ I_l)
    (j : Fin t) (h_slot : slot_at j = I_l) (u : Fin n_B) :
    ∫ gs, keptIndicator family t slot_at I_l a u gs
      ∂(combinedMeasure n_A n_B t p hp ht)
      = p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) := by
  classical
  -- Rewrite the kept-indicator as a product of two factors:
  -- graph-side `slotIndicator` (function of gs.1) and σ-side `slotIndicator`
  -- (function of gs.2).
  have h_factor : ∀ gs : (Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t),
      keptIndicator family t slot_at I_l a u gs =
        DaveyThesis2024.SecRandomBipartite.slotIndicator I_l a u gs.1 *
          slotIndicator n_A n_B t a u j gs.2 :=
    fun gs => keptIndicator_eq_prod family t slot_at h_inj I_l h_mem a h_a u j h_slot gs
  -- Unfold the combined measure for Fubini.
  unfold combinedMeasure
  -- Use Fubini-style `integral_prod` on the joint measure: rewrite the
  -- integral as an iterated integral. The integrand is a product of a
  -- function of gs.1 and a function of gs.2, so the iterated integral
  -- factorises via standard `integral_const_mul` / `integral_mul_const`.
  set μ₁ := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure
    with hμ₁_def
  set μ₂ := (slotAssignmentChoice n_A n_B t ht).toMeasure with hμ₂_def
  -- Integrability of the product integrand under μ₁.prod μ₂.
  have h_integrable :
      Integrable
        (fun gs : (Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t) =>
          DaveyThesis2024.SecRandomBipartite.slotIndicator I_l a u gs.1 *
            slotIndicator n_A n_B t a u j gs.2) (μ₁.prod μ₂) := by
    apply MeasureTheory.Integrable.mono'
      (g := fun _ => (1 : ℝ)) (MeasureTheory.integrable_const 1)
    · exact (Measurable.of_discrete).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun gs => ?_)
      rcases DaveyThesis2024.SecRandomBipartite.slotIndicator_indicator I_l a u gs.1 with h1 | h1
      · rw [h1]; simp
      · have h2 : slotIndicator n_A n_B t a u j gs.2 = 0 ∨
                  slotIndicator n_A n_B t a u j gs.2 = 1 := by
          unfold slotIndicator
          split_ifs <;> simp
        rcases h2 with h2 | h2
        · rw [h1, h2]; simp
        · rw [h1, h2]; simp
  -- Pointwise equality of integrands.
  rw [MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun gs => h_factor gs))]
  -- Apply Fubini.
  rw [MeasureTheory.integral_prod _ h_integrable]
  -- Inner integral over μ₂ of the σ-side factor (times a constant from gs.1).
  -- ∫ σ, slotInd_gr * slotInd_σ ∂μ₂ = slotInd_gr * ∫ σ, slotInd_σ ∂μ₂.
  have h_inner : ∀ f : Fin n_A × Fin n_B → Bool,
      ∫ σ, DaveyThesis2024.SecRandomBipartite.slotIndicator I_l a u f *
            slotIndicator n_A n_B t a u j σ ∂μ₂
        = DaveyThesis2024.SecRandomBipartite.slotIndicator I_l a u f * (1 / (t : ℝ)) := by
    intro f
    rw [MeasureTheory.integral_const_mul]
    congr 1
    -- ∫ σ, slotIndicator ... σ ∂μ₂ = 1/t.
    -- We use integral_slotIndicator_eq_one_over_t but specialised to the
    -- pure σ-marginal. The F.7.4.A theorem is over the joint measure; here
    -- we use the analogous one-marginal form derived from the slotPMF.
    rw [hμ₂_def, slotIndicator_eq_indicator]
    have h1 : (fun _ : Fin n_A × Fin n_B → Fin t => (1 : ℝ))
        = (1 : (Fin n_A × Fin n_B → Fin t) → ℝ) := by funext; rfl
    rw [h1]
    rw [MeasureTheory.integral_indicator_one MeasurableSet.of_discrete]
    unfold MeasureTheory.Measure.real
    rw [slotAssignmentChoice_apply_at_eq t ht a u j]
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp_rw [h_inner]
  -- Outer integral over μ₁: pull the (1/t) constant out, then use
  -- SlotConcentration's integral_slotIndicator_eq.
  rw [MeasureTheory.integral_mul_const]
  rw [DaveyThesis2024.SecRandomBipartite.integral_slotIndicator_eq p hp I_l a h_a u]
  -- Goal: p.toReal * (1-p.toReal) ^ (I_l.card-1) * (1/t)
  --     = p.toReal * (1-p.toReal) ^ (I_l.card-1) / t
  field_simp

/-! ## Sum-of-indicators identity for `keptSet`

`|T(a, l)|` cast to ℝ equals `∑ u : Fin n_B, keptIndicator ... gs u`. Mirrors
`SlotConcentration.candidateSlot_card_eq_sum_slotIndicator`. -/

lemma keptSet_card_eq_sum_keptIndicator
    (n_A n_B t : ℕ)
    (family : Finset (Finset (Fin n_A))) (slot_at : Fin t → Finset (Fin n_A))
    (I_l : Finset (Fin n_A)) (_h_mem : I_l ∈ family)
    (a : Fin n_A) (_h_a : a ∈ I_l)
    (gs : (Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) :
    ((keptSet (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1)
        family t slot_at I_l a gs.2).card : ℝ)
      = ∑ u : Fin n_B, keptIndicator family t slot_at I_l a u gs := by
  classical
  -- Rewrite keptSet as a filter, then translate the cardinality to a sum of indicators.
  unfold keptSet
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro u _
  unfold keptIndicator
  rfl

/-! ### iIndepFun across u: kept indicators on the joint product space

The family `{keptIndicator family t slot_at I_l a u}_(u : Fin n_B)` is
mutually independent under `combinedMeasure n_A n_B t p hp ht`. This is
the cycle-46 currying trick adapted to the joint space — we re-curry the
joint space:
  `((Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t))`
  `≃ᵐ Fin n_B → (Fin n_A → Bool) × (Fin n_A → Fin t)`
and the joint measure equals the `Measure.pi` of per-row joint measures.

The proof uses both `bipartiteEdgeChoice_toMeasure_eq_pi` and
`slotAssignmentChoice_toMeasure_eq_pi` to re-express each factor as a
`Measure.pi`, then applies `Measure.prod_pi` (or its analog via
`Measure.ext_of_singleton`). -/

open DaveyThesis2024.BipartiteRandomGraph in
theorem keptIndicator_iIndepFun_across_u
    (n_A n_B t : ℕ) (ht : 0 < t) (p : ENNReal) (hp : p ≤ 1)
    (family : Finset (Finset (Fin n_A))) (slot_at : Fin t → Finset (Fin n_A))
    (h_inj : Function.Injective slot_at)
    (I_l : Finset (Fin n_A)) (h_mem : I_l ∈ family) (a : Fin n_A) (h_a : a ∈ I_l)
    (j : Fin t) (h_slot : slot_at j = I_l) :
    ProbabilityTheory.iIndepFun
      (fun u : Fin n_B => keptIndicator family t slot_at I_l a u)
      (combinedMeasure n_A n_B t p hp ht) := by
  classical
  set μ := combinedMeasure n_A n_B t p hp ht with hμ_def
  -- The per-`u` indicator on rows: takes a row `(Fin n_A → Bool) × (Fin n_A → Fin t)`
  -- and computes the kept-indicator's value for that row.
  let h_row : ((Fin n_A → Bool) × (Fin n_A → Fin t)) → ℝ := fun row =>
    if (row.1 a = true ∧ ∀ a' ∈ I_l, a' ≠ a → row.1 a' = false) ∧
       row.2 a = j
    then 1 else 0
  have h_row_meas : Measurable h_row := Measurable.of_discrete
  -- Per-u projection: from the joint space to the per-row space.
  let proj : Fin n_B → ((Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) →
      ((Fin n_A → Bool) × (Fin n_A → Fin t)) :=
    fun u gs => (fun a' => gs.1 (a', u), fun a' => gs.2 (a', u))
  have h_proj_meas : ∀ u, Measurable (proj u) := fun u => Measurable.of_discrete
  -- Pointwise equality: keptIndicator family t slot_at I_l a u gs = h_row (proj u gs).
  have h_factor : ∀ u gs,
      keptIndicator family t slot_at I_l a u gs = h_row (proj u gs) := by
    intro u gs
    -- Translate using keptIndicator_eq_prod first.
    rw [keptIndicator_eq_prod family t slot_at h_inj I_l h_mem a h_a u j h_slot]
    -- Now LHS = (CN.slotIndicator I_l a u gs.1) * (SlotAssignment.slotIndicator ... gs.2),
    -- RHS = h_row (proj u gs) which by definition is:
    --   if ((proj u gs).1 a = true ∧ ∀ a' ∈ I_l, a' ≠ a → (proj u gs).1 a' = false) ∧
    --     (proj u gs).2 a = j then 1 else 0
    -- = if (gs.1 (a, u) = true ∧ ∀ a' ∈ I_l, a' ≠ a → gs.1 (a', u) = false) ∧
    --     gs.2 (a, u) = j then 1 else 0
    change (DaveyThesis2024.SecRandomBipartite.slotIndicator I_l a u gs.1) *
            slotIndicator n_A n_B t a u j gs.2
          = if (gs.1 (a, u) = true ∧ ∀ a' ∈ I_l, a' ≠ a → gs.1 (a', u) = false) ∧
              gs.2 (a, u) = j then 1 else 0
    unfold DaveyThesis2024.SecRandomBipartite.slotIndicator slotIndicator
    by_cases h1 : gs.1 (a, u) = true ∧ ∀ a' ∈ I_l, a' ≠ a → gs.1 (a', u) = false
    · by_cases h2 : gs.2 (a, u) = j
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]; ring
      · rw [if_pos h1, if_neg h2]
        rw [if_neg (fun (h : _ ∧ _) => h2 h.2)]
        ring
    · rw [if_neg h1]
      rw [if_neg (fun (h : _ ∧ _) => h1 h.1)]
      ring
  -- Curry equivalence: ((Fin n_A × Fin n_B → α) × (Fin n_A × Fin n_B → β))
  --                   ≃ᵐ (Fin n_B → (Fin n_A → α) × (Fin n_A → β)).
  let e : ((Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) ≃ᵐ
          (Fin n_B → (Fin n_A → Bool) × (Fin n_A → Fin t)) :=
    { toFun := fun gs u => (fun a' => gs.1 (a', u), fun a' => gs.2 (a', u))
      invFun := fun g =>
        (fun p => (g p.2).1 p.1, fun p => (g p.2).2 p.1)
      left_inv := fun gs => by
        ext ⟨a', u⟩
        · rfl
        · rfl
      right_inv := fun g => by
        funext u
        ext a'
        · rfl
        · rfl
      measurable_toFun := Measurable.of_discrete
      measurable_invFun := Measurable.of_discrete }
  -- The per-u measure on the row space.
  set νₐ := (DaveyThesis2024.BipartiteRandomGraph.slotPMF p hp).toMeasure with hνₐ_def
  set νs := (slotIndexPMF t ht).toMeasure with hνs_def
  -- The per-row joint measure (explicit, no `let`).
  set ν_row : MeasureTheory.Measure ((Fin n_A → Bool) × (Fin n_A → Fin t)) :=
    (MeasureTheory.Measure.pi (fun _ : Fin n_A => νₐ)).prod
      (MeasureTheory.Measure.pi (fun _ : Fin n_A => νs)) with hν_row_def
  haveI h_νₐ_prob : MeasureTheory.IsProbabilityMeasure νₐ :=
    PMF.toMeasure.isProbabilityMeasure _
  haveI h_νs_prob : MeasureTheory.IsProbabilityMeasure νs :=
    PMF.toMeasure.isProbabilityMeasure _
  haveI h_νA_pi_prob : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.pi (fun _ : Fin n_A => νₐ)) :=
    MeasureTheory.Measure.pi.instIsProbabilityMeasure _
  haveI h_νs_pi_prob : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.pi (fun _ : Fin n_A => νs)) :=
    MeasureTheory.Measure.pi.instIsProbabilityMeasure _
  haveI h_ν_row_prob : MeasureTheory.IsProbabilityMeasure ν_row := by
    rw [hν_row_def]; infer_instance
  -- The product-over-u of the per-row joint measures.
  set ν₂ : MeasureTheory.Measure (Fin n_B → (Fin n_A → Bool) × (Fin n_A → Fin t)) :=
    MeasureTheory.Measure.pi (fun _ : Fin n_B => ν_row) with hν₂_def
  haveI h_ν₂_prob : MeasureTheory.IsProbabilityMeasure ν₂ := by
    change MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.pi _)
    exact MeasureTheory.Measure.pi.instIsProbabilityMeasure _
  haveI h_μ_prob : MeasureTheory.IsProbabilityMeasure μ := by
    rw [hμ_def]; infer_instance
  -- Per-row singleton mass: ν_row {x} = (∏ a', νₐ {x.1 a'}) * (∏ a', νs {x.2 a'}).
  have h_νrow_singleton : ∀ x : (Fin n_A → Bool) × (Fin n_A → Fin t),
      ν_row {x} = (∏ a' : Fin n_A, νₐ {x.1 a'}) *
                   (∏ a' : Fin n_A, νs {x.2 a'}) := by
    intro x
    rw [hν_row_def]
    rw [show ({x} : Set ((Fin n_A → Bool) × (Fin n_A → Fin t)))
          = ({x.1} : Set _) ×ˢ ({x.2} : Set _) from by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_prod, Prod.ext_iff]]
    rw [MeasureTheory.Measure.prod_prod,
        MeasureTheory.Measure.pi_singleton, MeasureTheory.Measure.pi_singleton]
  -- Step: μ.map e = ν₂. Both measures evaluate the same on singletons.
  have h_map_e : μ.map e = ν₂ := by
    refine MeasureTheory.Measure.ext_of_singleton ?_
    intro g
    have h_singleton_pre : e ⁻¹' {g} = {e.symm g} := by
      ext gs
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      refine ⟨fun h => by rw [← h]; exact (e.left_inv gs).symm, ?_⟩
      intro h; rw [h]; exact e.right_inv g
    rw [MeasureTheory.Measure.map_apply e.measurable (measurableSet_singleton g)]
    rw [h_singleton_pre]
    -- LHS: μ {e.symm g} = (μ₁.prod μ₂) {e.symm g}.
    rw [hμ_def]
    unfold combinedMeasure
    rw [DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice_toMeasure_eq_pi p hp]
    rw [slotAssignmentChoice_toMeasure_eq_pi t ht n_A n_B]
    rw [show ({e.symm g} : Set ((Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)))
          = ({(fun p : Fin n_A × Fin n_B => (g p.2).1 p.1)} : Set _) ×ˢ
            ({(fun p : Fin n_A × Fin n_B => (g p.2).2 p.1)} : Set _) from by
      ext gs
      simp only [Set.mem_singleton_iff, Set.mem_prod, Prod.ext_iff]
      rfl]
    rw [MeasureTheory.Measure.prod_prod]
    rw [MeasureTheory.Measure.pi_singleton, MeasureTheory.Measure.pi_singleton]
    -- LHS now: (∏ p, slotPMF {(g p.2).1 p.1}) * (∏ p, slotIndexPMF {(g p.2).2 p.1}).
    -- RHS: ν₂ {g} = ∏ u, ν_row {g u}, expand ν_row via h_νrow_singleton.
    rw [hν₂_def]
    rw [MeasureTheory.Measure.pi_singleton]
    simp_rw [h_νrow_singleton]
    -- Goal: (∏ p, νₐ {(g p.2).1 p.1}) * (∏ p, νs {(g p.2).2 p.1})
    --     = ∏ u, ((∏ a', νₐ {(g u).1 a'}) * (∏ a', νs {(g u).2 a'}))
    rw [Finset.prod_mul_distrib]
    -- Now: LHS-side = ((∏ p, νₐ ...) * (∏ p, νs ...))
    --     RHS-side = ((∏ u, ∏ a', νₐ ...) * (∏ u, ∏ a', νs ...))
    congr 1
    all_goals {
      rw [show (Finset.univ : Finset (Fin n_A × Fin n_B))
            = (Finset.univ : Finset (Fin n_A)) ×ˢ (Finset.univ : Finset (Fin n_B)) by
          rw [Finset.univ_product_univ]]
      rw [Finset.prod_product_right]
    }
  -- iIndepFun on the curried side via iIndepFun_pi.
  -- Family Y u g := h_row (g u).
  have h_iIndep_Y : ProbabilityTheory.iIndepFun
      (fun (u : Fin n_B) (g : Fin n_B → (Fin n_A → Bool) × (Fin n_A → Fin t)) =>
        h_row (g u)) ν₂ := by
    change ProbabilityTheory.iIndepFun _
      (MeasureTheory.Measure.pi (fun _ : Fin n_B => ν_row))
    exact ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin n_B => ν_row)
      (X := fun _ : Fin n_B => h_row)
      (fun _ => h_row_meas.aemeasurable)
  -- Transport via iIndepFun_iff_map_fun_eq_pi_map.
  have h_kept_meas : ∀ u : Fin n_B,
      AEMeasurable (keptIndicator family t slot_at I_l a u) μ :=
    fun u => (measurable_keptIndicator family t slot_at I_l a u).aemeasurable
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map h_kept_meas]
  -- The combined function (fun gs u => keptIndicator ... u gs)
  -- equals (fun g u => h_row (g u)) ∘ e.
  have h_lhs_compose :
      (fun gs : (Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t) =>
        fun u : Fin n_B => keptIndicator family t slot_at I_l a u gs)
        = (fun g : Fin n_B → (Fin n_A → Bool) × (Fin n_A → Fin t) =>
            fun u : Fin n_B => h_row (g u)) ∘ e := by
    funext gs u
    simp only [Function.comp]
    exact h_factor u gs
  rw [h_lhs_compose]
  rw [← MeasureTheory.Measure.map_map (by exact Measurable.of_discrete) e.measurable]
  rw [h_map_e]
  -- Goal: ν₂.map (fun g u => h_row (g u)) = Measure.pi (fun u => μ.map (keptIndicator ... u)).
  have h_Y_meas : ∀ u : Fin n_B,
      AEMeasurable (fun g : Fin n_B → (Fin n_A → Bool) × (Fin n_A → Fin t) => h_row (g u)) ν₂ := by
    intro u
    exact (h_row_meas.comp (measurable_pi_apply u)).aemeasurable
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map h_Y_meas).mp h_iIndep_Y]
  -- Now: Measure.pi (fun u => ν₂.map (fun g => h_row (g u)))
  --     = Measure.pi (fun u => μ.map (keptIndicator ... u))
  refine congrArg MeasureTheory.Measure.pi ?_
  funext u
  symm
  have h_eq : keptIndicator family t slot_at I_l a u =
      (fun g : Fin n_B → (Fin n_A → Bool) × (Fin n_A → Fin t) => h_row (g u)) ∘ e := by
    funext gs
    simp only [Function.comp]
    exact h_factor u gs
  rw [h_eq]
  rw [← MeasureTheory.Measure.map_map
        (f := (e : ((Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) →
                Fin n_B → (Fin n_A → Bool) × (Fin n_A → Fin t)))
        (g := fun g : Fin n_B → (Fin n_A → Bool) × (Fin n_A → Fin t) => h_row (g u))
        (h_row_meas.comp (measurable_pi_apply u)) e.measurable]
  rw [h_map_e]

/-! ### Selector-side Chernoff for sum of kept indicators -/

open DaveyThesis2024.Concentration in
open DaveyThesis2024.BipartiteRandomGraph in
lemma keptIndicator_sum_upper_tail
    (n_A n_B t : ℕ) (ht : 0 < t) (p : ENNReal) (hp : p ≤ 1) (hp_pos : 0 < p.toReal)
    (family : Finset (Finset (Fin n_A))) (slot_at : Fin t → Finset (Fin n_A))
    (h_inj : Function.Injective slot_at)
    (I_l : Finset (Fin n_A)) (h_mem : I_l ∈ family) (a : Fin n_A) (h_a : a ∈ I_l)
    (j : Fin t) (h_slot : slot_at j = I_l)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (h_μ_pos :
      0 < (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ))) :
    (combinedMeasure n_A n_B t p hp ht).real
      {gs | (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ)) + τ
            ≤ ∑ u : Fin n_B, keptIndicator family t slot_at I_l a u gs}
    ≤ Real.exp (- τ^2 /
        (2 * ((n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ)) + τ / 3))) := by
  set μ := combinedMeasure n_A n_B t p hp ht with hμ_def
  set ρ : ℝ := p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) with hρ_def
  -- ρ bounds.
  have hp_le_one : p.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal (by norm_num)
    (by rw [ENNReal.ofReal_one]; exact hp)
  have h_1mp_nn : 0 ≤ 1 - p.toReal := by linarith
  have h_1mp_le_one : 1 - p.toReal ≤ 1 := by linarith [ENNReal.toReal_nonneg (a := p)]
  have h_pow_nn : 0 ≤ (1 - p.toReal) ^ (I_l.card - 1) := pow_nonneg h_1mp_nn _
  have h_pow_le_one : (1 - p.toReal) ^ (I_l.card - 1) ≤ 1 :=
    pow_le_one₀ h_1mp_nn h_1mp_le_one
  have h_t_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have h_t_ne : (t : ℝ) ≠ 0 := h_t_pos.ne'
  have hρ_nn : 0 ≤ ρ := by
    rw [hρ_def]
    exact div_nonneg (mul_nonneg hp_pos.le h_pow_nn) h_t_pos.le
  have h_ρ_num_le_one : p.toReal * (1 - p.toReal) ^ (I_l.card - 1) ≤ 1 := by
    calc p.toReal * (1 - p.toReal) ^ (I_l.card - 1) ≤ 1 * 1 :=
            mul_le_mul hp_le_one h_pow_le_one h_pow_nn (by norm_num)
      _ = 1 := by ring
  have h_one_le_t : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hρ_le_one : ρ ≤ 1 := by
    rw [hρ_def]
    have h1 : p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) ≤ 1 / (t : ℝ) := by
      apply div_le_div_of_nonneg_right h_ρ_num_le_one h_t_pos.le
    have h2 : (1 : ℝ) / (t : ℝ) ≤ 1 := by
      rw [div_le_one h_t_pos]; exact h_one_le_t
    linarith
  have h_sum_ρ : (∑ _u : Fin n_B, ρ) = (n_B : ℝ) * ρ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h_μ_pos_sum : 0 < ∑ _u : Fin n_B, ρ := by
    rw [h_sum_ρ]; exact h_μ_pos
  have h_chernoff := chernoff_A2_upper (μ := μ)
    (s := (Finset.univ : Finset (Fin n_B)))
    (X := fun u : Fin n_B => keptIndicator family t slot_at I_l a u)
    (keptIndicator_iIndepFun_across_u n_A n_B t ht p hp family slot_at h_inj
      I_l h_mem a h_a j h_slot)
    (fun u => measurable_keptIndicator family t slot_at I_l a u)
    (fun u gs => keptIndicator_indicator family t slot_at I_l a u gs)
    (fun _ => ρ)
    (fun _ => ⟨hρ_nn, hρ_le_one⟩)
    (fun u => by
      rw [hρ_def]
      exact integral_keptIndicator_eq n_A n_B t ht p hp family slot_at h_inj
        I_l h_mem a h_a j h_slot u)
    τ hτ h_μ_pos_sum
  rw [h_sum_ρ] at h_chernoff
  exact h_chernoff

open DaveyThesis2024.Concentration in
open DaveyThesis2024.BipartiteRandomGraph in
/-- **Lower-tail Chernoff for the kept-indicator sum** (R5.a).

Mirror of `keptIndicator_sum_upper_tail`: instead of bounding
`P[Σ keptIndicator ≥ μ + τ]` from above, this bounds
`P[Σ keptIndicator ≤ μ - τ]` via `chernoff_A2_lower`.

Used by `keptSet_concentration_aas_lower` (R5.b) to derive a LOWER bound on
`keptSet.card`, which feeds Wake 6's γ.H derivation of a lower bound on
`greedyMatchings.card` (and hence `bulk.card`).

The strictness hypothesis `τ < μ` is required by `chernoff_A2_lower` (so the
denominator `μ - τ/3 > 0` and the canonical multiplicative-Chernoff form
applies). It propagates upward as `δ < ρ` in R5.b. -/
lemma keptIndicator_sum_lower_tail
    (n_A n_B t : ℕ) (ht : 0 < t) (p : ENNReal) (hp : p ≤ 1) (hp_pos : 0 < p.toReal)
    (family : Finset (Finset (Fin n_A))) (slot_at : Fin t → Finset (Fin n_A))
    (h_inj : Function.Injective slot_at)
    (I_l : Finset (Fin n_A)) (h_mem : I_l ∈ family) (a : Fin n_A) (h_a : a ∈ I_l)
    (j : Fin t) (h_slot : slot_at j = I_l)
    (τ : ℝ) (hτ_nn : 0 ≤ τ)
    (h_τ_lt_μ : τ < (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ)))
    (h_μ_pos :
      0 < (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ))) :
    (combinedMeasure n_A n_B t p hp ht).real
      {gs | ∑ u : Fin n_B, keptIndicator family t slot_at I_l a u gs
            ≤ (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ)) - τ}
    ≤ Real.exp (- τ^2 /
        (2 * ((n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ)) - τ / 3))) := by
  set μ := combinedMeasure n_A n_B t p hp ht with hμ_def
  set ρ : ℝ := p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) with hρ_def
  -- ρ bounds.
  have hp_le_one : p.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal (by norm_num)
    (by rw [ENNReal.ofReal_one]; exact hp)
  have h_1mp_nn : 0 ≤ 1 - p.toReal := by linarith
  have h_1mp_le_one : 1 - p.toReal ≤ 1 := by linarith [ENNReal.toReal_nonneg (a := p)]
  have h_pow_nn : 0 ≤ (1 - p.toReal) ^ (I_l.card - 1) := pow_nonneg h_1mp_nn _
  have h_pow_le_one : (1 - p.toReal) ^ (I_l.card - 1) ≤ 1 :=
    pow_le_one₀ h_1mp_nn h_1mp_le_one
  have h_t_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have h_t_ne : (t : ℝ) ≠ 0 := h_t_pos.ne'
  have hρ_nn : 0 ≤ ρ := by
    rw [hρ_def]
    exact div_nonneg (mul_nonneg hp_pos.le h_pow_nn) h_t_pos.le
  have h_ρ_num_le_one : p.toReal * (1 - p.toReal) ^ (I_l.card - 1) ≤ 1 := by
    calc p.toReal * (1 - p.toReal) ^ (I_l.card - 1) ≤ 1 * 1 :=
            mul_le_mul hp_le_one h_pow_le_one h_pow_nn (by norm_num)
      _ = 1 := by ring
  have h_one_le_t : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hρ_le_one : ρ ≤ 1 := by
    rw [hρ_def]
    have h1 : p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) ≤ 1 / (t : ℝ) := by
      apply div_le_div_of_nonneg_right h_ρ_num_le_one h_t_pos.le
    have h2 : (1 : ℝ) / (t : ℝ) ≤ 1 := by
      rw [div_le_one h_t_pos]; exact h_one_le_t
    linarith
  have h_sum_ρ : (∑ _u : Fin n_B, ρ) = (n_B : ℝ) * ρ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h_μ_pos_sum : 0 < ∑ _u : Fin n_B, ρ := by
    rw [h_sum_ρ]; exact h_μ_pos
  have h_τ_lt_sum : τ < ∑ _u : Fin n_B, ρ := by
    rw [h_sum_ρ]; exact h_τ_lt_μ
  have h_chernoff := chernoff_A2_lower (μ := μ)
    (s := (Finset.univ : Finset (Fin n_B)))
    (X := fun u : Fin n_B => keptIndicator family t slot_at I_l a u)
    (keptIndicator_iIndepFun_across_u n_A n_B t ht p hp family slot_at h_inj
      I_l h_mem a h_a j h_slot)
    (fun u => measurable_keptIndicator family t slot_at I_l a u)
    (fun u gs => keptIndicator_indicator family t slot_at I_l a u gs)
    (fun _ => ρ)
    (fun _ => ⟨hρ_nn, hρ_le_one⟩)
    (fun u => by
      rw [hρ_def]
      exact integral_keptIndicator_eq n_A n_B t ht p hp family slot_at h_inj
        I_l h_mem a h_a j h_slot u)
    τ hτ_nn h_τ_lt_sum h_μ_pos_sum
  rw [h_sum_ρ] at h_chernoff
  exact h_chernoff

/-! ### Lower (good-event) bound + a.a.s. headline -/

open DaveyThesis2024.BipartiteRandomGraph in
lemma keptIndicator_sum_concentration_lower
    (n_A n_B t : ℕ) (ht : 0 < t) (p : ENNReal) (hp : p ≤ 1) (hp_pos : 0 < p.toReal)
    (family : Finset (Finset (Fin n_A))) (slot_at : Fin t → Finset (Fin n_A))
    (h_inj : Function.Injective slot_at)
    (I_l : Finset (Fin n_A)) (h_mem : I_l ∈ family) (a : Fin n_A) (h_a : a ∈ I_l)
    (j : Fin t) (h_slot : slot_at j = I_l)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (h_μ_pos :
      0 < (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ))) :
    (combinedMeasure n_A n_B t p hp ht).real
      {gs | (∑ u : Fin n_B, keptIndicator family t slot_at I_l a u gs)
              < (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ)) + τ}
    ≥ 1 - Real.exp (- τ^2 /
        (2 * ((n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ)) + τ / 3))) := by
  set μ := combinedMeasure n_A n_B t p hp ht with hμ_def
  set bad : Set ((Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) :=
    {gs | (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ)) + τ
          ≤ ∑ u : Fin n_B, keptIndicator family t slot_at I_l a u gs} with hbad_def
  set good : Set ((Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) :=
    {gs | (∑ u : Fin n_B, keptIndicator family t slot_at I_l a u gs)
            < (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ)) + τ} with hgood_def
  have h_good_compl : good = badᶜ := by
    ext gs
    simp only [hgood_def, hbad_def, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  have h_bad_meas : MeasurableSet bad := MeasurableSet.of_discrete
  have h_good_eq : μ good = 1 - μ bad := by
    rw [h_good_compl]; exact MeasureTheory.prob_compl_eq_one_sub h_bad_meas
  have h_bad_le_one : μ bad ≤ 1 := by
    rw [show (1 : ENNReal) = μ Set.univ from (MeasureTheory.measure_univ).symm]
    exact MeasureTheory.measure_mono (Set.subset_univ _)
  have h_good_toReal : (μ good).toReal = 1 - (μ bad).toReal := by
    rw [h_good_eq, ENNReal.toReal_sub_of_le h_bad_le_one ENNReal.one_ne_top]; simp
  have h_bad_le : μ.real bad ≤ Real.exp (- τ^2 /
        (2 * ((n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ)) + τ / 3))) :=
    keptIndicator_sum_upper_tail n_A n_B t ht p hp hp_pos family slot_at h_inj
      I_l h_mem a h_a j h_slot τ hτ h_μ_pos
  change (μ good).toReal ≥ _
  rw [h_good_toReal]
  unfold MeasureTheory.Measure.real at h_bad_le
  linarith

/-- **F.7.4.B a.a.s. headline**: `|T(a, l)|` concentrates within additive
`δ·n_B` of the mean `n_B · p · (1-p)^{|I_l|-1} / t`, a.a.s. as `n_B → ∞`.

The kept-set cardinality is bounded by the sum of kept-indicators across
`u : Fin n_B`. Mirror of `candidateSlot_concentration_aas`.

Requires `slot_at` injective so that `slot_at (σ(a,u)) = I_l` is the
singleton event `σ(a,u) = j` (with unique `j`). -/
theorem keptSet_concentration_aas
    (n_A n_B : ℕ)
    (p : ENNReal) (hp : p ≤ 1) (hp_pos : 0 < p.toReal) (hp_lt : p.toReal < 1)
    (t : ℕ) (ht : 0 < t)
    (family : Finset (Finset (Fin n_A))) (slot_at : Fin t → Finset (Fin n_A))
    (h_inj : Function.Injective slot_at)
    (I_l : Finset (Fin n_A)) (h_mem : I_l ∈ family) (a : Fin n_A) (h_a : a ∈ I_l)
    (j : Fin t) (h_slot : slot_at j = I_l)
    (δ : ℝ) (hδ_pos : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, N ≤ n_B →
      (combinedMeasure n_A n_B t p hp ht).real
        {gs | ((keptSet
                  (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1)
                  family t slot_at I_l a gs.2).card : ℝ)
              < (n_B : ℝ) *
                  (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) + δ)}
      ≥ 1 - ε := by
  classical
  set ρ : ℝ := p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) with hρ_def
  have h_1mp_pos : 0 < 1 - p.toReal := by linarith
  have h_t_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hρ_pos : 0 < ρ := by
    rw [hρ_def]
    exact div_pos (mul_pos hp_pos (pow_pos h_1mp_pos _)) h_t_pos
  -- Chernoff coefficient
  set c : ℝ := δ^2 / (2 * (ρ + δ/3)) with hc_def
  have hρ_plus_δ_third_pos : 0 < ρ + δ/3 := by linarith
  have hc_pos : 0 < c := by rw [hc_def]; positivity
  obtain ⟨N₀, hN₀⟩ := SECRandomBipartite.exists_N_exp_neg_le_eps c ε hc_pos hε
  refine ⟨max N₀ 1, ?_⟩
  intro hN
  have hN₀_le : N₀ ≤ n_B := le_trans (le_max_left _ _) hN
  have hone_le : 1 ≤ n_B := le_trans (le_max_right _ _) hN
  set M : ℝ := (n_B : ℝ) with hM_def
  have h_M_pos : 0 < M := by
    have h1 : 0 < n_B := by omega
    rw [hM_def]; exact_mod_cast h1
  set τ : ℝ := M * δ with hτ_def
  have h_τ_nn : 0 ≤ τ := by rw [hτ_def]; positivity
  have h_μ_pos : 0 < M * ρ := mul_pos h_M_pos hρ_pos
  -- Lower bound on the good event for the kept-indicator sum.
  have h_conc := keptIndicator_sum_concentration_lower n_A n_B t ht p hp hp_pos
    family slot_at h_inj I_l h_mem a h_a j h_slot τ h_τ_nn
    (by rw [← hρ_def, ← hM_def]; exact h_μ_pos)
  -- Rewrite the event using the sum-of-indicators identity for keptSet.
  set μ := combinedMeasure n_A n_B t p hp ht with hμ_def
  -- Sum-side good event = card-side good event.
  set sum_good : Set ((Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) :=
    {gs | (∑ u : Fin n_B, keptIndicator family t slot_at I_l a u gs)
            < M * ρ + τ}
  set card_good : Set ((Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) :=
    {gs | ((keptSet
              (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1)
              family t slot_at I_l a gs.2).card : ℝ)
          < (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) + δ)}
  have h_set_eq : sum_good = card_good := by
    apply Set.eq_of_subset_of_subset
    · intro gs hgs
      have h_sum_lt : (∑ u : Fin n_B, keptIndicator family t slot_at I_l a u gs) < M * ρ + τ :=
        hgs
      have h_arith : M * ρ + τ = M * (ρ + δ) := by rw [hτ_def]; ring
      have h_M_ρ_eq : M * (ρ + δ)
            = (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) + δ) := by
        rw [hM_def, hρ_def]
      change ((keptSet
              (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1)
              family t slot_at I_l a gs.2).card : ℝ)
            < (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) + δ)
      rw [keptSet_card_eq_sum_keptIndicator n_A n_B t family slot_at I_l h_mem a h_a gs]
      rw [← h_M_ρ_eq, ← h_arith]
      exact h_sum_lt
    · intro gs hgs
      have h_card_lt :
            ((keptSet
              (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1)
              family t slot_at I_l a gs.2).card : ℝ)
              < (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) + δ) := hgs
      rw [keptSet_card_eq_sum_keptIndicator n_A n_B t family slot_at I_l h_mem a h_a gs]
        at h_card_lt
      have h_arith : M * ρ + τ = M * (ρ + δ) := by rw [hτ_def]; ring
      have h_M_ρ_eq : M * (ρ + δ)
            = (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) + δ) := by
        rw [hM_def, hρ_def]
      change (∑ u : Fin n_B, keptIndicator family t slot_at I_l a u gs) < M * ρ + τ
      rw [h_arith, h_M_ρ_eq]
      exact h_card_lt
  -- The exp coefficient simplifies to -c·M.
  have h_exp_eq : Real.exp (- τ^2 /
                    (2 * ((n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ))
                          + τ / 3)))
                  = Real.exp (-(c * M)) := by
    congr 1
    rw [show ((n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ)) + τ / 3)
            = M * ρ + τ / 3 from by rw [hM_def, hρ_def]]
    rw [hτ_def, hc_def]
    have hM_ne : M ≠ 0 := ne_of_gt h_M_pos
    have h_denom_ne : (2 : ℝ) * (ρ + δ/3) ≠ 0 := by positivity
    field_simp
  -- h_conc is already in sum_good form (the set definition matches).
  rw [h_set_eq] at h_conc
  rw [h_exp_eq] at h_conc
  have h_exp_le_eps : Real.exp (-(c * M)) ≤ ε := by
    have h_cast : (-(c * M) : ℝ) = -(c * n_B) := by rw [hM_def]
    rw [h_cast]
    exact hN₀ n_B hN₀_le
  linarith

/-- **F.7.4.B a.a.s. headline (lower)**: `|T(a, l)|` is at LEAST
`n_B · (ρ - δ)` a.a.s. as `n_B → ∞`, where `ρ := p · (1-p)^{|I_l|-1} / t`.

Mirror of `keptSet_concentration_aas` invoking R5.a `keptIndicator_sum_lower_tail`
instead of `keptIndicator_sum_upper_tail`. The strictness hypothesis
`δ < ρ` ensures `ρ - δ > 0`, so the lower bound is meaningful.

Used by R5.c `keptSet_concentration_joint_aas_lower` to derive the joint
(Bonferroni-union) lower bound across all `(I_l, a)` pairs. -/
theorem keptSet_concentration_aas_lower
    (n_A n_B : ℕ)
    (p : ENNReal) (hp : p ≤ 1) (hp_pos : 0 < p.toReal) (hp_lt : p.toReal < 1)
    (t : ℕ) (ht : 0 < t)
    (family : Finset (Finset (Fin n_A))) (slot_at : Fin t → Finset (Fin n_A))
    (h_inj : Function.Injective slot_at)
    (I_l : Finset (Fin n_A)) (h_mem : I_l ∈ family) (a : Fin n_A) (h_a : a ∈ I_l)
    (j : Fin t) (h_slot : slot_at j = I_l)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (hδ_lt_ρ : δ < p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, N ≤ n_B →
      (combinedMeasure n_A n_B t p hp ht).real
        {gs | ((keptSet
                  (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1)
                  family t slot_at I_l a gs.2).card : ℝ)
              > (n_B : ℝ) *
                  (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) - δ)}
      ≥ 1 - ε := by
  classical
  set ρ : ℝ := p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) with hρ_def
  have h_1mp_pos : 0 < 1 - p.toReal := by linarith
  have h_t_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hρ_pos : 0 < ρ := by
    rw [hρ_def]
    exact div_pos (mul_pos hp_pos (pow_pos h_1mp_pos _)) h_t_pos
  -- Chernoff coefficient (note the MINUS — `δ < ρ` ensures denominator is positive).
  set c : ℝ := δ^2 / (2 * (ρ - δ/3)) with hc_def
  have hδ_lt_ρ' : δ < ρ := by rw [hρ_def]; exact hδ_lt_ρ
  have hρ_minus_δ_third_pos : 0 < ρ - δ/3 := by linarith
  have hc_pos : 0 < c := by rw [hc_def]; positivity
  obtain ⟨N₀, hN₀⟩ := SECRandomBipartite.exists_N_exp_neg_le_eps c ε hc_pos hε
  refine ⟨max N₀ 1, ?_⟩
  intro hN
  have hN₀_le : N₀ ≤ n_B := le_trans (le_max_left _ _) hN
  have hone_le : 1 ≤ n_B := le_trans (le_max_right _ _) hN
  set M : ℝ := (n_B : ℝ) with hM_def
  have h_M_pos : 0 < M := by
    have h1 : 0 < n_B := by omega
    rw [hM_def]; exact_mod_cast h1
  set τ : ℝ := M * δ with hτ_def
  have h_τ_nn : 0 ≤ τ := by rw [hτ_def]; positivity
  have h_μ_pos : 0 < M * ρ := mul_pos h_M_pos hρ_pos
  have h_τ_lt_μ : τ < M * ρ := by
    rw [hτ_def]
    exact mul_lt_mul_of_pos_left hδ_lt_ρ' h_M_pos
  set μ := combinedMeasure n_A n_B t p hp ht with hμ_def
  -- Apply R5.a to bound the bad (lower-tail) event from above.
  have h_lower := keptIndicator_sum_lower_tail n_A n_B t ht p hp hp_pos
    family slot_at h_inj I_l h_mem a h_a j h_slot τ h_τ_nn
    (by rw [← hρ_def, ← hM_def]; exact h_τ_lt_μ)
    (by rw [← hρ_def, ← hM_def]; exact h_μ_pos)
  -- The complement of the bad event is the good event (sum > M·ρ - τ).
  set bad : Set ((Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) :=
    {gs | ∑ u : Fin n_B, keptIndicator family t slot_at I_l a u gs
          ≤ (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ)) - τ}
    with hbad_def
  set sum_good : Set ((Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) :=
    {gs | (∑ u : Fin n_B, keptIndicator family t slot_at I_l a u gs)
            > M * ρ - τ}
    with hsg_def
  have h_sg_compl : sum_good = badᶜ := by
    ext gs
    simp only [hsg_def, hbad_def, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    rw [← hM_def, ← hρ_def]
  have h_bad_meas : MeasurableSet bad := MeasurableSet.of_discrete
  have h_univ_one : μ.real Set.univ = 1 := by
    rw [MeasureTheory.measureReal_def]; simp [MeasureTheory.measure_univ]
  have h_sg_real : μ.real sum_good = 1 - μ.real bad := by
    rw [h_sg_compl, MeasureTheory.measureReal_compl h_bad_meas, h_univ_one]
  -- Card-side good event = sum-side good event.
  set card_good : Set ((Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t)) :=
    {gs | ((keptSet
              (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1)
              family t slot_at I_l a gs.2).card : ℝ)
          > (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) - δ)}
    with hcg_def
  have h_set_eq : sum_good = card_good := by
    apply Set.eq_of_subset_of_subset
    · intro gs hgs
      have h_sum_gt : (∑ u : Fin n_B, keptIndicator family t slot_at I_l a u gs)
            > M * ρ - τ := hgs
      have h_arith : M * ρ - τ = M * (ρ - δ) := by rw [hτ_def]; ring
      have h_M_ρ_eq : M * (ρ - δ)
            = (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) - δ) := by
        rw [hM_def, hρ_def]
      change ((keptSet
              (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1)
              family t slot_at I_l a gs.2).card : ℝ)
            > (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) - δ)
      rw [keptSet_card_eq_sum_keptIndicator n_A n_B t family slot_at I_l h_mem a h_a gs]
      rw [← h_M_ρ_eq, ← h_arith]
      exact h_sum_gt
    · intro gs hgs
      have h_card_gt :
            ((keptSet
              (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1)
              family t slot_at I_l a gs.2).card : ℝ)
              > (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) - δ) := hgs
      rw [keptSet_card_eq_sum_keptIndicator n_A n_B t family slot_at I_l h_mem a h_a gs]
        at h_card_gt
      have h_arith : M * ρ - τ = M * (ρ - δ) := by rw [hτ_def]; ring
      have h_M_ρ_eq : M * (ρ - δ)
            = (n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ) - δ) := by
        rw [hM_def, hρ_def]
      change (∑ u : Fin n_B, keptIndicator family t slot_at I_l a u gs) > M * ρ - τ
      rw [h_arith, h_M_ρ_eq]
      exact h_card_gt
  -- The exp coefficient simplifies to -c·M.
  have h_exp_eq : Real.exp (- τ^2 /
                    (2 * ((n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ))
                          - τ / 3)))
                  = Real.exp (-(c * M)) := by
    congr 1
    rw [show ((n_B : ℝ) * (p.toReal * (1 - p.toReal) ^ (I_l.card - 1) / (t : ℝ)) - τ / 3)
            = M * ρ - τ / 3 from by rw [hM_def, hρ_def]]
    rw [hτ_def, hc_def]
    have hM_ne : M ≠ 0 := ne_of_gt h_M_pos
    have h_denom_ne : (2 : ℝ) * (ρ - δ/3) ≠ 0 := by
      have : (0 : ℝ) < 2 * (ρ - δ/3) := by linarith
      exact this.ne'
    field_simp
  rw [h_exp_eq] at h_lower
  -- Convert μ.real(card_good) ≥ 1 - ε via the sum-good = card-good bridge.
  have h_card_real : μ.real card_good = 1 - μ.real bad := by
    rw [← h_set_eq, h_sg_real]
  have h_exp_le_eps : Real.exp (-(c * M)) ≤ ε := by
    have h_cast : (-(c * M) : ℝ) = -(c * n_B) := by rw [hM_def]
    rw [h_cast]
    exact hN₀ n_B hN₀_le
  unfold MeasureTheory.Measure.real at h_lower
  change μ.real card_good ≥ 1 - ε
  rw [h_card_real]
  unfold MeasureTheory.Measure.real
  linarith

/-! ## F.7-Step-D — Marginalisation: `combinedMeasure` graph-only events → `bipartiteRandomMeasure`

The joint product measure `combinedMeasure = bipartiteEdgeChoice.toMeasure ×ₘ
slotAssignmentChoice.toMeasure` projects onto the graph axis as
`bipartiteEdgeChoice.toMeasure`, since the σ-axis (slot assignment) is a
probability measure and integrates to 1.

For a *graph-only* event of the form `{gs | event (boolToBipartiteGraph gs.1)}`
this lets us identify the joint measure with the bipartite random graph
measure `bipartiteRandomMeasure`, eliminating the σ-axis. The two
marginalisation directions:

* `combinedMeasure_marginal_eq_edgeChoice`: graph-only joint event measure
  equals the same event under `bipartiteEdgeChoice.toMeasure` (raw Bool-fn
  measure).

* `combinedMeasure_marginal_eq_bipartiteRandomMeasure`: composing with
  `bipartiteRandomMeasure_eq_preimage`, the same joint event measure equals
  the projected event measure on `SimpleGraph` under `bipartiteRandomMeasure`.

This is the load-bearing bridge for transferring joint-good-event lower
bounds (Step A on `combinedMeasure`) to graph-only existence statements
(`perPair_packing_aas_FKS` on `bipartiteRandomMeasure`). -/

/-- **Marginalisation (raw)**: a graph-only event has the same measure
under `combinedMeasure` as under `bipartiteEdgeChoice.toMeasure` (with the
σ-axis integrated out, since `slotAssignmentChoice.toMeasure` is a
probability measure on its space).

This is the key technical bridge: σ-axis events factorise as
`E_graph ×ˢ Set.univ`, and `Measure.prod_prod` reduces this to
`μ_graph(E_graph) · 1`. -/
lemma combinedMeasure_marginal_eq_edgeChoice
    (n_A n_B t : ℕ) (ht : 0 < t) (p : ENNReal) (hp : p ≤ 1)
    (E : Set (Fin n_A × Fin n_B → Bool)) :
    (combinedMeasure n_A n_B t p hp ht)
        {gs : (Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t) | gs.1 ∈ E}
      = (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure E := by
  classical
  -- Rewrite the event as a product `E ×ˢ Set.univ`.
  have h_set_eq :
      {gs : (Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t) | gs.1 ∈ E}
        = E ×ˢ (Set.univ : Set (Fin n_A × Fin n_B → Fin t)) := by
    ext gs
    simp [Set.mem_prod]
  rw [h_set_eq]
  unfold combinedMeasure
  rw [MeasureTheory.Measure.prod_prod]
  -- ν(univ) = 1 by IsProbabilityMeasure.
  rw [MeasureTheory.measure_univ, mul_one]

/-- **Marginalisation (graph form)**: a `SimpleGraph`-level event has the same
measure under `combinedMeasure` (projected through `boolToBipartiteGraph`)
as under `bipartiteRandomMeasure` directly.

Composes `combinedMeasure_marginal_eq_edgeChoice` with
`bipartiteRandomMeasure_eq_preimage`. -/
lemma combinedMeasure_marginal_eq_bipartiteRandomMeasure
    (n_A n_B t : ℕ) (ht : 0 < t) (p : ENNReal) (hp : p ≤ 1)
    (S : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)))
    (hS : MeasurableSet S) :
    (combinedMeasure n_A n_B t p hp ht)
        {gs : (Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t) |
          DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1 ∈ S}
      = DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B p hp S := by
  classical
  -- Rewrite the LHS event as `gs.1 ∈ (preimage S)`.
  have h_set_eq :
      {gs : (Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t) |
        DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1 ∈ S}
        = {gs | gs.1 ∈ (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph ⁻¹' S)} := by
    ext gs; rfl
  rw [h_set_eq]
  rw [combinedMeasure_marginal_eq_edgeChoice n_A n_B t ht p hp
      (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph ⁻¹' S)]
  rw [DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure_eq_preimage p hp hS]

/-- **Marginalisation (Measure.real form)**: real-valued version of
`combinedMeasure_marginal_eq_bipartiteRandomMeasure`. Used by Step-D to
convert joint-good-event lower bounds on `combinedMeasure` to
`bipartiteRandomMeasure` lower bounds. -/
lemma combinedMeasure_marginal_real_eq_bipartiteRandomMeasure
    (n_A n_B t : ℕ) (ht : 0 < t) (p : ENNReal) (hp : p ≤ 1)
    (S : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)))
    (hS : MeasurableSet S) :
    (combinedMeasure n_A n_B t p hp ht).real
        {gs : (Fin n_A × Fin n_B → Bool) × (Fin n_A × Fin n_B → Fin t) |
          DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph gs.1 ∈ S}
      = (DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B p hp).real S := by
  unfold MeasureTheory.Measure.real
  rw [combinedMeasure_marginal_eq_bipartiteRandomMeasure n_A n_B t ht p hp S hS]

end DaveyThesis2024.SecRandomBipartite.SlotAssignment
