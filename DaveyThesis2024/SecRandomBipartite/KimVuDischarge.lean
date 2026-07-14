/-
Copyright (c) 2026 Ross Kang.
Released under Apache 2.0 license.

# Kim–Vu discharge for the bipartite SEC count polynomial — L3 (independence integral)

This file connects the generic discrete-derivative calculus in `KimVuEffects` to the
concrete bipartite edge-choice measure. Step L3: the integral of a product of `monoH`
per-slot factors over a slot set factorises (slots are independent under the product
Bernoulli measure), giving `∏ (per-slot expectation)`.
-/

import DaveyThesis2024.SecRandomBipartite.KimVuEffects
import DaveyThesis2024.BipartiteRandomGraph

namespace DaveyThesis2024.SecRandomBipartite.KimVu

open MeasureTheory DaveyThesis2024.BipartiteRandomGraph

variable {n_A n_B : ℕ}

open ProbabilityTheory

/-- Every real-valued function on the finite (discrete) bipartite slot space is
integrable w.r.t. the bipartite edge-choice probability measure: it is measurable
(discrete σ-algebra) and bounded (finite domain), and the measure is finite. -/
private lemma integrable_of_discrete_finite
    (p : ENNReal) (hp : p ≤ 1) (h : (Fin n_A × Fin n_B → Bool) → ℝ) :
    MeasureTheory.Integrable h ((bipartiteEdgeChoice n_A n_B p hp).toMeasure) := by
  classical
  haveI : IsProbabilityMeasure ((bipartiteEdgeChoice n_A n_B p hp).toMeasure) := inferInstance
  -- Bound: the supremum of |h| over the finite domain.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ f, ‖h f‖ ≤ C := by
    rcases Finset.exists_le (Finset.univ.image (fun f => ‖h f‖)) with ⟨C, hC⟩
    refine ⟨C, fun f => ?_⟩
    exact hC ‖h f‖ (Finset.mem_image.2 ⟨f, Finset.mem_univ f, rfl⟩)
  exact (MeasureTheory.memLp_top_of_bound Measurable.of_discrete.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)).integrable le_top

/-- **L3a: single-slot expectation of a `monoH` factor.**
`∫ monoH S T i (g i) = p` if `i ∈ S`, `1−p` if `i ∈ T`, `1` otherwise. -/
lemma integral_monoH_single
    (S T : Finset (Fin n_A × Fin n_B)) (i : Fin n_A × Fin n_B)
    (p : ENNReal) (hp : p ≤ 1) :
    ∫ g, monoH S T i (g i) ∂((bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      = if i ∈ S then p.toReal else if i ∈ T then (1 - p.toReal) else 1 := by
  classical
  haveI : IsProbabilityMeasure ((bipartiteEdgeChoice n_A n_B p hp).toMeasure) := inferInstance
  -- The indicator `fun g => if g i = true then 1 else 0` equals `edgeIndicator i.1 i.2`.
  have h_ind : (fun g : Fin n_A × Fin n_B → Bool => (if g i = true then (1 : ℝ) else 0))
      = edgeIndicator i.1 i.2 := by
    funext g
    rw [edgeIndicator_apply]
  by_cases hS : i ∈ S
  · simp only [monoH, if_pos hS]
    rw [h_ind, integral_edgeIndicator_eq p hp]
  · by_cases hT : i ∈ T
    · simp only [monoH, if_neg hS, if_pos hT]
      -- integrand: 1 - (if g i = true then 1 else 0) = 1 - edgeIndicator i.1 i.2 g
      have hrw : (fun g : Fin n_A × Fin n_B → Bool =>
          (1 : ℝ) - (if g i = true then (1 : ℝ) else 0))
          = (fun g => (1 : ℝ) - edgeIndicator i.1 i.2 g) := by
        funext g; rw [edgeIndicator_apply]
      rw [hrw]
      rw [MeasureTheory.integral_sub (integrable_const 1)
        (integrable_of_discrete_finite p hp (edgeIndicator i.1 i.2))]
      rw [integral_edgeIndicator_eq p hp, MeasureTheory.integral_const]
      simp
    · simp only [monoH, if_neg hS, if_neg hT]
      rw [MeasureTheory.integral_const]
      simp

/-- **L3: product-integral over a slot set factorises (independence).**
`∫ ∏_{i∈U} monoH S T i (g i) = ∏_{i∈U} (per-slot expectation)`. -/
lemma integral_prod_monoH
    (S T U : Finset (Fin n_A × Fin n_B))
    (p : ENNReal) (hp : p ≤ 1) :
    ∫ g, (∏ i ∈ U, monoH S T i (g i)) ∂((bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      = ∏ i ∈ U, (if i ∈ S then p.toReal else if i ∈ T then (1 - p.toReal) else 1) := by
  classical
  set μ := (bipartiteEdgeChoice n_A n_B p hp).toMeasure with hμ
  haveI : IsProbabilityMeasure μ := inferInstance
  -- Per-coordinate factor function: `monoH` on slots of `U`, `1` elsewhere.
  let fU : (Fin n_A × Fin n_B) → Bool → ℝ :=
    fun i b => if i ∈ U then monoH S T i b else 1
  -- Coordinate independence on the full grid, transported through the pi bridge.
  have h_coord : iIndepFun
      (fun (i : Fin n_A × Fin n_B) (g : Fin n_A × Fin n_B → Bool) => g i) μ := by
    rw [hμ, bipartiteEdgeChoice_toMeasure_eq_pi p hp]
    haveI : IsProbabilityMeasure ((slotPMF p hp).toMeasure) := inferInstance
    exact iIndepFun_pi (X := fun (_ : Fin n_A × Fin n_B) (b : Bool) => b)
      (fun _ => Measurable.of_discrete.aemeasurable)
  -- Compose to get independence of the padded `monoH` factor family.
  have h_indep : iIndepFun (fun (i : Fin n_A × Fin n_B) (g : Fin n_A × Fin n_B → Bool) =>
      fU i (g i)) μ :=
    h_coord.comp (fun i => fU i) (fun _ => Measurable.of_discrete)
  -- Integral of the full-grid product factorises.
  have h_prod := h_indep.integral_fun_prod_eq_prod_integral
    (fun i => Measurable.of_discrete.aestronglyMeasurable)
  -- The full-grid product of `fU i (g i)` equals the `U`-restricted product of `monoH`.
  have h_lhs : (fun g : Fin n_A × Fin n_B → Bool => ∏ i, fU i (g i))
      = (fun g => ∏ i ∈ U, monoH S T i (g i)) := by
    funext g
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ U)]
    have h1 : (∏ i ∈ Finset.univ.filter (· ∈ U), fU i (g i))
        = ∏ i ∈ U, monoH S T i (g i) := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact Finset.prod_congr rfl (fun i hi => by simp only [fU, if_pos hi])
    have h2 : (∏ i ∈ Finset.univ.filter (fun i => ¬ i ∈ U), fU i (g i)) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp only [fU, if_neg hi.2]
    rw [h1, h2, mul_one]
  -- Transport the integral identity to the goal shape.
  rw [hμ] at h_prod ⊢
  rw [show (fun g : Fin n_A × Fin n_B → Bool => ∏ i ∈ U, monoH S T i (g i))
      = (fun g => ∏ i, fU i (g i)) from h_lhs.symm] at *
  -- Now `h_prod : ∫ g, ∏ i, fU i (g i) = ∏ i, ∫ g, fU i (g i)`.
  rw [h_prod]
  -- Reduce the full-grid product of per-slot integrals to a `U`-product.
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ U)]
  have hU : (∏ i ∈ Finset.univ.filter (· ∈ U), ∫ g, fU i (g i)
        ∂((bipartiteEdgeChoice n_A n_B p hp).toMeasure))
      = ∏ i ∈ U, (if i ∈ S then p.toReal else if i ∈ T then (1 - p.toReal) else 1) := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have : (fun g : Fin n_A × Fin n_B → Bool => fU i (g i))
        = (fun g => monoH S T i (g i)) := by
      funext g; simp only [fU, if_pos hi]
    rw [this, integral_monoH_single S T i p hp]
  have hUc : (∏ i ∈ Finset.univ.filter (fun i => ¬ i ∈ U), ∫ g, fU i (g i)
        ∂((bipartiteEdgeChoice n_A n_B p hp).toMeasure)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    simp only [Finset.mem_filter] at hi
    have : (fun g : Fin n_A × Fin n_B → Bool => fU i (g i)) = (fun _ => (1 : ℝ)) := by
      funext g; simp only [fU, if_neg hi.2]
    rw [this, MeasureTheory.integral_const]
    simp
  rw [hU, hUc, mul_one]

end DaveyThesis2024.SecRandomBipartite.KimVu
