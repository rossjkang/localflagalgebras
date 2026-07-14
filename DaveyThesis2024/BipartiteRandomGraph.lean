/-
Copyright (c) 2026 Ross Kang.
Released under Apache 2.0 license.

# The bipartite Erdős–Rényi random graph `G(n_A, n_B, p)` as a PMF

Phase Refactor-1 (Option 1 of `axiom_decomposition_plan.md`): build the
Erdős–Rényi bipartite random graph as a Mathlib `PMF`, then use
`PMF.toMeasure` to get a probability measure. This will replace the
opaque `probBipartiteRandom` axiom with a Lean-defined function.

## Design (pattern from `heftyhornkingpfender2026/TwoBites/ConcreteProbability.lean`)

```
sample space (raw):  Fin n_A × Fin n_B → Bool     -- one Bernoulli per cross-pair
edge-indicator PMF:  bipartiteEdgeChoice p       -- product Bernoulli
graph map:           boolToBipartiteGraph        -- (Bool fn) → SimpleGraph
graph PMF:           bipartiteErPMF p             -- = edgeChoice.map boolToBipartiteGraph
```

## Status

Phase 1 (this file): foundation — `boolToBipartiteGraph` and basic
properties. The PMF + measure layers come in subsequent cycles.
-/
import DaveyThesis2024.Concentration
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.ENNReal.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Independence.Basic



namespace DaveyThesis2024.BipartiteRandomGraph

open SimpleGraph

variable {n_A n_B : ℕ}

/-! ## Step 1: Bool-valued edge selector to bipartite SimpleGraph -/

/-- The underlying symmetric, irreflexive relation for the bipartite random graph.
`bipartiteRel f x y` holds iff `{x, y}` is a cross-pair `{Sum.inl a, Sum.inr b}` and
`f (a, b) = true`. -/
def bipartiteRel (f : Fin n_A × Fin n_B → Bool) :
    (Fin n_A ⊕ Fin n_B) → (Fin n_A ⊕ Fin n_B) → Prop :=
  fun x y => (∃ a b, x = Sum.inl a ∧ y = Sum.inr b ∧ f (a, b) = true) ∨
             (∃ a b, x = Sum.inr b ∧ y = Sum.inl a ∧ f (a, b) = true)

/-- Convert a Bool-valued cross-edge selector to a bipartite `SimpleGraph`.
An edge `{Sum.inl a, Sum.inr b}` is in the resulting graph iff `f (a, b) = true`.
No within-side edges exist (bipartite). -/
def boolToBipartiteGraph (f : Fin n_A × Fin n_B → Bool) :
    SimpleGraph (Fin n_A ⊕ Fin n_B) := SimpleGraph.fromRel (bipartiteRel f)

theorem boolToBipartiteGraph_adj_inl_inr (f : Fin n_A × Fin n_B → Bool)
    (a : Fin n_A) (b : Fin n_B) :
    (boolToBipartiteGraph f).Adj (Sum.inl a) (Sum.inr b) ↔ f (a, b) = true := by
  simp [boolToBipartiteGraph, SimpleGraph.fromRel, bipartiteRel]

theorem boolToBipartiteGraph_adj_inr_inl (f : Fin n_A × Fin n_B → Bool)
    (b : Fin n_B) (a : Fin n_A) :
    (boolToBipartiteGraph f).Adj (Sum.inr b) (Sum.inl a) ↔ f (a, b) = true := by
  simp [boolToBipartiteGraph, SimpleGraph.fromRel, bipartiteRel]

theorem boolToBipartiteGraph_not_adj_inl_inl (f : Fin n_A × Fin n_B → Bool)
    (a₁ a₂ : Fin n_A) :
    ¬ (boolToBipartiteGraph f).Adj (Sum.inl a₁) (Sum.inl a₂) := by
  simp [boolToBipartiteGraph, SimpleGraph.fromRel, bipartiteRel]

theorem boolToBipartiteGraph_not_adj_inr_inr (f : Fin n_A × Fin n_B → Bool)
    (b₁ b₂ : Fin n_B) :
    ¬ (boolToBipartiteGraph f).Adj (Sum.inr b₁) (Sum.inr b₂) := by
  simp [boolToBipartiteGraph, SimpleGraph.fromRel, bipartiteRel]

/-! ## Step 2: independent-Bernoulli PMF over `Fin n_A × Fin n_B → Bool`

For each cross-edge slot `(a, b)`, draw `Bernoulli(p)` independently;
combine into a function `f : Fin n_A × Fin n_B → Bool`. The probability
of a specific `f` is `∏_(a,b) (if f (a,b) then p else (1-p))`.
Summing over all `f` factors as `∏_(a,b) (p + (1-p)) = 1`. -/

open scoped ENNReal

/-- Edge weight at a single cross-pair: `p` if selected, `1 - p` if not. -/
@[simp] noncomputable def edgeWeight (p : ENNReal) (b : Bool) : ENNReal :=
  if b then p else 1 - p

lemma sum_edgeWeight_eq_one {p : ENNReal} (hp : p ≤ 1) :
    ∑ b : Bool, edgeWeight p b = 1 := by
  simp only [Fintype.sum_bool, edgeWeight, if_true]
  exact add_tsub_cancel_of_le hp

lemma sum_prod_edgeWeight_eq_one {p : ENNReal} (hp : p ≤ 1) (n_A n_B : ℕ) :
    (∑ f : Fin n_A × Fin n_B → Bool,
      ∏ e : Fin n_A × Fin n_B, edgeWeight p (f e)) = 1 := by
  classical
  rw [← Fintype.prod_sum (κ := fun _ : Fin n_A × Fin n_B => Bool)
        (fun _ b => edgeWeight p b)]
  rw [Finset.prod_congr rfl (fun e _ => sum_edgeWeight_eq_one hp)]
  exact Finset.prod_const_one

/-- The product-Bernoulli PMF on `Fin n_A × Fin n_B → Bool`: each cross-edge slot
independently picks Bernoulli(p). -/
noncomputable def bipartiteEdgeChoice (n_A n_B : ℕ) (p : ENNReal) (hp : p ≤ 1) :
    PMF (Fin n_A × Fin n_B → Bool) :=
  PMF.ofFintype (fun f => ∏ e : Fin n_A × Fin n_B, edgeWeight p (f e))
    (sum_prod_edgeWeight_eq_one hp n_A n_B)

@[simp] theorem bipartiteEdgeChoice_apply {n_A n_B : ℕ} (p : ENNReal) (hp : p ≤ 1)
    (f : Fin n_A × Fin n_B → Bool) :
    bipartiteEdgeChoice n_A n_B p hp f =
      ∏ e : Fin n_A × Fin n_B, edgeWeight p (f e) :=
  PMF.ofFintype_apply _ _

/-! ## Step 3: Bipartite Erdős–Rényi PMF on the graph type itself -/

/-- The bipartite Erdős–Rényi PMF `G(n_A, n_B, p)` on `SimpleGraph (Fin n_A ⊕ Fin n_B)`:
push the product-Bernoulli edge selector through `boolToBipartiteGraph`. -/
noncomputable def bipartiteErPMF (n_A n_B : ℕ) (p : ENNReal) (hp : p ≤ 1) :
    PMF (SimpleGraph (Fin n_A ⊕ Fin n_B)) :=
  (bipartiteEdgeChoice n_A n_B p hp).map boolToBipartiteGraph

/-! ## Step 4: Bridge to MeasureTheory — define the measure + probability function

Davey's Mathlib (v4.28.0) does not include the `MeasurableSpace SimpleGraph`
instance (added in a later Mathlib version). We declare it locally as the
discrete `⊤` structure, which is correct for the finite type
`SimpleGraph (Fin n_A ⊕ Fin n_B)`. -/

open MeasureTheory

instance simpleGraphFinSumMeasurableSpace :
    MeasurableSpace (SimpleGraph (Fin n_A ⊕ Fin n_B)) := ⊤

/-- The bipartite Erdős–Rényi probability measure on `SimpleGraph (Fin n_A ⊕ Fin n_B)`,
obtained from `bipartiteErPMF` via `PMF.toMeasure`. -/
noncomputable def bipartiteRandomMeasure (n_A n_B : ℕ) (p : ENNReal) (hp : p ≤ 1) :
    Measure (SimpleGraph (Fin n_A ⊕ Fin n_B)) :=
  (bipartiteErPMF n_A n_B p hp).toMeasure

/-- The measure is a probability measure (total mass 1). Automatically derived from `PMF`. -/
instance bipartiteRandomMeasure_isProbabilityMeasure
    (n_A n_B : ℕ) (p : ENNReal) (hp : p ≤ 1) :
    IsProbabilityMeasure (bipartiteRandomMeasure n_A n_B p hp) := by
  unfold bipartiteRandomMeasure
  infer_instance

/-- The probability of an event `E` under the bipartite Erdős–Rényi model
`G ~ G(n_A, n_B, p)`. Returns 0 if the probability parameter is outside `[0, 1]`.

This **replaces** the axiom `probBipartiteRandom` from earlier development —
Phase Refactor-1.E will substitute this concrete definition into `SECRandomBipartite.lean`. -/
noncomputable def probBipartiteRandomConcrete (n_A n_B : ℕ) (p : ℝ)
    (event : SimpleGraph (Fin n_A ⊕ Fin n_B) → Prop) : ℝ :=
  if hp : ENNReal.ofReal p ≤ 1 then
    ((bipartiteRandomMeasure n_A n_B (ENNReal.ofReal p) hp) {G | event G}).toReal
  else 0

/-! ## Step 5: Degree as a function of the edge selector

For each vertex `Sum.inl a`, the degree in `boolToBipartiteGraph f` equals
the number of `b : Fin n_B` such that `f (a, b) = true`. This is needed to
connect `Δ_A` to a sum of Bernoulli indicators for Chernoff. -/

/-- Number of edges incident to A-vertex `a` in the bipartite graph from
    selector `f`. -/
def degAOfSelector (f : Fin n_A × Fin n_B → Bool) (a : Fin n_A) : ℕ :=
  ((Finset.univ : Finset (Fin n_B)).filter (fun b => f (a, b) = true)).card

/-- Number of edges incident to B-vertex `b`. Symmetric. -/
def degBOfSelector (f : Fin n_A × Fin n_B → Bool) (b : Fin n_B) : ℕ :=
  ((Finset.univ : Finset (Fin n_A)).filter (fun a => f (a, b) = true)).card

/-- The bipartite graph's adjacency is decidable (classical, since we don't
need computability for measure-theoretic reasoning). -/
noncomputable instance boolToBipartiteGraph_decidableAdj
    (f : Fin n_A × Fin n_B → Bool) :
    DecidableRel (boolToBipartiteGraph f).Adj := by
  intro x y
  exact Classical.dec _

/-- Single-edge indicator: 1 if `f (a, b) = true`, 0 otherwise.
The collection `{edgeIndicator a b}_b` for fixed `a` are the indicator
random variables whose sum is `degAOfSelector f a`. -/
noncomputable def edgeIndicator (a : Fin n_A) (b : Fin n_B) :
    (Fin n_A × Fin n_B → Bool) → ℝ :=
  fun f => if f (a, b) = true then 1 else 0

@[simp] lemma edgeIndicator_apply (a : Fin n_A) (b : Fin n_B)
    (f : Fin n_A × Fin n_B → Bool) :
    edgeIndicator a b f = if f (a, b) = true then 1 else 0 := rfl

/-- Indicators take values in `{0, 1}`. -/
lemma edgeIndicator_indicator (a : Fin n_A) (b : Fin n_B)
    (f : Fin n_A × Fin n_B → Bool) :
    edgeIndicator a b f = 0 ∨ edgeIndicator a b f = 1 := by
  unfold edgeIndicator
  by_cases h : f (a, b) = true <;> simp [h]

/-- Sum of indicators for fixed `a` equals the degree count. -/
lemma sum_edgeIndicator_eq_degA (a : Fin n_A) (f : Fin n_A × Fin n_B → Bool) :
    (∑ b : Fin n_B, edgeIndicator a b f) = (degAOfSelector f a : ℝ) := by
  unfold edgeIndicator degAOfSelector
  rw [Finset.sum_boole]

/-- Measurability of `edgeIndicator a b` from `(Fin n_A × Fin n_B → Bool)` (carrying
the discrete σ-algebra on `Bool`-valued functions) to `ℝ` (Borel).

Since the source is a finite type with the discrete σ-algebra, *every* function
is measurable. -/
lemma measurable_edgeIndicator (a : Fin n_A) (b : Fin n_B) :
    Measurable (edgeIndicator a b) := by
  -- Source is finite ⟹ discrete σ-algebra ⟹ all functions measurable.
  exact Measurable.of_discrete

/-! ## Step 6: Expectation of edgeIndicator under bipartiteEdgeChoice

The probability that a specific edge slot is `true` under the product PMF
equals `p`. This is marginalization: the sum over `f` with `f(a,b) = true`
of `∏ e, edgeWeight p (f e)` factors as `edgeWeight p true · 1 = p`. The
expectation lemma `h_p_eq` follows from this via `integral_indicator`. -/

lemma bipartiteEdgeChoice_apply_at_eq_true (p : ENNReal) (hp : p ≤ 1)
    (a : Fin n_A) (b : Fin n_B) :
    (bipartiteEdgeChoice n_A n_B p hp).toMeasure {f | f (a, b) = true} = p := by
  classical
  have hms : MeasurableSet {f : Fin n_A × Fin n_B → Bool | f (a, b) = true} :=
    MeasurableSet.of_discrete
  rw [(bipartiteEdgeChoice n_A n_B p hp).toMeasure_apply hms]
  rw [tsum_eq_sum (s := (Finset.univ : Finset (Fin n_A × Fin n_B → Bool)))
        (fun f hf => absurd (Finset.mem_univ f) hf)]
  simp only [Set.indicator_apply, Set.mem_setOf_eq, bipartiteEdgeChoice_apply]
  rw [← Finset.sum_filter, Finset.sum_filter]
  -- Goal: ∑ f, if f(a,b)=true then ∏ e, edgeWeight p (f e) else 0 = p.
  -- Absorb the constraint into a per-slot indicator (1 at the target slot if f=true,
  -- 0 otherwise; 1 everywhere else).
  have key : ∀ f : Fin n_A × Fin n_B → Bool,
      (if f (a, b) = true then ∏ e : Fin n_A × Fin n_B, edgeWeight p (f e) else 0)
        = ∏ e : Fin n_A × Fin n_B,
            edgeWeight p (f e) * (if e = (a, b) ∧ f e = false then 0 else 1) := by
    intro f
    by_cases h : f (a, b) = true
    · rw [if_pos h]
      refine Finset.prod_congr rfl (fun e _ => ?_)
      by_cases he : e = (a, b)
      · subst he; simp [h]
      · simp [he]
    · rw [if_neg h]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ (a, b))
      have hf : f (a, b) = false := by simpa using h
      simp [hf]
  simp_rw [key]
  -- Commute sum and product via Fintype.prod_sum.
  rw [← Fintype.prod_sum (κ := fun _ : Fin n_A × Fin n_B => Bool)
        (fun e β => edgeWeight p β * (if e = (a, b) ∧ β = false then 0 else 1))]
  -- Per-slot evaluation: at the (a,b) slot we get p; everywhere else we get 1.
  have per_slot : ∀ e : Fin n_A × Fin n_B,
      (∑ β : Bool, edgeWeight p β * (if e = (a, b) ∧ β = false then 0 else 1))
        = if e = (a, b) then p else 1 := by
    intro e
    simp only [Fintype.sum_bool, edgeWeight]
    by_cases he : e = (a, b)
    · simp [he]
    · simp [he, add_tsub_cancel_of_le hp]
  rw [Finset.prod_congr rfl (fun e _ => per_slot e)]
  -- ∏ e ∈ univ, (if e = (a,b) then p else 1) = p
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  -- ⊢ p ^ ((Finset.univ : Finset _).filter (· = (a, b))).card = p
  -- The filter has exactly one element (a, b), card = 1, so p^1 = p.
  have hcard : ((Finset.univ : Finset (Fin n_A × Fin n_B)).filter (· = (a, b))).card = 1 := by
    simp [Finset.filter_eq']
  rw [hcard, pow_one]

/-! ## Pi-measure bridge

We exhibit `(bipartiteEdgeChoice n_A n_B p hp).toMeasure` as a literal `Measure.pi`
of per-slot Bernoulli measures. Combined with Mathlib's `iIndepFun_pi` this
proves the edge-indicator independence (eliminating two domain axioms). -/

/-- The per-slot Bernoulli PMF on `Bool`: probability `p` for `true`, `1 - p` for
`false`. Identical in content to `PMF.bernoulli` but parametrised by `ENNReal`
directly so it matches `edgeWeight`. -/
noncomputable def slotPMF (p : ENNReal) (hp : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b : Bool => edgeWeight p b) (sum_edgeWeight_eq_one hp)

@[simp] lemma slotPMF_apply (p : ENNReal) (hp : p ≤ 1) (b : Bool) :
    slotPMF p hp b = edgeWeight p b :=
  PMF.ofFintype_apply _ _

/-- The probability measure on `Fin n_A × Fin n_B → Bool` underlying
`bipartiteEdgeChoice` is the `Measure.pi` of independent per-slot Bernoulli
measures. This is the key bridge to Mathlib's `iIndepFun_pi`. -/
lemma bipartiteEdgeChoice_toMeasure_eq_pi (p : ENNReal) (hp : p ≤ 1) :
    (bipartiteEdgeChoice n_A n_B p hp).toMeasure
      = Measure.pi (fun _ : Fin n_A × Fin n_B => (slotPMF p hp).toMeasure) := by
  -- Both are probability measures on a finite (hence countable) space; it
  -- suffices to check agreement on singletons.
  refine Measure.ext_of_singleton ?_
  intro f
  -- LHS: PMF value at f = ∏ e, edgeWeight p (f e).
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton f),
    bipartiteEdgeChoice_apply]
  -- RHS: ∏ e, (slotPMF p hp).toMeasure {f e} = ∏ e, edgeWeight p (f e).
  rw [Measure.pi_singleton]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (f e)), slotPMF_apply]

open ProbabilityTheory in
/-- **Independence of edge indicators.**

For fixed `a : Fin n_A`, the family `(edgeIndicator a · : Fin n_B → ...)`
of indicator random variables is mutually independent under the bipartite
edge-choice measure.

Proof sketch: `bipartiteEdgeChoice.toMeasure = Measure.pi (slot PMFs)` by the
bridge lemma. Mathlib's `iIndepFun_pi` then gives independence of the full
family of slot-projections indexed by `Fin n_A × Fin n_B`. The single-row
family `(edgeIndicator a ·)` is the precomposition by the injection
`b ↦ (a, b) : Fin n_B → Fin n_A × Fin n_B`, so `iIndepFun.precomp` applies. -/
theorem edgeIndicator_iIndepFun (p : ENNReal) (hp : p ≤ 1) (a : Fin n_A) :
    ProbabilityTheory.iIndepFun (fun b : Fin n_B => edgeIndicator a b)
      ((bipartiteEdgeChoice n_A n_B p hp).toMeasure) := by
  classical
  -- Per-slot indicator on Bool.
  let toReal : Bool → ℝ := fun β => if β = true then (1 : ℝ) else 0
  -- Mathlib's `iIndepFun_pi`: with each ω_e ∈ Bool drawn independently,
  -- the family `e ↦ (ω ↦ toReal (ω e))` is iIndep over `Fin n_A × Fin n_B`.
  have h_full :
      ProbabilityTheory.iIndepFun
        (fun (e : Fin n_A × Fin n_B) (ω : Fin n_A × Fin n_B → Bool) => toReal (ω e))
        (Measure.pi (fun _ : Fin n_A × Fin n_B => (slotPMF p hp).toMeasure)) :=
    ProbabilityTheory.iIndepFun_pi (fun _ => Measurable.of_discrete.aemeasurable)
  -- Transport via the bridge lemma.
  rw [bipartiteEdgeChoice_toMeasure_eq_pi p hp]
  -- Precompose with the injection b ↦ (a, b) to restrict to a single row.
  have h_inj : Function.Injective (fun b : Fin n_B => (a, b)) := by
    intro b₁ b₂ h; exact (Prod.mk.injEq _ _ _ _).mp h |>.2
  exact h_full.precomp (g := fun b : Fin n_B => (a, b)) h_inj

/-- Expectation of `edgeIndicator a b` under the bipartite edge-choice PMF
equals `p.toReal`. This is the `h_p_eq` Chernoff prerequisite. -/
lemma integral_edgeIndicator_eq (p : ENNReal) (hp : p ≤ 1)
    (a : Fin n_A) (b : Fin n_B) :
    ∫ f, edgeIndicator a b f ∂((bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      = p.toReal := by
  classical
  have h_eq : edgeIndicator a b
      = Set.indicator {f : Fin n_A × Fin n_B → Bool | f (a, b) = true}
          (1 : (Fin n_A × Fin n_B → Bool) → ℝ) := by
    funext f
    unfold edgeIndicator
    by_cases h : f (a, b) = true <;> simp [h]
  rw [h_eq]
  rw [MeasureTheory.integral_indicator_one MeasurableSet.of_discrete]
  -- Goal: ((bipartiteEdgeChoice ...).toMeasure).real {f | f(a,b)=true} = p.toReal
  unfold MeasureTheory.Measure.real
  rw [bipartiteEdgeChoice_apply_at_eq_true p hp a b]

/-- The degree in the bipartite graph from a selector equals
`degAOfSelector` for an A-vertex. -/
lemma boolToBipartiteGraph_degree_inl (f : Fin n_A × Fin n_B → Bool) (a : Fin n_A) :
    (boolToBipartiteGraph f).degree (Sum.inl a) = degAOfSelector f a := by
  unfold SimpleGraph.degree degAOfSelector
  -- neighborFinset (Sum.inl a) = filter (G.Adj (Sum.inl a)) univ
  -- Image: x ↦ G.Adj (Sum.inl a) x = (Sum.inl a ≠ x) ∧ (∃ a' b, bipartiteRel...)
  -- For Sum.inl a' : never adj
  -- For Sum.inr b : adj iff f (a, b) = true
  -- So the count is |{b : Fin n_B | f (a, b) = true}|.
  rw [SimpleGraph.neighborFinset]
  -- Now goal: (G.neighborSet (Sum.inl a)).toFinset.card = filter (f (a, ·) = true) univ |>.card
  -- Strategy: show the two Finsets are in bijection via Sum.inr.
  have h_eq : (boolToBipartiteGraph f).neighborSet (Sum.inl a)
      = Sum.inr '' {b : Fin n_B | f (a, b) = true} := by
    ext x
    simp only [SimpleGraph.mem_neighborSet, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro hadj
      match x with
      | Sum.inl a' => exact absurd hadj (boolToBipartiteGraph_not_adj_inl_inl f a a')
      | Sum.inr b => exact ⟨b, (boolToBipartiteGraph_adj_inl_inr f a b).mp hadj, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact (boolToBipartiteGraph_adj_inl_inr f a b).mpr hb
  rw [Set.toFinset_congr h_eq, Set.toFinset_image,
    Finset.card_image_of_injective _ Sum.inr_injective]
  congr 1
  ext b
  simp

/-! ## Step 7: Apply Chernoff to single-vertex degree (Bennett form) -/

open DaveyThesis2024.Concentration in
/-- **Single-vertex lower-tail Chernoff (Bennett form)**: for fixed `a : Fin n_A`
and deviation `t ∈ [0, n_B p)`,
`Pr[deg_a ≤ n_B·p - t] ≤ exp(-t²/(2(n_B·p - t/3)))`.

Direct application of `chernoff_A2_lower` (Bennett form) to the family
`{edgeIndicator a b}_b`.

This is the BENNETT form (cleaner exponent in δ²·n_B·p) — replaces the raw
multiplicative form. Step 1.J of the J–N closure plan. -/
lemma deg_at_a_lower_tail (p : ENNReal) (hp : p ≤ 1)
    (a : Fin n_A) (t : ℝ) (ht_nn : 0 ≤ t)
    (ht_lt : t < (Fintype.card (Fin n_B) : ℝ) * p.toReal)
    (hμ_pos : 0 < (Fintype.card (Fin n_B) : ℝ) * p.toReal) :
    ((bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
      {f | (degAOfSelector f a : ℝ) ≤ (Fintype.card (Fin n_B) : ℝ) * p.toReal - t}
    ≤ Real.exp (- t^2 / (2 * ((Fintype.card (Fin n_B) : ℝ) * p.toReal - t / 3))) := by
  set μ := (bipartiteEdgeChoice n_A n_B p hp).toMeasure
  have h_p_bounds : ∀ _ : Fin n_B, 0 ≤ p.toReal ∧ p.toReal ≤ 1 :=
    fun _ => ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal (by norm_num)
      (by rw [ENNReal.ofReal_one]; exact hp)⟩
  have h_sum_eq : (∑ _ : Fin n_B, p.toReal) = (Fintype.card (Fin n_B) : ℝ) * p.toReal := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_t_lt_sum : t < ∑ _ : Fin n_B, p.toReal := by rw [h_sum_eq]; exact ht_lt
  have h_μ_pos_sum : 0 < ∑ _ : Fin n_B, p.toReal := by rw [h_sum_eq]; exact hμ_pos
  have h_chernoff := chernoff_A2_lower
    (μ := μ) (s := (Finset.univ : Finset (Fin n_B)))
    (X := fun b => edgeIndicator a b)
    (edgeIndicator_iIndepFun p hp a)
    (fun b => measurable_edgeIndicator a b)
    (fun b f => edgeIndicator_indicator a b f)
    (fun _ => p.toReal)
    h_p_bounds
    (fun b => integral_edgeIndicator_eq p hp a b)
    t ht_nn h_t_lt_sum h_μ_pos_sum
  -- Convert set form and ∑ → degAOfSelector.
  have h_set_eq : ∀ {ε : ℝ}, {f : Fin n_A × Fin n_B → Bool | ∑ b, edgeIndicator a b f ≤ ε}
      = {f | (degAOfSelector f a : ℝ) ≤ ε} := by
    intro ε; ext f; rw [Set.mem_setOf_eq, Set.mem_setOf_eq, sum_edgeIndicator_eq_degA a f]
  rwa [h_set_eq, h_sum_eq] at h_chernoff

/-! ## Step 8: Bridge selector measure → graph measure (Step 1.K)

`bipartiteErPMF = bipartiteEdgeChoice.map boolToBipartiteGraph`, so by
`PMF.toMeasure_map_apply`, an event on graphs pulls back to the corresponding
event on selectors. Combined with `boolToBipartiteGraph_degree_inl`, this
transfers the single-vertex Chernoff bound from selector-space to graph-space. -/

/-- `boolToBipartiteGraph` is measurable (target carries the discrete `⊤`
σ-algebra). -/
lemma measurable_boolToBipartiteGraph :
    Measurable (boolToBipartiteGraph : (Fin n_A × Fin n_B → Bool) → _) :=
  Measurable.of_discrete

/-- The measure of a graph event under `bipartiteRandomMeasure` equals the
measure of its preimage under `boolToBipartiteGraph` under
`bipartiteEdgeChoice.toMeasure`. -/
lemma bipartiteRandomMeasure_eq_preimage (p : ENNReal) (hp : p ≤ 1)
    {S : Set (SimpleGraph (Fin n_A ⊕ Fin n_B))} (hS : MeasurableSet S) :
    bipartiteRandomMeasure n_A n_B p hp S
      = (bipartiteEdgeChoice n_A n_B p hp).toMeasure (boolToBipartiteGraph ⁻¹' S) := by
  unfold bipartiteRandomMeasure bipartiteErPMF
  exact PMF.toMeasure_map_apply _ _ _ measurable_boolToBipartiteGraph hS

/-! ## Step 9: Single-vertex Bennett bound on graph measure (Step 1.M start)

The bridge from selector-measure bound to graph-measure bound. -/

/-! ## Step 9: Selector-side Δ_A and bridge to single-vertex bound

To avoid `SimpleGraph.degree` typeclass friction, define `deltaA_selector` (max
degree over A-side, working entirely on the selector function) and prove the
max ≥ single-vertex lift on the selector side. -/

/-- Selector-side `Δ_A`: maximum of `degAOfSelector f a` over `a ∈ Fin n_A`. -/
def deltaA_selector (f : Fin n_A × Fin n_B → Bool) : ℕ :=
  (Finset.univ : Finset (Fin n_A)).sup (fun a => degAOfSelector f a)

/-- The max ≥ single vertex lift on the selector side. -/
lemma degAOfSelector_le_deltaA_selector (f : Fin n_A × Fin n_B → Bool) (a₀ : Fin n_A) :
    degAOfSelector f a₀ ≤ deltaA_selector f :=
  Finset.le_sup (f := fun a => degAOfSelector f a) (Finset.mem_univ a₀)

/-- The probability that the selector-side `Δ_A` is below `(1-δ) n_B p` is at most
the probability that a chosen single vertex's degree is below the same threshold. -/
lemma deltaA_selector_lower_tail (p : ENNReal) (hp : p ≤ 1)
    (a₀ : Fin n_A) (ε : ℝ) :
    ((bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
      {f | (deltaA_selector f : ℝ) < ε}
    ≤ ((bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
      {f | (degAOfSelector f a₀ : ℝ) < ε} := by
  apply MeasureTheory.measureReal_mono _ (MeasureTheory.measure_ne_top _ _)
  intro f hf
  simp only [Set.mem_setOf_eq] at *
  exact lt_of_le_of_lt (by exact_mod_cast degAOfSelector_le_deltaA_selector f a₀) hf

open DaveyThesis2024.Concentration in
/-- **Chernoff lower-tail bound on selector-side Δ_A**: combines
`deltaA_selector_lower_tail` with `deg_at_a_lower_tail` to bound the
probability that the maximum A-side degree (in the selector form) is below
the deviation threshold. -/
lemma deltaA_selector_lower_tail_chernoff
    (p : ENNReal) (hp : p ≤ 1) [Nonempty (Fin n_A)]
    (t : ℝ) (ht_nn : 0 ≤ t)
    (ht_lt : t < (Fintype.card (Fin n_B) : ℝ) * p.toReal)
    (hμ_pos : 0 < (Fintype.card (Fin n_B) : ℝ) * p.toReal) :
    ((bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
      {f | (deltaA_selector f : ℝ) < (Fintype.card (Fin n_B) : ℝ) * p.toReal - t}
    ≤ Real.exp (- t^2 / (2 * ((Fintype.card (Fin n_B) : ℝ) * p.toReal - t / 3))) := by
  set ε := (Fintype.card (Fin n_B) : ℝ) * p.toReal - t with hε_def
  obtain ⟨a₀⟩ := ‹Nonempty (Fin n_A)›
  -- {f | deltaA_selector f < ε} ⊆ {f | degAOfSelector f a₀ < ε} ⊆ {f | degAOfSelector f a₀ ≤ ε}
  refine le_trans (deltaA_selector_lower_tail p hp a₀ ε) ?_
  refine le_trans ?_ (deg_at_a_lower_tail p hp a₀ t ht_nn ht_lt hμ_pos)
  apply MeasureTheory.measureReal_mono _ (MeasureTheory.measure_ne_top _ _)
  intro f hf
  simp only [Set.mem_setOf_eq] at *
  exact le_of_lt hf

/-! ## B-side mirror: infrastructure for `deltaB`

Symmetric mirror of the A-side infrastructure (Steps 5–9). For fixed
`b : Fin n_B`, the degree at `Sum.inr b` in `boolToBipartiteGraph f`
equals the number of `a : Fin n_A` such that `f (a, b) = true`. The
edge indicators `edgeIndicator_for_B b a` (varying over `a` with `b`
fixed) are mutually independent under the bipartite edge-choice
measure. -/

/-- Single-edge indicator (B-side variant): 1 if `f (a, b) = true`, 0 otherwise.
The collection `{edgeIndicator_for_B b a}_a` for fixed `b` are the indicator
random variables whose sum is `degBOfSelector f b`. -/
noncomputable def edgeIndicator_for_B (b : Fin n_B) (a : Fin n_A) :
    (Fin n_A × Fin n_B → Bool) → ℝ :=
  fun f => if f (a, b) = true then 1 else 0

@[simp] lemma edgeIndicator_for_B_apply (b : Fin n_B) (a : Fin n_A)
    (f : Fin n_A × Fin n_B → Bool) :
    edgeIndicator_for_B b a f = if f (a, b) = true then 1 else 0 := rfl

/-- B-side indicators take values in `{0, 1}`. -/
lemma edgeIndicator_for_B_indicator (b : Fin n_B) (a : Fin n_A)
    (f : Fin n_A × Fin n_B → Bool) :
    edgeIndicator_for_B b a f = 0 ∨ edgeIndicator_for_B b a f = 1 := by
  unfold edgeIndicator_for_B
  by_cases h : f (a, b) = true <;> simp [h]

/-- Sum of B-side indicators for fixed `b` equals the degree count. -/
lemma sum_edgeIndicator_for_B_eq_degB (b : Fin n_B) (f : Fin n_A × Fin n_B → Bool) :
    (∑ a : Fin n_A, edgeIndicator_for_B b a f) = (degBOfSelector f b : ℝ) := by
  unfold edgeIndicator_for_B degBOfSelector
  rw [Finset.sum_boole]

/-- Measurability of `edgeIndicator_for_B b a` from `(Fin n_A × Fin n_B → Bool)`
(discrete) to `ℝ` (Borel). -/
lemma measurable_edgeIndicator_for_B (b : Fin n_B) (a : Fin n_A) :
    Measurable (edgeIndicator_for_B b a) := Measurable.of_discrete

/-- Expectation of `edgeIndicator_for_B b a` under the bipartite edge-choice PMF
equals `p.toReal`. Mirror of `integral_edgeIndicator_eq`. -/
lemma integral_edgeIndicator_for_B_eq (p : ENNReal) (hp : p ≤ 1)
    (b : Fin n_B) (a : Fin n_A) :
    ∫ f, edgeIndicator_for_B b a f ∂((bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      = p.toReal := by
  classical
  have h_eq : edgeIndicator_for_B b a
      = Set.indicator {f : Fin n_A × Fin n_B → Bool | f (a, b) = true}
          (1 : (Fin n_A × Fin n_B → Bool) → ℝ) := by
    funext f
    unfold edgeIndicator_for_B
    by_cases h : f (a, b) = true <;> simp [h]
  rw [h_eq]
  rw [MeasureTheory.integral_indicator_one MeasurableSet.of_discrete]
  unfold MeasureTheory.Measure.real
  rw [bipartiteEdgeChoice_apply_at_eq_true p hp a b]

open ProbabilityTheory in
/-- **Independence of B-side edge indicators.**

For fixed `b : Fin n_B`, the family `(edgeIndicator_for_B b · : Fin n_A → ...)`
of indicator random variables is mutually independent under the bipartite
edge-choice measure. Mirror of `edgeIndicator_iIndepFun`. -/
theorem edgeIndicator_for_B_iIndepFun (p : ENNReal) (hp : p ≤ 1) (b : Fin n_B) :
    ProbabilityTheory.iIndepFun (fun a : Fin n_A => edgeIndicator_for_B b a)
      ((bipartiteEdgeChoice n_A n_B p hp).toMeasure) := by
  classical
  let toReal : Bool → ℝ := fun β => if β = true then (1 : ℝ) else 0
  have h_full :
      ProbabilityTheory.iIndepFun
        (fun (e : Fin n_A × Fin n_B) (ω : Fin n_A × Fin n_B → Bool) => toReal (ω e))
        (Measure.pi (fun _ : Fin n_A × Fin n_B => (slotPMF p hp).toMeasure)) :=
    ProbabilityTheory.iIndepFun_pi (fun _ => Measurable.of_discrete.aemeasurable)
  rw [bipartiteEdgeChoice_toMeasure_eq_pi p hp]
  have h_inj : Function.Injective (fun a : Fin n_A => (a, b)) := by
    intro a₁ a₂ h; exact (Prod.mk.injEq _ _ _ _).mp h |>.1
  exact h_full.precomp (g := fun a : Fin n_A => (a, b)) h_inj

/-- The degree in the bipartite graph from a selector equals
`degBOfSelector` for a B-vertex. Mirror of `boolToBipartiteGraph_degree_inl`. -/
lemma boolToBipartiteGraph_degree_inr (f : Fin n_A × Fin n_B → Bool) (b : Fin n_B) :
    (boolToBipartiteGraph f).degree (Sum.inr b) = degBOfSelector f b := by
  unfold SimpleGraph.degree degBOfSelector
  rw [SimpleGraph.neighborFinset]
  have h_eq : (boolToBipartiteGraph f).neighborSet (Sum.inr b)
      = Sum.inl '' {a : Fin n_A | f (a, b) = true} := by
    ext x
    simp only [SimpleGraph.mem_neighborSet, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro hadj
      match x with
      | Sum.inr b' => exact absurd hadj (boolToBipartiteGraph_not_adj_inr_inr f b b')
      | Sum.inl a => exact ⟨a, (boolToBipartiteGraph_adj_inr_inl f b a).mp hadj, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact (boolToBipartiteGraph_adj_inr_inl f b a).mpr ha
  rw [Set.toFinset_congr h_eq, Set.toFinset_image,
    Finset.card_image_of_injective _ Sum.inl_injective]
  congr 1
  ext a
  simp

open DaveyThesis2024.Concentration in
/-- **Single-vertex lower-tail Chernoff (B-side, Bennett form)**: for fixed
`b : Fin n_B` and deviation `t ∈ [0, n_A p)`,
`Pr[deg_b ≤ n_A·p - t] ≤ exp(-t²/(2(n_A·p - t/3)))`.

Mirror of `deg_at_a_lower_tail`. -/
lemma deg_at_b_lower_tail (p : ENNReal) (hp : p ≤ 1)
    (b : Fin n_B) (t : ℝ) (ht_nn : 0 ≤ t)
    (ht_lt : t < (Fintype.card (Fin n_A) : ℝ) * p.toReal)
    (hμ_pos : 0 < (Fintype.card (Fin n_A) : ℝ) * p.toReal) :
    ((bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
      {f | (degBOfSelector f b : ℝ) ≤ (Fintype.card (Fin n_A) : ℝ) * p.toReal - t}
    ≤ Real.exp (- t^2 / (2 * ((Fintype.card (Fin n_A) : ℝ) * p.toReal - t / 3))) := by
  set μ := (bipartiteEdgeChoice n_A n_B p hp).toMeasure
  have h_p_bounds : ∀ _ : Fin n_A, 0 ≤ p.toReal ∧ p.toReal ≤ 1 :=
    fun _ => ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal (by norm_num)
      (by rw [ENNReal.ofReal_one]; exact hp)⟩
  have h_sum_eq : (∑ _ : Fin n_A, p.toReal) = (Fintype.card (Fin n_A) : ℝ) * p.toReal := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_t_lt_sum : t < ∑ _ : Fin n_A, p.toReal := by rw [h_sum_eq]; exact ht_lt
  have h_μ_pos_sum : 0 < ∑ _ : Fin n_A, p.toReal := by rw [h_sum_eq]; exact hμ_pos
  have h_chernoff := chernoff_A2_lower
    (μ := μ) (s := (Finset.univ : Finset (Fin n_A)))
    (X := fun a => edgeIndicator_for_B b a)
    (edgeIndicator_for_B_iIndepFun p hp b)
    (fun a => measurable_edgeIndicator_for_B b a)
    (fun a f => edgeIndicator_for_B_indicator b a f)
    (fun _ => p.toReal)
    h_p_bounds
    (fun a => integral_edgeIndicator_for_B_eq p hp b a)
    t ht_nn h_t_lt_sum h_μ_pos_sum
  have h_set_eq : ∀ {ε : ℝ}, {f : Fin n_A × Fin n_B → Bool | ∑ a, edgeIndicator_for_B b a f ≤ ε}
      = {f | (degBOfSelector f b : ℝ) ≤ ε} := by
    intro ε; ext f; rw [Set.mem_setOf_eq, Set.mem_setOf_eq, sum_edgeIndicator_for_B_eq_degB b f]
  rwa [h_set_eq, h_sum_eq] at h_chernoff

/-- Selector-side `Δ_B`: maximum of `degBOfSelector f b` over `b ∈ Fin n_B`. -/
def deltaB_selector (f : Fin n_A × Fin n_B → Bool) : ℕ :=
  (Finset.univ : Finset (Fin n_B)).sup (fun b => degBOfSelector f b)

/-- The max ≥ single vertex lift on the selector side. -/
lemma degBOfSelector_le_deltaB_selector (f : Fin n_A × Fin n_B → Bool) (b₀ : Fin n_B) :
    degBOfSelector f b₀ ≤ deltaB_selector f :=
  Finset.le_sup (f := fun b => degBOfSelector f b) (Finset.mem_univ b₀)

/-- The probability that the selector-side `Δ_B` is below `(1-δ) n_A p` is at most
the probability that a chosen single vertex's degree is below the same threshold. -/
lemma deltaB_selector_lower_tail (p : ENNReal) (hp : p ≤ 1)
    (b₀ : Fin n_B) (ε : ℝ) :
    ((bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
      {f | (deltaB_selector f : ℝ) < ε}
    ≤ ((bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
      {f | (degBOfSelector f b₀ : ℝ) < ε} := by
  apply MeasureTheory.measureReal_mono _ (MeasureTheory.measure_ne_top _ _)
  intro f hf
  simp only [Set.mem_setOf_eq] at *
  exact lt_of_le_of_lt (by exact_mod_cast degBOfSelector_le_deltaB_selector f b₀) hf

open DaveyThesis2024.Concentration in
/-- **Chernoff lower-tail bound on selector-side Δ_B**: combines
`deltaB_selector_lower_tail` with `deg_at_b_lower_tail` to bound the
probability that the maximum B-side degree (in the selector form) is below
the deviation threshold. Mirror of `deltaA_selector_lower_tail_chernoff`. -/
lemma deltaB_selector_lower_tail_chernoff
    (p : ENNReal) (hp : p ≤ 1) [Nonempty (Fin n_B)]
    (t : ℝ) (ht_nn : 0 ≤ t)
    (ht_lt : t < (Fintype.card (Fin n_A) : ℝ) * p.toReal)
    (hμ_pos : 0 < (Fintype.card (Fin n_A) : ℝ) * p.toReal) :
    ((bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
      {f | (deltaB_selector f : ℝ) < (Fintype.card (Fin n_A) : ℝ) * p.toReal - t}
    ≤ Real.exp (- t^2 / (2 * ((Fintype.card (Fin n_A) : ℝ) * p.toReal - t / 3))) := by
  set ε := (Fintype.card (Fin n_A) : ℝ) * p.toReal - t with hε_def
  obtain ⟨b₀⟩ := ‹Nonempty (Fin n_B)›
  refine le_trans (deltaB_selector_lower_tail p hp b₀ ε) ?_
  refine le_trans ?_ (deg_at_b_lower_tail p hp b₀ t ht_nn ht_lt hμ_pos)
  apply MeasureTheory.measureReal_mono _ (MeasureTheory.measure_ne_top _ _)
  intro f hf
  simp only [Set.mem_setOf_eq] at *
  exact le_of_lt hf

end DaveyThesis2024.BipartiteRandomGraph
