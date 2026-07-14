/-
Copyright (c) 2026 Ross Kang.
Released under Apache 2.0 license.

# Asymmetric SEC for random bipartite graphs

Formalisation of the main theorem (Brualdi–Quinn conjecture, random
bipartite a.a.s. version):

> For random bipartite G ~ G(n_A, n_B, p) at constant p ∈ (0, 1),
> χ'_s(G) ≤ Δ_A(G) · Δ_B(G) a.a.s. as min(n_A, n_B) → ∞.

The proof uses the Pippenger–Spencer + Kim–Vu axiomatisation chain
in `SecRandomBipartite/PippengerSpencer.lean`. See
`SecRandomBipartite/Closure.lean` for the headline theorem
`secRandomBipartite_aas`.

The probabilistic core depends on two cited axioms (Kahn 1996 +
Kim–Vu 2000) and one explicit `asymptotic_regime` Prop hypothesis
(textbook exp/log calculation, deferred).
-/


import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import DaveyThesis2024.BipartiteRandomGraph



namespace SECRandomBipartite

open SimpleGraph

variable {V : Type*}

/-! ## Section 1: Definitions -/

/-- Two edges `e₁, e₂` of a simple graph `G` are *L²-adjacent* if they are
distinct and at distance at most 2 in the line graph `L(G)`, i.e., they
share a vertex of `G` or there is a "bridge" edge `e₃` sharing a vertex with
each.

**Bugfix (C-lite, 2026-06-02)**: parenthesised the previously-ambiguous
`A ∧ B ∨ C` form. Lean's precedence parsed it as `(A ∧ B) ∨ C`, which would
have allowed `e₁ = e₂` to be "L²-adjacent" via the trivial bridge `e₃ := e₁`,
silently creating self-loops in `lineGraphSq`. -/
def LineGraphSqAdj (G : SimpleGraph V) (e₁ e₂ : G.edgeSet) : Prop :=
  e₁ ≠ e₂ ∧
    (((e₁ : Sym2 V) ∩ (e₂ : Sym2 V) : Set V).Nonempty ∨
      ∃ e₃ : G.edgeSet,
        ((e₁ : Sym2 V) ∩ (e₃ : Sym2 V) : Set V).Nonempty ∧
        ((e₃ : Sym2 V) ∩ (e₂ : Sym2 V) : Set V).Nonempty)

/-- L²-adjacency is symmetric. -/
lemma LineGraphSqAdj.symm {G : SimpleGraph V} {e₁ e₂ : G.edgeSet}
    (h : LineGraphSqAdj G e₁ e₂) : LineGraphSqAdj G e₂ e₁ := by
  refine ⟨h.1.symm, ?_⟩
  rcases h.2 with hshare | ⟨e₃, h13, h32⟩
  · left; rwa [Set.inter_comm]
  · right; exact ⟨e₃, by rwa [Set.inter_comm], by rwa [Set.inter_comm]⟩

/-- L²-adjacency is irreflexive (no self-loops). -/
lemma LineGraphSqAdj.irrefl {G : SimpleGraph V} (e : G.edgeSet) :
    ¬ LineGraphSqAdj G e e := fun h => h.1 rfl

/-- The **square of the line graph** `L(G)²` as a `SimpleGraph G.edgeSet`.
Vertices are edges of `G`; edges of `L(G)²` are L²-adjacent pairs. -/
def lineGraphSq (G : SimpleGraph V) : SimpleGraph G.edgeSet where
  Adj := LineGraphSqAdj G
  symm _ _ h := LineGraphSqAdj.symm h
  loopless := ⟨fun e h => LineGraphSqAdj.irrefl e h⟩

@[simp] lemma lineGraphSq_adj (G : SimpleGraph V) (e₁ e₂ : G.edgeSet) :
    (lineGraphSq G).Adj e₁ e₂ ↔ LineGraphSqAdj G e₁ e₂ := Iff.rfl

/-- A *strong edge colouring* of `G` is a colouring of edges so that
L²-adjacent edges get different colours. Equivalent to a proper colouring
of `lineGraphSq G`. -/
def IsStrongEdgeColouring (G : SimpleGraph V) {C : Type*} (c : G.edgeSet → C) : Prop :=
  ∀ e₁ e₂ : G.edgeSet, LineGraphSqAdj G e₁ e₂ → c e₁ ≠ c e₂

/-- The *strong chromatic index* `χ'_s(G)` of a simple graph `G`: the
minimum number of colours required for a strong edge colouring. -/
noncomputable def chiPrimeS (G : SimpleGraph V) : ℕ∞ :=
  sInf ((fun (k : ℕ) => (k : ℕ∞)) ''
    {k : ℕ | ∃ c : G.edgeSet → Fin k, IsStrongEdgeColouring G c})

/-- **Bridge to Mathlib's `Colorable`**: a strong edge colouring of `G`
using `k` colours is exactly a proper colouring of `lineGraphSq G` using
`k` colours. -/
lemma colorable_lineGraphSq_iff (G : SimpleGraph V) (k : ℕ) :
    (lineGraphSq G).Colorable k ↔ ∃ c : G.edgeSet → Fin k, IsStrongEdgeColouring G c := by
  constructor
  · rintro ⟨coloring⟩
    refine ⟨coloring, ?_⟩
    intro e₁ e₂ hadj
    exact coloring.valid ((lineGraphSq_adj G e₁ e₂).mpr hadj)
  · rintro ⟨c, hc⟩
    refine ⟨⟨c, ?_⟩⟩
    intro e₁ e₂ hadj
    exact hc e₁ e₂ ((lineGraphSq_adj G e₁ e₂).mp hadj)

/-- **Bridge to Mathlib's chromaticNumber**: `chiPrimeS G = (lineGraphSq G).chromaticNumber`.

This connects our edge-colouring development to Mathlib's vertex-colouring
API, enabling future use of chromatic-number lemmas (degeneracy bounds,
greedy bounds, etc.) on `lineGraphSq G`. -/
lemma chiPrimeS_eq_chromaticNumber_lineGraphSq (G : SimpleGraph V) :
    chiPrimeS G = (lineGraphSq G).chromaticNumber := by
  unfold chiPrimeS SimpleGraph.chromaticNumber
  -- LHS: sInf ((↑·) '' {k | ∃ c : G.edgeSet → Fin k, IsStrongEdgeColouring G c})
  -- RHS: ⨅ n ∈ setOf (lineGraphSq G).Colorable, (n : ℕ∞)
  --    = sInf ((↑·) '' setOf (lineGraphSq G).Colorable)  by iInf_subtype + sInf_image
  -- Both reduce to sInf over the same image once we use colorable_lineGraphSq_iff.
  rw [iInf_subtype', ← sInf_range]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range, Subtype.exists,
    SimpleGraph.Colorable, exists_prop]
  constructor
  · rintro ⟨k, ⟨c, hc⟩, rfl⟩
    refine ⟨k, ?_, rfl⟩
    exact (colorable_lineGraphSq_iff G k).mpr ⟨c, hc⟩
  · rintro ⟨k, hcolor, rfl⟩
    exact ⟨k, (colorable_lineGraphSq_iff G k).mp hcolor, rfl⟩

/-- For a bipartite graph `G` with bipartition `A ∪ B`, the *A-side max
degree* `Δ_A(G)` is the maximum degree among `A`-vertices. -/
noncomputable def deltaA {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    [DecidableRel G.Adj] : ℕ :=
  (Finset.univ : Finset (Fin n_A)).sup fun a => G.degree (Sum.inl a)

/-- Symmetric: `Δ_B(G)` is the maximum degree among `B`-vertices. -/
noncomputable def deltaB {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    [DecidableRel G.Adj] : ℕ :=
  (Finset.univ : Finset (Fin n_B)).sup fun b => G.degree (Sum.inr b)

/-- `Δ_1(G) := max{deg(a) + deg(b) - 1 : {a, b} ∈ E(G)}` is the
   maximum endpoint-degree-sum-minus-one over edges of `G`. For a
   bipartite graph with each edge `{a, b}` having `a ∈ A` and `b ∈ B`,
   `Δ_1(G) ≤ Δ_A(G) + Δ_B(G) - 1`. -/
noncomputable def delta1 {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    [DecidableRel G.Adj] : ℕ :=
  ((Finset.univ : Finset (Fin n_A × Fin n_B)).filter
      (fun ab => G.Adj (Sum.inl ab.1) (Sum.inr ab.2))
    |>.sup
      fun ab => G.degree (Sum.inl ab.1) + G.degree (Sum.inr ab.2) - 1)

/-! ## Section 2: Random bipartite graph

The bipartite Erdős–Rényi random graph $G(n_A, n_B, p)$ is constructed as
a Mathlib `PMF` in `DaveyThesis2024.BipartiteRandomGraph`, with
`bipartiteRandomMeasure` the underlying probability measure. We re-expose
the standard probability function `probBipartiteRandom` as the concrete
one defined there. -/

/-- The probability of an event over the bipartite Erdős–Rényi random
graph `G ~ G(n_A, n_B, p)`. **Replaces the earlier axiom** with the
concrete definition `probBipartiteRandomConcrete` (Phase Refactor-1.E,
2026-06-01). -/
noncomputable def probBipartiteRandom (n_A n_B : ℕ) (p : ℝ)
    (event : SimpleGraph (Fin n_A ⊕ Fin n_B) → Prop) : ℝ :=
  DaveyThesis2024.BipartiteRandomGraph.probBipartiteRandomConcrete n_A n_B p event

/-! ## Section 3: Structural arithmetic lemmas (Lean-provable, no probability)

These lemmas connect the various degree quantities and form the
non-probabilistic content of the conjecture closure. -/

/-- **Arithmetic lemma.** For natural numbers `a, b ≥ 1`,
`a + b - 1 ≤ a * b`, equivalent to `(a - 1)(b - 1) ≥ 0`.

This lifts `Δ_A + Δ_B - 1 ≤ Δ_A * Δ_B` to the abstract setting once we
know at least one edge exists (so `Δ_A, Δ_B ≥ 1`). -/
lemma add_sub_one_le_mul {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a + b - 1 ≤ a * b := by
  rcases a with _ | a; · omega
  rcases b with _ | b; · omega
  -- Goal: (a+1) + (b+1) - 1 ≤ (a+1)*(b+1)
  calc a + 1 + (b + 1) - 1
      = a + b + 1 := by omega
    _ ≤ a * b + (a + b + 1) := Nat.le_add_left _ _
    _ = (a + 1) * (b + 1) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        ac_rfl

/-- `Δ_1(G) ≤ Δ_A(G) + Δ_B(G) - 1` for bipartite `G`, because each
edge's endpoint-degree-sum is bounded by `Δ_A + Δ_B`. -/
lemma delta1_le_deltaA_add_deltaB_sub_one {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj] :
    delta1 G ≤ deltaA G + deltaB G - 1 := by
  unfold delta1
  apply Finset.sup_le
  intro ab _
  have ha : G.degree (Sum.inl ab.1) ≤ deltaA G :=
    Finset.le_sup (f := fun a => G.degree (Sum.inl a)) (Finset.mem_univ ab.1)
  have hb : G.degree (Sum.inr ab.2) ≤ deltaB G :=
    Finset.le_sup (f := fun b => G.degree (Sum.inr b)) (Finset.mem_univ ab.2)
  omega

/-- The chained sparse-regime bound:
`Δ_1(G) ≤ Δ_A(G) · Δ_B(G)` whenever both side max-degrees are at least 1
(i.e., the graph has at least one edge on each side). -/
lemma delta1_le_deltaA_mul_deltaB {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (hA : 1 ≤ deltaA G) (hB : 1 ≤ deltaB G) :
    delta1 G ≤ deltaA G * deltaB G :=
  Nat.le_trans (delta1_le_deltaA_add_deltaB_sub_one G) (add_sub_one_le_mul hA hB)

/-- **Max ≥ single vertex (Step 1.L).** For any chosen `a₀ : Fin n_A`,
the side max degree `Δ_A G` is at least `G.degree (Sum.inl a₀)`. -/
lemma deltaA_ge_degree {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (a₀ : Fin n_A) :
    G.degree (Sum.inl a₀) ≤ deltaA G := by
  unfold deltaA
  exact Finset.le_sup (f := fun a => G.degree (Sum.inl a)) (Finset.mem_univ a₀)

/-- **Symmetric**: `Δ_B G ≥ G.degree (Sum.inr b₀)`. -/
lemma deltaB_ge_degree {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (b₀ : Fin n_B) :
    G.degree (Sum.inr b₀) ≤ deltaB G := by
  unfold deltaB
  exact Finset.le_sup (f := fun b => G.degree (Sum.inr b)) (Finset.mem_univ b₀)

/-- **Bridge**: `deltaA (boolToBipartiteGraph f)` (using the canonical
decidability instance) equals the selector-side `deltaA_selector f`. -/
lemma deltaA_boolToBipartiteGraph_eq {n_A n_B : ℕ}
    (f : Fin n_A × Fin n_B → Bool) :
    @deltaA n_A n_B (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph f)
      (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_decidableAdj f)
      = DaveyThesis2024.BipartiteRandomGraph.deltaA_selector f := by
  unfold deltaA DaveyThesis2024.BipartiteRandomGraph.deltaA_selector
  apply Finset.sup_congr rfl
  intro a _
  exact DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_degree_inl f a

/-- **Bridge (B-side mirror)**: `deltaB (boolToBipartiteGraph f)` (using the
canonical decidability instance) equals the selector-side `deltaB_selector f`. -/
lemma deltaB_boolToBipartiteGraph_eq {n_A n_B : ℕ}
    (f : Fin n_A × Fin n_B → Bool) :
    @deltaB n_A n_B (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph f)
      (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_decidableAdj f)
      = DaveyThesis2024.BipartiteRandomGraph.deltaB_selector f := by
  unfold deltaB DaveyThesis2024.BipartiteRandomGraph.deltaB_selector
  apply Finset.sup_congr rfl
  intro b _
  exact DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_degree_inr f b

/-! ## Arithmetic threshold for the exp bound

`deltaA_concentration` requires choosing `N` such that `exp(-c·n) ≤ ε` for `n ≥ N`,
where `c` depends on `δ, p`. This is purely Real-arithmetic. -/

/-- For any positive `c` and `ε`, there is an `N` such that `exp(-c·n) ≤ ε` whenever
`n ≥ N`. The threshold is essentially `N := ⌈-log(ε)/c⌉`. -/
lemma exists_N_exp_neg_le_eps (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Real.exp (-(c * n)) ≤ ε := by
  by_cases hε_le_one : 1 ≤ ε
  · -- ε ≥ 1: trivially true since exp(-anything) ≤ 1.
    refine ⟨0, fun n _ => ?_⟩
    refine le_trans ?_ hε_le_one
    have h_nn : 0 ≤ c * (n : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg n)
    calc Real.exp (-(c * n)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  · -- ε < 1: log ε < 0; choose N := ⌈-log(ε)/c⌉.
    push_neg at hε_le_one
    have hlog_neg : Real.log ε < 0 := Real.log_neg hε hε_le_one
    set threshold : ℝ := -Real.log ε / c with hthreshold_def
    have hthreshold_pos : 0 < threshold := by
      rw [hthreshold_def]; exact div_pos (neg_pos.mpr hlog_neg) hc
    refine ⟨⌈threshold⌉₊, fun n hn => ?_⟩
    have hn_ge : threshold ≤ (n : ℝ) :=
      le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
    -- exp(-c·n) ≤ exp(-c·threshold) = exp(log ε) = ε.
    have h_exp_le : Real.exp (-(c * n)) ≤ Real.exp (-(c * threshold)) := by
      apply Real.exp_le_exp.mpr
      have : c * threshold ≤ c * n := mul_le_mul_of_nonneg_left hn_ge hc.le
      linarith
    have h_simp : Real.exp (-(c * threshold)) = ε := by
      rw [hthreshold_def]
      field_simp
      rw [Real.exp_log hε]
    linarith [h_simp.symm ▸ h_exp_le]

/-! ## Section 3.5: deltaA concentration as theorem (replaces axiom)

Final assembly: combine the selector-side Chernoff bound, the
selector→graph bridge, the measure preimage formula, and the
exp-threshold lemma to prove `deltaA_concentration`. -/

open DaveyThesis2024.BipartiteRandomGraph in
/-- **deltaA_concentration as a Lean theorem** (no longer an axiom).
For any fixed `p ∈ (0, 1)` and any `δ, ε > 0`, there exists `N` such that
for all `n_A, n_B ≥ N`, the probability that `Δ_A(G) ≥ (1-δ)·n_B·p` is at
least `1 - ε`.

The proof assembly is non-trivial — it combines:
* `deltaA_selector_lower_tail_chernoff` (selector-side Bennett bound),
* `deltaA_boolToBipartiteGraph_eq` (selector→graph bridge),
* `bipartiteRandomMeasure_eq_preimage` (PMF.toMeasure_map),
* `exists_N_exp_neg_le_eps` (arithmetic threshold).

This is the **completion of Step 1.M** of the J–N closure plan
(see the development notes).
The detailed assembly is ~200 lines of measure-theoretic + Real
arithmetic wiring; structured as:
1. case split on `δ ≥ 1` (trivial event) vs main case `0 < δ < 1`,
2. choose threshold `c := δ² · p / 2` and `N₀` from `exists_N_exp_neg_le_eps`,
3. set deviation `t := δ · n_B · p` so `n_B · p − t = (1−δ) · n_B · p`,
4. apply Chernoff and bound the exponent by `−c · n_B`,
5. bridge graph measure → selector measure via `bipartiteRandomMeasure_eq_preimage`
   and `deltaA_boolToBipartiteGraph_eq`,
6. convert `μ(bad) ≤ ε` to `μ(good) ≥ 1 − ε` via `prob_compl_eq_one_sub`. -/
theorem deltaA_concentration_proof (p : ℝ) (hp_lb : (0 : ℝ) < p) (hp_ub : p < 1) :
    ∀ δ > (0 : ℝ), ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n_A n_B : ℕ,
      min n_A n_B ≥ N →
      probBipartiteRandom n_A n_B p
        (fun G => ∀ [DecidableRel G.Adj],
          (1 - δ) * (n_B : ℝ) * p ≤ (deltaA G : ℝ))
      ≥ 1 - ε := by
  intro δ hδ ε hε
  -- Set up p as ENNReal-valid.
  have hp_ofReal : ENNReal.ofReal p ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_ub.le
  have hp_toReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp_lb.le
  -- Case split on δ ≥ 1: the event is then trivially true (LHS ≤ 0 ≤ deltaA).
  by_cases hδ1 : 1 ≤ δ
  · refine ⟨0, fun n_A n_B _ => ?_⟩
    -- The event holds for every G, so the probability is 1.
    have h_event : ∀ G : SimpleGraph (Fin n_A ⊕ Fin n_B),
        ∀ [DecidableRel G.Adj],
        (1 - δ) * (n_B : ℝ) * p ≤ (deltaA G : ℝ) := by
      intro G _
      have h_lhs_nonpos : (1 - δ) * (n_B : ℝ) * p ≤ 0 := by
        have h1 : 1 - δ ≤ 0 := by linarith
        have h2 : 0 ≤ (n_B : ℝ) := Nat.cast_nonneg _
        have h3 : (1 - δ) * (n_B : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 h2
        exact mul_nonpos_of_nonpos_of_nonneg h3 hp_lb.le
      exact le_trans h_lhs_nonpos (Nat.cast_nonneg _)
    -- Therefore probBipartiteRandom = 1.
    have h_prob_eq_one : probBipartiteRandom n_A n_B p
        (fun G => ∀ [DecidableRel G.Adj],
          (1 - δ) * (n_B : ℝ) * p ≤ (deltaA G : ℝ)) = 1 := by
      unfold probBipartiteRandom DaveyThesis2024.BipartiteRandomGraph.probBipartiteRandomConcrete
      simp only [hp_ofReal, dite_true]
      have h_univ : {G : SimpleGraph (Fin n_A ⊕ Fin n_B) |
          ∀ [DecidableRel G.Adj], (1 - δ) * (n_B : ℝ) * p ≤ (deltaA G : ℝ)}
          = Set.univ := Set.eq_univ_of_forall h_event
      rw [h_univ, MeasureTheory.measure_univ]
      simp
    rw [h_prob_eq_one]; linarith
  -- Main case: 0 < δ < 1.
  push_neg at hδ1
  -- Threshold c := δ²·p/2 > 0.
  set c : ℝ := δ^2 * p / 2 with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]; positivity
  -- Get N₀ from the arithmetic threshold lemma.
  obtain ⟨N₀, hN₀⟩ := exists_N_exp_neg_le_eps c ε hc_pos hε
  refine ⟨max N₀ 1, fun n_A n_B hN => ?_⟩
  -- From min n_A n_B ≥ max N₀ 1, derive n_A ≥ 1 and n_B ≥ N₀.
  have hN₀_le : N₀ ≤ min n_A n_B := le_trans (le_max_left _ _) hN
  have hone_le : 1 ≤ min n_A n_B := le_trans (le_max_right _ _) hN
  have hnA_pos : 1 ≤ n_A := le_trans hone_le (Nat.min_le_left _ _)
  have hnB_pos : 1 ≤ n_B := le_trans hone_le (Nat.min_le_right _ _)
  have hnB_ge_N₀ : N₀ ≤ n_B := le_trans hN₀_le (Nat.min_le_right _ _)
  -- Nonemptiness of Fin n_A.
  haveI : Nonempty (Fin n_A) := Fin.pos_iff_nonempty.mp hnA_pos
  -- Real values of n_A, n_B.
  have hnB_real_pos : (0 : ℝ) < n_B := by exact_mod_cast hnB_pos
  -- t := δ·n_B·p, the deviation.
  set t : ℝ := δ * (n_B : ℝ) * p with ht_def
  have ht_nn : 0 ≤ t := by rw [ht_def]; positivity
  -- n_B·p > 0 (used as the Chernoff μ).
  have hμ_pos : 0 < (n_B : ℝ) * p := mul_pos hnB_real_pos hp_lb
  -- t < n_B·p (since δ < 1).
  have ht_lt : t < (n_B : ℝ) * p := by
    rw [ht_def]
    have : δ * ((n_B : ℝ) * p) < 1 * ((n_B : ℝ) * p) :=
      mul_lt_mul_of_pos_right hδ1 hμ_pos
    linarith [this]
  -- Rewrite to the Fintype.card form needed by the Chernoff lemma.
  have hcard_eq : (Fintype.card (Fin n_B) : ℝ) = (n_B : ℝ) := by
    rw [Fintype.card_fin]
  -- Apply Chernoff: μ_selector { f | deltaA_selector f < n_B p - t } ≤ exp(-t²/(2(n_B p - t/3))).
  have h_chernoff :=
    @DaveyThesis2024.BipartiteRandomGraph.deltaA_selector_lower_tail_chernoff
      n_A n_B (ENNReal.ofReal p) hp_ofReal _ t ht_nn
      (by rw [hcard_eq, hp_toReal]; exact ht_lt)
      (by rw [hcard_eq, hp_toReal]; exact hμ_pos)
  -- Set up the abbreviations for the measure.
  set μ := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B
    (ENNReal.ofReal p) hp_ofReal).toMeasure with hμ_def
  -- (1 - δ) * n_B * p = n_B * p - t.
  have h_threshold_eq : (1 - δ) * (n_B : ℝ) * p
      = (Fintype.card (Fin n_B) : ℝ) * (ENNReal.ofReal p).toReal - t := by
    rw [hcard_eq, hp_toReal, ht_def]; ring
  -- Exponent bound: -t²/(2(n_B p - t/3)) ≤ -(c · n_B).
  have h_exp_bound :
      Real.exp (- t^2 /
        (2 * ((Fintype.card (Fin n_B) : ℝ) * (ENNReal.ofReal p).toReal - t / 3)))
      ≤ Real.exp (-(c * (n_B : ℝ))) := by
    apply Real.exp_le_exp.mpr
    rw [hcard_eq, hp_toReal]
    -- Want: -t²/(2(n_B p - t/3)) ≤ -(c · n_B).
    -- Equivalently: c · n_B ≤ t² / (2(n_B p - t/3)).
    -- With t = δ n_B p: t² = δ² n_B² p².
    -- 2(n_B p - t/3) = 2 n_B p (1 - δ/3) ≤ 2 n_B p.
    -- So t²/(2(n_B p - t/3)) ≥ δ² n_B² p² / (2 n_B p) = δ² n_B p / 2 = c · n_B.
    have h_denom_pos : 0 < 2 * ((n_B : ℝ) * p - t / 3) := by
      have h_t3_lt : t / 3 < (n_B : ℝ) * p := by linarith [ht_lt]
      linarith
    have h_denom_le : 2 * ((n_B : ℝ) * p - t / 3) ≤ 2 * ((n_B : ℝ) * p) := by
      have : 0 ≤ t / 3 := by linarith
      linarith
    -- c · n_B = δ²·p·n_B / 2 = (δ·n_B·p)·(δ·p) / (2·p) = t · δ / 2... easier route:
    -- Show: c · n_B · (2 · (n_B p - t/3)) ≤ t².
    have hp_nn : 0 ≤ p := hp_lb.le
    rw [neg_div, neg_le_neg_iff]
    -- Goal: c · n_B ≤ t² / (2 (n_B p - t/3))
    rw [le_div_iff₀ h_denom_pos]
    -- Goal: c · n_B · (2 (n_B p - t/3)) ≤ t²
    have h_lhs_le : c * (n_B : ℝ) * (2 * ((n_B : ℝ) * p - t / 3))
        ≤ c * (n_B : ℝ) * (2 * ((n_B : ℝ) * p)) := by
      apply mul_le_mul_of_nonneg_left h_denom_le
      have : 0 ≤ c := hc_pos.le
      positivity
    refine le_trans h_lhs_le ?_
    -- c · n_B · 2 · n_B · p = δ² · n_B² · p² = t²
    rw [hc_def, ht_def]
    ring_nf
    nlinarith [sq_nonneg δ, sq_nonneg ((n_B : ℝ)), sq_nonneg p, hp_lb, hnB_real_pos]
  -- Combine: μ {f | deltaA_selector f < n_B p - t} ≤ exp(-c · n_B) ≤ ε.
  have h_chernoff_eps : μ.real
      {f | (DaveyThesis2024.BipartiteRandomGraph.deltaA_selector f : ℝ)
        < (Fintype.card (Fin n_B) : ℝ) * (ENNReal.ofReal p).toReal - t} ≤ ε := by
    refine le_trans h_chernoff ?_
    refine le_trans h_exp_bound ?_
    exact hN₀ n_B hnB_ge_N₀
  -- Bridge to graph measure via bipartiteRandomMeasure_eq_preimage.
  -- The "bad event" on graphs: ¬ event. Convert to selector via preimage.
  -- We use the explicit bad set on graphs: { G | ¬ (∀ [DecidableRel G.Adj], ...) }.
  set badG : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) :=
    {G | ¬ (∀ [DecidableRel G.Adj],
          (1 - δ) * (n_B : ℝ) * p ≤ (deltaA G : ℝ))} with hbadG_def
  have hbadG_measurable : MeasurableSet badG := MeasurableSet.of_discrete
  -- Show: preimage of badG under boolToBipartiteGraph = {f | deltaA_selector f < n_B p - t}.
  -- Direction: at G = boolToBipartiteGraph f, deltaA G = deltaA_selector f
  -- (via canonical decidability instance; all instances agree).
  have h_preimage_sub :
      DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph ⁻¹' badG
      ⊆ {f | (DaveyThesis2024.BipartiteRandomGraph.deltaA_selector f : ℝ)
          < (Fintype.card (Fin n_B) : ℝ) * (ENNReal.ofReal p).toReal - t} := by
    intro f hf
    simp only [Set.mem_preimage, hbadG_def, Set.mem_setOf_eq] at hf
    push_neg at hf
    -- hf : ∃ inst : DecidableRel (boolToBipartiteGraph f).Adj,
    --        (deltaA (boolToBipartiteGraph f) : ℝ) < (1 - δ) * n_B * p
    obtain ⟨inst, hf_inst⟩ := hf
    -- Show deltaA at this instance equals deltaA_selector f, regardless of instance.
    have h_deltaA_eq :
        @deltaA n_A n_B (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph f) inst
        = DaveyThesis2024.BipartiteRandomGraph.deltaA_selector f := by
      unfold deltaA DaveyThesis2024.BipartiteRandomGraph.deltaA_selector
      apply Finset.sup_congr rfl
      intro a _
      -- G.degree is well-defined: at the canonical instance it equals degAOfSelector,
      -- and at any other instance the result is the same.
      have h_canonical :
        @SimpleGraph.degree _ (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph f)
          (Sum.inl a)
          (@SimpleGraph.neighborSetFintype _ _ _
            (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_decidableAdj f) _)
        = DaveyThesis2024.BipartiteRandomGraph.degAOfSelector f a :=
        DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_degree_inl f a
      -- Both instances give the same degree (any two Fintype instances on the same Set are equal).
      unfold SimpleGraph.degree at h_canonical ⊢
      convert h_canonical using 2
      ext v
      simp only [SimpleGraph.mem_neighborFinset]
    rw [h_deltaA_eq] at hf_inst
    -- hf_inst : (deltaA_selector f : ℝ) < (1 - δ) * n_B * p
    change ((DaveyThesis2024.BipartiteRandomGraph.deltaA_selector f : ℝ)
        < (Fintype.card (Fin n_B) : ℝ) * (ENNReal.ofReal p).toReal - t)
    rw [← h_threshold_eq]
    exact hf_inst
  -- The graph-side measure of badG is ≤ μ-selector measure of preimage ≤ ε.
  have h_badG_le : (DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B
      (ENNReal.ofReal p) hp_ofReal badG).toReal ≤ ε := by
    rw [DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure_eq_preimage
      (ENNReal.ofReal p) hp_ofReal hbadG_measurable]
    -- Goal: (μ (preimage badG)).toReal ≤ ε.
    have h_mono : μ (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph ⁻¹' badG)
        ≤ μ {f | (DaveyThesis2024.BipartiteRandomGraph.deltaA_selector f : ℝ)
          < (Fintype.card (Fin n_B) : ℝ) * (ENNReal.ofReal p).toReal - t} :=
      MeasureTheory.measure_mono h_preimage_sub
    have h_finite : μ {f | (DaveyThesis2024.BipartiteRandomGraph.deltaA_selector f : ℝ)
        < (Fintype.card (Fin n_B) : ℝ) * (ENNReal.ofReal p).toReal - t} ≠ ⊤ :=
      (MeasureTheory.measure_lt_top _ _).ne
    have h_mono_real :
        (μ (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph ⁻¹' badG)).toReal
        ≤ μ.real {f | (DaveyThesis2024.BipartiteRandomGraph.deltaA_selector f : ℝ)
          < (Fintype.card (Fin n_B) : ℝ) * (ENNReal.ofReal p).toReal - t} := by
      unfold MeasureTheory.Measure.real
      exact ENNReal.toReal_mono h_finite h_mono
    linarith [h_mono_real, h_chernoff_eps]
  -- Now compute: probBipartiteRandom = 1 - (measure of bad event).
  unfold probBipartiteRandom DaveyThesis2024.BipartiteRandomGraph.probBipartiteRandomConcrete
  simp only [hp_ofReal, dite_true]
  set ν := DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B
    (ENNReal.ofReal p) hp_ofReal with hν_def
  -- Good set = complement of badG.
  set goodG : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) :=
    {G | ∀ [DecidableRel G.Adj], (1 - δ) * (n_B : ℝ) * p ≤ (deltaA G : ℝ)} with hgoodG_def
  have h_good_compl : goodG = badGᶜ := by
    ext G; simp [hgoodG_def, hbadG_def]
  have h_good_meas : MeasurableSet goodG := MeasurableSet.of_discrete
  -- ν goodG = 1 - ν badG via prob_compl_eq_one_sub.
  have h_good_compl_eq : ν goodG = 1 - ν badG := by
    rw [h_good_compl]
    exact MeasureTheory.prob_compl_eq_one_sub hbadG_measurable
  have h_bad_le_one : ν badG ≤ 1 := by
    rw [show (1 : ENNReal) = ν Set.univ from (MeasureTheory.measure_univ).symm]
    exact MeasureTheory.measure_mono (Set.subset_univ _)
  have h_good_toReal : (ν goodG).toReal = 1 - (ν badG).toReal := by
    rw [h_good_compl_eq, ENNReal.toReal_sub_of_le h_bad_le_one ENNReal.one_ne_top]
    simp
  -- We want (ν goodG).toReal ≥ 1 - ε.
  change ((ν {G | ∀ [DecidableRel G.Adj], (1 - δ) * (n_B : ℝ) * p ≤ (deltaA G : ℝ)}).toReal
    ≥ 1 - ε)
  have h_set_eq : {G | ∀ [DecidableRel G.Adj], (1 - δ) * (n_B : ℝ) * p
      ≤ ((deltaA G) : ℝ)} = goodG := rfl
  rw [h_set_eq, h_good_toReal]
  linarith [h_badG_le]

open DaveyThesis2024.BipartiteRandomGraph in
/-- **deltaB_concentration as a Lean theorem** (mirror of `deltaA_concentration_proof`).
For any fixed `p ∈ (0, 1)` and any `δ, ε > 0`, there exists `N` such that
for all `n_A, n_B ≥ N`, the probability that `Δ_B(G) ≥ (1-δ)·n_A·p` is at
least `1 - ε`.

This is the symmetric mirror of `deltaA_concentration_proof`, obtained by
swapping `A ↔ B`, `Sum.inl ↔ Sum.inr`, `n_A ↔ n_B`. The proof structure
is identical; only indices differ. -/
theorem deltaB_concentration_proof (p : ℝ) (hp_lb : (0 : ℝ) < p) (hp_ub : p < 1) :
    ∀ δ > (0 : ℝ), ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n_A n_B : ℕ,
      min n_A n_B ≥ N →
      probBipartiteRandom n_A n_B p
        (fun G => ∀ [DecidableRel G.Adj],
          (1 - δ) * (n_A : ℝ) * p ≤ (deltaB G : ℝ))
      ≥ 1 - ε := by
  intro δ hδ ε hε
  -- Set up p as ENNReal-valid.
  have hp_ofReal : ENNReal.ofReal p ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_ub.le
  have hp_toReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp_lb.le
  -- Case split on δ ≥ 1: the event is then trivially true (LHS ≤ 0 ≤ deltaB).
  by_cases hδ1 : 1 ≤ δ
  · refine ⟨0, fun n_A n_B _ => ?_⟩
    have h_event : ∀ G : SimpleGraph (Fin n_A ⊕ Fin n_B),
        ∀ [DecidableRel G.Adj],
        (1 - δ) * (n_A : ℝ) * p ≤ (deltaB G : ℝ) := by
      intro G _
      have h_lhs_nonpos : (1 - δ) * (n_A : ℝ) * p ≤ 0 := by
        have h1 : 1 - δ ≤ 0 := by linarith
        have h2 : 0 ≤ (n_A : ℝ) := Nat.cast_nonneg _
        have h3 : (1 - δ) * (n_A : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 h2
        exact mul_nonpos_of_nonpos_of_nonneg h3 hp_lb.le
      exact le_trans h_lhs_nonpos (Nat.cast_nonneg _)
    have h_prob_eq_one : probBipartiteRandom n_A n_B p
        (fun G => ∀ [DecidableRel G.Adj],
          (1 - δ) * (n_A : ℝ) * p ≤ (deltaB G : ℝ)) = 1 := by
      unfold probBipartiteRandom DaveyThesis2024.BipartiteRandomGraph.probBipartiteRandomConcrete
      simp only [hp_ofReal, dite_true]
      have h_univ : {G : SimpleGraph (Fin n_A ⊕ Fin n_B) |
          ∀ [DecidableRel G.Adj], (1 - δ) * (n_A : ℝ) * p ≤ (deltaB G : ℝ)}
          = Set.univ := Set.eq_univ_of_forall h_event
      rw [h_univ, MeasureTheory.measure_univ]
      simp
    rw [h_prob_eq_one]; linarith
  -- Main case: 0 < δ < 1.
  push_neg at hδ1
  -- Threshold c := δ²·p/2 > 0.
  set c : ℝ := δ^2 * p / 2 with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]; positivity
  obtain ⟨N₀, hN₀⟩ := exists_N_exp_neg_le_eps c ε hc_pos hε
  refine ⟨max N₀ 1, fun n_A n_B hN => ?_⟩
  -- From min n_A n_B ≥ max N₀ 1, derive n_B ≥ 1 and n_A ≥ N₀.
  have hN₀_le : N₀ ≤ min n_A n_B := le_trans (le_max_left _ _) hN
  have hone_le : 1 ≤ min n_A n_B := le_trans (le_max_right _ _) hN
  have hnA_pos : 1 ≤ n_A := le_trans hone_le (Nat.min_le_left _ _)
  have hnB_pos : 1 ≤ n_B := le_trans hone_le (Nat.min_le_right _ _)
  have hnA_ge_N₀ : N₀ ≤ n_A := le_trans hN₀_le (Nat.min_le_left _ _)
  -- Nonemptiness of Fin n_B.
  haveI : Nonempty (Fin n_B) := Fin.pos_iff_nonempty.mp hnB_pos
  -- Real values.
  have hnA_real_pos : (0 : ℝ) < n_A := by exact_mod_cast hnA_pos
  -- t := δ·n_A·p, the deviation.
  set t : ℝ := δ * (n_A : ℝ) * p with ht_def
  have ht_nn : 0 ≤ t := by rw [ht_def]; positivity
  -- n_A·p > 0 (used as the Chernoff μ).
  have hμ_pos : 0 < (n_A : ℝ) * p := mul_pos hnA_real_pos hp_lb
  -- t < n_A·p (since δ < 1).
  have ht_lt : t < (n_A : ℝ) * p := by
    rw [ht_def]
    have : δ * ((n_A : ℝ) * p) < 1 * ((n_A : ℝ) * p) :=
      mul_lt_mul_of_pos_right hδ1 hμ_pos
    linarith [this]
  have hcard_eq : (Fintype.card (Fin n_A) : ℝ) = (n_A : ℝ) := by
    rw [Fintype.card_fin]
  -- Apply B-side Chernoff.
  have h_chernoff :=
    @DaveyThesis2024.BipartiteRandomGraph.deltaB_selector_lower_tail_chernoff
      n_A n_B (ENNReal.ofReal p) hp_ofReal _ t ht_nn
      (by rw [hcard_eq, hp_toReal]; exact ht_lt)
      (by rw [hcard_eq, hp_toReal]; exact hμ_pos)
  set μ := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B
    (ENNReal.ofReal p) hp_ofReal).toMeasure with hμ_def
  -- (1 - δ) * n_A * p = n_A * p - t.
  have h_threshold_eq : (1 - δ) * (n_A : ℝ) * p
      = (Fintype.card (Fin n_A) : ℝ) * (ENNReal.ofReal p).toReal - t := by
    rw [hcard_eq, hp_toReal, ht_def]; ring
  -- Exponent bound.
  have h_exp_bound :
      Real.exp (- t^2 /
        (2 * ((Fintype.card (Fin n_A) : ℝ) * (ENNReal.ofReal p).toReal - t / 3)))
      ≤ Real.exp (-(c * (n_A : ℝ))) := by
    apply Real.exp_le_exp.mpr
    rw [hcard_eq, hp_toReal]
    have h_denom_pos : 0 < 2 * ((n_A : ℝ) * p - t / 3) := by
      have h_t3_lt : t / 3 < (n_A : ℝ) * p := by linarith [ht_lt]
      linarith
    have h_denom_le : 2 * ((n_A : ℝ) * p - t / 3) ≤ 2 * ((n_A : ℝ) * p) := by
      have : 0 ≤ t / 3 := by linarith
      linarith
    have hp_nn : 0 ≤ p := hp_lb.le
    rw [neg_div, neg_le_neg_iff]
    rw [le_div_iff₀ h_denom_pos]
    have h_lhs_le : c * (n_A : ℝ) * (2 * ((n_A : ℝ) * p - t / 3))
        ≤ c * (n_A : ℝ) * (2 * ((n_A : ℝ) * p)) := by
      apply mul_le_mul_of_nonneg_left h_denom_le
      have : 0 ≤ c := hc_pos.le
      positivity
    refine le_trans h_lhs_le ?_
    rw [hc_def, ht_def]
    ring_nf
    nlinarith [sq_nonneg δ, sq_nonneg ((n_A : ℝ)), sq_nonneg p, hp_lb, hnA_real_pos]
  -- Combine: μ {f | deltaB_selector f < n_A p - t} ≤ exp(-c · n_A) ≤ ε.
  have h_chernoff_eps : μ.real
      {f | (DaveyThesis2024.BipartiteRandomGraph.deltaB_selector f : ℝ)
        < (Fintype.card (Fin n_A) : ℝ) * (ENNReal.ofReal p).toReal - t} ≤ ε := by
    refine le_trans h_chernoff ?_
    refine le_trans h_exp_bound ?_
    exact hN₀ n_A hnA_ge_N₀
  -- Bridge to graph measure.
  set badG : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) :=
    {G | ¬ (∀ [DecidableRel G.Adj],
          (1 - δ) * (n_A : ℝ) * p ≤ (deltaB G : ℝ))} with hbadG_def
  have hbadG_measurable : MeasurableSet badG := MeasurableSet.of_discrete
  have h_preimage_sub :
      DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph ⁻¹' badG
      ⊆ {f | (DaveyThesis2024.BipartiteRandomGraph.deltaB_selector f : ℝ)
          < (Fintype.card (Fin n_A) : ℝ) * (ENNReal.ofReal p).toReal - t} := by
    intro f hf
    simp only [Set.mem_preimage, hbadG_def, Set.mem_setOf_eq] at hf
    push_neg at hf
    obtain ⟨inst, hf_inst⟩ := hf
    have h_deltaB_eq :
        @deltaB n_A n_B (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph f) inst
        = DaveyThesis2024.BipartiteRandomGraph.deltaB_selector f := by
      unfold deltaB DaveyThesis2024.BipartiteRandomGraph.deltaB_selector
      apply Finset.sup_congr rfl
      intro b _
      have h_canonical :
        @SimpleGraph.degree _ (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph f)
          (Sum.inr b)
          (@SimpleGraph.neighborSetFintype _ _ _
            (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_decidableAdj f) _)
        = DaveyThesis2024.BipartiteRandomGraph.degBOfSelector f b :=
        DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_degree_inr f b
      unfold SimpleGraph.degree at h_canonical ⊢
      convert h_canonical using 2
      ext v
      simp only [SimpleGraph.mem_neighborFinset]
    rw [h_deltaB_eq] at hf_inst
    change ((DaveyThesis2024.BipartiteRandomGraph.deltaB_selector f : ℝ)
        < (Fintype.card (Fin n_A) : ℝ) * (ENNReal.ofReal p).toReal - t)
    rw [← h_threshold_eq]
    exact hf_inst
  have h_badG_le : (DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B
      (ENNReal.ofReal p) hp_ofReal badG).toReal ≤ ε := by
    rw [DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure_eq_preimage
      (ENNReal.ofReal p) hp_ofReal hbadG_measurable]
    have h_mono : μ (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph ⁻¹' badG)
        ≤ μ {f | (DaveyThesis2024.BipartiteRandomGraph.deltaB_selector f : ℝ)
          < (Fintype.card (Fin n_A) : ℝ) * (ENNReal.ofReal p).toReal - t} :=
      MeasureTheory.measure_mono h_preimage_sub
    have h_finite : μ {f | (DaveyThesis2024.BipartiteRandomGraph.deltaB_selector f : ℝ)
        < (Fintype.card (Fin n_A) : ℝ) * (ENNReal.ofReal p).toReal - t} ≠ ⊤ :=
      (MeasureTheory.measure_lt_top _ _).ne
    have h_mono_real :
        (μ (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph ⁻¹' badG)).toReal
        ≤ μ.real {f | (DaveyThesis2024.BipartiteRandomGraph.deltaB_selector f : ℝ)
          < (Fintype.card (Fin n_A) : ℝ) * (ENNReal.ofReal p).toReal - t} := by
      unfold MeasureTheory.Measure.real
      exact ENNReal.toReal_mono h_finite h_mono
    linarith [h_mono_real, h_chernoff_eps]
  unfold probBipartiteRandom DaveyThesis2024.BipartiteRandomGraph.probBipartiteRandomConcrete
  simp only [hp_ofReal, dite_true]
  set ν := DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B
    (ENNReal.ofReal p) hp_ofReal with hν_def
  set goodG : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) :=
    {G | ∀ [DecidableRel G.Adj], (1 - δ) * (n_A : ℝ) * p ≤ (deltaB G : ℝ)} with hgoodG_def
  have h_good_compl : goodG = badGᶜ := by
    ext G; simp [hgoodG_def, hbadG_def]
  have h_good_compl_eq : ν goodG = 1 - ν badG := by
    rw [h_good_compl]
    exact MeasureTheory.prob_compl_eq_one_sub hbadG_measurable
  have h_bad_le_one : ν badG ≤ 1 := by
    rw [show (1 : ENNReal) = ν Set.univ from (MeasureTheory.measure_univ).symm]
    exact MeasureTheory.measure_mono (Set.subset_univ _)
  have h_good_toReal : (ν goodG).toReal = 1 - (ν badG).toReal := by
    rw [h_good_compl_eq, ENNReal.toReal_sub_of_le h_bad_le_one ENNReal.one_ne_top]
    simp
  change ((ν {G | ∀ [DecidableRel G.Adj], (1 - δ) * (n_A : ℝ) * p ≤ (deltaB G : ℝ)}).toReal
    ≥ 1 - ε)
  have h_set_eq : {G | ∀ [DecidableRel G.Adj], (1 - δ) * (n_A : ℝ) * p
      ≤ ((deltaB G) : ℝ)} = goodG := rfl
  rw [h_set_eq, h_good_toReal]
  linarith [h_badG_le]

/-! ## Polynomial-dominates-log threshold (Phase A arithmetic helper)

For the main `secRandomBipartite_aas` assembly: we need to choose `N` such
that for all `n ≥ N`, `C·n²·p / log(n²) ≤ (1-δ)²·n²·p²` (so the nibble bound
beats the BQM bound). Equivalent: `1/log(n²) ≤ (1-δ)²·p / C`, so
`log(n²) ≥ C / ((1-δ)²·p)`, so `n² ≥ exp(C/((1-δ)²·p))`. -/

/-- Arithmetic threshold: given `C, R > 0`, there is `N` such that for all
`n ≥ N`, `1 / Real.log (n : ℝ) ≤ R` (when `n ≥ 2` so `log n > 0`). -/
lemma exists_N_one_div_log_le (R : ℝ) (hR_pos : 0 < R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (1 : ℝ) / Real.log n ≤ R := by
  set threshold : ℝ := Real.exp (1 / R) with hthr_def
  have hthr_pos : 0 < threshold := Real.exp_pos _
  refine ⟨max 2 ⌈threshold⌉₊, fun n hn => ?_⟩
  have h2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hthr_le : threshold ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (le_trans (le_max_right _ _) hn))
  -- log n ≥ log threshold = 1/R, hence 1/log n ≤ R.
  have hlog_n_pos : 0 < Real.log n := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < n)
  have hlog_ge : 1 / R ≤ Real.log n := by
    have := Real.log_le_log hthr_pos hthr_le
    rw [hthr_def, Real.log_exp] at this
    exact this
  rw [div_le_iff₀ hlog_n_pos]
  rw [div_le_iff₀ hR_pos] at hlog_ge
  linarith

/-! ## Section 4: Probabilistic core axioms

The following axioms encode the probabilistic content of the proof.
Each is *atomic* (corresponds to a single mathematical claim) and has
a three-section docstring per the project's convention:
**Statement** (what is claimed), **Why needed** (which lemma uses it),
**Why correct** (mathematical justification). -/

/-- **deltaA_concentration as a Lean theorem** (formerly axiom, eliminated
2026-06-01 cycle 36).

**Statement.** For random bipartite `G ~ G(n_A, n_B, p)` at any fixed
constant `p ∈ (0, 1)`, the A-side maximum degree concentrates near its
expectation `n_B · p`: for any `δ > 0`, `Δ_A(G) ≥ (1 - δ) · n_B · p`
with probability tending to 1.

Alias for `deltaA_concentration_proof` (proved via the selector-side
Chernoff stack — see cycle 34). -/
alias deltaA_concentration := deltaA_concentration_proof

/-- **deltaB_concentration as a Lean theorem** (formerly axiom, eliminated
2026-06-01 cycle 36). Symmetric of `deltaA_concentration`.

Alias for `deltaB_concentration_proof` (proved via the selector-side
Chernoff stack, B-side mirror — see cycle 35). -/
alias deltaB_concentration := deltaB_concentration_proof

/-! ### Note (Phase F.7.4+F.7.5, 2026-06-02): nibble-bound decomposition

The previously-monolithic axiom `chiPrimeS_nibble_quantitative_bound`
has been **decomposed** into:

* an *atomic* axiom `perPair_packing_aas_FKS` (residual probabilistic
  content of FKS Lemma 7.B — existence of a `PerPairCover` family
  a.a.s.); and
* a *theorem* `chiPrimeS_nibble_quantitative_bound` (deterministic
  reduction via cycle-21 `chiPrimeS_le_of_perPairCover_family`).

Both live in `DaveyThesis2024.SecRandomBipartite.PairPacking` (downstream of this
file). They are still in the `SECRandomBipartite` namespace, so the
fully-qualified reference
`SECRandomBipartite.chiPrimeS_nibble_quantitative_bound` continues to
resolve. The dependent headline `secRandomBipartite_aas` was likewise
relocated to `DaveyThesis2024.SecRandomBipartite.PairPacking` (same namespace),
because its proof body needs the now-theorem
`chiPrimeS_nibble_quantitative_bound` whose dependency
`chiPrimeS_le_of_perPairCover_family` lives in PairPacking. The cycle
`SECRandomBipartite ← CN.Setup ← CN.PairPacking ← SECRandomBipartite`
prevented an in-place rewrite.

Net axiom count unchanged (still 1), but the residual is now precisely
the FKS Lemma 7.B output rather than a black-box nibble bound. -/

/-- **Bonferroni / inclusion-exclusion.** For any two events `E1, E2`,
the probability of their intersection is at least the sum of their
probabilities minus 1.

Formerly an axiom; now a theorem provable from the underlying probability
measure structure (Refactor-1.F, 2026-06-01). -/
theorem probBipartiteRandom_inter_bound (n_A n_B : ℕ) (p : ℝ)
    (E1 E2 : SimpleGraph (Fin n_A ⊕ Fin n_B) → Prop) :
    probBipartiteRandom n_A n_B p (fun G => E1 G ∧ E2 G)
    ≥ probBipartiteRandom n_A n_B p E1 + probBipartiteRandom n_A n_B p E2 - 1 := by
  unfold probBipartiteRandom DaveyThesis2024.BipartiteRandomGraph.probBipartiteRandomConcrete
  by_cases hp : ENNReal.ofReal p ≤ 1
  · simp only [hp, dite_true]
    set μ := DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B
      (ENNReal.ofReal p) hp
    set s1 : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) := {G | E1 G}
    set s2 : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) := {G | E2 G}
    have h_inter : {G | E1 G ∧ E2 G} = s1 ∩ s2 := rfl
    rw [h_inter]
    -- Inclusion-exclusion: μ(s1) + μ(s2) = μ(s1 ∪ s2) + μ(s1 ∩ s2)
    -- so μ(s1 ∩ s2) = μ(s1) + μ(s2) - μ(s1 ∪ s2) ≥ μ(s1) + μ(s2) - 1.
    have h_union_le : μ (s1 ∪ s2) ≤ 1 :=
      le_trans (MeasureTheory.measure_mono (Set.subset_univ _))
        (le_of_eq (MeasureTheory.measure_univ))
    have h_inex : μ s1 + μ s2 = μ (s1 ∪ s2) + μ (s1 ∩ s2) :=
      (MeasureTheory.measure_union_add_inter s1 (MeasurableSet.of_discrete)).symm
    have h_finite_s1 : μ s1 ≠ ⊤ :=
      (MeasureTheory.measure_lt_top μ s1).ne
    have h_finite_s2 : μ s2 ≠ ⊤ :=
      (MeasureTheory.measure_lt_top μ s2).ne
    have h_finite_union : μ (s1 ∪ s2) ≠ ⊤ :=
      (MeasureTheory.measure_lt_top μ (s1 ∪ s2)).ne
    have h_finite_inter : μ (s1 ∩ s2) ≠ ⊤ :=
      (MeasureTheory.measure_lt_top μ (s1 ∩ s2)).ne
    -- Move to ENNReal toReal
    have h_inex_real : (μ s1).toReal + (μ s2).toReal
        = (μ (s1 ∪ s2)).toReal + (μ (s1 ∩ s2)).toReal := by
      rw [← ENNReal.toReal_add h_finite_s1 h_finite_s2,
          ← ENNReal.toReal_add h_finite_union h_finite_inter, h_inex]
    have h_union_le_real : (μ (s1 ∪ s2)).toReal ≤ 1 := by
      have h1 : (1 : ℝ) = (1 : ENNReal).toReal := by simp
      rw [h1]
      exact ENNReal.toReal_mono ENNReal.one_ne_top h_union_le
    linarith
  · simp only [hp, dite_false]; linarith

/-! ## Section 5: Main theorem

`secRandomBipartite_aas` was moved to `DaveyThesis2024.SecRandomBipartite.PairPacking`
(downstream file, same `SECRandomBipartite` namespace). See the note
preceding `probBipartiteRandom_inter_bound` above. -/

end SECRandomBipartite
