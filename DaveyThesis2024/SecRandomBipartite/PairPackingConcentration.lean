/-
Copyright (c) 2026 Ross Kang.
Released under Apache 2.0 license.

# Phase F.7.1 — Per-pair edge-count concentration

For random bipartite `G ~ G(n_A, n_B, p)` and any block pair `(S, T)`,
`|crossBlockPairs G S T|` concentrates around `|S| · |T| · p` (the
expected value). This is the first probabilistic input to the bipartite
SCI bipartite chain (FKS Lemma 6 part 2 analog).

## Status
Phase F.7.1 cycle 23 (2026-06-02): scaffold + full-product `iIndepFun`.
-/

import DaveyThesis2024.SecRandomBipartite.PairPacking
import DaveyThesis2024.BipartiteRandomGraph
import DaveyThesis2024.Concentration

namespace DaveyThesis2024.SecRandomBipartite

open DaveyThesis2024.BipartiteRandomGraph

/-! ## Full-product `iIndepFun` for `edgeIndicator`

`edgeIndicator_iIndepFun` (BipartiteRandomGraph.lean) gives independence
for the *row* family `{edgeIndicator a b}_(b ∈ Fin n_B)` for fixed `a`.
For the per-pair edge concentration, we need the **full-product** family
`{edgeIndicator a b}_((a, b) ∈ Fin n_A × Fin n_B)`. This drops the
row-restriction in the proof — just apply `iIndepFun_pi` directly. -/

variable {n_A n_B : ℕ}

open ProbabilityTheory in
/-- Full-product independence: the family of all `edgeIndicator a b`,
indexed by `(a, b) : Fin n_A × Fin n_B`, is mutually independent under
the bipartite edge-choice measure.

Mirrors `edgeIndicator_iIndepFun` (which is the row-restricted version
via `.precomp`) but does not precompose — we use the natural product
index. -/
theorem edgeIndicator_full_iIndepFun (p : ENNReal) (hp : p ≤ 1) :
    iIndepFun (fun ab : Fin n_A × Fin n_B => edgeIndicator ab.1 ab.2)
      ((bipartiteEdgeChoice n_A n_B p hp).toMeasure) := by
  classical
  -- Per-slot indicator on Bool.
  let toReal : Bool → ℝ := fun β => if β = true then (1 : ℝ) else 0
  -- `iIndepFun_pi` over the full index set Fin n_A × Fin n_B.
  have h_full :
      iIndepFun
        (fun (e : Fin n_A × Fin n_B) (ω : Fin n_A × Fin n_B → Bool) => toReal (ω e))
        (MeasureTheory.Measure.pi (fun _ : Fin n_A × Fin n_B => (slotPMF p hp).toMeasure)) :=
    iIndepFun_pi (fun _ => Measurable.of_discrete.aemeasurable)
  -- Transport via the bridge lemma.
  rw [bipartiteEdgeChoice_toMeasure_eq_pi p hp]
  -- The functions agree pointwise.
  exact h_full

/-! ## Sum-of-indicators identity for crossBlockPairs cardinality

`(crossBlockPairs (boolToBipartiteGraph f) S T).card = ∑ ab ∈ S × T,
edgeIndicator ab.1 ab.2 f` (cast to ℝ). Mirrors `sum_edgeIndicator_eq_degA`
(BipartiteRandomGraph.lean:207) for the per-pair-pair case. -/

/-- Cardinality of `crossBlockPairs` for `boolToBipartiteGraph f` equals
the sum of edge-indicators over `S ×ˢ T`. -/
lemma crossBlockPairs_card_eq_sum_edgeIndicator
    (S : Finset (Fin n_A)) (T : Finset (Fin n_B))
    (f : Fin n_A × Fin n_B → Bool) :
    ((crossBlockPairs (boolToBipartiteGraph f) S T).card : ℝ)
      = ∑ ab ∈ S ×ˢ T, edgeIndicator ab.1 ab.2 f := by
  classical
  unfold crossBlockPairs
  have h_filter : (S ×ˢ T).filter
        (fun ab => (boolToBipartiteGraph f).Adj (Sum.inl ab.1) (Sum.inr ab.2))
      = (S ×ˢ T).filter (fun ab => f (ab.1, ab.2) = true) := by
    apply Finset.filter_congr
    intro ab _
    exact boolToBipartiteGraph_adj_inl_inr f ab.1 ab.2
  rw [h_filter, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro ab _
  unfold edgeIndicator
  by_cases h : f (ab.1, ab.2) = true <;> simp [h]

/-! ## Per-pair upper tail (selector-side Chernoff)

Apply `chernoff_A2_upper` to the family `{edgeIndicator ab.1 ab.2}_(ab ∈ S × T)`,
using `edgeIndicator_full_iIndepFun` for independence and the cycle 24
identity to translate to crossBlockPairs cardinality. -/

open DaveyThesis2024.Concentration

/-- Selector-side Chernoff upper tail for `|crossBlockPairs|`. -/
lemma crossBlockPairs_selector_upper_tail
    (p : ENNReal) (hp : p ≤ 1)
    (S : Finset (Fin n_A)) (T : Finset (Fin n_B))
    (t : ℝ) (ht : 0 ≤ t)
    (h_μ_pos : 0 < ((S ×ˢ T).card : ℝ) * p.toReal) :
    ((bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
      {f | ((S ×ˢ T).card : ℝ) * p.toReal + t
            ≤ ((crossBlockPairs (boolToBipartiteGraph f) S T).card : ℝ)}
    ≤ Real.exp (- t^2 / (2 * (((S ×ˢ T).card : ℝ) * p.toReal + t / 3))) := by
  set μ := (bipartiteEdgeChoice n_A n_B p hp).toMeasure
  have h_p_bounds : ∀ _ : Fin n_A × Fin n_B, 0 ≤ p.toReal ∧ p.toReal ≤ 1 :=
    fun _ => ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal (by norm_num)
      (by rw [ENNReal.ofReal_one]; exact hp)⟩
  have h_sum_p : (∑ _ ∈ S ×ˢ T, p.toReal) = ((S ×ˢ T).card : ℝ) * p.toReal := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h_μ_pos_sum : 0 < ∑ _ ∈ S ×ˢ T, p.toReal := by rw [h_sum_p]; exact h_μ_pos
  have h_chernoff := chernoff_A2_upper (μ := μ) (s := S ×ˢ T)
    (X := fun ab : Fin n_A × Fin n_B => edgeIndicator ab.1 ab.2)
    (edgeIndicator_full_iIndepFun p hp)
    (fun ab => measurable_edgeIndicator ab.1 ab.2)
    (fun ab f => edgeIndicator_indicator ab.1 ab.2 f)
    (fun _ => p.toReal)
    h_p_bounds
    (fun ab => integral_edgeIndicator_eq p hp ab.1 ab.2)
    t ht h_μ_pos_sum
  -- Translate ∑ ab, edgeIndicator → crossBlockPairs.card
  have h_set_eq :
      {f : Fin n_A × Fin n_B → Bool |
          (∑ _ ∈ S ×ˢ T, p.toReal) + t ≤ ∑ ab ∈ S ×ˢ T, edgeIndicator ab.1 ab.2 f}
      = {f |
          ((S ×ˢ T).card : ℝ) * p.toReal + t
            ≤ ((crossBlockPairs (boolToBipartiteGraph f) S T).card : ℝ)} := by
    ext f
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
        crossBlockPairs_card_eq_sum_edgeIndicator S T f, h_sum_p]
  rw [h_set_eq] at h_chernoff
  rw [h_sum_p] at h_chernoff
  exact h_chernoff

/-! ## Instance-independence of `crossBlockPairs.card`

For the graph-side lift, we need to convert `∀ [DecidableRel G.Adj], ...`
into the canonical-instance form (where `crossBlockPairs` uses
`boolToBipartiteGraph_decidableAdj f`). Since `Decidable` is a
Subsingleton, `crossBlockPairs G S T` as a Finset is the same
regardless of which `DecidableRel` instance is used. -/

/-- `crossBlockPairs G S T` is independent of the `DecidableRel G.Adj`
instance: any two instances give the same Finset (and hence the same
cardinality). Standard instance-uniqueness for `Decidable`. -/
lemma crossBlockPairs_inst_indep
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B))
    (S : Finset (Fin n_A)) (T : Finset (Fin n_B))
    (inst1 inst2 : DecidableRel G.Adj) :
    @crossBlockPairs n_A n_B G inst1 S T = @crossBlockPairs n_A n_B G inst2 S T := by
  ext ab
  rw [@mem_crossBlockPairs _ _ G inst1, @mem_crossBlockPairs _ _ G inst2]

/-! ## Graph-side upper tail (lift via `bipartiteRandomMeasure_eq_preimage`) -/

/-- Graph-side Chernoff upper tail for the per-pair edge count. -/
lemma crossBlockPairs_graph_upper_tail
    (p : ENNReal) (hp : p ≤ 1)
    (S : Finset (Fin n_A)) (T : Finset (Fin n_B))
    (t : ℝ) (ht : 0 ≤ t)
    (h_μ_pos : 0 < ((S ×ˢ T).card : ℝ) * p.toReal) :
    (bipartiteRandomMeasure n_A n_B p hp).real
      {G : SimpleGraph (Fin n_A ⊕ Fin n_B) | ∃ inst : DecidableRel G.Adj,
        ((S ×ˢ T).card : ℝ) * p.toReal + t
          ≤ ((@crossBlockPairs n_A n_B G inst S T).card : ℝ)}
    ≤ Real.exp (- t^2 / (2 * (((S ×ˢ T).card : ℝ) * p.toReal + t / 3))) := by
  set μ := (bipartiteEdgeChoice n_A n_B p hp).toMeasure
  set ν := bipartiteRandomMeasure n_A n_B p hp
  set badG : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) :=
    {G | ∃ inst : DecidableRel G.Adj,
      ((S ×ˢ T).card : ℝ) * p.toReal + t
        ≤ ((@crossBlockPairs n_A n_B G inst S T).card : ℝ)} with hbadG_def
  have hbadG_meas : MeasurableSet badG := MeasurableSet.of_discrete
  set selBad : Set (Fin n_A × Fin n_B → Bool) :=
    {f | ((S ×ˢ T).card : ℝ) * p.toReal + t
          ≤ ((crossBlockPairs (boolToBipartiteGraph f) S T).card : ℝ)}
    with hselBad_def
  have h_preimage_sub : boolToBipartiteGraph ⁻¹' badG ⊆ selBad := by
    intro f hf
    simp only [Set.mem_preimage, hbadG_def, Set.mem_setOf_eq] at hf
    obtain ⟨inst, hf_inst⟩ := hf
    -- Convert to the canonical-instance form via cycle 26.
    simp only [hselBad_def, Set.mem_setOf_eq]
    rwa [crossBlockPairs_inst_indep (boolToBipartiteGraph f) S T
      (boolToBipartiteGraph_decidableAdj f) inst]
  -- Apply cycle 25 + measure pull-back.
  calc ν.real badG
      = μ.real (boolToBipartiteGraph ⁻¹' badG) := by
        unfold MeasureTheory.Measure.real
        rw [bipartiteRandomMeasure_eq_preimage p hp hbadG_meas]
    _ ≤ μ.real selBad := by
        unfold MeasureTheory.Measure.real
        exact ENNReal.toReal_mono (MeasureTheory.measure_lt_top _ _).ne
          (MeasureTheory.measure_mono h_preimage_sub)
    _ ≤ Real.exp _ := crossBlockPairs_selector_upper_tail p hp S T t ht h_μ_pos

/-! ## Good-event form (complement) -/

/-- Complementary form: the **good event** that `|crossBlockPairs G S T|`
stays below the Chernoff threshold has probability ≥ `1 - exp(...)`. -/
lemma crossBlockPairs_graph_concentration_lower
    (p : ENNReal) (hp : p ≤ 1)
    (S : Finset (Fin n_A)) (T : Finset (Fin n_B))
    (t : ℝ) (ht : 0 ≤ t)
    (h_μ_pos : 0 < ((S ×ˢ T).card : ℝ) * p.toReal) :
    (bipartiteRandomMeasure n_A n_B p hp).real
      {G : SimpleGraph (Fin n_A ⊕ Fin n_B) | ∀ [inst : DecidableRel G.Adj],
        ((@crossBlockPairs n_A n_B G inst S T).card : ℝ)
          < ((S ×ˢ T).card : ℝ) * p.toReal + t}
    ≥ 1 - Real.exp (- t^2 / (2 * (((S ×ˢ T).card : ℝ) * p.toReal + t / 3))) := by
  set ν := bipartiteRandomMeasure n_A n_B p hp
  set badG : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) :=
    {G | ∃ inst : DecidableRel G.Adj,
      ((S ×ˢ T).card : ℝ) * p.toReal + t
        ≤ ((@crossBlockPairs n_A n_B G inst S T).card : ℝ)} with hbadG_def
  set goodG : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) :=
    {G | ∀ [inst : DecidableRel G.Adj],
      ((@crossBlockPairs n_A n_B G inst S T).card : ℝ)
        < ((S ×ˢ T).card : ℝ) * p.toReal + t} with hgoodG_def
  have h_good_compl : goodG = badGᶜ := by
    ext G
    simp only [hgoodG_def, hbadG_def, Set.mem_setOf_eq, Set.mem_compl_iff,
               not_exists, not_le]
  have h_bad_meas : MeasurableSet badG := MeasurableSet.of_discrete
  -- ν goodG = 1 - ν badG via prob_compl
  have h_good_compl_eq : ν goodG = 1 - ν badG := by
    rw [h_good_compl]; exact MeasureTheory.prob_compl_eq_one_sub h_bad_meas
  have h_bad_finite : ν badG ≠ ⊤ := (MeasureTheory.measure_lt_top _ _).ne
  have h_bad_le_one : ν badG ≤ 1 := by
    rw [show (1 : ENNReal) = ν Set.univ from (MeasureTheory.measure_univ).symm]
    exact MeasureTheory.measure_mono (Set.subset_univ _)
  have h_good_toReal : (ν goodG).toReal = 1 - (ν badG).toReal := by
    rw [h_good_compl_eq, ENNReal.toReal_sub_of_le h_bad_le_one ENNReal.one_ne_top]; simp
  have h_bad_le : ν.real badG
      ≤ Real.exp (- t^2 / (2 * (((S ×ˢ T).card : ℝ) * p.toReal + t / 3))) :=
    crossBlockPairs_graph_upper_tail p hp S T t ht h_μ_pos
  change (ν goodG).toReal ≥ _
  rw [h_good_toReal]
  unfold MeasureTheory.Measure.real at h_bad_le
  linarith

/-! ## Cycle 29 — specialisation to `t := M^(3/4)` -/

/-- Specialisation of cycle 28 with `t := |S × T|^(3/4)`: the deviation used
in the bipartite analog of FKS Lemma 6.B. -/
lemma crossBlockPairs_three_fourths_lower
    (p : ENNReal) (hp : p ≤ 1) (hp_pos : 0 < p.toReal)
    (S : Finset (Fin n_A)) (T : Finset (Fin n_B))
    (h_card_pos : 0 < (S ×ˢ T).card) :
    (bipartiteRandomMeasure n_A n_B p hp).real
      {G : SimpleGraph (Fin n_A ⊕ Fin n_B) | ∀ [inst : DecidableRel G.Adj],
        ((@crossBlockPairs n_A n_B G inst S T).card : ℝ)
          < ((S ×ˢ T).card : ℝ) * p.toReal
            + ((S ×ˢ T).card : ℝ) ^ ((3 : ℝ) / 4)}
    ≥ 1 - Real.exp (- (((S ×ˢ T).card : ℝ) ^ ((3 : ℝ) / 4))^2
                     / (2 * (((S ×ˢ T).card : ℝ) * p.toReal
                         + ((S ×ˢ T).card : ℝ) ^ ((3 : ℝ) / 4) / 3))) := by
  have h_M_pos : 0 < ((S ×ˢ T).card : ℝ) := by exact_mod_cast h_card_pos
  have h_t_nn : 0 ≤ ((S ×ˢ T).card : ℝ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg h_M_pos.le _
  have h_μ_pos : 0 < ((S ×ˢ T).card : ℝ) * p.toReal := mul_pos h_M_pos hp_pos
  exact crossBlockPairs_graph_concentration_lower p hp S T _ h_t_nn h_μ_pos

/-! ## Cycle 30 — a.a.s. headline with multiplicative deviation `t := M·δ`

The cleaner-arithmetic form: for any `δ > 0`, the event
`|crossBlockPairs G S T| < (p + δ)·|S × T|` holds a.a.s. as
`|S × T| → ∞`. Sufficient for the FKS argument (modulo absorbing `δ`
into the headline constant `C`). -/

/-- F.7.1 a.a.s. headline: per-pair edge count concentrates within
multiplicative `δ` of the mean, a.a.s. as `|S × T| → ∞`. -/
theorem crossBlockPairs_concentration_aas
    (p : ENNReal) (hp : p ≤ 1) (hp_pos : 0 < p.toReal)
    (δ : ℝ) (hδ_pos : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (S : Finset (Fin n_A)) (T : Finset (Fin n_B)),
      N ≤ (S ×ˢ T).card →
      (bipartiteRandomMeasure n_A n_B p hp).real
        {G : SimpleGraph (Fin n_A ⊕ Fin n_B) | ∀ [inst : DecidableRel G.Adj],
          ((@crossBlockPairs n_A n_B G inst S T).card : ℝ)
            < ((S ×ˢ T).card : ℝ) * (p.toReal + δ)}
      ≥ 1 - ε := by
  -- Chernoff coefficient: c := δ² / (2(p + δ/3))
  set c : ℝ := δ^2 / (2 * (p.toReal + δ/3)) with hc_def
  have hp_plus_δ_third_pos : 0 < p.toReal + δ/3 := by linarith
  have hc_pos : 0 < c := by rw [hc_def]; positivity
  -- N₀ such that for n ≥ N₀, exp(-c·n) ≤ ε
  obtain ⟨N₀, hN₀⟩ := SECRandomBipartite.exists_N_exp_neg_le_eps c ε hc_pos hε
  refine ⟨max N₀ 1, ?_⟩
  intro S T hST
  have hN₀_le : N₀ ≤ (S ×ˢ T).card := le_trans (le_max_left _ _) hST
  have hone_le : 1 ≤ (S ×ˢ T).card := le_trans (le_max_right _ _) hST
  set M : ℝ := ((S ×ˢ T).card : ℝ) with hM_def
  have h_M_pos : 0 < M := by
    have h1 : 0 < (S ×ˢ T).card := by omega
    rw [hM_def]; exact_mod_cast h1
  set t : ℝ := M * δ with ht_def
  have h_t_nn : 0 ≤ t := by rw [ht_def]; positivity
  have h_μ_pos : 0 < M * p.toReal := mul_pos h_M_pos hp_pos
  -- Apply cycle 28 with t := M·δ
  have h_conc := crossBlockPairs_graph_concentration_lower p hp S T t h_t_nn h_μ_pos
  -- Rewrite the event: M·p + t = M·p + M·δ = M·(p + δ)
  have h_set_eq :
    {G : SimpleGraph (Fin n_A ⊕ Fin n_B) | ∀ [inst : DecidableRel G.Adj],
      ((@crossBlockPairs n_A n_B G inst S T).card : ℝ) < M * p.toReal + t}
    = {G | ∀ [inst : DecidableRel G.Adj],
      ((@crossBlockPairs n_A n_B G inst S T).card : ℝ) < M * (p.toReal + δ)} := by
    have h_arith : M * p.toReal + t = M * (p.toReal + δ) := by rw [ht_def]; ring
    ext G
    simp only [Set.mem_setOf_eq]
    rw [h_arith]
  rw [h_set_eq] at h_conc
  -- Simplify the exp: -t²/(2(Mp + t/3)) = -c·M
  have h_exp_eq : Real.exp (-t^2 / (2 * (M * p.toReal + t / 3)))
                = Real.exp (-(c * M)) := by
    congr 1
    rw [ht_def, hc_def]
    have hM_ne : M ≠ 0 := ne_of_gt h_M_pos
    have h_denom_ne : (2 : ℝ) * (p.toReal + δ/3) ≠ 0 := by positivity
    field_simp
  rw [h_exp_eq] at h_conc
  -- Apply hN₀ to bound exp by ε
  have h_exp_le_eps : Real.exp (-(c * M)) ≤ ε := by
    have h_cast : (-(c * M) : ℝ) = -(c * (S ×ˢ T).card) := by rw [hM_def]
    rw [h_cast]
    exact hN₀ (S ×ˢ T).card hN₀_le
  linarith

end DaveyThesis2024.SecRandomBipartite

/-! ## Weakened a.a.s. packing bound (no `1/log` FKS improvement)

The atomic axiom `perPair_packing_aas_FKS` (PairPacking.lean) packages
the full FKS Lemma 7.B output: a per-block-pair `PerPairCover` family
whose **total** size is `⌈C · n_A · n_B · p / log(n_A · n_B)⌉`. The
`1 / log(n_A · n_B)` factor is the genuine FKS improvement obtained
by greedy transversal extraction over k-subset slots; formalising it
requires three further probabilistic ingredients (`exists_valid_k_subset_family`,
per-slot concentration, greedy transversal) that have not yet been
assembled end-to-end in Lean.

The **weak** theorem below drops that improvement: it proves the same
existence statement but with size bound `⌈C · n_A · n_B · p⌉` (no
`/log`). This is a Lean-provable corollary of cycle-22 `trivialPerPairCover`
+ cycle-30 `crossBlockPairs_concentration_aas`, requiring no new
probabilistic content beyond per-pair edge-count concentration.

Mathematically the weak bound is just `χ'_s(G) ≤ O(|E(G)|)` (after
applying `chiPrimeS_le_of_perPairCover_family`), which is the
deterministic trivial bound for the strong chromatic index. The
weak bound is **NOT** strong enough to close `secRandomBipartite_aas`
(`χ'_s ≤ Δ_A · Δ_B`), since `|E(G)| = Θ(n_A n_B p)` while
`Δ_A · Δ_B = Θ(n_A n_B p²)`. The headline `secRandomBipartite_aas`
therefore continues to depend on the genuine FKS axiom.

The point of this theorem is twofold:
* it eliminates **all** atomic-axiom content from the weakened headline
  (the new theorem depends only on standard Lean axioms),
* it confirms that the `PerPairCover` API is sufficient to assemble
  packing-style a.a.s. statements end-to-end — the remaining gap to
  the FKS axiom is purely the `/log` improvement. -/

namespace SECRandomBipartite

open DaveyThesis2024.BipartiteRandomGraph
open DaveyThesis2024.SecRandomBipartite

variable {n_A n_B : ℕ}

/-- `block n 1 hs ⟨0, hs⟩ = Finset.univ`: the singleton-block partition has
one block containing everything. -/
private lemma block_one_eq_univ (n : ℕ) (hs : (0 : ℕ) < 1) :
    DaveyThesis2024.SecRandomBipartite.block n 1 hs ⟨0, hs⟩ = (Finset.univ : Finset (Fin n)) := by
  ext i
  simp only [DaveyThesis2024.SecRandomBipartite.mem_block, Finset.mem_univ, iff_true]
  apply Fin.ext
  simp [DaveyThesis2024.SecRandomBipartite.blockOf, Nat.mod_one]

/--
**Weakened a.a.s. packing (no `/log` factor)**: residual probabilistic
content of the bipartite CN nibble *without* the FKS Lemma-7 greedy
transversal step.

**Statement.** For random bipartite `G ~ G(n_A, n_B, p)` at constant
`p ∈ (0, 1)`, for any `ε > 0`, for `min(n_A, n_B)` sufficiently large,
a.a.s.\ a `PerPairCover` family exists across all block-pairs `(A_i, B_j)`
in the (trivial) singleton partition, with the total cover size bounded
by `⌈2 · n_A · n_B · p⌉`.

**Why correct.** Specialise to `s_A := s_B := 1` (trivial partition);
the per-pair cover is `trivialPerPairCover` (cycle 22), of size exactly
`(crossBlockPairs G univ univ).card`. Cycle-30
`crossBlockPairs_concentration_aas` with `δ := p` gives a.a.s.
`(crossBlockPairs G univ univ).card < n_A · n_B · (p + p) = 2 · n_A · n_B · p`.
Since `(crossBlockPairs G univ univ).card` is a `ℕ`, the strict
inequality lifts to `≤ ⌈2 · n_A · n_B · p⌉₊`.

This is a strict weakening of `perPair_packing_aas_FKS` — the FKS axiom
has size bound `⌈C · n_A · n_B · p / log(n_A · n_B)⌉` (with `/log`),
which is strictly smaller asymptotically and is the genuine improvement
delivered by the greedy transversal. The weak version below is
fully proved with no domain axioms; the gap to the FKS axiom is precisely
the `/log` improvement (a non-trivial probabilistic argument). -/
theorem perPair_packing_aas_weak
    (p : ℝ) (hp_lb : (0 : ℝ) < p) (hp_ub : p < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n_A n_B : ℕ,
        min n_A n_B ≥ N →
        probBipartiteRandom n_A n_B p
          (fun G => ∀ [DecidableRel G.Adj], DaveyThesis2024.SecRandomBipartite.IsBipartiteOnSum G →
            ∃ (s_A s_B : ℕ) (hsA : 0 < s_A) (hsB : 0 < s_B) (k_per : ℕ),
              s_A * s_B * k_per ≤
                ⌈C * (n_A : ℝ) * n_B * p⌉₊ ∧
              Nonempty (∀ (i : Fin s_A) (j : Fin s_B),
                DaveyThesis2024.SecRandomBipartite.PerPairCover G
                  (DaveyThesis2024.SecRandomBipartite.block n_A s_A hsA i)
                  (DaveyThesis2024.SecRandomBipartite.block n_B s_B hsB j) k_per))
        ≥ 1 - ε := by
  -- Choose `C := 2`, `δ := p` for the concentration call.
  refine ⟨2, by norm_num, fun ε hε => ?_⟩
  -- ENNReal scaffolding.
  have hp_ofReal : ENNReal.ofReal p ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_ub.le
  have hp_toReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp_lb.le
  have hp_ENN_pos : 0 < (ENNReal.ofReal p).toReal := by rw [hp_toReal]; exact hp_lb
  -- The Chernoff coefficient and uniform threshold N₀ depend only on (p, δ, ε), not n_A/n_B.
  -- Inline cycle-30's threshold computation with δ := p: c := p² / (2(p + p/3)) = 3p/8.
  -- Actual cycle-30 uses c := δ² / (2(p + δ/3)). With δ := p: c := p² / (2 · 4p/3) = 3p/8.
  set c : ℝ := p^2 / (2 * ((ENNReal.ofReal p).toReal + p/3)) with hc_def
  have hp_plus_third_pos : 0 < (ENNReal.ofReal p).toReal + p/3 := by
    rw [hp_toReal]; linarith
  have hc_pos : 0 < c := by rw [hc_def]; positivity
  -- Uniform N₀ from arithmetic threshold.
  obtain ⟨N₀, hN₀_arith⟩ := exists_N_exp_neg_le_eps c ε hc_pos hε
  refine ⟨max N₀ 1, fun n_A n_B hN_ge => ?_⟩
  -- Auxiliary positivity facts.
  have hN₀_le_min : N₀ ≤ min n_A n_B := le_trans (le_max_left _ _) hN_ge
  have hone_le_min : 1 ≤ min n_A n_B := le_trans (le_max_right _ _) hN_ge
  have hnA_pos : 0 < n_A := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1)
    (le_trans hone_le_min (Nat.min_le_left _ _))
  have hnB_pos : 0 < n_B := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1)
    (le_trans hone_le_min (Nat.min_le_right _ _))
  -- (univ ×ˢ univ).card = n_A · n_B.
  set S : Finset (Fin n_A) := Finset.univ
  set T : Finset (Fin n_B) := Finset.univ
  have h_card_ST : (S ×ˢ T).card = n_A * n_B := by
    simp [S, T]
  have h_card_ge_N₀ : N₀ ≤ (S ×ˢ T).card := by
    rw [h_card_ST]
    calc N₀ ≤ min n_A n_B := hN₀_le_min
      _ ≤ n_A := Nat.min_le_left _ _
      _ = n_A * 1 := (Nat.mul_one _).symm
      _ ≤ n_A * n_B := Nat.mul_le_mul_left _ hnB_pos
  -- Inline cycle-30 derivation specialised to S = T = univ, δ = p (uniform in n_A, n_B).
  -- Apply cycle-28 `crossBlockPairs_graph_concentration_lower` with t := M·δ = (n_A·n_B)·p.
  set M : ℝ := ((S ×ˢ T).card : ℝ) with hM_def
  have h_M_pos : 0 < M := by
    have h_card_pos : 0 < (S ×ˢ T).card := by
      rw [h_card_ST]; exact Nat.mul_pos hnA_pos hnB_pos
    rw [hM_def]; exact_mod_cast h_card_pos
  set t : ℝ := M * p with ht_def
  have h_t_nn : 0 ≤ t := by rw [ht_def]; positivity
  have h_μ_pos : 0 < M * (ENNReal.ofReal p).toReal :=
    mul_pos h_M_pos hp_ENN_pos
  have h_chern := DaveyThesis2024.SecRandomBipartite.crossBlockPairs_graph_concentration_lower
    (ENNReal.ofReal p) hp_ofReal S T t h_t_nn h_μ_pos
  -- Rewrite the event to use 2*p: M·p_real + t = M·p + M·p = M·(2p).
  have h_event_eq :
      {G : SimpleGraph (Fin n_A ⊕ Fin n_B) | ∀ [inst : DecidableRel G.Adj],
        ((@crossBlockPairs n_A n_B G inst S T).card : ℝ)
          < M * (ENNReal.ofReal p).toReal + t}
      = {G | ∀ [inst : DecidableRel G.Adj],
        ((@crossBlockPairs n_A n_B G inst S T).card : ℝ)
          < M * (2 * p)} := by
    have h_arith : M * (ENNReal.ofReal p).toReal + t = M * (2 * p) := by
      rw [hp_toReal, ht_def]; ring
    ext G; simp only [Set.mem_setOf_eq, h_arith]
  rw [h_event_eq] at h_chern
  -- Bound the exp factor: -t²/(2(M·p + t/3)) = -c·M.
  have h_exp_eq : Real.exp (-t^2 / (2 * (M * (ENNReal.ofReal p).toReal + t / 3)))
                = Real.exp (-(c * M)) := by
    congr 1
    rw [ht_def, hc_def, hp_toReal]
    have hM_ne : M ≠ 0 := ne_of_gt h_M_pos
    have h_denom_ne : (2 : ℝ) * (p + p/3) ≠ 0 := by positivity
    field_simp
  rw [h_exp_eq] at h_chern
  -- Apply arithmetic threshold: exp(-c·M) ≤ ε using M ≥ N₀.
  have h_M_ge_N₀ : (N₀ : ℝ) ≤ M := by
    rw [hM_def]; exact_mod_cast h_card_ge_N₀
  have h_exp_le_ε : Real.exp (-(c * M)) ≤ ε := by
    -- Need to convert (c * M) to (c * n) form; use M = n_A · n_B as a Nat.
    have h_M_eq_Nat : M = ((n_A * n_B : ℕ) : ℝ) := by
      rw [hM_def, h_card_ST]
    rw [h_M_eq_Nat]
    have h_NAB_ge : N₀ ≤ n_A * n_B := by
      have := h_card_ge_N₀; rw [h_card_ST] at this; exact this
    exact hN₀_arith (n_A * n_B) h_NAB_ge
  have h_conc : (bipartiteRandomMeasure n_A n_B (ENNReal.ofReal p) hp_ofReal).real
        {G : SimpleGraph (Fin n_A ⊕ Fin n_B) | ∀ [inst : DecidableRel G.Adj],
          ((@crossBlockPairs n_A n_B G inst S T).card : ℝ) < M * (2 * p)} ≥ 1 - ε := by
    linarith
  -- The target event implies the concentration event ⟹ measure-mono.
  set Conc : SimpleGraph (Fin n_A ⊕ Fin n_B) → Prop :=
    fun G => ∀ [DecidableRel G.Adj],
      ((@crossBlockPairs n_A n_B G _ S T).card : ℝ)
        < ((S ×ˢ T).card : ℝ) * (2 * p)
  set Pack : SimpleGraph (Fin n_A ⊕ Fin n_B) → Prop :=
    fun G => ∀ [DecidableRel G.Adj], DaveyThesis2024.SecRandomBipartite.IsBipartiteOnSum G →
      ∃ (s_A s_B : ℕ) (hsA : 0 < s_A) (hsB : 0 < s_B) (k_per : ℕ),
        s_A * s_B * k_per ≤
          ⌈2 * (n_A : ℝ) * n_B * p⌉₊ ∧
        Nonempty (∀ (i : Fin s_A) (j : Fin s_B),
          DaveyThesis2024.SecRandomBipartite.PerPairCover G
            (DaveyThesis2024.SecRandomBipartite.block n_A s_A hsA i)
            (DaveyThesis2024.SecRandomBipartite.block n_B s_B hsB j) k_per)
  -- Show: for any G satisfying Conc, the trivial cover witnesses Pack.
  have h_impl : ∀ G : SimpleGraph (Fin n_A ⊕ Fin n_B), Conc G → Pack G := by
    intro G hConc inst _h_bip
    -- Witness: s_A = s_B = 1, k_per = (crossBlockPairs G univ univ).card.
    refine ⟨1, 1, Nat.one_pos, Nat.one_pos, (crossBlockPairs G S T).card, ?_, ?_⟩
    · -- Size bound: 1 * 1 * card = card < 2·n_A·n_B·p, then ⌈⌉ rounds up.
      have h_card_lt : ((crossBlockPairs G S T).card : ℝ)
          < ((S ×ˢ T).card : ℝ) * (2 * p) := hConc
      have h_card_lt' : ((crossBlockPairs G S T).card : ℝ)
          < 2 * (n_A : ℝ) * n_B * p := by
        have h_cast_ST : ((S ×ˢ T).card : ℝ) = (n_A : ℝ) * n_B := by
          rw [h_card_ST]; push_cast; ring
        rw [h_cast_ST] at h_card_lt
        linarith
      have h_ceil_ge : ((crossBlockPairs G S T).card : ℝ)
          ≤ (⌈2 * (n_A : ℝ) * n_B * p⌉₊ : ℝ) := by
        have h_le_ceil : 2 * (n_A : ℝ) * n_B * p ≤ (⌈2 * (n_A : ℝ) * n_B * p⌉₊ : ℝ) :=
          Nat.le_ceil _
        linarith
      have h_nat_le : (crossBlockPairs G S T).card ≤ ⌈2 * (n_A : ℝ) * n_B * p⌉₊ := by
        exact_mod_cast h_ceil_ge
      simpa using h_nat_le
    · -- Provide the trivial per-pair cover at the unique block-pair (0, 0).
      refine ⟨fun i j => ?_⟩
      -- Both i, j : Fin 1 so they're ⟨0, _⟩.
      have hi : i = ⟨0, Nat.one_pos⟩ := Subsingleton.elim _ _
      have hj : j = ⟨0, Nat.one_pos⟩ := Subsingleton.elim _ _
      subst hi; subst hj
      -- block n_A 1 _ ⟨0, _⟩ = univ; similarly for n_B.
      have hS_eq : DaveyThesis2024.SecRandomBipartite.block n_A 1 Nat.one_pos ⟨0, Nat.one_pos⟩
                 = (Finset.univ : Finset (Fin n_A)) := block_one_eq_univ n_A Nat.one_pos
      have hT_eq : DaveyThesis2024.SecRandomBipartite.block n_B 1 Nat.one_pos ⟨0, Nat.one_pos⟩
                 = (Finset.univ : Finset (Fin n_B)) := block_one_eq_univ n_B Nat.one_pos
      rw [hS_eq, hT_eq]
      exact DaveyThesis2024.SecRandomBipartite.trivialPerPairCover G Finset.univ Finset.univ
  -- Use measure monotonicity to lift the concentration probability.
  unfold probBipartiteRandom probBipartiteRandomConcrete
  simp only [hp_ofReal, dite_true]
  have hPack_meas : MeasurableSet {G | Pack G} := MeasurableSet.of_discrete
  have hConc_meas : MeasurableSet {G | Conc G} := MeasurableSet.of_discrete
  -- (bipartiteRandomMeasure ...).toReal of the {G | Pack G} set is ≥ same of Conc.
  have h_mono :
      (bipartiteRandomMeasure n_A n_B (ENNReal.ofReal p) hp_ofReal {G | Conc G}).toReal
      ≤ (bipartiteRandomMeasure n_A n_B (ENNReal.ofReal p) hp_ofReal {G | Pack G}).toReal := by
    apply ENNReal.toReal_mono
    · exact (MeasureTheory.measure_lt_top _ _).ne
    · apply MeasureTheory.measure_mono
      intro G hG; exact h_impl G hG
  -- h_conc is the same statement up to `.real` ↔ `.toReal` and event-set unfolding.
  have h_conc' :
      (bipartiteRandomMeasure n_A n_B (ENNReal.ofReal p) hp_ofReal {G | Conc G}).toReal
        ≥ 1 - ε := by
    have h_eq : {G : SimpleGraph (Fin n_A ⊕ Fin n_B) | Conc G}
              = {G | ∀ [inst : DecidableRel G.Adj],
                  ((@crossBlockPairs n_A n_B G inst S T).card : ℝ)
                    < ((S ×ˢ T).card : ℝ) * (2 * p)} := by
      ext G; rfl
    rw [h_eq]
    exact h_conc
  linarith

end SECRandomBipartite
