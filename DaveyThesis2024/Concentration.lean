import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Concentration inequalities (ported from TwoBites/Concentration.lean)

**Port note (2026-06-01; trimmed 2026-06-19).** This file was ported from
`heftyhornkingpfender2026/TwoBites/Concentration.lean`. The downstream
rare-event corollary (`chernoff_A3_real_ineq`, `chernoff_corollary_A3`) and the
McDiarmid sub-tree (`mcdiarmid_*`) were **removed**: they were unused by any
Davey headline (the SEC random-bipartite result goes through the verbatim
Kim–Vu / Pippenger–Spencer axioms), and their proofs needed Mathlib v4.30 API
absent from Davey's v4.28.0 (e.g. `Real.log_five_gt_d9`), forcing a `sorry` on
`log_five_div_two_ge_nine_tenths`. The complete, sorry-free versions live in
hefty. What remains — the multiplicative-Chernoff core
(`multiplicative_chernoff_indicators` + `_lower`) and the Bennett-form A.2
bounds (`chernoff_A2_upper` + `_lower`), which `SECRandomBipartite` uses for
`Δ_A`/`Δ_B` concentration — builds from standard Lean axioms only.

Used by `DaveyThesis2024.SECRandomBipartite` to derive max-degree
concentration on `Δ_A`, `Δ_B` (eliminating two domain axioms in the
SEC random formalisation, Port-A of `axiom_decomposition_plan.md`).

---

This file builds the Appendix A inequalities from
Hefty–Horn–King–Pfender (arXiv:2510.19718v3), which the §3 lemmas (3.1, 3.3, 3.4)
consume to bound `P(R^c) = o(1)`. The paper's exact statements (pp. 17–18):

* **A.2** (Chernoff/Hoeffding): for `S_n = X_1 + ... + X_n` with `0 ≤ X_i ≤ 1` independent,
  `μ = Σ E[X_i]`, and `t ≥ 0`,
  `P(S_n ≥ μ + t) ≤ exp(-t² / (2(μ + t/3)))`,
  and for `0 ≤ t ≤ μ`, `P(S_n ≤ μ - t) ≤ exp(-t² / (2(μ - t/3)))`.

* **A.3** (corollary): if `t ≥ (3/2)·μ`, then `P(S_n ≥ μ + t) ≤ exp(-t/2)`.

* **A.4** (McDiarmid): for `Z = Z(W_1, ..., W_n)` of independent r.v.s with bounded
  differences `|Z(...W_i...) - Z(...W'_i...)| ≤ c_i`,
  `P(Z ≥ EZ + t) ≤ exp(-t²/(2 Σ c_i²))` (and symmetric lower tail).

## Status

The **canonical multiplicative Chernoff** (form `P[ε ≤ S] ≤ exp(-ε·log(ε/μ) + ε - μ)`)
is fully proven below as `multiplicative_chernoff_indicators`, with the matching lower
tail `multiplicative_chernoff_indicators_lower`. The paper's specific A.2 **upper-tail**
form `exp(-t²/(2(μ + t/3)))` is proven as `chernoff_A2_upper` via the Bennett-style
inequality `bennett_real_ineq` (lower tail: `chernoff_A2_lower`). The rare-event
corollary A.3 and McDiarmid A.4 are **not** included here (removed 2026-06-19 as
unused by any headline; the complete, sorry-free versions live in
`heftyhornkingpfender2026/TwoBites/Concentration.lean`).

## Attribution

The core multiplicative-Chernoff content (lemmas `bernoulli_mgf_le`,
`indicator_exp_pointwise`, `indicator_mgf_eq`, `sum_bernoulli_mgf_le`, and
`multiplicative_chernoff_indicators`) is ported from the sibling Lean project
`hurleydejoannisdevercloskang2022/HJK2022/Scratch/PathE2MultiplicativeChernoff.lean`,
where it was proved independently for a hypergraph-Ramsey nibble argument. The proofs
use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`); namespaces
adapted from `HJK2022.PathE2` to `DaveyThesis2024.Concentration`.
-/

open MeasureTheory ProbabilityTheory Real

namespace DaveyThesis2024.Concentration

/-- **Bernoulli MGF upper bound**: for `X ∼ Bernoulli(p)`,
`mgf X t = (1-p) + p·eᵗ ≤ exp(p·(eᵗ - 1))`.

Proof: for all real `y`, `1 + y ≤ e^y` (Real.add_one_le_exp).
Set `y = p(eᵗ - 1)`: `LHS = 1 + y`, `RHS = exp(y)`. -/
lemma bernoulli_mgf_le (p : ℝ) (_hp : 0 ≤ p) (_hp1 : p ≤ 1) (t : ℝ) :
    (1 - p) + p * Real.exp t ≤ Real.exp (p * (Real.exp t - 1)) := by
  set y : ℝ := p * (Real.exp t - 1) with hy_def
  have h_lhs : (1 - p) + p * Real.exp t = 1 + y := by rw [hy_def]; ring
  rw [h_lhs]
  linarith [Real.add_one_le_exp y]

/-- **Pointwise identity** for the MGF integrand on a `{0,1}`-indicator.
For any `t` and any `X ω ∈ {0, 1}`: `exp(t · X ω) = 1 + X ω · (exp t - 1)`. -/
lemma indicator_exp_pointwise {ι : Type*} {Ω : Type*}
    (X : ι → Ω → ℝ) (h_indicator : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (i : ι) (t : ℝ) (ω : Ω) :
    Real.exp (t * X i ω) = 1 + X i ω * (Real.exp t - 1) := by
  rcases h_indicator i ω with h0 | h1
  · rw [h0, mul_zero, Real.exp_zero]; ring
  · rw [h1, mul_one]; ring

/-- **MGF computation for a single `{0,1}`-indicator**: `mgf X t = (1-p) + p·exp(t)`.

Uses `indicator_exp_pointwise` to rewrite the integrand, then linearity of integral +
`IsProbabilityMeasure` (so `∫1 = 1`) + `h_p_eq : ∫X = p`. -/
lemma indicator_mgf_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*}
    (X : ι → Ω → ℝ)
    (h_meas : ∀ i, Measurable (X i))
    (h_indicator : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ι → ℝ)
    (h_p_eq : ∀ i, ∫ ω, X i ω ∂μ = p i)
    (i : ι) (t : ℝ) :
    mgf (X i) μ t = (1 - p i) + p i * Real.exp t := by
  have h_pt : ∀ ω, Real.exp (t * X i ω) = 1 + X i ω * (Real.exp t - 1) :=
    fun ω => indicator_exp_pointwise X h_indicator i t ω
  have h_X_bound : ∀ ω, ‖X i ω‖ ≤ 1 := fun ω => by
    rcases h_indicator i ω with h | h <;> simp [h]
  have h_X_int : Integrable (X i) μ :=
    MeasureTheory.Integrable.of_bound (h_meas i).aestronglyMeasurable 1
      (ae_of_all _ h_X_bound)
  unfold mgf
  simp only [h_pt]
  rw [integral_add (integrable_const _) (h_X_int.mul_const _)]
  rw [integral_const, integral_mul_const, h_p_eq]
  have h_univ : μ.real Set.univ = 1 := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.measure_univ]; rfl
  rw [h_univ]
  simp only [smul_eq_mul, mul_one]
  ring

/-- **MGF tail bound for sum of independent Bernoullis**.

For `X = Σᵢ X_i` where `X_i` are independent `{0,1}`-indicators with `P[X_i = 1] = p_i`
and `μ = Σ p_i`, `mgf X t ≤ exp(μ·(eᵗ - 1))` for all `t`.

Proof: `iIndepFun.mgf_sum` (mgf is multiplicative for independent variables) + per-vertex
`bernoulli_mgf_le`. -/
lemma sum_bernoulli_mgf_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} (s : Finset ι)
    (X : ι → Ω → ℝ)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_indicator : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ι → ℝ)
    (h_p_bounds : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (h_p_eq : ∀ i, ∫ ω, X i ω ∂μ = p i)
    (t : ℝ) :
    mgf (fun ω => ∑ i ∈ s, X i ω) μ t ≤
      Real.exp ((∑ i ∈ s, p i) * (Real.exp t - 1)) := by
  rw [show (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i from funext fun ω => by simp]
  rw [iIndepFun.mgf_sum h_indep h_meas s]
  have h_each : ∀ i ∈ s, mgf (X i) μ t ≤ Real.exp (p i * (Real.exp t - 1)) := by
    intro i _
    rw [indicator_mgf_eq X h_meas h_indicator p h_p_eq i t]
    exact bernoulli_mgf_le (p i) (h_p_bounds i).1 (h_p_bounds i).2 t
  have h_each_nn : ∀ i ∈ s, 0 ≤ mgf (X i) μ t := fun i _ => mgf_nonneg
  calc ∏ i ∈ s, mgf (X i) μ t
      ≤ ∏ i ∈ s, Real.exp (p i * (Real.exp t - 1)) :=
        Finset.prod_le_prod h_each_nn h_each
    _ = Real.exp (∑ i ∈ s, p i * (Real.exp t - 1)) := by
        rw [← Real.exp_sum]
    _ = Real.exp ((∑ i ∈ s, p i) * (Real.exp t - 1)) := by
        congr 1
        rw [← Finset.sum_mul]

/-- **Multiplicative Chernoff** for sums of independent Bernoulli indicators (canonical form).

For `X = Σᵢ X_i` (independent `{0,1}`-indicators with `P[X_i = 1] = p_i`), `μ = Σ p_i`,
and `ε > μ`:
  `P[ε ≤ X] ≤ exp(-ε·log(ε/μ) + ε - μ)`

This is equivalent to `(eμ/ε)^ε · exp(-μ)`. From this canonical form the paper's
A.2 form `exp(-t²/(2(μ+t/3)))` follows via a real-analytic inequality (bridge lemma TODO).

Proof:
1. Markov on exp: `P[ε ≤ X] ≤ exp(-t·ε) · mgf X t` (mathlib `measure_ge_le_exp_mul_mgf`).
2. `sum_bernoulli_mgf_le`: `mgf X t ≤ exp(μ·(eᵗ - 1))`.
3. Substitute `t = log(ε/μ)`: bound becomes `exp(-ε·log(ε/μ) + ε - μ)`. -/
theorem multiplicative_chernoff_indicators
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} (s : Finset ι)
    (X : ι → Ω → ℝ)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_indicator : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ι → ℝ)
    (h_p_bounds : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (h_p_eq : ∀ i, ∫ ω, X i ω ∂μ = p i)
    (ε : ℝ) (hε_pos : 0 < ε)
    (h_μ_pos : 0 < ∑ i ∈ s, p i)
    (h_μ_lt_ε : (∑ i ∈ s, p i) < ε) :
    μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤
      Real.exp (-ε * Real.log (ε / (∑ i ∈ s, p i)) + ε - (∑ i ∈ s, p i)) := by
  set μ_total : ℝ := ∑ i ∈ s, p i with hμ_total_def
  set t : ℝ := Real.log (ε / μ_total) with ht_def
  have hε_div_pos : 0 < ε / μ_total := div_pos hε_pos h_μ_pos
  have ht_pos : 0 < t := by
    rw [ht_def]; exact Real.log_pos (by rw [lt_div_iff₀ h_μ_pos]; linarith)
  have h_sum_meas : Measurable (fun ω => ∑ i ∈ s, X i ω) :=
    Finset.measurable_sum s (fun i _ => h_meas i)
  have h_int_exp : Integrable (fun ω => Real.exp (t * ∑ i ∈ s, X i ω)) μ := by
    apply MeasureTheory.Integrable.of_bound
      ((measurable_const.mul h_sum_meas).exp.aestronglyMeasurable)
      (Real.exp (t * s.card))
    refine ae_of_all _ fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have h_sum_le : ∑ i ∈ s, X i ω ≤ s.card := by
      calc ∑ i ∈ s, X i ω ≤ ∑ _i ∈ s, (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro i _
              rcases h_indicator i ω with h | h <;> rw [h] <;> norm_num
        _ = s.card := by simp
    exact mul_le_mul_of_nonneg_left h_sum_le ht_pos.le
  have h_chernoff := measure_ge_le_exp_mul_mgf (μ := μ)
    (X := fun ω => ∑ i ∈ s, X i ω) ε ht_pos.le h_int_exp
  have h_mgf_bound : mgf (fun ω => ∑ i ∈ s, X i ω) μ t ≤
      Real.exp (μ_total * (Real.exp t - 1)) :=
    sum_bernoulli_mgf_le s X h_indep h_meas h_indicator p h_p_bounds h_p_eq t
  have h_combined : μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤
      Real.exp (-t * ε) * Real.exp (μ_total * (Real.exp t - 1)) := by
    refine h_chernoff.trans ?_
    apply mul_le_mul_of_nonneg_left h_mgf_bound
    exact (Real.exp_pos _).le
  have h_exp_t : Real.exp t = ε / μ_total := by
    rw [ht_def]; exact Real.exp_log hε_div_pos
  have h_simp : μ_total * (Real.exp t - 1) = ε - μ_total := by
    rw [h_exp_t]
    field_simp
  refine h_combined.trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [h_simp]
  linarith

/-- **Multiplicative Chernoff — lower tail** for sums of independent Bernoulli indicators.

For `X = Σᵢ X_i` (independent `{0,1}`-indicators with `P[X_i = 1] = p_i`), `μ = Σ p_i`,
and `0 < ε < μ`:
  `P[X ≤ ε] ≤ exp(-ε·log(ε/μ) + ε - μ)`

Same canonical form as the upper tail; the exponent is negative in both regimes (it's a
relative-entropy expression). Proof mirrors the upper tail but uses `t = log(ε/μ) < 0`
with mathlib's `measure_le_le_exp_mul_mgf`. -/
theorem multiplicative_chernoff_indicators_lower
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} (s : Finset ι)
    (X : ι → Ω → ℝ)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_indicator : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ι → ℝ)
    (h_p_bounds : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (h_p_eq : ∀ i, ∫ ω, X i ω ∂μ = p i)
    (ε : ℝ) (hε_pos : 0 < ε)
    (h_ε_lt_μ : ε < (∑ i ∈ s, p i)) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ ε} ≤
      Real.exp (-ε * Real.log (ε / (∑ i ∈ s, p i)) + ε - (∑ i ∈ s, p i)) := by
  set μ_total : ℝ := ∑ i ∈ s, p i with hμ_total_def
  set t : ℝ := Real.log (ε / μ_total) with ht_def
  have h_μ_total_pos : 0 < μ_total := lt_trans hε_pos h_ε_lt_μ
  have hε_div_pos : 0 < ε / μ_total := div_pos hε_pos h_μ_total_pos
  have hε_div_lt_one : ε / μ_total < 1 := (div_lt_one h_μ_total_pos).mpr h_ε_lt_μ
  have ht_neg : t < 0 := by
    rw [ht_def]; exact Real.log_neg hε_div_pos hε_div_lt_one
  have h_sum_meas : Measurable (fun ω => ∑ i ∈ s, X i ω) :=
    Finset.measurable_sum s (fun i _ => h_meas i)
  have h_int_exp : Integrable (fun ω => Real.exp (t * ∑ i ∈ s, X i ω)) μ := by
    apply MeasureTheory.Integrable.of_bound
      ((measurable_const.mul h_sum_meas).exp.aestronglyMeasurable)
      (Real.exp 0)
    refine ae_of_all _ fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    -- t < 0 and ΣX_i ≥ 0, so t · ΣX_i ≤ 0
    have h_X_nn : ∀ i ∈ s, 0 ≤ X i ω := by
      intro i _; rcases h_indicator i ω with h | h <;> rw [h] <;> norm_num
    have h_sum_nn : 0 ≤ ∑ i ∈ s, X i ω := Finset.sum_nonneg h_X_nn
    have := mul_nonpos_of_nonpos_of_nonneg ht_neg.le h_sum_nn
    linarith
  have h_chernoff := measure_le_le_exp_mul_mgf (μ := μ)
    (X := fun ω => ∑ i ∈ s, X i ω) ε ht_neg.le h_int_exp
  have h_mgf_bound : mgf (fun ω => ∑ i ∈ s, X i ω) μ t ≤
      Real.exp (μ_total * (Real.exp t - 1)) :=
    sum_bernoulli_mgf_le s X h_indep h_meas h_indicator p h_p_bounds h_p_eq t
  have h_combined : μ.real {ω | ∑ i ∈ s, X i ω ≤ ε} ≤
      Real.exp (-t * ε) * Real.exp (μ_total * (Real.exp t - 1)) := by
    refine h_chernoff.trans ?_
    apply mul_le_mul_of_nonneg_left h_mgf_bound
    exact (Real.exp_pos _).le
  have h_exp_t : Real.exp t = ε / μ_total := by
    rw [ht_def]; exact Real.exp_log hε_div_pos
  have h_simp : μ_total * (Real.exp t - 1) = ε - μ_total := by
    rw [h_exp_t]
    field_simp
  refine h_combined.trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [h_simp]
  linarith

/-! ### Bridge to paper-form A.2 (upper tail)

The canonical multiplicative-Chernoff form `exp(-ε log(ε/μ) + ε - μ)` (with `ε = μ + t`)
becomes the paper's `exp(-t²/(2(μ + t/3)))` via the **Bennett-style** inequality

  `(μ + t) · log(1 + t/μ) - t ≥ t² / (2(μ + t/3))`   for `μ > 0`, `t ≥ 0`.

Substituting `α := t/μ ≥ 0` and dividing by `μ > 0`, this is equivalent to

  `(1 + α) · log(1 + α) - α ≥ 3α² / (6 + 2α)`   for `α ≥ 0`.   (★)

We prove (★) by defining `g(α) := (1+α) log(1+α) - α - 3α²/(6+2α)` and showing
`g(α) ≥ 0` on `[0, ∞)`. Strategy:
* `g(0) = 0`;
* `g'(α) = log(1+α) - 6α(6+α)/(6+2α)²`, with `g'(0) = 0`;
* `g''(α) = 1/(1+α) - 216/(6+2α)³`, and `g''(α) ≥ 0` reduces (via `6+2α = 2(3+α)`) to
  the polynomial inequality `(3+α)³ ≥ 27(1+α)`, i.e. `α²(9+α) ≥ 0`.
* Two applications of `monotoneOn_of_deriv_nonneg`: first to get `g'(α) ≥ g'(0) = 0`,
  then to get `g(α) ≥ g(0) = 0`. -/

/-- Cubic auxiliary inequality used in the second-derivative computation for the
Bennett bound: `(3 + α)³ ≥ 27 (1 + α)` for `α ≥ 0`. Expands to `α²·(9 + α) ≥ 0`. -/
private lemma cube_three_plus_ge {α : ℝ} (hα : 0 ≤ α) :
    27 * (1 + α) ≤ (3 + α) ^ 3 := by
  nlinarith [sq_nonneg α, sq_nonneg (3 + α), mul_nonneg (sq_nonneg α) hα]

/-- **Bennett real inequality** (paper-form A.2 bridge, normalized form).

For all `α ≥ 0`:
  `3 α² / (6 + 2α) ≤ (1 + α) · log(1 + α) - α`.

Proof: define `g(α) := (1+α) log(1+α) - α - 3α²/(6+2α)`; show `g ≥ 0` on `[0, ∞)` via
`MonotoneOn` of `g` (derived from `g'(α) ≥ 0` on the interior, in turn from `g''(α) ≥ 0`
on the interior). All bookkeeping is via `HasDerivAt` to avoid `deriv` rewrites. -/
lemma bennett_real_ineq {α : ℝ} (hα : 0 ≤ α) :
    3 * α ^ 2 / (6 + 2 * α) ≤ (1 + α) * Real.log (1 + α) - α := by
  -- Helper: 1 + x > 0 on Ici 0.
  have h_one_plus_pos : ∀ x ∈ Set.Ici (0 : ℝ), 0 < 1 + x := by
    intro x hx; linarith [Set.mem_Ici.mp hx]
  have h_six_plus_pos : ∀ x ∈ Set.Ici (0 : ℝ), 0 < 6 + 2 * x := by
    intro x hx; linarith [Set.mem_Ici.mp hx]
  -- Define the rational piece b(x) := 3 x² / (6 + 2x).
  set b : ℝ → ℝ := fun x => 3 * x ^ 2 / (6 + 2 * x) with hb_def
  -- Define g(x) := (1+x) log(1+x) - x - b(x).
  set g : ℝ → ℝ := fun x => (1 + x) * Real.log (1 + x) - x - b x with hg_def
  -- Define g'(x) := log(1+x) - 6 x (6 + x) / (6+2x)².
  set g' : ℝ → ℝ := fun x => Real.log (1 + x) - 6 * x * (6 + x) / (6 + 2 * x) ^ 2 with hg'_def
  -- Define g''(x) := 1/(1+x) - 216 / (6+2x)³.
  set g'' : ℝ → ℝ := fun x => (1 + x)⁻¹ - 216 / (6 + 2 * x) ^ 3 with hg''_def
  --
  -- STEP 1: HasDerivAt for b at any x with 6 + 2x ≠ 0.
  --
  have hb_deriv : ∀ x, 0 < 6 + 2 * x →
      HasDerivAt b (6 * x * (6 + x) / (6 + 2 * x) ^ 2) x := by
    intro x hx
    -- numerator: 3 x², derivative 6 x
    have h_num : HasDerivAt (fun y : ℝ => 3 * y ^ 2) (6 * x) x := by
      have h := (hasDerivAt_pow 2 x).const_mul (3 : ℝ)
      -- (hasDerivAt_pow 2 x) gives derivative of y² as 2 · x^(2-1) = 2x; const_mul gives 3 · 2x.
      -- Cast (2 - 1 : ℕ) = 1 and pow_one to clean up.
      convert h using 1
      push_cast
      ring
    -- denominator: 6 + 2y, derivative 2
    have h_den : HasDerivAt (fun y : ℝ => 6 + 2 * y) 2 x := by
      have h1 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
        simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
      simpa using h1.const_add (6 : ℝ)
    have h_den_ne : (6 + 2 * x) ≠ 0 := hx.ne'
    have h_div := h_num.div h_den h_den_ne
    -- Simplify: (6 x · (6+2x) - 3 x² · 2) / (6+2x)² = 6 x (6+x) / (6+2x)²
    convert h_div using 1
    have hsq : (6 + 2 * x) ≠ 0 := h_den_ne
    field_simp
    ring
  --
  -- Define f1(x) := 6 x (6 + x) / (6 + 2x)² so g'(x) = log(1+x) - f1(x).
  -- We need HasDerivAt f1 at each x ≥ 0; its derivative is 216 / (6+2x)³.
  set f1 : ℝ → ℝ := fun x => 6 * x * (6 + x) / (6 + 2 * x) ^ 2 with hf1_def
  have hf1_deriv : ∀ x, 0 < 6 + 2 * x →
      HasDerivAt f1 (216 / (6 + 2 * x) ^ 3) x := by
    intro x hx
    -- numerator: 6 x (6 + x) = 36 x + 6 x². derivative = 36 + 12 x.
    have h_num : HasDerivAt (fun y : ℝ => 6 * y * (6 + y)) (36 + 12 * x) x := by
      have h1 : HasDerivAt (fun y : ℝ => 6 * y) 6 x := by
        simpa using (hasDerivAt_id x).const_mul (6 : ℝ)
      have h2 : HasDerivAt (fun y : ℝ => 6 + y) 1 x := by
        simpa using (hasDerivAt_id x).const_add (6 : ℝ)
      have hmul := h1.mul h2
      -- 6 · (6 + x) + 6 x · 1 = 36 + 6 x + 6 x = 36 + 12 x
      convert hmul using 1
      ring
    -- denominator: (6 + 2 x)². derivative = 2 (6+2x) · 2 = 4 (6+2x).
    have h_den_inner : HasDerivAt (fun y : ℝ => 6 + 2 * y) 2 x := by
      have h1 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
        simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
      simpa using h1.const_add (6 : ℝ)
    have h_den : HasDerivAt (fun y : ℝ => (6 + 2 * y) ^ 2) (2 * (6 + 2 * x) * 2) x := by
      have := h_den_inner.pow 2
      simpa [pow_succ, pow_zero, one_mul] using this
    have h_den_ne : (6 + 2 * x) ^ 2 ≠ 0 := pow_ne_zero _ hx.ne'
    have h_div := h_num.div h_den h_den_ne
    convert h_div using 1
    -- Now check: 216 / (6+2x)³ = ((36+12x)·(6+2x)² - (6 x (6+x))·(2 (6+2x) · 2)) / (6+2x)⁴
    have h_pos : (6 + 2 * x) ≠ 0 := hx.ne'
    have h_pos2 : ((6 + 2 * x) ^ 2) ≠ 0 := pow_ne_zero _ h_pos
    have h_pos3 : ((6 + 2 * x) ^ 3) ≠ 0 := pow_ne_zero _ h_pos
    field_simp
    ring
  --
  -- STEP 3: HasDerivAt for g'(x) = log(1+x) - f1(x), with derivative = 1/(1+x) - 216/(6+2x)³.
  --
  have hg'_HD : ∀ x, 0 < 1 + x → 0 < 6 + 2 * x →
      HasDerivAt g' (g'' x) x := by
    intro x hx hxs
    -- log(1+x) has derivative 1/(1+x)
    have h_arg : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have h_log : HasDerivAt (fun y : ℝ => Real.log (1 + y)) ((1 + x)⁻¹ * 1) x :=
      (Real.hasDerivAt_log hx.ne').comp x h_arg
    have h_log' : HasDerivAt (fun y : ℝ => Real.log (1 + y)) ((1 + x)⁻¹) x := by
      simpa using h_log
    have h_f1 := hf1_deriv x hxs
    have h_sub := h_log'.sub h_f1
    convert h_sub using 1
  --
  -- STEP 4: g''(x) ≥ 0 for x ≥ 0.
  --
  have hg''_nn : ∀ x, 0 ≤ x → 0 ≤ g'' x := by
    intro x hx
    have hx1 : (0 : ℝ) < 1 + x := by linarith
    have hx6 : (0 : ℝ) < 6 + 2 * x := by linarith
    have hx3 : (0 : ℝ) < (6 + 2 * x) ^ 3 := pow_pos hx6 _
    -- Need: 1/(1+x) ≥ 216 / (6+2x)³.
    -- Equivalent to (6+2x)³ ≥ 216·(1+x), since 1+x > 0 and (6+2x)³ > 0.
    have h_cube : 216 * (1 + x) ≤ (6 + 2 * x) ^ 3 := by
      -- (6+2x)³ = 8 (3+x)³ ≥ 8 · 27 (1+x) = 216 (1+x).
      have h_eq : (6 + 2 * x) ^ 3 = 8 * (3 + x) ^ 3 := by ring
      rw [h_eq]
      have := cube_three_plus_ge hx
      nlinarith [this]
    -- Now: 1/(1+x) - 216/(6+2x)³ ≥ 0.
    have h_ne1 : (1 + x) ≠ 0 := hx1.ne'
    have h_ne3 : (6 + 2 * x) ^ 3 ≠ 0 := hx3.ne'
    change 0 ≤ (1 + x)⁻¹ - 216 / (6 + 2 * x) ^ 3
    rw [sub_nonneg, div_le_iff₀ hx3, inv_mul_eq_div, le_div_iff₀ hx1]
    linarith
  --
  -- STEP 5: g'(0) = 0.
  --
  have hg'_zero : g' 0 = 0 := by
    change Real.log (1 + 0) - 6 * 0 * (6 + 0) / (6 + 2 * 0) ^ 2 = 0
    simp [Real.log_one]
  --
  -- STEP 6: Continuity of g' on Ici 0.
  --
  have hg'_cont : ContinuousOn g' (Set.Ici (0 : ℝ)) := by
    refine ContinuousOn.sub ?_ ?_
    · -- log(1+x) is continuous on Ici 0 (since 1+x > 0 there)
      intro x hx
      have hpos : 0 < 1 + x := h_one_plus_pos x hx
      exact ((Real.continuousAt_log hpos.ne').comp
        (continuous_const.add continuous_id).continuousAt).continuousWithinAt
    · -- 6 x (6+x) / (6+2x)² is continuous on Ici 0
      intro x hx
      have hpos : 0 < 6 + 2 * x := h_six_plus_pos x hx
      have hne : (6 + 2 * x) ^ 2 ≠ 0 := pow_ne_zero _ hpos.ne'
      have h_num_cont : ContinuousAt (fun y : ℝ => 6 * y * (6 + y)) x :=
        ((continuous_const.mul continuous_id).mul
          (continuous_const.add continuous_id)).continuousAt
      have h_den_cont : ContinuousAt (fun y : ℝ => (6 + 2 * y) ^ 2) x :=
        ((continuous_const.add (continuous_const.mul continuous_id)).pow 2).continuousAt
      exact (h_num_cont.div h_den_cont hne).continuousWithinAt
  --
  -- STEP 7: g' is differentiable on the interior of Ici 0, with derivative g''.
  --
  have hg'_diff : DifferentiableOn ℝ g' (interior (Set.Ici (0 : ℝ))) := by
    intro x hx
    rw [interior_Ici] at hx
    have hxlb : (0 : ℝ) < x := hx
    have hx1 : (0 : ℝ) < 1 + x := by linarith
    have hxs : (0 : ℝ) < 6 + 2 * x := by linarith
    exact (hg'_HD x hx1 hxs).differentiableAt.differentiableWithinAt
  -- deriv g' x = g'' x on the interior.
  have hg'_deriv_eq : ∀ x ∈ interior (Set.Ici (0 : ℝ)), deriv g' x = g'' x := by
    intro x hx
    rw [interior_Ici] at hx
    have hxlb : (0 : ℝ) < x := hx
    have hx1 : (0 : ℝ) < 1 + x := by linarith
    have hxs : (0 : ℝ) < 6 + 2 * x := by linarith
    exact (hg'_HD x hx1 hxs).deriv
  --
  -- STEP 8: g' is MonotoneOn Ici 0, hence g'(α) ≥ g'(0) = 0.
  --
  have hg'_mono : MonotoneOn g' (Set.Ici (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _) hg'_cont hg'_diff ?_
    intro x hx
    rw [hg'_deriv_eq x hx]
    rw [interior_Ici] at hx
    exact hg''_nn x hx.le
  have hg'_nn : ∀ α, 0 ≤ α → 0 ≤ g' α := by
    intro α hα
    have h0_mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl
    have hα_mem : α ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hα
    have := hg'_mono h0_mem hα_mem hα
    rw [hg'_zero] at this
    exact this
  --
  -- STEP 9: HasDerivAt for g at each x with 0 < 1 + x and 0 < 6+2x.
  --
  have hg_HD : ∀ x, 0 < 1 + x → 0 < 6 + 2 * x →
      HasDerivAt g (g' x) x := by
    intro x hx hxs
    -- (1+x) log(1+x): derivative = 1 · log(1+x) + (1+x) · 1/(1+x) = log(1+x) + 1
    have h_arg : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have h_log : HasDerivAt (fun y : ℝ => Real.log (1 + y)) ((1 + x)⁻¹) x := by
      have := (Real.hasDerivAt_log hx.ne').comp x h_arg
      simpa using this
    have h_prod : HasDerivAt (fun y : ℝ => (1 + y) * Real.log (1 + y))
        (1 * Real.log (1 + x) + (1 + x) * ((1 + x)⁻¹)) x := h_arg.mul h_log
    have h_prod' : HasDerivAt (fun y : ℝ => (1 + y) * Real.log (1 + y))
        (Real.log (1 + x) + 1) x := by
      have hne : (1 + x) ≠ 0 := hx.ne'
      convert h_prod using 1
      field_simp
    have h_id : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
    have h_diff := h_prod'.sub h_id
    have h_b := hb_deriv x hxs
    have h_sub := h_diff.sub h_b
    convert h_sub using 1
    -- g' x = log(1+x) - 6 x (6+x) / (6+2x)² and we need:
    --   (log(1+x) + 1) - 1 - 6 x (6+x)/(6+2x)² = log(1+x) - 6 x (6+x)/(6+2x)²
    change Real.log (1 + x) - 6 * x * (6 + x) / (6 + 2 * x) ^ 2
      = Real.log (1 + x) + 1 - 1 - 6 * x * (6 + x) / (6 + 2 * x) ^ 2
    ring
  --
  -- STEP 10: Continuity of g on Ici 0.
  --
  have hg_cont : ContinuousOn g (Set.Ici (0 : ℝ)) := by
    refine ContinuousOn.sub (ContinuousOn.sub ?_ continuousOn_id) ?_
    · -- (1+x) log(1+x) continuous on Ici 0
      intro x hx
      have hpos : 0 < 1 + x := h_one_plus_pos x hx
      have h1 : ContinuousAt (fun y : ℝ => 1 + y) x :=
        (continuous_const.add continuous_id).continuousAt
      have h2 : ContinuousAt (fun y : ℝ => Real.log (1 + y)) x :=
        (Real.continuousAt_log hpos.ne').comp (continuous_const.add continuous_id).continuousAt
      exact (h1.mul h2).continuousWithinAt
    · -- b(x) = 3 x² / (6+2x) continuous on Ici 0
      intro x hx
      have hpos : 0 < 6 + 2 * x := h_six_plus_pos x hx
      have h_num_cont : ContinuousAt (fun y : ℝ => 3 * y ^ 2) x :=
        (continuous_const.mul (continuous_pow 2)).continuousAt
      have h_den_cont : ContinuousAt (fun y : ℝ => 6 + 2 * y) x :=
        (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
      exact (h_num_cont.div h_den_cont hpos.ne').continuousWithinAt
  --
  -- STEP 11: g is differentiable on the interior of Ici 0, with derivative g'.
  --
  have hg_diff : DifferentiableOn ℝ g (interior (Set.Ici (0 : ℝ))) := by
    intro x hx
    rw [interior_Ici] at hx
    have hxlb : (0 : ℝ) < x := hx
    have hx1 : (0 : ℝ) < 1 + x := by linarith
    have hxs : (0 : ℝ) < 6 + 2 * x := by linarith
    exact (hg_HD x hx1 hxs).differentiableAt.differentiableWithinAt
  have hg_deriv_eq : ∀ x ∈ interior (Set.Ici (0 : ℝ)), deriv g x = g' x := by
    intro x hx
    rw [interior_Ici] at hx
    have hxlb : (0 : ℝ) < x := hx
    have hx1 : (0 : ℝ) < 1 + x := by linarith
    have hxs : (0 : ℝ) < 6 + 2 * x := by linarith
    exact (hg_HD x hx1 hxs).deriv
  --
  -- STEP 12: g is MonotoneOn Ici 0; g(0) = 0, so g(α) ≥ 0.
  --
  have hg_mono : MonotoneOn g (Set.Ici (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _) hg_cont hg_diff ?_
    intro x hx
    rw [hg_deriv_eq x hx]
    rw [interior_Ici] at hx
    exact hg'_nn x hx.le
  have hg_zero : g 0 = 0 := by
    change (1 + 0) * Real.log (1 + 0) - 0 - 3 * (0:ℝ) ^ 2 / (6 + 2 * 0) = 0
    simp [Real.log_one]
  have h0_mem : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl
  have hα_mem : α ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hα
  have hg_at := hg_mono h0_mem hα_mem hα
  rw [hg_zero] at hg_at
  -- hg_at : 0 ≤ g α = (1+α) log(1+α) - α - 3 α² / (6+2α)
  have h_unfold : 0 ≤ (1 + α) * Real.log (1 + α) - α - 3 * α ^ 2 / (6 + 2 * α) := hg_at
  linarith

/-- **Theorem A.2** (upper tail, paper form). For independent `{0,1}`-indicators `X_i` with
`μ = Σ p_i > 0` and `t ≥ 0`:
  `P[Σ X_i ≥ μ + t] ≤ exp(-t² / (2·(μ + t/3)))`. -/
theorem chernoff_A2_upper
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} (s : Finset ι)
    (X : ι → Ω → ℝ)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_indicator : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ι → ℝ)
    (h_p_bounds : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (h_p_eq : ∀ i, ∫ ω, X i ω ∂μ = p i)
    (t : ℝ) (ht : 0 ≤ t)
    (h_μ_pos : 0 < ∑ i ∈ s, p i) :
    μ.real {ω | (∑ i ∈ s, p i) + t ≤ ∑ i ∈ s, X i ω} ≤
      Real.exp (- t^2 / (2 * ((∑ i ∈ s, p i) + t / 3))) := by
  set μ₀ : ℝ := ∑ i ∈ s, p i with hμ₀_def
  -- Edge case: t = 0. Then the exponent is 0 and the RHS = 1, so the bound is trivial.
  rcases eq_or_lt_of_le ht with ht_eq | ht_pos
  · -- t = 0: RHS = exp 0 = 1 ≥ probability.
    rw [← ht_eq]
    simp only [pow_two, mul_zero, neg_zero, zero_div, Real.exp_zero]
    exact measureReal_le_one
  -- Now 0 < t. Apply multiplicative_chernoff_indicators with ε := μ₀ + t.
  have hε_pos : 0 < μ₀ + t := by linarith
  have hμ_lt_ε : μ₀ < μ₀ + t := by linarith
  have h_cher := multiplicative_chernoff_indicators (μ := μ) s X
    h_indep h_meas h_indicator p h_p_bounds h_p_eq (μ₀ + t) hε_pos h_μ_pos hμ_lt_ε
  refine h_cher.trans ?_
  apply Real.exp_le_exp.mpr
  -- Goal: -(μ₀+t)·log((μ₀+t)/μ₀) + (μ₀+t) - μ₀ ≤ -t² / (2·(μ₀ + t/3))
  -- i.e., (μ₀+t)·log((μ₀+t)/μ₀) - t ≥ t² / (2·(μ₀ + t/3)).
  -- Set α := t/μ₀ ≥ 0. Then (μ₀+t)/μ₀ = 1 + α, μ₀+t = μ₀(1+α), t = μ₀·α.
  -- The inequality becomes μ₀ · [(1+α)·log(1+α) - α] ≥ μ₀² α² / (2 μ₀ · (1 + α/3))
  --                                              = μ₀ · α² / (2(1 + α/3)) = μ₀ · 3α² / (6 + 2α).
  -- Dividing by μ₀ > 0: (1+α)·log(1+α) - α ≥ 3α²/(6+2α), which is bennett_real_ineq.
  set α : ℝ := t / μ₀ with hα_def
  have hα_nn : (0 : ℝ) ≤ α := by
    rw [hα_def]; exact div_nonneg ht h_μ_pos.le
  have hα_pos : 0 < α := by rw [hα_def]; exact div_pos ht_pos h_μ_pos
  have h_ratio_eq : (μ₀ + t) / μ₀ = 1 + α := by
    rw [hα_def]; field_simp
  have h_t_eq : t = μ₀ * α := by
    rw [hα_def]; field_simp
  have h_one_plus_α_pos : 0 < 1 + α := by linarith
  -- The Bennett inequality:
  have h_bennett : 3 * α ^ 2 / (6 + 2 * α) ≤ (1 + α) * Real.log (1 + α) - α :=
    bennett_real_ineq hα_nn
  -- Now rewrite the LHS and RHS of the goal.
  rw [h_ratio_eq]
  -- Goal: -(μ₀+t) * log(1+α) + (μ₀+t) - μ₀ ≤ -t^2/(2·(μ₀ + t/3))
  -- Replace μ₀ + t = μ₀ * (1+α), t = μ₀ * α.
  have h_sum_eq : μ₀ + t = μ₀ * (1 + α) := by rw [h_t_eq]; ring
  rw [h_sum_eq, h_t_eq]
  -- Goal: -(μ₀ * (1+α)) * log(1+α) + μ₀ * (1+α) - μ₀ ≤ -(μ₀ * α)^2 / (2·(μ₀ + (μ₀ * α)/3))
  -- Simplify RHS denominator: μ₀ + μ₀ α / 3 = μ₀ · (1 + α/3) = μ₀ · (3 + α)/3 = μ₀ (6 + 2α)/6.
  --   So 2·(μ₀ + μ₀ α/3) = μ₀ (6 + 2α)/3.
  --   RHS = -(μ₀ α)² · 3 / (μ₀·(6+2α)) = -3 μ₀² α² / (μ₀ (6+2α)) = -3 μ₀ α² / (6+2α).
  --   So RHS = -μ₀ · 3 α² / (6 + 2α).
  -- LHS = -μ₀ (1+α) log(1+α) + μ₀ (1+α) - μ₀
  --     = -μ₀ (1+α) log(1+α) + μ₀ α
  --     = -μ₀ · [(1+α) log(1+α) - α].
  -- Inequality becomes: -μ₀ · [(1+α) log(1+α) - α] ≤ -μ₀ · 3 α²/(6+2α)
  --                     ⇔ μ₀ · 3 α²/(6+2α) ≤ μ₀ · [(1+α) log(1+α) - α]
  --                     ⇐ 3 α²/(6+2α) ≤ (1+α) log(1+α) - α (and μ₀ ≥ 0).
  have h_six_plus_pos : (0 : ℝ) < 6 + 2 * α := by linarith
  have h_six_plus_ne : (6 + 2 * α : ℝ) ≠ 0 := h_six_plus_pos.ne'
  -- Multiply Bennett by μ₀ > 0:  μ₀ · 3α²/(6+2α) ≤ μ₀ · [(1+α)·log(1+α) - α].
  have h_mul : μ₀ * (3 * α ^ 2 / (6 + 2 * α)) ≤ μ₀ * ((1 + α) * Real.log (1 + α) - α) :=
    mul_le_mul_of_nonneg_left h_bennett h_μ_pos.le
  -- Useful positivity facts:
  have h_one_plus_third_pos : (0 : ℝ) < 1 + α / 3 := by linarith
  have h_denom_inner_pos : 0 < μ₀ + μ₀ * α / 3 := by
    have : 0 ≤ μ₀ * α / 3 := by positivity
    linarith
  have h_denom_pos : 0 < 2 * (μ₀ + μ₀ * α / 3) := by linarith
  have h_denom_ne : 2 * (μ₀ + μ₀ * α / 3) ≠ 0 := h_denom_pos.ne'
  -- Algebraic identity: -(μ₀ α)² / (2 (μ₀ + μ₀ α / 3)) = -(μ₀ · 3 α² / (6 + 2α)).
  -- Convert both sides to a single fraction with denominator (6+2α)·(μ_term), then ring.
  have h_rhs_eq : -(μ₀ * α) ^ 2 / (2 * (μ₀ + μ₀ * α / 3))
        = -(μ₀ * (3 * α ^ 2 / (6 + 2 * α))) := by
    field_simp
    ring
  rw [h_rhs_eq]
  -- Goal: -(μ₀ * (1+α)) * log(1+α) + μ₀ * (1+α) - μ₀ ≤ -(μ₀ * (3 * α^2 / (6 + 2α)))
  -- Equivalently: μ₀ · 3 α²/(6+2α) ≤ μ₀ · (1+α) · log(1+α) - μ₀ · α
  --             = μ₀ · ((1+α) · log(1+α) - α).
  -- LHS of goal equals -(μ₀ · ((1+α) · log(1+α) - α)). Verify:
  --   -(μ₀(1+α)) log(1+α) + μ₀(1+α) - μ₀
  -- = -μ₀(1+α) log(1+α) + μ₀ + μ₀ α - μ₀
  -- = -μ₀(1+α) log(1+α) + μ₀ α
  -- = -(μ₀(1+α) log(1+α) - μ₀ α)
  -- = -μ₀ · ((1+α) log(1+α) - α).
  nlinarith [h_mul, h_μ_pos]

/-! ### Bridge to paper-form A.2 (lower tail)

Mirror of the upper-tail bridge. The canonical multiplicative-Chernoff lower-tail form
(with `ε = μ - t`, `0 < t < μ`) becomes the paper's `exp(-t²/(2(μ - t/3)))` via the
**Bennett-style** inequality

  `(μ - t) · log(1 - t/μ) + t ≤ - t² / (2(μ - t/3))`   for `μ > 0`, `0 ≤ t < μ`.

Substituting `α := t/μ ∈ [0, 1)` and dividing by `μ > 0`, this is equivalent to

  `(1 - α) · log(1 - α) + α ≥ 3α² / (6 - 2α)`   for `α ∈ [0, 1)`.   (★_L)

We prove (★_L) by defining `g(α) := (1-α) log(1-α) + α - 3α²/(6-2α)` and showing
`g(α) ≥ 0` on `[0, 1)`. Strategy mirrors the upper tail:
* `g(0) = 0`;
* `g'(α) = -log(1-α) - 6α(6-α)/(6-2α)²`, with `g'(0) = 0`;
* `g''(α) = 1/(1-α) - 216/(6-2α)³`, and `g''(α) ≥ 0` reduces (via `6-2α = 2(3-α)`) to
  the polynomial inequality `(3-α)³ ≥ 27(1-α)`, i.e. `α²(9-α) ≥ 0`. -/

/-- Cubic auxiliary inequality used in the second-derivative computation for the
lower-tail Bennett bound: `(3 - α)³ ≥ 27 (1 - α)` for `α ∈ [0, 1)` (in fact for
`α ∈ [0, 9]`). Expands to `α²·(9 - α) ≥ 0`. -/
private lemma cube_three_minus_ge {α : ℝ} (hα_lt : α < 1) :
    27 * (1 - α) ≤ (3 - α) ^ 3 := by
  nlinarith [sq_nonneg α, sq_nonneg (3 - α), hα_lt]

/-- **Bennett real inequality** (paper-form A.2 lower-tail bridge, normalized form).

For all `α ∈ [0, 1)`:
  `3 α² / (6 - 2α) ≤ (1 - α) · log(1 - α) + α`.

Proof: mirror of `bennett_real_ineq` — define `g(α) := (1-α) log(1-α) + α - 3α²/(6-2α)`;
show `g ≥ 0` on `[0, 1)` via `MonotoneOn` of `g` (derived from `g'(α) ≥ 0` on the
interior, in turn from `g''(α) ≥ 0` on the interior). -/
lemma bennett_real_ineq_lower {α : ℝ} (hα_nn : 0 ≤ α) (hα_lt : α < 1) :
    3 * α ^ 2 / (6 - 2 * α) ≤ (1 - α) * Real.log (1 - α) + α := by
  -- Helper: 1 - x > 0 on Ico 0 1.
  have h_one_minus_pos : ∀ x ∈ Set.Ico (0 : ℝ) 1, 0 < 1 - x := by
    intro x hx; have hx1 : x < 1 := hx.2; linarith
  have h_six_minus_pos : ∀ x ∈ Set.Ico (0 : ℝ) 1, 0 < 6 - 2 * x := by
    intro x hx; have hx1 : x < 1 := hx.2; linarith
  -- Define the rational piece b(x) := 3 x² / (6 - 2x).
  set b : ℝ → ℝ := fun x => 3 * x ^ 2 / (6 - 2 * x) with hb_def
  -- Define g(x) := (1-x) log(1-x) + x - b(x).
  set g : ℝ → ℝ := fun x => (1 - x) * Real.log (1 - x) + x - b x with hg_def
  -- Define g'(x) := -log(1-x) - 6 x (6 - x) / (6-2x)².
  set g' : ℝ → ℝ := fun x => -Real.log (1 - x) - 6 * x * (6 - x) / (6 - 2 * x) ^ 2 with hg'_def
  -- Define g''(x) := 1/(1-x) - 216 / (6-2x)³.
  set g'' : ℝ → ℝ := fun x => (1 - x)⁻¹ - 216 / (6 - 2 * x) ^ 3 with hg''_def
  --
  -- STEP 1: HasDerivAt for b at any x with 6 - 2x ≠ 0.
  --
  have hb_deriv : ∀ x, 0 < 6 - 2 * x →
      HasDerivAt b (6 * x * (6 - x) / (6 - 2 * x) ^ 2) x := by
    intro x hx
    -- numerator: 3 x², derivative 6 x
    have h_num : HasDerivAt (fun y : ℝ => 3 * y ^ 2) (6 * x) x := by
      have h := (hasDerivAt_pow 2 x).const_mul (3 : ℝ)
      convert h using 1
      push_cast
      ring
    -- denominator: 6 - 2y, derivative -2
    have h_den : HasDerivAt (fun y : ℝ => 6 - 2 * y) (-2) x := by
      have h1 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
        simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
      have h2 : HasDerivAt (fun y : ℝ => 6 - 2 * y) (0 - 2) x := by
        simpa using (hasDerivAt_const x (6:ℝ)).sub h1
      simpa using h2
    have h_den_ne : (6 - 2 * x) ≠ 0 := hx.ne'
    have h_div := h_num.div h_den h_den_ne
    convert h_div using 1
    -- (6 x · (6-2x) - 3 x² · (-2)) / (6-2x)² = (6x(6-2x) + 6x²)/(6-2x)² = 6x(6-x)/(6-2x)²
    have hsq : (6 - 2 * x) ≠ 0 := h_den_ne
    field_simp
    ring
  --
  -- STEP 2: HasDerivAt for f1(x) := 6 x (6 - x) / (6 - 2x)², derivative 216/(6-2x)³.
  --
  set f1 : ℝ → ℝ := fun x => 6 * x * (6 - x) / (6 - 2 * x) ^ 2 with hf1_def
  have hf1_deriv : ∀ x, 0 < 6 - 2 * x →
      HasDerivAt f1 (216 / (6 - 2 * x) ^ 3) x := by
    intro x hx
    -- numerator: 6 x (6 - x) = 36 x - 6 x². derivative = 36 - 12 x.
    have h_num : HasDerivAt (fun y : ℝ => 6 * y * (6 - y)) (36 - 12 * x) x := by
      have h1 : HasDerivAt (fun y : ℝ => 6 * y) 6 x := by
        simpa using (hasDerivAt_id x).const_mul (6 : ℝ)
      have h2 : HasDerivAt (fun y : ℝ => 6 - y) (-1) x := by
        have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
        have := (hasDerivAt_const x (6:ℝ)).sub hid
        simpa using this
      have hmul := h1.mul h2
      -- 6 · (6 - x) + 6 x · (-1) = 36 - 6 x - 6 x = 36 - 12 x
      convert hmul using 1
      ring
    -- denominator: (6 - 2 x)². derivative = 2 (6-2x) · (-2) = -4 (6-2x).
    have h_den_inner : HasDerivAt (fun y : ℝ => 6 - 2 * y) (-2) x := by
      have h1 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
        simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
      have h2 : HasDerivAt (fun y : ℝ => 6 - 2 * y) (0 - 2) x := by
        simpa using (hasDerivAt_const x (6:ℝ)).sub h1
      simpa using h2
    have h_den : HasDerivAt (fun y : ℝ => (6 - 2 * y) ^ 2) (2 * (6 - 2 * x) * (-2)) x := by
      have := h_den_inner.pow 2
      simpa [pow_succ, pow_zero, one_mul] using this
    have h_den_ne : (6 - 2 * x) ^ 2 ≠ 0 := pow_ne_zero _ hx.ne'
    have h_div := h_num.div h_den h_den_ne
    convert h_div using 1
    have h_pos : (6 - 2 * x) ≠ 0 := hx.ne'
    have h_pos2 : ((6 - 2 * x) ^ 2) ≠ 0 := pow_ne_zero _ h_pos
    have h_pos3 : ((6 - 2 * x) ^ 3) ≠ 0 := pow_ne_zero _ h_pos
    field_simp
    ring
  --
  -- STEP 3: HasDerivAt for g'(x) = -log(1-x) - f1(x), derivative = 1/(1-x) - 216/(6-2x)³.
  --
  have hg'_HD : ∀ x, 0 < 1 - x → 0 < 6 - 2 * x →
      HasDerivAt g' (g'' x) x := by
    intro x hx hxs
    -- log(1 - x) has derivative (1-x)⁻¹ · (-1) = -1/(1-x).
    have h_arg : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
      have := (hasDerivAt_const x (1:ℝ)).sub hid
      simpa using this
    have h_log : HasDerivAt (fun y : ℝ => Real.log (1 - y)) ((1 - x)⁻¹ * (-1)) x :=
      (Real.hasDerivAt_log hx.ne').comp x h_arg
    -- -log(1 - x): derivative = -((1-x)⁻¹ * (-1)) = (1-x)⁻¹.
    have h_neg_log : HasDerivAt (fun y : ℝ => -Real.log (1 - y)) ((1 - x)⁻¹) x := by
      have := h_log.neg
      convert this using 1
      ring
    have h_f1 := hf1_deriv x hxs
    have h_sub := h_neg_log.sub h_f1
    convert h_sub using 1
  --
  -- STEP 4: g''(x) ≥ 0 for x ∈ [0, 1).
  --
  have hg''_nn : ∀ x, 0 ≤ x → x < 1 → 0 ≤ g'' x := by
    intro x hx_nn hx_lt
    have hx1 : (0 : ℝ) < 1 - x := by linarith
    have hx6 : (0 : ℝ) < 6 - 2 * x := by linarith
    have hx3 : (0 : ℝ) < (6 - 2 * x) ^ 3 := pow_pos hx6 _
    -- Need: 1/(1-x) ≥ 216 / (6-2x)³.
    -- Equivalent to (6-2x)³ ≥ 216·(1-x).
    have h_cube : 216 * (1 - x) ≤ (6 - 2 * x) ^ 3 := by
      -- (6-2x)³ = 8 (3-x)³ ≥ 8 · 27 (1-x) = 216 (1-x).
      have h_eq : (6 - 2 * x) ^ 3 = 8 * (3 - x) ^ 3 := by ring
      rw [h_eq]
      have := cube_three_minus_ge hx_lt
      nlinarith [this]
    have h_ne1 : (1 - x) ≠ 0 := hx1.ne'
    have h_ne3 : (6 - 2 * x) ^ 3 ≠ 0 := hx3.ne'
    change 0 ≤ (1 - x)⁻¹ - 216 / (6 - 2 * x) ^ 3
    rw [sub_nonneg, div_le_iff₀ hx3, inv_mul_eq_div, le_div_iff₀ hx1]
    linarith
  --
  -- STEP 5: g'(0) = 0.
  --
  have hg'_zero : g' 0 = 0 := by
    change -Real.log (1 - 0) - 6 * 0 * (6 - 0) / (6 - 2 * 0) ^ 2 = 0
    simp [Real.log_one]
  --
  -- STEP 6: Continuity of g' on Ico 0 1.
  --
  have hg'_cont : ContinuousOn g' (Set.Ico (0 : ℝ) 1) := by
    refine ContinuousOn.sub ?_ ?_
    · -- -log(1-x) continuous on Ico 0 1
      intro x hx
      have hpos : 0 < 1 - x := h_one_minus_pos x hx
      exact (((Real.continuousAt_log hpos.ne').comp
        (continuous_const.sub continuous_id).continuousAt).neg).continuousWithinAt
    · -- 6 x (6-x) / (6-2x)² continuous on Ico 0 1
      intro x hx
      have hpos : 0 < 6 - 2 * x := h_six_minus_pos x hx
      have hne : (6 - 2 * x) ^ 2 ≠ 0 := pow_ne_zero _ hpos.ne'
      have h_num_cont : ContinuousAt (fun y : ℝ => 6 * y * (6 - y)) x :=
        ((continuous_const.mul continuous_id).mul
          (continuous_const.sub continuous_id)).continuousAt
      have h_den_cont : ContinuousAt (fun y : ℝ => (6 - 2 * y) ^ 2) x :=
        ((continuous_const.sub (continuous_const.mul continuous_id)).pow 2).continuousAt
      exact (h_num_cont.div h_den_cont hne).continuousWithinAt
  --
  -- STEP 7: g' is differentiable on the interior of Ico 0 1 = Ioo 0 1, with derivative g''.
  --
  have hg'_diff : DifferentiableOn ℝ g' (interior (Set.Ico (0 : ℝ) 1)) := by
    intro x hx
    rw [interior_Ico] at hx
    have hxlb : (0 : ℝ) < x := hx.1
    have hxub : x < 1 := hx.2
    have hx1 : (0 : ℝ) < 1 - x := by linarith
    have hxs : (0 : ℝ) < 6 - 2 * x := by linarith
    exact (hg'_HD x hx1 hxs).differentiableAt.differentiableWithinAt
  have hg'_deriv_eq : ∀ x ∈ interior (Set.Ico (0 : ℝ) 1), deriv g' x = g'' x := by
    intro x hx
    rw [interior_Ico] at hx
    have hxlb : (0 : ℝ) < x := hx.1
    have hxub : x < 1 := hx.2
    have hx1 : (0 : ℝ) < 1 - x := by linarith
    have hxs : (0 : ℝ) < 6 - 2 * x := by linarith
    exact (hg'_HD x hx1 hxs).deriv
  --
  -- STEP 8: g' is MonotoneOn Ico 0 1, hence g'(α) ≥ g'(0) = 0.
  --
  have hg'_mono : MonotoneOn g' (Set.Ico (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico _ _) hg'_cont hg'_diff ?_
    intro x hx
    rw [hg'_deriv_eq x hx]
    rw [interior_Ico] at hx
    exact hg''_nn x hx.1.le hx.2
  have hg'_nn : ∀ α, 0 ≤ α → α < 1 → 0 ≤ g' α := by
    intro α hα_nn hα_lt
    have h0_mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
    have hα_mem : α ∈ Set.Ico (0 : ℝ) 1 := ⟨hα_nn, hα_lt⟩
    have := hg'_mono h0_mem hα_mem hα_nn
    rw [hg'_zero] at this
    exact this
  --
  -- STEP 9: HasDerivAt for g at each x with 0 < 1 - x and 0 < 6-2x.
  --
  have hg_HD : ∀ x, 0 < 1 - x → 0 < 6 - 2 * x →
      HasDerivAt g (g' x) x := by
    intro x hx hxs
    -- (1-x) log(1-x): derivative = (-1) · log(1-x) + (1-x) · (-1/(1-x)) = -log(1-x) - 1
    have h_arg : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
      have := (hasDerivAt_const x (1:ℝ)).sub hid
      simpa using this
    have h_log : HasDerivAt (fun y : ℝ => Real.log (1 - y)) ((1 - x)⁻¹ * (-1)) x :=
      (Real.hasDerivAt_log hx.ne').comp x h_arg
    have h_prod : HasDerivAt (fun y : ℝ => (1 - y) * Real.log (1 - y))
        ((-1) * Real.log (1 - x) + (1 - x) * ((1 - x)⁻¹ * (-1))) x := h_arg.mul h_log
    have h_prod' : HasDerivAt (fun y : ℝ => (1 - y) * Real.log (1 - y))
        (-Real.log (1 - x) - 1) x := by
      have hne : (1 - x) ≠ 0 := hx.ne'
      convert h_prod using 1
      field_simp
      ring
    have h_id : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
    have h_add := h_prod'.add h_id
    have h_b := hb_deriv x hxs
    have h_sub := h_add.sub h_b
    convert h_sub using 1
    -- g' x = -log(1-x) - 6 x (6-x) / (6-2x)²; we need:
    --   (-log(1-x) - 1) + 1 - 6 x (6-x)/(6-2x)² = -log(1-x) - 6 x (6-x)/(6-2x)²
    change -Real.log (1 - x) - 6 * x * (6 - x) / (6 - 2 * x) ^ 2
      = -Real.log (1 - x) - 1 + 1 - 6 * x * (6 - x) / (6 - 2 * x) ^ 2
    ring
  --
  -- STEP 10: Continuity of g on Ico 0 1.
  --
  have hg_cont : ContinuousOn g (Set.Ico (0 : ℝ) 1) := by
    refine ContinuousOn.sub (ContinuousOn.add ?_ continuousOn_id) ?_
    · -- (1-x) log(1-x) continuous on Ico 0 1
      intro x hx
      have hpos : 0 < 1 - x := h_one_minus_pos x hx
      have h1 : ContinuousAt (fun y : ℝ => 1 - y) x :=
        (continuous_const.sub continuous_id).continuousAt
      have h2 : ContinuousAt (fun y : ℝ => Real.log (1 - y)) x :=
        (Real.continuousAt_log hpos.ne').comp (continuous_const.sub continuous_id).continuousAt
      exact (h1.mul h2).continuousWithinAt
    · -- b(x) = 3 x² / (6-2x) continuous on Ico 0 1
      intro x hx
      have hpos : 0 < 6 - 2 * x := h_six_minus_pos x hx
      have h_num_cont : ContinuousAt (fun y : ℝ => 3 * y ^ 2) x :=
        (continuous_const.mul (continuous_pow 2)).continuousAt
      have h_den_cont : ContinuousAt (fun y : ℝ => 6 - 2 * y) x :=
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt
      exact (h_num_cont.div h_den_cont hpos.ne').continuousWithinAt
  --
  -- STEP 11: g is differentiable on the interior of Ico 0 1, with derivative g'.
  --
  have hg_diff : DifferentiableOn ℝ g (interior (Set.Ico (0 : ℝ) 1)) := by
    intro x hx
    rw [interior_Ico] at hx
    have hxlb : (0 : ℝ) < x := hx.1
    have hxub : x < 1 := hx.2
    have hx1 : (0 : ℝ) < 1 - x := by linarith
    have hxs : (0 : ℝ) < 6 - 2 * x := by linarith
    exact (hg_HD x hx1 hxs).differentiableAt.differentiableWithinAt
  have hg_deriv_eq : ∀ x ∈ interior (Set.Ico (0 : ℝ) 1), deriv g x = g' x := by
    intro x hx
    rw [interior_Ico] at hx
    have hxlb : (0 : ℝ) < x := hx.1
    have hxub : x < 1 := hx.2
    have hx1 : (0 : ℝ) < 1 - x := by linarith
    have hxs : (0 : ℝ) < 6 - 2 * x := by linarith
    exact (hg_HD x hx1 hxs).deriv
  --
  -- STEP 12: g is MonotoneOn Ico 0 1; g(0) = 0, so g(α) ≥ 0.
  --
  have hg_mono : MonotoneOn g (Set.Ico (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico _ _) hg_cont hg_diff ?_
    intro x hx
    rw [hg_deriv_eq x hx]
    rw [interior_Ico] at hx
    exact hg'_nn x hx.1.le hx.2
  have hg_zero : g 0 = 0 := by
    change (1 - 0) * Real.log (1 - 0) + 0 - 3 * (0:ℝ) ^ 2 / (6 - 2 * 0) = 0
    simp [Real.log_one]
  have h0_mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hα_mem : α ∈ Set.Ico (0 : ℝ) 1 := ⟨hα_nn, hα_lt⟩
  have hg_at := hg_mono h0_mem hα_mem hα_nn
  rw [hg_zero] at hg_at
  -- hg_at : 0 ≤ g α = (1-α) log(1-α) + α - 3 α² / (6-2α)
  have h_unfold : 0 ≤ (1 - α) * Real.log (1 - α) + α - 3 * α ^ 2 / (6 - 2 * α) := hg_at
  linarith

/-- **Theorem A.2** (lower tail, paper form). For independent `{0,1}`-indicators `X_i` with
`μ = Σ p_i > 0` and `0 ≤ t < μ`:
  `P[Σ X_i ≤ μ - t] ≤ exp(-t² / (2·(μ - t/3)))`.

Note: the paper states `0 ≤ t ≤ μ`. We use strict `t < μ` so that the canonical
multiplicative-Chernoff form (which requires `ε = μ - t > 0`) applies. At `t = μ` the
RHS denominator `μ - t/3 = (2/3)μ > 0` so the bound is meaningful, but `P[S ≤ 0]` needs
a separate argument; not needed for §3 use. -/
theorem chernoff_A2_lower
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} (s : Finset ι)
    (X : ι → Ω → ℝ)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_indicator : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ι → ℝ)
    (h_p_bounds : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (h_p_eq : ∀ i, ∫ ω, X i ω ∂μ = p i)
    (t : ℝ) (ht_nn : 0 ≤ t) (ht_lt_μ : t < ∑ i ∈ s, p i)
    (h_μ_pos : 0 < ∑ i ∈ s, p i) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ (∑ i ∈ s, p i) - t} ≤
      Real.exp (- t^2 / (2 * ((∑ i ∈ s, p i) - t / 3))) := by
  set μ₀ : ℝ := ∑ i ∈ s, p i with hμ₀_def
  -- Edge case: t = 0. Then the exponent is 0 and the RHS = 1, so the bound is trivial.
  rcases eq_or_lt_of_le ht_nn with ht_eq | ht_pos
  · -- t = 0: RHS = exp 0 = 1 ≥ probability.
    rw [← ht_eq]
    simp only [pow_two, mul_zero, neg_zero, zero_div, Real.exp_zero]
    exact measureReal_le_one
  -- Now 0 < t < μ₀. Apply multiplicative_chernoff_indicators_lower with ε := μ₀ - t.
  have hε_pos : 0 < μ₀ - t := by linarith
  have hε_lt_μ : μ₀ - t < μ₀ := by linarith
  have h_cher := multiplicative_chernoff_indicators_lower (μ := μ) s X
    h_indep h_meas h_indicator p h_p_bounds h_p_eq (μ₀ - t) hε_pos hε_lt_μ
  -- Convert {ω | ΣX ≤ μ₀ - t} (target set) into the form {ω | ΣX ≤ ε} with ε = μ₀ - t.
  refine h_cher.trans ?_
  apply Real.exp_le_exp.mpr
  -- Goal: -(μ₀-t)·log((μ₀-t)/μ₀) + (μ₀-t) - μ₀ ≤ -t² / (2·(μ₀ - t/3))
  -- i.e., (μ₀-t)·log((μ₀-t)/μ₀) + t ≤ t² / (2·(μ₀ - t/3))... wait the sign.
  --
  -- Actually: -(μ₀-t)·log((μ₀-t)/μ₀) + (μ₀-t) - μ₀ = -(μ₀-t)·log(1-α) - t where α = t/μ₀,
  -- = -μ₀(1-α) log(1-α) - μ₀ α.
  -- We want this ≤ -t²/(2(μ₀-t/3)) = -μ₀² α² / (μ₀(6-2α)/3) = -3μ₀ α²/(6-2α) = -μ₀·3α²/(6-2α).
  -- Equivalently: μ₀·3α²/(6-2α) ≤ μ₀(1-α) log(1-α) + μ₀ α = μ₀·[(1-α) log(1-α) + α].
  -- Divide by μ₀ > 0: 3α²/(6-2α) ≤ (1-α) log(1-α) + α, which is bennett_real_ineq_lower.
  set α : ℝ := t / μ₀ with hα_def
  have hα_nn : (0 : ℝ) ≤ α := by
    rw [hα_def]; exact div_nonneg ht_nn h_μ_pos.le
  have hα_pos : 0 < α := by rw [hα_def]; exact div_pos ht_pos h_μ_pos
  have hα_lt_one : α < 1 := by
    rw [hα_def, div_lt_one h_μ_pos]; exact ht_lt_μ
  have h_ratio_eq : (μ₀ - t) / μ₀ = 1 - α := by
    rw [hα_def]; field_simp
  have h_t_eq : t = μ₀ * α := by
    rw [hα_def]; field_simp
  have h_one_minus_α_pos : 0 < 1 - α := by linarith
  -- The Bennett lower-tail inequality:
  have h_bennett : 3 * α ^ 2 / (6 - 2 * α) ≤ (1 - α) * Real.log (1 - α) + α :=
    bennett_real_ineq_lower hα_nn hα_lt_one
  -- Rewrite the LHS and RHS of the goal.
  rw [h_ratio_eq]
  have h_diff_eq : μ₀ - t = μ₀ * (1 - α) := by rw [h_t_eq]; ring
  rw [h_diff_eq, h_t_eq]
  -- Goal:
  --   -(μ₀ * (1 - α)) * log(1 - α) + μ₀ * (1 - α) - μ₀
  --     ≤ -(μ₀ * α)^2 / (2 · (μ₀ - (μ₀ * α)/3))
  -- LHS = -μ₀(1-α) log(1-α) + μ₀(1-α) - μ₀ = -μ₀(1-α) log(1-α) - μ₀ α
  --     = -μ₀ · [(1-α) log(1-α) + α].
  -- RHS denominator: 2 · (μ₀ - μ₀ α/3) = 2 μ₀ (1 - α/3) = μ₀(6 - 2α)/3.
  --   So RHS = -(μ₀ α)² · 3 / (μ₀(6-2α)) = -3 μ₀ α²/(6-2α) = -μ₀ · 3α²/(6-2α).
  -- Inequality becomes: -μ₀ · [(1-α) log(1-α) + α] ≤ -μ₀ · 3α²/(6-2α)
  --   ⇔ μ₀ · 3α²/(6-2α) ≤ μ₀ · [(1-α) log(1-α) + α]
  --   ⇐ 3α²/(6-2α) ≤ (1-α) log(1-α) + α (and μ₀ ≥ 0).
  have h_six_minus_pos : (0 : ℝ) < 6 - 2 * α := by linarith
  have h_six_minus_ne : (6 - 2 * α : ℝ) ≠ 0 := h_six_minus_pos.ne'
  -- Multiply Bennett by μ₀ > 0.
  have h_mul : μ₀ * (3 * α ^ 2 / (6 - 2 * α)) ≤ μ₀ * ((1 - α) * Real.log (1 - α) + α) :=
    mul_le_mul_of_nonneg_left h_bennett h_μ_pos.le
  have h_one_minus_third_pos : (0 : ℝ) < 1 - α / 3 := by linarith
  have h_denom_inner_pos : 0 < μ₀ - μ₀ * α / 3 := by
    have h_pos : 0 < μ₀ * (1 - α / 3) := mul_pos h_μ_pos h_one_minus_third_pos
    have : μ₀ * (1 - α / 3) = μ₀ - μ₀ * α / 3 := by ring
    linarith
  have h_denom_pos : 0 < 2 * (μ₀ - μ₀ * α / 3) := by linarith
  have h_denom_ne : 2 * (μ₀ - μ₀ * α / 3) ≠ 0 := h_denom_pos.ne'
  -- Algebraic identity: -(μ₀ α)² / (2 (μ₀ - μ₀ α / 3)) = -(μ₀ · 3 α² / (6 - 2α)).
  have h_rhs_eq : -(μ₀ * α) ^ 2 / (2 * (μ₀ - μ₀ * α / 3))
        = -(μ₀ * (3 * α ^ 2 / (6 - 2 * α))) := by
    have h_lhs_eq : -(μ₀ * α) ^ 2 / (2 * (μ₀ - μ₀ * α / 3))
        = -((μ₀ * α) ^ 2 / (2 * (μ₀ - μ₀ * α / 3))) := by ring
    have h_rhs_split : μ₀ * (3 * α ^ 2 / (6 - 2 * α))
        = (μ₀ * (3 * α ^ 2)) / (6 - 2 * α) := by
      rw [mul_div_assoc']
    rw [h_lhs_eq, h_rhs_split]
    congr 1
    rw [div_eq_div_iff h_denom_ne h_six_minus_ne]
    ring
  rw [h_rhs_eq]
  -- Goal: -(μ₀ * (1-α)) * log(1-α) + μ₀ * (1-α) - μ₀ ≤ -(μ₀ * (3 * α^2 / (6 - 2α)))
  -- LHS = -μ₀(1-α) log(1-α) + μ₀ - μ₀ α - μ₀ = -μ₀(1-α) log(1-α) - μ₀ α
  --     = -μ₀ · [(1-α) log(1-α) + α].
  -- We have μ₀ · 3α²/(6-2α) ≤ μ₀ · [(1-α) log(1-α) + α], so
  --   -μ₀ · [(1-α) log(1-α) + α] ≤ -μ₀ · 3α²/(6-2α). Done.
  nlinarith [h_mul, h_μ_pos]


end DaveyThesis2024.Concentration
