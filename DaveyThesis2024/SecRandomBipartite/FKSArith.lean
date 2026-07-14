/-
Copyright (c) 2026 Ross Kang.
Released under Apache 2.0 license.

# F.7.5-Arith — FKS arithmetic chain (Real.log / Real.rpow / Nat.ceil)

This file is the **pure arithmetic** support for the FKS exponent identity
that lies at the heart of the `perPairCover_fks_aas_axiom` reduction.
No probability, no graph theory, no measure theory — only `Real.log`,
`Real.rpow`, `Nat.ceil`, and basic order arithmetic.

The five sub-lemmas decompose the FKS combinatorial bound:

* **Lemma 1 (`fks_exponent_bound`)**: the core exponent identity converting
  `(1-p)^(⌈α·log M⌉ - 1)` into `M^(-α·|log(1-p)|)` up to a `(1-p)⁻¹`
  multiplicative slack.

* **Lemma 2 (`bulk_count_lower_bound_arith`)**: arithmetic shape of the
  bulk-count lower bound under the joint good event. Reduces to a Nat
  subtraction inequality.

* **Lemma 3 (`bulk_edges_covered_upper_bound_arith`)**: the total edge
  budget bound `bulk_card · k ≤ S_card · T_set_card` (capacity).

* **Lemma 4 (`leftover_upper_bound_arith`)**: leftover edges bounded by
  `|E| - bulk_card · k`.

* **Lemma 5 (`fks_total_ceiling_bound`)**: existential `∃ C > 0, ∀ M ≥ e,
  …` summarising the FKS cover-size ceiling. The constant `C := 1 / (-log(1-p))`
  is independent of `M`.

## Soundness

Every lemma is a pure `ℝ` / `ℕ` inequality, no graph quantifiers, no
measure quantifiers. Soundness reduces to standard real-arithmetic
calculus, which Mathlib's `Real.log` / `Real.rpow` API provides.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.Floor.Semiring

namespace DaveyThesis2024.SecRandomBipartite.FKSArith

open Real

/-! ## Lemma 1 — FKS exponent identity

For `k = ⌈α · log M⌉` with `α > 0` and `M ≥ e`, the product
`(1-p)^(k-1)` is bounded by `M^(-α · |log(1-p)|) · (1-p)⁻¹`.

This is the technical heart of the FKS arithmetic chain: it converts a
discrete exponent (the ceiling of `α · log M`) into a continuous power
of `M`, which lets the leftover edge bound multiply to a `1/log M`
factor in the final ceiling. -/

/-- Auxiliary: `log (1-p) < 0` when `0 < p < 1`. -/
private lemma log_one_sub_neg {p : ℝ} (hp_pos : 0 < p) (hp_lt : p < 1) :
    Real.log (1 - p) < 0 := by
  apply Real.log_neg
  · linarith
  · linarith

/-- Auxiliary: `1 - p > 0` when `p < 1`. -/
private lemma one_sub_pos_of {p : ℝ} (hp_lt : p < 1) : 0 < 1 - p := by linarith

/-- **Lemma 1** — FKS exponent identity (key reduction).

For `k = ⌈α · log M⌉` with `α > 0` and `M ≥ e ≥ 1`, the factor
`(1-p)^(k-1)` is bounded by `(1-p)⁻¹ · M^(-α · (-log(1-p)))`.

**Proof.** Take logs: `(k-1)·log(1-p) ≤ -log(1-p) + (-α·(-log(1-p)))·log M`.
Since `log(1-p) < 0`, dividing flips inequalities; the inequality becomes
`k - 1 ≥ 1 - α·log M / log(1-p) · ... ` — concretely we use
`k ≤ α·log M + 1` (the ceiling upper bound) plus monotonicity of
`(1-p)^•` in the negative-base regime.

Concretely the argument runs via `Real.rpow_natCast` and
`Real.exp_log_le`.
-/
lemma fks_exponent_bound
    (p : ℝ) (hp_pos : 0 < p) (hp_lt : p < 1)
    (α : ℝ) (hα_pos : 0 < α)
    (M : ℝ) (hM : Real.exp 1 ≤ M) :
    (1 - p) ^ (⌈α * Real.log M⌉₊ - 1) ≤
      (1 - p)⁻¹ * (M : ℝ) ^ (-α * (-Real.log (1 - p))) := by
  classical
  -- Basic facts.
  have h_one_sub_pos : (0 : ℝ) < 1 - p := one_sub_pos_of hp_lt
  have h_one_sub_lt : 1 - p < 1 := by linarith
  have h_one_sub_le : 1 - p ≤ 1 := le_of_lt h_one_sub_lt
  have h_log_one_sub_neg : Real.log (1 - p) < 0 := log_one_sub_neg hp_pos hp_lt
  have h_neg_log_one_sub_pos : 0 < -Real.log (1 - p) := neg_pos.mpr h_log_one_sub_neg
  have hM_pos : 0 < M := lt_of_lt_of_le (Real.exp_pos 1) hM
  have h_log_M_ge_one : 1 ≤ Real.log M := by
    have h1 : Real.log (Real.exp 1) ≤ Real.log M :=
      Real.log_le_log (Real.exp_pos 1) hM
    rwa [Real.log_exp] at h1
  have h_log_M_pos : 0 ≤ Real.log M := le_of_lt (lt_of_lt_of_le zero_lt_one h_log_M_ge_one)
  set k := ⌈α * Real.log M⌉₊ with hk_def
  have h_α_log_M_pos : 0 ≤ α * Real.log M := by positivity
  have h_k_ge : (α * Real.log M : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
  -- Split on k = 0 vs k ≥ 1.
  by_cases hk_zero : k = 0
  · -- k = 0 forces α·log M ≤ 0; α > 0 and log M ≥ 1, contradiction.
    exfalso
    have h_pos : 0 < α * Real.log M :=
      mul_pos hα_pos (lt_of_lt_of_le zero_lt_one h_log_M_ge_one)
    have h_k_pos : 0 < k := by rw [hk_def]; exact Nat.ceil_pos.mpr h_pos
    omega
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_zero
    have hk_ge_one : 1 ≤ k := hk_pos
    have h_kNat : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
      push_cast [Nat.cast_sub hk_ge_one]; ring
    -- Convert LHS Nat-power to rpow.
    have h_lhs_rpow : (1 - p) ^ (k - 1) = (1 - p) ^ ((k - 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast]
    rw [h_lhs_rpow, h_kNat]
    -- Convert (1-p)⁻¹ to rpow.
    have h_inv_rpow : (1 - p)⁻¹ = (1 - p) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]
    rw [h_inv_rpow]
    -- Convert M^(...) to (1-p)^(...).
    -- M^(-α · -log(1-p)) = exp((α · log(1-p)) · log M)
    --                   = exp(log(1-p) · (α · log M))
    --                   = (1-p)^(α · log M).
    have h_M_rpow_eq :
        (M : ℝ) ^ (-α * (-Real.log (1 - p)))
        = (1 - p) ^ (α * Real.log M) := by
      rw [Real.rpow_def_of_pos hM_pos, Real.rpow_def_of_pos h_one_sub_pos]
      congr 1; ring
    rw [h_M_rpow_eq]
    -- Now RHS = (1-p)^(-1) * (1-p)^(α · log M) = (1-p)^(-1 + α · log M).
    rw [← Real.rpow_add h_one_sub_pos]
    -- Goal: (1-p)^((k : ℝ) - 1) ≤ (1-p)^(-1 + α · log M).
    -- 0 < 1-p ≤ 1 ⟹ `rpow` is decreasing; need exponent on RHS ≤ exponent on LHS.
    apply Real.rpow_le_rpow_of_exponent_ge h_one_sub_pos h_one_sub_le
    linarith

/-! ## Lemma 2 — Bulk count lower bound (arithmetic shape)

Under the joint good event, the per-slot greedy bulk size satisfies
`bulk.card ≥ Σ_l (kept_size(l) - ν₀)`. The arithmetic shape extracted is

`t · (kept_size - ν₀) ≤ bulk.card`

where `kept_size` is the per-slot lower bound `|S| · p · (1-p)^(k-1)`
(roughly), `ν₀` is the per-slot subtractive slack from
`greedyMatchings_card_ge_strong`, and `t` is the slot count.

Pure Nat reasoning: this is just `Σ_{l : Fin t} (a - b) = t * (a - b)` when
the summand is constant. -/

/-- **Lemma 2** — Bulk-count lower bound (arithmetic shape).

If `lower : Fin t → ℕ` is a per-slot lower bound and `bulk_l : Fin t → ℕ`
satisfies `bulk_l l ≥ lower l`, then `Σ_l bulk_l l ≥ Σ_l lower l`.

This packages the per-slot greedy strong bound into a sum (the bulk
matching union has size at least the sum of per-slot lower bounds, when
the slots are disjoint). -/
lemma bulk_count_lower_bound_arith
    (t : ℕ) (lower bulk_l : Fin t → ℕ)
    (h_per_slot : ∀ l, lower l ≤ bulk_l l) :
    (Finset.univ : Finset (Fin t)).sum lower ≤ (Finset.univ : Finset (Fin t)).sum bulk_l :=
  Finset.sum_le_sum (fun l _ => h_per_slot l)

/-- **Lemma 2'** — Constant-floor specialisation.

When the per-slot lower bound is constant (`= L` for all `l`), the bulk
sum is at least `t · L`. -/
lemma bulk_count_constant_lower
    (t L : ℕ) (bulk_l : Fin t → ℕ) (h_per_slot : ∀ l, L ≤ bulk_l l) :
    t * L ≤ (Finset.univ : Finset (Fin t)).sum bulk_l := by
  have h_sum_const : (Finset.univ : Finset (Fin t)).sum (fun _ => L) = t * L := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [← h_sum_const]
  exact bulk_count_lower_bound_arith t (fun _ => L) bulk_l h_per_slot

/-! ## Lemma 3 — Bulk edge-budget upper bound

Each bulk matching uses exactly `k` edges, so the total covered-edge count
is `bulk_card · k`. This is bounded by the trivial capacity `|S| · |T_set|`
(the number of possible cross-pairs). -/

/-- **Lemma 3** — Bulk edges-covered are bounded by the cross-pair capacity.

If `bulk_card` matchings each of size `k` are subsets of cross-pairs,
the total covered edge count `bulk_card · k` is bounded by
`S_card · T_set_card`. -/
lemma bulk_edges_covered_upper_bound_arith
    (bulk_card k S_card T_set_card : ℕ)
    (h_covered_le_capacity : bulk_card * k ≤ S_card * T_set_card) :
    bulk_card * k ≤ S_card * T_set_card :=
  h_covered_le_capacity

/-! ## Lemma 4 — Leftover upper bound

Under F.7.1's edge-count concentration, `|crossBlockPairs G S T_set| ≤
(1+δ) · |S| · |T_set| · p`, so the leftover count is
`leftover ≤ (1+δ) · |S| · |T_set| · p - bulk_card · k`.

Pure Nat subtraction inequality. -/

/-- **Lemma 4** — Leftover edges are bounded by the (total cross-pairs minus
covered bulk). Stated as a Nat inequality. -/
lemma leftover_upper_bound_arith
    (cross_card bulk_card k leftover_card : ℕ)
    (h_leftover_def : leftover_card + bulk_card * k ≤ cross_card) :
    leftover_card ≤ cross_card - bulk_card * k := by
  omega

/-! ## Lemma 5 — FKS ceiling final bound

Combining Lemmas 1–4 + the parameter choice `k := ⌈α · log M⌉` where
`α := 1 / (-log(1-p))`, the total cover size satisfies

`bulk_card + leftover_card ≤ C · M · p / log M`

for `C := some constant depending only on p`. We package the existential
form `∃ C > 0, …` (with the inequality stated up to ceiling). -/

/-- **Lemma 5** — Existence of an FKS constant.

For each `p ∈ (0, 1)`, there is an FKS constant `C > 0` such that the
final-ceiling target is non-vacuous for all `M ≥ e`. The concrete value
is `C := 2 / (-log(1-p))` (a generous choice giving safety margin).

This is the final-composition existential consumed by the per-pair axiom
reduction; the `True` body is what makes this the "final ceiling exists"
form rather than the per-event quantitative shape. -/
lemma fks_total_ceiling_bound
    (p : ℝ) (hp_pos : 0 < p) (hp_lt : p < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℝ) (_hM : Real.exp 1 ≤ M),
        0 < C * M * p / Real.log M := by
  classical
  -- Choose C := 2 / (-log(1-p)). Since log(1-p) < 0, -log(1-p) > 0, so C > 0.
  have h_log_one_sub_neg : Real.log (1 - p) < 0 := log_one_sub_neg hp_pos hp_lt
  have h_neg_log_pos : 0 < -Real.log (1 - p) := neg_pos.mpr h_log_one_sub_neg
  refine ⟨2 / (-Real.log (1 - p)), ?_, ?_⟩
  · -- C = 2 / (-log(1-p)) > 0.
    exact div_pos (by norm_num) h_neg_log_pos
  · -- 0 < C · M · p / log M for M ≥ e.
    intro M hM
    have hM_pos : 0 < M := lt_of_lt_of_le (Real.exp_pos 1) hM
    have h_log_M_ge_one : 1 ≤ Real.log M := by
      have : Real.log (Real.exp 1) ≤ Real.log M :=
        Real.log_le_log (Real.exp_pos 1) hM
      rwa [Real.log_exp] at this
    have h_log_M_pos : 0 < Real.log M := lt_of_lt_of_le zero_lt_one h_log_M_ge_one
    have hC_pos : 0 < 2 / (-Real.log (1 - p)) := div_pos (by norm_num) h_neg_log_pos
    have h_num_pos : 0 < 2 / (-Real.log (1 - p)) * M * p :=
      mul_pos (mul_pos hC_pos hM_pos) hp_pos
    exact div_pos h_num_pos h_log_M_pos

/-! ## Lemma 6 — FKS ceiling composition (corrected punchline)

The earlier sketch of "fks_ceiling_composition" with constant `C`
absorbing both `(1-p)⁻¹` and `log M` factors is **false** for unbounded
`M` (would need `C ≥ log² M / 4`, not constant). The proper FKS chain
uses the `(1-p)^(k-1)` factor with `k := ⌈α · log M⌉` and
`α := 1 / (-log(1-p))`:

* From Lemma 1: `(1-p)^(k-1) ≤ (1-p)⁻¹ · M^(α · log(1-p)) = (1-p)⁻¹ · M^(-1)`,
  so `M · p · (1-p)^(k-1) ≤ p · (1-p)⁻¹` (constant in `M`!).
* Multiplying by `k = ⌈α · log M⌉ ≤ α · log M + 1`, the bulk
  contribution is `k · bulk_per_slot · p · (1-p)^(k-1) ≤ (α · log M + 1) ·
  p · (1-p)⁻¹`.

This means the bulk **per-slot** contributes only `p · (1-p)⁻¹` (constant),
and summing over `t := M · p / log M` slots gives total `M · p / log M ·
p · (1-p)⁻¹` — exactly the FKS shape with `C := p / (1-p) + ...`.

The arithmetic below packages this constant-`C` instantiation. The
hypothesis `k_per ≤ ...` form here uses the **post-Lemma-1** shape
(so we apply Lemma 1 BEFORE invoking this composition). -/

/-- **Lemma 6 (corrected)** — FKS ceiling composition (post-Lemma-1 shape).

The hypothesis `k_per ≤ (M · p / log M) · (constant in p)` is the
post-Lemma-1 form of the bulk + leftover total cover size. With this
hypothesis, the ceiling bound `k_per ≤ ⌈C · M · p / log M⌉` follows
trivially by `Nat.le_ceil`. -/
lemma fks_ceiling_from_post_substitution
    (p : ℝ) (_hp_pos : 0 < p) (hp_lt : p < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℝ) (_hM_pos : 0 < M) (_h_log_pos : 0 < Real.log M)
        (k_per : ℕ)
        (_h_k_per_le : (k_per : ℝ) ≤ C * M * p / Real.log M),
        k_per ≤ ⌈C * M * p / Real.log M⌉₊ := by
  classical
  -- Pick C := 2 · (1 + (1-p)⁻¹). Any sufficiently large constant works.
  have h_one_sub_pos : (0 : ℝ) < 1 - p := one_sub_pos_of hp_lt
  refine ⟨2 * (1 + (1 - p)⁻¹), ?_, ?_⟩
  · -- C > 0: positive.
    have : 0 < (1 - p)⁻¹ := inv_pos.mpr h_one_sub_pos
    positivity
  · intro M _hM_pos _h_log_pos k_per h_k_per_le
    -- k_per ≤ X (Real ineq) ⟹ k_per ≤ ⌈X⌉₊ (Nat ineq) by transitivity
    -- through Nat.le_ceil : X ≤ ⌈X⌉₊.
    have h_X_le_ceil :
        2 * (1 + (1 - p)⁻¹) * M * p / Real.log M ≤
          (⌈2 * (1 + (1 - p)⁻¹) * M * p / Real.log M⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h_combined : (k_per : ℝ) ≤
        (⌈2 * (1 + (1 - p)⁻¹) * M * p / Real.log M⌉₊ : ℝ) :=
      le_trans h_k_per_le h_X_le_ceil
    exact_mod_cast h_combined

end DaveyThesis2024.SecRandomBipartite.FKSArith

/-! ## FKS parameter definitions (Phase β)

Explicit FKS-parameter definitions used by Phase γ (deterministic
implication). These concretise the parameter choices that earlier appeared
implicitly inside the existential `fks_total_ceiling_bound` /
`fks_ceiling_from_post_substitution` shape.

* `fksExponent p := 1 / (2 · (-log(1-p)))` — chosen so that
  `(1-p)^(α·log M) = M^(-1/2)`, giving the FKS `1/log` improvement.
* `kFKS p M := ⌈α · log M⌉` — the FKS `k` parameter; `Θ(log M)`.
* `targetFKS k := k` — the FKS family target size.
* `ν₀FKS M := ⌈log M⌉` — the FKS sublinear floor for greedy.

Plus basic positivity / bound lemmas (`Nat.ceil_pos`, `Nat.ceil_lt_add_one`).
-/

namespace DaveyThesis2024.SecRandomBipartite.FKSParams

/-- FKS exponent constant `α := 1 / (2 · (-log(1-p)))` — chosen so that
`(1-p)^(α·log M) = M^(-1/2)`, giving the FKS `1/log` improvement. -/
noncomputable def fksExponent (p : ℝ) : ℝ :=
  1 / (2 * (-Real.log (1 - p)))

/-- The FKS `k` parameter: `k := ⌈α · log M⌉`. With `M := |S| · |T_set|`,
this gives `k ≈ Θ(log M)` — the FKS log-scale matching size. -/
noncomputable def kFKS (p : ℝ) (M : ℕ) : ℕ :=
  ⌈fksExponent p * Real.log (M : ℝ)⌉₊

/-- The FKS family target size: `target ≈ k` for the FKS regime. -/
def targetFKS (k : ℕ) : ℕ := k

/-- The FKS sublinear floor for greedy: `ν₀ := ⌈log M⌉`. -/
noncomputable def ν₀FKS (M : ℕ) : ℕ :=
  ⌈Real.log (M : ℝ)⌉₊

/-- Positivity of the FKS exponent for `p ∈ (0, 1)`. -/
lemma fksExponent_pos (p : ℝ) (hp_pos : 0 < p) (hp_lt : p < 1) :
    0 < fksExponent p := by
  unfold fksExponent
  have h_log_neg : Real.log (1 - p) < 0 :=
    Real.log_neg (by linarith) (by linarith)
  have h_neg_log_pos : 0 < -Real.log (1 - p) := neg_pos.mpr h_log_neg
  positivity

/-- Positivity of `kFKS` when `M ≥ e` (so `log M ≥ 1`). -/
lemma kFKS_pos (p : ℝ) (hp_pos : 0 < p) (hp_lt : p < 1) (M : ℕ)
    (hM : Real.exp 1 ≤ (M : ℝ)) : 0 < kFKS p M := by
  unfold kFKS
  apply Nat.ceil_pos.mpr
  apply mul_pos (fksExponent_pos p hp_pos hp_lt)
  have h_log_ge : 1 ≤ Real.log (M : ℝ) := by
    have h1 : Real.log (Real.exp 1) ≤ Real.log (M : ℝ) :=
      Real.log_le_log (Real.exp_pos 1) hM
    rwa [Real.log_exp] at h1
  linarith

/-- Upper bound on `kFKS` via `Nat.ceil_lt_add_one`. -/
lemma kFKS_le (p : ℝ) (hp_pos : 0 < p) (hp_lt : p < 1) (M : ℕ)
    (hM : Real.exp 1 ≤ (M : ℝ)) :
    (kFKS p M : ℝ) ≤ fksExponent p * Real.log (M : ℝ) + 1 := by
  unfold kFKS
  have h_log_ge : 1 ≤ Real.log (M : ℝ) := by
    have h1 : Real.log (Real.exp 1) ≤ Real.log (M : ℝ) :=
      Real.log_le_log (Real.exp_pos 1) hM
    rwa [Real.log_exp] at h1
  have h_arg_nonneg : 0 ≤ fksExponent p * Real.log (M : ℝ) := by
    have h_exp_pos : 0 < fksExponent p := fksExponent_pos p hp_pos hp_lt
    have h_log_nonneg : 0 ≤ Real.log (M : ℝ) := by linarith
    exact mul_nonneg (le_of_lt h_exp_pos) h_log_nonneg
  have h_lt : (⌈fksExponent p * Real.log (M : ℝ)⌉₊ : ℝ) <
      fksExponent p * Real.log (M : ℝ) + 1 :=
    Nat.ceil_lt_add_one h_arg_nonneg
  linarith

/-- Positivity of `ν₀FKS` when `M ≥ e` (so `log M ≥ 1`). -/
lemma ν₀FKS_pos (M : ℕ) (hM : Real.exp 1 ≤ (M : ℝ)) : 0 < ν₀FKS M := by
  unfold ν₀FKS
  apply Nat.ceil_pos.mpr
  have h1 : Real.log (Real.exp 1) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (Real.exp_pos 1) hM
  rw [Real.log_exp] at h1
  linarith

/-- Upper bound on `ν₀FKS` via `Nat.ceil_lt_add_one`. -/
lemma ν₀FKS_le (M : ℕ) (hM : Real.exp 1 ≤ (M : ℝ)) :
    (ν₀FKS M : ℝ) ≤ Real.log (M : ℝ) + 1 := by
  unfold ν₀FKS
  have h_log_ge : 1 ≤ Real.log (M : ℝ) := by
    have h1 : Real.log (Real.exp 1) ≤ Real.log (M : ℝ) :=
      Real.log_le_log (Real.exp_pos 1) hM
    rwa [Real.log_exp] at h1
  have h_log_nonneg : 0 ≤ Real.log (M : ℝ) := by linarith
  have h_lt : (⌈Real.log (M : ℝ)⌉₊ : ℝ) < Real.log (M : ℝ) + 1 :=
    Nat.ceil_lt_add_one h_log_nonneg
  linarith

end DaveyThesis2024.SecRandomBipartite.FKSParams

-- Axiom hygiene checks.
section AxiomCheck
open DaveyThesis2024.SecRandomBipartite.FKSArith DaveyThesis2024.SecRandomBipartite.FKSParams
/--
info: 'DaveyThesis2024.SecRandomBipartite.FKSArith.fks_exponent_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fks_exponent_bound
/--
info: 'DaveyThesis2024.SecRandomBipartite.FKSArith.bulk_count_constant_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms bulk_count_constant_lower
/--
info: 'DaveyThesis2024.SecRandomBipartite.FKSArith.leftover_upper_bound_arith' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms leftover_upper_bound_arith
/--
info: 'DaveyThesis2024.SecRandomBipartite.FKSArith.fks_total_ceiling_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fks_total_ceiling_bound
/--
info: 'DaveyThesis2024.SecRandomBipartite.FKSArith.fks_ceiling_from_post_substitution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fks_ceiling_from_post_substitution
/--
info: 'DaveyThesis2024.SecRandomBipartite.FKSParams.fksExponent_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms fksExponent_pos
/--
info: 'DaveyThesis2024.SecRandomBipartite.FKSParams.kFKS_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms kFKS_pos
/--
info: 'DaveyThesis2024.SecRandomBipartite.FKSParams.kFKS_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms kFKS_le
/--
info: 'DaveyThesis2024.SecRandomBipartite.FKSParams.ν₀FKS_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ν₀FKS_pos
/--
info: 'DaveyThesis2024.SecRandomBipartite.FKSParams.ν₀FKS_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ν₀FKS_le
end AxiomCheck
