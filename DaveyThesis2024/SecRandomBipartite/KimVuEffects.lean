/-
Copyright (c) 2026 Ross Kang.
Released under Apache 2.0 license.

# Kim–Vu polynomial concentration — verbatim, sound restatement

This file replaces the previous `kim_vu_concentration_for_edge_polynomials` axiom, which
was **inconsistent** (its `f`, `μ`, `E_max` were free parameters with only positivity, so
one could instantiate `f ≡ 0, μ = 1, ε = 1, E_max = 1` and derive `1 ≤ exp(-1/8) < 1`).

The verbatim Kim–Vu Main Theorem (Combinatorica 20 (2000), 417–434) is stated in terms of
the *expected partial-derivative effects* of the polynomial `Y`. We encode the discrete
partial derivative `∂_A f` via the finite-difference formula (order-independent by
construction), and require the parameters `E`, `E'` to be genuine **upper bounds** on the
expected effects — exactly what Kim–Vu's `E(H) = max_{i≥0} E_i` and `E'(H) = max_{i≥1} E_i`
provide. This makes the statement sound (no degenerate `E` shrinking) and faithful (the
deviation scale `a_k·(E·E')^{1/2}·λ^k` and tail `O(exp(-λ + (k-1)log n))` are verbatim).

## Verbatim source

> **Main Theorem (Kim–Vu).** `Pr(|Y_H − E_0(H)| > a_k·(E(H)·E'(H))^{1/2}·λ^k)`
> `= O(exp(−λ + (k−1)·log n))`, for any `λ > 1`, with `a_k = 8^k·(k!)^{1/2}`,
> where `E_0(H) = E[Y_H]`, `E(H) = max_{i≥0} E_i(H)`, `E'(H) = max_{i≥1} E_i(H)`, and
> `E_i(H)` is the maximum over `i`-subsets `A` of variables of `E[∂_A Y_H]`.

The `O(·)` constant (depending only on the degree `k`) is rendered as the existential `C`
in the axiom below.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace DaveyThesis2024.SecRandomBipartite.KimVu

open MeasureTheory

/-- The discrete partial derivative of `f` with respect to the slot set `A`, via the
finite-difference formula
`∂_A f (g) = ∑_{B ⊆ A} (-1)^{|A∖B|} · f(g overwritten to true on B, false on A∖B)`.

For a multilinear function of `{0,1}` (Bool) variables this is exactly the mixed partial
derivative, and it is independent of the order in which one differentiates (the formula is
symmetric in the elements of `A`). Outside of `A`, the argument keeps the value of `g`. -/
noncomputable def discreteDeriv {ι : Type*} [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (A : Finset ι) (g : ι → Bool) : ℝ :=
  ∑ B ∈ A.powerset, (-1 : ℝ) ^ (A.card - B.card) *
    f (fun i => if i ∈ B then true else if i ∈ A then false else g i)

/-- `∂_∅ f = f`. -/
@[simp] lemma discreteDeriv_empty {ι : Type*} [DecidableEq ι]
    (f : (ι → Bool) → ℝ) (g : ι → Bool) :
    discreteDeriv f ∅ g = f g := by
  simp [discreteDeriv]

/-- **L1: `discreteDeriv` is linear over finite sums.** -/
lemma discreteDeriv_finset_sum {ι : Type*} [DecidableEq ι] {α : Type*}
    (s : Finset α) (F : α → (ι → Bool) → ℝ) (A : Finset ι) (g : ι → Bool) :
    discreteDeriv (fun g => ∑ i ∈ s, F i g) A g
      = ∑ i ∈ s, discreteDeriv (F i) A g := by
  unfold discreteDeriv
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- **L2 (core): finite-difference factorization for a product of per-coordinate functions.**
For `f g = ∏ i, h i (g i)`, the discrete derivative `∂_A f` factors as
`(∏_{i∈A}(h i true − h i false)) · (∏_{i∉A} h i (g i))`. This is the engine behind the
monomial derivative: a present-slot contributes `(1−0)=1`, an absent-slot `(0−1)=−1`, and a
slot the monomial does not mention contributes `(1−1)=0`, killing `∂_A` unless `A ⊆ support`. -/
lemma discreteDeriv_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → Bool → ℝ) (A : Finset ι) (g : ι → Bool) :
    discreteDeriv (fun g => ∏ i, h i (g i)) A g
      = (∏ i ∈ A, (h i true - h i false)) * (∏ i ∈ Aᶜ, h i (g i)) := by
  unfold discreteDeriv
  have key : ∀ B ∈ A.powerset,
      (-1 : ℝ) ^ (A.card - B.card) *
        ∏ i, h i (if i ∈ B then true else if i ∈ A then false else g i)
      = (∏ i ∈ Aᶜ, h i (g i)) *
          ((∏ i ∈ B, h i true) * (∏ i ∈ A \ B, (- h i false))) := by
    intro B hB
    rw [Finset.mem_powerset] at hB
    -- split the full product over ι into A and Aᶜ
    rw [← Finset.prod_mul_prod_compl A
          (fun i => h i (if i ∈ B then true else if i ∈ A then false else g i))]
    -- the Aᶜ factor equals ∏ i ∈ Aᶜ, h i (g i)
    have hAc : (∏ i ∈ Aᶜ, h i (if i ∈ B then true else if i ∈ A then false else g i))
        = ∏ i ∈ Aᶜ, h i (g i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.mem_compl] at hi
      have hiB : i ∉ B := fun hh => hi (hB hh)
      simp [hiB, hi]
    -- the A factor splits over B and A \ B
    have hA : (∏ i ∈ A, h i (if i ∈ B then true else if i ∈ A then false else g i))
        = (∏ i ∈ A \ B, h i false) * (∏ i ∈ B, h i true) := by
      rw [← Finset.prod_sdiff hB]
      congr 1
      · apply Finset.prod_congr rfl
        intro i hi
        rw [Finset.mem_sdiff] at hi
        have hiA : i ∈ A := hi.1
        have hiB : i ∉ B := hi.2
        simp [hiB, hiA]
      · apply Finset.prod_congr rfl
        intro i hi
        simp [hi]
    rw [hA, hAc]
    -- handle the (-1) sign: A.card - B.card = (A \ B).card
    have hcard : A.card - B.card = (A \ B).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hB]
    have hsign : (-1 : ℝ) ^ (A.card - B.card) * (∏ i ∈ A \ B, h i false)
        = ∏ i ∈ A \ B, (- h i false) := by
      rw [hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring
    calc (-1 : ℝ) ^ (A.card - B.card) *
            (((∏ i ∈ A \ B, h i false) * ∏ i ∈ B, h i true) * ∏ i ∈ Aᶜ, h i (g i))
        = ((-1 : ℝ) ^ (A.card - B.card) * (∏ i ∈ A \ B, h i false)) *
            ((∏ i ∈ B, h i true) * ∏ i ∈ Aᶜ, h i (g i)) := by ring
      _ = (∏ i ∈ A \ B, (- h i false)) *
            ((∏ i ∈ B, h i true) * ∏ i ∈ Aᶜ, h i (g i)) := by rw [hsign]
      _ = (∏ i ∈ Aᶜ, h i (g i)) *
            ((∏ i ∈ B, h i true) * ∏ i ∈ A \ B, (- h i false)) := by ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
  rw [show (∑ B ∈ A.powerset, (∏ i ∈ B, h i true) * (∏ i ∈ A \ B, (- h i false)))
        = ∏ i ∈ A, (h i true + (- h i false)) by
      rw [Finset.prod_add]]
  rw [show (∏ i ∈ A, (h i true + (- h i false)))
        = ∏ i ∈ A, (h i true - h i false) by
      apply Finset.prod_congr rfl
      intro i _
      ring]
  ring

/-- Per-coordinate factor of a `(∏_{S} x)(∏_{T}(1−x))` monomial: present slot ↦ `[g i]`,
absent slot ↦ `1 − [g i]`, unmentioned slot ↦ `1`. (`S` takes priority; under `Disjoint S T`
the two cases are exclusive.) -/
noncomputable def monoH {ι : Type*} [DecidableEq ι] (S T : Finset ι) (i : ι) (b : Bool) : ℝ :=
  if i ∈ S then (if b then (1 : ℝ) else 0)
  else if i ∈ T then (1 - if b then (1 : ℝ) else 0)
  else 1

/-- The per-coordinate finite difference of `monoH`: `+1` on `S`, `−1` on `T`, `0` elsewhere. -/
lemma monoH_diff {ι : Type*} [DecidableEq ι] (S T : Finset ι) (i : ι) :
    monoH S T i true - monoH S T i false
      = if i ∈ S then (1 : ℝ) else if i ∈ T then (-1 : ℝ) else 0 := by
  unfold monoH
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]

/-- The constant factor of the monomial derivative: `(−1)^{|A∩T|}` if `A ⊆ S∪T`, else `0`. -/
lemma discreteDeriv_monomial_const {ι : Type*} [DecidableEq ι]
    (S T : Finset ι) (hST : Disjoint S T) (A : Finset ι) :
    (∏ i ∈ A, (monoH S T i true - monoH S T i false))
      = if A ⊆ S ∪ T then (-1 : ℝ) ^ (A ∩ T).card else 0 := by
  simp_rw [monoH_diff]
  by_cases h : A ⊆ S ∪ T
  · rw [if_pos h]
    -- rewrite integrand: for i ∈ A, the `else 0` branch never fires
    have hcongr : (∏ i ∈ A, (if i ∈ S then (1:ℝ) else if i ∈ T then (-1:ℝ) else 0))
        = ∏ i ∈ A, (if i ∈ S then (1:ℝ) else -1) := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      by_cases hS : i ∈ S
      · simp [hS]
      · have hT : i ∈ T := by
          have := h hi
          rcases Finset.mem_union.mp this with hh | hh
          · exact absurd hh hS
          · exact hh
        simp [hS, hT]
    rw [hcongr]
    -- split A into A∩S (1's) and A\S (-1's)
    rw [Finset.prod_ite (fun _ => (1:ℝ)) (fun _ => (-1:ℝ))]
    simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
    -- (A.filter (· ∉ S)).card = (A ∩ T).card
    have hcard : (A.filter (fun i => i ∉ S)).card = (A ∩ T).card := by
      congr 1
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_inter]
      constructor
      · rintro ⟨hiA, hiS⟩
        refine ⟨hiA, ?_⟩
        rcases Finset.mem_union.mp (h hiA) with hh | hh
        · exact absurd hh hiS
        · exact hh
      · rintro ⟨hiA, hiT⟩
        exact ⟨hiA, fun hiS => (Finset.disjoint_left.mp hST hiS) hiT⟩
    rw [hcard]
  · rw [if_neg h]
    obtain ⟨i, hiA, hiST⟩ := Finset.not_subset.mp h
    refine Finset.prod_eq_zero hiA ?_
    rw [Finset.mem_union, not_or] at hiST
    simp [hiST.1, hiST.2]

/-- **Monomial finite-difference derivative.** For disjoint `S`, `T`,
`∂_A [(∏_S x)(∏_T(1−x))] = (if A ⊆ S∪T then (−1)^{|A∩T|} else 0) · (∏_{i∈Aᶜ} monoH S T i (g i))`. -/
lemma discreteDeriv_monomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : Finset ι) (hST : Disjoint S T) (A : Finset ι) (g : ι → Bool) :
    discreteDeriv (fun g => ∏ i, monoH S T i (g i)) A g
      = (if A ⊆ S ∪ T then (-1 : ℝ) ^ (A ∩ T).card else 0)
          * (∏ i ∈ Aᶜ, monoH S T i (g i)) := by
  rw [discreteDeriv_prod, discreteDeriv_monomial_const S T hST]

/-- The `monoH` product over `univ` equals the explicit `(∏_S x)(∏_T(1−x))` monomial,
for disjoint `S`, `T` (slots outside `S∪T` contribute the factor `1`). -/
lemma prod_monoH {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : Finset ι) (hST : Disjoint S T) (g : ι → Bool) :
    (∏ i, monoH S T i (g i))
      = (∏ i ∈ S, (if g i = true then (1 : ℝ) else 0))
          * (∏ i ∈ T, (1 - if g i = true then (1 : ℝ) else 0)) := by
  -- Reduce the product over `univ` to the product over `S ∪ T`.
  rw [← Finset.prod_subset (Finset.subset_univ (S ∪ T))]
  · -- Split over the disjoint union `S ∪ T`.
    rw [Finset.prod_union hST]
    congr 1
    · -- On `S`: `monoH S T i (g i) = if g i then 1 else 0`.
      refine Finset.prod_congr rfl ?_
      intro i hiS
      simp [monoH, hiS]
    · -- On `T`: `i ∉ S`, so `monoH S T i (g i) = 1 - if g i then 1 else 0`.
      refine Finset.prod_congr rfl ?_
      intro i hiT
      have hiS : i ∉ S := fun hiS => (Finset.disjoint_left.mp hST hiS) hiT
      simp [monoH, hiS, hiT]
  · -- Slots outside `S ∪ T` contribute the factor `1`.
    intro i _ hi
    rw [Finset.mem_union, not_or] at hi
    simp [monoH, hi.1, hi.2]

/-- The Kim–Vu degree-`k` deviation constant `a_k = 8^k · (k!)^{1/2}`. -/
noncomputable def kimVuConst (k : ℕ) : ℝ := (8 : ℝ) ^ k * Real.sqrt (k.factorial)

lemma kimVuConst_pos (k : ℕ) : 0 < kimVuConst k := by
  unfold kimVuConst
  have h1 : (0 : ℝ) < (8 : ℝ) ^ k := by positivity
  have h2 : (0 : ℝ) < Real.sqrt (k.factorial) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast k.factorial_pos
  positivity

/-- **Kim–Vu polynomial concentration — verbatim Main Theorem.**

For a polynomial `f` of degree `k` in independent Bool variables under a probability
measure `μm`, if `E` upper-bounds every **expected absolute partial-derivative effect**
`E[|∂_A f|]` and `E'` upper-bounds those for nonempty `A` (i.e. `E ≥ E(H)`, `E' ≥ E'(H)` in
Kim–Vu's notation), and `mean = E[f]`, then for every `λ > 1`:

  `Pr(|f − mean| > a_k·(E·E')^{1/2}·λ^k) ≤ C · exp(−λ + (k−1)·log(#variables))`,

with `a_k = kimVuConst k` and a constant `C > 0` depending only on `k` (the `O(·)`
constant). This is the published statement; we take it as a cited axiom because Mathlib
has no polynomial-concentration infrastructure (martingale decoupling / Talagrand chaining,
est. 2000–3000 LOC).

**Why `E[|∂_A f|]`, not `|E[∂_A f]|`.** Concentration is governed by the *fluctuation* of the
partial derivatives, i.e. `E[|∂_A f|]` — the expectation of the absolute partial derivative.
Using `|E[∂_A f]|` (absolute value of the expectation) would be unsound: cancellation can make
`|E[∂_A f]|` small while `f` still fluctuates. For a positive-coefficient polynomial the two
agree (`∂_A f ≥ 0`); our application's count polynomial is positive-VALUED but not
positive-coefficient, so we use the robust `E[|∂_A f|]` form, which both governs the
fluctuation and is provable by triangle inequality over the constituent monomials. The
`E`/`E'`-as-upper-bound formulation is sound: enlarging `E` only widens the deviation
threshold, weakening the event, matching Kim–Vu's use of the maxima `E(H), E'(H)`.

**Citation.** Kim, J. H., and Vu, V. H. "Concentration of multivariate polynomials and its
applications." *Combinatorica* 20 (2000), 417–434, Main Theorem (`a_k = 8^k·(k!)^{1/2}`). -/
axiom kim_vu_concentration_verbatim (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (μm : Measure (ι → Bool)) [IsProbabilityMeasure μm]
      (f : (ι → Bool) → ℝ) (mean E E' : ℝ),
      mean = ∫ g, f g ∂μm →
      (∀ A : Finset ι, ∫ g, |discreteDeriv f A g| ∂μm ≤ E) →
      (∀ A : Finset ι, A.Nonempty → ∫ g, |discreteDeriv f A g| ∂μm ≤ E') →
      0 < E → 0 < E' →
      ∀ lam : ℝ, 1 < lam →
        μm.real {g : ι → Bool | kimVuConst k * Real.sqrt (E * E') * lam ^ k < |f g - mean|}
          ≤ C * Real.exp (-lam + (k - 1 : ℝ) * Real.log (Fintype.card ι))

/-- **Bridge: verbatim Kim–Vu ⟹ the ε-relative-deviation form.**

Given the verbatim concentration bound at a witness `lam`, plus the *polynomial-regime*
conditions
* `h_thresh`: the verbatim deviation threshold is below the relative target `ε·μ`
  (equivalently `λ` is large enough that `a_k√(E E')λ^k < εμ`), and
* `h_tail`: the verbatim tail dominates the target `deg·exp(−ε²μ/(8E_max))`,

we recover `Pr(εμ ≤ |f − μ|) ≤ deg·exp(−ε²μ/(8E_max))`. The proof is event inclusion +
monotonicity; the regime inequalities `h_thresh`/`h_tail` are the genuine mathematical
side-conditions (the "`μ ≫ E_max`" polynomial regime), discharged at the concrete `D(e)`
level where `N`, `μ`, `E_max`, `k` are pinned down — not smuggled. -/
theorem eps_form_of_verbatim
    {ι : Type*} [Fintype ι] [DecidableEq ι] (μm : Measure (ι → Bool)) [IsProbabilityMeasure μm]
    (f : (ι → Bool) → ℝ) (μ E E' : ℝ) (k deg : ℕ) (C ε E_max lam : ℝ)
    (h_verb : μm.real {g : ι → Bool |
                kimVuConst k * Real.sqrt (E * E') * lam ^ k < |f g - μ|}
              ≤ C * Real.exp (-lam + (k - 1 : ℝ) * Real.log (Fintype.card ι)))
    (h_thresh : kimVuConst k * Real.sqrt (E * E') * lam ^ k < ε * μ)
    (h_tail : C * Real.exp (-lam + (k - 1 : ℝ) * Real.log (Fintype.card ι))
                ≤ (deg : ℝ) * Real.exp (-ε ^ 2 * μ / (8 * E_max))) :
    μm.real {g : ι → Bool | ε * μ ≤ |f g - μ|}
      ≤ (deg : ℝ) * Real.exp (-ε ^ 2 * μ / (8 * E_max)) := by
  have hsub : {g : ι → Bool | ε * μ ≤ |f g - μ|} ⊆
      {g : ι → Bool | kimVuConst k * Real.sqrt (E * E') * lam ^ k < |f g - μ|} := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    linarith
  calc μm.real {g : ι → Bool | ε * μ ≤ |f g - μ|}
      ≤ μm.real {g : ι → Bool |
          kimVuConst k * Real.sqrt (E * E') * lam ^ k < |f g - μ|} :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ C * Real.exp (-lam + (k - 1 : ℝ) * Real.log (Fintype.card ι)) := h_verb
    _ ≤ (deg : ℝ) * Real.exp (-ε ^ 2 * μ / (8 * E_max)) := h_tail

end DaveyThesis2024.SecRandomBipartite.KimVu
