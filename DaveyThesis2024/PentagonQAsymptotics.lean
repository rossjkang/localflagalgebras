import DaveyThesis2024.PentagonQBrrbSurj

/-!
# (a3): the asymptotics

`(a2a)` and `(a2b)` give exact counts with binomial factors `C(Δ−1,4)` and
`C(Δ−2,3)`, against the density normaliser `C(Δ,8)`.  `(a3)` turns those ratios
into the paper's `1680·Δ⁻⁴(1+O(1/Δ))` and `6720·Δ⁻⁵(1+O(1/Δ))`.

This file starts with the **exact** closed forms, as `Nat` identities valid for
`Δ ≥ 8`.  They are exact, not asymptotic, which is worth having: the limit then
follows from a rational function rather than from an estimate.

Per the development notes, the pieces to reuse are
`choose_ratio_tendsto_one` (`LocalFlagAlgebra.lean:5402`) and the `Δ < 8` guards
`choose_eight_pos_of_guard` / `choose_eight_eq_zero_of_lt`
(`PentagonQNonVacuity.lean:218,223`) — the plan lists the `Δ < 8` degeneracy as
work to do, and it is already handled.
-/

namespace Davey2024
namespace PentagonQAsymptotics

/-- **`(a2a)`'s binomial ratio, exactly.**
`C(Δ−1,4) / C(Δ,8) = 1680 / (Δ(Δ−5)(Δ−6)(Δ−7))`, cleared of denominators. -/
theorem choose_ratio_tau1 {Δ : ℕ} (h : 8 ≤ Δ) :
    Nat.choose (Δ - 1) 4 * (Δ * ((Δ - 5) * ((Δ - 6) * (Δ - 7))))
      = 1680 * Nat.choose Δ 8 := by
  obtain ⟨n, rfl⟩ : ∃ n, Δ = n + 8 := ⟨Δ - 8, by omega⟩
  rw [show n + 8 - 1 = n + 7 from by omega, show n + 8 - 5 = n + 3 from by omega,
    show n + 8 - 6 = n + 2 from by omega, show n + 8 - 7 = n + 1 from by omega]
  apply Nat.eq_of_mul_eq_mul_right (show 0 < 40320 by norm_num)
  have h4 : Nat.descFactorial (n + 7) 4 = 24 * Nat.choose (n + 7) 4 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; norm_num [Nat.factorial]
  have h8 : Nat.descFactorial (n + 8) 8 = 40320 * Nat.choose (n + 8) 8 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; norm_num [Nat.factorial]
  have key : Nat.descFactorial (n + 7) 4 * ((n + 8) * ((n + 3) * ((n + 2) * (n + 1))))
      = Nat.descFactorial (n + 8) 8 := by
    simp only [Nat.descFactorial, Nat.sub_zero, Nat.mul_one,
      show n + 7 - 1 = n + 6 from by omega, show n + 7 - 2 = n + 5 from by omega,
      show n + 7 - 3 = n + 4 from by omega,
      show n + 8 - 1 = n + 7 from by omega, show n + 8 - 2 = n + 6 from by omega,
      show n + 8 - 3 = n + 5 from by omega, show n + 8 - 4 = n + 4 from by omega,
      show n + 8 - 5 = n + 3 from by omega, show n + 8 - 6 = n + 2 from by omega,
      show n + 8 - 7 = n + 1 from by omega]
    ring
  rw [h4, h8] at key
  nlinarith [key]

/-- **`(a2b)`'s binomial ratio, exactly.**
`C(Δ−2,3) / C(Δ,8) = 6720 / (Δ(Δ−1)(Δ−5)(Δ−6)(Δ−7))`, cleared of denominators. -/
theorem choose_ratio_tau23 {Δ : ℕ} (h : 8 ≤ Δ) :
    Nat.choose (Δ - 2) 3 * (Δ * ((Δ - 1) * ((Δ - 5) * ((Δ - 6) * (Δ - 7)))))
      = 6720 * Nat.choose Δ 8 := by
  obtain ⟨n, rfl⟩ : ∃ n, Δ = n + 8 := ⟨Δ - 8, by omega⟩
  rw [show n + 8 - 2 = n + 6 from by omega, show n + 8 - 1 = n + 7 from by omega,
    show n + 8 - 5 = n + 3 from by omega, show n + 8 - 6 = n + 2 from by omega,
    show n + 8 - 7 = n + 1 from by omega]
  apply Nat.eq_of_mul_eq_mul_right (show 0 < 40320 by norm_num)
  have h3 : Nat.descFactorial (n + 6) 3 = 6 * Nat.choose (n + 6) 3 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; norm_num [Nat.factorial]
  have h8 : Nat.descFactorial (n + 8) 8 = 40320 * Nat.choose (n + 8) 8 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; norm_num [Nat.factorial]
  have key : Nat.descFactorial (n + 6) 3 *
      ((n + 8) * ((n + 7) * ((n + 3) * ((n + 2) * (n + 1)))))
      = Nat.descFactorial (n + 8) 8 := by
    simp only [Nat.descFactorial, Nat.sub_zero, Nat.mul_one,
      show n + 6 - 1 = n + 5 from by omega, show n + 6 - 2 = n + 4 from by omega,
      show n + 8 - 1 = n + 7 from by omega, show n + 8 - 2 = n + 6 from by omega,
      show n + 8 - 3 = n + 5 from by omega, show n + 8 - 4 = n + 4 from by omega,
      show n + 8 - 5 = n + 3 from by omega, show n + 8 - 6 = n + 2 from by omega,
      show n + 8 - 7 = n + 1 from by omega]
    ring
  rw [h3, h8] at key
  nlinarith [key]

/-! ## The limits

The closed forms are exact rational functions, so the limit is a quotient of
polynomials — no estimate is needed.  `1 − c/Δ → 1` is the only analytic input. -/

open Filter in
/-- `1 − c/Δ → 1`. -/
theorem tendsto_one_sub_div (c : ℕ) :
    Tendsto (fun Δ : ℕ => 1 - (c : ℝ) / (Δ : ℝ)) atTop (nhds 1) := by
  have h := tendsto_const_div_atTop_nhds_zero_nat (c : ℝ)
  simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub h

open Filter in
/-- `Δ⁴ / (Δ(Δ−5)(Δ−6)(Δ−7)) → 1`. -/
theorem tendsto_pow4_div : Tendsto
    (fun Δ : ℕ => ((Δ : ℝ) ^ 4) / ((Δ : ℝ) * (((Δ : ℝ) - 5) * (((Δ : ℝ) - 6) * ((Δ : ℝ) - 7)))))
    atTop (nhds 1) := by
  have hprod : Tendsto
      (fun Δ : ℕ => (1 - (5 : ℝ) / (Δ : ℝ)) * ((1 - (6 : ℝ) / (Δ : ℝ)) * (1 - (7 : ℝ) / (Δ : ℝ))))
      atTop (nhds 1) := by
    simpa using (tendsto_one_sub_div 5).mul ((tendsto_one_sub_div 6).mul (tendsto_one_sub_div 7))
  have hinv := hprod.inv₀ (by norm_num)
  rw [inv_one] at hinv
  refine hinv.congr' ?_
  filter_upwards [eventually_ge_atTop 8] with Δ hΔ
  have hD : (8 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have h0 : (Δ : ℝ) ≠ 0 := by linarith
  have h5 : (Δ : ℝ) - 5 ≠ 0 := by linarith
  have h6 : (Δ : ℝ) - 6 ≠ 0 := by linarith
  have h7 : (Δ : ℝ) - 7 ≠ 0 := by linarith
  field_simp

open Filter in
/-- `Δ⁵ / (Δ(Δ−1)(Δ−5)(Δ−6)(Δ−7)) → 1`. -/
theorem tendsto_pow5_div : Tendsto
    (fun Δ : ℕ => ((Δ : ℝ) ^ 5) /
      ((Δ : ℝ) * (((Δ : ℝ) - 1) * (((Δ : ℝ) - 5) * (((Δ : ℝ) - 6) * ((Δ : ℝ) - 7))))))
    atTop (nhds 1) := by
  have hprod : Tendsto
      (fun Δ : ℕ => (1 - (1 : ℝ) / (Δ : ℝ)) * ((1 - (5 : ℝ) / (Δ : ℝ)) *
        ((1 - (6 : ℝ) / (Δ : ℝ)) * (1 - (7 : ℝ) / (Δ : ℝ)))))
      atTop (nhds 1) := by
    simpa using (tendsto_one_sub_div 1).mul ((tendsto_one_sub_div 5).mul
      ((tendsto_one_sub_div 6).mul (tendsto_one_sub_div 7)))
  have hinv := hprod.inv₀ (by norm_num)
  rw [inv_one] at hinv
  refine hinv.congr' ?_
  filter_upwards [eventually_ge_atTop 8] with Δ hΔ
  have hD : (8 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have h0 : (Δ : ℝ) ≠ 0 := by linarith
  have h1 : (Δ : ℝ) - 1 ≠ 0 := by linarith
  have h5 : (Δ : ℝ) - 5 ≠ 0 := by linarith
  have h6 : (Δ : ℝ) - 6 ≠ 0 := by linarith
  have h7 : (Δ : ℝ) - 7 ≠ 0 := by linarith
  field_simp

/-! ## The two constants -/

/-- The τ₁ ratio over `ℝ`.  `C(Δ,8) ≠ 0` is `Nat.choose_pos` — which is exactly
what `PentagonQNonVacuity.choose_eight_pos_of_guard` wraps; used directly here
rather than taking an import edge for a one-line alias. -/
theorem ratio_tau1_real {Δ : ℕ} (h : 8 ≤ Δ) :
    (Nat.choose (Δ - 1) 4 : ℝ) / (Nat.choose Δ 8 : ℝ)
      = 1680 / ((Δ : ℝ) * (((Δ : ℝ) - 5) * (((Δ : ℝ) - 6) * ((Δ : ℝ) - 7)))) := by
  have hc : (0 : ℝ) < (Nat.choose Δ 8 : ℝ) := by exact_mod_cast Nat.choose_pos h
  have hD : (8 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast h
  have hp : (0 : ℝ) < (Δ : ℝ) * (((Δ : ℝ) - 5) * (((Δ : ℝ) - 6) * ((Δ : ℝ) - 7))) :=
    mul_pos (by linarith) (mul_pos (by linarith) (mul_pos (by linarith) (by linarith)))
  rw [div_eq_div_iff hc.ne' hp.ne',
    show ((Δ : ℝ) - 5) = ((Δ - 5 : ℕ) : ℝ) from by
      rw [Nat.cast_sub (by omega : 5 ≤ Δ)]; norm_num,
    show ((Δ : ℝ) - 6) = ((Δ - 6 : ℕ) : ℝ) from by
      rw [Nat.cast_sub (by omega : 6 ≤ Δ)]; norm_num,
    show ((Δ : ℝ) - 7) = ((Δ - 7 : ℕ) : ℝ) from by
      rw [Nat.cast_sub (by omega : 7 ≤ Δ)]; norm_num]
  exact_mod_cast choose_ratio_tau1 h

/-- The τ₂/τ₃ ratio over `ℝ`. -/
theorem ratio_tau23_real {Δ : ℕ} (h : 8 ≤ Δ) :
    (Nat.choose (Δ - 2) 3 : ℝ) / (Nat.choose Δ 8 : ℝ)
      = 6720 / ((Δ : ℝ) * (((Δ : ℝ) - 1) *
          (((Δ : ℝ) - 5) * (((Δ : ℝ) - 6) * ((Δ : ℝ) - 7))))) := by
  have hc : (0 : ℝ) < (Nat.choose Δ 8 : ℝ) := by exact_mod_cast Nat.choose_pos h
  have hD : (8 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast h
  have hp : (0 : ℝ) < (Δ : ℝ) * (((Δ : ℝ) - 1) *
      (((Δ : ℝ) - 5) * (((Δ : ℝ) - 6) * ((Δ : ℝ) - 7)))) :=
    mul_pos (by linarith) (mul_pos (by linarith)
      (mul_pos (by linarith) (mul_pos (by linarith) (by linarith))))
  rw [div_eq_div_iff hc.ne' hp.ne',
    show ((Δ : ℝ) - 1) = ((Δ - 1 : ℕ) : ℝ) from by
      rw [Nat.cast_sub (by omega : 1 ≤ Δ)]; norm_num,
    show ((Δ : ℝ) - 5) = ((Δ - 5 : ℕ) : ℝ) from by
      rw [Nat.cast_sub (by omega : 5 ≤ Δ)]; norm_num,
    show ((Δ : ℝ) - 6) = ((Δ - 6 : ℕ) : ℝ) from by
      rw [Nat.cast_sub (by omega : 6 ≤ Δ)]; norm_num,
    show ((Δ : ℝ) - 7) = ((Δ - 7 : ℕ) : ℝ) from by
      rw [Nat.cast_sub (by omega : 7 ≤ Δ)]; norm_num]
  exact_mod_cast choose_ratio_tau23 h

open Filter in
/-- **`(a3)` for `(a2a)`.**  `Δ⁴ · C(Δ−1,4)/C(Δ,8) → 1680`. -/
theorem tendsto_tau1_const : Tendsto
    (fun Δ : ℕ => (Δ : ℝ) ^ 4 * ((Nat.choose (Δ - 1) 4 : ℝ) / (Nat.choose Δ 8 : ℝ)))
    atTop (nhds 1680) := by
  have h := tendsto_pow4_div.const_mul (1680 : ℝ)
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 8] with Δ hΔ
  rw [ratio_tau1_real hΔ]
  have hD : (8 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have hp : ((Δ : ℝ) * (((Δ : ℝ) - 5) * (((Δ : ℝ) - 6) * ((Δ : ℝ) - 7)))) ≠ 0 :=
    (mul_pos (by linarith) (mul_pos (by linarith)
      (mul_pos (by linarith) (by linarith)))).ne'
  field_simp

open Filter in
/-- **`(a3)` for `(a2b)`.**  `Δ⁵ · C(Δ−2,3)/C(Δ,8) → 6720`. -/
theorem tendsto_tau23_const : Tendsto
    (fun Δ : ℕ => (Δ : ℝ) ^ 5 * ((Nat.choose (Δ - 2) 3 : ℝ) / (Nat.choose Δ 8 : ℝ)))
    atTop (nhds 6720) := by
  have h := tendsto_pow5_div.const_mul (6720 : ℝ)
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 8] with Δ hΔ
  rw [ratio_tau23_real hΔ]
  have hD : (8 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have hp : ((Δ : ℝ) * (((Δ : ℝ) - 1) *
      (((Δ : ℝ) - 5) * (((Δ : ℝ) - 6) * ((Δ : ℝ) - 7))))) ≠ 0 :=
    (mul_pos (by linarith) (mul_pos (by linarith)
      (mul_pos (by linarith) (mul_pos (by linarith) (by linarith))))).ne'
  field_simp

/-! ## The absorption

The target is
`2·pentagonQ/Δ⁵ − Σⱼ coefⱼ·ρ(Fⱼ;G') → 0`.  Feeding `(a2a)`, `(a2b)` and the
pentagon-visit identity into `(a1)` turns the flag side into

```
(8/6720)·P(G,v)·[C(Δ−1,4)/C(Δ,8)]  +  (2/6720)·Σ_{u∼v}P(G,u)·[C(Δ−2,3)/C(Δ,8)]
```

and the two constants reconcile **exactly**: `(8/6720)·1680 = 2` and
`(2/6720)·6720 = 2`, which is what `2·pentagonQ/Δ⁵ = 2P/Δ⁴ + 2ΣP/Δ⁵` needs.  The
difference is then

```
(P/Δ⁴)·[2 − (8/6720)·Δ⁴R₁]  +  (ΣP/Δ⁵)·[2 − (2/6720)·Δ⁵R₂]
```

— a **bounded** factor times a factor tending to zero.  `P(G,v) ≤ Δ⁴` is
`pentagonCountAt_le_degree_pow` (`PentagonConjecture.lean:16033`), already in the
repository. -/

open Filter in
/-- Bounded times null is null.  The absorption's only analytic content. -/
theorem tendsto_zero_of_bounded_mul {f g : ℕ → ℝ} (hf : ∀ k, |f k| ≤ 1)
    (hg : Tendsto g atTop (nhds 0)) :
    Tendsto (fun k => f k * g k) atTop (nhds 0) := by
  refine squeeze_zero_norm (fun k => ?_) (by simpa using hg.abs)
  calc ‖f k * g k‖ = |f k| * |g k| := by rw [Real.norm_eq_abs, abs_mul]
    _ ≤ 1 * |g k| := mul_le_mul_of_nonneg_right (hf k) (abs_nonneg _)
    _ = |g k| := one_mul _

open Filter in
/-- The `τ₁` bracket tends to zero: `2 − (8/6720)·Δ⁴·C(Δ−1,4)/C(Δ,8) → 0`. -/
theorem tendsto_bracket_tau1 : Tendsto
    (fun Δ : ℕ => 2 - (8 / 6720 : ℝ) *
      ((Δ : ℝ) ^ 4 * ((Nat.choose (Δ - 1) 4 : ℝ) / (Nat.choose Δ 8 : ℝ))))
    atTop (nhds 0) := by
  have h := (tendsto_tau1_const.const_mul (8 / 6720 : ℝ))
  have : (8 / 6720 : ℝ) * 1680 = 2 := by norm_num
  rw [this] at h
  simpa using (tendsto_const_nhds (x := (2 : ℝ)) (f := atTop)).sub h

open Filter in
/-- The `τ₂/τ₃` bracket tends to zero: `2 − (2/6720)·Δ⁵·C(Δ−2,3)/C(Δ,8) → 0`. -/
theorem tendsto_bracket_tau23 : Tendsto
    (fun Δ : ℕ => 2 - (2 / 6720 : ℝ) *
      ((Δ : ℝ) ^ 5 * ((Nat.choose (Δ - 2) 3 : ℝ) / (Nat.choose Δ 8 : ℝ))))
    atTop (nhds 0) := by
  have h := (tendsto_tau23_const.const_mul (2 / 6720 : ℝ))
  have : (2 / 6720 : ℝ) * 6720 = 2 := by norm_num
  rw [this] at h
  simpa using (tendsto_const_nhds (x := (2 : ℝ)) (f := atTop)).sub h

/-! ## Transport to a degree sequence

The target axiom is stated over a `StrictMono` degree sequence, not over `Δ`
directly.  `StrictMono.tendsto_atTop` moves the limits across — the idiom the
repository already uses at `PentagonQBridge.lean:9740`.

This also disposes of the `Δ < 8` terms the plan flags: nothing here needs them
excluded, because the bracket limits are `atTop` statements and `StrictMono`
sends the index to infinity.  The degenerate terms are simply not eventually
present. -/

open Filter in
/-- The `τ₁` bracket along a strictly increasing degree sequence. -/
theorem tendsto_bracket_tau1_seq {Δseq : ℕ → ℕ} (hmono : StrictMono Δseq) :
    Tendsto
      (fun k => 2 - (8 / 6720 : ℝ) *
        ((Δseq k : ℝ) ^ 4 *
          ((Nat.choose (Δseq k - 1) 4 : ℝ) / (Nat.choose (Δseq k) 8 : ℝ))))
      atTop (nhds 0) :=
  tendsto_bracket_tau1.comp hmono.tendsto_atTop

open Filter in
/-- The `τ₂/τ₃` bracket along a strictly increasing degree sequence. -/
theorem tendsto_bracket_tau23_seq {Δseq : ℕ → ℕ} (hmono : StrictMono Δseq) :
    Tendsto
      (fun k => 2 - (2 / 6720 : ℝ) *
        ((Δseq k : ℝ) ^ 5 *
          ((Nat.choose (Δseq k - 2) 3 : ℝ) / (Nat.choose (Δseq k) 8 : ℝ))))
      atTop (nhds 0) :=
  tendsto_bracket_tau23.comp hmono.tendsto_atTop

open Filter in
/-- **The absorption, assembled.**  A sum of two bounded-times-null terms is
null — the shape the target difference takes once `(a1)`–`(a2b)` have rewritten
the flag side. -/
theorem tendsto_absorption {f₁ f₂ g₁ g₂ : ℕ → ℝ}
    (hf₁ : ∀ k, |f₁ k| ≤ 1) (hf₂ : ∀ k, |f₂ k| ≤ 1)
    (hg₁ : Tendsto g₁ atTop (nhds 0)) (hg₂ : Tendsto g₂ atTop (nhds 0)) :
    Tendsto (fun k => f₁ k * g₁ k + f₂ k * g₂ k) atTop (nhds 0) := by
  simpa using (tendsto_zero_of_bounded_mul hf₁ hg₁).add
    (tendsto_zero_of_bounded_mul hf₂ hg₂)

/-! ## Bridging to `μ`

`(a2a)` and `(a2b)` are stated at `brrbGenFlag` and `pentFlag`; `muG` is stated at
`tauFlag`.  The flags are equal but **not definitionally**, and `rw` cannot move
between them: abstracting the flag breaks the root's type, so the motive is
ill-formed.  A `subst`-based congruence sidesteps that — the sizes *are*
definitionally equal, so the two roots are the same term up to `Fin.ext`. -/

open Davey2024.PentagonQMuFlag Davey2024.PentagonQWeights
  Davey2024.PentagonQBrrbSurj Davey2024.PentagonQIsoInvariance in
/-- Transport `rootedCountG` across an equality of source flags.
See [[feedback_dependent_subst_helper_pattern]]: promoted to a standalone helper
precisely because `rw` fails on the motive. -/
theorem rootedCountG_congr {F F' G : GenFlag CG2 (GenFlagType.empty CG2)}
    (h : F = F') (r : Fin F.size) (r' : Fin F'.size) (hr : r.val = r'.val) :
    rootedCountG F G r = rootedCountG F' G r' := by
  subst h
  congr 1
  exact Fin.ext hr

open Davey2024.PentagonQMuFlag Davey2024.PentagonQWeights
  Davey2024.PentagonQIsoInvariance Finset in
/-- `Σ μ` splits into the three rooted counts, by linearity. -/
theorem sum_muG_decompose {n : ℕ} (T : Finset (Finset (Fin n)))
    (H : Finset (Fin n) → GenFlag CG2 (GenFlagType.empty CG2)) :
    (T.sum fun S => muG (H S))
      = 4 * (T.sum fun S => rootedCountG (tauFlag tau1 4) (H S)
              ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩)
        + (T.sum fun S => rootedCountG (tauFlag tau2 5) (H S)
              ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩)
        + 2 * (T.sum fun S => rootedCountG (tauFlag tau3 5) (H S)
              ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩) := by
  unfold muG
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

open Davey2024.PentagonQMuFlag Davey2024.PentagonQWeights
  Davey2024.PentagonQBrrbSurj Davey2024.PentagonQIsoInvariance Finset in
open Classical in
/-- **The μ-sum in closed form.**  `(a2a)` + `(a2b)` + the pentagon-visit
identity, substituted into the decomposition:

```
Σ_{|S|=8} μ(G'[S]) = 8·P(G,v)·C(Δ−1,4) + 2·C(Δ−2,3)·Σ_{u∼v}P(G,u)
```
-/
theorem sum_muG_host_closed (G : Flag emptyType) (v : Fin G.size)
    (htf : IsTriangleFree G) (hreg : IsRegular G) :
    ((Finset.univ.filter
        (fun S : Finset (Fin (vColouredClass G v htf hreg).graph.size) => S.card = 8)).sum
        fun S => muG ((vColouredClass G v htf hreg).toGenFlag.genInducedSubflag S
          (fun i => i.elim0) (Nat.zero_le _)))
      = 8 * pentagonCountAt G v * Nat.choose (maxDegree G - 1) 4
        + 2 * Nat.choose (maxDegree G - 2) 3 *
            ((blackSet (vColouredClass G v htf hreg)).sum
              fun u => pentagonCountAt G u) := by
  rw [sum_muG_decompose]
  -- move each rooted count onto the flag its (a2) lemma is stated at
  have c1 : ∀ S : Finset (Fin (vColouredClass G v htf hreg).graph.size),
      rootedCountG (tauFlag tau1 4)
          ((vColouredClass G v htf hreg).toGenFlag.genInducedSubflag S
            (fun i => i.elim0) (Nat.zero_le _))
          ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩
        = rootedCountG brrbGenFlag
          ((vColouredClass G v htf hreg).toGenFlag.genInducedSubflag S
            (fun i => i.elim0) (Nat.zero_le _)) brrbRoot :=
    fun S => rootedCountG_congr tauFlag_tau1_eq_brrbGenFlag _ _ rfl
  have c2 : ∀ S : Finset (Fin (vColouredClass G v htf hreg).graph.size),
      rootedCountG (tauFlag tau2 5)
          ((vColouredClass G v htf hreg).toGenFlag.genInducedSubflag S
            (fun i => i.elim0) (Nat.zero_le _))
          ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩
        = rootedCountG sdpFlag56
          ((vColouredClass G v htf hreg).toGenFlag.genInducedSubflag S
            (fun i => i.elim0) (Nat.zero_le _)) (pidx 0) :=
    fun S => rootedCountG_congr tauFlag_tau2_eq_sdpFlag56 _ _ rfl
  have c3 : ∀ S : Finset (Fin (vColouredClass G v htf hreg).graph.size),
      rootedCountG (tauFlag tau3 5)
          ((vColouredClass G v htf hreg).toGenFlag.genInducedSubflag S
            (fun i => i.elim0) (Nat.zero_le _))
          ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩
        = rootedCountG pentagonTwoBlack
          ((vColouredClass G v htf hreg).toGenFlag.genInducedSubflag S
            (fun i => i.elim0) (Nat.zero_le _)) (pidx 0) :=
    fun S => rootedCountG_congr tauFlag_tau3_eq_pentagonTwoBlack _ _ rfl
  rw [Finset.sum_congr rfl (fun S _ => c1 S), Finset.sum_congr rfl (fun S _ => c2 S),
    Finset.sum_congr rfl (fun S _ => c3 S)]
  have e1 := sum_n1_eq_two_mul_pentagon G v htf hreg
  have e2 := sum_n2_eq_two_mul_copies (vColouredClass G v htf hreg)
  have e3 := sum_n3_eq_two_mul_copies (vColouredClass G v htf hreg)
  have hv := pentagon_visit_identity (vColouredClass G v htf hreg)
  rw [e1, e2, e3]
  simp only [vColouredClass_graph] at hv ⊢
  rw [← hv]
  ring

open Davey2024.PentagonQBrrbSurj Finset in
open Classical in
/-- `Σ_{u∼v} P(G,u) ≤ Δ⁵`.  The black set *is* `N(v)`, and `blackCount` gives it
exactly `Δ` members, each contributing at most `Δ⁴`. -/
theorem sum_black_pentagonCount_le (C : ColouredGraphClass) :
    ((blackSet C).sum fun u => (pentagonCountAt C.graph u : ℝ))
      ≤ (maxDegree C.graph : ℝ) ^ 5 := by
  have hcard : (blackSet C).card = maxDegree C.graph := C.blackCount
  have hterm : ∀ u ∈ blackSet C,
      (pentagonCountAt C.graph u : ℝ) ≤ (maxDegree C.graph : ℝ) ^ 4 :=
    fun u _ => pentagonCountAt_le_degree_pow C.graph u C.triangleFree
  calc ((blackSet C).sum fun u => (pentagonCountAt C.graph u : ℝ))
      ≤ ((blackSet C).card : ℝ) * (maxDegree C.graph : ℝ) ^ 4 := by
        simpa using Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (maxDegree C.graph : ℝ) ^ 5 := by rw [hcard]; ring

open Davey2024.PentagonQBrrbSurj in
/-- `P(G,v)/Δ⁴ ∈ [0,1]`, the first bounded factor of the absorption. -/
theorem abs_pentagon_div_le_one (G : Flag emptyType) (v : Fin G.size)
    (htf : IsTriangleFree G) (hΔ : 0 < maxDegree G) :
    |(pentagonCountAt G v : ℝ) / (maxDegree G : ℝ) ^ 4| ≤ 1 := by
  have hD : (0 : ℝ) < (maxDegree G : ℝ) := by exact_mod_cast hΔ
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (maxDegree G : ℝ) ^ 4)]
  rw [div_le_one (by positivity)]
  exact pentagonCountAt_le_degree_pow G v htf

open Davey2024.PentagonQBrrbSurj in
/-- `Σ_{u∼v}P(G,u)/Δ⁵ ∈ [0,1]`, the second bounded factor. -/
theorem abs_sum_black_div_le_one (C : ColouredGraphClass) (hΔ : 0 < maxDegree C.graph) :
    |((blackSet C).sum fun u => (pentagonCountAt C.graph u : ℝ)) /
      (maxDegree C.graph : ℝ) ^ 5| ≤ 1 := by
  have hD : (0 : ℝ) < (maxDegree C.graph : ℝ) := by exact_mod_cast hΔ
  have hnn : (0 : ℝ) ≤ ((blackSet C).sum fun u => (pentagonCountAt C.graph u : ℝ)) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  rw [abs_div, abs_of_nonneg hnn,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (maxDegree C.graph : ℝ) ^ 5),
    div_le_one (by positivity)]
  exact sum_black_pentagonCount_le C

open Davey2024.PentagonQBrrbSurj Finset in
open Classical in
/-- The black set of the `v`-colouring **is** `N(v)` — so the flag side's sum and
`pentagonQ`'s neighbour sum are the same object. -/
theorem blackSet_vColouredClass (G : Flag emptyType) (v : Fin G.size)
    (htf : IsTriangleFree G) (hreg : IsRegular G) :
    blackSet (vColouredClass G v htf hreg)
      = Finset.univ.filter (fun u => G.graph.Adj v u) := by
  ext u
  simp only [blackSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => vColouring_eq_one.mp h, fun h => vColouring_eq_one.mpr h⟩

open Davey2024.PentagonQBrrbSurj in
open Classical in
/-- The black-set sum **is** `pentagonQ` minus its first term.  Proved here, in
isolation, because the two neighbour sums carry different `Decidable` instances:
`ring` sees distinct atoms and prints the goal as `X = X`.  `ring_nf` normalises
them; in a larger goal it does not, which is why this is factored out. -/
theorem blackSet_sum_eq_pentagonQ_sub (G : Flag emptyType) (v : Fin G.size)
    (htf : IsTriangleFree G) (hreg : IsRegular G) :
    ((blackSet (vColouredClass G v htf hreg)).sum fun u => (pentagonCountAt G u : ℝ))
      = pentagonQ G v - (maxDegree G : ℝ) * (pentagonCountAt G v : ℝ) := by
  unfold pentagonQ
  rw [blackSet_vColouredClass]
  ring_nf
  rfl

#print axioms blackSet_sum_eq_pentagonQ_sub
#print axioms blackSet_vColouredClass
#print axioms sum_black_pentagonCount_le
#print axioms abs_pentagon_div_le_one
#print axioms abs_sum_black_div_le_one
#print axioms sum_muG_host_closed
#print axioms rootedCountG_congr
#print axioms sum_muG_decompose
#print axioms tendsto_bracket_tau1_seq
#print axioms tendsto_bracket_tau23_seq
#print axioms tendsto_absorption
open Filter in
/-- Eventually-bounded times null is null.  The `∀ k` form is not usable at the
target: `P/Δ⁴` needs `Δ > 0`, which holds only eventually along the sequence. -/
theorem tendsto_zero_of_eventually_bounded_mul {f g : ℕ → ℝ}
    (hf : ∀ᶠ k in atTop, |f k| ≤ 1) (hg : Tendsto g atTop (nhds 0)) :
    Tendsto (fun k => f k * g k) atTop (nhds 0) := by
  refine squeeze_zero_norm' ?_ (by simpa using hg.abs)
  filter_upwards [hf] with k hk
  calc ‖f k * g k‖ = |f k| * |g k| := by rw [Real.norm_eq_abs, abs_mul]
    _ ≤ 1 * |g k| := mul_le_mul_of_nonneg_right hk (abs_nonneg _)
    _ = |g k| := one_mul _

open Filter in
/-- The absorption, with eventual bounds. -/
theorem tendsto_absorption' {f₁ f₂ g₁ g₂ : ℕ → ℝ}
    (hf₁ : ∀ᶠ k in atTop, |f₁ k| ≤ 1) (hf₂ : ∀ᶠ k in atTop, |f₂ k| ≤ 1)
    (hg₁ : Tendsto g₁ atTop (nhds 0)) (hg₂ : Tendsto g₂ atTop (nhds 0)) :
    Tendsto (fun k => f₁ k * g₁ k + f₂ k * g₂ k) atTop (nhds 0) := by
  simpa using (tendsto_zero_of_eventually_bounded_mul hf₁ hg₁).add
    (tendsto_zero_of_eventually_bounded_mul hf₂ hg₂)

#print axioms tendsto_zero_of_eventually_bounded_mul
#print axioms tendsto_absorption'
#print axioms tendsto_zero_of_bounded_mul
#print axioms tendsto_bracket_tau1
#print axioms tendsto_bracket_tau23
#print axioms tendsto_tau1_const
#print axioms tendsto_tau23_const
#print axioms ratio_tau1_real
#print axioms ratio_tau23_real
#print axioms tendsto_one_sub_div
#print axioms tendsto_pow4_div
#print axioms tendsto_pow5_div
#print axioms choose_ratio_tau1
#print axioms choose_ratio_tau23

end PentagonQAsymptotics
end Davey2024
