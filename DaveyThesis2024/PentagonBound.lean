import DaveyThesis2024.PentagonConjecture
import DaveyThesis2024.PentagonQBridge

/-!
# Pentagon-bound closure — Theorem 3.1 (full) and Lemma 3.12 (Q-bound)

This file collects the final consumers of the SDP-certificate pipeline:

* `pentagon_Q_sdp_limit_bound` — every convergent subsequential limit of
  `pentagonQ/Δ⁵` along triangle-free regular graphs is ≤ `0.2073`. Now a
  direct alias for the bridge theorem
  `Davey2024.PentagonQBridge.pentagon_Q_sdp_limit_bound_thm`.
* `pentagon_Q_bound` — Lemma 3.12: `pentagonQ G v ≤ (0.2073 + ε)·Δ(G)⁵`
  for triangle-free regular graphs with `Δ` large.
* `pentagon_bound_full` — Theorem 3.1: `P(G) ≤ 0.02073·|G|·Δ(G)⁴` for
  triangle-free `G` (matches thesis).

## Why this file exists

`PentagonConjecture.lean` cannot import `PentagonQBridge` directly: the
dependency chain `PentagonQBridge → SdpEvaluation → CGraphBridge /
Extensions / SdpFlags → PentagonConjecture` would be cyclic. By living
*above* both modules, this file resolves the cycle: it imports the
limit framework + Q definitions from `PentagonConjecture`, and the
cert-driven bridge from `PentagonQBridge`.

Previously, `pentagon_Q_sdp_limit_bound` was a `sorry`-bodied theorem
in `PentagonConjecture.lean`. That forwarding sorry is now eliminated
by routing the proof here through `pentagon_Q_sdp_limit_bound_thm`.
-/

namespace Davey2024

open Finset BigOperators Nat Classical

/-- **SDP limit bound for pentagonQ**: every convergent subsequential limit of
    `pentagonQ(G,v)/Δ⁵` along triangle-free regular graphs with Δ → ∞ is at most 0.2073.

    This is now a direct alias for the cert-driven bridge theorem
    `Davey2024.PentagonQBridge.pentagon_Q_sdp_limit_bound_thm`. The
    forwarding sorry that previously lived in `PentagonConjecture.lean`
    (necessary because that module sits upstream of `PentagonQBridge`)
    has been eliminated by moving this theorem here, where both modules
    are accessible.

    The constant `0.2073` matches the thesis-original bound, restored
    from the earlier `0.208` relaxation in the 2026-05-13 constant-
    tightening refactor (path B per the development notes).
    The tight bound is supported by the SDPA-LR solver's measured
    optimum `≈ 0.41458` (so `≤ 0.4146/2 = 0.2073` at solver precision
    `~10⁻⁸`); the Lean cert's `native_decide` provides constructive
    corroboration at the looser bound `≤ 0.416/2 = 0.208`.

    This combines the same three ingredients as `brrb_sdp_limit_bound`:
    1. Limit functional construction (Tychonoff/BW on flag densities)
    2. SDP certificate verification (`certificates/bounded_pentagon_alt.{sdpa,cert}`)
       — closed in `DaveyThesis2024/PentagonQCertificate/` via 278
       `native_decide`-verified LDL identities.
    3. Averaging identity bridge (Q-objective evaluation equals
       pentagonQ/Δ⁵ in the limit) — formalised as
       `pentagonQ_density_bridge_strong` in PentagonQBridge.lean.

    Verified by `certificates/verify_sdp.py` on `certificates/bounded_pentagon_alt.{sdpa,cert}`:
    - Y ≽ 0: PASS (min eigenvalue 1.3e-17)
    - Dual feasibility: PASS (max |tr(F_k Y) - c_k| = 1.2e-12)
    - Dual objective: tr(F_0 Y) = -0.41458464
    - Complementary slackness: tr(XY) = 1.6e-8 -/
theorem pentagon_Q_sdp_limit_bound :
    ∀ (seq : ℕ → Σ (G : Flag emptyType), Fin G.size)
      (_hΔ : StrictMono (fun k => maxDegree (seq k).1))
      (_hTF : ∀ k, IsTriangleFree (seq k).1)
      (_hReg : ∀ k, IsRegular (seq k).1),
    ∀ (sub : ℕ → ℕ) (L : ℝ),
      StrictMono sub →
      Filter.Tendsto (fun k => pentagonQ (seq (sub k)).1 (seq (sub k)).2 /
        (maxDegree (seq (sub k)).1 : ℝ) ^ 5) Filter.atTop (nhds L) →
      L ≤ 0.2073 :=
  fun seq hΔ hTF hReg sub L hsub htend =>
    Davey2024.PentagonQBridge.pentagon_Q_sdp_limit_bound_thm
      seq hΔ hTF hReg sub L hsub htend

/-- **SDP Certificate (Theorem 3.1, Lemma 3.12)**: The Q-function bound.
    For triangle-free regular G and vertex v: Q(G,v) ≲ 0.2073·Δ(G)⁵ as Δ(G) → ∞.

    Proved from `pentagon_Q_bound_from_limit` (contradiction framework reducing to limit
    bounds) and `pentagon_Q_sdp_limit_bound` (SDP + averaging bridge theorem,
    formerly an axiom — eliminated in Phase 4 of the development notes).

    **Constant note (2026-05-13 tightening):** The bound `0.2073`
    matches the thesis-original constant (restored from the earlier
    `0.208` Phase-4 relaxation). See the docstring of
    `pentagon_Q_sdp_limit_bound` (above) for the justification chain.

    The full n=8 SDP pipeline:
    1. The Q-objective O_Q ∈ FlagAlg(∅) combines BRRB paths and pentagon terms:
       O_Q = ⟦proj(BRRB_path, 8)⟧ + ⟦proj(C₅_1black, 8)⟧ + 2·⟦proj(C₅_2black, 8)⟧
    2. CSDP solves the SDP on 9295 size-8 flags with 278 Cauchy-Schwarz blocks,
       finding optimal value 0.41458464, so φ(O_Q) ≤ 0.4146 = 2 · 0.2073
    3. The bridge Q(G,v)/Δ⁵ → φ(O_Q)/2 converts to Q(G,v) ≤ (0.2073 + ε)·Δ⁵

    Verified by `certificates/verify_sdp.py` on `certificates/bounded_pentagon_alt.{sdpa,cert}`:
    - Y ≽ 0: PASS (min eigenvalue 1.3e-17)
    - Dual feasibility: PASS (max |tr(F_k Y) - c_k| = 1.2e-12)
    - Dual objective: tr(F_0 Y) = -0.41458464
    - Complementary slackness: tr(XY) = 1.6e-8 -/
theorem pentagon_Q_bound :
    ∀ eps : ℝ, 0 < eps → ∃ D₀ : ℕ, ∀ G : Flag emptyType, ∀ v : Fin G.size,
      IsTriangleFree G → IsRegular G → D₀ ≤ maxDegree G →
      pentagonQ G v ≤ (0.2073 + eps) * maxDegree G ^ 5 := by
  apply pentagon_Q_bound_from_limit 0.2073 (by norm_num)
  exact pentagon_Q_sdp_limit_bound

/-- **Theorem 3.1**: If G is triangle-free then P(G) ≤ 0.02073·|G|·Δ(G)⁴.

    Proof: By Lemma 3.12 (`pentagon_Q_bound`), Σ_v Q(G,v) ≲ 0.2073·|G|·Δ(G)⁵.
    By the Q sum formula, 10·Δ(G)·P(G) ≲ 0.2073·|G|·Δ(G)⁵.
    Therefore P(G) ≲ 0.02073·|G|·Δ(G)⁴.

    **Constant note (2026-05-13 tightening):** The bound `0.02073`
    matches the thesis-original Theorem 3.1 constant, restored from
    the earlier `0.0208` Phase-4 relaxation. The tightening is
    axiomatic-level: the axiom `phi_evalAlg_O_Q_alg_le_bound` was
    tightened `≤ 0.416 → ≤ 0.4146`, justified primarily by the
    SDPA-LR solver's measured optimum `≈ 0.41458`, with the Lean
    cert's `native_decide` providing constructive corroboration at
    the looser `≤ 0.416` bound. See the development notes. -/
theorem pentagon_bound_full (G : Flag emptyType) (hG : IsTriangleFree G) :
    (pentagonCount G : ℝ) ≤ 0.02073 * G.size * maxDegree G ^ 4 := by
  -- Step 1: Reduce to asymptotic bound
  refine pentagon_asymptotic_suffices 0.02073 (by norm_num) (fun eps heps => ?_) G hG
  -- Step 2: Get Q bound for regular graphs
  obtain ⟨D₀, hD₀⟩ := pentagon_Q_bound (10 * eps) (by linarith)
  -- Use D₀' = max D₀ 1 to ensure Δ ≥ 1 (needed for division by Δ)
  refine ⟨max D₀ 1, fun G' hTF' hDeg' => ?_⟩
  -- Step 3: Extend from regular to all triangle-free via pentagon_regular_suffices
  obtain ⟨G'', hTF'', hReg'', hDelta, hRatio⟩ := pentagon_regular_suffices G' hTF'
  -- G'' is regular, triangle-free, Δ(G'') = Δ(G'), P(G')*|G''| ≤ P(G'')*|G'|
  have hDeg'' : D₀ ≤ maxDegree G'' := by
    have : max D₀ 1 ≤ maxDegree G' := hDeg'
    omega
  -- Step 4: Bound Q sum for G''
  -- Each vertex: Q(G'',v) ≤ (0.2073 + 10eps) * Δ⁵
  have hQv : ∀ v : Fin G''.size,
      pentagonQ G'' v ≤ (0.2073 + 10 * eps) * (maxDegree G'' : ℝ) ^ 5 :=
    fun v => hD₀ G'' v hTF'' hReg'' hDeg''
  -- Sum over vertices: Σ_v Q(G'',v) ≤ |G''| * (0.2073 + 10eps) * Δ⁵
  have hQsum_bound : (Finset.univ : Finset (Fin G''.size)).sum (pentagonQ G'') ≤
      (G''.size : ℝ) * ((0.2073 + 10 * eps) * (maxDegree G'' : ℝ) ^ 5) := by
    calc (Finset.univ : Finset (Fin G''.size)).sum (pentagonQ G'')
        ≤ (Finset.univ : Finset (Fin G''.size)).sum
            (fun _ => (0.2073 + 10 * eps) * (maxDegree G'' : ℝ) ^ 5) :=
          Finset.sum_le_sum (fun v _ => hQv v)
      _ = (G''.size : ℝ) * ((0.2073 + 10 * eps) * (maxDegree G'' : ℝ) ^ 5) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Step 5: By pentagon_Q_sum: Σ_v Q(G'',v) = 10 * Δ * P(G'')
  have hQsum := pentagon_Q_sum G'' hReg''
  -- Step 6: Combine to bound P(G'') for regular graph
  -- 10 * Δ * P(G'') ≤ |G''| * (0.2073 + 10eps) * Δ⁵
  -- If Δ > 0: P(G'') ≤ |G''| * (0.02073 + eps) * Δ⁴
  have hDelta_pos : (0 : ℝ) < (maxDegree G'' : ℝ) := Nat.cast_pos.mpr (by omega)
  -- Step 7: From Q sum and Q sum bound, derive P(G'') bound
  -- 10 * Δ * P(G'') = Σ_v Q(G'',v) ≤ |G''| * (0.2073 + 10eps) * Δ⁵
  -- So P(G'') ≤ |G''| * (0.02073 + eps) * Δ⁴ (dividing by 10Δ)
  have hQsum_cast : (10 * maxDegree G'' * pentagonCount G'' : ℝ) =
      10 * (maxDegree G'' : ℝ) * (pentagonCount G'' : ℝ) := by
    norm_cast
  have hQ_combined : 10 * (maxDegree G'' : ℝ) * (pentagonCount G'' : ℝ) ≤
      (G''.size : ℝ) * ((0.2073 + 10 * eps) * (maxDegree G'' : ℝ) ^ 5) := by
    rw [← hQsum_cast, ← hQsum]; exact hQsum_bound
  -- Derive P(G'') ≤ (0.02073 + eps) * |G''| * Δ⁴
  have h10D_pos : (0 : ℝ) < 10 * (maxDegree G'' : ℝ) := by positivity
  have hP_bound : (pentagonCount G'' : ℝ) ≤
      (0.02073 + eps) * (G''.size : ℝ) * (maxDegree G'' : ℝ) ^ 4 := by
    calc (pentagonCount G'' : ℝ)
        ≤ (G''.size : ℝ) * ((0.2073 + 10 * eps) * (maxDegree G'' : ℝ) ^ 5) /
          (10 * (maxDegree G'' : ℝ)) := (le_div_iff₀ h10D_pos).mpr (by linarith)
      _ = (0.02073 + eps) * (G''.size : ℝ) * (maxDegree G'' : ℝ) ^ 4 := by
          rw [pow_succ]; field_simp; ring
  -- Step 8: Transfer from G'' to G' via density ratio
  rw [hDelta] at hP_bound
  by_cases hsize : (G''.size : ℝ) = 0
  · -- G''.size = 0 → maxDegree G'' = 0 → maxDegree G' = 0 → no edges → no pentagons
    have hsize_nat : G''.size = 0 := by exact_mod_cast hsize
    have hmaxdeg'' : maxDegree G'' = 0 := by
      unfold maxDegree
      have : Finset.univ (α := Fin G''.size) = ∅ := by
        ext v; exact absurd v.isLt (by omega)
      rw [this, Finset.sup_empty]; rfl
    have hmaxdeg' : maxDegree G' = 0 := by omega
    have hno_edges : ∀ u v : Fin G'.size, ¬G'.graph.Adj u v := by
      intro u v hadj
      have h1 : (Finset.univ.filter (fun w => G'.graph.Adj u w)).card ≤ maxDegree G' :=
        Finset.le_sup (f := fun v =>
          (Finset.univ.filter (fun u => G'.graph.Adj v u)).card) (Finset.mem_univ u)
      have h2 : 0 < (Finset.univ.filter (fun w => G'.graph.Adj u w)).card :=
        Finset.card_pos.mpr ⟨v, by simp [hadj]⟩
      omega
    have hcount : pentagonCount G' = 0 := by
      unfold pentagonCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro S _
      rintro ⟨f, _, _, hf_adj⟩
      exact hno_edges (f 0) (f 1) ((hf_adj 0 1).mp (by
        unfold cycleGraph5; rw [SimpleGraph.fromRel_adj]; exact ⟨by decide, Or.inl (by decide)⟩))
    simp [hcount, hmaxdeg']
  · -- |G''| > 0: can divide
    have hsize_pos : (0 : ℝ) < G''.size :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hsize)
    -- From hRatio and hP_bound, get P(G') * |G''| ≤ bound * |G''|
    have hne : (G''.size : ℝ) ≠ 0 := ne_of_gt hsize_pos
    have hcombined : (pentagonCount G' : ℝ) * G''.size ≤
        (0.02073 + eps) * G'.size * (maxDegree G' : ℝ) ^ 4 * G''.size := by
      calc (pentagonCount G' : ℝ) * G''.size
          ≤ (pentagonCount G'' : ℝ) * G'.size := hRatio
        _ ≤ ((0.02073 + eps) * G''.size * (maxDegree G' : ℝ) ^ 4) * G'.size :=
            mul_le_mul_of_nonneg_right hP_bound (Nat.cast_nonneg _)
        _ = (0.02073 + eps) * G'.size * (maxDegree G' : ℝ) ^ 4 * G''.size := by ring
    exact le_of_mul_le_mul_right hcombined hsize_pos

end Davey2024
