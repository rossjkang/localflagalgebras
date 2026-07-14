import DaveyThesis2024.StrongEdgeColouring
import DaveyThesis2024.SecBridge
import DaveyThesis2024.SecBipartiteBridge
import DaveyThesis2024.SecAsymmetricBipartiteBridge
import DaveyThesis2024.Reductions.WLOGRegular
import DaveyThesis2024.SecFPeeling
import DaveyThesis2024.SecFPadding
import DaveyThesis2024.SecAsymBridgeF
import DaveyThesis2024.SecAsymReduction
import DaveyThesis2024.SecAsymHighSide

/-!
# Strong-chromatic-index closure — Theorems 4.1 and 4.9 (top of import chain)

This file collects the final consumers of the SEC SDP-certificate pipeline.

**Status (B1 repair, Phase L4 — 2026-07-11):** the original F-free consumer
chain (`sec_sdp_limit_bound{,_bipartite}`, `sec_bound_from_limit_reg`,
`sec_vertex_sparsity{,_bipartite}`, `sec_line_graph_sq_sparsity{,_bipartite}`,
`sec_combined_bound{,_bipartite}`, `strong_chromatic_index_bound_Reg`, and the
whole `_thesis_tight` mirror) was **retired** in L4.2: it consumed the
`K_{3,3}`-refutable SEC identity axiom. The four deterministic SEC headlines
now route through the **§5 F-faithful consumer rebuild** (`secF_*` /
`secBipF_*`), which applies the SDP identity to the F-subset `H[F]` only.

* **§5 (F-faithful)** — `secSparsityF` / `secBipartiteSparsityF`,
  `secF_bound_from_limit`, `secF_vertex_sparsity` / `secBipF_vertex_sparsity`,
  `secF_combined_bound` / `secBipF_combined_bound(_Reg)`,
  `strong_chromatic_index_bound_Reg_F`. These consume the F-faithful bridge
  theorem `SecBridge.secF_density_bridge` (and its bipartite twin).
* `strong_chromatic_index_bound` (Theorem 4.1) and
  `strong_chromatic_index_bipartite` (Theorem 4.9), plus their `_thesis_tight`
  variants — statements byte-unchanged from before the repair, now proved via
  the §5 F-faithful chain + `strong_chromatic_index_Reg_suffices`.
* The **asymmetric** bipartite chain (§8) is independent of the deterministic
  chain and was left untouched by the repair.

## Why this file exists (import-cycle resolution)

`StrongEdgeColouring.lean` cannot import `SecBridge`/`SecBipartiteBridge`
directly: the chain `SecBridge → CGraph22Bridge → StrongEdgeColouring`
would be cyclic. By living *above* the bridges, this file:

* imports the limit framework + sec defs from `StrongEdgeColouring`,
* imports the cert-driven bridges,
* and re-establishes the axiom names as **theorems** consuming the bridges.

This mirrors `PentagonBound.lean`'s role for the Pentagon-Q chain.

## Restriction note (Regular) — Phase 2 of WLOG-regular closure

The F-faithful density bridge `SecBridge.secF_density_bridge` requires
`IsRegular` of the underlying sequence, because the limit-functional
construction in `SecBridge` (`secF_phi_construction`) threads it through to
land in `secGenGraphClassF`. The cert-driven SDP closure therefore produces
the Reg case `strong_chromatic_index_bound_Reg_F`.

The fully unrestricted `strong_chromatic_index_bound` (matching the
thesis Theorem 4.1 statement) is recovered by combining the Reg case
with the reduction theorem `strong_chromatic_index_Reg_suffices` below,
which captures the classical "WLOG regular" reduction from thesis §4.1
(also cf. Pentagon-Q's `pentagon_regular_suffices`). The four historical
bounds (`molloy_reed_1997`, `bruhn_joos_2015`, `bonamy_perrett_postle_2018`,
`hurley_kang_2022`) are now stated unrestricted as well.

The bipartite headline `strong_chromatic_index_bipartite` retains its
original `IsBipartite` hypothesis (matching the bridge); no analogous
reduction is required there since the bipartite SEC bridge was already
TF + Reg-free.
-/

namespace Davey2024

open Finset BigOperators Nat Classical

noncomputable section

set_option linter.unusedSectionVars false

/-! ## §4.4d-iv: Main theorems (general SEC) -/

/-- **Theorem 3.1 improvement (Strong Neighbourhood Density)**: stub statement —
    the precise bound is captured by `secF_combined_bound`. Retained for
    historical/citation parity with the thesis layout. -/
theorem strong_neighbourhood_density_improved (eta : ℝ)
    (_heta1 : 0 ≤ eta) (_heta2 : eta ≤ 0.3) :
    ∀ eps : ℝ, 0 < eps → ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      D₀ ≤ maxDegree G →
      True := by
  intro _eps _heps
  exact ⟨0, fun G _ => trivial⟩

/-- **Reduction theorem: Regular case suffices for the χ'_s bound** (§4.1, Reduction).

    **Statement.** If for some constant `c > 0` and for some `D₀` every
    regular `G` with `D₀ ≤ Δ(G)` satisfies `χ'_s(G) ≤ c · Δ(G)²`, then the
    same bound holds (with a possibly larger `D₀`) for *every* graph `G`
    with sufficient max degree — no regularity hypothesis required.

    **Why needed.** Our cert-driven SDP bridge (`SecBridge`) is formulated
    over the F-faithful local-flag class `secGenGraphClassF`, whose elements
    are Δ-regular (2,2)-coloured graphs. Threading this
    through the limit-functional construction (`secF_phi_construction`,
    `secF_density_bridge`) forces an `IsRegular` hypothesis on each
    `(seq k).1`, which propagates up to `secF_bound_from_limit` and
    `strong_chromatic_index_bound_Reg_F`. The thesis (Theorem 4.1) is stated
    for arbitrary `G`; the WLOG-regular reduction is a pre-existing
    combinatorial argument (see "Why correct" below), not part of the
    SDP/flag-algebra core of the formalisation.

    **Why correct.** The WLOG-regular reduction (thesis §4.1 "Reduction",
    explicitly noted as folklore: *"The first reduction we can note is
    that WLOG we can assume G is regular, as outlined in each of the
    above papers."*) Standard construction: take two copies of `G` and
    add edges between low-degree vertex pairs to raise `δ(G)` to `Δ(G)`
    while preserving `Δ(G)` and not decreasing `χ'_s`; iterate. The
    Pentagon-Q analog of this is formalised as `pentagon_regular_suffices`
    in `PentagonConjecture.lean:1368`.

    **Closure status (Phase 3, 2026-05-20).** This was previously an
    axiom; it has been closed as a theorem by the Molloy–Reed iterated
    doubling construction (`sec_regular_suffices` in
    `Reductions/WLOGRegular.lean`). The key new combinatorial content is
    `strongChromaticIndex_le_doubledFlag`: the strong chromatic index
    does not decrease under doubling, because any strong edge colouring
    of `doubledFlag G` restricts (along the copy-0 embedding) to a
    strong edge colouring of `G` with the same colour set.

    **Citations.**
    * Thesis §4.1 "Reduction" (chapter 4, line 152 of
      `thesis_source/chapters/strong_edge_colouring.tex`).
    * Molloy & Reed, "A bound on the strong chromatic index of a graph",
      JCTB 69 (1997), 103-109 — the original sparse-cover construction.
    * Bruhn & Joos, "A stronger bound for the strong chromatic index",
      Combin. Probab. Comput. 27 (2018), 21-43 — refined WLOG-regular
      reduction at constant ~1.93.
    * Hurley, de Joannis de Verclos & Kang, "An improved procedure for
      colouring graphs of bounded local density", JCTB 2022 (§1.6) —
      reduction at the thesis's working constant 1.73.
    * Pentagon-Q Lean analog: `pentagon_regular_suffices`
      (`DaveyThesis2024/PentagonConjecture.lean:1368`). -/
theorem strong_chromatic_index_Reg_suffices (c : ℝ) :
    (∃ D₀ : ℕ, ∀ G : Flag emptyType, IsRegular G →
       D₀ ≤ maxDegree G →
       (strongChromaticIndex G : ℝ) ≤ c * (maxDegree G : ℝ) ^ 2) →
    (∃ D₀ : ℕ, ∀ G : Flag emptyType, D₀ ≤ maxDegree G →
       (strongChromaticIndex G : ℝ) ≤ c * (maxDegree G : ℝ) ^ 2) := by
  rintro ⟨D₀, hReg⟩
  refine ⟨D₀, fun G hΔ => ?_⟩
  obtain ⟨H, hH_reg, hH_maxdeg, hH_mono⟩ :=
    Davey2024.Reductions.WLOGRegular.sec_regular_suffices G
  have hΔ_H : D₀ ≤ maxDegree H := by rw [hH_maxdeg]; exact hΔ
  have hbd : (strongChromaticIndex H : ℝ) ≤ c * (maxDegree H : ℝ) ^ 2 :=
    hReg H hH_reg hΔ_H
  have hmono : (strongChromaticIndex G : ℝ) ≤ (strongChromaticIndex H : ℝ) := by
    exact_mod_cast hH_mono
  calc (strongChromaticIndex G : ℝ)
      ≤ (strongChromaticIndex H : ℝ) := hmono
    _ ≤ c * (maxDegree H : ℝ) ^ 2 := hbd
    _ = c * (maxDegree G : ℝ) ^ 2 := by rw [hH_maxdeg]

/-! ## §5. F-faithful consumer rebuild (B1 repair, Phase L3.4 — 2026-07-11)

Everything below rebuilds the deterministic SEC consumer chain on the
F-faithful axioms (the development notes Phase L3). The old chain above
(`sec_vertex_sparsity` → `sec_combined_bound` → headlines) is retired in
L4.2; nothing below references the old (false/vacuous) axioms. -/

section SecFConsumer

open Davey2024.SecBridge Davey2024.SecBipartiteBridge

/-- **F-faithful sparsity parameter** (general):
`σ_F = 1 − 10.644/16 − secIdentityTol − 1/10000 = 0.33464`. The three
subtractions: the loose SDP density bound over 16, the L2 identity
tolerance, and the BW `ε`-slack of `secF_bound_from_limit`. -/
noncomputable def secSparsityF : ℝ := 1 - 10.644 / 16 - secIdentityTol - 1/10000

lemma secSparsityF_val : secSparsityF = 0.33464 := by
  unfold secSparsityF secIdentityTol; norm_num

lemma secSparsityF_pos : 0 < secSparsityF := by rw [secSparsityF_val]; norm_num

lemma secSparsityF_le_one : secSparsityF ≤ 1 := by rw [secSparsityF_val]; norm_num

/-- √σ_F ≤ 0.5786 (since 0.5786² = 0.33477796 ≥ 0.33464 = σ_F). -/
lemma sqrt_secSparsityF_le : Real.sqrt secSparsityF ≤ 0.5786 :=
  (Real.sqrt_le_sqrt (by rw [secSparsityF_val]; norm_num)).trans_eq
    (Real.sqrt_sq (by norm_num))

/-- σ_F · √σ_F ≤ 0.19363. -/
lemma secSparsityF_mul_sqrt_le : secSparsityF * Real.sqrt secSparsityF ≤ 0.19363 := by
  have hsigma : secSparsityF ≤ 0.33464 := le_of_eq secSparsityF_val
  have hsqrt := sqrt_secSparsityF_le
  calc secSparsityF * Real.sqrt secSparsityF
      ≤ 0.33464 * 0.5786 := by
        apply mul_le_mul hsigma hsqrt (Real.sqrt_nonneg _) (by norm_num)
    _ ≤ 0.19363 := by norm_num

/-- ε(σ_F) > 0.13504. -/
lemma colouringEps_secSparsityF_gt : 0.13504 < colouringEps secSparsityF := by
  unfold colouringEps
  have hbound := secSparsityF_mul_sqrt_le
  have h1 : secSparsityF / 2 - secSparsityF * Real.sqrt secSparsityF / 6 ≥
      secSparsityF / 2 - 0.19363 / 6 := by
    linarith [div_le_div_of_nonneg_right hbound (show (0:ℝ) ≤ 6 by norm_num)]
  linarith [show secSparsityF / 2 - 0.19363 / 6 > 0.13504 by
    rw [secSparsityF_val]; norm_num]

/-- (1 − ε(σ_F))·2 < 1.72992 — closes the 1.73 thesis-tight headline from the
LOOSE bound (gate L2(d) strict-drop arithmetic, draft §6b). -/
lemma secF_colouring_factor_lt : (1 - colouringEps secSparsityF) * 2 < 1.72992 := by
  linarith [colouringEps_secSparsityF_gt]

/-- **F-faithful bipartite sparsity parameter**:
`σ_F^bip = 1 − 4.093/8 − secIdentityTol − 1/10000 = 0.488265`. -/
noncomputable def secBipartiteSparsityF : ℝ :=
  1 - 4.093 / 8 - secIdentityTol - 1/10000

lemma secBipartiteSparsityF_val : secBipartiteSparsityF = 0.488265 := by
  unfold secBipartiteSparsityF secIdentityTol; norm_num

lemma secBipartiteSparsityF_pos : 0 < secBipartiteSparsityF := by
  rw [secBipartiteSparsityF_val]; norm_num

lemma secBipartiteSparsityF_le_one : secBipartiteSparsityF ≤ 1 := by
  rw [secBipartiteSparsityF_val]; norm_num

/-- √σ_F^bip ≤ 0.6988 (0.6988² = 0.48832144 ≥ 0.488265). -/
lemma sqrt_secBipartiteSparsityF_le : Real.sqrt secBipartiteSparsityF ≤ 0.6988 :=
  (Real.sqrt_le_sqrt (by rw [secBipartiteSparsityF_val]; norm_num)).trans_eq
    (Real.sqrt_sq (by norm_num))

/-- σ_F^bip · √σ_F^bip ≤ 0.34120. -/
lemma secBipartiteSparsityF_mul_sqrt_le :
    secBipartiteSparsityF * Real.sqrt secBipartiteSparsityF ≤ 0.34120 := by
  have hsigma : secBipartiteSparsityF ≤ 0.488265 := le_of_eq secBipartiteSparsityF_val
  have hsqrt := sqrt_secBipartiteSparsityF_le
  calc secBipartiteSparsityF * Real.sqrt secBipartiteSparsityF
      ≤ 0.488265 * 0.6988 := by
        apply mul_le_mul hsigma hsqrt (Real.sqrt_nonneg _) (by norm_num)
    _ ≤ 0.34120 := by norm_num

/-- ε(σ_F^bip) > 0.187265. -/
lemma colouringEps_secBipartiteSparsityF_gt :
    0.187265 < colouringEps secBipartiteSparsityF := by
  unfold colouringEps
  have hbound := secBipartiteSparsityF_mul_sqrt_le
  have h1 : secBipartiteSparsityF / 2 -
      secBipartiteSparsityF * Real.sqrt secBipartiteSparsityF / 6 ≥
      secBipartiteSparsityF / 2 - 0.34120 / 6 := by
    linarith [div_le_div_of_nonneg_right hbound (show (0:ℝ) ≤ 6 by norm_num)]
  linarith [show secBipartiteSparsityF / 2 - 0.34120 / 6 > 0.187265 by
    rw [secBipartiteSparsityF_val]; norm_num]

/-- (1 − ε(σ_F^bip))·2 < 1.62547 — closes the 1.6255 thesis-tight bipartite
headline from the LOOSE bound. -/
lemma secBipF_colouring_factor_lt :
    (1 - colouringEps secBipartiteSparsityF) * 2 < 1.62547 := by
  linarith [colouringEps_secBipartiteSparsityF_gt]

/-- `strongFDegree` is at most the max degree of `L(G)²`. -/
lemma strongFDegree_le_lineGraphSq_maxDegree (G : Flag emptyType)
    (F : Finset (Fin (lineGraphSqFlag G).size))
    (v : Fin (lineGraphSqFlag G).size) :
    SecBridge.strongFDegree G F v ≤ maxDegree (lineGraphSqFlag G) := by
  refine le_trans (Finset.card_le_card
    (Finset.filter_subset_filter _ (Finset.subset_univ F))) ?_
  exact Finset.le_sup (f := fun w =>
    (Finset.univ.filter (fun u => (lineGraphSqFlag G).graph.Adj w u)).card)
    (Finset.mem_univ v)

/-- `fEdgesInNeighbourhood ≤ strongFDegree²` (the pair filter lives in the
square of the F-neighbour set). -/
lemma fEdgesInNeighbourhood_le_sq (G : Flag emptyType)
    (F : Finset (Fin (lineGraphSqFlag G).size))
    (v : Fin (lineGraphSqFlag G).size) :
    SecBridge.fEdgesInNeighbourhood G F v ≤ (SecBridge.strongFDegree G F v) ^ 2 := by
  refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
  rw [Finset.card_product]
  exact le_of_eq (sq (SecBridge.strongFDegree G F v)).symm

/-- The within-F density lies in `[0, 4]` once `1 ≤ Δ(G)`. -/
lemma secF_density_in_Icc (G : Flag emptyType)
    (F : Finset (Fin (lineGraphSqFlag G).size))
    (v : Fin (lineGraphSqFlag G).size) (hΔ : 1 ≤ maxDegree G) :
    (SecBridge.fEdgesInNeighbourhood G F v : ℝ) /
      (Nat.choose (2 * (maxDegree G) ^ 2) 2 : ℝ) ∈ Set.Icc 0 4 := by
  set m : ℕ := 2 * (maxDegree G) ^ 2 with hm_def
  have hm2 : 2 ≤ m := by
    have : 1 ≤ (maxDegree G) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hden_nat : m ^ 2 ≤ 4 * Nat.choose m 2 := by
    rw [Nat.choose_two_right]
    have h1 : m * (m - 1) / 2 * 2 = m * (m - 1) := by
      apply Nat.div_mul_cancel
      rcases Nat.even_or_odd m with he | ho
      · exact Dvd.dvd.mul_right he.two_dvd _
      · exact Dvd.dvd.mul_left (Nat.Odd.sub_odd ho odd_one).two_dvd _
    nlinarith [Nat.sub_add_cancel (show 1 ≤ m by omega),
      Nat.div_mul_le_self (m * (m - 1)) 2]
  have hnum : SecBridge.fEdgesInNeighbourhood G F v ≤ m ^ 2 := by
    have h1 := fEdgesInNeighbourhood_le_sq G F v
    have h2 := strongFDegree_le_lineGraphSq_maxDegree G F v
    have h3 := lineGraphSq_maxDegree_le G
    have h4 : SecBridge.strongFDegree G F v ≤ m := le_trans h2 h3
    calc SecBridge.fEdgesInNeighbourhood G F v
        ≤ (SecBridge.strongFDegree G F v) ^ 2 := h1
      _ ≤ m ^ 2 := Nat.pow_le_pow_left h4 2
  have hden_pos : 0 < Nat.choose m 2 := Nat.choose_pos (by omega)
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rw [div_le_iff₀ (by exact_mod_cast hden_pos)]
    have : (SecBridge.fEdgesInNeighbourhood G F v : ℝ) ≤ (m ^ 2 : ℕ) := by
      exact_mod_cast hnum
    calc (SecBridge.fEdgesInNeighbourhood G F v : ℝ)
        ≤ ((m ^ 2 : ℕ) : ℝ) := this
      _ ≤ ((4 * Nat.choose m 2 : ℕ) : ℝ) := by exact_mod_cast hden_nat
      _ = 4 * (Nat.choose m 2 : ℝ) := by push_cast; ring

/-- **Bolzano–Weierstrass for within-F densities**: along any item sequence
with strictly increasing max degree there is a convergent subsequence of
`fEdgesInNeighbourhood / C(2Δ², 2)`. -/
theorem secF_density_convergent_subseq
    (seq : ℕ → SecBridge.SecFSeqItem)
    (hΔ : StrictMono (fun k => maxDegree (seq k).G)) :
    ∃ (sub : ℕ → ℕ) (L : ℝ), StrictMono sub ∧ 0 ≤ L ∧
      Filter.Tendsto (fun k =>
        (SecBridge.fEdgesInNeighbourhood (seq (sub k)).G (seq (sub k)).F
          (seq (sub k)).v : ℝ) /
        (Nat.choose (2 * (maxDegree (seq (sub k)).G) ^ 2) 2 : ℝ))
        Filter.atTop (nhds L) := by
  let seq' := fun k => seq (k + 1)
  have hΔ_ge : ∀ k, 1 ≤ maxDegree (seq' k).G := by
    intro k
    have h : k + 1 ≤ maxDegree (seq (k + 1)).G := hΔ.id_le (k + 1)
    change 1 ≤ maxDegree (seq (k + 1)).G
    omega
  have hmem : ∀ k,
      (SecBridge.fEdgesInNeighbourhood (seq' k).G (seq' k).F (seq' k).v : ℝ) /
        (Nat.choose (2 * (maxDegree (seq' k).G) ^ 2) 2 : ℝ) ∈ Set.Icc 0 4 :=
    fun k => secF_density_in_Icc (seq' k).G (seq' k).F (seq' k).v (hΔ_ge k)
  obtain ⟨L, hL_mem, ψ, hψ_mono, hψ_tend⟩ := isCompact_Icc.tendsto_subseq hmem
  refine ⟨fun k => ψ k + 1, L, ?_, hL_mem.1, hψ_tend⟩
  intro a b hab
  exact Nat.add_lt_add_right (hψ_mono hab) 1

/-- **F-faithful Reg contradiction framework** (mirror of
`sec_bound_from_limit_reg` with the within-F quantity and the full gate
carried through the counterexample extraction — the gate hypotheses are
per-k, so they compose with subsequences). -/
theorem secF_bound_from_limit
    (c : ℝ) (_hc : 0 ≤ c)
    (hlim : ∀ (seq : ℕ → SecBridge.SecFSeqItem)
      (_hΔ : StrictMono (fun k => maxDegree (seq k).G))
      (_hReg : ∀ k, IsRegular (seq k).G)
      (_hFdeg : ∀ k, ∀ e ∈ (seq k).F,
        17297 * (maxDegree (seq k).G) ^ 2 ≤
          10000 * SecBridge.strongFDegree (seq k).G (seq k).F e),
      ∀ (sub : ℕ → ℕ) (L : ℝ), StrictMono sub →
        Filter.Tendsto (fun k =>
          (SecBridge.fEdgesInNeighbourhood (seq (sub k)).G (seq (sub k)).F
            (seq (sub k)).v : ℝ) /
          (Nat.choose (2 * (maxDegree (seq (sub k)).G) ^ 2) 2 : ℝ))
          Filter.atTop (nhds L) → L ≤ c) :
    ∀ eps : ℝ, 0 < eps → ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      ∀ F : Finset (Fin (lineGraphSqFlag G).size),
      IsRegular G →
      (∀ e ∈ F, 17297 * (maxDegree G) ^ 2 ≤
        10000 * SecBridge.strongFDegree G F e) →
      D₀ ≤ maxDegree G →
      ∀ v ∈ F,
        (SecBridge.fEdgesInNeighbourhood G F v : ℝ) ≤
          (c + eps) * (Nat.choose (2 * (maxDegree G) ^ 2) 2 : ℝ) := by
  intro eps heps
  by_contra h_not
  push_neg at h_not
  have h_exists : ∀ D : ℕ, ∃ it : SecBridge.SecFSeqItem,
      IsRegular it.G ∧
      (∀ e ∈ it.F, 17297 * (maxDegree it.G) ^ 2 ≤
        10000 * SecBridge.strongFDegree it.G it.F e) ∧
      D < maxDegree it.G ∧
      (c + eps) * (Nat.choose (2 * (maxDegree it.G) ^ 2) 2 : ℝ) <
        (SecBridge.fEdgesInNeighbourhood it.G it.F it.v : ℝ) := by
    intro D
    obtain ⟨G, F, hReg, hFdeg, hG_deg, v, hvF, hv⟩ := h_not (D + 1)
    exact ⟨⟨G, F, v, hvF⟩, hReg, hFdeg, (show D < maxDegree G by omega), hv⟩
  let buildSeq : ℕ → SecBridge.SecFSeqItem :=
    Nat.rec (h_exists 1).choose
      (fun _ p => (h_exists (maxDegree p.G)).choose)
  have hΔ_strict : StrictMono (fun k => maxDegree (buildSeq k).G) :=
    strictMono_nat_of_lt_succ fun k =>
      (h_exists (maxDegree (buildSeq k).G)).choose_spec.2.2.1
  have hΔ_ge1 : ∀ k, 1 ≤ maxDegree (buildSeq k).G := by
    intro k
    have h1 : 1 < maxDegree (buildSeq 0).G := (h_exists 1).choose_spec.2.2.1
    rcases k with _ | k
    · omega
    · have h2 : maxDegree (buildSeq 0).G < maxDegree (buildSeq (k + 1)).G :=
        hΔ_strict (Nat.zero_lt_succ k)
      omega
  let shiftSeq : ℕ → SecBridge.SecFSeqItem := fun k => buildSeq (k + 1)
  have hΔ_shift : StrictMono (fun k => maxDegree (shiftSeq k).G) :=
    fun a b hab => hΔ_strict (by omega : a + 1 < b + 1)
  have hReg_shift : ∀ k, IsRegular (shiftSeq k).G :=
    fun k => (h_exists (maxDegree (buildSeq k).G)).choose_spec.1
  have hFdeg_shift : ∀ k, ∀ e ∈ (shiftSeq k).F,
      17297 * (maxDegree (shiftSeq k).G) ^ 2 ≤
        10000 * SecBridge.strongFDegree (shiftSeq k).G (shiftSeq k).F e :=
    fun k => (h_exists (maxDegree (buildSeq k).G)).choose_spec.2.1
  obtain ⟨sub, L, hsub_mono, _, hL_tend⟩ :=
    secF_density_convergent_subseq shiftSeq hΔ_shift
  have hden_pos : ∀ k, 0 < Nat.choose (2 * (maxDegree (shiftSeq (sub k)).G) ^ 2) 2 := by
    intro k
    apply Nat.choose_pos
    change 2 ≤ 2 * (maxDegree (buildSeq (sub k + 1)).G) ^ 2
    have h1 : 1 ≤ maxDegree (buildSeq (sub k + 1)).G := hΔ_ge1 (sub k + 1)
    have h2 : 1 ≤ (maxDegree (buildSeq (sub k + 1)).G) ^ 2 :=
      Nat.one_le_pow _ _ (by omega)
    omega
  have hL_ge : c + eps ≤ L := by
    apply ge_of_tendsto hL_tend
    rw [Filter.eventually_atTop]
    refine ⟨0, fun k _ => le_of_lt ?_⟩
    rw [lt_div_iff₀ (by exact_mod_cast hden_pos k)]
    exact (h_exists (maxDegree (buildSeq (sub k)).G)).choose_spec.2.2.2
  linarith [hlim shiftSeq hΔ_shift hReg_shift hFdeg_shift sub L hsub_mono hL_tend]

/-- **Per-F-edge SDP sparsity (general)**: for regular `G` and any F-set
satisfying the min-strong-degree gate, once `Δ(G)` is large every `v ∈ F`
has within-F neighbourhood density at most `1 − σ_F` at the `C(2Δ²,2)`
scale. Replaces the all-vertex `sec_vertex_sparsity` on the F-faithful
chain. Uses `c = 10.644/16 + secIdentityTol` (the bridge bound) and
`eps = 1/10000`, so `c + eps = 1 − secSparsityF`. -/
theorem secF_vertex_sparsity :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      ∀ F : Finset (Fin (lineGraphSqFlag G).size),
      IsRegular G →
      (∀ e ∈ F, 17297 * (maxDegree G) ^ 2 ≤
        10000 * SecBridge.strongFDegree G F e) →
      D₀ ≤ maxDegree G →
      ∀ v ∈ F,
        (SecBridge.fEdgesInNeighbourhood G F v : ℝ) ≤
          (1 - secSparsityF) * (Nat.choose (2 * (maxDegree G) ^ 2) 2 : ℝ) := by
  obtain ⟨D₀, hD₀⟩ := secF_bound_from_limit (10.644 / 16 + secIdentityTol)
    (by unfold secIdentityTol; norm_num)
    (fun seq hΔ hReg hFdeg sub L hsub htend =>
      SecBridge.secF_density_bridge seq hΔ hReg hFdeg sub L hsub htend)
    (1/10000) (by norm_num)
  refine ⟨D₀, fun G F hReg hFdeg hG v hvF => ?_⟩
  have h := hD₀ G F hReg hFdeg hG v hvF
  have hval : (10.644 / 16 + secIdentityTol) + 1/10000 = 1 - secSparsityF := by
    unfold secSparsityF; ring
  rwa [hval] at h

/-- **Per-F-edge SDP sparsity (bipartite)**: bipartite mirror at
`c = 4.093/8 + secIdentityTol`, gate 16254, `c + eps = 1 − σ_F^bip`. -/
theorem secBipF_vertex_sparsity :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      ∀ F : Finset (Fin (lineGraphSqFlag G).size),
      IsRegular G → IsBipartite G →
      (∀ e ∈ F, 16254 * (maxDegree G) ^ 2 ≤
        10000 * SecBridge.strongFDegree G F e) →
      D₀ ≤ maxDegree G →
      ∀ v ∈ F,
        (SecBridge.fEdgesInNeighbourhood G F v : ℝ) ≤
          (1 - secBipartiteSparsityF) * (Nat.choose (2 * (maxDegree G) ^ 2) 2 : ℝ) := by
  -- Bipartite framework: mirror `secF_bound_from_limit` inline with the
  -- extra `IsBipartite` invariant threaded through the extraction.
  have main : ∀ eps : ℝ, 0 < eps → ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      ∀ F : Finset (Fin (lineGraphSqFlag G).size),
      IsRegular G → IsBipartite G →
      (∀ e ∈ F, 16254 * (maxDegree G) ^ 2 ≤
        10000 * SecBridge.strongFDegree G F e) →
      D₀ ≤ maxDegree G →
      ∀ v ∈ F,
        (SecBridge.fEdgesInNeighbourhood G F v : ℝ) ≤
          ((4.093 / 8 + secIdentityTol) + eps) *
            (Nat.choose (2 * (maxDegree G) ^ 2) 2 : ℝ) := by
    intro eps heps
    by_contra h_not
    push_neg at h_not
    have h_exists : ∀ D : ℕ, ∃ it : SecBridge.SecFSeqItem,
        IsRegular it.G ∧ IsBipartite it.G ∧
        (∀ e ∈ it.F, 16254 * (maxDegree it.G) ^ 2 ≤
          10000 * SecBridge.strongFDegree it.G it.F e) ∧
        D < maxDegree it.G ∧
        ((4.093 / 8 + secIdentityTol) + eps) *
            (Nat.choose (2 * (maxDegree it.G) ^ 2) 2 : ℝ) <
          (SecBridge.fEdgesInNeighbourhood it.G it.F it.v : ℝ) := by
      intro D
      obtain ⟨G, F, hReg, hBip, hFdeg, hG_deg, v, hvF, hv⟩ := h_not (D + 1)
      exact ⟨⟨G, F, v, hvF⟩, hReg, hBip, hFdeg,
        (show D < maxDegree G by omega), hv⟩
    let buildSeq : ℕ → SecBridge.SecFSeqItem :=
      Nat.rec (h_exists 1).choose
        (fun _ p => (h_exists (maxDegree p.G)).choose)
    have hΔ_strict : StrictMono (fun k => maxDegree (buildSeq k).G) :=
      strictMono_nat_of_lt_succ fun k =>
        (h_exists (maxDegree (buildSeq k).G)).choose_spec.2.2.2.1
    have hΔ_ge1 : ∀ k, 1 ≤ maxDegree (buildSeq k).G := by
      intro k
      have h1 : 1 < maxDegree (buildSeq 0).G := (h_exists 1).choose_spec.2.2.2.1
      rcases k with _ | k
      · omega
      · have h2 : maxDegree (buildSeq 0).G < maxDegree (buildSeq (k + 1)).G :=
          hΔ_strict (Nat.zero_lt_succ k)
        omega
    let shiftSeq : ℕ → SecBridge.SecFSeqItem := fun k => buildSeq (k + 1)
    have hΔ_shift : StrictMono (fun k => maxDegree (shiftSeq k).G) :=
      fun a b hab => hΔ_strict (by omega : a + 1 < b + 1)
    have hReg_shift : ∀ k, IsRegular (shiftSeq k).G :=
      fun k => (h_exists (maxDegree (buildSeq k).G)).choose_spec.1
    have hBip_shift : ∀ k, IsBipartite (shiftSeq k).G :=
      fun k => (h_exists (maxDegree (buildSeq k).G)).choose_spec.2.1
    have hFdeg_shift : ∀ k, ∀ e ∈ (shiftSeq k).F,
        16254 * (maxDegree (shiftSeq k).G) ^ 2 ≤
          10000 * SecBridge.strongFDegree (shiftSeq k).G (shiftSeq k).F e :=
      fun k => (h_exists (maxDegree (buildSeq k).G)).choose_spec.2.2.1
    obtain ⟨sub, L, hsub_mono, _, hL_tend⟩ :=
      secF_density_convergent_subseq shiftSeq hΔ_shift
    have hden_pos : ∀ k,
        0 < Nat.choose (2 * (maxDegree (shiftSeq (sub k)).G) ^ 2) 2 := by
      intro k
      apply Nat.choose_pos
      change 2 ≤ 2 * (maxDegree (buildSeq (sub k + 1)).G) ^ 2
      have h1 : 1 ≤ maxDegree (buildSeq (sub k + 1)).G := hΔ_ge1 (sub k + 1)
      have h2 : 1 ≤ (maxDegree (buildSeq (sub k + 1)).G) ^ 2 :=
        Nat.one_le_pow _ _ (by omega)
      omega
    have hL_ge : (4.093 / 8 + secIdentityTol) + eps ≤ L := by
      apply ge_of_tendsto hL_tend
      rw [Filter.eventually_atTop]
      refine ⟨0, fun k _ => le_of_lt ?_⟩
      rw [lt_div_iff₀ (by exact_mod_cast hden_pos k)]
      exact (h_exists (maxDegree (buildSeq (sub k)).G)).choose_spec.2.2.2.2
    have hL_le := secBipF_density_bridge shiftSeq hΔ_shift hBip_shift hReg_shift
      hFdeg_shift sub L hsub_mono hL_tend
    linarith
  obtain ⟨D₀, hD₀⟩ := main (1/10000) (by norm_num)
  refine ⟨D₀, fun G F hReg hBip hFdeg hG v hvF => ?_⟩
  have h := hD₀ G F hReg hBip hFdeg hG v hvF
  have hval : (4.093 / 8 + secIdentityTol) + 1/10000 = 1 - secBipartiteSparsityF := by
    unfold secBipartiteSparsityF; ring
  rwa [hval] at h

/-- The F-peeling threshold at η = 0.2703: `t(Δ) = ⌈1.7297·Δ²⌉` in exact
integers. -/
noncomputable def secFThreshold (G : Flag emptyType) : ℕ :=
  (17297 * (maxDegree G) ^ 2 + 9999) / 10000

/-- The peeled set satisfies the L2 gate (integer ceil-division conversion). -/
lemma secFThreshold_gate (G : Flag emptyType) :
    ∀ e ∈ maximalStrongF G (secFThreshold G),
      17297 * (maxDegree G) ^ 2 ≤
        10000 * SecBridge.strongFDegree G (maximalStrongF G (secFThreshold G)) e := by
  intro e he
  have h := maximalStrongF_min_degree G (secFThreshold G) e he
  have ht : secFThreshold G = (17297 * (maxDegree G) ^ 2 + 9999) / 10000 := rfl
  omega

/-- `fEdgesOn` at `lineGraphSqFlag` is `fEdgesInNeighbourhood` (definitional). -/
lemma fEdgesOn_lineGraphSq (G : Flag emptyType)
    (F : Finset (Fin (lineGraphSqFlag G).size))
    (v : Fin (lineGraphSqFlag G).size) :
    fEdgesOn (lineGraphSqFlag G) F v = SecBridge.fEdgesInNeighbourhood G F v := rfl

/-- **F-faithful combined bound (general, Reg case)** — the two-branch close:
peel F at the η = 0.2703 threshold; colour `H[F]` by the degree-scale
colouring theorem at `D = 2Δ²`; extend to `H = L(G)²` by the degeneracy
greedy; close each branch against `C`. -/
theorem secF_combined_bound (C : ℝ)
    (hC1 : (1 - colouringEps secSparsityF) * 2 < C)
    (hC2 : (1.7297 : ℝ) < C) :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType, IsRegular G → D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ C * (maxDegree G : ℝ) ^ 2 := by
  set iota : ℝ := (C - (1 - colouringEps secSparsityF) * 2) / 2 with hiota_def
  have hiota_pos : 0 < iota := by rw [hiota_def]; linarith
  obtain ⟨X₀, hX⟩ := hurley_colouring_scale secSparsityF iota
    secSparsityF_pos secSparsityF_le_one hiota_pos
  obtain ⟨D₁, hD₁⟩ := secF_vertex_sparsity
  obtain ⟨D₂, hD₂⟩ : ∃ D₂ : ℕ, ∀ Δ : ℕ, D₂ ≤ Δ →
      1.7297 * (Δ:ℝ)^2 + 1 ≤ C * (Δ:ℝ)^2 := by
    refine ⟨Nat.ceil (1/(C - 1.7297)) + 1, fun Δ hΔ => ?_⟩
    have hpos : (0:ℝ) < C - 1.7297 := by linarith
    have h1 : (1/(C - 1.7297)) ≤ (Δ:ℝ) := by
      calc (1/(C - 1.7297)) ≤ (Nat.ceil (1/(C - 1.7297)) : ℝ) := Nat.le_ceil _
        _ ≤ (Δ : ℝ) := by exact_mod_cast le_trans (Nat.le_succ _) hΔ
    have hΔ1 : (1:ℝ) ≤ (Δ:ℝ) := by
      have : 1 ≤ Δ := by omega
      exact_mod_cast this
    have h2 : 1 ≤ (C - 1.7297) * (Δ:ℝ) := by
      rw [div_le_iff₀ hpos] at h1
      linarith
    nlinarith
  refine ⟨max (max D₁ X₀) (max D₂ 1), fun G hReg hG => ?_⟩
  have hΔD₁ : D₁ ≤ maxDegree G := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hG
  have hΔX₀ : X₀ ≤ maxDegree G := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hG
  have hΔD₂ : D₂ ≤ maxDegree G := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hG
  have hΔ1 : 1 ≤ maxDegree G := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hG
  have hgate := secFThreshold_gate G
  -- S-degree bound in H[F]:
  have hSdeg : ∀ v ∈ maximalStrongF G (secFThreshold G),
      ((maximalStrongF G (secFThreshold G)).filter
        (fun i => (lineGraphSqFlag G).graph.Adj v i)).card ≤ 2 * (maxDegree G)^2 := by
    intro v _
    exact le_trans (strongFDegree_le_lineGraphSq_maxDegree G _ v)
      (lineGraphSq_maxDegree_le G)
  -- Per-F-edge sparsity at scale C(2Δ², 2):
  have hsparse : ∀ v ∈ maximalStrongF G (secFThreshold G),
      (fEdgesOn (lineGraphSqFlag G) (maximalStrongF G (secFThreshold G)) v : ℝ) ≤
        (1 - secSparsityF) * (Nat.choose (2 * (maxDegree G)^2) 2 : ℝ) := by
    intro v hv
    rw [fEdgesOn_lineGraphSq]
    exact hD₁ G _ hReg hgate hΔD₁ v hv
  have hX₀D : X₀ ≤ 2 * (maxDegree G)^2 := by
    have h := hΔX₀
    nlinarith
  have hcolF := hX (lineGraphSqFlag G) (maximalStrongF G (secFThreshold G))
    (2 * (maxDegree G)^2) hX₀D hSdeg hsparse
  obtain ⟨col, hcol_proper, hcol_lt⟩ :=
    chromaticNumberOn_witness (lineGraphSqFlag G) (maximalStrongF G (secFThreshold G))
  have hchiH : chromaticNumber (lineGraphSqFlag G) ≤
      max (chromaticNumberOn (lineGraphSqFlag G) (maximalStrongF G (secFThreshold G)))
        (secFThreshold G) := by
    apply chromaticNumber_le_of_maximalStrongF_colouring G (secFThreshold G) _
      (le_max_right _ _) col
    · exact fun i hi j hj hadj => hcol_proper i hi j hj hadj
    · exact fun i hi => lt_of_lt_of_le (hcol_lt i hi) (le_max_left _ _)
  have hbranch1 : ((chromaticNumberOn (lineGraphSqFlag G)
      (maximalStrongF G (secFThreshold G)) : ℕ) : ℝ) ≤ C * (maxDegree G : ℝ)^2 := by
    have hcast : ((2 * (maxDegree G)^2 : ℕ) : ℝ) = 2 * (maxDegree G : ℝ)^2 := by
      push_cast; ring
    have halg : (1 - colouringEps secSparsityF + iota) * (2 * (maxDegree G : ℝ)^2)
        = C * (maxDegree G : ℝ)^2 := by
      rw [hiota_def]; ring
    calc ((chromaticNumberOn (lineGraphSqFlag G)
          (maximalStrongF G (secFThreshold G)) : ℕ) : ℝ)
        ≤ (1 - colouringEps secSparsityF + iota) * ((2 * (maxDegree G)^2 : ℕ) : ℝ) := hcolF
      _ = C * (maxDegree G : ℝ)^2 := by rw [hcast, halg]
  have hbranch2 : ((secFThreshold G : ℕ) : ℝ) ≤ C * (maxDegree G : ℝ)^2 := by
    have h1 : 10000 * secFThreshold G ≤ 17297 * (maxDegree G)^2 + 9999 := by
      have ht : secFThreshold G = (17297 * (maxDegree G) ^ 2 + 9999) / 10000 := rfl
      omega
    have h2 : ((10000 * secFThreshold G : ℕ) : ℝ) ≤
        ((17297 * (maxDegree G)^2 + 9999 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    have h3 : (secFThreshold G : ℝ) ≤ 1.7297 * (maxDegree G : ℝ)^2 + 1 := by nlinarith
    linarith [hD₂ (maxDegree G) hΔD₂]
  calc (strongChromaticIndex G : ℝ)
      ≤ (chromaticNumber (lineGraphSqFlag G) : ℝ) := by
        exact_mod_cast strongChromaticIndex_le_lineGraphSq G
    _ ≤ ((max (chromaticNumberOn (lineGraphSqFlag G)
          (maximalStrongF G (secFThreshold G))) (secFThreshold G) : ℕ) : ℝ) := by
        exact_mod_cast hchiH
    _ ≤ C * (maxDegree G : ℝ)^2 := by
        rw [Nat.cast_max]
        exact max_le hbranch1 hbranch2

/-- The bipartite F-peeling threshold at η = 0.3746:
`t(Δ) = ⌈1.6254·Δ²⌉` in exact integers. -/
noncomputable def secBipFThreshold (G : Flag emptyType) : ℕ :=
  (16254 * (maxDegree G) ^ 2 + 9999) / 10000

/-- The bipartite peeled set satisfies the L2 gate. -/
lemma secBipFThreshold_gate (G : Flag emptyType) :
    ∀ e ∈ maximalStrongF G (secBipFThreshold G),
      16254 * (maxDegree G) ^ 2 ≤
        10000 * SecBridge.strongFDegree G (maximalStrongF G (secBipFThreshold G)) e := by
  intro e he
  have h := maximalStrongF_min_degree G (secBipFThreshold G) e he
  have ht : secBipFThreshold G = (16254 * (maxDegree G) ^ 2 + 9999) / 10000 := rfl
  omega

/-- **F-faithful combined bound (bipartite, Reg case)** — mirror of
`secF_combined_bound` at η = 0.3746 / `σ_F^bip`. -/
theorem secBipF_combined_bound_Reg (C : ℝ)
    (hC1 : (1 - colouringEps secBipartiteSparsityF) * 2 < C)
    (hC2 : (1.6254 : ℝ) < C) :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType, IsRegular G → IsBipartite G →
      D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ C * (maxDegree G : ℝ) ^ 2 := by
  set iota : ℝ := (C - (1 - colouringEps secBipartiteSparsityF) * 2) / 2 with hiota_def
  have hiota_pos : 0 < iota := by rw [hiota_def]; linarith
  obtain ⟨X₀, hX⟩ := hurley_colouring_scale secBipartiteSparsityF iota
    secBipartiteSparsityF_pos secBipartiteSparsityF_le_one hiota_pos
  obtain ⟨D₁, hD₁⟩ := secBipF_vertex_sparsity
  obtain ⟨D₂, hD₂⟩ : ∃ D₂ : ℕ, ∀ Δ : ℕ, D₂ ≤ Δ →
      1.6254 * (Δ:ℝ)^2 + 1 ≤ C * (Δ:ℝ)^2 := by
    refine ⟨Nat.ceil (1/(C - 1.6254)) + 1, fun Δ hΔ => ?_⟩
    have hpos : (0:ℝ) < C - 1.6254 := by linarith
    have h1 : (1/(C - 1.6254)) ≤ (Δ:ℝ) := by
      calc (1/(C - 1.6254)) ≤ (Nat.ceil (1/(C - 1.6254)) : ℝ) := Nat.le_ceil _
        _ ≤ (Δ : ℝ) := by exact_mod_cast le_trans (Nat.le_succ _) hΔ
    have hΔ1 : (1:ℝ) ≤ (Δ:ℝ) := by
      have : 1 ≤ Δ := by omega
      exact_mod_cast this
    have h2 : 1 ≤ (C - 1.6254) * (Δ:ℝ) := by
      rw [div_le_iff₀ hpos] at h1
      linarith
    nlinarith
  refine ⟨max (max D₁ X₀) (max D₂ 1), fun G hReg hBip hG => ?_⟩
  have hΔD₁ : D₁ ≤ maxDegree G := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hG
  have hΔX₀ : X₀ ≤ maxDegree G := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hG
  have hΔD₂ : D₂ ≤ maxDegree G := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hG
  have hΔ1 : 1 ≤ maxDegree G := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hG
  have hgate := secBipFThreshold_gate G
  have hSdeg : ∀ v ∈ maximalStrongF G (secBipFThreshold G),
      ((maximalStrongF G (secBipFThreshold G)).filter
        (fun i => (lineGraphSqFlag G).graph.Adj v i)).card ≤ 2 * (maxDegree G)^2 := by
    intro v _
    exact le_trans (strongFDegree_le_lineGraphSq_maxDegree G _ v)
      (lineGraphSq_maxDegree_le G)
  have hsparse : ∀ v ∈ maximalStrongF G (secBipFThreshold G),
      (fEdgesOn (lineGraphSqFlag G) (maximalStrongF G (secBipFThreshold G)) v : ℝ) ≤
        (1 - secBipartiteSparsityF) * (Nat.choose (2 * (maxDegree G)^2) 2 : ℝ) := by
    intro v hv
    rw [fEdgesOn_lineGraphSq]
    exact hD₁ G _ hReg hBip hgate hΔD₁ v hv
  have hX₀D : X₀ ≤ 2 * (maxDegree G)^2 := by
    have h := hΔX₀
    nlinarith
  have hcolF := hX (lineGraphSqFlag G) (maximalStrongF G (secBipFThreshold G))
    (2 * (maxDegree G)^2) hX₀D hSdeg hsparse
  obtain ⟨col, hcol_proper, hcol_lt⟩ :=
    chromaticNumberOn_witness (lineGraphSqFlag G) (maximalStrongF G (secBipFThreshold G))
  have hchiH : chromaticNumber (lineGraphSqFlag G) ≤
      max (chromaticNumberOn (lineGraphSqFlag G)
        (maximalStrongF G (secBipFThreshold G))) (secBipFThreshold G) := by
    apply chromaticNumber_le_of_maximalStrongF_colouring G (secBipFThreshold G) _
      (le_max_right _ _) col
    · exact fun i hi j hj hadj => hcol_proper i hi j hj hadj
    · exact fun i hi => lt_of_lt_of_le (hcol_lt i hi) (le_max_left _ _)
  have hbranch1 : ((chromaticNumberOn (lineGraphSqFlag G)
      (maximalStrongF G (secBipFThreshold G)) : ℕ) : ℝ) ≤ C * (maxDegree G : ℝ)^2 := by
    have hcast : ((2 * (maxDegree G)^2 : ℕ) : ℝ) = 2 * (maxDegree G : ℝ)^2 := by
      push_cast; ring
    have halg : (1 - colouringEps secBipartiteSparsityF + iota) * (2 * (maxDegree G : ℝ)^2)
        = C * (maxDegree G : ℝ)^2 := by
      rw [hiota_def]; ring
    calc ((chromaticNumberOn (lineGraphSqFlag G)
          (maximalStrongF G (secBipFThreshold G)) : ℕ) : ℝ)
        ≤ (1 - colouringEps secBipartiteSparsityF + iota) *
            ((2 * (maxDegree G)^2 : ℕ) : ℝ) := hcolF
      _ = C * (maxDegree G : ℝ)^2 := by rw [hcast, halg]
  have hbranch2 : ((secBipFThreshold G : ℕ) : ℝ) ≤ C * (maxDegree G : ℝ)^2 := by
    have h1 : 10000 * secBipFThreshold G ≤ 16254 * (maxDegree G)^2 + 9999 := by
      have ht : secBipFThreshold G = (16254 * (maxDegree G) ^ 2 + 9999) / 10000 := rfl
      omega
    have h2 : ((10000 * secBipFThreshold G : ℕ) : ℝ) ≤
        ((16254 * (maxDegree G)^2 + 9999 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    have h3 : (secBipFThreshold G : ℝ) ≤ 1.6254 * (maxDegree G : ℝ)^2 + 1 := by nlinarith
    linarith [hD₂ (maxDegree G) hΔD₂]
  calc (strongChromaticIndex G : ℝ)
      ≤ (chromaticNumber (lineGraphSqFlag G) : ℝ) := by
        exact_mod_cast strongChromaticIndex_le_lineGraphSq G
    _ ≤ ((max (chromaticNumberOn (lineGraphSqFlag G)
          (maximalStrongF G (secBipFThreshold G))) (secBipFThreshold G) : ℕ) : ℝ) := by
        exact_mod_cast hchiH
    _ ≤ C * (maxDegree G : ℝ)^2 := by
        rw [Nat.cast_max]
        exact max_le hbranch1 hbranch2

/-- **F-faithful combined bound (bipartite, unrestricted)**: the Reg case +
the WLOG-regular bipartite reduction (doubling preserves bipartiteness). -/
theorem secBipF_combined_bound (C : ℝ)
    (hC1 : (1 - colouringEps secBipartiteSparsityF) * 2 < C)
    (hC2 : (1.6254 : ℝ) < C) :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType, IsBipartite G → D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ C * (maxDegree G : ℝ) ^ 2 := by
  obtain ⟨D₀, hD₀⟩ := secBipF_combined_bound_Reg C hC1 hC2
  refine ⟨D₀, fun G hBip hG => ?_⟩
  obtain ⟨G', hReg', hBip', hΔ', hChi'⟩ :=
    Davey2024.Reductions.WLOGRegular.sec_bipartite_regular_suffices G hBip
  have hG' : D₀ ≤ maxDegree G' := by rw [hΔ']; exact hG
  have h1 : (strongChromaticIndex G : ℝ) ≤ (strongChromaticIndex G' : ℝ) := by
    exact_mod_cast hChi'
  have h2 := hD₀ G' hReg' hBip' hG'
  rw [hΔ'] at h2
  linarith

/-- **Theorem 4.1 (Main Result, Reg case — F-faithful rebuild)**:
`χ'_s(G) ≤ 1.74·Δ(G)²` for regular `G` with Δ large, via the two-branch
F-route (peel at η = 0.2703, padded Hurley at D = 2Δ², degeneracy greedy). -/
theorem strong_chromatic_index_bound_Reg_F :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      IsRegular G → D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ 1.74 * (maxDegree G : ℝ) ^ 2 :=
  secF_combined_bound 1.74
    (lt_trans secF_colouring_factor_lt (by norm_num))
    (by norm_num)

end SecFConsumer

/-- **Theorem 4.1 (Main Result, unrestricted)**: For every graph `G` with
    Δ(G) sufficiently large: `χ'_s(G) ≤ 1.74·Δ(G)²`.

    Thesis-faithful in structure (Theorem 4.1 applied to all graphs, no
    regularity hypothesis). The constant is 1.74 (not the thesis's 1.73):
    the 2026-05-14 refactor eliminated the strict-bound axiom
    `phi_evalAlg_O_sec_alg_le_bound_strict` by absorbing its `1/10000`
    L-space buffer into a `1/200` σ-space shift, at the cost of moving the
    headline constant from 1.73 to 1.74.

    Proof: combine the cert-driven Reg case `strong_chromatic_index_bound_Reg_F`
    (depending on the F-faithful SEC bridge and SDP certificate) with the
    reduction theorem `strong_chromatic_index_Reg_suffices` (capturing the
    classical "WLOG regular" reduction of thesis §4.1). -/
theorem strong_chromatic_index_bound :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ 1.74 * (maxDegree G : ℝ) ^ 2 :=
  -- (B1 repair, Phase L3.4(d), 2026-07-11: rewired from the old
  -- `strong_chromatic_index_bound_Reg` chain — which consumed the refuted
  -- identity axiom — to the F-faithful `strong_chromatic_index_bound_Reg_F`.)
  strong_chromatic_index_Reg_suffices 1.74 strong_chromatic_index_bound_Reg_F

/-! ## §4.5d: Bipartite main theorems -/

/-- **Theorem 4.9 (Bipartite Case)**: For bipartite G with Δ(G) sufficiently large:
    `χ'_s(G) ≤ 1.63·Δ(G)²`.

    Note: The thesis achieves 1.6254Δ² exactly. The formalization's value rose
    from 1.6255 (= 1.6254 + 0.0001 ι-slack) to 1.63 in the 2026-05-14
    constant-relaxation refactor, which absorbed the strict-bound axiom's
    `1/10000` L-space buffer into a `1/200` shift in `secBipartiteSparsity`. -/
theorem strong_chromatic_index_bipartite :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      IsBipartite G → D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ 1.63 * (maxDegree G : ℝ) ^ 2 :=
  -- (B1 repair, Phase L3.4(d), 2026-07-11: rewired to the F-faithful chain.)
  secBipF_combined_bound 1.63
    (lt_trans secBipF_colouring_factor_lt (by norm_num))
    (by norm_num)

/-! ## Historical Bounds (unrestricted)

All four bounds below are looser corollaries of the headline
`strong_chromatic_index_bound`, restated for citation parity with the
thesis. Each is now unrestricted (no TF or regularity hypotheses) to
match the original statements in the cited papers. -/

/-- Molloy-Reed (1997): `χ'_s(G) ≤ 1.998·Δ(G)²` for large Δ.
    Follows from `strong_chromatic_index_bound`. -/
theorem molloy_reed_1997 :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ 1.998 * (maxDegree G : ℝ) ^ 2 := by
  obtain ⟨D₀, hD⟩ := strong_chromatic_index_bound
  exact ⟨D₀, fun G hG =>
    le_trans (hD G hG) (by nlinarith [sq_nonneg (maxDegree G : ℝ)])⟩

/-- Bruhn-Joos (2015): `χ'_s(G) ≤ 1.93·Δ(G)²` for large Δ. -/
theorem bruhn_joos_2015 :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ 1.93 * (maxDegree G : ℝ) ^ 2 := by
  obtain ⟨D₀, hD⟩ := strong_chromatic_index_bound
  exact ⟨D₀, fun G hG =>
    le_trans (hD G hG) (by nlinarith [sq_nonneg (maxDegree G : ℝ)])⟩

/-- Bonamy-Perrett-Postle (2018): `χ'_s(G) ≤ 1.835·Δ(G)²` for large Δ. -/
theorem bonamy_perrett_postle_2018 :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ 1.835 * (maxDegree G : ℝ) ^ 2 := by
  obtain ⟨D₀, hD⟩ := strong_chromatic_index_bound
  exact ⟨D₀, fun G hG =>
    le_trans (hD G hG) (by nlinarith [sq_nonneg (maxDegree G : ℝ)])⟩

/-- Hurley-de Joannis de Verclos-Kang (2022): `χ'_s(G) ≤ 1.772·Δ(G)²` for large Δ. -/
theorem hurley_kang_2022 :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ 1.772 * (maxDegree G : ℝ) ^ 2 := by
  obtain ⟨D₀, hD⟩ := strong_chromatic_index_bound
  exact ⟨D₀, fun G hG =>
    le_trans (hD G hG) (by nlinarith [sq_nonneg (maxDegree G : ℝ)])⟩

/-! ## §4.10: Thesis-tight headlines (1.73 / 1.6255)

The thesis-published constants 1.73 (Theorem 4.1) and 1.6255 (Theorem 4.9).

**B1 repair note (gate L2(d), 2026-07-11):** the pre-repair thesis-tight path
re-introduced the strict-bound axioms (`phi_evalAlg_O_sec_alg_le_bound_strict`
and bipartite analog). Those strict axioms were found to be artefact-unsupported
and were DROPPED; the F-faithful loose bounds already close the thesis constants
(`(1 − ε(σ_F))·2 < 1.72992 < 1.73`, bipartite `< 1.62547 < 1.6255`). So the
thesis-tight headlines below now share the SAME F-faithful axiom set as the
default headlines — the only difference is the numeric constant in the statement. -/

/-- **Theorem 4.1 (thesis-tight, unrestricted)**: `χ'_s(G) ≤ 1.73·Δ(G)²`.

Proved from the F-faithful loose bound (no strict axiom); the close is
`(1 − ε(σ_F))·2 < 1.72992 < 1.73`. Use this when thesis-faithfulness
is required; otherwise the default `strong_chromatic_index_bound`
at `≤ 1.74·Δ²` is equivalent (same axiom set, slightly looser constant). -/
theorem strong_chromatic_index_bound_thesis_tight :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ 1.73 * (maxDegree G : ℝ) ^ 2 :=
  -- (B1 repair, Phase L3.4(d), 2026-07-11: now proved from the LOOSE bound
  -- alone — no strict axiom exists any more (gate L2(d)); the close is
  -- (1 − ε(σ_F))·2 < 1.72992 < 1.73, the development notes §6b.)
  strong_chromatic_index_Reg_suffices 1.73
    (secF_combined_bound 1.73
      (lt_trans secF_colouring_factor_lt (by norm_num))
      (by norm_num))

/-! ### Bipartite thesis-tight chain -/

/-- **Theorem 4.9 (thesis-tight)**: `χ'_s(G) ≤ 1.6255·Δ(G)²` for bipartite G.

Proved from the F-faithful loose bound (no strict axiom, gate L2(d)); the
close is `(1 − ε(σ_F^bip))·2 < 1.62547 < 1.6255`, recovering the
thesis-published constant 1.6255. -/
theorem strong_chromatic_index_bipartite_thesis_tight :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      IsBipartite G → D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ 1.6255 * (maxDegree G : ℝ) ^ 2 :=
  -- (B1 repair, Phase L3.4(d), 2026-07-11: now proved from the LOOSE bound
  -- alone — no strict axiom (gate L2(d)); close: (1 − ε(σ_F^bip))·2 <
  -- 1.62547 < 1.6255, max-branch 1.6254 < 1.6255.)
  secBipF_combined_bound 1.6255
    (lt_trans secBipF_colouring_factor_lt (by norm_num))
    (by norm_num)

/-! ## §8 (Paper 2): Asymmetric bipartite case

The §8 asymmetric bipartite case (paper L1983-L2139): for
`p ∈ (0, 1]`, an asymmetric-bipartite graph `G = A ⊔ B` with `A`
`Δ`-regular and `B` degree `≤ pΔ` satisfies
`χ'_s(G) ≤ 1.6632·p·Δ²` (paper Theorem 2.17), relaxed to the uniform
`1.6633·Δ²` via `p ≤ 1`.

**Route 1 (B1 R1b repair, 2026-07-12).** The asymmetric problem is
F-free / all-vertex by design (thesis §4.6, Molloy–Reed). The sound
per-vertex density bound is proved at `p = 1` on a regular bipartite
blow-up via the F-free CG4 cert (`SecAsymBridgeF.secAsymF_p1_vertex_bound`)
and carried to general `p` per-graph by the proven blow-up transfer
(`SecAsymBlowup.blowup_transfer_uncond`), giving the all-vertex sparsity
`secAsymF_biregular_vertex_bound` at the clean Nat scale `D = 2⌊pΔ⌋Δ`. The
degree-scale Hurley lemma (`secAsymF_scale_colouring`) at
`σ_p ≈ 0.4312` then closes the three headlines. Sound axiom set: the
three CG4 `_F` axioms (identity, eval bound, locality) plus
`hurley_colouring_lemma` (verified via `AxiomCheck.lean`).

The earlier general-`p` CG22 SDP-limit chain — with a per-`G`
combinatorial-identity axiom (FALSE for general `p`), a vacuous
eval-bound axiom, its strict variant, and a CG22 regularity axiom —
was retired here and in `SecAsymmetricBipartiteBridge`.
-/

open Davey2024.SecAsymmetricBipartiteBridge
open Davey2024.SecAsymReduction

/-! ### §8 (Route 1) — F-free asymmetric chain via the CG4 `p = 1` bound + transfer

The asymmetric SEC headlines now route through the sound `p = 1` CG4 arm
(`SecAsymBridgeF`) carried to general `p` per-graph by the proven blow-up
transfer. `secAsymF_biregular_vertex_bound` supplies, per host `G`, a clean Nat
scale `D = 2⌊pΔ⌋Δ` with `Δ(L(G)²) ≤ D ≤ 2pΔ²` and all-vertex sparsity
`eIN ≤ (1−σ)·C(D,2)`. Feeding that into the degree-scale Hurley lemma at
`S = univ` yields the chromatic bound. The old general-`p` SDP-limit chain
(false/vacuous CG22 axioms) is retired. -/

/-- `chromaticNumberOn` over the full vertex set is the ordinary chromatic
number (the two defining infima range over identical sets). -/
theorem chromaticNumberOn_univ (H : Flag emptyType) :
    chromaticNumberOn H Finset.univ = chromaticNumber H := by
  unfold chromaticNumberOn chromaticNumber
  congr 1
  ext k
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨col, hproper, hlt⟩
    exact ⟨col, fun u v hadj => hproper u (Finset.mem_univ u) v (Finset.mem_univ v) hadj,
      fun v => hlt v (Finset.mem_univ v)⟩
  · rintro ⟨col, hproper, hlt⟩
    exact ⟨col, fun i _ j _ hadj => hproper i j hadj, fun i _ => hlt i⟩

/-- `fEdgesOn` over the full vertex set is `edgesInNeighbourhood` (same filter
shapes; definitional). -/
theorem fEdgesOn_univ (H : Flag emptyType) (v : Fin H.size) :
    fEdgesOn H Finset.univ v = edgesInNeighbourhood H v := rfl

/-- **Route-1 asymmetric colouring core.** For every `p ∈ (0,1]` and `ι > 0`,
every `p`-asymmetric-bipartite `G` with `Δ` large has
`χ'_s(G) ≤ (1 − ε(σ_p) + ι)·2pΔ²`. The all-vertex generic-normalizer sparsity
(`secAsymF_biregular_vertex_bound`, at Nat scale `D = 2⌊pΔ⌋Δ ≤ 2pΔ²`) feeds the
degree-scale Hurley lemma with `S = univ`. -/
theorem secAsymF_scale_colouring (p : ℝ) (hp1 : 0 < p) (hp2 : p ≤ 1)
    (iota : ℝ) (hiota : 0 < iota) :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      IsBiregularFloor p G → D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤
        (1 - colouringEps secAsymBipartiteSparsity + iota) *
          (2 * p * (maxDegree G : ℝ) ^ 2) := by
  obtain ⟨X₀, hX⟩ := hurley_colouring_scale secAsymBipartiteSparsity iota
    secAsymBipartiteSparsity_pos secAsymBipartiteSparsity_le_one hiota
  obtain ⟨D₁, hD₁⟩ := secAsymF_biregular_vertex_bound p hp1 hp2
  refine ⟨max D₁ X₀, fun G hbireg hG => ?_⟩
  have hGD₁ : D₁ ≤ maxDegree G := le_trans (le_max_left _ _) hG
  have hGX₀ : X₀ ≤ maxDegree G := le_trans (le_max_right _ _) hG
  obtain ⟨D, hGD, hHD, hDle, hDsparse⟩ := hD₁ G hbireg hGD₁
  have hX₀D : X₀ ≤ D := le_trans hGX₀ hGD
  have hSdeg : ∀ v ∈ (Finset.univ : Finset (Fin (lineGraphSqFlag G).size)),
      ((Finset.univ : Finset (Fin (lineGraphSqFlag G).size)).filter
        (fun i => (lineGraphSqFlag G).graph.Adj v i)).card ≤ D :=
    fun v _ => le_trans (degree_le_maxDegree (lineGraphSqFlag G) v) hHD
  have hsparse : ∀ v ∈ (Finset.univ : Finset (Fin (lineGraphSqFlag G).size)),
      (fEdgesOn (lineGraphSqFlag G) Finset.univ v : ℝ) ≤
        (1 - secAsymBipartiteSparsity) * (Nat.choose D 2 : ℝ) := by
    intro v _
    rw [fEdgesOn_univ]
    exact hDsparse v
  have hcol := hX (lineGraphSqFlag G) Finset.univ D hX₀D hSdeg hsparse
  rw [chromaticNumberOn_univ] at hcol
  have hcoeff_nn : (0 : ℝ) ≤ 1 - colouringEps secAsymBipartiteSparsity + iota := by
    have h : colouringEps secAsymBipartiteSparsity ≤ secAsymBipartiteSparsity / 2 := by
      unfold colouringEps
      linarith [mul_nonneg (le_of_lt secAsymBipartiteSparsity_pos)
        (Real.sqrt_nonneg secAsymBipartiteSparsity)]
    linarith [secAsymBipartiteSparsity_le_one, le_of_lt hiota]
  calc (strongChromaticIndex G : ℝ)
      ≤ (chromaticNumber (lineGraphSqFlag G) : ℝ) := by
        exact_mod_cast strongChromaticIndex_le_lineGraphSq G
    _ ≤ (1 - colouringEps secAsymBipartiteSparsity + iota) * (D : ℝ) := hcol
    _ ≤ (1 - colouringEps secAsymBipartiteSparsity + iota) *
          (2 * p * (maxDegree G : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hDle hcoeff_nn

/-- **Theorem 2.17 (Paper 2 §8) — Asymmetric bipartite strong chromatic
index bound (TIGHT, Route 1)**: For every $p \in (0, 1]$, every
$p$-asymmetric-bipartite graph $G$ with $\Delta(G)$ sufficiently large
satisfies
$$\chi'_s(G) \leq 1.6633 \cdot \Delta(G)^2.$$

Route 1: the sound F-free CG4 `p = 1` per-vertex bound
(`secAsymF_p1_vertex_bound`) is carried to general `p` per-graph by the
proven blow-up transfer (`secAsymF_biregular_vertex_bound`), then coloured by
the degree-scale Hurley lemma at the asymmetric sparsity
$\sigma_p \approx 0.4312$ (`secAsymF_scale_colouring`). The general-`p`
CG22 SDP-limit axioms (false identity + vacuous eval bound) are retired;
the chain now rests only on the three sound CG4 `_F` axioms plus
`hurley_colouring_lemma`. Instantiating $\iota = 4\cdot 10^{-5}$ and using
$p \le 1$ relaxes the per-$p$ bound to the uniform headline. -/
theorem strong_chromatic_index_asymmetric_bipartite_tight
    (p : ℝ) (_hp1 : 0 < p) (_hp2 : p ≤ 1) :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      IsAsymmetricBipartite p G → D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ 1.6633 * (maxDegree G : ℝ) ^ 2 := by
  -- (B1 repair, Phase L5.R2, 2026-07-12: the p-FREE constant `1.6633·Δ²`
  -- needs no asymmetric identity — it is implied by the sound symmetric
  -- bipartite bound `strong_chromatic_index_bipartite_thesis_tight`
  -- (`≤ 1.6255·Δ²`) since an asymmetric-bipartite graph is bipartite and
  -- `1.6255 ≤ 1.6633`. The per-`p` `1.6632·p·Δ²` form (which genuinely
  -- needs the p-factor) remains `..._thesis_tight`. The ratio `p` and its
  -- bounds are irrelevant here.)
  obtain ⟨D₀, hD₀⟩ := strong_chromatic_index_bipartite_thesis_tight
  refine ⟨D₀, fun G hAsym hG => ?_⟩
  have h := hD₀ G hAsym.isBipartite hG
  nlinarith [h, sq_nonneg (maxDegree G : ℝ)]

/-- **Asymmetric bipartite headline (loose corollary of the bipartite
thesis-tight bound)**: for every $p \in (0, 1]$, every
$p$-asymmetric-bipartite graph with large Δ satisfies
$\chi'_s(G) \le 1.6633 \cdot \Delta(G)^2$.

Since `strong_chromatic_index_asymmetric_bipartite_tight` gives
`≤ 1.6633·Δ²` via the sound symmetric bipartite path
(`strong_chromatic_index_bipartite_thesis_tight`, `≤ 1.6255·Δ²`), this
theorem is a direct alias. It carries **no** asymmetric identity axiom.
Retained for backward citation parity.

**Constant note**: this is `1.6633·Δ²` rather than the paper's
`1.6632·p·Δ²`; see
`strong_chromatic_index_asymmetric_bipartite_thesis_tight` for the
per-$p$ paper-exact form. -/
theorem strong_chromatic_index_asymmetric_bipartite
    (p : ℝ) (hp1 : 0 < p) (hp2 : p ≤ 1) :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      IsAsymmetricBipartite p G → D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ 1.6633 * (maxDegree G : ℝ) ^ 2 :=
  strong_chromatic_index_asymmetric_bipartite_tight p hp1 hp2

/-- **Theorem 2.17 (Paper 2 §8) — Asymmetric bipartite thesis-tight
headline**: For every $p \in (0, 1]$, every $p$-asymmetric-bipartite
graph $G$ with $\Delta(G)$ sufficiently large satisfies
$$\chi'_s(G) \leq 1.6632 \cdot p \cdot \Delta(G)^2.$$

This is the **paper-exact constant** of Paper 2 Theorem 2.17. Under
Route 1 it closes from the loose colouring core **without any strict
cert axiom**: `secAsymF_scale_colouring` gives
`χ'_s ≤ (1 − ε(σ_p) + ι)·2pΔ²`, and choosing the fixed
`ι = (1.6632 − (1−ε(σ_p))·2)/2 > 0` (positive by
`sec_asym_bipartite_colouring_factor_lt`) makes `(1−ε(σ_p)+ι)·2 = 1.6632`
exactly, so the strict `(1−ε(σ_p))·2 < 1.6632` slack is precisely what
absorbs `ι`. -/
theorem sec_asym_thesis_tight_biregular
    (p : ℝ) (hp1 : 0 < p) (hp2 : p ≤ 1) :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      IsBiregularFloor p G → D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ 1.6632 * p * (maxDegree G : ℝ) ^ 2 := by
  have hlt := sec_asym_bipartite_colouring_factor_lt
  obtain ⟨D₀, hD₀⟩ := secAsymF_scale_colouring p hp1 hp2
    ((1.6632 - (1 - colouringEps secAsymBipartiteSparsity) * 2) / 2) (by linarith)
  refine ⟨D₀, fun G hbireg hG => ?_⟩
  have h := hD₀ G hbireg hG
  calc (strongChromaticIndex G : ℝ)
      ≤ (1 - colouringEps secAsymBipartiteSparsity +
          (1.6632 - (1 - colouringEps secAsymBipartiteSparsity) * 2) / 2) *
          (2 * p * (maxDegree G : ℝ) ^ 2) := h
    _ = 1.6632 * p * (maxDegree G : ℝ) ^ 2 := by ring

/-- **Theorem 2.17 (Paper 2 §8) — Asymmetric bipartite thesis-tight
headline (general host, Route 1)**: For every $p \in (0, 1]$, every
$p$-asymmetric-bipartite graph $G$ with $\Delta(G)$ sufficiently large
satisfies
$$\chi'_s(G) \leq 1.6632 \cdot p \cdot \Delta(G)^2.$$

This is the **paper-exact per-$p$ constant** of Paper 2 Theorem 2.17,
stated for all `IsAsymmetricBipartite p G` (byte-identical in shape to the
two sibling headlines). It widens the biregular-narrowed helper
`sec_asym_thesis_tight_biregular` back to arbitrary asymmetric-bipartite
hosts via the **WLOG-biregular reduction** (`asym_biregular_reduction`,
`SecAsymReduction`): the exact `(Δ, ⌊pΔ⌋)`-biregular completion
`H = biregularCompletion G S ⌊pΔ⌋` satisfies `IsBiregularFloor p H`,
`Δ(H) = Δ(G)`, and `χ'ₛ(G) ≤ χ'ₛ(H)` (copy-0 induced embedding + χ'ₛ
monotonicity). The `Δ ≥ ⌈1/p⌉` gate forces `⌊pΔ⌋ ≥ 1`. -/
theorem strong_chromatic_index_asymmetric_bipartite_thesis_tight
    (p : ℝ) (hp1 : 0 < p) (hp2 : p ≤ 1) :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      Davey2024.SecAsymHighSide.IsAsymmetricBipartiteMaxDeg p G → D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ 1.6632 * p * (maxDegree G : ℝ) ^ 2 := by
  obtain ⟨D₀b, hb⟩ := sec_asym_thesis_tight_biregular p hp1 hp2
  refine ⟨max D₀b (Nat.ceil (1 / p)), fun G hMax hG => ?_⟩
  have hGD₀b : D₀b ≤ maxDegree G := le_trans (le_max_left _ _) hG
  have hGceil : Nat.ceil (1 / p) ≤ maxDegree G := le_trans (le_max_right _ _) hG
  -- `pΔ ≥ 1` from `Δ ≥ ⌈1/p⌉` (mirrors `secAsymF_biregular_vertex_bound`).
  have hpΔ1 : (1 : ℝ) ≤ p * (maxDegree G : ℝ) := by
    have h1 : (1 : ℝ) / p ≤ (maxDegree G : ℝ) := by
      calc (1 : ℝ) / p ≤ (Nat.ceil (1 / p) : ℝ) := Nat.le_ceil _
        _ ≤ (maxDegree G : ℝ) := by exact_mod_cast hGceil
    rw [div_le_iff₀ hp1] at h1; linarith
  -- HIGH-SIDE completion: `IsAsymmetricBipartiteMaxDeg p G` → `IsAsymmetricBipartite p G'`
  -- (high side exactly `Δ`-regular), same `Δ`, `χ'ₛ(G) ≤ χ'ₛ(G')`.
  obtain ⟨G', hG'asym, hG'max, hG'mono⟩ :=
    Davey2024.SecAsymHighSide.highSide_reduction p hp1 hp2 G hMax hpΔ1
  have hG'D₀b : D₀b ≤ maxDegree G' := by rw [hG'max]; exact hGD₀b
  have hpΔ1' : (1 : ℝ) ≤ p * (maxDegree G' : ℝ) := by rw [hG'max]; exact hpΔ1
  have ha1 : 1 ≤ Nat.floor (p * (maxDegree G' : ℝ)) :=
    Nat.le_floor (by exact_mod_cast hpΔ1')
  obtain ⟨H, hHbf, hHmax, hmono⟩ := asym_biregular_reduction p hp1 hp2 G' hG'asym ha1
  have hD₀bH : D₀b ≤ maxDegree H := by rw [hHmax]; exact hG'D₀b
  have hbH := hb H hHbf hD₀bH
  calc (strongChromaticIndex G : ℝ)
      ≤ (strongChromaticIndex G' : ℝ) := by exact_mod_cast hG'mono
    _ ≤ (strongChromaticIndex H : ℝ) := by exact_mod_cast hmono
    _ ≤ 1.6632 * p * (maxDegree H : ℝ) ^ 2 := hbH
    _ = 1.6632 * p * (maxDegree G : ℝ) ^ 2 := by rw [hHmax, hG'max]

/-- **Asymmetric thesis-tight headline, high-side-regular corollary** (old
`IsAsymmetricBipartite`-hypothesis form). Immediate from the max-degree headline
`strong_chromatic_index_asymmetric_bipartite_thesis_tight` via
`IsAsymmetricBipartite.toMaxDeg` (drop the high-side degree-equality clause).
Retained for backward citation parity. -/
theorem strong_chromatic_index_asymmetric_bipartite_thesis_tight_regular
    (p : ℝ) (hp1 : 0 < p) (hp2 : p ≤ 1) :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      IsAsymmetricBipartite p G → D₀ ≤ maxDegree G →
      (strongChromaticIndex G : ℝ) ≤ 1.6632 * p * (maxDegree G : ℝ) ^ 2 := by
  obtain ⟨D₀, hD₀⟩ := strong_chromatic_index_asymmetric_bipartite_thesis_tight p hp1 hp2
  exact ⟨D₀, fun G hAsym hG => hD₀ G (Davey2024.SecAsymHighSide.IsAsymmetricBipartite.toMaxDeg hAsym) hG⟩


end  -- noncomputable section

end Davey2024

