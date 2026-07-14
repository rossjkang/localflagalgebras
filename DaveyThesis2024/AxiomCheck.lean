import DaveyThesis2024.PentagonBound
import DaveyThesis2024.PentagonDelta3
import DaveyThesis2024.PentagonDelta3Unique
import DaveyThesis2024.PentagonDelta4
import DaveyThesis2024.PentagonDelta4Witness
import DaveyThesis2024.StrongChromaticIndex
import DaveyThesis2024.InducedMatchingAsymmetric
import DaveyThesis2024.SECRandomBipartite
import DaveyThesis2024.SecRandomBipartite.PairPacking
import DaveyThesis2024.SecRandomBipartite.PairPackingConcentration
import DaveyThesis2024.SecRandomBipartite.Closure
import DaveyThesis2024.SecRandomBipartite.PippengerSpencer
import DaveyThesis2024.BipartiteOmegaL2

/-!
# Axiom hygiene check

Guards the axiom sets of the four main theorems plus the two
`_thesis_tight` variants. If anything causes a set to change (e.g.
someone accidentally introduces a new axiom dependency, or refactors
in a way that pulls in an extra `sorryAx`), the `#guard_msgs` checks
below will fail and the build breaks.

This file is built as part of the standard `lake build` (since it sits
inside `DaveyThesis2024/`), so CI just needs `lake build` to enforce
the hygiene. No external script needed.

Last verified: 2026-07-11 (B1 repair L4.1) on branch `sec-f-faithful-fix`.
The four deterministic SEC headlines now route through the F-faithful
axiom sets (`sec_combinatorial_identity_F`, `phi_evalAlg_O_sec_alg_le_bound_F`,
`flagBasis_sec_isLocalFlag_F`, plus bipartite twins) after the B1
inconsistency (`sec_combinatorial_identity_step1`) was retired.
-/

namespace Davey2024

/-- info: 'Davey2024.pentagon_bound_full' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound,
 Davey2024.PentagonQBridge.pentagonQ_basis_combinatorial_identity_step1,
 Davey2024.PentagonQBridge.phi_evalAlg_O_Q_alg_le_bound] -/
#guard_msgs in
#print axioms pentagon_bound_full

/-- info: 'Davey2024.pentagon_bound_simple' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound] -/
#guard_msgs in
#print axioms pentagon_bound_simple

/-- info: 'Davey2024.strong_chromatic_index_bound' depends on axioms: [propext,
 Classical.choice,
 Davey2024.hurley_colouring_lemma,
 Quot.sound,
 Davey2024.SecBridge.flagBasis_sec_isLocalFlag_F,
 Davey2024.SecBridge.phi_evalAlg_O_sec_alg_le_bound_F,
 Davey2024.SecBridge.sec_combinatorial_identity_F] -/
#guard_msgs in
#print axioms strong_chromatic_index_bound

/-- info: 'Davey2024.strong_chromatic_index_bipartite' depends on axioms: [propext,
 Classical.choice,
 Davey2024.hurley_colouring_lemma,
 Quot.sound,
 Davey2024.SecBipartiteBridge.flagBasis_sec_bip_isLocalFlag_F,
 Davey2024.SecBipartiteBridge.phi_evalAlg_O_sec_bip_alg_le_bound_F,
 Davey2024.SecBipartiteBridge.sec_combinatorial_identity_bipartite_F] -/
#guard_msgs in
#print axioms strong_chromatic_index_bipartite

/-- info: 'Davey2024.strong_chromatic_index_bound_thesis_tight' depends on axioms: [propext,
 Classical.choice,
 Davey2024.hurley_colouring_lemma,
 Quot.sound,
 Davey2024.SecBridge.flagBasis_sec_isLocalFlag_F,
 Davey2024.SecBridge.phi_evalAlg_O_sec_alg_le_bound_F,
 Davey2024.SecBridge.sec_combinatorial_identity_F] -/
#guard_msgs in
#print axioms strong_chromatic_index_bound_thesis_tight

/-- info: 'Davey2024.strong_chromatic_index_bipartite_thesis_tight' depends on axioms: [propext,
 Classical.choice,
 Davey2024.hurley_colouring_lemma,
 Quot.sound,
 Davey2024.SecBipartiteBridge.flagBasis_sec_bip_isLocalFlag_F,
 Davey2024.SecBipartiteBridge.phi_evalAlg_O_sec_bip_alg_le_bound_F,
 Davey2024.SecBipartiteBridge.sec_combinatorial_identity_bipartite_F] -/
#guard_msgs in
#print axioms strong_chromatic_index_bipartite_thesis_tight

-- After the B1 L5 repair (2026-07-12): the two p-FREE §8 asymmetric
-- headlines (`≤ 1.6633·Δ²`) are implied by the sound symmetric bipartite
-- bound (an asymmetric-bipartite graph is bipartite; `1.6255 ≤ 1.6633`),
-- so they depend only on the sound BIPARTITE `_F` axioms + Hurley — NOT
-- on any asymmetric identity. Only the p-factor thesis-tight headline
-- (`1.6632·p·Δ²`) uses the asymmetric CG4 arm, whose identity axiom
-- `sec_combinatorial_identity_asymmetric_F` is now soundly gated on
-- genuine `IsRegular` (via the WLOG-biregular reduction) — no longer the
-- false `IsAsymmetricBipartite 1`-only gate.

/-- info: 'Davey2024.strong_chromatic_index_asymmetric_bipartite_tight' depends on axioms: [propext,
 Classical.choice,
 Davey2024.hurley_colouring_lemma,
 Quot.sound,
 Davey2024.SecBipartiteBridge.flagBasis_sec_bip_isLocalFlag_F,
 Davey2024.SecBipartiteBridge.phi_evalAlg_O_sec_bip_alg_le_bound_F,
 Davey2024.SecBipartiteBridge.sec_combinatorial_identity_bipartite_F] -/
#guard_msgs in
#print axioms strong_chromatic_index_asymmetric_bipartite_tight

/-- info: 'Davey2024.strong_chromatic_index_asymmetric_bipartite' depends on axioms: [propext,
 Classical.choice,
 Davey2024.hurley_colouring_lemma,
 Quot.sound,
 Davey2024.SecBipartiteBridge.flagBasis_sec_bip_isLocalFlag_F,
 Davey2024.SecBipartiteBridge.phi_evalAlg_O_sec_bip_alg_le_bound_F,
 Davey2024.SecBipartiteBridge.sec_combinatorial_identity_bipartite_F] -/
#guard_msgs in
#print axioms strong_chromatic_index_asymmetric_bipartite

-- Asymmetric thesis-tight headline: paper-exact constant 1.6632·p·Δ².
-- Uses the asymmetric CG4 arm; identity now soundly gated on `IsRegular`.

/-- info: 'Davey2024.strong_chromatic_index_asymmetric_bipartite_thesis_tight' depends on axioms: [propext,
 Classical.choice,
 Davey2024.hurley_colouring_lemma,
 Quot.sound,
 Davey2024.SecAsymmetricBipartiteBridge.flagBasis_asym_isLocalFlag_F,
 Davey2024.SecAsymmetricBipartiteBridge.phi_evalAlg_O_asym_CG4_le_bound,
 Davey2024.SecAsymmetricBipartiteBridge.sec_combinatorial_identity_asymmetric_F] -/
#guard_msgs in
#print axioms strong_chromatic_index_asymmetric_bipartite_thesis_tight

-- FGST 1989 Theorem 1, asymmetric reading: bipartite ν_s lower bound.
-- Depends only on the three standard Lean axioms; no project user axioms.

/-- info: 'Davey2024.edges_le_nu_s_mul_mul_bipartite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms edges_le_nu_s_mul_mul_bipartite

/-- info: 'Davey2024.edges_le_nu_s_mul_sq_bipartite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms edges_le_nu_s_mul_sq_bipartite

-- Asymmetric Śleszyńska-Nowak: ω(L(G)²) ≤ Δ_A·Δ_B (and ≤ Δ²) for bipartite G
-- (Paper 2, asymmetric clique number). Both depend only on the three standard
-- Lean axioms; no project user axioms. Guarded here so the result stays
-- axiom-hygiene checked alongside the headlines.

/-- info: 'Davey2024.omega_lineGraphSq_le_mul_bipartite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms omega_lineGraphSq_le_mul_bipartite

/-- info: 'Davey2024.omega_lineGraphSq_le_sq_bipartite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms omega_lineGraphSq_le_sq_bipartite

end Davey2024

-- Paper-3: asymmetric SEC for random bipartite (a.a.s.).
-- Monolithic axiom is being decomposed (Phase P.A done 2026-06-01) into
-- atomic axioms (deltaA/deltaB concentration, nibble quantitative bound,
-- intersection bound). Main theorem is temporarily sorry'd until Phase
-- P.D combines them. See the development notes.

-- Structural arithmetic lemma: zero domain axioms (unchanged through decomposition).

/-- info: 'SECRandomBipartite.delta1_le_deltaA_mul_deltaB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SECRandomBipartite.delta1_le_deltaA_mul_deltaB

-- Paper-3 concentration theorems (Cycles 34 + 35, 2026-06-01; Phase B 2026-06-02):
-- deltaA/deltaB concentration proved as Lean theorems. Phase B eliminated the
-- two edgeIndicator independence axioms by exhibiting the bipartite edge-choice
-- PMF as a literal `Measure.pi` and invoking `iIndepFun_pi`. The concentration
-- proofs now depend only on the standard Lean axioms.

/-- info: 'SECRandomBipartite.deltaA_concentration_proof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SECRandomBipartite.deltaA_concentration_proof

/-- info: 'SECRandomBipartite.deltaB_concentration_proof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SECRandomBipartite.deltaB_concentration_proof

-- Main theorem (Phase P.D completed, sorry filled; Phase B 2026-06-02 reduced
-- axiom set). SOUNDNESS FIX (2026-06-18, I4 delete): `secRandomBipartite_aas`
-- resolves to the B–Q a.a.s. headline proved from the SOUND, verbatim literature
-- axioms (`kim_vu_concentration_verbatim` + `pippenger_spencer_covering_verbatim`),
-- replacing the former FKS-route proof that depended on the INCONSISTENT
-- `kim_vu_concentration_for_edge_polynomials`. The honest balanced-asymptotic
-- gap WAS carried by the `asymptotic_regime_BQ` hypothesis (a Prop, not an axiom);
-- as of the bounded-aspect-ratio discharge it is now PROVED as the theorem
-- `asymptotic_regime_BQ_holds` (guard `max n_A n_B ≤ C·min n_A n_B`), so
-- `secRandomBipartite_aas` is HYPOTHESIS-FREE (only the aspect params `(C, hC)` +
-- `p ∈ (0,1)`). The axiom SET below is unchanged (3 standard + 2 verbatim).
-- The inconsistent axiom and the dead FKS chain (including the former
-- `secRandomBipartite_aas_fks_shape` / `_fks_form` headlines) were physically
-- deleted in I4.
/--
info: 'SECRandomBipartite.secRandomBipartite_aas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 DaveyThesis2024.SecRandomBipartite.KimVu.kim_vu_concentration_verbatim,
 DaveyThesis2024.SecRandomBipartite.PippengerSpencer.pippenger_spencer_covering_verbatim]
-/
#guard_msgs in
#print axioms SECRandomBipartite.secRandomBipartite_aas

-- Weakened a.a.s. per-pair packing (no `/log` FKS improvement, 2026-06-02):
-- a Lean-proved theorem, no domain axioms, only standard Lean axioms.
-- (The stronger FKS-shape `1 / log(n_A · n_B)` packing route was deleted in I4
-- together with the inconsistent axiom it depended on.)

/-- info: 'SECRandomBipartite.perPair_packing_aas_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SECRandomBipartite.perPair_packing_aas_weak

-- Δ = 3 pentagon density bound `5·P ≤ 6·|G|` (P ≤ 6n/5) and its tightness at the
-- Petersen graph. Standard Lean axioms only (kernel `decide`, no `native_decide`).

/-- info: 'Davey2024.pentagon_bound_delta3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.pentagon_bound_delta3

/-- info: 'Davey2024.pentagon_bound_delta3_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.pentagon_bound_delta3_tight

-- Δ = 3 uniqueness: a triangle-free Δ≤3 graph attains P = 6n/5 iff it is a disjoint
-- union of Petersen graphs. Standard Lean axioms only.

/-- info: 'Davey2024.pentagon_delta3_extremal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.pentagon_delta3_extremal_iff

-- Δ = 4: the honest provable local-method bound 5·P ≤ 24·|G| (P ≤ 4.8n), and the
-- C₁₂(2,3) witness realising the conjectured ratio 1/64 (P·64 = |G|·4⁴). Standard axioms.

/-- info: 'Davey2024.pentagon_bound_delta4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.pentagon_bound_delta4

/-- info: 'Davey2024.pentagon_delta4_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.pentagon_delta4_witness

/-- info: 'Davey2024.pentagonCountAt_le_24_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.pentagonCountAt_le_24_tight

-- Δ = 5 tight pentagon bound `P ≤ 12·|G|` and its extremal characterisation
-- (equality iff a disjoint union of Clebsch graphs), plus the Clebsch blow-up
-- tightness witness `clebsch_blowup_tight`. All standard Lean axioms only
-- (enumeration-free dual-certificate proof; no `native_decide`).

/-- info: 'Davey2024.pentagon_delta5_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.pentagon_delta5_tight

/-- info: 'Davey2024.clebsch_blowup_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.clebsch_blowup_tight

/-- info: 'Davey2024.pentagon_delta5_extremal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.pentagon_delta5_extremal_iff

-- HJK degree-scale colouring, obtained from the fixed-Δ `hurley_colouring_lemma`
-- by K_{D,D} disjoint-union padding (B1 repair L3.3). Guarded to certify the
-- padding route introduces NO new axiom beyond the verbatim HJK lemma.

/-- info: 'Davey2024.hurley_colouring_scale' depends on axioms: [propext,
 Classical.choice,
 Davey2024.hurley_colouring_lemma,
 Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.hurley_colouring_scale
