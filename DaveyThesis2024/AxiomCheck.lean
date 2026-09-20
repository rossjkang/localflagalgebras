import DaveyThesis2024.PentagonBound
import DaveyThesis2024.PentagonQNonVacuity
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
import DaveyThesis2024.Delta4.Transport
import DaveyThesis2024.Delta4.Pack
import DaveyThesis2024.Delta4.ModelArith
import DaveyThesis2024.Delta4.Search
import DaveyThesis2024.Delta4.BallInvariance
import DaveyThesis2024.Delta4.Prune
import DaveyThesis2024.Delta4.CreditCharge
import DaveyThesis2024.Delta4.MaskGen
import DaveyThesis2024.Delta4.Chunk
import DaveyThesis2024.Delta4.BoxOfRoot
import DaveyThesis2024.Delta4.Assembly
import DaveyThesis2024.Delta4.ChunkP
import DaveyThesis2024.Delta4.Layer7

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

/-- info: 'Davey2024.pentagon_bound_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pentagon_bound_simple

-- The WLOG-regular reduction the pentagon headlines lean on: every triangle-free G has a
-- regular G' of the same maximum degree whose pentagon density is at least as large. Proved
-- outright, so the regularity hypothesis in the certificate bounds costs no generality.

/-- info: 'Davey2024.pentagon_regular_suffices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pentagon_regular_suffices

-- NON-VACUITY REGRESSION for the pentagon-Q domain axioms (added 2026-09-20).
-- `pentagonQ_basis_combinatorial_identity_step1` was FALSE until that date: it
-- asserted an exact identity at every index with only `0 < Δ`, while its
-- right-hand side divides by `Nat.choose Δ 8`, which vanishes below degree 8,
-- so it forced `pentagonQ = 0`.  `pentagon_bound_full` was therefore derived
-- from an inconsistent hypothesis set.  The axiom now carries `8 ≤ Δ`.
-- These two guards are the regression: the first keeps the repaired hypothesis
-- set SATISFIABLE (so the axiom is not vacuously true), the second pins the
-- arithmetic fact the old form violated.  Guarding axiom NAMES, as the rest of
-- this file does, cannot catch a false axiom -- that is how this defect and
-- three earlier ones in this project survived it.

/-- info: 'Davey2024.PentagonQNonVacuity.admissibleSeq_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PentagonQNonVacuity.admissibleSeq_exists

/-- info: 'Davey2024.PentagonQNonVacuity.choose_eight_pos_of_guard' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PentagonQNonVacuity.choose_eight_pos_of_guard

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

-- Δ = 4: the local-method bound 5·P ≤ 24·|G| (P ≤ 4.8n) proved outright, and the C₁₂(2,3)
-- witness attaining the extremal ratio 1/64 (P·64 = |G|·4⁴). The sharp bound P ≤ 4|G| that
-- C₁₂(2,3) attains is now an unconditional theorem too,
-- `Delta4Gen.pentagon_bound_delta4_sharp`, on these same three axioms. It cannot be guarded
-- from here: its module `Delta4.Generated.CheckAll` is deliberately outside the default
-- build, since importing it would make every `lake build` re-pay the ~2 h finite check. What
-- IS guarded here is the bridge it is applied to, below; the generated side prints its own
-- axiom line, by the recipe in `Delta4/Generated/generator/README.md`.
-- Standard axioms.

/-- info: 'Davey2024.pentagon_bound_delta4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.pentagon_bound_delta4

/-- info: 'Davey2024.pentagon_delta4_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.pentagon_delta4_witness

-- Saturation, the hinge of the sharp Δ = 4 route: on a triangle-free 4-regular graph
-- every root neighbour has exactly three shell neighbours, so the shell spends the full
-- attachment budget of 12.  This is what turns a high root's shell into a finite object
-- and lets the classification avoid an external graph enumerator.  Standard axioms only:
-- the sharp Δ = 4 theorem must land in the `pentagon_bound_simple` class, NOT the
-- `pentagon_bound_full` class, so no `Lean.ofReduceBool` / `Lean.trustCompiler` here.

/-- info: 'Davey2024.PentagonLocal.attach_multiplicity_eq_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.attach_multiplicity_eq_three

/-- info: 'Davey2024.PentagonLocal.sum_attach_card_eq_twelve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.sum_attach_card_eq_twelve

-- Non-vacuity: C₁₂(2,3) satisfies all three saturation hypotheses, so neither statement
-- above is vacuous.  These two guards are the regression that keeps it that way.

/-- info: 'Davey2024.c12_isRegular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.c12_isRegular

/-- info: 'Davey2024.c12_sum_attach_card_eq_twelve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.c12_sum_attach_card_eq_twelve

-- Stage 2 of the sharp Δ = 4 route: the punctured-root count r_a (pentagons through a
-- neighbour that avoid the root) is at most thirteen, and the rerooting row splits as
-- Q(v) = 6·p(v) + Σ r_a.  Together these close the branch where the shell objective is at
-- most eighteen; the complementary branch is the high-root case T ≥ 19.

/-- info: 'Davey2024.PentagonLocal.pentagonCountAt_avoid_le_thirteen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.pentagonCountAt_avoid_le_thirteen

/-- info: 'Davey2024.pentagonQ_eq_six_mul_add_avoid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.pentagonQ_eq_six_mul_add_avoid

/-- info: 'Davey2024.pentagonQ_le_160_of_shellObjective_le_eighteen'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.pentagonQ_le_160_of_shellObjective_le_eighteen'

-- Non-vacuity of the low branch: K₄,₄ has shell objective 0, so the theorem above fires.

/-- info: 'Davey2024.k44_pentagonQ_le_160' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.k44_pentagonQ_le_160

-- The shell T-identity: 2T + 4n3 + 12n4 + sum (2k-1)u = 36 + 2 e22 at a root of a
-- triangle-free 4-regular graph.  This is what makes the high-root search space finite,
-- and e22 <= 6 is the filter that bounds the shell objective by 24.

/-- info: 'Davey2024.PentagonLocal.shellObjective_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.shellObjective_identity

/-- info: 'Davey2024.PentagonLocal.e22_le_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.e22_le_six

/-- info: 'Davey2024.PentagonLocal.shellObjective_le_24' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.shellObjective_le_24

/-- info: 'Davey2024.c12_shellObjective_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.c12_shellObjective_identity

-- Stage 3, first half: the neighbour layer.  (F4) is an EQUALITY, not the inequality the
-- certificate usually supplies, because on a punctured shell edge the weights are (1,1) or
-- (1,2) where certY43 is tight.  With saturation at the neighbour it gives 2*T_a <= 27.

/-- info: 'Davey2024.PentagonLocal.avoid_F4_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.avoid_F4_identity

/-- info: 'Davey2024.PentagonLocal.sum_avoidAttach_eq_nine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.sum_avoidAttach_eq_nine

/-- info: 'Davey2024.PentagonLocal.two_mul_avoidObjective_le_27' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.two_mul_avoidObjective_le_27

/-- info: 'Davey2024.PentagonLocal.avoid_defect_term_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.avoid_defect_term_nonneg

-- The shell fibre map is a bijection, so the pentagon count at v EQUALS the weighted
-- shell-edge count -- with no degree hypothesis, unlike the inequality it refines.
-- Off the critical path (the P <= 4|G| chain uses the inequality in the safe direction),
-- but it closes a gap in the stated identities of the development notes.

/-- info: 'Davey2024.PentagonLocal.pentagonCountAt_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.pentagonCountAt_eq_sum

-- r_a <= 13 by the sharp F4 route (equality, not inequality), under the extra regularity
-- hypothesis that saturation at the neighbour needs. The original route is kept: it holds
-- under strictly weaker hypotheses.

/-- info: 'Davey2024.PentagonLocal.pentagonCountAt_avoid_le_thirteen'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.pentagonCountAt_avoid_le_thirteen'

-- The visible-defect vocabulary. Definitions only so far; the design decision recorded with
-- them is that the defect difference is NEVER formed in Nat, only the two subtraction-free
-- sums visibleCredit and visibleCharge.

/-- info: 'Davey2024.PentagonLocal.sum_visible_add_unseen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.sum_visible_add_unseen

-- Conservativity (D^vis <= D) and the high-root branch. With these the ANALYTIC layer of the
-- sharp Delta=4 route is complete: P(G) <= 4|G| now follows from one hypothesis about the
-- visible defect at high roots. NOTE that hypothesis is an unbounded forall over every
-- triangle-free 4-regular graph of every order -- NOT a finite check. Reducing it to one is
-- the model-transport stage and is not done.

/-- info: 'Davey2024.PentagonLocal.conservativity_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.conservativity_at

/-- info: 'Davey2024.pentagonQ_le_160_of_visible_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.pentagonQ_le_160_of_visible_bound

/-- info: 'Davey2024.pentagon_bound_delta4_of_visible_enumeration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.pentagon_bound_delta4_of_visible_enumeration

-- Radius-2 locality: unseenDeg is the only quantity in the transport row that looks past
-- distance two, and under regularity it equals a slot count computed from radius-2 data.
-- This removes one obstruction to the model transport; it does not achieve it.

/-- info: 'Davey2024.PentagonLocal.dhat_eq_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.dhat_eq_local

-- The radius-2 ball. Every index set the transport row ranges over lies inside it, and its
-- size is at most 17 -- attained, not slack, so the finite model must be sized for 17 rather
-- than the census maximum of 14. Containment is necessary but NOT sufficient: isomorphism
-- invariance of the row's quantities on the ball is still missing.

/-- info: 'Davey2024.PentagonLocal.visibleAvoid_subset_ball2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.visibleAvoid_subset_ball2

/-- info: 'Davey2024.PentagonLocal.card_ball2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.card_ball2_le

-- Transfer along a closed induced injection: the whole henum row is an iff. NOTE this is
-- COMPONENT invariance, not locality -- the closure hypothesis says the image is a union of
-- connected components, so it does NOT finitise the forall H. The step the transport needs is
-- invariance under isomorphism of the rooted radius-2 ball, which is still open and must go
-- through dhat_eq_local under regularity.

/-- info: 'Davey2024.PentagonLocal.visibleRow_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.visibleRow_transfer

-- The Stage-4 gate: K_a decomposes into a root part and a shell part, so it never escapes
-- radius two. Had it escaped, the finite model would need radius three and the transport
-- design would be wrong. This is the go/no-go the merged Stage-4 plan waits on.

/-- info: 'Davey2024.PentagonLocal.visibleAvoid_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.visibleAvoid_eq

/-- info: 'Davey2024.PentagonLocal.visibleAvoid_subset_rootNbrs_union_shellPos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.visibleAvoid_subset_rootNbrs_union_shellPos

-- Stage 4, the finite model. Obligation 4: the model's punctured attachment weights really do
-- reproduce the graph's |avoidAttach|, which is what lets a rooted graph be replaced by three
-- natural numbers. The packing lemmas are Mathlib-free and sit at the bottom of the import
-- graph.

/-- info: 'Davey2024.PentagonLocal.avoidAttach_card_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.avoidAttach_card_root

/-- info: 'Davey2024.PentagonLocal.avoidAttach_card_shell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.avoidAttach_card_shell

/-- info: 'Delta4Model.msk_packK' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Delta4Model.msk_packK

-- The merged Stage-4 plan states obligation 7 FALSELY. This is the disproof of its exact
-- statement: A = 4096 records 1 ~ 0 without 0 ~ 1 and satisfies every hypothesis the plan
-- lists, yet the conclusion fails because the second summand carries. The repair is one extra
-- hypothesis, which the traversal has for free. Guarded so the false form cannot creep back.

/-- info: 'Delta4Model.plan_edg_addEdge_false' does not depend on any axioms -/
#guard_msgs in
#print axioms Delta4Model.plan_edg_addEdge_false

-- Stage 4, third pass. Obligation 16 (the prune is sound, so pruning loses no leaf),
-- obligations 12/13 (the graph-side credit and charge totals ARE the model's), and
-- obligation 19 (the mask generator is complete). Together with searchNP_complete these are
-- the pieces the finite check is assembled from.

/-- info: 'Delta4Model.searchP_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Delta4Model.searchP_complete

/-- info: 'Davey2024.PentagonLocal.visibleCreditTotal_eq_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.visibleCreditTotal_eq_model

/-- info: 'Davey2024.PentagonLocal.visibleChargeTotal_eq_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.visibleChargeTotal_eq_model

/-- info: 'Delta4Model.msGen_complete_of_box' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Delta4Model.msGen_complete_of_box

-- Obligation 10, unconditional: a real rooted graph's encoding lands in the model's box.
-- This was FALSE until the D16 repair (the encoding sorted the shell by vertex index while
-- Box requires masks non-decreasing; 97.7% of census roots violated it). shellArr is now
-- mask-sorted and the census count is 0.

/-- info: 'Davey2024.PentagonLocal.box_of_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.PentagonLocal.box_of_root

-- THE STAGE-4 HEADLINE, now discharged. The sharp Delta=4 bound rests on ONE decidable
-- Boolean:
--   checkAll = true -> forall G, triangle-free -> maxDegree <= 4 -> pentagonCount G <= 4|G|
-- checkAll ranges over n <= 12 and K in msGen n (862 entries total). That Boolean is proved:
-- `Delta4Gen.checkAll_true`, in the generated tree, over 2,685,792 pruned search nodes. Both
-- forms of the bridge are guarded below - the raw one and the layer-indexed
-- `pentagon_bound_delta4_sharp_of_checkAll` that the generated headline actually applies.

/-- info: 'Davey2024.Delta4Assembly.pentagon_bound_delta4_of_checkAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Davey2024.Delta4Assembly.pentagon_bound_delta4_of_checkAll

-- NB the layer-indexed bridge lives at ROOT level, not under `Davey2024`: AssemblyLayers.lean
-- opens `namespace Delta4Assembly` at top level while Assembly.lean nests the same namespace
-- inside `Davey2024`. Hence the `_root_` below; the two names are not the same declaration.

/-- info: 'Delta4Assembly.pentagon_bound_delta4_sharp_of_checkAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms _root_.Delta4Assembly.pentagon_bound_delta4_sharp_of_checkAll

-- The chunk algebra for the PRUNED traversal. Chunk.lean's version is goNP-level, whose tree
-- is ~614M nodes; this one is about goPrune pruneOK (2,685,792 nodes) and is what the finite
-- check must be generated against. layerOK_of_msCnt consumes a NODE COUNT rather than a bare
-- Bool, which is mandatory: LayerOK n reduces to true = true, so a proof about one layer is
-- otherwise defeq-accepted for another.

/-- info: 'Delta4Chunk.layerOK_of_msCnt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Delta4Chunk.layerOK_of_msCnt

-- The first complete layer of the finite check. LayerOK 7 covers 249 masks and 28,957 pruned
-- nodes, three of them heavy enough to need a frontier cut. Note LayerOK is defeq-transferable
-- between layers, so what makes this meaningful is that the chain runs through
-- msCnt 7 (msGen 7) = (28957, 0) with the node count carried.

/-- info: 'Layer7.l7_layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Layer7.l7_layer

/-- info: 'Delta4Chunk.msCnt_singleton' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Delta4Chunk.msCnt_singleton

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

-- Paper-3 local-law certificate arithmetic and explicit realization
-- interfaces. These guards make the default library build compile the three
-- certificate data files and ensure that the graph-to-law endpoint wrappers
-- introduce no project axioms. Constructing a `RealizedLaw` from a finite
-- graph remains a separate, explicit proof obligation.

-- Short conceptual Paper-3 bridges.  Their graph-side structural inputs are
-- explicit hypotheses; these guards check that the injection, aggregation,
-- and discharging implications themselves introduce no project axioms.
