import DaveyThesis2024.SecBipartiteCertificate
import DaveyThesis2024.SecBipartiteBasis
import DaveyThesis2024.LocalFlagAlgebra
import DaveyThesis2024.CG22
import DaveyThesis2024.CGraph22Bridge
import DaveyThesis2024.StrongEdgeColouring
import DaveyThesis2024.SecBridge

/-!
# SecBipartiteBridge — algebra-level objective + axioms for the bipartite SEC SDP

**Status (Phase S3.G, 2026-05-14):** the bipartite analog of `SecBridge`.
Mirrors that file's structure exactly with these substitutions:

* `SecCertificate` → `SecBipartiteCertificate` (3,808 flags vs 17,950, 52
  blocks vs 39).
* `SecBasis.flagBasis_sec` → `SecBipartiteBasis.flagBasis_sec` (the size-5
  (2,2)-coloured ∅-flag basis ordered to match the bipartite SDPA).
* `10.644 = secDensityBound` → `4.093 = secBipartiteDensityBound`.
* Bipartite normalisation factor `1/8` (not `1/16`): the bipartite (4,2)-
  coloured graph construction eliminates the factor-of-2 double-counting
  present in the general (2,2)-coloured case (see thesis §4.5 +
  `notes/bipartite_normalisation.md`).
* `IsBipartite` hypothesis on every sequence element (replaces the
  general bridge's `IsRegular` hypothesis; in the bipartite setting,
  regularity is a downstream consequence of the bipartite structure, so
  the upstream consumer `sec_sdp_limit_bound_bipartite` carries only
  `IsBipartite`). (Pre-2026-05-20 the general bridge carried a TF
  hypothesis as well; Phase 1 of the WLOG-regular closure plan dropped
  it. Bipartite implies TF, so the bipartite docstring's earlier
  reference to TF-implicit downstream-ness is now vacuous.)

**Status (B1 repair, Phase L4 — 2026-07-11):** the original F-free
bipartite chain (`secBipGenGraphClass`, `colouredGraph22OfVertexBip`,
`sec_bipartite_seq_to_genFlag`, the old
`phi_evalAlg_O_sec_bip_alg_eq_target_sum`, the false axiom
`sec_combinatorial_identity_bipartite_step1`, the old bound/locality
axioms, both `_strict` axioms, and the
`sec_bipartite_density_bridge_strong`/`sec_sdp_limit_bound_bipartite_via_bridge`
consumers) has been **retired** — it is the exact bipartite mirror of the
`K_{3,3}`-refutable general chain. The surviving objective objects
(`secBipGenDelta`, `secBipartiteBasisSize`, `targetArrBip`,
`O_sec_bip_coef`, `O_sec_bip_alg`) are class-independent and are reused
verbatim by the F-faithful replacement below.

## What this file provides

* `secBipGenDelta : GenGraphParam CG22` — the SEC degree parameter, same
  function as `secGenDelta`.
* `O_sec_bip_coef k : ℝ` — the sign-flipped cert coefficient
  `-(target[k] / linearScale)`.
* `O_sec_bip_alg : GenFlagAlg CG22 (GenFlagType.empty CG22)` — the
  algebra-level bipartite SEC objective.
* **§8 (F-faithful)** — `secBipGenGraphClassF`,
  `phi_evalAlg_O_sec_bip_alg_eq_target_sum_F`, the restated F-faithful
  axioms (`sec_combinatorial_identity_bipartite_F`,
  `phi_evalAlg_O_sec_bip_alg_le_bound_F`, `flagBasis_sec_bip_isLocalFlag_F`)
  and the PROVED `secBipF_density_bridge`. This is the sound chain the two
  bipartite SEC headlines route through; it shares the host construction
  (`SecBridge.colouredGraph22OfEdgeF` / `SecFSeqItem`) with the general
  case and restricts the SDP identity to the F-subset `H[F]`.

The consumer chain (F-peeling, degeneracy greedy, combined bounds, the
two bipartite headlines) lives in `StrongChromaticIndex.lean`.

## Sign convention

Same as `SecBridge`: the SDPA `Minimizing: -(...)` convention means the
cert's `target_str` is the negative of the underlying SEC flag
coefficient. `O_sec_bip_coef` flips this sign so the result is non-
negative; see `O_sec_bip_coef`'s docstring for details.
-/

namespace Davey2024.SecBipartiteBridge

open Davey2024 SecBipartiteCertificate SecBipartiteBasis

open Finset Classical in
noncomputable section

/-! ## §1. Bipartite SEC graph class + Δ parameter at `CG22` -/

/-- The **bipartite SEC degree parameter** at `CG22`: same as the
general case (max degree of the underlying simple graph). -/
noncomputable def secBipGenDelta : GenGraphParam CG22 :=
  fun G => Finset.sup Finset.univ (fun v => (Finset.univ.filter (G.str.1.Adj v)).card)

/-! ## §2. Algebra-level objective `O_sec_bip_alg` (S3.G.1.A) -/

/-- The number of size-5 flags in the bipartite SEC basis (= 3,808). -/
abbrev secBipartiteBasisSize : Nat := SecBipartiteCertificate.numConstraints

/-- The bipartite cert's `target` vector cached as an `Array Int`. -/
def targetArrBip : Array Int :=
  (Davey2024.SecBipartiteCertificate.target).toArray

/-- The ℝ coefficient for bipartite SEC basis index `k`.

Same sign convention as `Davey2024.SecBridge.O_sec_coef`: the bipartite
SDPA file `certificates/bipartite_strong_edge_colouring.sdpa` uses the
`min -(...)` objective, so `targetArr[k] ≤ 0` for every basis index `k`.
`O_sec_bip_coef` flips this sign to recover the TRUE non-negative
bipartite SEC flag coefficient at basis index `k`. -/
noncomputable def O_sec_bip_coef (k : Fin secBipartiteBasisSize) : ℝ :=
  -((targetArrBip[k.val]! : ℝ) /
    (Davey2024.SecBipartiteCertificate.linearScale : ℝ))

/-- **Algebra-level bipartite SEC objective.**

`O_sec_bip_alg = Σ_{k=0}^{3807}  O_sec_bip_coef k •
   GenFlagAlg.single (SecBipartiteBasis.flagBasis_sec k)`.

The 3,808-term `Finset.sum` is symbolic (`noncomputable`); ~4.7× smaller
than the general SEC's 17,950-term sum but structurally identical. -/
noncomputable def O_sec_bip_alg : GenFlagAlg CG22 (GenFlagType.empty CG22) :=
  (Finset.univ : Finset (Fin secBipartiteBasisSize)).sum
    (fun k => O_sec_bip_coef k • GenFlagAlg.single (SecBipartiteBasis.flagBasis_sec k))

/-! ## §8. F-faithful constructions — bipartite mirror (B1 repair, Phase L1)

Mirror of `Davey2024.SecBridge` §8 (see the polarity rationale there and
the pinned table in the development notes §5 L1.2). The bipartite
bridge shares the `CG22` universe and the `ColouredGraph22` packaging
with the general case, and the bipartite basis projection has the SAME
CG22 polarity as the general one (`SecBipartiteBasis.lean:170`: raw
vertex ∈ {0,1,2,3}, X = {0,1} → **0**, Y = {2,3} → 1 — high-bit
projection; raw edge 1 = F_EDGE → `edgeCol = 1`). Hence the host
construction and per-`k` item type are literally SHARED:
`Davey2024.SecBridge.colouredGraph22OfEdgeF` / `SecFSeqItem` /
`SecFSeqItem.toGenFlag` serve both bridges (the bipartite structure
enters through the basis flags and the `IsBipartite` hypotheses of the
L2 axioms, not through the host construction). Only the class needs a
bipartite twin, mirroring `secBipGenGraphClass` vs `secGenGraphClass`. -/

/-- **F-faithful bipartite SEC graph class** (replaces
`secBipGenGraphClass`, whose third clause has both the polarity and the
bound wrong — pinned table, plan §5 L1.2). Same two clauses as
`Davey2024.SecBridge.secGenGraphClassF`:
1. edge-colour symmetry;
2. bounded black (= colour-**0**) vertex count ≤ **2·Δ**. -/
noncomputable def secBipGenGraphClassF : GenGraphClass CG22 :=
  fun G =>
    let graph := G.str.1
    let vcol  := G.str.2.1
    let ecol  := G.str.2.2
    -- Edge-colour symmetry.
    (∀ u v : Fin G.size, ecol u v = ecol v u) ∧
    -- Bounded black-vertex (colour-0) count: ≤ 2 · max degree.
    (Finset.univ.filter (fun v : Fin G.size => vcol v = 0)).card ≤
      2 * Finset.sup Finset.univ (fun v => (Finset.univ.filter (graph.Adj v)).card)

/-- Every F-faithful item's flag belongs to `secBipGenGraphClassF`
(definitionally the same predicate as `secGenGraphClassF`, so the
general membership proof applies verbatim). -/
theorem SecFSeqItem_toGenFlag_mem_bipClassF (it : SecBridge.SecFSeqItem) :
    secBipGenGraphClassF it.toGenFlag.forget :=
  it.toGenFlag_mem_classF

/-! ### §8b. Bipartite F-class functional plumbing (Phase L2 prep)

Definitions and PROVED theorems only — mirrors `Davey2024.SecBridge` §8b.
The restated bipartite L2 axioms are drafted for review in
the development notes and are NOT declared here yet. -/

/-- `secBipGenDelta` of an F-faithful item's flag is the underlying max
degree (bipartite mirror of `secGenDelta_secF_seq_to_genFlag`). -/
theorem secBipGenDelta_secF_seq_to_genFlag
    (seq : ℕ → SecBridge.SecFSeqItem) (k : ℕ) :
    secBipGenDelta (SecBridge.secF_seq_to_genFlag seq k).forget =
      maxDegree (seq k).G := rfl

/-- Wrap an F-faithful item sequence as a
`GenDeltaIncreasingSeq CG22 ∅ secBipGenDelta`. -/
noncomputable def secBipF_toGenDeltaSeq (seq : ℕ → SecBridge.SecFSeqItem)
    (hΔ : StrictMono (fun k => maxDegree (seq k).G)) :
    GenDeltaIncreasingSeq CG22 (GenFlagType.empty CG22) secBipGenDelta where
  seq k := SecBridge.secF_seq_to_genFlag seq k
  increasing := by
    intro a b hab
    change secBipGenDelta (SecBridge.secF_seq_to_genFlag seq a).forget <
           secBipGenDelta (SecBridge.secF_seq_to_genFlag seq b).forget
    rw [secBipGenDelta_secF_seq_to_genFlag, secBipGenDelta_secF_seq_to_genFlag]
    exact hΔ hab

/-- **Bipartite F-faithful phi construction** (mirror of
`secF_phi_construction` at the bipartite class; membership is
unconditional, the cert-side hypotheses — regularity, bipartiteness,
per-F-edge min-degree — are carried by the L2 axioms' gate). -/
noncomputable def secBipF_phi_construction (seq : ℕ → SecBridge.SecFSeqItem)
    (hΔ : StrictMono (fun k => maxDegree (seq k).G))
    (sub : ℕ → ℕ) (hsub : StrictMono sub) :
    GenLimitFunctional CG22 (GenFlagType.empty CG22)
      secBipGenGraphClassF secBipGenDelta := by
  let cseq : ℕ → SecBridge.SecFSeqItem := fun k => seq (sub k)
  have hΔ' : StrictMono (fun k => maxDegree (cseq k).G) := hΔ.comp hsub
  exact genLimit_functional_construction CG22 (GenFlagType.empty CG22)
    secBipGenGraphClassF secBipGenDelta
    (secBipF_toGenDeltaSeq cseq hΔ')
    (fun k => SecFSeqItem_toGenFlag_mem_bipClassF (cseq k))

/-- **Eval-level basis expansion at the bipartite F-faithful class**
(new-class copy of `phi_evalAlg_O_sec_bip_alg_eq_target_sum`). -/
theorem phi_evalAlg_O_sec_bip_alg_eq_target_sum_F
    (phi : GenLimitFunctional CG22 (GenFlagType.empty CG22)
      secBipGenGraphClassF secBipGenDelta) :
    phi.evalAlg O_sec_bip_alg
      = (Finset.univ : Finset (Fin secBipartiteBasisSize)).sum
          (fun k => O_sec_bip_coef k * phi.eval (SecBipartiteBasis.flagBasis_sec k)) := by
  unfold O_sec_bip_alg
  rw [phi.evalAlg_finset_sum_genFlagAlg]
  exact Finset.sum_congr rfl fun k _ => by rw [phi.evalAlg_smul, phi.evalAlg_single]

/-! ### §8c. Restated (F-faithful) bipartite SEC axioms — Phase L2 (2026-07-11)

Bipartite mirrors of `Davey2024.SecBridge` §8c, landed after coordinator
review of the development notes (amendments A1 + the gate
L2(d) revision). Constants: η = 0.3746 (gate integer 16254 = 10000·(2 − η),
matching the three R3 constraint lines `[|(Σ F − 1.6254·2·ext({2,idX},0)·
ext({2,idX},0))·ext({2,idX},0)|] ≥ 0`, X ∈ {3,4,5}, in
`certificates/bipartite_strong_edge_colouring.sdpa`, generated at
`bipartite_strong_edge_colouring.rs:165–168`); prescale 1/8 (not 1/16 — the
bipartite raw (4,2)-colour construction eliminates the factor-2 double
count, thesis §4.5). The `_F` suffixes mark L2–L3 coexistence with the old
axioms above (rewired L3.4, deleted L4.2).

**No strict-bound axiom (gate L2(d) finding).** The pre-repair bipartite
strict constant `4.0922 = 4.093 − 8/10000` sits below every recorded
optimum (SDPA-LR ≈ 4.0928, CSDP 4.0927013) and is not the thesis's value —
artefact-unsupported, same defect class as the general strict 10.6424. Both
strict axioms are DROPPED: the loose bound closes the thesis-tight bipartite
headline too (ς = 1 − 4.093/8 = 0.488375 → 2(1−ε(ς)) = 1.62539 < 1.6255,
headroom ≈ 1.0×10⁻⁴ after the 10⁻⁵ tolerance; max-branch 1.6254 < 1.6255).
See `Davey2024.SecBridge` §8c and the development notes §6. -/

open Davey2024.SecBridge in
/-- A bipartite SEC limit functional at the F-faithful class is *regularly
F-constructed* iff it arises from `secBipF_phi_construction` on an item
sequence satisfying the full bipartite cert-side gate: strictly increasing
max degree, per-k bipartiteness and regularity, and the per-F-edge
min-strong-degree at η = 0.3746. Mirrors
`Davey2024.SecBridge.secPhiRegularF`; the gates are conjuncts, not
construction arguments. Satisfiability: bipartite Δ-regular girth-≥6 graphs
with F = E(G) pass the gate for Δ ≥ 6
(the development notes §5.3). -/
def secBipPhiRegularF
    (phi : GenLimitFunctional CG22 (GenFlagType.empty CG22)
      secBipGenGraphClassF secBipGenDelta) : Prop :=
  ∃ (seq : ℕ → SecFSeqItem)
    (hΔ : StrictMono (fun k => maxDegree (seq k).G))
    (sub : ℕ → ℕ) (hsub : StrictMono sub),
    (∀ k, IsBipartite (seq k).G) ∧
    (∀ k, IsRegular (seq k).G) ∧
    (∀ k, ∀ e ∈ (seq k).F,
      16254 * (maxDegree (seq k).G) ^ 2 ≤
        10000 * strongFDegree (seq k).G (seq k).F e) ∧
    phi = secBipF_phi_construction seq hΔ sub hsub

open Davey2024.SecBridge in
/-- **Domain axiom — F-faithful bipartite SEC combinatorial identity
(asymptotic, one-sided, toleranced).** Replaces the K₃,₃-refutable
`sec_combinatorial_identity_bipartite_step1` (same failure mode as the
general case, the development notes §0 item 4).

## Statement

For every F-faithful item sequence `(G_k, F_k, v_k)` (`v_k ∈ F_k`
structural) that is Δ-strictly-increasing, per-k bipartite and regular, and
satisfies the per-F-edge min-strong-degree gate at `η = 0.3746` in exact
integers (`16254·Δ² ≤ 10000·strongFDegree`), eventually in `k`:

    |E(H[N_{H[F_k]}(v_k)])| / C(2Δ_k², 2)
      ≤ (1/8)·Σ_j O_sec_bip_coef j · d_j(G'_k)  +  secIdentityTol,

over the 3,808-flag bipartite basis, with the same F-faithful host
construction as the general case (the bipartite basis's CG22 projection has
identical polarity: raw vertex ∈ {0,1,2,3}, X = {0,1} → 0 by high bit, raw
edge 1 = F_EDGE → 1 — `SecBipartiteBasis.lean:170`). The `1/8` prescale
reflects the bipartite construction's elimination of the general case's
factor-2 double count (thesis §4.5, `σ_bip = 1 − λ/8`).

## Why this axiom is needed

As the general `sec_combinatorial_identity_F`: the decomposition (discard
incident pairs / identify with E_O up to pairs containing `v_k` / classify
E_O pairs against the cert target) is exact only asymptotically — thesis
Lemmas 4.2–4.4 + Cor 4.4.1 apply verbatim to the bipartite class — and the
3,808-class cert-arithmetic step is Lean-infeasible (~10⁴–10⁵ LOC; per-k
`native_decide` impossible on an abstract host). Exact and tolerance-free
forms are both false (finite-k corrections resp. target integerisation).

## Why this axiom is correct

As the general version, with: thesis §4.5's bipartite reduction; the Rust
bipartite generator/emitter as the independent source (rounding residue over
3,808 flags at this axiom's own 1/8 prescale: ≈ 9.1×10⁻⁷ crude,
≈ 3.5×10⁻⁹ refined — derivation in the development notes
§1.2 — both ≪ 10⁻⁵); gate truth tests
(the development notes §5): K_{m,m} fails the gate for every
F (1.6254 > 1), bipartite girth-6 Δ-regular graphs with F = E pass it for
Δ ≥ 6. -/
axiom sec_combinatorial_identity_bipartite_F
    (seq : ℕ → SecFSeqItem)
    (hΔ : StrictMono (fun k => maxDegree (seq k).G))
    (hBip : ∀ k, IsBipartite (seq k).G)
    (hReg : ∀ k, IsRegular (seq k).G)
    (hFdeg : ∀ k, ∀ e ∈ (seq k).F,
      16254 * (maxDegree (seq k).G) ^ 2 ≤
        10000 * strongFDegree (seq k).G (seq k).F e) :
    ∀ᶠ k in Filter.atTop,
      (fEdgesInNeighbourhood (seq k).G (seq k).F (seq k).v : ℝ) /
          (Nat.choose (2 * (maxDegree (seq k).G) ^ 2) 2 : ℝ) ≤
        (1/8 : ℝ) *
          (Finset.univ : Finset (Fin secBipartiteBasisSize)).sum
            (fun j => O_sec_bip_coef j *
              genUnlabelledDensity CG22 (GenFlagType.empty CG22)
                (SecBipartiteBasis.flagBasis_sec j)
                (secF_seq_to_genFlag seq k).forget
                secBipGenDelta)
        + secIdentityTol

/-- **Domain axiom — bipartite SEC eval-level upper bound (F-faithful class,
loose).**

## Statement

Every regularly-F-constructed functional at the bipartite F-faithful class
(`secBipPhiRegularF`) satisfies

    phi.evalAlg O_sec_bip_alg ≤ 4.093 = secBipartiteDensityBound.

## Why this axiom is needed

Unchanged from the pre-repair `phi_evalAlg_O_sec_bip_alg_le_bound`: the
per-block iso table needed to lift the 52 `native_decide`-verified LDL block
witnesses to the eval-level cone inequality is missing (same ≥-5-flag
blocker as the general case).

## Why this axiom is correct

1. **Exhaustive constraint discharge.** The bipartite SDPA program (`solve`
   at `bipartite_strong_edge_colouring.rs:150–180`) has exactly FIVE
   linear-constraint families beyond the Cauchy–Schwarz blocks; each maps to
   a Lean-side hypothesis:
   * `flag ≥ 0`, 3,808 rows — intrinsic to
     `GenLimitFunctional.nonneg_on_flags`.
   * R3 min-degree, 3 rows at 1.6254 (rs:165–168; one per F-edge type
     xx/xy/yx) — carried by the `hFdeg` conjunct of `secBipPhiRegularF` via
     `strongFDegree` (thesis Lemma 4.3).
   * Regularity family (`Degree::regularity`, rs:171) — carried by the per-k
     `IsRegular` conjunct.
   * Side-count equalities (`size_of_x`, rs:134–143): per size-4 type `t`,
     `ext_t − ext_{col-0}(t) = 0` AND `ext_t − ext_{col-1}(t) = 0`
     (762 rows) — EXACT side-count-= Δ equalities: in a Δ-regular bipartite
     host each raw-colour side contributes exactly Δ to the extension
     counts; discharged by the F-faithful construction together with the
     per-k `IsRegular` and `IsBipartite` conjuncts. (Gate L2(d) correction:
     these were previously mis-mapped to the ≤ 2Δ class clause; the
     bipartite cert has NO `2·ext − ext_X ≥ 0` inequality family — the
     class's vcol-0 ≤ 2Δ clause is a Lean-side invariant of the
     construction, not the discharge of a cert row.)
   * Normalisations `ones(n, i, col) = 1` for i = 1..5, col ∈ {0, 1}
     (10 rows; rs:175–178) — NOT intrinsic partition-of-unity: `ones` is
     the `Degree::project` of the monochromatic empty `k`-graph
     (`src/degree.rs:42–56`), whose density-1 content is an exact
     count-per-Δ statement about the host's colour classes; discharged by
     the same route as the side-count equalities — the F-faithful
     construction together with the per-k `IsRegular` and `IsBipartite`
     conjuncts (gate L2(d) follow-up (i), corrected in L3.0).
2. **Solver certificate.** SDPA-LR primal optimum ≈ 4.0928 (precision
   ~10⁻⁸); CSDP cross-check 4.0927013, gap 5.88×10⁻⁸
   (`second_solver_verification.md`).
3. **Per-block PSD witnesses.** All 52 blocks `native_decide`-verified in
   `SecBipartiteCertificate`, plus `cert_slack_within_budget`
   (`secBipartiteSlackBudget = 1×10²³`, ≈ 2.4× safety) at the nominal pair
   `(4093, 1000)`.
4. **Independent artefact.** `verify_sec_cert.py` GREEN on all 52 blocks. -/
axiom phi_evalAlg_O_sec_bip_alg_le_bound_F
    (phi : GenLimitFunctional CG22 (GenFlagType.empty CG22)
      secBipGenGraphClassF secBipGenDelta)
    (hreg : secBipPhiRegularF phi) :
    phi.evalAlg O_sec_bip_alg ≤ 4.093

/-- **Domain axiom — bipartite SEC basis flag locality (F-faithful class).**

## Statement

Every one of the 3,808 bipartite basis flags is a local ∅-flag for the
bipartite F-faithful class/degree pair.

## Why this axiom is needed

Unchanged from the pre-repair `flagBasis_sec_bip_isLocalFlag`:
`phi.convergence` requires per-flag locality; the algorithmic witness
extraction is deferred (same as the general case).

## Why this axiom is correct

Thesis locality criterion (every component has a black vertex or labelled
vertex); the Rust bipartite enumeration generates exactly the local flags,
and the CG22 high-bit projection preserves the anchor structure (X-vertices
→ colour 0). The class change (black count ≤ Δ → ≤ 2Δ) only doubles the
anchor budget in the IC bound; bounded density is preserved. Pentagon Q's
proved `flagBasis_isLocalFlag` is the structural template. -/
axiom flagBasis_sec_bip_isLocalFlag_F (k : Fin secBipartiteBasisSize) :
    GenIsLocalFlag (GenFlagType.empty CG22) (SecBipartiteBasis.flagBasis_sec k)
      secBipGenGraphClassF secBipGenDelta

/-! ### §8d. Bipartite F-faithful density bridge (Phase L3.4(a) — PROVED)

Mirror of `Davey2024.SecBridge.secF_density_bridge` at the bipartite class
(1/8 prescale, bound 4.093). -/

open Davey2024.SecBridge in
/-- **Bipartite F-faithful SEC density bridge (PROVED).** Any subsequential
limit of the within-F density along a gated bipartite item sequence is at
most `4.093/8 + secIdentityTol`. Proof mirrors
`Davey2024.SecBridge.secF_density_bridge`. -/
theorem secBipF_density_bridge
    (seq : ℕ → SecFSeqItem)
    (hΔ : StrictMono (fun k => maxDegree (seq k).G))
    (hBip : ∀ k, IsBipartite (seq k).G)
    (hReg : ∀ k, IsRegular (seq k).G)
    (hFdeg : ∀ k, ∀ e ∈ (seq k).F,
      16254 * (maxDegree (seq k).G) ^ 2 ≤
        10000 * strongFDegree (seq k).G (seq k).F e)
    (sub : ℕ → ℕ) (L : ℝ) (hsub : StrictMono sub)
    (htend : Filter.Tendsto (fun k =>
      (fEdgesInNeighbourhood (seq (sub k)).G (seq (sub k)).F (seq (sub k)).v : ℝ) /
      (Nat.choose (2 * (maxDegree (seq (sub k)).G) ^ 2) 2 : ℝ))
      Filter.atTop (nhds L)) :
    L ≤ 4.093 / 8 + secIdentityTol := by
  set phi := secBipF_phi_construction seq hΔ sub hsub with hphi_def
  have hreg : secBipPhiRegularF phi :=
    ⟨seq, hΔ, sub, hsub, hBip, hReg, hFdeg, hphi_def⟩
  set cseq : ℕ → SecFSeqItem := fun k => seq (sub k) with hcseq_def
  have htend_diag : Filter.Tendsto (fun n =>
      (fEdgesInNeighbourhood (seq (sub (phi.sub n))).G (seq (sub (phi.sub n))).F
        (seq (sub (phi.sub n))).v : ℝ) /
      (Nat.choose (2 * (maxDegree (seq (sub (phi.sub n))).G) ^ 2) 2 : ℝ))
      Filter.atTop (nhds L) :=
    htend.comp phi.sub_strictMono.tendsto_atTop
  have hIdent := sec_combinatorial_identity_bipartite_F seq hΔ hBip hReg hFdeg
  have hcompTop : Filter.Tendsto (fun n => sub (phi.sub n))
      Filter.atTop Filter.atTop :=
    (hsub.comp phi.sub_strictMono).tendsto_atTop
  have hIdent_diag : ∀ᶠ n in Filter.atTop,
      (fEdgesInNeighbourhood (seq (sub (phi.sub n))).G (seq (sub (phi.sub n))).F
        (seq (sub (phi.sub n))).v : ℝ) /
      (Nat.choose (2 * (maxDegree (seq (sub (phi.sub n))).G) ^ 2) 2 : ℝ) ≤
      (1/8 : ℝ) *
        (Finset.univ : Finset (Fin secBipartiteBasisSize)).sum
          (fun j => O_sec_bip_coef j *
            genUnlabelledDensity CG22 (GenFlagType.empty CG22)
              (SecBipartiteBasis.flagBasis_sec j)
              (secF_seq_to_genFlag seq (sub (phi.sub n))).forget
              secBipGenDelta)
      + secIdentityTol :=
    hcompTop.eventually hIdent
  set uD : Fin secBipartiteBasisSize → ℕ → ℝ := fun j n =>
    genUnlabelledDensity CG22 (GenFlagType.empty CG22)
      (SecBipartiteBasis.flagBasis_sec j)
      (secF_seq_to_genFlag cseq (phi.sub n)).forget
      secBipGenDelta with huD_def
  have huD_tend : ∀ j : Fin secBipartiteBasisSize,
      Filter.Tendsto (uD j) Filter.atTop
        (nhds (phi.eval (SecBipartiteBasis.flagBasis_sec j))) := by
    intro j
    exact phi.convergence (SecBipartiteBasis.flagBasis_sec j)
      (flagBasis_sec_bip_isLocalFlag_F j)
  have hSum_tend : Filter.Tendsto
      (fun n => (1/8 : ℝ) *
        (Finset.univ : Finset (Fin secBipartiteBasisSize)).sum
          (fun j => O_sec_bip_coef j * uD j n) + secIdentityTol)
      Filter.atTop
      (nhds ((1/8 : ℝ) *
        (Finset.univ : Finset (Fin secBipartiteBasisSize)).sum
          (fun j => O_sec_bip_coef j * phi.eval (SecBipartiteBasis.flagBasis_sec j))
        + secIdentityTol)) := by
    apply Filter.Tendsto.add_const
    apply Filter.Tendsto.const_mul
    apply tendsto_finset_sum
    intro j _
    exact (huD_tend j).const_mul (O_sec_bip_coef j)
  have hL_le : L ≤ (1/8 : ℝ) *
      (Finset.univ : Finset (Fin secBipartiteBasisSize)).sum
        (fun j => O_sec_bip_coef j * phi.eval (SecBipartiteBasis.flagBasis_sec j))
      + secIdentityTol :=
    le_of_tendsto_of_tendsto htend_diag hSum_tend hIdent_diag
  have hAggr := phi_evalAlg_O_sec_bip_alg_eq_target_sum_F phi
  have hBound := phi_evalAlg_O_sec_bip_alg_le_bound_F phi hreg
  rw [hAggr] at hBound
  linarith [hL_le, hBound]

end  -- noncomputable section

end Davey2024.SecBipartiteBridge
