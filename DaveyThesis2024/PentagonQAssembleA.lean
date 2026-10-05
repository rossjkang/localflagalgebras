import DaveyThesis2024.PentagonQAsymptotics
import DaveyThesis2024.PentagonQCompleteFlag

/-!
# Item (a), assembled

Joins `(a1)`'s `basis_identity_host` to `(a2a)`/`(a2b)`/`(a3)`.

**In the default build, and it carries a cost.**  This module was written
outside `DaveyThesis2024.lean`, but `PentagonQBridge` now imports it in order to
prove `pentagonQ_basis_combinatorial_identity_step1` rather than assume it — and
`PentagonQBridge` *is* root-imported.  So the root now reaches
`PentagonQCompleteFlag` and through it `PentagonQWeightsBridge`, whose
`native_decide` was the dominant cost at roughly 1 h 56 m until the 2026-10-05
partition; the figures below are that pre-partition snapshot, kept because they
are what the ranges were measured on.

**That adds roughly 2 h 20 m of compiled evaluation to a cold build.**  On the
2026-10-02 00:42 full build (3829 jobs, successful), the one run that rebuilt
all four: `PentagonQWeightsBridge` 6952 s, `PentagonQDistinctCheck` 1211 s,
`PentagonQComplete` 246 s, `PentagonQFamily` 133 s, plus the eight smaller
checks in `PentagonQPatFacts` — on top of whatever the build already cost.

Treat those as one snapshot, not constants.  Across every build log kept here
the measured spreads are `PentagonQWeightsBridge` 6595–6964 s,
`PentagonQDistinctCheck` 1085–1334 s, `PentagonQComplete` 174–544 s and
`PentagonQFamily` 76–288 s — so quote a range, or name the run, but do not
state a bare figure as the cost.  This file is where the measured figures for
the item-(a) chain belong, because it is downstream of every module it names
and so can be corrected without paying for them again.  (A *warm* rebuild
touching nothing in this chain is still seconds.)  That was a deliberate trade:
discharging the axiom requires its proof, and the proof rests on those checks.
Edits to `PentagonQRooted` or `PentagonQWeights` once cost the full two hours,
not seconds.

**Since 2026-10-05 they do not.**  `PentagonQWeightsBridge`'s check is split
across `PartitionExp.Chunk0..3`, which Lake builds concurrently, so a cold build
pays roughly one chunk rather than all four; the module itself is now a
restatement and costs seconds.  Separately, `BasisDataIntegrity` fell from the
most expensive module in the development to one of the cheapest when `reach8`'s
closure chain was replaced by a materialised set.  The ranges above are
pre-partition history: quote them for what the single-`native_decide` check
cost, not for what the chain costs now.
-/

namespace Davey2024
namespace PentagonQAssembleA

open Davey2024.PentagonQBrrbSurj Davey2024.PentagonQAsymptotics
  Davey2024.PentagonQCompleteFlag Davey2024.PentagonQMuFlag

open Classical in
/-- **The flag side, in closed form.**  `(a1)` says the weighted density sum is
`(1/(6720·C(Δ,8)))·Σ μ`; `sum_muG_host_closed` says what that `Σ μ` is.  Together
they put the flag side entirely in terms of `P(G,v)` and `Σ_{u∼v} P(G,u)`. -/
theorem flag_side_closed (G : Flag emptyType) (v : Fin G.size)
    (htf : IsTriangleFree G) (hreg : IsRegular G) :
    Finset.sum Finset.univ (fun j =>
      PentagonQObjective.O_Q_coef j *
        genUnlabelledDensity CG2 (GenFlagType.empty CG2)
          (PentagonQBasis.flagBasisCGraph j).toGenFlag (vColouredClass G v htf hreg).toGenFlag brrbGenDelta)
      = (1 / (6720 * (Nat.choose (maxDegree G) 8 : ℝ))) *
        ((8 * pentagonCountAt G v * Nat.choose (maxDegree G - 1) 4
          + 2 * Nat.choose (maxDegree G - 2) 3 *
              ((blackSet (vColouredClass G v htf hreg)).sum
                fun u => pentagonCountAt G u) : ℕ) : ℝ) := by
  rw [basis_identity_host (vColouredClass G v htf hreg) brrbGenDelta,
    brrbGenDelta_toGenFlag]
  simp only [vColouredClass_graph]
  -- the two sums differ only by `C.toGenFlag.size` vs `C.graph.size`, which are
  -- definitionally equal; `congr` lets defeq close it where `rw` cannot match
  congr 2
  exact sum_muG_host_closed G v htf hreg

open Classical in
/-- **The rearrangement.**  The target difference is a sum of two
bounded-times-null products, pointwise.

`pentagonQ` is deliberately **never unfolded**: doing so introduces a second
neighbour-sum whose `Decidable` instance differs from the flag side's, and `ring`
then sees two distinct atoms.  `blackSet_sum_eq_pentagonQ_sub` absorbs that
mismatch once, in isolation. -/
theorem pointwise_diff (G : Flag emptyType) (v : Fin G.size)
    (htf : IsTriangleFree G) (hreg : IsRegular G) (h8 : 8 ≤ maxDegree G) :
    2 * (pentagonQ G v / (maxDegree G : ℝ) ^ 5)
      - Finset.sum Finset.univ (fun j => PentagonQObjective.O_Q_coef j *
          genUnlabelledDensity CG2 (GenFlagType.empty CG2)
            (PentagonQBasis.flagBasisCGraph j).toGenFlag
            (vColouredClass G v htf hreg).toGenFlag brrbGenDelta)
      = ((pentagonCountAt G v : ℝ) / (maxDegree G : ℝ) ^ 4) *
          (2 - (8 / 6720 : ℝ) * ((maxDegree G : ℝ) ^ 4 *
            ((Nat.choose (maxDegree G - 1) 4 : ℝ) / (Nat.choose (maxDegree G) 8 : ℝ))))
        + ((pentagonQ G v - (maxDegree G : ℝ) * (pentagonCountAt G v : ℝ))
              / (maxDegree G : ℝ) ^ 5) *
          (2 - (2 / 6720 : ℝ) * ((maxDegree G : ℝ) ^ 5 *
            ((Nat.choose (maxDegree G - 2) 3 : ℝ) / (Nat.choose (maxDegree G) 8 : ℝ)))) := by
  have hD : (0 : ℝ) < (maxDegree G : ℝ) := by
    have : 0 < maxDegree G := by omega
    exact_mod_cast this
  have hC : (0 : ℝ) < (Nat.choose (maxDegree G) 8 : ℝ) := by
    exact_mod_cast Nat.choose_pos h8
  rw [flag_side_closed G v htf hreg]
  push_cast
  rw [blackSet_sum_eq_pentagonQ_sub G v htf hreg]
  field_simp
  ring

open Filter in
open Classical in
/-- **Item (a).**  The basis combinatorial identity, asymptotically. -/
theorem basis_combinatorial_identity_step1
    (seq : ℕ → Σ (G : Flag emptyType), Fin G.size)
    (hΔ : StrictMono (fun k => maxDegree (seq k).1))
    (hTF : ∀ k, IsTriangleFree (seq k).1)
    (hReg : ∀ k, IsRegular (seq k).1) :
    Tendsto (fun k => 2 * (pentagonQ (seq k).1 (seq k).2 / (maxDegree (seq k).1 : ℝ) ^ 5)
      - Finset.sum Finset.univ (fun j => PentagonQObjective.O_Q_coef j *
          genUnlabelledDensity CG2 (GenFlagType.empty CG2) (PentagonQBasis.flagBasis j)
            (vColouredClass (seq k).1 (seq k).2 (hTF k) (hReg k)).toGenFlag
            brrbGenDelta))
      atTop (nhds 0) := by
  have hat : Tendsto (fun k => maxDegree (seq k).1) atTop atTop := hΔ.tendsto_atTop
  have h8 : ∀ᶠ k in atTop, 8 ≤ maxDegree (seq k).1 := hat.eventually_ge_atTop 8
  have hb1 : ∀ᶠ k in atTop,
      |(pentagonCountAt (seq k).1 (seq k).2 : ℝ) / (maxDegree (seq k).1 : ℝ) ^ 4| ≤ 1 := by
    filter_upwards [h8] with k hk
    exact abs_pentagon_div_le_one (seq k).1 (seq k).2 (hTF k) (by omega)
  have hb2 : ∀ᶠ k in atTop,
      |(pentagonQ (seq k).1 (seq k).2
          - (maxDegree (seq k).1 : ℝ) * (pentagonCountAt (seq k).1 (seq k).2 : ℝ))
        / (maxDegree (seq k).1 : ℝ) ^ 5| ≤ 1 := by
    filter_upwards [h8] with k hk
    rw [← blackSet_sum_eq_pentagonQ_sub (seq k).1 (seq k).2 (hTF k) (hReg k)]
    exact abs_sum_black_div_le_one (vColouredClass (seq k).1 (seq k).2 (hTF k) (hReg k))
      (by simpa using (by omega : 0 < maxDegree (seq k).1))
  refine (tendsto_absorption' hb1 hb2
    (tendsto_bracket_tau1_seq hΔ) (tendsto_bracket_tau23_seq hΔ)).congr' ?_
  filter_upwards [h8] with k hk
  exact (pointwise_diff (seq k).1 (seq k).2 (hTF k) (hReg k) hk).symm

#print axioms basis_combinatorial_identity_step1
#print axioms pointwise_diff
#print axioms flag_side_closed

end PentagonQAssembleA
end Davey2024
