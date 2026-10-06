import DaveyThesis2024.AffinePlaneFamily
import DaveyThesis2024.SecBipartiteBridge

/-!
# Non-vacuity for the general and bipartite SEC domain axioms

The four remaining Group-3 gates:

* `SecBridge.sec_combinatorial_identity_F` and its companion
  `phi_evalAlg_O_sec_alg_le_bound_F`, gated on `secPhiRegularF`;
* `SecBipartiteBridge.sec_combinatorial_identity_bipartite_F` and
  `phi_evalAlg_O_sec_bip_alg_le_bound_F`, gated on `secBipPhiRegularF`.

All four demand a sequence of regular graphs of strictly increasing degree in
which **every** `F`-edge has strong `F`-degree at least `1.7297 Δ²` (general) or
`1.6254 Δ²` (bipartite).  `K_{n,n}` cannot serve: its edges at distance one lie
in 4-cycles, leaving only `≈ Δ²`.  The affine-plane incidence family of
`AffinePlaneFamily` does, with `F` the whole edge set, because it has no
4-cycles — see `line_unique`.
-/

namespace Davey2024
namespace SecGenBipNonVacuity

open Davey2024 Davey2024.AffinePlaneFamily Davey2024.SecBridge

/-- The admissible sequence: the affine plane over the `(k+15)`-th prime, with
`F` the whole edge set. -/
noncomputable def affSeq (k : ℕ) : SecFSeqItem where
  G := affFlag (primeSeq k)
  F := Finset.univ
  v := affEdgeIdx (primeSeq k)
  hv := Finset.mem_univ _

@[simp] lemma affSeq_G (k : ℕ) : (affSeq k).G = affFlag (primeSeq k) := rfl
@[simp] lemma affSeq_F (k : ℕ) : (affSeq k).F = Finset.univ := rfl

lemma affSeq_maxDegree (k : ℕ) : maxDegree (affSeq k).G = primeSeq k :=
  affFlag_maxDegree _ (by have := primeSeq_ge k; omega)

lemma affSeq_mono : StrictMono (fun k => maxDegree (affSeq k).G) := by
  intro a b hab
  simp only [affSeq_maxDegree]
  exact primeSeq_strictMono hab

lemma affSeq_regular (k : ℕ) : IsRegular (affSeq k).G :=
  affFlag_isRegular _ (by have := primeSeq_ge k; omega)

lemma affSeq_bipartite (k : ℕ) : IsBipartite (affSeq k).G := affFlag_isBipartite

lemma affSeq_gate (k : ℕ) : ∀ e ∈ (affSeq k).F,
    17297 * (maxDegree (affSeq k).G) ^ 2 ≤
      10000 * strongFDegree (affSeq k).G (affSeq k).F e :=
  fun e _ => affFlag_gate (primeSeq_ge k) e

lemma affSeq_gate_bip (k : ℕ) : ∀ e ∈ (affSeq k).F,
    16254 * (maxDegree (affSeq k).G) ^ 2 ≤
      10000 * strongFDegree (affSeq k).G (affSeq k).F e :=
  fun e _ => affFlag_gate_bip (primeSeq_ge k) e

/-! ## The four regressions -/

/-- **Non-vacuity of the general combinatorial identity.** -/
theorem affSeq_exists :
    ∃ seq : ℕ → SecFSeqItem,
      StrictMono (fun k => maxDegree (seq k).G) ∧
      (∀ k, IsRegular (seq k).G) ∧
      (∀ k, ∀ e ∈ (seq k).F,
        17297 * (maxDegree (seq k).G) ^ 2 ≤
          10000 * strongFDegree (seq k).G (seq k).F e) ∧
      (∀ N, ∃ k, N ≤ maxDegree (seq k).G) :=
  ⟨affSeq, affSeq_mono, affSeq_regular, affSeq_gate, fun N =>
    ⟨N, le_trans (affSeq_mono.le_apply) (le_of_eq rfl)⟩⟩

/-- **Non-vacuity of the bipartite combinatorial identity.** -/
theorem affSeq_exists_bip :
    ∃ seq : ℕ → SecFSeqItem,
      StrictMono (fun k => maxDegree (seq k).G) ∧
      (∀ k, IsBipartite (seq k).G) ∧
      (∀ k, IsRegular (seq k).G) ∧
      (∀ k, ∀ e ∈ (seq k).F,
        16254 * (maxDegree (seq k).G) ^ 2 ≤
          10000 * strongFDegree (seq k).G (seq k).F e) :=
  ⟨affSeq, affSeq_mono, affSeq_bipartite, affSeq_regular, affSeq_gate_bip⟩

/-- **Non-vacuity of the general certificate-output gate.** -/
theorem secPhiRegularF_satisfiable :
    ∃ phi : GenLimitFunctional CG22 (GenFlagType.empty CG22)
      secGenGraphClassF secGenDelta, secPhiRegularF phi := by
  refine ⟨secF_phi_construction affSeq affSeq_mono id strictMono_id, ?_⟩
  exact ⟨affSeq, affSeq_mono, id, strictMono_id, affSeq_regular, affSeq_gate, rfl⟩

open Davey2024.SecBipartiteBridge in
/-- **Non-vacuity of the bipartite certificate-output gate.** -/
theorem secBipPhiRegularF_satisfiable :
    ∃ phi : GenLimitFunctional CG22 (GenFlagType.empty CG22)
      secBipGenGraphClassF secBipGenDelta, secBipPhiRegularF phi := by
  refine ⟨secBipF_phi_construction affSeq affSeq_mono id strictMono_id, ?_⟩
  exact ⟨affSeq, affSeq_mono, id, strictMono_id, affSeq_bipartite, affSeq_regular,
    affSeq_gate_bip, rfl⟩

end SecGenBipNonVacuity
end Davey2024
