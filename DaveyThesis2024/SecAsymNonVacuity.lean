import DaveyThesis2024.SecAsymBridgeF

/-!
# Non-vacuity regression for the asymmetric SEC domain axioms

`SecAsymBridgeF.sec_combinatorial_identity_asymmetric_F` and
`phi_evalAlg_O_asym_CG4_le_bound` are both gated: the first on a sequence of
`IsAsymmetricBipartite 1`, `IsRegular` graphs of strictly increasing maximum
degree, the second on `secAsymPhiRegular4`, which asserts that `phi` arises from
`secAsymF_phi_construction` applied to such a sequence.  If no such sequence
existed, both would hold vacuously and the Theorem 1.3 headline would rest on
nothing.

This file exhibits one.  `K_{n,n}` is `n`-regular and bipartite with both sides
of degree exactly `n`, so it satisfies `IsAsymmetricBipartite 1` outright.

**Why this axiom in particular.**  `sec_combinatorial_identity_asymmetric_F` was
found **false** once already (2026-07): it was gated only on
`IsAsymmetricBipartite 1` and was refutable on `(Δ, Δ/2)`-semiregular hosts, and
the repair was to add the genuine `IsRegular` gate.  A gate strong enough to be
vacuous would hide exactly that class of error, so the gate needs a witness.
-/

namespace Davey2024
namespace SecAsymNonVacuity

open Davey2024
open Davey2024.SecAsymmetricBipartiteBridge

/-! ## `K_{n,n}` -/

/-- `K_{n,n}` on `Fin (2n)`: the sides are `{v : v.val < n}` and its complement. -/
def kbipGraph (n : ℕ) : SimpleGraph (Fin (2 * n)) :=
  SimpleGraph.fromRel (fun u v => (u.val < n) ≠ (v.val < n))

instance kbipDec (n : ℕ) : DecidableRel (kbipGraph n).Adj := by
  unfold kbipGraph
  intro u v
  rw [SimpleGraph.fromRel_adj]
  exact instDecidableAnd

/-- `K_{n,n}` as a `Flag emptyType`. -/
def kbip (n : ℕ) : Flag emptyType where
  size := 2 * n
  graph := kbipGraph n
  embedding := ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
  hsize := Nat.zero_le _

instance (n : ℕ) : DecidableRel (kbip n).graph.Adj := kbipDec n

@[simp] lemma kbip_size (n : ℕ) : (kbip n).size = 2 * n := rfl

/-- Adjacency in `K_{n,n}` is exactly "opposite sides". -/
lemma kbip_adj_iff (n : ℕ) (u v : Fin (kbip n).size) :
    (kbip n).graph.Adj u v ↔ ((u.val < n) ≠ (v.val < n)) := by
  show (kbipGraph n).Adj u v ↔ _
  unfold kbipGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact fun hc => h hc.symm
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    exact h rfl

/-- Filter cards differing only in the `Decidable` instance agree.  `maxDegree` and
`IsAsymmetricBipartite` elaborate their filters with the classical instance, while the
lemmas below use the registered decidable one; this bridges them.  (Same device as
`PentagonDelta4Witness.card_filter_inst`, restated to avoid the import.) -/
private theorem card_filter_inst {α : Type*} (s : Finset α) (p : α → Prop)
    (d1 d2 : DecidablePred p) :
    (@Finset.filter α p d1 s).card = (@Finset.filter α p d2 s).card := by
  have h : d1 = d2 := Subsingleton.elim _ _
  subst h; rfl

/-! ## Degrees -/

/-- The low side has `n` vertices. -/
lemma card_low (n : ℕ) :
    ((Finset.univ : Finset (Fin (kbip n).size)).filter (fun u => u.val < n)).card = n := by
  classical
  have himg : (((Finset.univ : Finset (Fin (kbip n).size)).filter
      (fun u => u.val < n)).image Fin.val) = Finset.range n := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hi
      refine ⟨⟨i, ?_⟩, hi, rfl⟩
      show i < 2 * n
      omega
  calc ((Finset.univ : Finset (Fin (kbip n).size)).filter (fun u => u.val < n)).card
      = (((Finset.univ : Finset (Fin (kbip n).size)).filter
            (fun u => u.val < n)).image Fin.val).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ = (Finset.range n).card := by rw [himg]
    _ = n := Finset.card_range n

/-- The high side has `n` vertices. -/
lemma card_high (n : ℕ) :
    ((Finset.univ : Finset (Fin (kbip n).size)).filter (fun u => ¬ u.val < n)).card = n := by
  classical
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin (kbip n).size))) (p := fun u => u.val < n)
  rw [card_low] at hsplit
  have hcard : (Finset.univ : Finset (Fin (kbip n).size)).card = 2 * n := by
    simp [Finset.card_univ]
  rw [hcard] at hsplit
  omega

/-- Every vertex of `K_{n,n}` has degree `n`. -/
lemma kbip_degree (n : ℕ) (v : Fin (kbip n).size) :
    ((Finset.univ : Finset (Fin (kbip n).size)).filter
      (fun u => (kbip n).graph.Adj v u)).card = n := by
  classical
  by_cases hv : v.val < n
  · have hset : ((Finset.univ : Finset (Fin (kbip n).size)).filter
        (fun u => (kbip n).graph.Adj v u))
        = (Finset.univ : Finset (Fin (kbip n).size)).filter (fun u => ¬ u.val < n) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, kbip_adj_iff]
      constructor
      · intro h hc; exact h (by simp [hv, hc])
      · intro h hc; exact h (hc ▸ hv)
    rw [hset, card_high]
  · have hset : ((Finset.univ : Finset (Fin (kbip n).size)).filter
        (fun u => (kbip n).graph.Adj v u))
        = (Finset.univ : Finset (Fin (kbip n).size)).filter (fun u => u.val < n) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, kbip_adj_iff]
      constructor
      · intro h
        by_contra hc
        exact h (by simp [hv, hc])
      · intro h hc; exact hv (hc ▸ h)
    rw [hset, card_low]

/-- Hence `Δ(K_{n,n}) = n`, for `n ≥ 1`. -/
lemma kbip_maxDegree (n : ℕ) (hn : 0 < n) : maxDegree (kbip n) = n := by
  have hv0 : (0 : ℕ) < (kbip n).size := by show 0 < 2 * n; omega
  unfold maxDegree
  apply le_antisymm
  · refine Finset.sup_le (fun v _ => ?_)
    exact le_trans (le_of_eq (card_filter_inst _ _ _ _)) (kbip_degree n v).le
  · refine le_trans ?_ (Finset.le_sup (Finset.mem_univ (⟨0, hv0⟩ : Fin (kbip n).size)))
    exact le_of_eq ((kbip_degree n _).symm.trans (card_filter_inst _ _ _ _))

lemma kbip_regular (n : ℕ) (hn : 0 < n) : IsRegular (kbip n) := by
  intro v
  rw [kbip_maxDegree n hn]
  exact (card_filter_inst _ _ _ _).trans (kbip_degree n v)

/-- `K_{n,n}` is asymmetric-bipartite at ratio `1`: both sides have degree `Δ`. -/
lemma kbip_asym (n : ℕ) (hn : 0 < n) : IsAsymmetricBipartite 1 (kbip n) := by
  classical
  refine ⟨(Finset.univ : Finset (Fin (kbip n).size)).filter (fun v => v.val < n),
    ?_, ?_, ?_⟩
  · intro u v huv
    rw [kbip_adj_iff] at huv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h hc; exact huv (by simp [h, hc])
    · intro h
      by_contra hc
      exact huv (by simp [hc, h])
  · intro u _
    rw [kbip_maxDegree n hn]
    exact (card_filter_inst _ _ _ _).trans (kbip_degree n u)
  · intro u _
    rw [kbip_maxDegree n hn, one_mul]
    refine Nat.cast_le.mpr (le_of_eq ?_)
    exact (card_filter_inst _ _ _ _).trans (kbip_degree n u)

/-! ## The admissible sequence

`SecFSeqItem` is not used here: the asymmetric axiom's sequence type is
`Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size`, so each term needs a
distinguished **edge** of `G`.  `K_{n,n}` has one as soon as `n ≥ 1`. -/

/-- The edge `{0, n}` of `K_{n,n}`, for `n ≥ 1`. -/
lemma kbip_edge_mem (n : ℕ) (hn : 0 < n) :
    ((⟨0, by show 0 < 2 * n; omega⟩ : Fin (kbip n).size),
     (⟨n, by show n < 2 * n; omega⟩ : Fin (kbip n).size)) ∈ edgeFinset (kbip n) := by
  classical
  simp only [edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, ?_⟩
  · rw [kbip_adj_iff]
    show (0 < n) ≠ (n < n)
    exact fun hc => absurd (hc ▸ hn) (Nat.lt_irrefl n)
  · show (0 : ℕ) < n
    omega

/-- A distinguished vertex of `L(K_{n,n})²`, i.e. an edge of `K_{n,n}`. -/
noncomputable def kbipEdgeIdx (n : ℕ) (hn : 0 < n) :
    Fin (lineGraphSqFlag (kbip n)).size :=
  (edgeFinset (kbip n)).equivFin ⟨_, kbip_edge_mem n hn⟩

/-- The sequence: `K_{k+1,k+1}` with a distinguished edge. -/
noncomputable def asymSeq :
    ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size :=
  fun k => ⟨kbip (k + 1), kbipEdgeIdx (k + 1) (Nat.succ_pos k)⟩

lemma asymSeq_fst (k : ℕ) : (asymSeq k).1 = kbip (k + 1) := rfl

lemma asymSeq_maxDegree (k : ℕ) : maxDegree (asymSeq k).1 = k + 1 := by
  rw [asymSeq_fst, kbip_maxDegree (k + 1) (Nat.succ_pos k)]

lemma asymSeq_mono : StrictMono (fun k => maxDegree (asymSeq k).1) := by
  intro a b hab
  simp only [asymSeq_maxDegree]
  omega

lemma asymSeq_asym (k : ℕ) : IsAsymmetricBipartite 1 (asymSeq k).1 :=
  kbip_asym (k + 1) (Nat.succ_pos k)

lemma asymSeq_regular (k : ℕ) : IsRegular (asymSeq k).1 :=
  kbip_regular (k + 1) (Nat.succ_pos k)

/-! ## The two regressions -/

/-- **Non-vacuity of the asymmetric combinatorial identity.**  Every hypothesis of
`SecAsymBridgeF.sec_combinatorial_identity_asymmetric_F` is simultaneously
satisfiable, so the axiom is not vacuously true and Theorem 1.3 does not rest on
an empty hypothesis set.  The final clause records that the degrees really do
grow without bound, so the axiom's `Filter.atTop` conclusion has content.

Witness: `K_{n,n}`, which is `n`-regular with both sides of degree exactly `n`,
hence `IsAsymmetricBipartite 1`. -/
theorem asymSeq_exists :
    ∃ seq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size,
      StrictMono (fun k => maxDegree (seq k).1) ∧
      (∀ k, IsAsymmetricBipartite 1 (seq k).1) ∧
      (∀ k, IsRegular (seq k).1) ∧
      (∀ N, ∃ k, N ≤ maxDegree (seq k).1) :=
  ⟨asymSeq, asymSeq_mono, asymSeq_asym, asymSeq_regular, fun N =>
    ⟨N, by rw [asymSeq_maxDegree]; omega⟩⟩

/-- **Non-vacuity of the certificate-output gate.**  Some limit functional satisfies
`secAsymPhiRegular4`, so `SecAsymBridgeF.phi_evalAlg_O_asym_CG4_le_bound` is not
vacuously true. -/
theorem secAsymPhiRegular4_satisfiable :
    ∃ phi : GenLimitFunctional CG4 (GenFlagType.empty CG4)
      secAsymGenGraphClass4 secAsymGenDelta4, secAsymPhiRegular4 phi := by
  refine ⟨secAsymF_phi_construction asymSeq asymSeq_mono asymSeq_asym id strictMono_id, ?_⟩
  exact ⟨asymSeq, asymSeq_mono, asymSeq_asym, id, strictMono_id, rfl⟩

end SecAsymNonVacuity
end Davey2024
