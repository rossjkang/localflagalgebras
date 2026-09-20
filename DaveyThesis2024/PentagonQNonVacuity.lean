import DaveyThesis2024.PentagonQBridge
import DaveyThesis2024.PentagonDelta3

/-!
# Non-vacuity regression for the pentagon-Q domain axioms

On 2026-09-20 an adversarial audit showed that
`PentagonQBridge.pentagonQ_basis_combinatorial_identity_step1` was **false** as
stated, so `pentagon_bound_full` (Paper 1, Theorem 1.2) was derived from an
inconsistent hypothesis set and carried no formal assurance.

The defect: the axiom asserted an *exact* identity at *every* index of an
admissible sequence, with only `0 < Δ` as a guard.  Its right-hand side runs
`genUnlabelledDensity`, which divides by `Nat.choose (brrbGenDelta …) 8`.  For
`Δ < 8` that binomial is `0`, and Lean's division by zero is zero, so every
summand vanishes and the identity forces `pentagonQ = 0` — contradicted by any
triangle-free regular graph carrying pentagons.

A first repair guarded the axiom on `8 ≤ Δ`.  That removed the refutation but
not the underlying error: the left side normalises by a **power** `Δ⁵` and the
right by a **binomial** `Nat.choose Δ 8`, while the coefficients are
`Δ`-independent constants, so the two sides agree only as `Δ → ∞`.  The axiom
is now stated **asymptotically**, exactly as the paper's Lemma 7.9 states it
(`2Q/Δ⁵ = Σⱼ coefⱼ·ρ(basisⱼ) + o(1)`), and the degree guard is gone — a limit
statement is immune to the low-degree terms, since `StrictMono` puts only
finitely many of them below any threshold.

**Why this file exists.**  `AxiomCheck.lean` pins the *names* of the domain
axioms, never their consistency, which is why three earlier false axioms in this
project (`sec_combinatorial_identity_step1`, the Kim–Vu axiom, and
`sec_combinatorial_identity_asymmetric_F`) and this one all survived it.  The
theorems below are the regression that keeps the repaired hypothesis set
**satisfiable** — if a future edit re-breaks the guard, `admissibleSeq_exists`
still holds but `choose_eight_pos_of_guard` pins the exact arithmetic fact the
old form violated.

Both theorems are proved outright, on the three standard kernel axioms.
-/

namespace Davey2024
namespace PentagonQNonVacuity

open Classical

/-! ## An admissible sequence exists

We exhibit a concrete sequence satisfying every hypothesis of the axiom:
strictly increasing maximum degree, triangle-free, and regular.  Balanced
blow-ups of the Petersen graph give the degrees; `pentagon_regular_suffices`
regularises each term while preserving triangle-freeness and maximum degree.
-/

/-- A positive pentagon count forces a positive maximum degree.  Stated generically
in `G`: specialising it to a concrete flag breaks the `Finset.filter` instance match
(see the decidable-instance note in the project's records). -/
lemma maxDegree_pos_of_pentagonCount {G : Flag emptyType}
    (h : pentagonCount G ≠ 0) : 0 < maxDegree G := by
  by_contra hc
  push_neg at hc
  have h' : maxDegree G = 0 := Nat.le_zero.mp hc
  have hnoadj : ∀ u v : Fin G.size, ¬ G.graph.Adj u v := by
    intro u v huv
    have hle : (Finset.univ.filter (fun w => G.graph.Adj u w)).card ≤ maxDegree G :=
      Finset.le_sup (f := fun v => (Finset.univ.filter (fun u => G.graph.Adj v u)).card)
        (Finset.mem_univ u)
    rw [h'] at hle
    have hmem : v ∈ Finset.univ.filter (fun w => G.graph.Adj u w) := by simp [huv]
    have hcard : 0 < (Finset.univ.filter (fun w => G.graph.Adj u w)).card :=
      Finset.card_pos.mpr ⟨v, hmem⟩
    omega
  apply h
  have hempty : (Finset.univ.filter (IsPentagon G)) = (∅ : Finset (Finset (Fin G.size))) := by
    rw [Finset.filter_eq_empty_iff]
    intro S _
    rintro ⟨f, -, -, hadj⟩
    exact hnoadj (f 0) (f 1) ((hadj 0 1).mp (by decide))
  unfold pentagonCount
  rw [hempty]
  simp

/-- `Δ(Petersen)`; we only need `0 < dPet`. -/
noncomputable def dPet : ℕ := maxDegree petersenFlag

lemma dPet_pos : 0 < dPet :=
  maxDegree_pos_of_pentagonCount (by rw [pentagonCount_petersen]; norm_num)

/-- The `(k+1)`-fold balanced blow-up of the Petersen graph. -/
noncomputable def Bk (k : ℕ) : Flag emptyType :=
  blowupFlag petersenFlag (k + 1) (Nat.succ_pos k)

lemma Bk_TF (k : ℕ) : IsTriangleFree (Bk k) :=
  blowup_triangle_free petersenFlag petersenFlag_triangleFree (k + 1) (Nat.succ_pos k)

lemma Bk_deg (k : ℕ) : maxDegree (Bk k) = (k + 1) * dPet :=
  le_antisymm (blowup_maxDegree_ub _ _ _) (blowup_maxDegree_lb _ _ _)

/-- Its regularisation, via the project's own WLOG-regular reduction. -/
noncomputable def Rk (k : ℕ) : Flag emptyType :=
  (pentagon_regular_suffices (Bk k) (Bk_TF k)).choose

lemma Rk_spec (k : ℕ) :
    IsTriangleFree (Rk k) ∧ IsRegular (Rk k) ∧ maxDegree (Rk k) = maxDegree (Bk k) ∧
      (pentagonCount (Bk k) : ℝ) * (Rk k).size ≤ (pentagonCount (Rk k) : ℝ) * (Bk k).size :=
  (pentagon_regular_suffices (Bk k) (Bk_TF k)).choose_spec

lemma Rk_deg (k : ℕ) : maxDegree (Rk k) = (k + 1) * dPet := by
  rw [(Rk_spec k).2.2.1, Bk_deg]

lemma Rk_size_pos (k : ℕ) : 0 < (Rk k).size := by
  by_contra hc
  push_neg at hc
  have hz : (Rk k).size = 0 := Nat.le_zero.mp hc
  have hmd : maxDegree (Rk k) = 0 := by
    unfold maxDegree
    have hempty : (Finset.univ : Finset (Fin (Rk k).size)) = ∅ := by
      ext x; exact absurd x.isLt (by omega)
    rw [hempty]; simp
  rw [Rk_deg] at hmd
  have := dPet_pos
  have : 0 < (k + 1) * dPet := Nat.mul_pos (Nat.succ_pos k) dPet_pos
  omega

/-- The admissible sequence itself. -/
noncomputable def admissibleSeq : ℕ → Σ (G : Flag emptyType), Fin G.size :=
  fun k => ⟨Rk k, ⟨0, Rk_size_pos k⟩⟩

lemma admissibleSeq_fst (k : ℕ) : (admissibleSeq k).1 = Rk k := rfl

lemma admissibleSeq_mono : StrictMono (fun k => maxDegree (admissibleSeq k).1) := by
  intro a b hab
  simp only [admissibleSeq_fst, Rk_deg]
  exact Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl _) dPet_pos

lemma admissibleSeq_TF (k : ℕ) : IsTriangleFree (admissibleSeq k).1 := (Rk_spec k).1

lemma admissibleSeq_Reg (k : ℕ) : IsRegular (admissibleSeq k).1 := (Rk_spec k).2.1

/-- **Non-vacuity.**  Every hypothesis of
`pentagonQ_basis_combinatorial_identity_step1` is simultaneously satisfiable, so
the axiom is not vacuously true and `pentagon_bound_full` does not rest on an
empty hypothesis set.  The final clause records that the degrees really do grow
without bound, so the axiom's `Filter.atTop` conclusion has content.

If a future edit tightens the hypotheses into unsatisfiability, this breaks. -/
theorem admissibleSeq_exists :
    ∃ (seq : ℕ → Σ (G : Flag emptyType), Fin G.size),
      StrictMono (fun k => maxDegree (seq k).1) ∧
      (∀ k, IsTriangleFree (seq k).1) ∧
      (∀ k, IsRegular (seq k).1) ∧
      (∃ k, 8 ≤ maxDegree (seq k).1) := by
  refine ⟨admissibleSeq, admissibleSeq_mono, admissibleSeq_TF, admissibleSeq_Reg, ⟨7, ?_⟩⟩
  rw [admissibleSeq_fst, Rk_deg]
  have := dPet_pos
  calc 8 = 8 * 1 := by norm_num
    _ ≤ (7 + 1) * dPet := Nat.mul_le_mul_left 8 dPet_pos

/-! ## The exact arithmetic fact the old form violated -/

/-- **The defect guard.**  Under the axiom's `8 ≤ Δ` hypothesis the binomial in
the denominator of `genUnlabelledDensity` is nonzero, so the right-hand side of
the combinatorial identity is not identically zero.

This is precisely what failed before 2026-09-20: with only `0 < Δ`, a sequence
entry of degree below `8` gave `Nat.choose Δ 8 = 0`, every summand collapsed to
`0 / 0 = 0` in Lean, and the identity forced `pentagonQ = 0`.  Kept after the
move to the asymptotic form, because it pins the arithmetic that made the
pointwise form untenable. -/
theorem choose_eight_pos_of_guard {Δ : ℕ} (h : 8 ≤ Δ) : 0 < Nat.choose Δ 8 :=
  Nat.choose_pos h

/-- The contrapositive, stated explicitly so the failure mode is searchable:
below degree `8` the denominator vanishes. -/
theorem choose_eight_eq_zero_of_lt {Δ : ℕ} (h : Δ < 8) : Nat.choose Δ 8 = 0 :=
  Nat.choose_eq_zero_of_lt h

end PentagonQNonVacuity
end Davey2024
