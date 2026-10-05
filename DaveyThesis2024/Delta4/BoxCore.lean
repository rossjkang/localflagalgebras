import DaveyThesis2024.Delta4.ModelArith

/-!
# Track `boxDischarge`, second pass: obligations 14 and 15 *unconditionally* from `Box`

`DaveyThesis2024/Delta4/ModelArith.lean` proves the model T-identity and `e₂₂ ≤ 6` in two
layers: a hypothesis layer (`T_identity_of`, `e22_le_six_of`, §10) whose six arguments are
plain facts about `(n, K, A)`, and a `Box` layer (§11) that feeds them.  This file redoes the
**second** layer from scratch — every `Box → hypothesis` step is re-derived here directly from
`box_iff`, none of `Delta4Model`'s `box_*` corollaries is used — and then states the two
obligations in the exact shape the plan asks for.  The hypothesis layer is reused as is: it is
kernel-checked from its own hypotheses, so the only thing a second pass can add there is a
check that the *statements* match, which §4 performs by typechecking both files' theorems
against one literal copy of the required statement.

Three things this pass adds beyond re-deriving the wiring.

* **§0/§1.**  The discharge is routed through `BoxCore`, a structure carrying only the six
  clauses the arithmetic actually consumes.  `Delta4Model`'s §11 comment *claims* the size
  bounds, the packing bounds `K < 16ⁿ`, `A < 4096ⁿ`, `row A i < 2ⁿ`, the sortedness clause and
  the row-disjointness half of (B3)/(B5) are unused; routing through `BoxCore` turns that claim
  into a typecheck.  The search may recanonicalise freely without touching the prune.

* **§3.**  `3 ≤ n ≤ 12` is **not** an independent modelling assumption: it follows from (B1)
  and (B4) alone.  `∑ᵢ kᵢ = 12` with `1 ≤ kᵢ ≤ 4` forces `12/4 ≤ n ≤ 12`.  So obligation 10
  gets the size clauses for free once it has the mask clauses, and no shell of a triangle-free
  4-regular graph can leave the box by being too big.

* **§5/§6.**  Non-vacuity at *every* `n` the box admits: ten witnesses, `n = 3, …, 12`, each
  the honest encoding of a root vertex of a real triangle-free 4-regular graph (nine found by
  `geng`/circulant search, the `n = 12` one an explicit 17-vertex graph whose root lies in no
  4-cycle, so all twelve slots have weight 1).  `n = 12` is attained, so the box's upper size
  bound is tight and the search really must reach it.  §6 adds the (B4) counterexample that
  `ModelArith` does not have: a state failing *only* saturation on which the identity is false.

**Saturation is a `Box` clause.**  Not in the form `∑ᵢ kᵢ = 12` but in the stronger per-letter
form `BoxSpec.sat : ∀ a < 4, ∑_{i<n} hasL K i a = 3`; `box_sat` below sums it over the four
letters.  The model type needs no extra clause.

Nothing here is a `sorry`, an axiom or a `native_decide`; `decide` is kernel evaluation of
`Nat` arithmetic on literal witnesses.
-/

namespace Delta4Model
namespace BoxDischarge

/-! ## 0.  `BoxCore`: the six clauses the arithmetic consumes -/

/-- The part of `Box` that obligations 14 and 15 actually use: (B1) mask positivity,
(B4) saturation, irreflexivity and symmetry of the shell adjacency, (B2) the degree cap, and
the *mask* half of (B3).  Deliberately omits the size bounds, `K < 16ⁿ`, `A < 4096ⁿ`,
`row A i < 2ⁿ`, sortedness, and the row half of (B3)/(B5). -/
structure BoxCore (n K A : Nat) : Prop where
  maskPos : ∀ i, i < n → 1 ≤ msk K i
  sat : ∀ a, a < 4 → sumUpto (fun i => hasL K i a) n 0 = 3
  irrefl : ∀ i, i < n → edg A i i = 0
  symm : ∀ i, i < n → ∀ j, j < n → edg A i j = edg A j i
  degCap : ∀ i, i < n → kwt K i + deg n A i ≤ 4
  maskDisj : ∀ i, i < n → ∀ j, j < n → edg A i j = 1 → (msk K i &&& msk K j) = 0

/-- Every `Box` state is a `BoxCore` state.  This is the *only* place `Box` is unpacked. -/
theorem boxCore_of_box {n K A : Nat} (h : Box n K A = true) : BoxCore n K A := by
  obtain ⟨-, -, -, -, -, hmask, -, hsat, hirr, hsym, hcap, hdis⟩ := (box_iff n K A).1 h
  refine ⟨hmask, hsat, hirr, hsym, hcap, fun i hi j hj hij => ?_⟩
  rcases hdis i hi j hj with h0 | ⟨hm, -⟩
  · rw [h0] at hij; exact absurd hij (by decide)
  · exact hm

/-! ## 1.  The six hypotheses of `T_identity_of` / `e22_le_six_of`, from `BoxCore` -/

/-- A nonzero 4-bit mask carries at least one letter.  Complete case check on the 15
admissible masks — no appeal to `Delta4Model.kwt_pos_of_msk_pos`. -/
theorem kwt_pos_of_mask_pos {K i : Nat} (h : 1 ≤ msk K i) : 1 ≤ kwt K i := by
  have hlt : msk K i < 16 := msk_lt_16 K i
  have hk : kwt K i
      = bitv (msk K i) 0 + bitv (msk K i) 1 + bitv (msk K i) 2 + bitv (msk K i) 3 := rfl
  rw [hk]
  generalize hm : msk K i = m at h hlt ⊢
  interval_cases m <;> decide

theorem core_kwt_pos {n K A : Nat} (hc : BoxCore n K A) : ∀ i, i < n → 1 ≤ kwt K i :=
  fun i hi => kwt_pos_of_mask_pos (hc.maskPos i hi)

/-- The slot budget is exact: the truncated `slack` loses nothing under the degree cap. -/
theorem core_budget {n K A : Nat} (hc : BoxCore n K A) :
    ∀ i, i < n → kwt K i + deg n A i + slack n K A i = 4 := by
  intro i hi
  have := hc.degCap i hi
  unfold slack
  omega

/-- `∑_{i<n} k_i` splits into the four per-letter column sums.  Direct induction. -/
theorem sum_kwt_split (n K : Nat) :
    sumUpto (fun i => kwt K i) n 0
      = sumUpto (fun i => hasL K i 0) n 0 + sumUpto (fun i => hasL K i 1) n 0
        + sumUpto (fun i => hasL K i 2) n 0 + sumUpto (fun i => hasL K i 3) n 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [sumUpto_succ]
      rw [ih]
      have : kwt K n = hasL K n 0 + hasL K n 1 + hasL K n 2 + hasL K n 3 := rfl
      omega

/-- **Saturation, summed.**  Per-letter `= 3` over four letters gives `∑_i k_i = 12`. -/
theorem core_sat {n K A : Nat} (hc : BoxCore n K A) : sumUpto (fun i => kwt K i) n 0 = 12 := by
  rw [sum_kwt_split n K, hc.sat 0 (by decide), hc.sat 1 (by decide), hc.sat 2 (by decide),
    hc.sat 3 (by decide)]

/-- Two `0/1` values whose product vanishes sum to at most `1`. -/
theorem sum_le_one_of_prod_zero {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 0) :
    a + b ≤ 1 := by
  rcases Nat.mul_eq_zero.1 h with h | h <;> omega

/-- **(B3), summed.**  The endpoints of a shell edge carry disjoint letter sets, so the four
root letters bound the sum of their weights. -/
theorem core_kwt_add_le_four {n K A : Nat} (hc : BoxCore n K A) {i j : Nat}
    (hi : i < n) (hj : j < n) (hij : edg A i j = 1) : kwt K i + kwt K j ≤ 4 := by
  have hm := (land_eq_zero_iff (msk K i) (msk K j)).1 (hc.maskDisj i hi j hj hij)
  have e0 := sum_le_one_of_prod_zero (bitv_le_one (msk K i) 0) (bitv_le_one (msk K j) 0) (hm 0)
  have e1 := sum_le_one_of_prod_zero (bitv_le_one (msk K i) 1) (bitv_le_one (msk K j) 1) (hm 1)
  have e2 := sum_le_one_of_prod_zero (bitv_le_one (msk K i) 2) (bitv_le_one (msk K j) 2) (hm 2)
  have e3 := sum_le_one_of_prod_zero (bitv_le_one (msk K i) 3) (bitv_le_one (msk K j) 3) (hm 3)
  have hki : kwt K i
      = bitv (msk K i) 0 + bitv (msk K i) 1 + bitv (msk K i) 2 + bitv (msk K i) 3 := rfl
  have hkj : kwt K j
      = bitv (msk K j) 0 + bitv (msk K j) 1 + bitv (msk K j) 2 + bitv (msk K j) 3 := rfl
  omega

/-! ## 2.  The five theorems the track owes, from `Box` -/

/-- **(B1) discharged.**  Every recorded slot has positive weight. -/
theorem box_kwt_pos {n K A : Nat} (h : Box n K A = true) : ∀ i, i < n → 1 ≤ kwt K i :=
  core_kwt_pos (boxCore_of_box h)

/-- **(B2) discharged.**  The slot budget `k_i + d_{F⁺}(i) + u_i = 4` is exact. -/
theorem box_budget {n K A : Nat} (h : Box n K A = true) :
    ∀ i, i < n → kwt K i + deg n A i + slack n K A i = 4 :=
  core_budget (boxCore_of_box h)

/-- **(B4) discharged.**  `∑_{i<n} k_i = 12`. -/
theorem box_sat {n K A : Nat} (h : Box n K A = true) : sumUpto (fun i => kwt K i) n 0 = 12 :=
  core_sat (boxCore_of_box h)

/-- **(B3) discharged.**  Shell-edge endpoints have weights summing to at most `4`. -/
theorem box_kwt_add_le_four {n K A : Nat} (h : Box n K A = true) :
    ∀ i, i < n → ∀ j, j < n → edg A i j = 1 → kwt K i + kwt K j ≤ 4 :=
  fun _i hi _j hj hij => core_kwt_add_le_four (boxCore_of_box h) hi hj hij

/-- **Obligation 14, unconditional.**  `2T + 4n₃ + 12n₄ + ∑_i(2k_i−1)u_i = 36 + 2e₂₂`,
from `BoxCore` alone — so from `Box`, and from any future box that keeps these six clauses. -/
theorem core_T_identity {n K A : Nat} (hc : BoxCore n K A) :
    twoT n K A + 4 * n3 n K + 12 * n4 n K + slackSum n K A = 36 + 2 * e22 n K A :=
  T_identity_of (core_kwt_pos hc) hc.symm hc.irrefl
    (fun _i hi _j hj hij => core_kwt_add_le_four hc hi hj hij) (core_budget hc) (core_sat hc)

/-- **Obligation 15, unconditional**, from `BoxCore`. -/
theorem core_e22_le_six {n K A : Nat} (hc : BoxCore n K A) : e22 n K A ≤ 6 :=
  e22_le_six_of hc.symm hc.irrefl hc.degCap (core_sat hc)

/-- **Obligation 14.**  The model T-identity, unconditional on `Box n K A = true`. -/
theorem model_T_identity {n K A : Nat} (h : Box n K A = true) :
    twoT n K A + 4 * n3 n K + 12 * n4 n K + slackSum n K A = 36 + 2 * e22 n K A :=
  core_T_identity (boxCore_of_box h)

/-- **Obligation 15.**  `e₂₂ ≤ 6`, unconditional on `Box n K A = true`. -/
theorem model_e22_le_six {n K A : Nat} (h : Box n K A = true) : e22 n K A ≤ 6 :=
  core_e22_le_six (boxCore_of_box h)

/-- The shape the prune consumes: `2T ≤ 48`, i.e. `T ≤ 24`. -/
theorem model_twoT_le {n K A : Nat} (h : Box n K A = true) : twoT n K A ≤ 48 := by
  have h1 := model_T_identity h
  have h2 := model_e22_le_six h
  omega

/-! ## 3.  The size bounds are redundant

`3 ≤ n` and `n ≤ 12` are consequences of (B1) and (B4), not extra modelling assumptions.
Obligation 10 therefore does not have to produce them separately, and — read the other way —
no root vertex of a triangle-free 4-regular graph can have a positive shell outside `[3, 12]`. -/

theorem sumUpto_const (c : Nat) : ∀ n, sumUpto (fun _ => c) n 0 = c * n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [sumUpto_succ, ih]; ring

theorem core_size_bounds {n K A : Nat} (hc : BoxCore n K A) : 3 ≤ n ∧ n ≤ 12 := by
  have hlow : sumUpto (fun _ => 1) n 0 ≤ sumUpto (fun i => kwt K i) n 0 :=
    sumUpto_le _ _ n fun i hi => core_kwt_pos hc i hi
  have hhigh : sumUpto (fun i => kwt K i) n 0 ≤ sumUpto (fun _ => 4) n 0 :=
    sumUpto_le _ _ n fun i _ => kwt_le_four K i
  rw [sumUpto_const 1 n] at hlow
  rw [sumUpto_const 4 n] at hhigh
  rw [core_sat hc] at hlow hhigh
  omega

theorem box_size_bounds {n K A : Nat} (h : Box n K A = true) : 3 ≤ n ∧ n ≤ 12 :=
  core_size_bounds (boxCore_of_box h)

/-! ## 4.  Statement agreement with `ModelArith`

One literal copy of each required statement, discharged twice: once by this file's proof and
once by `Delta4Model`'s.  If either file's theorem said something else, one of these four
would fail to elaborate. -/

example : ∀ {n K A : Nat}, Box n K A = true → ∀ i, i < n → 1 ≤ kwt K i :=
  fun h i hi => box_kwt_pos h i hi
example : ∀ {n K A : Nat}, Box n K A = true → ∀ i, i < n → 1 ≤ kwt K i :=
  fun h _ hi => _root_.Delta4Model.box_kwt_pos h hi

example : ∀ {n K A : Nat}, Box n K A = true →
    ∀ i, i < n → kwt K i + deg n A i + slack n K A i = 4 :=
  fun h i hi => box_budget h i hi
example : ∀ {n K A : Nat}, Box n K A = true →
    ∀ i, i < n → kwt K i + deg n A i + slack n K A i = 4 :=
  fun h _ hi => _root_.Delta4Model.box_slack_add h hi

example : ∀ {n K A : Nat}, Box n K A = true → sumUpto (fun i => kwt K i) n 0 = 12 :=
  fun h => box_sat h
example : ∀ {n K A : Nat}, Box n K A = true → sumUpto (fun i => kwt K i) n 0 = 12 :=
  fun h => _root_.Delta4Model.box_sum_kwt h

example : ∀ {n K A : Nat}, Box n K A = true →
    twoT n K A + 4 * n3 n K + 12 * n4 n K + slackSum n K A = 36 + 2 * e22 n K A :=
  fun h => model_T_identity h
example : ∀ {n K A : Nat}, Box n K A = true →
    twoT n K A + 4 * n3 n K + 12 * n4 n K + slackSum n K A = 36 + 2 * e22 n K A :=
  fun h => _root_.Delta4Model.model_T_identity h

example : ∀ {n K A : Nat}, Box n K A = true → e22 n K A ≤ 6 := fun h => model_e22_le_six h
example : ∀ {n K A : Nat}, Box n K A = true → e22 n K A ≤ 6 :=
  fun h => _root_.Delta4Model.model_e22_le_six h

/-! ## 5.  Non-vacuity at every admissible `n`

Ten witnesses, `n = 3, …, 12`.  Every one is the encoding (masks sorted, slots ordered by
`(mask, vertex)`) of a root vertex of a genuine triangle-free 4-regular graph: `n = 3` is
`K₄,₄`; `n = 4, 5, 9, 10, 11` come from `geng -c -t -d4 -D4` at orders 14–16; `n = 6, 7` from
order 12; `n = 8` from the circulant `C₁₃(1,5)`; `n = 12` from an explicit 17-vertex graph
(root `v`, four letters, twelve weight-1 slots carrying a 3-regular triangle-free graph with
no edge inside a letter class) whose root lies in no 4-cycle.

Each line proves `Box = true` by kernel evaluation, then takes the identity and `e₂₂ ≤ 6`
through §2 — so the discharge is exercised on data, not only on the empty box. -/

theorem box_w3 : Box 3 4095 0 = true := by decide
theorem box_w4 : Box 4 65235 0 = true := by decide
theorem box_w5 : Box 5 1043505 33570816 = true := by decide
theorem box_w6 : Box 6 13419315 3459890689008074784 = true := by decide
theorem box_w7 : Box 7 214586145 28339966039254257406002 = true := by decide
theorem box_w8 : Box 8 3397731105 96827418524244286894182538 = true := by decide
theorem box_w9 : Box 9 54899450385 1426435819209073010117315002508 = true := by decide
theorem box_w10 : Box 10 861212451345 5519034071594991668408880479470176 = true := by decide
theorem box_w11 :
    Box 11 10480865387025 47861296586515524351785238008142102752 = true := by decide
theorem box_w12 :
    Box 12 150101660147985 1502870397429555450610676047445054855381640 = true := by decide

/-- The identity holds on all ten, through the discharge of §2. -/
theorem identity_w3 :
    twoT 3 4095 0 + 4 * n3 3 4095 + 12 * n4 3 4095 + slackSum 3 4095 0
      = 36 + 2 * e22 3 4095 0 := model_T_identity box_w3
theorem identity_w7 :
    twoT 7 214586145 28339966039254257406002 + 4 * n3 7 214586145 + 12 * n4 7 214586145
        + slackSum 7 214586145 28339966039254257406002
      = 36 + 2 * e22 7 214586145 28339966039254257406002 := model_T_identity box_w7
theorem identity_w12 :
    twoT 12 150101660147985 1502870397429555450610676047445054855381640
        + 4 * n3 12 150101660147985 + 12 * n4 12 150101660147985
        + slackSum 12 150101660147985 1502870397429555450610676047445054855381640
      = 36 + 2 * e22 12 150101660147985 1502870397429555450610676047445054855381640 :=
  model_T_identity box_w12

/-- `n = 5`: the one witness on which *every* term of the identity is nonzero —
`2T = 8`, `e₂₂ = 1`, `n₃ = 1`, `n₄ = 1`, `∑(2k−1)u = 14`.  Nothing in the identity is
carried by a term that is always zero on the data. -/
theorem identity_w5 :
    twoT 5 1043505 33570816 + 4 * n3 5 1043505 + 12 * n4 5 1043505
        + slackSum 5 1043505 33570816
      = 36 + 2 * e22 5 1043505 33570816 := model_T_identity box_w5

theorem values_w5 :
    twoT 5 1043505 33570816 = 8 ∧ e22 5 1043505 33570816 = 1
      ∧ n3 5 1043505 = 1 ∧ n4 5 1043505 = 1 ∧ slackSum 5 1043505 33570816 = 14 := by decide

/-- `n = 12` is attained by a real shell, so the box's upper size bound is tight: twelve
weight-1 slots, each with three shell neighbours, `2T = 36`, `e₂₂ = 0`, no slack. -/
theorem values_w12 :
    twoT 12 150101660147985 1502870397429555450610676047445054855381640 = 36
      ∧ e22 12 150101660147985 1502870397429555450610676047445054855381640 = 0
      ∧ n3 12 150101660147985 = 0 ∧ n4 12 150101660147985 = 0
      ∧ slackSum 12 150101660147985 1502870397429555450610676047445054855381640 = 0 := by decide

/-- The sharpest shell seen in the census: `2T = 42` at `n = 7`, comfortably inside
`model_twoT_le`'s cap of `48` and inside the leaf window `38 ≤ 2T`. -/
theorem values_w7 :
    twoT 7 214586145 28339966039254257406002 = 42
      ∧ e22 7 214586145 28339966039254257406002 = 3
      ∧ n3 7 214586145 = 0 ∧ n4 7 214586145 = 0
      ∧ slackSum 7 214586145 28339966039254257406002 = 0 := by decide

theorem window_w7 : 38 ≤ twoT 7 214586145 28339966039254257406002
    ∧ twoT 7 214586145 28339966039254257406002 ≤ 48 :=
  ⟨by decide, model_twoT_le box_w7⟩

/-- `e₂₂ ≤ 6` on all ten, via §2 — and the observed maximum over the ten is `4`, so the
bound is not tight on this sample. -/
theorem e22_w6 : e22 6 13419315 3459890689008074784 ≤ 6 := model_e22_le_six box_w6
theorem e22_w6_value : e22 6 13419315 3459890689008074784 = 4 := by decide

/-! ## 6.  (B4) is load-bearing

`ModelArith` shows (B1) cannot be dropped.  Here is the companion for (B4): `n = 4`,
`K = 65535` (four slots of mask `15`), `A = 0`.  Mask positivity, sortedness, both packing
bounds, `row A i < 2ⁿ`, irreflexivity, symmetry, the degree cap and (B3)/(B5) all hold — the
first conjunct below checks exactly that inside Lean — and saturation alone fails: each letter
is used four times, not three, so `∑ k_i = 16`.  The identity is then false by twelve, the
`12n₄` of the fourth weight-4 slot.  Without (B4) the constant `36` has nothing to stand on. -/

theorem box_false_without_B4 : Box 4 65535 0 = false := by decide

theorem without_B4_every_other_clause :
    (∀ i, i < 4 → 1 ≤ msk 65535 i)
      ∧ (∀ i, i < 3 → msk 65535 i ≤ msk 65535 (i + 1))
      ∧ (65535 < 16 ^ 4 ∧ (0 : Nat) < 4096 ^ 4)
      ∧ (∀ i, i < 4 → row 0 i < 2 ^ 4)
      ∧ (∀ i, i < 4 → edg 0 i i = 0)
      ∧ (∀ i, i < 4 → ∀ j, j < 4 → edg 0 i j = edg 0 j i)
      ∧ (∀ i, i < 4 → kwt 65535 i + deg 4 0 i ≤ 4)
      ∧ (∀ i, i < 4 → ∀ j, j < 4 →
          edg 0 i j = 0 ∨ ((msk 65535 i &&& msk 65535 j) = 0 ∧ (row 0 i &&& row 0 j) = 0))
      ∧ ¬ (∀ a, a < 4 → sumUpto (fun i => hasL 65535 i a) 4 0 = 3) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, fun h => ?_⟩
  have := h 0 (by decide)
  exact absurd this (by decide)

theorem sum_kwt_without_B4 : sumUpto (fun i => kwt 65535 i) 4 0 = 16 := by decide

theorem identity_fails_without_B4 :
    twoT 4 65535 0 + 4 * n3 4 65535 + 12 * n4 4 65535 + slackSum 4 65535 0
      ≠ 36 + 2 * e22 4 65535 0 := by decide

/-! ## 7.  `BoxCore` is *strictly* weaker than `Box`, and that is not an accident

`28339966039254257408050` is the `n = 7` witness with one extra bit set in row `0`, at
position `11 ≥ n`.  It fails `Box` — and fails exactly one clause, `row A i < 2ⁿ`, checked
clause by clause outside Lean — yet it is still a `BoxCore` state, because every model
quantity that the identity mentions (`deg`, `twoT`, `e₂₂`) sums only over `j < n` and so
cannot see the stray bit.  The identity holds on it all the same.

So the prune's arithmetic genuinely does not depend on the canonicalisation clauses: they are
there for the search, not for obligations 14 and 15.  Obligation 10 still has to produce them
if the search's own reasoning uses them — this is a statement about *this* file's dependencies,
not a licence to drop clauses from `Box`. -/

theorem box_false_ghost_bit : Box 7 214586145 28339966039254257408050 = false := by decide

theorem core_ghost_bit : BoxCore 7 214586145 28339966039254257408050 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem identity_ghost_bit :
    twoT 7 214586145 28339966039254257408050 + 4 * n3 7 214586145 + 12 * n4 7 214586145
        + slackSum 7 214586145 28339966039254257408050
      = 36 + 2 * e22 7 214586145 28339966039254257408050 := core_T_identity core_ghost_bit

theorem e22_ghost_bit : e22 7 214586145 28339966039254257408050 ≤ 6 :=
  core_e22_le_six core_ghost_bit

/-- The stray bit really is invisible to the model quantities: same `2T`, same `e₂₂`. -/
theorem ghost_bit_invisible :
    twoT 7 214586145 28339966039254257408050 = twoT 7 214586145 28339966039254257406002
      ∧ e22 7 214586145 28339966039254257408050
          = e22 7 214586145 28339966039254257406002 := by decide

end BoxDischarge
end Delta4Model
