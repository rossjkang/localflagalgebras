/-
Stage-4 finite model for `henum` (Δ = 4 pentagon census), per STAGE4_PLAN_merged §1:
three bare `Nat`s `(n, K, A)`; digits by `/` and `%`; masks base 16; adjacency rows
base 4096 (12 bits).  ONE copy of every model quantity — statements and search share it.
-/
import Init.Data.Nat.Bitwise.Lemmas
import Init.Omega

namespace Delta4Model

/-! ## 0.  Bounded folds -/

/-- `∑_{i < n} f i`, accumulator-passing and structurally recursive. -/
def sumUpto (f : Nat → Nat) : Nat → Nat → Nat
  | 0,   acc => acc
  | n+1, acc => sumUpto f n (acc + f n)

/-- `∀ i < n, f i`, structurally recursive and short-circuiting. -/
def allUpto (f : Nat → Bool) : Nat → Bool
  | 0   => true
  | n+1 => f n && allUpto f n

theorem sumUpto_acc (f : Nat → Nat) : ∀ n acc, sumUpto f n acc = acc + sumUpto f n 0
  | 0,   acc => by simp [sumUpto]
  | n+1, acc => by
      rw [sumUpto, sumUpto_acc f n (acc + f n), sumUpto, sumUpto_acc f n (0 + f n)]
      omega

@[simp] theorem sumUpto_zero (f : Nat → Nat) : sumUpto f 0 0 = 0 := rfl

theorem sumUpto_succ (f : Nat → Nat) (n : Nat) :
    sumUpto f (n+1) 0 = sumUpto f n 0 + f n := by
  rw [sumUpto, sumUpto_acc f n (0 + f n)]; omega

theorem sumUpto_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i, i < n → f i = g i) :
    sumUpto f n 0 = sumUpto g n 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sumUpto_succ, sumUpto_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
        h n (Nat.lt_succ_self n)]

theorem sumUpto_le (f g : Nat → Nat) (n : Nat) (h : ∀ i, i < n → f i ≤ g i) :
    sumUpto f n 0 ≤ sumUpto g n 0 := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
      rw [sumUpto_succ, sumUpto_succ]
      exact Nat.add_le_add (ih fun i hi => h i (Nat.lt_succ_of_lt hi)) (h n (Nat.lt_succ_self n))

theorem allUpto_eq_true_iff {f : Nat → Bool} {n : Nat} :
    allUpto f n = true ↔ ∀ i, i < n → f i = true := by
  induction n with
  | zero => simp [allUpto]
  | succ n ih =>
      simp only [allUpto, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h2 i hi
        · exact h1
      · exact fun h => ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem of_allUpto {f : Nat → Bool} {n i : Nat} (h : allUpto f n = true) (hi : i < n) :
    f i = true := allUpto_eq_true_iff.1 h i hi

/-! ## 1.  Digits -/

/-- Mask of shell slot `i`: base-16 digit `i` of `K`, a 4-bit letter set. -/
@[inline] def msk (K i : Nat) : Nat := K / 16 ^ i % 16

/-- Adjacency row of shell slot `i`: base-4096 digit `i` of `A`, 12 bits. -/
@[inline] def row (A i : Nat) : Nat := A / 4096 ^ i % 4096

/-- Bit `j` of `m`, by `/` and `%`. -/
@[inline] def bitv (m j : Nat) : Nat := m / 2 ^ j % 2

/-- Adjacency bit `i ~ j` inside the positive shell. -/
@[inline] def edg (A i j : Nat) : Nat := bitv (row A i) j

/-- `a ∈ A_{x_i}`: does slot `i` carry root letter `a`? -/
@[inline] def hasL (K i a : Nat) : Nat := bitv (msk K i) a

/-- `k_i = |A_{x_i}|`: popcount of the mask over the four root letters. -/
@[inline] def kwt (K i : Nat) : Nat := hasL K i 0 + hasL K i 1 + hasL K i 2 + hasL K i 3

theorem msk_lt_16 (K i : Nat) : msk K i < 16 := Nat.mod_lt _ (by decide)
theorem row_lt_4096 (A i : Nat) : row A i < 4096 := Nat.mod_lt _ (by decide)
theorem bitv_lt_two (m j : Nat) : bitv m j < 2 := Nat.mod_lt _ (by decide)
theorem bitv_le_one (m j : Nat) : bitv m j ≤ 1 := Nat.lt_succ_iff.1 (bitv_lt_two m j)
theorem edg_le_one (A i j : Nat) : edg A i j ≤ 1 := bitv_le_one _ _
theorem hasL_le_one (K i a : Nat) : hasL K i a ≤ 1 := bitv_le_one _ _
theorem kwt_le_four (K i : Nat) : kwt K i ≤ 4 := by
  have := hasL_le_one K i 0; have := hasL_le_one K i 1
  have := hasL_le_one K i 2; have := hasL_le_one K i 3
  unfold kwt; omega

/-- Bridge to `Nat.testBit`: reads the bitwise `&&&` clauses of `Box` back as
    `bitv` statements.  Consumed by the transport (obligation 10). -/
theorem bitv_eq_toNat_testBit (m j : Nat) : bitv m j = (m.testBit j).toNat :=
  (Nat.toNat_testBit m j).symm

theorem land_eq_zero_iff (m m' : Nat) :
    (m &&& m') = 0 ↔ ∀ j, bitv m j * bitv m' j = 0 := by
  constructor
  · intro h j
    have : (m &&& m').testBit j = false := by rw [h]; exact Nat.zero_testBit j
    rw [Nat.testBit_and] at this
    simp only [bitv_eq_toNat_testBit]
    rcases Bool.and_eq_false_iff.1 this with h' | h' <;> simp [h']
  · intro h
    refine Nat.eq_of_testBit_eq fun j => ?_
    rw [Nat.testBit_and, Nat.zero_testBit]
    have := h j
    simp only [bitv_eq_toNat_testBit] at this
    cases hm : m.testBit j <;> cases hm' : m'.testBit j <;> simp_all

/-! ## 2.  Derived shell quantities -/

/-- `d_{F⁺}(i)`: the number of positive-shell neighbours of slot `i`. -/
def deg (n A i : Nat) : Nat := sumUpto (fun j => edg A i j) n 0

/-- `u_i = 4 − k_i − d_{F⁺}(i)`.  Truncated; `Box` makes it exact. -/
def slack (n K A i : Nat) : Nat := 4 - kwt K i - deg n A i

/-- `2T = ∑_i ∑_j [i ~ j] k_i k_j`: the doubled shell objective. -/
def twoT (n K A : Nat) : Nat :=
  sumUpto (fun i => sumUpto (fun j => edg A i j * kwt K i * kwt K j) n 0) n 0

/-- `e₂₂`: shell edges with `k = 2` at both ends, counted once (`j < i`). -/
def e22 (n K A : Nat) : Nat :=
  sumUpto (fun i =>
    sumUpto (fun j => if kwt K i = 2 ∧ kwt K j = 2 then edg A i j else 0) i 0) n 0

/-! ## 3.  Punctured attachment weights `k_a(·)` (plan obligation 4) -/

/-- `k_a(b)` for a *root* letter `b ≠ a`: `|N(a) ∩ N(b) \ {v}| = |B_a ∩ B_b|`. -/
def rootW (n K : Nat) (a b : Nat) : Nat := sumUpto (fun i => hasL K i a * hasL K i b) n 0

/-- `k_a(y)` for a *shell* slot `y`: `|N(y) ∩ B_a|`, zero when `y ∈ B_a`
    (such a `y` is adjacent to `a`, so not in `S_a`). -/
def shellW (n K A : Nat) (a y : Nat) : Nat :=
  (1 - hasL K y a) * sumUpto (fun i => hasL K i a * edg A y i) n 0

/-- Dual weights `c = certY43 = (0,1,3,0,0,…)`. -/
def cert : Nat → Nat
  | 1 => 1
  | 2 => 3
  | _ => 0

/-! ## 4.  Visible credit and visible charge -/

/-- `∑_{z ∈ K_a} 3 k_a(z)` at one root letter `a`. -/
def creditAt (n K A a : Nat) : Nat :=
  sumUpto (fun b => if b = a then 0 else 3 * rootW n K a b) 4 0
  + sumUpto (fun y => 3 * shellW n K A a y) n 0

/-- `d̂_a(b) = |N(b) ∩ K_a|`, `b ≠ a` a root letter.  `u_b = 0` and `v ∉ K_a`,
    so only `B_b` counts. -/
def dhatRoot (n K A a b : Nat) : Nat :=
  sumUpto (fun y => if shellW n K A a y = 0 then 0 else hasL K y b) n 0

/-- `d̂_a(y) = |N(y) ∩ K_a| + u_y` at a shell slot `y`. -/
def dhatShell (n K A a y : Nat) : Nat :=
  sumUpto (fun b => if b = a then 0 else if rootW n K a b = 0 then 0 else hasL K y b) 4 0
  + sumUpto (fun z => if z = y then 0 else if shellW n K A a z = 0 then 0 else edg A y z) n 0
  + slack n K A y

/-- `∑_{z ∈ K_a} d̂_a(z)·c(k_a(z))` at one root letter `a`. -/
def chargeAt (n K A a : Nat) : Nat :=
  sumUpto (fun b => if b = a then 0 else dhatRoot n K A a b * cert (rootW n K a b)) 4 0
  + sumUpto (fun y => dhatShell n K A a y * cert (shellW n K A a y)) n 0

/-- `visibleCreditTotal`. -/
def credit (n K A : Nat) : Nat := sumUpto (creditAt n K A) 4 0

/-- `visibleChargeTotal`. -/
def charge (n K A : Nat) : Nat := sumUpto (chargeAt n K A) 4 0

/-! ## 5.  The box -/

/-- The search box: `(N)`, `(B1)`–`(B5)` of `SHELL_BOX_AND_FIBRE.tex`, saturation,
    canonical packing, symmetry/irreflexivity of `A`, sorted masks (§5 D16). -/
def Box (n K A : Nat) : Bool :=
  -- (N) shell size
  decide (3 ≤ n) && decide (n ≤ 12)
  -- canonical packing: no digits above the shell
  && decide (K < 16 ^ n) && decide (A < 4096 ^ n)
  && allUpto (fun i => decide (row A i < 2 ^ n)) n
  -- (B1) every recorded shell vertex carries an attachment
  && allUpto (fun i => decide (1 ≤ msk K i)) n
  -- (D16) masks non-decreasing
  && allUpto (fun i => decide (msk K i ≤ msk K (i+1))) (n - 1)
  -- (B4) saturation: every root letter is used exactly three times
  && allUpto (fun a => decide (sumUpto (fun i => hasL K i a) n 0 = 3)) 4
  -- `A` is a simple graph on the shell
  && allUpto (fun i => decide (edg A i i = 0)) n
  && allUpto (fun i => allUpto (fun j => decide (edg A i j = edg A j i)) n) n
  -- (B2) degree cap
  && allUpto (fun i => decide (kwt K i + deg n A i ≤ 4)) n
  -- (B3) a shell edge shares no root letter, (B5) and closes no shell triangle
  && allUpto (fun i => allUpto (fun j =>
       decide (edg A i j = 0)
         || (decide (msk K i &&& msk K j = 0) && decide (row A i &&& row A j = 0))) n) n

/-- `Box` as a `Prop`: the transport (obligation 10) proves *this* and converts
    with `box_iff`; the search consumes `Box … = true`.  Clause order = `Box`. -/
structure BoxSpec (n K A : Nat) : Prop where
  size_lb : 3 ≤ n
  size_ub : n ≤ 12
  packK : K < 16 ^ n
  packA : A < 4096 ^ n
  rowLt : ∀ i, i < n → row A i < 2 ^ n
  maskPos : ∀ i, i < n → 1 ≤ msk K i
  sorted : ∀ i, i < n - 1 → msk K i ≤ msk K (i + 1)
  sat : ∀ a, a < 4 → sumUpto (fun i => hasL K i a) n 0 = 3
  irrefl : ∀ i, i < n → edg A i i = 0
  symm : ∀ i, i < n → ∀ j, j < n → edg A i j = edg A j i
  degCap : ∀ i, i < n → kwt K i + deg n A i ≤ 4
  edgeDisj : ∀ i, i < n → ∀ j, j < n →
    edg A i j = 0 ∨ (msk K i &&& msk K j = 0 ∧ row A i &&& row A j = 0)

theorem box_iff (n K A : Nat) : Box n K A = true ↔ BoxSpec n K A := by
  simp only [Box, Bool.and_eq_true, decide_eq_true_eq, allUpto_eq_true_iff,
    Bool.or_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9,
      fun i hi j hj => h10 i hi j hj, h11,
      fun i hi j hj => by simpa using h12 i hi j hj⟩
  · intro hb
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb.size_lb, hb.size_ub⟩, hb.packK⟩, hb.packA⟩, hb.rowLt⟩,
      hb.maskPos⟩, hb.sorted⟩, hb.sat⟩, hb.irrefl⟩,
      fun i hi j hj => hb.symm i hi j hj⟩, hb.degCap⟩,
      fun i hi j hj => by simpa using hb.edgeDisj i hi j hj⟩

theorem box_masks_pos {n K A : Nat} (h : Box n K A = true) {i : Nat} (hi : i < n) :
    1 ≤ msk K i := ((box_iff n K A).1 h).maskPos i hi

theorem box_edg_irrefl {n K A : Nat} (h : Box n K A = true) {i : Nat} (hi : i < n) :
    edg A i i = 0 := ((box_iff n K A).1 h).irrefl i hi

theorem box_edg_symm {n K A : Nat} (h : Box n K A = true) {i j : Nat}
    (hi : i < n) (hj : j < n) : edg A i j = edg A j i :=
  ((box_iff n K A).1 h).symm i hi j hj

/-- `Box` implies the degree cap `k_i + d_{F⁺}(i) ≤ 4`. -/
theorem box_deg_cap {n K A : Nat} (h : Box n K A = true) {i : Nat} (hi : i < n) :
    kwt K i + deg n A i ≤ 4 := ((box_iff n K A).1 h).degCap i hi

theorem box_deg_le_four {n K A : Nat} (h : Box n K A = true) {i : Nat} (hi : i < n) :
    deg n A i ≤ 4 := Nat.le_trans (Nat.le_add_left _ _) (box_deg_cap h hi)

/-- The slack is exact under `Box`: `k_i + d_{F⁺}(i) + u_i = 4`. -/
theorem box_slack_add {n K A : Nat} (h : Box n K A = true) {i : Nat} (hi : i < n) :
    kwt K i + deg n A i + slack n K A i = 4 := by
  have := box_deg_cap h hi; unfold slack; omega

theorem box_saturation {n K A : Nat} (h : Box n K A = true) {a : Nat} (ha : a < 4) :
    sumUpto (fun i => hasL K i a) n 0 = 3 := ((box_iff n K A).1 h).sat a ha

theorem box_size {n K A : Nat} (h : Box n K A = true) : 3 ≤ n ∧ n ≤ 12 :=
  ⟨((box_iff n K A).1 h).size_lb, ((box_iff n K A).1 h).size_ub⟩

/-- (B3)+(B5) in `bitv` form — the shape the transport produces. -/
theorem box_edge_disjoint {n K A : Nat} (h : Box n K A = true) {i j : Nat}
    (hi : i < n) (hj : j < n) (hij : edg A i j = 1) :
    (∀ a, hasL K i a * hasL K j a = 0) ∧ (∀ t, edg A i t * edg A j t = 0) := by
  rcases ((box_iff n K A).1 h).edgeDisj i hi j hj with h0 | ⟨hm, hr⟩
  · omega
  · exact ⟨(land_eq_zero_iff _ _).1 hm, (land_eq_zero_iff _ _).1 hr⟩

/-- The kernel leaf test, written in `2T` (plan §5 D13). -/
def leafOK (n K A : Nat) : Bool :=
  decide (twoT n K A < 38) || decide (charge n K A + 6 * twoT n K A ≤ credit n K A + 212)

end Delta4Model
