import DaveyThesis2024.Delta4.Model

/-!
# Δ = 4 finite model: the packing lemmas

Obligations 6 and 7 of the Stage 4 plan.  `packK` and
`packA` build the model's two packed words from digit lists, and the extraction lemmas say the
accessors read back what was packed.  `edg_addEdge_add` is the incremental update the search
traversal performs at each accepted pair.

**The plan states obligation 7 falsely, and `plan_edg_addEdge_false` disproves it here.**
The hypothesis `edg A i j = 0` constrains bit `j` of row `i` only; the update also writes bit
`i` of row `j`, and if *that* bit is already set the addition carries and the claimed value is
wrong.  `A = 4096` — the word recording `1 ∼ 0` but not `0 ∼ 1` — is a concrete counterexample
satisfying every hypothesis the plan lists.  The repair is one extra hypothesis, `edg A j i = 0`,
which the traversal has for free because it maintains `A` symmetric; `edg_addEdge_of_symm`
packages exactly that.  The plan's `hA : A < 4096 ^ 12` turns out to be unnecessary — the
update is digit-local — so the traversal need not carry that bound.

**Superseded in practice.**  `Delta4Model.edg_addEdge` in `Delta4/Search.lean` proves the same
update rule with **no freshness hypotheses at all**, because the search's `addEdge` uses
bitwise `|||` rather than `+`.  Or is idempotent, so no carry can occur and the whole
difficulty the plan's obligation 7 describes simply does not arise.  The addition-based lemmas
here are kept because they are what obligation 7 asks for and because `plan_edg_addEdge_false`
documents why its stated form is wrong, but new code should use the `Search` version.
-/

namespace Delta4Model

section Pack

/-! ## P0.  Base-`b` digit arithmetic (the engine for both obligations)

`msk`, `row` and `bitv` are all the same operation `X / b ^ i % b` at bases
`16`, `4096`, `2`.  Proving the digit facts once, generically, serves obligation 6
(digit of a packed list) and obligation 7 (digit of a no-carry increment) and the
base-2 bit reasoning inside obligation 7. -/

/-- No carry out of digit `i`: adding `b ^ i * c` leaves the quotient above digit
`i` untouched, provided digit `i` of `X` plus `c` still fits in a digit. -/
theorem div_succ_add_pow_mul {b : Nat} (hb : 0 < b) (X c i : Nat)
    (h : X / b ^ i % b + c < b) :
    (X + b ^ i * c) / b ^ (i + 1) = X / b ^ (i + 1) := by
  have hbp : 0 < b ^ i := Nat.pow_pos hb
  have e : b ^ (i + 1) = b ^ i * b := Nat.pow_succ b i
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left X c hbp]
  have hd := Nat.div_add_mod (X / b ^ i) b
  have key : X / b ^ i + c = X / b ^ i % b + c + b * (X / b ^ i / b) := by omega
  rw [key, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt h, Nat.zero_add]

/-- The same, at every height above `i`. -/
theorem div_add_pow_mul_of_lt {b : Nat} (hb : 0 < b) (X c i n : Nat)
    (h : X / b ^ i % b + c < b) (hin : i < n) :
    (X + b ^ i * c) / b ^ n = X / b ^ n := by
  obtain ⟨d, rfl⟩ : ∃ d, n = i + 1 + d := ⟨n - (i + 1), by omega⟩
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    div_succ_add_pow_mul hb X c i h]

/-- **No-carry digit update.**  If digit `i` of `X` has room for `c`, then adding
`b ^ i * c` changes digit `i` by `c` and changes no other digit. -/
theorem digit_add_pow_mul {b : Nat} (hb : 0 < b) (X c i i' : Nat)
    (h : X / b ^ i % b + c < b) :
    (X + b ^ i * c) / b ^ i' % b = X / b ^ i' % b + (if i' = i then c else 0) := by
  rcases Nat.lt_trichotomy i' i with hlt | heq | hgt
  · -- below `i`: the added term is divisible by `b ^ (i'+1)`
    have hne : ¬ (i' = i) := by omega
    obtain ⟨d, hd⟩ : ∃ d, i = i' + 1 + d := ⟨i - (i' + 1), by omega⟩
    subst hd
    have e : b ^ (i' + 1 + d) * c = b ^ i' * (b * (b ^ d * c)) := by
      rw [Nat.pow_add, Nat.pow_succ]; simp [Nat.mul_assoc]
    rw [e, Nat.add_mul_div_left X _ (Nat.pow_pos hb), Nat.add_mul_mod_self_left]
    simp [hne]
  · -- at `i`
    subst heq
    rw [Nat.add_mul_div_left X c (Nat.pow_pos hb)]
    have hd := Nat.div_add_mod (X / b ^ i') b
    have key : X / b ^ i' + c = X / b ^ i' % b + c + b * (X / b ^ i' / b) := by omega
    rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
    simp
  · -- above `i`: no carry reaches it
    have hne : ¬ (i' = i) := by omega
    rw [div_add_pow_mul_of_lt hb X c i i' h hgt]
    simp [hne]

/-! ## P1.  Specialisations to `row` and `bitv` -/

/-- Base-4096 form: adding `4096 ^ i * c` bumps row `i` by `c` and nothing else. -/
theorem row_add (A c i i' : Nat) (h : row A i + c < 4096) :
    row (A + 4096 ^ i * c) i' = row A i' + (if i' = i then c else 0) :=
  digit_add_pow_mul (b := 4096) (by decide) A c i i' h

/-- Base-2 form: setting a clear bit `j` leaves every other bit alone. -/
theorem bitv_add (m j j' : Nat) (h : bitv m j = 0) :
    bitv (m + 2 ^ j) j' = bitv m j' + (if j' = j then 1 else 0) := by
  have h' : m / 2 ^ j % 2 + 1 < 2 := by simp only [bitv] at h; omega
  have key := digit_add_pow_mul (b := 2) (by decide) m 1 j j' h'
  simp only [Nat.mul_one] at key
  simpa only [bitv] using key

/-- Setting a clear bit below the width does not overflow the width. -/
theorem add_two_pow_lt (m j n : Nat) (hm : m < 2 ^ n) (hjn : j < n) (h : bitv m j = 0) :
    m + 2 ^ j < 2 ^ n := by
  have h' : m / 2 ^ j % 2 + 1 < 2 := by simp only [bitv] at h; omega
  have key := div_add_pow_mul_of_lt (b := 2) (by decide) m 1 j n h' hjn
  simp only [Nat.mul_one] at key
  rw [Nat.div_eq_of_lt hm] at key
  exact Nat.lt_of_div_eq_zero (Nat.pow_pos (by decide)) key

/-- A row stays a 12-bit digit when a clear bit of it is set. -/
theorem row_add_two_pow_lt {A i j : Nat} (hj : j < 12) (h : edg A i j = 0) :
    row A i + 2 ^ j < 4096 := by
  have e : (2 : Nat) ^ 12 = 4096 := by decide
  have hm : row A i < 2 ^ 12 := by have := row_lt_4096 A i; omega
  have := add_two_pow_lt (row A i) j 12 hm hj h
  omega

/-! ## P2.  Obligation 6 — `packK` / `packA` extraction

Digit of a packed little-endian list.  Two shapes, one per base; both are the two
generic one-step lemmas `digit_zero_of_lt` / `digit_succ_of_lt` plus a list induction. -/

theorem digit_zero_of_lt {b a p : Nat} (ha : a < b) : (a + b * p) / b ^ 0 % b = a := by
  rw [Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

theorem digit_succ_of_lt {b a p i : Nat} (hb : 0 < b) (ha : a < b) :
    (a + b * p) / b ^ (i + 1) % b = p / b ^ i % b := by
  have e : b ^ (i + 1) = b * b ^ i := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [e, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left a p hb, Nat.div_eq_of_lt ha,
    Nat.zero_add]

/-- Little-endian base-16 packing of the mask list: the head is shell slot `0`. -/
def packK : List Nat → Nat
  | [] => 0
  | m :: ms => m + 16 * packK ms

/-- Little-endian base-4096 packing of the row list: the head is shell slot `0`. -/
def packA : List Nat → Nat
  | [] => 0
  | r :: rs => r + 4096 * packA rs

/-- **Obligation 6a.**  `msk` reads back the packed mask list.  Out of range on
both sides: `msk` sees a zero digit, `getD` returns the default `0`. -/
theorem msk_packK : ∀ (ms : List Nat), (∀ m ∈ ms, m < 16) → ∀ i,
    msk (packK ms) i = ms.getD i 0 := by
  intro ms
  induction ms with
  | nil => intro _ i; simp [packK, msk]
  | cons m ms ih =>
      intro h i
      have hm : m < 16 := h m (by simp)
      have h' : ∀ x ∈ ms, x < 16 := fun x hx => h x (by simp [hx])
      cases i with
      | zero =>
          rw [List.getD_cons_zero]
          show (m + 16 * packK ms) / 16 ^ 0 % 16 = m
          exact digit_zero_of_lt hm
      | succ i =>
          rw [List.getD_cons_succ]
          show (m + 16 * packK ms) / 16 ^ (i + 1) % 16 = ms.getD i 0
          rw [digit_succ_of_lt (b := 16) (by decide) hm]
          exact ih h' i

/-- **Obligation 6b.**  `row` reads back the packed row list. -/
theorem row_packA : ∀ (rs : List Nat), (∀ r ∈ rs, r < 4096) → ∀ i,
    row (packA rs) i = rs.getD i 0 := by
  intro rs
  induction rs with
  | nil => intro _ i; simp [packA, row]
  | cons r rs ih =>
      intro h i
      have hr : r < 4096 := h r (by simp)
      have h' : ∀ x ∈ rs, x < 4096 := fun x hx => h x (by simp [hx])
      cases i with
      | zero =>
          rw [List.getD_cons_zero]
          show (r + 4096 * packA rs) / 4096 ^ 0 % 4096 = r
          exact digit_zero_of_lt hr
      | succ i =>
          rw [List.getD_cons_succ]
          show (r + 4096 * packA rs) / 4096 ^ (i + 1) % 4096 = rs.getD i 0
          rw [digit_succ_of_lt (b := 4096) (by decide) hr]
          exact ih h' i

/-- ADDED (not in the plan's obligation 6, needed by `Box`'s packing clause
`K < 16 ^ n`): a packed list is a canonically packed `Nat`. -/
theorem packK_lt : ∀ (ms : List Nat), (∀ m ∈ ms, m < 16) →
    packK ms < 16 ^ ms.length := by
  intro ms
  induction ms with
  | nil => intro _; simp [packK]
  | cons m ms ih =>
      intro h
      have hm : m < 16 := h m (by simp)
      have hlt := ih (fun x hx => h x (by simp [hx]))
      have e : (16 : Nat) ^ (m :: ms).length = 16 ^ ms.length * 16 := by
        rw [List.length_cons, Nat.pow_succ]
      show m + 16 * packK ms < 16 ^ (m :: ms).length
      rw [e]; omega

/-- ADDED, for `Box`'s clause `A < 4096 ^ n`. -/
theorem packA_lt : ∀ (rs : List Nat), (∀ r ∈ rs, r < 4096) →
    packA rs < 4096 ^ rs.length := by
  intro rs
  induction rs with
  | nil => intro _; simp [packA]
  | cons r rs ih =>
      intro h
      have hr : r < 4096 := h r (by simp)
      have hlt := ih (fun x hx => h x (by simp [hx]))
      have e : (4096 : Nat) ^ (r :: rs).length = 4096 ^ rs.length * 4096 := by
        rw [List.length_cons, Nat.pow_succ]
      show r + 4096 * packA rs < 4096 ^ (r :: rs).length
      rw [e]; omega

/-- ADDED, convenience: the bit form of `row_packA`, which is what the generator
actually reads. -/
theorem edg_packA (rs : List Nat) (h : ∀ r ∈ rs, r < 4096) (i j : Nat) :
    edg (packA rs) i j = bitv (rs.getD i 0) j := by
  simp only [edg, row_packA rs h i]

/-! ## P3.  Obligation 7 — fresh-digit incremental update

**The plan's statement of obligation 7 is FALSE as written** — see
`plan_edg_addEdge_false` below.  `hfresh : edg A i j = 0` constrains bit `j` of row
`i` only; the second summand `4096 ^ j * 2 ^ i` writes bit `i` of row `j`, and if
that bit is already set the addition *carries* and the claimed value `1` at
`(j, i)` is wrong.  The repair is one extra hypothesis, `edg A j i = 0`, which the
traversal has for free (it maintains `A` symmetric, so `edg A j i = edg A i j`);
`edg_addEdge_of_symm` packages exactly that.

Two further remarks on the plan's signature, both in the caller's favour:
* `hA : A < 4096 ^ 12` is **not needed** — the update is digit-local, so nothing
  above digit `j` is touched whatever the size of `A`.  Dropping it removes a
  bound the traversal would otherwise have to carry.
* `hij : i < j` is used only for `i ≠ j` and `i < 12`; `i ≠ j` plus `i < 12`
  would do, but `i < j` is what the canonical `pairList` supplies, so it stays. -/

/-- The row-level content of obligation 7: an `addEdge` is a no-carry update of the
two base-4096 digits `i` and `j`, and of nothing else.  ADDED as a separate step —
`edg_addEdge_add`, `addEdge_lt` and `row_addEdge_lt` are all corollaries of it. -/
theorem row_addEdge (A i j t : Nat) (hij : i < j) (hj : j < 12)
    (hfresh : edg A i j = 0) (hfresh' : edg A j i = 0) :
    row (A + 4096 ^ i * 2 ^ j + 4096 ^ j * 2 ^ i) t
      = row A t + (if t = i then 2 ^ j else 0) + (if t = j then 2 ^ i else 0) := by
  have hb1 : row A i + 2 ^ j < 4096 := row_add_two_pow_lt hj hfresh
  have hb2 : row A j + 2 ^ i < 4096 := row_add_two_pow_lt (by omega) hfresh'
  have hb2' : row (A + 4096 ^ i * 2 ^ j) j + 2 ^ i < 4096 := by
    rw [row_add A (2 ^ j) i j hb1]; simpa [show ¬ (j = i) from by omega] using hb2
  rw [row_add (A + 4096 ^ i * 2 ^ j) (2 ^ i) j t hb2', row_add A (2 ^ j) i t hb1]

/-- **Obligation 7, corrected and with `hA` dropped.** -/
theorem edg_addEdge_add (A i j i' j' : Nat) (hij : i < j) (hj : j < 12)
    (hfresh : edg A i j = 0) (hfresh' : edg A j i = 0) :
    edg (A + 4096 ^ i * 2 ^ j + 4096 ^ j * 2 ^ i) i' j'
      = if (i' = i ∧ j' = j) ∨ (i' = j ∧ j' = i) then 1 else edg A i' j' := by
  have hji : ¬ (j = i) := by omega
  have hij' : ¬ (i = j) := by omega
  have hf1 : bitv (row A i) j = 0 := hfresh
  have hf2 : bitv (row A j) i = 0 := hfresh'
  have rows := fun t => row_addEdge A i j t hij hj hfresh hfresh'
  simp only [edg]
  by_cases h1 : i' = i
  · -- row `i`: bit `j` flips 0 → 1, nothing else moves
    have hnj : ¬ (i' = j) := by omega
    have hrow : row (A + 4096 ^ i * 2 ^ j + 4096 ^ j * 2 ^ i) i' = row A i' + 2 ^ j := by
      rw [rows i']; simp [h1, hij']
    have hz : bitv (row A i') j = 0 := by rw [h1]; exact hfresh
    rw [hrow, bitv_add (row A i') j j' hz]
    by_cases h2 : j' = j
    · simp [h1, h2, hf1]
    · simp [h2, hnj]
  · by_cases h1' : i' = j
    · -- row `j`: bit `i` flips 0 → 1
      have hrow : row (A + 4096 ^ i * 2 ^ j + 4096 ^ j * 2 ^ i) i' = row A i' + 2 ^ i := by
        rw [rows i']; simp [h1', hji]
      have hz : bitv (row A i') i = 0 := by rw [h1']; exact hfresh'
      rw [hrow, bitv_add (row A i') i j' hz]
      by_cases h2 : j' = i
      · simp [h1', h2, hf2]
      · simp [h1, h2]
    · -- every other row is untouched
      have hrow : row (A + 4096 ^ i * 2 ^ j + 4096 ^ j * 2 ^ i) i' = row A i' := by
        rw [rows i']; simp [h1, h1']
      rw [hrow]; simp [h1, h1']

/-- **Obligation 7 in the shape the traversal uses.**  The search maintains `A`
symmetric on the shell, so the single freshness hypothesis of the plan really does
suffice — once the symmetry it is relying on is made explicit. -/
theorem edg_addEdge_of_symm (A i j i' j' : Nat) (hij : i < j) (hj : j < 12)
    (hsym : edg A j i = edg A i j) (hfresh : edg A i j = 0) :
    edg (A + 4096 ^ i * 2 ^ j + 4096 ^ j * 2 ^ i) i' j'
      = if (i' = i ∧ j' = j) ∨ (i' = j ∧ j' = i) then 1 else edg A i' j' :=
  edg_addEdge_add A i j i' j' hij hj hfresh (by rw [hsym]; exact hfresh)

/-- The update preserves symmetry of `A`, so `edg_addEdge_of_symm` composes along a
run of `addEdge`s.  ADDED — obligation 17's prefix invariant needs it. -/
theorem edg_addEdge_symm (A i j : Nat) (hij : i < j) (hj : j < 12)
    (hsym : ∀ s t, edg A s t = edg A t s) (hfresh : edg A i j = 0) :
    ∀ s t, edg (A + 4096 ^ i * 2 ^ j + 4096 ^ j * 2 ^ i) s t
         = edg (A + 4096 ^ i * 2 ^ j + 4096 ^ j * 2 ^ i) t s := by
  have hfresh' : edg A j i = 0 := by rw [hsym]; exact hfresh
  intro s t
  rw [edg_addEdge_add A i j s t hij hj hfresh hfresh',
      edg_addEdge_add A i j t s hij hj hfresh hfresh', hsym s t]
  by_cases h1 : (s = i ∧ t = j) ∨ (s = j ∧ t = i) <;>
    by_cases h2 : (t = i ∧ s = j) ∨ (t = j ∧ s = i) <;> simp [h1, h2] <;> omega

/-! ### The two `Box` packing invariants, preserved

ADDED.  `Box` carries `A < 4096 ^ n` and `∀ i < n, row A i < 2 ^ n`; obligation 17's
prefix invariant has to re-establish both after every `addEdge`, and both are
corollaries of `row_addEdge` / `add_two_pow_lt`. -/

/-- Canonical packing survives an `addEdge`. -/
theorem addEdge_lt (A n i j : Nat) (hij : i < j) (hj : j < n) (hn : n ≤ 12)
    (hA : A < 4096 ^ n) (hfresh : edg A i j = 0) (hfresh' : edg A j i = 0) :
    A + 4096 ^ i * 2 ^ j + 4096 ^ j * 2 ^ i < 4096 ^ n := by
  have hb1 : row A i + 2 ^ j < 4096 := row_add_two_pow_lt (by omega) hfresh
  have hb2 : row A j + 2 ^ i < 4096 := row_add_two_pow_lt (by omega) hfresh'
  have hb2' : row (A + 4096 ^ i * 2 ^ j) j + 2 ^ i < 4096 := by
    rw [row_add A (2 ^ j) i j hb1]; simpa [show ¬ (j = i) from by omega] using hb2
  have k1 : (A + 4096 ^ i * 2 ^ j) / 4096 ^ n = A / 4096 ^ n :=
    div_add_pow_mul_of_lt (b := 4096) (by decide) A (2 ^ j) i n hb1 (by omega)
  have k2 : (A + 4096 ^ i * 2 ^ j + 4096 ^ j * 2 ^ i) / 4096 ^ n
      = (A + 4096 ^ i * 2 ^ j) / 4096 ^ n :=
    div_add_pow_mul_of_lt (b := 4096) (by decide) _ (2 ^ i) j n hb2' hj
  have hz : (A + 4096 ^ i * 2 ^ j + 4096 ^ j * 2 ^ i) / 4096 ^ n = 0 := by
    rw [k2, k1, Nat.div_eq_of_lt hA]
  exact Nat.lt_of_div_eq_zero (Nat.pow_pos (by decide)) hz

/-- The row-width invariant survives an `addEdge`. -/
theorem row_addEdge_lt (A n i j t : Nat) (hij : i < j) (hj : j < n) (hn : n ≤ 12)
    (hrow : ∀ s, row A s < 2 ^ n) (hfresh : edg A i j = 0) (hfresh' : edg A j i = 0) :
    row (A + 4096 ^ i * 2 ^ j + 4096 ^ j * 2 ^ i) t < 2 ^ n := by
  rw [row_addEdge A i j t hij (by omega) hfresh hfresh']
  by_cases h1 : t = i
  · have e1 : (if t = i then (2:Nat) ^ j else 0) = 2 ^ j := by simp [h1]
    have e2 : (if t = j then (2:Nat) ^ i else 0) = 0 := by
      simp [show ¬ (t = j) from by omega]
    rw [e1, e2, Nat.add_zero]
    exact add_two_pow_lt (row A t) j n (hrow t) hj (by rw [h1]; exact hfresh)
  · by_cases h1' : t = j
    · have e1 : (if t = i then (2:Nat) ^ j else 0) = 0 := by simp [h1]
      have e2 : (if t = j then (2:Nat) ^ i else 0) = 2 ^ i := by simp [h1']
      rw [e1, e2, Nat.add_zero]
      exact add_two_pow_lt (row A t) i n (hrow t) (by omega) (by rw [h1']; exact hfresh')
    · have e1 : (if t = i then (2:Nat) ^ j else 0) = 0 := by simp [h1]
      have e2 : (if t = j then (2:Nat) ^ i else 0) = 0 := by simp [h1']
      rw [e1, e2]
      simpa using hrow t

/-! ### The falsification

Concretely: `A = 4096` is the adjacency word whose only set bit is bit `0` of row
`1` — i.e. `1 ~ 0` is recorded but `0 ~ 1` is not.  It satisfies the plan's
`hfresh` at `(i, j) = (0, 1)`.  Adding the pair writes `2 ^ 0` into row `1`, which
already holds `2 ^ 0`; the carry moves the bit to position `1` and `edg A' 1 0`
comes out `0`, not the `1` the plan claims. -/

theorem plan_edg_addEdge_false :
    ¬ ∀ (A i j i' j' : Nat), A < 4096 ^ 12 → i < j → j < 12 → edg A i j = 0 →
        edg (A + 4096 ^ i * 2 ^ j + 4096 ^ j * 2 ^ i) i' j'
          = if (i' = i ∧ j' = j) ∨ (i' = j ∧ j' = i) then 1 else edg A i' j' := by
  intro h
  have hA : (4096 : Nat) < 4096 ^ 12 := by
    have h10 : 0 < (4096 : Nat) ^ 10 := Nat.pow_pos (by decide)
    have e12 : (4096 : Nat) ^ 12 = 4096 ^ 10 * 4096 * 4096 := by
      rw [Nat.pow_succ, Nat.pow_succ]
    rw [e12]
    calc (4096 : Nat) < 1 * 4096 * 4096 := by decide
      _ ≤ 4096 ^ 10 * 4096 * 4096 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h10)
  have bad := h 4096 0 1 1 0 hA (by decide) (by decide) (by decide)
  revert bad
  decide

/-- Sanity, the positive direction: on a *symmetric* `A` the corrected lemma
delivers the plan's intended conclusion at both ends of the new edge. -/
example : edg (0 + 4096 ^ 0 * 2 ^ 1 + 4096 ^ 1 * 2 ^ 0) 1 0 = 1 := by decide
example : edg (0 + 4096 ^ 0 * 2 ^ 1 + 4096 ^ 1 * 2 ^ 0) 0 1 = 1 := by decide

/-! ### Regression checks against the definitions (kernel-evaluated)

These pin the *meaning* of the two extraction theorems, not just their types. -/

-- `packK [3, 5, 9]`: slot 0 has letters {0,1}, slot 1 has {0,2}, slot 2 has {0,3}.
example : msk (packK [3, 5, 9]) 0 = 3 := by decide
example : msk (packK [3, 5, 9]) 1 = 5 := by decide
example : msk (packK [3, 5, 9]) 2 = 9 := by decide
example : msk (packK [3, 5, 9]) 3 = 0 := by decide   -- past the end
example : kwt (packK [3, 5, 9]) 1 = 2 := by decide
example : packK [3, 5, 9] < 16 ^ 3 := by decide

-- `packA [2, 1, 0]`: the single shell edge `0 ~ 1`.
example : row (packA [2, 1, 0]) 1 = 1 := by decide
example : edg (packA [2, 1, 0]) 0 1 = 1 := by decide
example : edg (packA [2, 1, 0]) 1 0 = 1 := by decide
example : edg (packA [2, 1, 0]) 0 2 = 0 := by decide
example : edg (packA [2, 1, 0]) 5 3 = 0 := by decide  -- past the end
example : deg 3 (packA [2, 1, 0]) 0 = 1 := by decide

-- `packA` of a 12-slot list is a legal `A` for `Box`.
example : packA [2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] < 4096 ^ 12 := by decide

-- `edg_addEdge_add` at a live instance: add `2 ~ 5` to the word already holding `0 ~ 1`.
example :
    edg (packA [2, 1, 0, 0, 0, 0] + 4096 ^ 2 * 2 ^ 5 + 4096 ^ 5 * 2 ^ 2) 2 5 = 1 := by decide
example :
    edg (packA [2, 1, 0, 0, 0, 0] + 4096 ^ 2 * 2 ^ 5 + 4096 ^ 5 * 2 ^ 2) 5 2 = 1 := by decide
example :
    edg (packA [2, 1, 0, 0, 0, 0] + 4096 ^ 2 * 2 ^ 5 + 4096 ^ 5 * 2 ^ 2) 0 1 = 1 := by decide
example :
    edg (packA [2, 1, 0, 0, 0, 0] + 4096 ^ 2 * 2 ^ 5 + 4096 ^ 5 * 2 ^ 2) 2 3 = 0 := by decide

end Pack
end Delta4Model
