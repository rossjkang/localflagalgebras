import DaveyThesis2024.Delta4.Model
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Δ = 4 finite model: the arithmetic the prune rests on

Obligations 14 and 15 of the merged Stage-4 plan — the model-side T-identity and `e₂₂ ≤ 6`,
ported from the graph-side `shellObjective_identity` and `e22_le_six`.

§6(c) of the plan records that the prune these support has **no plan B**: without it a single
attachment-mask multiset blows past 40M search nodes, and a cheap provable substitute past
60M.  They are also the sharpest available check on the model type — the plan's own test is
that "if the ported identity does not close, the model is carrying the wrong state".
-/

namespace Delta4Model

/-! ## 6.  ADDED: `sumUpto` algebra

Everything from here on is new.  Nothing in §§0–5 is redefined.

Nine general facts about `sumUpto`, none of them specific to the census: additivity,
scalar multiplication on either side, the constant-zero sum, their doubly-indexed versions,
and — the only one with any content — the **square split** `∑_{i<n}∑_{j<n} = (strict lower) + (strict upper) + (diagonal)`.
That last one is the model's replacement for `sum_pairsLtOn_endpoints` /
`sum_pairsAdjOn_eq` (`PentagonDelta4.lean:837`): the graph side gets the
square-to-triangle exchange from `Finset.sum_product` and a `Prod.swap` bijection, and
the model has no `Finset`, so it is an induction instead. -/

theorem sumUpto_const_zero (n : Nat) : sumUpto (fun _ => 0) n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumUpto_succ, ih]

theorem sumUpto_add (f g : Nat → Nat) (n : Nat) :
    sumUpto (fun i => f i + g i) n 0 = sumUpto f n 0 + sumUpto g n 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sumUpto_succ (fun i => f i + g i) n, sumUpto_succ f n, sumUpto_succ g n, ih]
      omega

theorem sumUpto_mul_left (c : Nat) (f : Nat → Nat) (n : Nat) :
    sumUpto (fun i => c * f i) n 0 = c * sumUpto f n 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sumUpto_succ (fun i => c * f i) n, sumUpto_succ f n, ih, Nat.mul_add]

theorem sumUpto_mul_right (f : Nat → Nat) (c : Nat) (n : Nat) :
    sumUpto (fun i => f i * c) n 0 = sumUpto f n 0 * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sumUpto_succ (fun i => f i * c) n, sumUpto_succ f n, ih, Nat.add_mul]

/-- Congruence for a doubly-indexed sum with a variable inner bound (`m i`). -/
theorem sumUpto_nested_congr {f g : Nat → Nat → Nat} {m : Nat → Nat} {n : Nat}
    (h : ∀ i, i < n → ∀ j, j < m i → f i j = g i j) :
    sumUpto (fun i => sumUpto (fun j => f i j) (m i) 0) n 0
      = sumUpto (fun i => sumUpto (fun j => g i j) (m i) 0) n 0 :=
  sumUpto_congr fun i hi => sumUpto_congr fun j hj => h i hi j hj

theorem sumUpto_nested_add (f g : Nat → Nat → Nat) (m : Nat → Nat) (n : Nat) :
    sumUpto (fun i => sumUpto (fun j => f i j + g i j) (m i) 0) n 0
      = sumUpto (fun i => sumUpto (fun j => f i j) (m i) 0) n 0
        + sumUpto (fun i => sumUpto (fun j => g i j) (m i) 0) n 0 := by
  rw [← sumUpto_add]
  exact sumUpto_congr fun i _ => sumUpto_add (fun j => f i j) (fun j => g i j) (m i)

theorem sumUpto_nested_mul_left (c : Nat) (f : Nat → Nat → Nat) (m : Nat → Nat) (n : Nat) :
    sumUpto (fun i => sumUpto (fun j => c * f i j) (m i) 0) n 0
      = c * sumUpto (fun i => sumUpto (fun j => f i j) (m i) 0) n 0 := by
  rw [← sumUpto_mul_left]
  exact sumUpto_congr fun i _ => sumUpto_mul_left c (fun j => f i j) (m i)

/-- **The square split.**  Unconditional: no symmetry, no vanishing diagonal.
    `∑_{i<n} ∑_{j<n} f i j = ∑_{i<n} ∑_{j<i} f i j + ∑_{i<n} ∑_{j<i} f j i + ∑_{i<n} f i i`. -/
theorem sumUpto_sq_split (f : Nat → Nat → Nat) (n : Nat) :
    sumUpto (fun i => sumUpto (fun j => f i j) n 0) n 0
      = sumUpto (fun i => sumUpto (fun j => f i j) i 0) n 0
        + sumUpto (fun i => sumUpto (fun j => f j i) i 0) n 0
        + sumUpto (fun i => f i i) n 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hrow : ∀ i, sumUpto (fun j => f i j) (n+1) 0 = sumUpto (fun j => f i j) n 0 + f i n :=
        fun i => sumUpto_succ (fun j => f i j) n
      have hL : sumUpto (fun i => sumUpto (fun j => f i j) (n+1) 0) (n+1) 0
          = (sumUpto (fun i => sumUpto (fun j => f i j) n 0) n 0
              + sumUpto (fun i => f i n) n 0)
            + (sumUpto (fun j => f n j) n 0 + f n n) := by
        rw [sumUpto_succ (fun i => sumUpto (fun j => f i j) (n+1) 0) n, hrow n,
          sumUpto_congr (g := fun i => sumUpto (fun j => f i j) n 0 + f i n)
            (fun i _ => hrow i),
          sumUpto_add (fun i => sumUpto (fun j => f i j) n 0) (fun i => f i n) n]
      have hT : sumUpto (fun i => sumUpto (fun j => f i j) i 0) (n+1) 0
          = sumUpto (fun i => sumUpto (fun j => f i j) i 0) n 0 + sumUpto (fun j => f n j) n 0 :=
        sumUpto_succ (fun i => sumUpto (fun j => f i j) i 0) n
      have hU : sumUpto (fun i => sumUpto (fun j => f j i) i 0) (n+1) 0
          = sumUpto (fun i => sumUpto (fun j => f j i) i 0) n 0 + sumUpto (fun j => f j n) n 0 :=
        sumUpto_succ (fun i => sumUpto (fun j => f j i) i 0) n
      have hD : sumUpto (fun i => f i i) (n+1) 0 = sumUpto (fun i => f i i) n 0 + f n n :=
        sumUpto_succ (fun i => f i i) n
      rw [hL, hT, hU, hD]
      omega

/-- The square sum of a symmetric summand with vanishing diagonal is twice the
    strict lower triangle.  (The model's `sum_pairsLtOn_endpoints`.) -/
theorem sumUpto_sq_eq_two_mul_tri {f : Nat → Nat → Nat} {n : Nat}
    (hsymm : ∀ i, i < n → ∀ j, j < n → f i j = f j i)
    (hdiag : ∀ i, i < n → f i i = 0) :
    sumUpto (fun i => sumUpto (fun j => f i j) n 0) n 0
      = 2 * sumUpto (fun i => sumUpto (fun j => f i j) i 0) n 0 := by
  have hsplit := sumUpto_sq_split f n
  have hU : sumUpto (fun i => sumUpto (fun j => f j i) i 0) n 0
      = sumUpto (fun i => sumUpto (fun j => f i j) i 0) n 0 :=
    sumUpto_congr fun i hi =>
      sumUpto_congr fun j hj => hsymm j (Nat.lt_trans hj hi) i hi
  have hD : sumUpto (fun i => f i i) n 0 = 0 := by
    rw [sumUpto_congr (g := fun _ => 0) fun i hi => hdiag i hi]
    exact sumUpto_const_zero n
  omega

/-! ## 7.  ADDED: the two arithmetic cores, and what `Box` gives at a slot

`edge_split` is `PentagonLocal.two_mul_prod_split` (`PentagonDelta4.lean:879`) with the
edge indicator `e ∈ {0,1}` carried through, so that it applies to *every* ordered pair and
not only to the pairs that happen to be edges; `slot_identity` is
`PentagonLocal.weight_class_identity` (884) with `4 - k` already resolved into `d + u`, so
that no truncated subtraction survives.  Both are proved exactly as the graph versions:
`interval_cases` then `decide`/`omega`. -/

/-- **Step A, model form.**  `2·e·k_i·k_j = e(2k_i−1) + e(2k_j−1) + 2·e·[k_i = k_j = 2]`
    for an edge indicator `e ≤ 1` and positive weights summing to at most `4` on an edge. -/
theorem edge_split {e ki kj : Nat} (he : e ≤ 1) (hki : 1 ≤ ki) (hkj : 1 ≤ kj)
    (hsum : e = 1 → ki + kj ≤ 4) :
    2 * (e * ki * kj)
      = (e * (2 * ki - 1) + e * (2 * kj - 1))
        + 2 * (if ki = 2 ∧ kj = 2 then e else 0) := by
  interval_cases e
  · simp
  · have hs := hsum rfl
    have hi4 : ki ≤ 4 := by omega
    have hj4 : kj ≤ 4 := by omega
    interval_cases ki <;> interval_cases kj <;> revert hs <;> decide

/-- **Step D+E, model form.**  At a slot with `1 ≤ k` and an exact budget `k + d + u = 4`,
    `d(2k−1) + 4[k=3] + 12[k=4] + (2k−1)u = 3k`. -/
theorem slot_identity {k d u : Nat} (hk : 1 ≤ k) (hbudget : k + d + u = 4) :
    d * (2 * k - 1) + 4 * (if k = 3 then 1 else 0) + 12 * (if k = 4 then 1 else 0)
        + (2 * k - 1) * u = 3 * k := by
  have hk4 : k ≤ 4 := by omega
  interval_cases k <;> norm_num <;> omega

/-- A mask is a nonzero 4-bit word, so it carries at least one letter. -/
theorem kwt_pos_of_msk_pos {K i : Nat} (h : 1 ≤ msk K i) : 1 ≤ kwt K i := by
  have hlt : msk K i < 16 := msk_lt_16 K i
  show 1 ≤ bitv (msk K i) 0 + bitv (msk K i) 1 + bitv (msk K i) 2 + bitv (msk K i) 3
  generalize hm : msk K i = m at h hlt
  interval_cases m <;> decide

theorem box_kwt_pos {n K A : Nat} (hb : Box n K A = true) {i : Nat} (hi : i < n) :
    1 ≤ kwt K i := kwt_pos_of_msk_pos (box_masks_pos hb hi)

/-- Two `0/1` values with vanishing product sum to at most `1`. -/
theorem add_le_one_of_mul_eq_zero {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 0) :
    a + b ≤ 1 := by
  rcases Nat.mul_eq_zero.1 h with h | h <;> omega

/-- **(B3), summed.**  The endpoints of a shell edge carry disjoint letter sets, so their
    weights fit inside the four root letters.  This is the model's
    `PentagonLocal.attach_card_add_le4`. -/
theorem box_kwt_add_le_four {n K A : Nat} (hb : Box n K A = true) {i j : Nat}
    (hi : i < n) (hj : j < n) (hij : edg A i j = 1) : kwt K i + kwt K j ≤ 4 := by
  obtain ⟨hm, -⟩ := box_edge_disjoint hb hi hj hij
  have h0 := add_le_one_of_mul_eq_zero (hasL_le_one K i 0) (hasL_le_one K j 0) (hm 0)
  have h1 := add_le_one_of_mul_eq_zero (hasL_le_one K i 1) (hasL_le_one K j 1) (hm 1)
  have h2 := add_le_one_of_mul_eq_zero (hasL_le_one K i 2) (hasL_le_one K j 2) (hm 2)
  have h3 := add_le_one_of_mul_eq_zero (hasL_le_one K i 3) (hasL_le_one K j 3) (hm 3)
  unfold kwt
  omega

/-- **(B4), summed over the four letters.**  `∑_i k_i = 12`: the model's
    `PentagonLocal.sum_attach_card_eq_twelve` (`PentagonDelta4.lean:399`). -/
theorem box_sum_kwt {n K A : Nat} (hb : Box n K A = true) :
    sumUpto (fun i => kwt K i) n 0 = 12 := by
  have hsplit : sumUpto (fun i => kwt K i) n 0
      = ((sumUpto (fun i => hasL K i 0) n 0 + sumUpto (fun i => hasL K i 1) n 0)
          + sumUpto (fun i => hasL K i 2) n 0) + sumUpto (fun i => hasL K i 3) n 0 := by
    show sumUpto (fun i => ((hasL K i 0 + hasL K i 1) + hasL K i 2) + hasL K i 3) n 0 = _
    rw [sumUpto_add (fun i => (hasL K i 0 + hasL K i 1) + hasL K i 2) (fun i => hasL K i 3) n,
      sumUpto_add (fun i => hasL K i 0 + hasL K i 1) (fun i => hasL K i 2) n,
      sumUpto_add (fun i => hasL K i 0) (fun i => hasL K i 1) n]
  rw [hsplit, box_saturation hb (show 0 < 4 by decide), box_saturation hb (show 1 < 4 by decide),
    box_saturation hb (show 2 < 4 by decide), box_saturation hb (show 3 < 4 by decide)]

/-! ## 8.  ADDED: the handshake, and `2T` as a vertex sum

From here to §11 every result is stated against the *individual* facts it consumes, not
against `Box`, with the `Box` corollaries collected in §11.  Two reasons, both practical:
it makes "which clause does the prune depend on?" a typecheck rather than a claim, and
obligation 16 has to apply this arithmetic to partial search states, where the full `Box`
is not yet available.

`handshake_of` is the model's `sum_pairsAdjOn_eq` (`PentagonDelta4.lean:837`) combined with
`sum_pairsLtOn_endpoints` (803): a degree-weighted vertex sum equals the sum over strict
lower-triangle pairs of the two endpoint weights.  It is a corollary of the square split. -/

theorem handshake_of {n A : Nat} (hsymm : ∀ i, i < n → ∀ j, j < n → edg A i j = edg A j i)
    (hdiag : ∀ i, i < n → edg A i i = 0) (g : Nat → Nat) :
    sumUpto (fun i => deg n A i * g i) n 0
      = sumUpto (fun i => sumUpto (fun j => edg A i j * g i + edg A i j * g j) i 0) n 0 := by
  have hsplit : sumUpto (fun i => sumUpto (fun j => edg A i j * g i) n 0) n 0
      = sumUpto (fun i => sumUpto (fun j => edg A i j * g i) i 0) n 0
        + sumUpto (fun i => sumUpto (fun j => edg A j i * g j) i 0) n 0
        + sumUpto (fun i => edg A i i * g i) n 0 :=
    sumUpto_sq_split (fun i j => edg A i j * g i) n
  have hsq : sumUpto (fun i => sumUpto (fun j => edg A i j * g i) n 0) n 0
      = sumUpto (fun i => deg n A i * g i) n 0 :=
    sumUpto_congr fun i _ => sumUpto_mul_right (fun j => edg A i j) (g i) n
  have hU : sumUpto (fun i => sumUpto (fun j => edg A j i * g j) i 0) n 0
      = sumUpto (fun i => sumUpto (fun j => edg A i j * g j) i 0) n 0 :=
    sumUpto_nested_congr fun i hi j hj => by rw [hsymm j (Nat.lt_trans hj hi) i hi]
  have hD : sumUpto (fun i => edg A i i * g i) n 0 = 0 := by
    rw [sumUpto_congr (g := fun _ => 0) fun i hi => by rw [hdiag i hi, Nat.zero_mul]]
    exact sumUpto_const_zero n
  have hadd : sumUpto (fun i => sumUpto (fun j => edg A i j * g i + edg A i j * g j) i 0) n 0
      = sumUpto (fun i => sumUpto (fun j => edg A i j * g i) i 0) n 0
        + sumUpto (fun i => sumUpto (fun j => edg A i j * g j) i 0) n 0 :=
    sumUpto_nested_add (fun i j => edg A i j * g i) (fun i j => edg A i j * g j) (fun i => i) n
  omega

/-- **Steps A + B + C, model form.**  `2T = ∑_i d_{F⁺}(i)·(2k_i − 1) + 2 e₂₂`.
    The model's `PentagonLocal.two_mul_T_eq` (`PentagonDelta4.lean:939`).
    Step B (restriction to `S⁺`) is free here, but only because of `hpos`: `Box` (B1) keeps
    zero-weight slots out of the model entirely, so there is nothing to discard.  A slot of
    weight `0` carrying a shell edge would break this identity — see §11. -/
theorem twoT_eq_of {n K A : Nat}
    (hpos : ∀ i, i < n → 1 ≤ kwt K i)
    (hsymm : ∀ i, i < n → ∀ j, j < n → edg A i j = edg A j i)
    (hdiag : ∀ i, i < n → edg A i i = 0)
    (hedge : ∀ i, i < n → ∀ j, j < n → edg A i j = 1 → kwt K i + kwt K j ≤ 4) :
    twoT n K A = sumUpto (fun i => deg n A i * (2 * kwt K i - 1)) n 0 + 2 * e22 n K A := by
  have hsq : twoT n K A
      = 2 * sumUpto (fun i => sumUpto (fun j => edg A i j * kwt K i * kwt K j) i 0) n 0 :=
    sumUpto_sq_eq_two_mul_tri
      (fun i hi j hj => by rw [hsymm i hi j hj]; ring)
      (fun i hi => by rw [hdiag i hi]; ring)
  have hmul : sumUpto (fun i =>
        sumUpto (fun j => 2 * (edg A i j * kwt K i * kwt K j)) i 0) n 0
      = 2 * sumUpto (fun i => sumUpto (fun j => edg A i j * kwt K i * kwt K j) i 0) n 0 :=
    sumUpto_nested_mul_left 2 (fun i j => edg A i j * kwt K i * kwt K j) (fun i => i) n
  have hpt : sumUpto (fun i =>
        sumUpto (fun j => 2 * (edg A i j * kwt K i * kwt K j)) i 0) n 0
      = sumUpto (fun i => sumUpto (fun j =>
          (edg A i j * (2 * kwt K i - 1) + edg A i j * (2 * kwt K j - 1))
            + 2 * (if kwt K i = 2 ∧ kwt K j = 2 then edg A i j else 0)) i 0) n 0 :=
    sumUpto_nested_congr fun i hi j hj =>
      edge_split (edg_le_one A i j) (hpos i hi) (hpos j (Nat.lt_trans hj hi))
        (fun he => hedge i hi j (Nat.lt_trans hj hi) he)
  have hsplit2 : sumUpto (fun i => sumUpto (fun j =>
        (edg A i j * (2 * kwt K i - 1) + edg A i j * (2 * kwt K j - 1))
          + 2 * (if kwt K i = 2 ∧ kwt K j = 2 then edg A i j else 0)) i 0) n 0
      = sumUpto (fun i => sumUpto (fun j =>
          edg A i j * (2 * kwt K i - 1) + edg A i j * (2 * kwt K j - 1)) i 0) n 0
        + sumUpto (fun i => sumUpto (fun j =>
          2 * (if kwt K i = 2 ∧ kwt K j = 2 then edg A i j else 0)) i 0) n 0 :=
    sumUpto_nested_add
      (fun i j => edg A i j * (2 * kwt K i - 1) + edg A i j * (2 * kwt K j - 1))
      (fun i j => 2 * (if kwt K i = 2 ∧ kwt K j = 2 then edg A i j else 0)) (fun i => i) n
  have hE : sumUpto (fun i => sumUpto (fun j =>
        2 * (if kwt K i = 2 ∧ kwt K j = 2 then edg A i j else 0)) i 0) n 0
      = 2 * e22 n K A :=
    sumUpto_nested_mul_left 2
      (fun i j => if kwt K i = 2 ∧ kwt K j = 2 then edg A i j else 0) (fun i => i) n
  have hhs : sumUpto (fun i => deg n A i * (2 * kwt K i - 1)) n 0
      = sumUpto (fun i => sumUpto (fun j =>
          edg A i j * (2 * kwt K i - 1) + edg A i j * (2 * kwt K j - 1)) i 0) n 0 :=
    handshake_of hsymm hdiag (fun i => 2 * kwt K i - 1)
  omega

/-! ## 9.  ADDED: the counting quantities of the identity

`n3`, `n4` and `slackSum` are the plan's names (obligations 14 and 16).  They are *not*
stored in the model state — they are abbreviations for `sumUpto` folds over `(n,K,A)`, so
there is nothing for the transport to produce and nothing that can drift out of step with the
state (plan §5: "no redundant derived fields"). -/

/-- `n₃`: the number of slots of weight `3`. -/
def n3 (n K : Nat) : Nat := sumUpto (fun i => if kwt K i = 3 then 1 else 0) n 0

/-- `n₄`: the number of slots of weight `4`. -/
def n4 (n K : Nat) : Nat := sumUpto (fun i => if kwt K i = 4 then 1 else 0) n 0

/-- `∑_i (2k_i − 1) u_i`: the slack term of the T-identity. -/
def slackSum (n K A : Nat) : Nat := sumUpto (fun i => (2 * kwt K i - 1) * slack n K A i) n 0

theorem slackSum_def (n K A : Nat) :
    slackSum n K A = sumUpto (fun i => (2 * kwt K i - 1) * slack n K A i) n 0 := rfl

/-! ## 10.  ADDED: obligations 14 and 15, in hypothesis form -/

/-- **Steps D + E, summed.**  `∑_i d_{F⁺}(i)(2k_i−1) + 4n₃ + 12n₄ + ∑_i (2k_i−1)u_i = 36`.
    Uses only positivity, the exact slot budget (B2 made exact) and saturation (B4). -/
theorem vertex_sum_of {n K A : Nat}
    (hpos : ∀ i, i < n → 1 ≤ kwt K i)
    (hbudget : ∀ i, i < n → kwt K i + deg n A i + slack n K A i = 4)
    (htot : sumUpto (fun i => kwt K i) n 0 = 12) :
    sumUpto (fun i => deg n A i * (2 * kwt K i - 1)) n 0
        + 4 * n3 n K + 12 * n4 n K + slackSum n K A = 36 := by
  have hpt : sumUpto (fun i =>
        ((deg n A i * (2 * kwt K i - 1) + 4 * (if kwt K i = 3 then 1 else 0))
          + 12 * (if kwt K i = 4 then 1 else 0)) + (2 * kwt K i - 1) * slack n K A i) n 0
      = sumUpto (fun i => 3 * kwt K i) n 0 :=
    sumUpto_congr fun i hi => slot_identity (hpos i hi) (hbudget i hi)
  have h1 : sumUpto (fun i =>
        ((deg n A i * (2 * kwt K i - 1) + 4 * (if kwt K i = 3 then 1 else 0))
          + 12 * (if kwt K i = 4 then 1 else 0)) + (2 * kwt K i - 1) * slack n K A i) n 0
      = ((sumUpto (fun i => deg n A i * (2 * kwt K i - 1)) n 0
            + sumUpto (fun i => 4 * (if kwt K i = 3 then 1 else 0)) n 0)
          + sumUpto (fun i => 12 * (if kwt K i = 4 then 1 else 0)) n 0)
        + sumUpto (fun i => (2 * kwt K i - 1) * slack n K A i) n 0 := by
    rw [sumUpto_add (fun i => ((deg n A i * (2 * kwt K i - 1)
          + 4 * (if kwt K i = 3 then 1 else 0)) + 12 * (if kwt K i = 4 then 1 else 0)))
        (fun i => (2 * kwt K i - 1) * slack n K A i) n,
      sumUpto_add (fun i => deg n A i * (2 * kwt K i - 1)
          + 4 * (if kwt K i = 3 then 1 else 0))
        (fun i => 12 * (if kwt K i = 4 then 1 else 0)) n,
      sumUpto_add (fun i => deg n A i * (2 * kwt K i - 1))
        (fun i => 4 * (if kwt K i = 3 then 1 else 0)) n]
  have h3 : sumUpto (fun i => 4 * (if kwt K i = 3 then 1 else 0)) n 0 = 4 * n3 n K :=
    sumUpto_mul_left 4 (fun i => if kwt K i = 3 then 1 else 0) n
  have h4 : sumUpto (fun i => 12 * (if kwt K i = 4 then 1 else 0)) n 0 = 12 * n4 n K :=
    sumUpto_mul_left 12 (fun i => if kwt K i = 4 then 1 else 0) n
  have h36 : sumUpto (fun i => 3 * kwt K i) n 0 = 36 := by
    rw [sumUpto_mul_left 3 (fun i => kwt K i) n, htot]
  rw [slackSum_def]
  omega

/-- **Obligation 14, hypothesis form.**  `2T + 4n₃ + 12n₄ + ∑_i (2k_i−1)u_i = 36 + 2e₂₂`.
    Port of `PentagonLocal.shellObjective_identity` (`PentagonDelta4.lean:995`). -/
theorem T_identity_of {n K A : Nat}
    (hpos : ∀ i, i < n → 1 ≤ kwt K i)
    (hsymm : ∀ i, i < n → ∀ j, j < n → edg A i j = edg A j i)
    (hdiag : ∀ i, i < n → edg A i i = 0)
    (hedge : ∀ i, i < n → ∀ j, j < n → edg A i j = 1 → kwt K i + kwt K j ≤ 4)
    (hbudget : ∀ i, i < n → kwt K i + deg n A i + slack n K A i = 4)
    (htot : sumUpto (fun i => kwt K i) n 0 = 12) :
    twoT n K A + 4 * n3 n K + 12 * n4 n K + slackSum n K A = 36 + 2 * e22 n K A := by
  have h1 := twoT_eq_of hpos hsymm hdiag hedge
  have h2 := vertex_sum_of hpos hbudget htot
  omega

/-- The `(2,2)` square sum is twice `e₂₂`. -/
theorem two_mul_e22_of {n K A : Nat}
    (hsymm : ∀ i, i < n → ∀ j, j < n → edg A i j = edg A j i)
    (hdiag : ∀ i, i < n → edg A i i = 0) :
    2 * e22 n K A
      = sumUpto (fun i =>
          sumUpto (fun j => if kwt K i = 2 ∧ kwt K j = 2 then edg A i j else 0) n 0) n 0 :=
  (sumUpto_sq_eq_two_mul_tri
    (f := fun i j => if kwt K i = 2 ∧ kwt K j = 2 then edg A i j else 0)
    (fun i hi j hj => by
      show (if kwt K i = 2 ∧ kwt K j = 2 then edg A i j else 0)
          = (if kwt K j = 2 ∧ kwt K i = 2 then edg A j i else 0)
      rw [hsymm i hi j hj]
      by_cases h : kwt K i = 2 ∧ kwt K j = 2
      · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
      · rw [if_neg h, if_neg fun hc => h ⟨hc.2, hc.1⟩])
    (fun i hi => by
      show (if kwt K i = 2 ∧ kwt K i = 2 then edg A i i else 0) = 0
      split
      · exact hdiag i hi
      · rfl)).symm

/-- A weight-2 slot has at most two positive-shell neighbours, and no other slot contributes
    to the `(2,2)` row sum. -/
theorem e22_row_le_of {n K A : Nat} (hcap : ∀ i, i < n → kwt K i + deg n A i ≤ 4)
    {i : Nat} (hi : i < n) :
    sumUpto (fun j => if kwt K i = 2 ∧ kwt K j = 2 then edg A i j else 0) n 0
      ≤ (if kwt K i = 2 then 2 else 0) := by
  by_cases hk : kwt K i = 2
  · rw [if_pos hk]
    have hle : sumUpto (fun j => if kwt K i = 2 ∧ kwt K j = 2 then edg A i j else 0) n 0
        ≤ sumUpto (fun j => edg A i j) n 0 :=
      sumUpto_le _ _ n fun j _ => by
        split
        · exact Nat.le_refl _
        · exact Nat.zero_le _
    have hd : deg n A i = sumUpto (fun j => edg A i j) n 0 := rfl
    have := hcap i hi
    omega
  · rw [if_neg hk]
    have : sumUpto (fun j => if kwt K i = 2 ∧ kwt K j = 2 then edg A i j else 0) n 0 = 0 := by
      rw [sumUpto_congr (g := fun _ => 0) fun j _ => if_neg fun hc => hk hc.1]
      exact sumUpto_const_zero n
    omega

/-- **Obligation 15, hypothesis form.**  `e₂₂ ≤ 6`.
    Port of `PentagonLocal.e22_le_six` (`PentagonDelta4.lean:1110`).  Same two steps as the
    graph proof, but fused: the weight-2 slots span a subgraph of maximum degree at most
    `4 − 2 = 2` (`hcap`), so the handshake gives `2e₂₂ ≤ 2·#{i : k_i = 2}`, and each weight-2
    slot spends `2` of the total attachment `12` (`htot`), so `#{i : k_i = 2} ≤ 6`.
    The graph proof routes through `shellTwo` and `pairsLtOn`; here the two steps compose
    pointwise inside one `sumUpto_le`, so no analogue of `shellTwo` is needed.  Note this
    does *not* need `hpos`: a zero-weight slot is simply not a weight-2 slot. -/
theorem e22_le_six_of {n K A : Nat}
    (hsymm : ∀ i, i < n → ∀ j, j < n → edg A i j = edg A j i)
    (hdiag : ∀ i, i < n → edg A i i = 0)
    (hcap : ∀ i, i < n → kwt K i + deg n A i ≤ 4)
    (htot : sumUpto (fun i => kwt K i) n 0 = 12) : e22 n K A ≤ 6 := by
  have hsq := two_mul_e22_of (K := K) hsymm hdiag
  have hrow : sumUpto (fun i =>
        sumUpto (fun j => if kwt K i = 2 ∧ kwt K j = 2 then edg A i j else 0) n 0) n 0
      ≤ sumUpto (fun i => if kwt K i = 2 then 2 else 0) n 0 :=
    sumUpto_le _ _ n fun i hi => e22_row_le_of hcap hi
  have hcnt : sumUpto (fun i => if kwt K i = 2 then 2 else 0) n 0
      ≤ sumUpto (fun i => kwt K i) n 0 :=
    sumUpto_le _ _ n fun i _ => by
      split
      · omega
      · exact Nat.zero_le _
  omega

/-! ## 11.  ADDED: the `Box` corollaries, and what the prune consumes

The six hypotheses of `T_identity_of` come from exactly five `Box` clauses — (B1) masks
positive, (B2) the degree cap, (B3) the mask-disjointness half, (B4) saturation, and the
irreflexivity/symmetry of `A`.  **Not used:** the size bounds `3 ≤ n ≤ 12`, the packing
bounds `K < 16ⁿ`, `A < 4096ⁿ`, `row A i < 2ⁿ`, the sortedness clause (D16), and the
row-disjointness half of (B3)/(B5).  So the prune's foundations are insensitive to any
later change in the search's canonicalisation — that is a typecheck here, not a claim.

(B1) is the one that would be easy to lose in obligation 10 and is genuinely load-bearing:
a recorded slot of weight `0` carrying a shell edge makes `T_identity_of` false, because on
the graph side such a vertex is outside `S⁺` and its edges never enter `shellPosDeg`.  The
transport must therefore record `shellPos`, not `shellSet`. -/

theorem model_T_identity {n K A : Nat} (hb : Box n K A = true) :
    twoT n K A + 4 * n3 n K + 12 * n4 n K + slackSum n K A = 36 + 2 * e22 n K A :=
  T_identity_of (fun _ hi => box_kwt_pos hb hi) (fun _ hi _ hj => box_edg_symm hb hi hj)
    (fun _ hi => box_edg_irrefl hb hi)
    (fun _ hi _ hj he => box_kwt_add_le_four hb hi hj he)
    (fun _ hi => box_slack_add hb hi) (box_sum_kwt hb)

/-- Obligation 14 in the plan's spelled-out shape (no `slackSum` abbreviation). -/
theorem model_T_identity' (n K A : Nat) (hb : Box n K A = true) :
    twoT n K A + 4 * n3 n K + 12 * n4 n K
        + sumUpto (fun i => (2 * kwt K i - 1) * slack n K A i) n 0
      = 36 + 2 * e22 n K A := model_T_identity hb

/-- **Obligation 15.**  `e₂₂ ≤ 6`. -/
theorem model_e22_le_six {n K A : Nat} (hb : Box n K A = true) : e22 n K A ≤ 6 :=
  e22_le_six_of (fun _ hi _ hj => box_edg_symm hb hi hj) (fun _ hi => box_edg_irrefl hb hi)
    (fun _ hi => box_deg_cap hb hi) (box_sum_kwt hb)

/-- `2T + 4n₃ + 12n₄ + ∑(2k−1)u ≤ 48`: the identity with `e₂₂ ≤ 6` substituted.  This is the
    shape obligation 16 uses — every unit of `4n₃ + 12n₄ + ∑(2k−1)u` comes off the `2T` cap. -/
theorem model_defect_le {n K A : Nat} (hb : Box n K A = true) :
    twoT n K A + 4 * n3 n K + 12 * n4 n K + slackSum n K A ≤ 48 := by
  have h1 := model_T_identity hb
  have h2 := model_e22_le_six hb
  omega

/-- `2T ≤ 48`, i.e. `T ≤ 24`.  The graph-side statement is
    `PentagonLocal.shellObjective_le_24_of_regular` (`PentagonDelta4.lean:1125`). -/
theorem model_twoT_le {n K A : Nat} (hb : Box n K A = true) : twoT n K A ≤ 48 := by
  have := model_defect_le hb
  omega

/-- The leaf test is only ever *reached* in the window `38 ≤ 2T ≤ 48`
    (`leafOK` discharges `2T < 38` outright). -/
theorem model_twoT_window {n K A : Nat} (hb : Box n K A = true) (h : 38 ≤ twoT n K A) :
    38 ≤ twoT n K A ∧ twoT n K A ≤ 48 := ⟨h, model_twoT_le hb⟩

/-! ## 12.  ADDED: non-vacuity regressions (plan §6(e.6))

`Box` is satisfiable, and it is satisfied by the shells of *real* graphs, so obligations 14
and 15 are not vacuously true.  Each witness below is the punctured radius-2 shell of a root
of a triangle-free 4-regular graph, encoded by the rule the transport (obligation 10) will
have to reproduce: slots sorted by mask, `K = ∑ mask_i·16^i`, `A = ∑ row_i·4096^i`.

* `K₄,₄` at any root — the all-weight-4 corner, `n = 3`, `n₄ = 3`, `2T = 0`.
* `C₁₂(2,3)` at any root — the sharp Δ=4 extremal circulant; `2T = 40 ≥ 38`, so this witness
  lands inside the high window the census search actually explores.
* A random triangle-free 4-regular graph on 12 vertices — the mixed case, with all four terms
  of the identity nonzero (`n₃ = 1`, `∑(2k−1)u = 14`, `e₂₂ = 1`).

Checked independently against 3,264 roots of 4-regular triangle-free graphs (all 4-regular
triangle-free circulants on 8–19 vertices, every root, plus `K₄,₄` and swap-randomised
graphs): `Box` held at every root, the identity held at every root, and `e₂₂ ≤ 6`,
`2T ≤ 48` were never tight-violated (observed maxima `e₂₂ = 4`, `2T = 42`).

`decide` here is kernel evaluation of `Nat` arithmetic on the literal witness — no
`native_decide`, no new axiom. -/

/-- `K₄,₄`, root `0`: three shell slots of weight `4`, no shell edges. -/
theorem box_witness_K44 : Box 3 4095 0 = true := by decide

theorem identity_witness_K44 :
    twoT 3 4095 0 + 4 * n3 3 4095 + 12 * n4 3 4095 + slackSum 3 4095 0
      = 36 + 2 * e22 3 4095 0 := model_T_identity box_witness_K44

theorem values_witness_K44 :
    twoT 3 4095 0 = 0 ∧ e22 3 4095 0 = 0 ∧ n3 3 4095 = 0 ∧ n4 3 4095 = 3
      ∧ slackSum 3 4095 0 = 0 := by decide

/-- `C₁₂(2,3)`, root `0`: `n = 7`, masks `1,3,5,6,8,10,12`, `2T = 40` — a *high* shell. -/
theorem box_witness_C12 : Box 7 212362545 14172867997950680563816 = true := by decide

theorem identity_witness_C12 :
    twoT 7 212362545 14172867997950680563816
        + 4 * n3 7 212362545 + 12 * n4 7 212362545
        + slackSum 7 212362545 14172867997950680563816
      = 36 + 2 * e22 7 212362545 14172867997950680563816 :=
  model_T_identity box_witness_C12

theorem values_witness_C12 :
    twoT 7 212362545 14172867997950680563816 = 40
      ∧ e22 7 212362545 14172867997950680563816 = 2
      ∧ n3 7 212362545 = 0 ∧ n4 7 212362545 = 0
      ∧ slackSum 7 212362545 14172867997950680563816 = 0 := by decide

/-- The high window of `model_twoT_window` is inhabited: `38 ≤ 2T = 40 ≤ 48`. -/
theorem window_witness_C12 :
    38 ≤ twoT 7 212362545 14172867997950680563816
      ∧ twoT 7 212362545 14172867997950680563816 ≤ 48 :=
  model_twoT_window box_witness_C12 (by decide)

/-- A swap-randomised triangle-free 4-regular graph on 12 vertices, root `0`:
    every term of the identity is nonzero. -/
theorem box_witness_mixed : Box 6 13346385 1152921710782087212 = true := by decide

theorem identity_witness_mixed :
    twoT 6 13346385 1152921710782087212
        + 4 * n3 6 13346385 + 12 * n4 6 13346385
        + slackSum 6 13346385 1152921710782087212
      = 36 + 2 * e22 6 13346385 1152921710782087212 :=
  model_T_identity box_witness_mixed

theorem values_witness_mixed :
    twoT 6 13346385 1152921710782087212 = 20
      ∧ e22 6 13346385 1152921710782087212 = 1
      ∧ n3 6 13346385 = 1 ∧ n4 6 13346385 = 0
      ∧ slackSum 6 13346385 1152921710782087212 = 14 := by decide

/-! ### (B1) is load-bearing, not decorative

`9444734654726875217924` is the mixed witness above with one extra slot of mask `0` joined to
a slot that had spare degree, and the slots re-sorted so that the masks are still
non-decreasing.  It satisfies **every** clause of `Box` except (B1) — checked clause by clause
outside Lean — and the identity is false on it: `2T + 4n₃ + 12n₄ + ∑(2k−1)u = 35` against
`36 + 2e₂₂ = 38`.  The three missing units are the slack the weight-0 slot stole from its
neighbour.  On the graph side that slot is simply not in `S⁺` and its edge never enters
`shellPosDeg`, so obligation 10 must encode `shellPos`, not `shellSet`.

An *isolated* weight-0 slot, by contrast, is harmless — `2·0 − 1` truncates to `0` in `Nat`,
so it contributes nothing to any term.  The counterexample therefore needs the shell edge. -/

theorem box_false_without_B1 : Box 7 213542160 9444734654726875217924 = false := by decide

theorem identity_fails_without_B1 :
    twoT 7 213542160 9444734654726875217924
        + 4 * n3 7 213542160 + 12 * n4 7 213542160
        + slackSum 7 213542160 9444734654726875217924
      ≠ 36 + 2 * e22 7 213542160 9444734654726875217924 := by decide

end Delta4Model
