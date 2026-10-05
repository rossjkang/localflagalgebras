import DaveyThesis2024.Delta4.Model

/-!
# Δ = 4 finite model: the saturated attachment-mask generator (plan obligation 19)

The outer loop of the Stage-4 finite check.  `Delta4Model.Box n K A` constrains `K` through
four clauses that mention `K` alone — canonical packing, mask positivity, sortedness,
saturation — and this file collapses the unbounded `∀ K` over those clauses to membership in
an explicit finite list.

## What is proved

* `msGen : Nat → List Nat` — structurally recursive, `Nat`-packed, no `native_decide`,
  no `sorry`, no new axiom.
* `msGen_complete : maskBox n K = true → K ∈ msGen n` — **completeness**, by induction on the
  slot count.  A proof, not a `decide`.
* `msGen_sound : K ∈ msGen n → maskBox n K = true` — **soundness**, likewise a proof.
* `mem_msGen_iff` — the two directions packaged: `K ∈ msGen n ↔ maskBox n K = true`.
* `msGen_complete_of_box : Box n K A = true → K ∈ msGen n` — the consumer-facing form.
* `maskBox_size : maskBox n K = true → n ≤ 12` and
  `msGen_eq_nil_of_thirteen_le : 13 ≤ n → msGen n = []` — the slot count is capped by
  saturation itself, not only by `Box`'s `(N)` clause.

`#print axioms` on `msGen_complete`, `msGen_complete_of_box`, `msGen_sound`, `mem_msGen_iff`,
`msGen_eq_nil_of_thirteen_le` reports `[propext, Quot.sound]`; the three kernel-computed
statements (`msGen_card_total`, `msGen_three`, `msGen_twelve`) report no axioms at all.

Completeness and soundness together say `msGen n` is *exactly* the set of admissible `K`, so
its cardinality is a falsifiable measurement rather than a tautology.  That is the guard the
merged plan's §6(e) asks for, and at its strongest layer (§6(e).1, "soundness does not rest on
the generator at all"): a generator that is incomplete but whose `Bool` check still returns
`true` cannot hide behind either of these two theorems, and cannot hide behind the counts
either.

## The measured 862

`msGen_card_0 … msGen_card_12` are kernel-checked cardinalities, one declaration per slot
count (the plan's §5 D10 chunking discipline, measured again in §7: one declaration covering
all thirteen thrashes and does not finish), and `msGen_card_total` adds them to **862** — the plan's independently
measured number of saturated attachment-mask multisets over a 4-element root with each letter
covered exactly three times.  The per-slot-count split is

    n    3   4   5    6    7    8   9  10  11  12
    #    1  14  92  221  249  172  81  25   6   1

and `n ≤ 2` and `n ≥ 13` are empty (the latter is `msGen_eq_nil_of_thirteen_le`, so **862 is
the total over every slot count**, not only over `3 ≤ n ≤ 12`).

Outside Lean the same numbers were reproduced twice independently: by the multiplicity
recursion of `enum5.py` (the script the plan's 862 came from) and by brute force over every
`K < 16 ^ n` for `n ≤ 6`.  The generated *sets*, not only the counts, agree with both.
`enum5.py` and `enum9.py` were re-run while preparing this file and still report `641572`
nodes / `7838` high configurations and `{19: 15, 20: 0, 21: 0, 24: 32}` minimum margins,
matching the recorded `enum9_out.txt` line for line.

For orientation: of the 862 words only slot counts `6 … 10` carry a high configuration
(`53, 153, 1204, 1276, 5152` of the 7838, on the `S4`-quotiented representatives).  The
generator deliberately does **not** pre-filter on that — the plan's §5 rules the `862 -> 151`
pre-filter worthless, and `msGen` has to be complete for all 862 anyway.

## The sortedness caveat, stated explicitly

Words are packed exactly as `Delta4Model.msk` reads them: `K = ∑_{i<n} m_i · 16 ^ i`, slot `0`
least significant.  The generator emits **sorted words only** — `m_0 ≤ m_1 ≤ … ≤ m_{n-1}` —
because sortedness is a `Box` clause (`STAGE4_PLAN_merged` §5, D16).  So completeness is
completeness *against the sorted representative*: a `K` whose masks are not non-decreasing is
not in `msGen n`, and is not claimed to be.  That is the right statement because `Box` already
refuses such a `K`; `maskBox` carries the same clause, and `maskBox_of_box` is what connects
the two.

## How this plugs into obligation 22

`Search.lean` closes `searchNP_leafOK_complete (n K A : Nat) (hbox : Box n K A = true)
(h : searchNP leafOK n K = true) : leafOK n K A = true`, i.e. it consumes the pair `(n, K)`,
not `K` alone.  `msGen` is indexed the same way, so the assembly is

  `Box n K A = true`
    → `n ≤ 12` (`Model.box_size`) and `K ∈ msGen n` (`msGen_complete_of_box`)
    → a finite disjunction over the 862 `(n, K)` pairs
    → per pair, the obligation-21 chunk fact `searchNP leafOK n K = true`
    → `searchNP_leafOK_complete` gives `leafOK n K A = true`.

Nothing in this file needs `A`, the search, or the prune; equally, nothing here supplies them.

## What is assumed

Nothing outside `DaveyThesis2024.Delta4.Model`.  In particular this file does **not** assume
the `boxDischarge` bridge (the obligation-14/15 hypothesis-form gap): it consumes
`Box … = true` directly, through `box_iff`, which is proved in `Model.lean`.  Plan §6(e) is
respected — no model quantity is redefined here; `maskBox` is a conjunction of `Box`'s own
clauses, written with `Delta4Model`'s own `msk`, `hasL`, `sumUpto` and `allUpto`.
-/

namespace Delta4Model

/-! ## 0.  Reading `bitv` at the four literal letters

The generator extracts mask bits with `/` and `%` at *literal* denominators rather than
through `2 ^ a`: at kernel-reduction speed that is worth roughly a factor of two, and these
four lemmas are what keep it the same function as `Delta4Model.bitv`. -/

theorem bitv_zero (m : Nat) : bitv m 0 = m % 2 := by
  show m / 2 ^ 0 % 2 = m % 2
  rw [Nat.pow_zero, Nat.div_one]

theorem bitv_one (m : Nat) : bitv m 1 = m / 2 % 2 := rfl
theorem bitv_two (m : Nat) : bitv m 2 = m / 4 % 2 := rfl
theorem bitv_three (m : Nat) : bitv m 3 = m / 8 % 2 := rfl

/-! ## 1.  Three arithmetic facts about `msk`, and a bottom-peeling `sumUpto` -/

/-- Slot `0` is the low base-16 digit. -/
theorem msk_zero (K : Nat) : msk K 0 = K % 16 := by simp [msk]

/-- Dividing by `16` shifts the slot index down by one. -/
theorem msk_div (K i : Nat) : msk (K / 16) i = msk K (i + 1) := by
  simp only [msk, Nat.div_div_eq_div_mul]
  rw [Nat.pow_succ, Nat.mul_comm (16 ^ i) 16]

/-- The same shift for the letter indicators. -/
theorem hasL_div (K i a : Nat) : hasL (K / 16) i a = hasL K (i + 1) a := by
  simp [hasL, msk_div]

theorem msk_pack {m w : Nat} (hm : m < 16) : msk (m + 16 * w) 0 = m := by
  rw [msk_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm]

theorem div_pack {m w : Nat} (hm : m < 16) : (m + 16 * w) / 16 = w := by
  rw [Nat.add_mul_div_left _ _ (by decide : 0 < 16), Nat.div_eq_of_lt hm, Nat.zero_add]

theorem msk_pack_succ {m w : Nat} (hm : m < 16) (i : Nat) :
    msk (m + 16 * w) (i + 1) = msk w i := by
  rw [← msk_div, div_pack hm]

theorem hasL_pack_succ {m w : Nat} (hm : m < 16) (i a : Nat) :
    hasL (m + 16 * w) (i + 1) a = hasL w i a := by
  simp [hasL, msk_pack_succ hm]

/-- `sumUpto` peeled at the **bottom** (`Model.sumUpto_succ` peels at the top). -/
theorem sumUpto_shift (f : Nat → Nat) (r : Nat) :
    sumUpto f (r + 1) 0 = f 0 + sumUpto (fun i => f (i + 1)) r 0 := by
  induction r with
  | zero => simp [sumUpto]
  | succ r ih =>
      rw [sumUpto_succ, ih, sumUpto_succ (fun i => f (i + 1)) r]
      omega

/-- A non-decreasing word is bounded below by its first letter. -/
theorem msk_mono_zero {K r : Nat} (hs : ∀ i, i + 1 < r → msk K i ≤ msk K (i + 1)) :
    ∀ j, j < r → msk K 0 ≤ msk K j := by
  intro j
  induction j with
  | zero => intro _; exact Nat.le_refl _
  | succ j ih => intro hj; exact Nat.le_trans (ih (by omega)) (hs j (by omega))

/-! ## 2.  The generator -/

/--
`genMask r lo c₀ c₁ c₂ c₃` lists every packed word `w = ∑_{t<r} m_t · 16 ^ t` with

* exactly `r` slots, each mask `m_t < 16`;
* `lo ≤ m₀ ≤ m₁ ≤ … ≤ m_{r-1}`;
* root letter `a` covered **exactly** `c_a` times, i.e. `∑_{t<r} bitv m_t a = c_a`.

Mask positivity is not a separate clause: the top-level call starts at `lo = 1` and the
non-decreasing invariant propagates it.  The guards are raw `Bool` (`Nat.ble`, `&&`, `bif`)
and the bit extractions use literal denominators — both purely for kernel-reduction speed;
§0 and `genMask_sound`/`genMask_complete` tie them back to `Delta4Model.bitv`.
-/
def genMask : Nat → Nat → Nat → Nat → Nat → Nat → List Nat
  | 0, _, c0, c1, c2, c3 =>
      bif Nat.beq c0 0 && Nat.beq c1 0 && Nat.beq c2 0 && Nat.beq c3 0 then [0] else []
  | r + 1, lo, c0, c1, c2, c3 =>
      (List.range' lo (16 - lo)).flatMap (fun m =>
        bif Nat.ble (m % 2) c0 && Nat.ble (m / 2 % 2) c1 && Nat.ble (m / 4 % 2) c2
              && Nat.ble (m / 8 % 2) c3 then
          (genMask r m (c0 - m % 2) (c1 - m / 2 % 2) (c2 - m / 4 % 2)
              (c3 - m / 8 % 2)).map (fun w => m + 16 * w)
        else [])

/-- The candidate `K` words for a shell of `n` slots: masks in `1..15`, non-decreasing, every
    root letter covered exactly three times. -/
def msGen (n : Nat) : List Nat := genMask n 1 3 3 3 3

/-! ## 3.  `maskBox`: the `K`-only clauses of `Box`, clause for clause -/

/--
The part of `Delta4Model.Box` that mentions `K` and not `A`.  Each conjunct is copied from
`Box` (`Model.lean` §5) and written with `Delta4Model`'s own quantities — nothing is
redefined here.  Clause for clause, against `Box`:

| `Box` clause | here |
|---|---|
| `decide (K < 16 ^ n)` (canonical packing) | identical |
| `allUpto (fun i => decide (1 <= msk K i)) n` — (B1) | identical |
| `allUpto (fun i => decide (msk K i <= msk K (i+1))) (n - 1)` — (D16) | identical |
| `allUpto (fun a => decide (sumUpto (fun i => hasL K i a) n 0 = 3)) 4` — (B4) | identical |

`Box`'s remaining clauses all mention `A` or only `n`, and none of them constrains `K`.
`maskBox_of_box` is the one-line consequence, via `Model.box_iff`.
-/
def maskBox (n K : Nat) : Bool :=
  decide (K < 16 ^ n)
  && allUpto (fun i => decide (1 ≤ msk K i)) n
  && allUpto (fun i => decide (msk K i ≤ msk K (i + 1))) (n - 1)
  && allUpto (fun a => decide (sumUpto (fun i => hasL K i a) n 0 = 3)) 4

theorem maskBox_of_box {n K A : Nat} (h : Box n K A = true) : maskBox n K = true := by
  have hb := (box_iff n K A).1 h
  simp only [maskBox, Bool.and_eq_true, decide_eq_true_eq, allUpto_eq_true_iff]
  exact ⟨⟨⟨hb.packK, hb.maskPos⟩, hb.sorted⟩, hb.sat⟩

theorem maskBox_pack {n K : Nat} (h : maskBox n K = true) : K < 16 ^ n := by
  simp only [maskBox, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1.1

theorem maskBox_pos {n K : Nat} (h : maskBox n K = true) : ∀ i, i < n → 1 ≤ msk K i := by
  simp only [maskBox, Bool.and_eq_true, decide_eq_true_eq, allUpto_eq_true_iff] at h
  exact h.1.1.2

theorem maskBox_sorted {n K : Nat} (h : maskBox n K = true) :
    ∀ i, i < n - 1 → msk K i ≤ msk K (i + 1) := by
  simp only [maskBox, Bool.and_eq_true, decide_eq_true_eq, allUpto_eq_true_iff] at h
  exact h.1.2

theorem maskBox_sat {n K : Nat} (h : maskBox n K = true) :
    ∀ a, a < 4 → sumUpto (fun i => hasL K i a) n 0 = 3 := by
  simp only [maskBox, Bool.and_eq_true, decide_eq_true_eq, allUpto_eq_true_iff] at h
  exact h.2

/-- `maskBox` is exactly the four clauses, packaged for the soundness direction. -/
theorem maskBox_intro {n K : Nat} (hpack : K < 16 ^ n)
    (hpos : ∀ i, i < n → 1 ≤ msk K i)
    (hsort : ∀ i, i < n - 1 → msk K i ≤ msk K (i + 1))
    (hsat : ∀ a, a < 4 → sumUpto (fun i => hasL K i a) n 0 = 3) : maskBox n K = true := by
  simp only [maskBox, Bool.and_eq_true, decide_eq_true_eq, allUpto_eq_true_iff]
  exact ⟨⟨⟨hpack, hpos⟩, hsort⟩, hsat⟩

/-! ## 4.  Completeness -/

/--
The induction carrying `msGen_complete`: a packed word of `r` slots, masks non-decreasing and
bounded below by `lo`, is generated at the coverage vector it actually realises.
-/
theorem genMask_complete : ∀ (r K lo : Nat), K < 16 ^ r →
    (∀ i, i < r → 1 ≤ msk K i) →
    (∀ i, i < r → lo ≤ msk K i) →
    (∀ i, i + 1 < r → msk K i ≤ msk K (i + 1)) →
    K ∈ genMask r lo (sumUpto (fun i => hasL K i 0) r 0) (sumUpto (fun i => hasL K i 1) r 0)
        (sumUpto (fun i => hasL K i 2) r 0) (sumUpto (fun i => hasL K i 3) r 0) := by
  intro r
  induction r with
  | zero =>
      intro K lo hK _ _ _
      have hK0 : K = 0 := by simpa using hK
      subst hK0
      simp [genMask, sumUpto]
  | succ r ih =>
      intro K lo hK hpos hlo hsorted
      have hm16 : msk K 0 < 16 := msk_lt_16 K 0
      have hsplit : msk K 0 + 16 * (K / 16) = K := by
        rw [msk_zero]; exact Nat.mod_add_div K 16
      have hK' : K / 16 < 16 ^ r := by
        rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 16)]
        rw [Nat.pow_succ] at hK; exact hK
      -- the coverage of `K` splits as (low digit) + (coverage of the shifted word)
      have hcov : ∀ a : Nat, sumUpto (fun i => hasL K i a) (r + 1) 0
          = bitv (msk K 0) a + sumUpto (fun i => hasL (K / 16) i a) r 0 := by
        intro a
        rw [sumUpto_shift (fun i => hasL K i a) r,
          sumUpto_congr (n := r) (f := fun i => hasL K (i + 1) a)
            (g := fun i => hasL (K / 16) i a) (fun i _ => (hasL_div K i a).symm)]
        rfl
      -- the shifted word inherits every hypothesis
      have hpos' : ∀ i, i < r → 1 ≤ msk (K / 16) i := by
        intro i hi; rw [msk_div]; exact hpos (i + 1) (by omega)
      have hlo' : ∀ i, i < r → msk K 0 ≤ msk (K / 16) i := by
        intro i hi; rw [msk_div]; exact msk_mono_zero hsorted (i + 1) (by omega)
      have hsorted' : ∀ i, i + 1 < r → msk (K / 16) i ≤ msk (K / 16) (i + 1) := by
        intro i hi; rw [msk_div, msk_div]; exact hsorted (i + 1) (by omega)
      have hrec := ih (K / 16) (msk K 0) hK' hpos' hlo' hsorted'
      -- assemble
      rw [genMask, List.mem_flatMap]
      refine ⟨msk K 0, List.mem_range'_1.2 ⟨hlo 0 (by omega), by omega⟩, ?_⟩
      rw [hcov 0, hcov 1, hcov 2, hcov 3]
      rw [bitv_zero, bitv_one, bitv_two, bitv_three]
      rw [show (Nat.ble (msk K 0 % 2)
              (msk K 0 % 2 + sumUpto (fun i => hasL (K / 16) i 0) r 0)
            && Nat.ble (msk K 0 / 2 % 2)
              (msk K 0 / 2 % 2 + sumUpto (fun i => hasL (K / 16) i 1) r 0)
            && Nat.ble (msk K 0 / 4 % 2)
              (msk K 0 / 4 % 2 + sumUpto (fun i => hasL (K / 16) i 2) r 0)
            && Nat.ble (msk K 0 / 8 % 2)
              (msk K 0 / 8 % 2 + sumUpto (fun i => hasL (K / 16) i 3) r 0)) = true from by
        simp [Nat.ble_eq]]
      simp only [cond_true, Nat.add_sub_cancel_left]
      exact List.mem_map.2 ⟨K / 16, hrec, hsplit⟩

/-- **Obligation 19, completeness.**  Every `K` satisfying the mask clauses of `Box` is
    generated. -/
theorem msGen_complete (n K : Nat) (h : maskBox n K = true) : K ∈ msGen n := by
  have hsat := maskBox_sat h
  have key := genMask_complete n K 1 (maskBox_pack h) (maskBox_pos h)
    (fun i hi => maskBox_pos h i hi) (fun i hi => maskBox_sorted h i (by omega))
  rw [hsat 0 (by decide), hsat 1 (by decide), hsat 2 (by decide), hsat 3 (by decide)] at key
  exact key

/-- The consumer-facing form: the outer loop of the finite check may range over `msGen n`. -/
theorem msGen_complete_of_box {n K A : Nat} (h : Box n K A = true) : K ∈ msGen n :=
  msGen_complete n K (maskBox_of_box h)

/-! ## 5.  Soundness -/

/--
Soundness: everything the generator emits really is a packed, sorted, `lo`-bounded word with
the prescribed coverage.  With `genMask_complete` this pins `msGen n` to *exactly* the
admissible set, which is what makes the cardinalities below a measurement.
-/
theorem genMask_sound : ∀ (r lo c0 c1 c2 c3 K : Nat),
    K ∈ genMask r lo c0 c1 c2 c3 →
      K < 16 ^ r
      ∧ (∀ i, i < r → lo ≤ msk K i)
      ∧ (∀ i, i + 1 < r → msk K i ≤ msk K (i + 1))
      ∧ sumUpto (fun i => hasL K i 0) r 0 = c0
      ∧ sumUpto (fun i => hasL K i 1) r 0 = c1
      ∧ sumUpto (fun i => hasL K i 2) r 0 = c2
      ∧ sumUpto (fun i => hasL K i 3) r 0 = c3 := by
  intro r
  induction r with
  | zero =>
      intro lo c0 c1 c2 c3 K hK
      rw [genMask] at hK
      cases hc : (Nat.beq c0 0 && Nat.beq c1 0 && Nat.beq c2 0 && Nat.beq c3 0) with
      | false => rw [hc, cond_false] at hK; simp at hK
      | true =>
          rw [hc, cond_true] at hK
          simp only [Bool.and_eq_true, Nat.beq_eq] at hc
          obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := hc
          simp only [List.mem_singleton] at hK
          subst hK; subst h0; subst h1; subst h2; subst h3
          exact ⟨by decide, fun i hi => absurd hi (Nat.not_lt_zero i),
            fun i hi => absurd hi (Nat.not_lt_zero _), rfl, rfl, rfl, rfl⟩
  | succ r ih =>
      intro lo c0 c1 c2 c3 K hK
      rw [genMask, List.mem_flatMap] at hK
      obtain ⟨m, hmr, hmem⟩ := hK
      obtain ⟨hlom, hmlt⟩ := List.mem_range'_1.1 hmr
      have hm16 : m < 16 := by omega
      cases hg : (Nat.ble (m % 2) c0 && Nat.ble (m / 2 % 2) c1 && Nat.ble (m / 4 % 2) c2
          && Nat.ble (m / 8 % 2) c3) with
      | false => rw [hg, cond_false] at hmem; simp at hmem
      | true =>
      rw [hg, cond_true] at hmem
      simp only [Bool.and_eq_true, Nat.ble_eq] at hg
      obtain ⟨⟨⟨hg0, hg1⟩, hg2⟩, hg3⟩ := hg
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hmem
      obtain ⟨hwlt, hwlo, hwsort, hw0, hw1, hw2, hw3⟩ := ih m _ _ _ _ w hw
      have hm0 : msk (m + 16 * w) 0 = m := msk_pack hm16
      have hms : ∀ i, msk (m + 16 * w) (i + 1) = msk w i := msk_pack_succ hm16
      have hcov : ∀ a, sumUpto (fun i => hasL (m + 16 * w) i a) (r + 1) 0
          = bitv m a + sumUpto (fun i => hasL w i a) r 0 := by
        intro a
        rw [sumUpto_shift (fun i => hasL (m + 16 * w) i a) r,
          sumUpto_congr (n := r) (f := fun i => hasL (m + 16 * w) (i + 1) a)
            (g := fun i => hasL w i a) (fun i _ => hasL_pack_succ hm16 i a)]
        simp [hasL, hm0]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Nat.pow_succ]
        calc m + 16 * w < 16 * (w + 1) := by omega
          _ ≤ 16 * 16 ^ r := Nat.mul_le_mul_left 16 hwlt
          _ = 16 ^ r * 16 := Nat.mul_comm _ _
      · intro i _
        cases i with
        | zero => rw [hm0]; exact hlom
        | succ j => rw [hms j]; exact Nat.le_trans hlom (hwlo j (by omega))
      · intro i hi
        cases i with
        | zero => rw [hm0, hms 0]; exact hwlo 0 (by omega)
        | succ j => rw [hms j, hms (j + 1)]; exact hwsort j (by omega)
      · rw [hcov 0, hw0, bitv_zero]; omega
      · rw [hcov 1, hw1, bitv_one]; omega
      · rw [hcov 2, hw2, bitv_two]; omega
      · rw [hcov 3, hw3, bitv_three]; omega

/-- **Obligation 19, soundness.**  Everything `msGen n` emits passes `maskBox`. -/
theorem msGen_sound {n K : Nat} (h : K ∈ msGen n) : maskBox n K = true := by
  obtain ⟨hlt, hlo, hsort, h0, h1, h2, h3⟩ := genMask_sound n 1 3 3 3 3 K h
  refine maskBox_intro hlt (fun i hi => hlo i hi) (fun i hi => hsort i (by omega)) ?_
  intro a ha
  rcases a with _ | _ | _ | _ | a
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · omega

/-- The two directions together: `msGen n` is *exactly* the admissible set. -/
theorem mem_msGen_iff (n K : Nat) : K ∈ msGen n ↔ maskBox n K = true :=
  ⟨msGen_sound, msGen_complete n K⟩

/-! ## 6.  `n ≤ 12` is forced, so thirteen declarations are exhaustive -/

/-- `∑_i k_i` splits into the four letter counts.  Proved by direct induction so that this
    file needs only `Model.lean`; `ModelArith.lean` derives the same splitting from its own
    `sumUpto_add` (see the landing note at the foot of the file). -/
theorem sumUpto_kwt_split (K n : Nat) :
    sumUpto (fun i => kwt K i) n 0
      = sumUpto (fun i => hasL K i 0) n 0 + sumUpto (fun i => hasL K i 1) n 0
        + sumUpto (fun i => hasL K i 2) n 0 + sumUpto (fun i => hasL K i 3) n 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sumUpto_succ (fun i => kwt K i) n, sumUpto_succ (fun i => hasL K i 0) n,
        sumUpto_succ (fun i => hasL K i 1) n, sumUpto_succ (fun i => hasL K i 2) n,
        sumUpto_succ (fun i => hasL K i 3) n, ih]
      show _ + (hasL K n 0 + hasL K n 1 + hasL K n 2 + hasL K n 3) = _
      omega

theorem sumUpto_ge_card {f : Nat → Nat} {n : Nat} (h : ∀ i, i < n → 1 ≤ f i) :
    n ≤ sumUpto f n 0 := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
      rw [sumUpto_succ]
      have h1 := ih (fun i hi => h i (by omega))
      have h2 := h n (by omega)
      omega

/-- A nonzero 4-bit mask carries at least one root letter.  (`ModelArith.lean:159` has the
    same statement as `kwt_pos_of_msk_pos`; see the landing note.) -/
theorem one_le_kwt {K i : Nat} (h : 1 ≤ msk K i) : 1 ≤ kwt K i := by
  have h16 := msk_lt_16 K i
  have e1 : msk K i / 2 / 2 = msk K i / 4 := by rw [Nat.div_div_eq_div_mul]
  have e2 : msk K i / 4 / 2 = msk K i / 8 := by rw [Nat.div_div_eq_div_mul]
  have e3 : msk K i / 8 / 2 = msk K i / 16 := by rw [Nat.div_div_eq_div_mul]
  simp only [kwt, hasL, bitv_zero, bitv_one, bitv_two, bitv_three]
  omega

/-- Saturation caps the slot count: twelve letter-slots, each mask using at least one. -/
theorem maskBox_size {n K : Nat} (h : maskBox n K = true) : n ≤ 12 := by
  have hpos := maskBox_pos h
  have hsat := maskBox_sat h
  have hsum : sumUpto (fun i => kwt K i) n 0 = 12 := by
    rw [sumUpto_kwt_split, hsat 0 (by decide), hsat 1 (by decide), hsat 2 (by decide),
      hsat 3 (by decide)]
  have := sumUpto_ge_card (f := fun i => kwt K i) (fun i hi => one_le_kwt (hpos i hi))
  omega

/-- Beyond twelve slots the generator is empty, so the thirteen cardinalities below account
    for **every** admissible `K`, at every slot count. -/
theorem msGen_eq_nil_of_thirteen_le {n : Nat} (h : 13 ≤ n) : msGen n = [] := by
  rcases hl : msGen n with _ | ⟨K, t⟩
  · rfl
  · exact absurd (maskBox_size (msGen_sound (n := n) (K := K) (by rw [hl]; exact List.mem_cons_self)))
      (by omega)

/-! ## 7.  The cross-check: the measured 862

Thirteen kernel-checked cardinalities, one declaration each.  That split is forced, and it is
the plan's §5 D10 chunking constraint showing up at a much smaller scale.  A single
declaration covering all thirteen was measured: it thrashed (GC-bound, ~3.8 GB of 16 GB) and
was still running after ten minutes, when it was killed.  The split runs in 68 s kernel /
1 min 41 s wall for the whole file, peak ~3.5 GB.

The generator is written for kernel-reduction speed for the same reason:
`List.range' lo (16 - lo)` rather than a scan from `0`, raw `Nat.ble`/`&&`/`bif` rather than
`Decidable` instances for `And`, and literal `/ 2, / 4, / 8` rather than `2 ^ a`.  Each of the
three was measured separately; together they are worth about 2.5x. -/

set_option maxRecDepth 100000 in
theorem msGen_card_0 : (msGen 0).length = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem msGen_card_1 : (msGen 1).length = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem msGen_card_2 : (msGen 2).length = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem msGen_card_3 : (msGen 3).length = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem msGen_card_4 : (msGen 4).length = 14 := by decide +kernel

set_option maxRecDepth 100000 in
theorem msGen_card_5 : (msGen 5).length = 92 := by decide +kernel

set_option maxRecDepth 100000 in
theorem msGen_card_6 : (msGen 6).length = 221 := by decide +kernel

set_option maxRecDepth 100000 in
theorem msGen_card_7 : (msGen 7).length = 249 := by decide +kernel

set_option maxRecDepth 100000 in
theorem msGen_card_8 : (msGen 8).length = 172 := by decide +kernel

set_option maxRecDepth 100000 in
theorem msGen_card_9 : (msGen 9).length = 81 := by decide +kernel

set_option maxRecDepth 100000 in
theorem msGen_card_10 : (msGen 10).length = 25 := by decide +kernel

set_option maxRecDepth 100000 in
theorem msGen_card_11 : (msGen 11).length = 6 := by decide +kernel

set_option maxRecDepth 100000 in
theorem msGen_card_12 : (msGen 12).length = 1 := by decide +kernel

/-- **862.**  The plan's measured number of saturated attachment-mask multisets over a
    4-element root with each letter covered exactly three times, reproduced inside the kernel.
    With `msGen_eq_nil_of_thirteen_le` this is the total over *all* slot counts. -/
theorem msGen_card_total :
    (msGen 0).length + (msGen 1).length + (msGen 2).length + (msGen 3).length
      + (msGen 4).length + (msGen 5).length + (msGen 6).length + (msGen 7).length
      + (msGen 8).length + (msGen 9).length + (msGen 10).length + (msGen 11).length
      + (msGen 12).length = 862 := by
  rw [msGen_card_0, msGen_card_1, msGen_card_2, msGen_card_3, msGen_card_4, msGen_card_5,
    msGen_card_6, msGen_card_7, msGen_card_8, msGen_card_9, msGen_card_10, msGen_card_11,
    msGen_card_12]

/-! Two anchors, one at each end of the range: the only 3-slot word attaches every root letter
at every slot, and the only 12-slot word is the all-singletons one (masks `1,1,1,2,2,2,4,4,4,
8,8,8`, packed little-endian). -/

set_option maxRecDepth 100000 in
theorem msGen_three : msGen 3 = [0xfff] := by decide +kernel

set_option maxRecDepth 100000 in
theorem msGen_twelve : msGen 12 = [0x888444222111] := by decide +kernel

/-! ## 8.  Landing note for whoever merges this

The file was developed against `Model.lean` alone, deliberately: it must not inherit the
obligation-14/15 hypothesis-form gap, and it must not pull in Mathlib.  Two consequences the
merge should tidy, neither of which is a name clash as the file stands:

* `one_le_kwt` is `ModelArith.kwt_pos_of_msk_pos` (`ModelArith.lean:159`) under another name.
  If this file is ever allowed to import `ModelArith`, delete `one_le_kwt` and use that.
* `sumUpto_kwt_split` re-proves by direct induction the splitting that `ModelArith.box_sum_kwt`
  (`ModelArith.lean:188`) does with `ModelArith.sumUpto_add`.  Same remark.

Nothing here redefines a model quantity (plan §6(e)): `msk`, `hasL`, `bitv`, `kwt`, `sumUpto`,
`allUpto`, `Box`, `box_iff` are all `Model.lean`'s, and `maskBox` is a conjunction of `Box`'s
own clauses rather than a restatement of any of them.
-/

end Delta4Model

