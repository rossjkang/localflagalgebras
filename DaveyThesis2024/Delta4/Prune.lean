import DaveyThesis2024.Delta4.Search
import DaveyThesis2024.Delta4.ModelArith

/-!
# Δ = 4 finite model: obligation 16 — the T-bound prune, and its soundness

Plan §6(c): *"the prune is mandatory, not an optimisation … no plan B"*.  `Search.lean`
supplies the prune-**free** traversal (`goNP`, `searchNP`) and its completeness spike
(`searchNP_complete`, `searchNP_leafOK_complete`).  This file adds the prune that the
executed search actually uses, and proves that switching it on loses nothing.

Nothing in `Model.lean`, `Search.lean` or `ModelArith.lean` is redefined: every model
quantity (`twoT`, `e22`, `slack`, `kwt`, `msk`, `n3`, `n4`, `slackSum`, `leafOK`, `Box`) is
the one already there, and the traversal reuses `pairList`, `takeGuard`, `addEdge`, `Inv`
and `WF` verbatim (plan §6(e): never define a second copy of a model quantity).

## What the prune is

`ModelArith.model_T_identity` (obligation 14, already proved *from* `Box` — no hypothesis
form needed here) says

```
  2T + 4n₃ + 12n₄ + ∑ᵢ (2kᵢ − 1)uᵢ  =  36 + 2e₂₂.
```

Writing `base2 := 36 − 4n₃ − 12n₄` this is the reference script's
`T2 = base2 + 2*e22 - d2`, kept additive so that no `ℕ` subtraction is ever needed.
At a node of the traversal the two sides are bounded by quantities the node can see:

* `e₂₂` can only grow by the still-undecided `(2,2)` pairs — `rem22` (the reference's
  `rem22`, *including* its `ms[i]&ms[j]==0` filter);
* `∑ᵢ (2kᵢ−1)uᵢ` is at least its restriction to the slots whose degree is already final —
  `fixedSlack` (the reference's `d2fix`).

so every leaf `A` below the node has

```
  2T(A) + 4n₃ + 12n₄ + fixedSlack ≤ 36 + 2(e₂₂(Aᶜᵘʳ) + rem22).
```

`leafOK` passes outright when `2T < 38`, so the branch may be cut as soon as

```
  36 + 2(e₂₂(Aᶜᵘʳ) + rem22)  <  38 + 4n₃ + 12n₄ + fixedSlack,
```

which is `pruneOK` below, and is the reference's `if base2+2*(e22+rem22)-d2fix<38: return`
transposed out of `ℕ`-subtraction.

## Statements closed here

* `e22_le_of_inv`   — plan obligation 16's first monotonicity fact (`e22 ≤ e22UpTo + r22`),
                      stated against the *spike's own* prefix invariant `Inv`, as §6(c) asks.
* `fixedSlack_le_slackSum` — the second (`slackSum ≥ defc`).
* `prune_sound`     — the two of them plus obligation 14.
* `searchP_complete` — the headline: the pruned search dominates every `Box` point.
* `searchPW_complete` — the same for the variant that also carries the reference's
                      root-level `min(·, |w₂|)` cap (`e22_le_w2count`).

No `native_decide`, no new axiom, no `sorry`.

## Measured against the reference enumeration

An independent Python port of these definitions (on top of an independent port of
`Model.lean`/`Search.lean`) was run against the reference enumerator:

* the per-multiset root filter reproduces the reference **exactly**: 862 mask multisets,
  **151** survive the prune at the root, and running all 862 instead of the 151 costs
  **711** extra nodes — both numbers are the plan's own (§6 "the 862 → 151 pre-filter");
* a re-implementation of the reference's *vertex-ordered* traversal and prune reproduces
  the plan's D8 figure **2,823,721** nodes exactly;
* this file's prune, on `Search.pairList`'s own order, costs **2,685,792** nodes over all
  862 multisets (2,685,081 over the 151) — **8.1 % under** the plan's D8 pair-ordered
  budget of 2,923,555, i.e. the prune is at least as strong as whatever that figure was
  measured with;
* the two monotonicity lemmas, the T-identity and the prune implication were checked on
  every `Box` point of every shell with `n ≤ 6` (11,920 points, 156,147 prune firings) and
  on 258,600 random `Box` completions across all shell sizes `3 ≤ n ≤ 12`
  (5,046,495 prune firings): no failures.

**Not yet done — the executable form.**  `pruneOK` recomputes `e22`, `rem22`, `touched` and
`slack` from scratch at every node, which is fine for the *statement* but too slow for
`decide +kernel` at 2.7 M nodes.  The cure is the refinement pattern `Search.goNPD_eq_goNP`
already uses for the degree cache: carry `e22` and `deg` as accumulators and tabulate the
suffix-constants `rem22`/`touched` once per `(n, K)`.  `e22_addEdge` below is exactly the
update lemma such a cached traversal needs, and `Search.dg`/`bumpDeg`/`deg_addEdge_*` are
the others.  That is a refinement of this file, not a change to it.
-/

namespace Delta4Model

/-! ## 1.  The two node-local bounds

Both are folds over the list of **still-undecided** pairs, exactly as `Inv` is.  Neither
mentions the past of the search. -/

/-- `rem22 K ps`: how many still-undecided pairs could become a `(2,2)` shell edge.
    An edge needs disjoint root masks (`Box`, clause (B3)), so the mask test is part of the
    count — this is the reference enumeration's `rem22` verbatim. -/
def rem22 (K : Nat) : List (Nat × Nat) → Nat
  | []      => 0
  | p :: ps =>
      (if kwt K p.1 = 2 ∧ kwt K p.2 = 2 ∧ (msk K p.1 &&& msk K p.2) = 0 then 1 else 0)
        + rem22 K ps

@[simp] theorem rem22_nil (K : Nat) : rem22 K [] = 0 := rfl

theorem rem22_cons (K i j : Nat) (ps : List (Nat × Nat)) :
    rem22 K ((i, j) :: ps)
      = (if kwt K i = 2 ∧ kwt K j = 2 ∧ (msk K i &&& msk K j) = 0 then 1 else 0)
        + rem22 K ps := rfl

/-- `touched ps x`: slot `x` still has an undecided incident pair, so its degree — and hence
    its slack — can still change.  Its negation is the reference's "vertex `< v`". -/
def touched (ps : List (Nat × Nat)) (x : Nat) : Bool :=
  ps.any (fun p => p.1 == x || p.2 == x)

/-- `fixedSlack`: `∑ᵢ (2kᵢ − 1)uᵢ` restricted to the slots whose degree is already final.
    The reference enumeration's `d2fix`. -/
def fixedSlack (n K A : Nat) (ps : List (Nat × Nat)) : Nat :=
  sumUpto (fun x => if touched ps x then 0 else (2 * kwt K x - 1) * slack n K A x) n 0

/-- `#{i < n : kᵢ = 2}`.  Caps `e₂₂`, because a weight-2 slot has at most `4 − 2 = 2`
    shell neighbours; the reference uses this cap in its root-level pre-filter. -/
def w2count (n K : Nat) : Nat := sumUpto (fun i => if kwt K i = 2 then 1 else 0) n 0

/-! ## 2.  Membership plumbing for `inPs`

`inPs` and `Inv` are `Search.lean`'s; these are the three facts about the head of the pair
list that the spike proved inline and that this file needs again. -/

theorem inPs_cons {i j : Nat} {ps : List (Nat × Nat)} (x y : Nat) :
    inPs ((i, j) :: ps) x y ↔ ((x = i ∧ y = j) ∨ (x = j ∧ y = i) ∨ inPs ps x y) := by
  simp only [inPs, List.mem_cons, Prod.mk.injEq]
  constructor
  · rintro (⟨⟨rfl, rfl⟩ | hx⟩ | ⟨⟨rfl, rfl⟩ | hx⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr hx))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | (hx | hx))
    · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inr hx)

/-- The head pair of a well-formed list occurs in neither orientation in the tail. -/
theorem head_fresh {n i j : Nat} {ps : List (Nat × Nat)} (hwf : WF n ((i, j) :: ps)) :
    ∀ x y : Nat, inPs ps x y → ¬ ((x = i ∧ y = j) ∨ (x = j ∧ y = i)) := by
  obtain ⟨hji, -, hnotin, hwf'⟩ := hwf
  rintro x y hx (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · rcases hx with hx | hx
    · exact hnotin hx
    · exact absurd (WF.mem_bounds hwf' _ hx).1 (by omega)
  · rcases hx with hx | hx
    · exact absurd (WF.mem_bounds hwf' _ hx).1 (by omega)
    · exact hnotin hx

/-- Both entries of a pair of a well-formed list are shell slots. -/
theorem inPs_bounds {n : Nat} {ps : List (Nat × Nat)} (hwf : WF n ps) {x y : Nat}
    (h : inPs ps x y) : x < n ∧ y < n := by
  rcases h with hm | hm
  · have := WF.mem_bounds hwf _ hm; exact ⟨this.2, by omega⟩
  · have := WF.mem_bounds hwf _ hm; exact ⟨by omega, this.2⟩

/-! ## 3.  Stepping the invariant

The two branch steps of `goNP_complete`, extracted so that this file's three inductions
share them instead of repeating them. -/

/-- TAKE: the target carries the head edge, so committing it keeps the invariant. -/
theorem inv_take {n A Acur i j : Nat} {ps : List (Nat × Nat)} (hn : n ≤ 12)
    (hwf : WF n ((i, j) :: ps)) (hinv : Inv n A Acur ((i, j) :: ps))
    (hij : edg A i j = 1) (hji : edg A j i = 1) : Inv n A (addEdge Acur i j) ps := by
  obtain ⟨hji', hin, hnotin, hwf'⟩ := hwf
  have hjn : j < n := Nat.lt_trans hji' hin
  have hfresh := head_fresh (n := n) ⟨hji', hin, hnotin, hwf'⟩
  refine ⟨?_, ?_⟩
  · intro x hx y hy hni
    rw [edg_addEdge _ _ _ _ _ (by omega) (by omega) (by omega)]
    by_cases hc : (x = i ∧ y = j) ∨ (x = j ∧ y = i)
    · rw [if_pos hc]
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hij.symm
      · exact hji.symm
    · rw [if_neg hc]
      exact hinv.agree x hx y hy (fun hh => by
        rcases (inPs_cons (i := i) (j := j) (ps := ps) x y).1 hh with h1 | h1 | h1
        · exact hc (Or.inl h1)
        · exact hc (Or.inr h1)
        · exact hni h1)
  · intro x y hxy
    have hb := inPs_bounds hwf' hxy
    rw [edg_addEdge _ _ _ _ _ (by omega) (by omega) (by omega), if_neg (hfresh x y hxy)]
    exact hinv.clr x y ((inPs_cons (i := i) (j := j) (ps := ps) x y).2 (Or.inr (Or.inr hxy)))

/-- SKIP: the target does not carry the head edge, so the invariant survives untouched. -/
theorem inv_skip {n A Acur i j : Nat} {ps : List (Nat × Nat)}
    (hwf : WF n ((i, j) :: ps)) (hinv : Inv n A Acur ((i, j) :: ps))
    (hij : edg A i j = 0) (hji : edg A j i = 0) : Inv n A Acur ps := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy hni
    by_cases hc : (x = i ∧ y = j) ∨ (x = j ∧ y = i)
    · have h0 : edg Acur x y = 0 :=
        hinv.clr x y ((inPs_cons (i := i) (j := j) (ps := ps) x y).2
          (Or.elim hc Or.inl (fun hh => Or.inr (Or.inl hh))))
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [h0, hij]
      · rw [h0, hji]
    · exact hinv.agree x hx y hy (fun hh => by
        rcases (inPs_cons (i := i) (j := j) (ps := ps) x y).1 hh with h1 | h1 | h1
        · exact hc (Or.inl h1)
        · exact hc (Or.inr h1)
        · exact hni h1)
  · intro x y hxy
    exact hinv.clr x y ((inPs_cons (i := i) (j := j) (ps := ps) x y).2 (Or.inr (Or.inr hxy)))

/-! ## 4.  `e₂₂` under the traversal

Two facts: `e₂₂` reads `A` only on `[0,n)²` (so the base case of the induction below is a
congruence), and committing one canonical pair moves it by exactly the pair's own `(2,2)`
indicator. -/

theorem e22_congr {n K X Y : Nat} (h : EdgAgree n X Y) : e22 n K X = e22 n K Y :=
  sumUpto_congr fun i hi =>
    sumUpto_congr fun j hj => by rw [h i hi j (Nat.lt_trans hj hi)]

/-- Committing the canonical pair `j < i < n` bumps `e₂₂` by `[kᵢ = kⱼ = 2]` and nothing
    else.  `edg Acur i j = 0` is the `Inv.clr` half of the prefix invariant. -/
theorem e22_addEdge {n K Acur i j : Nat} (hn : n ≤ 12) (hji : j < i) (hin : i < n)
    (h0 : edg Acur i j = 0) :
    e22 n K (addEdge Acur i j)
      = e22 n K Acur + (if kwt K i = 2 ∧ kwt K j = 2 then 1 else 0) := by
  have hoff : ∀ a, a < n → ∀ b, b < a → ¬ (a = i ∧ b = j) →
      edg (addEdge Acur i j) a b = edg Acur a b := by
    intro a ha b hb hc
    rw [edg_addEdge _ _ _ _ _ (by omega) (by omega) (by omega), if_neg]
    rintro (hh | ⟨rfl, rfl⟩)
    · exact hc hh
    · omega
  have hat : edg (addEdge Acur i j) i j = 1 := by
    rw [edg_addEdge _ _ _ _ _ (by omega) (by omega) (by omega), if_pos (Or.inl ⟨rfl, rfl⟩)]
  have hoffs : ∀ a, a < n → ∀ b, b < a → ¬ (a = i ∧ b = j) →
      (if kwt K a = 2 ∧ kwt K b = 2 then edg (addEdge Acur i j) a b else 0)
        = (if kwt K a = 2 ∧ kwt K b = 2 then edg Acur a b else 0) := by
    intro a ha b hb hc; rw [hoff a ha b hb hc]
  by_cases hk : kwt K i = 2 ∧ kwt K j = 2
  · rw [if_pos hk]
    refine sumUpto_bump _ _ n i hin (fun a ha hai => ?_) ?_
    · exact sumUpto_congr fun b hb => hoffs a ha b hb (fun hh => hai hh.1)
    · refine sumUpto_bump _ _ i j hji (fun b hb hbj => ?_) ?_
      · exact hoffs i hin b hb (fun hh => hbj hh.2)
      · rw [hat, if_pos hk, if_pos hk, h0]
  · rw [if_neg hk, Nat.add_zero]
    refine sumUpto_congr fun a ha => sumUpto_congr fun b hb => ?_
    by_cases hc : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := hc
      rw [if_neg hk, if_neg hk]
    · exact hoffs a ha b hb hc

/-- **Obligation 16, monotonicity fact one.**  Every `(2,2)` edge of the target that the
    partial graph is still missing sits on a pair that is still undecided, so `rem22`
    already pays for it. -/
theorem e22_le_of_inv {n K A : Nat} (hbox : Box n K A = true) :
    ∀ ps : List (Nat × Nat), WF n ps → ∀ Acur : Nat, Inv n A Acur ps →
      e22 n K A ≤ e22 n K Acur + rem22 K ps := by
  have hn12 : n ≤ 12 := (box_size hbox).2
  intro ps
  induction ps with
  | nil =>
      intro _ Acur hinv
      have hc : e22 n K Acur = e22 n K A :=
        e22_congr (fun p hp q hq => hinv.agree p hp q hq (by simp [inPs]))
      rw [rem22_nil, hc]
      omega
  | cons p ps ih =>
      obtain ⟨i, j⟩ := p
      intro hwf Acur hinv
      obtain ⟨hji0, hin0, hnotin, hwf'⟩ := hwf
      -- `WF` unfolds with `(i,j).1`/`(i,j).2`; restate so unification picks `i`, `j`
      have hji : j < i := hji0
      have hin : i < n := hin0
      have hjn : j < n := Nat.lt_trans hji hin
      have hwf : WF n ((i, j) :: ps) := ⟨hji0, hin0, hnotin, hwf'⟩
      by_cases hij : edg A i j = 1
      · have hji' : edg A j i = 1 := by rw [← box_edg_symm hbox hin hjn]; exact hij
        have hmsk : msk K i &&& msk K j = 0 := by
          rcases ((box_iff n K A).1 hbox).edgeDisj i hin j hjn with h0 | ⟨hm, -⟩
          · omega
          · exact hm
        have h0 : edg Acur i j = 0 := hinv.clr i j (Or.inl List.mem_cons_self)
        have hstep := ih hwf' (addEdge Acur i j) (inv_take hn12 hwf hinv hij hji')
        rw [e22_addEdge hn12 hji hin h0] at hstep
        rw [rem22_cons]
        have hif : (if kwt K i = 2 ∧ kwt K j = 2 ∧ (msk K i &&& msk K j) = 0 then 1 else 0)
            = (if kwt K i = 2 ∧ kwt K j = 2 then 1 else 0) := by
          by_cases hk : kwt K i = 2 ∧ kwt K j = 2
          · rw [if_pos ⟨hk.1, hk.2, hmsk⟩, if_pos hk]
          · rw [if_neg (fun hh => hk ⟨hh.1, hh.2.1⟩), if_neg hk]
        rw [hif]
        omega
      · have hij0 : edg A i j = 0 := by have := edg_le_one A i j; omega
        have hji00 : edg A j i = 0 := by rw [← box_edg_symm hbox hin hjn]; exact hij0
        have hstep := ih hwf' Acur (inv_skip hwf hinv hij0 hji00)
        rw [rem22_cons]
        omega

/-! ## 5.  The slack bound

`fixedSlack` only ever charges a slot whose incident pairs are **all** decided, and such a
slot has the same degree — hence the same slack — in the partial graph and in the target.
Every other slot is charged `0`, which is a lower bound because `slack ≥ 0`. -/

theorem touched_of_inPs {ps : List (Nat × Nat)} {x q : Nat} (h : inPs ps x q) :
    touched ps x = true := by
  unfold touched
  rw [List.any_eq_true]
  rcases h with hm | hm
  · exact ⟨(x, q), hm, by simp⟩
  · exact ⟨(q, x), hm, by simp⟩

theorem deg_eq_of_not_touched {n A Acur : Nat} {ps : List (Nat × Nat)}
    (hinv : Inv n A Acur ps) {x : Nat} (hx : x < n) (ht : touched ps x = false) :
    deg n Acur x = deg n A x :=
  sumUpto_congr fun q hq =>
    hinv.agree x hx q hq (fun hc => by rw [touched_of_inPs hc] at ht; exact Bool.noConfusion ht)

/-- **Obligation 16, monotonicity fact two.**  The target's slack sum dominates the partial
    graph's committed prefix (`slackSum ≥ defc`). -/
theorem fixedSlack_le_slackSum {n K A Acur : Nat} {ps : List (Nat × Nat)}
    (hinv : Inv n A Acur ps) : fixedSlack n K Acur ps ≤ slackSum n K A := by
  have hL : fixedSlack n K Acur ps
      = sumUpto (fun x => if touched ps x then 0 else (2 * kwt K x - 1) * slack n K Acur x)
          n 0 := rfl
  rw [hL, slackSum_def]
  refine sumUpto_le _ _ n fun x hx => ?_
  by_cases ht : touched ps x = true
  · rw [if_pos ht]; exact Nat.zero_le _
  · have htf : touched ps x = false := by
      cases h : touched ps x
      · rfl
      · exact absurd h ht
    rw [if_neg ht]
    have hs : slack n K Acur x = slack n K A x := by
      unfold slack; rw [deg_eq_of_not_touched hinv hx htf]
    rw [hs]

/-! ## 6.  The weight-2 cap on `e₂₂`

A weight-2 slot has at most `4 − 2 = 2` shell neighbours (`ModelArith.e22_row_le_of`), so
`2e₂₂ ≤ 2·#{i : kᵢ = 2}`.  The reference enumeration uses this as `min(len(p22), len(w2))`
in its per-multiset pre-filter; §8 folds it into `pruneOKW`. -/

theorem e22_le_w2count {n K A : Nat} (hb : Box n K A = true) : e22 n K A ≤ w2count n K := by
  have hsq := two_mul_e22_of (K := K) (A := A) (fun _ hi _ hj => box_edg_symm hb hi hj)
    (fun _ hi => box_edg_irrefl hb hi)
  have hrow : sumUpto (fun i =>
        sumUpto (fun j => if kwt K i = 2 ∧ kwt K j = 2 then edg A i j else 0) n 0) n 0
      ≤ sumUpto (fun i => if kwt K i = 2 then 2 else 0) n 0 :=
    sumUpto_le _ _ n fun i hi => e22_row_le_of (fun _ h => box_deg_cap hb h) hi
  have hmul : sumUpto (fun i => if kwt K i = 2 then 2 else 0) n 0 = 2 * w2count n K := by
    have h1 : sumUpto (fun i => if kwt K i = 2 then 2 else 0) n 0
        = sumUpto (fun i => 2 * (if kwt K i = 2 then 1 else 0)) n 0 :=
      sumUpto_congr fun i _ => by split <;> rfl
    rw [h1, sumUpto_mul_left]
    rfl
  have h2 : 2 * e22 n K A ≤ 2 * w2count n K := by rw [hsq, ← hmul]; exact hrow
  omega

/-! ## 7.  Prune soundness

The prune cuts a branch only when the T-identity already forces `2T < 38` at *every* leaf
below it, and `leafOK` passes outright there.  This is the whole mathematical content of
obligation 16. -/

/-- `leafOK`'s first disjunct. -/
theorem leafOK_of_twoT_lt {n K A : Nat} (h : twoT n K A < 38) : leafOK n K A = true := by
  unfold leafOK
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl h

/-- The prune's engine, with the `e₂₂` upper bound left as a parameter `E` so that the
    plain and the `w₂`-capped prune share one proof.  `hid` is obligation 14
    (`ModelArith.model_T_identity`), used *as proved from* `Box` — not assumed. -/
theorem twoT_lt_of_bound {n K A Acur : Nat} {ps : List (Nat × Nat)} (hbox : Box n K A = true)
    (hinv : Inv n A Acur ps) {E : Nat} (hE : e22 n K A ≤ E)
    (hlt : 36 + 2 * E < 38 + 4 * n3 n K + 12 * n4 n K + fixedSlack n K Acur ps) :
    twoT n K A < 38 := by
  have hid := model_T_identity hbox
  have h2 := fixedSlack_le_slackSum (K := K) hinv
  omega

/-- The T-bound prune, transposed out of `ℕ`-subtraction: with
    `base2 = 36 − 4n₃ − 12n₄` this is the reference's
    `if base2 + 2*(e22 + rem22) - d2fix < 38: return`. -/
def pruneOK (n K A : Nat) (ps : List (Nat × Nat)) : Bool :=
  decide (36 + 2 * (e22 n K A + rem22 K ps)
    < 38 + 4 * n3 n K + 12 * n4 n K + fixedSlack n K A ps)

/-- The same prune with the reference's `min(·, |w₂|)` cap folded in at every node
    (the reference applies it only once, as a per-multiset pre-filter).

    **Measured redundant.**  Over all 862 mask multisets — 2,685,792 traversal nodes — there
    is **no** node at which `pruneOKW` fires and `pruneOK` does not: `rem22` already carries
    the mask-disjointness filter, which subsumes the cap.  Kept because it is the reference's
    own form and costs one extra `min`; `searchP`/`searchP_complete` is the primary pair. -/
def pruneOKW (n K A : Nat) (ps : List (Nat × Nat)) : Bool :=
  decide (36 + 2 * min (e22 n K A + rem22 K ps) (w2count n K)
    < 38 + 4 * n3 n K + 12 * n4 n K + fixedSlack n K A ps)

/-- **Obligation 16.**  If the prune fires at a node of the traversal, then every `Box`
    point the node still covers already passes `leafOK`. -/
theorem prune_sound {n K A Acur : Nat} {ps : List (Nat × Nat)} (hbox : Box n K A = true)
    (hwf : WF n ps) (hinv : Inv n A Acur ps) (hpr : pruneOK n K Acur ps = true) :
    leafOK n K A = true := by
  rw [pruneOK, decide_eq_true_eq] at hpr
  exact leafOK_of_twoT_lt
    (twoT_lt_of_bound hbox hinv (e22_le_of_inv hbox ps hwf Acur hinv) hpr)

/-- Obligation 16 for the `w₂`-capped prune. -/
theorem prune_sound_w {n K A Acur : Nat} {ps : List (Nat × Nat)} (hbox : Box n K A = true)
    (hwf : WF n ps) (hinv : Inv n A Acur ps) (hpr : pruneOKW n K Acur ps = true) :
    leafOK n K A = true := by
  rw [pruneOKW, decide_eq_true_eq] at hpr
  exact leafOK_of_twoT_lt
    (twoT_lt_of_bound hbox hinv
      (le_min (e22_le_of_inv hbox ps hwf Acur hinv) (e22_le_w2count hbox)) hpr)

/-! ## 8.  The pruned traversal

`goPrune` is `Search.goNP` with `leafP := leafOK` and one extra test at every internal node.
The prune is a *parameter* with a soundness side condition, so the plain and the capped
searches are two instantiations of one induction rather than two copies of it. -/

def goPrune (pr : Nat → Nat → Nat → List (Nat × Nat) → Bool) (n K : Nat) :
    List (Nat × Nat) → Nat → Bool
  | [],      A => leafOK n K A
  | p :: ps, A =>
      if pr n K A (p :: ps) then true
      else
        goPrune pr n K ps A
          && (if takeGuard n K A p.1 p.2 then goPrune pr n K ps (addEdge A p.1 p.2) else true)

theorem goPrune_complete (pr : Nat → Nat → Nat → List (Nat × Nat) → Bool) {n K A : Nat}
    (hbox : Box n K A = true)
    (hsound : ∀ (ps : List (Nat × Nat)) (Acur : Nat), WF n ps → Inv n A Acur ps →
      pr n K Acur ps = true → leafOK n K A = true) :
    ∀ ps : List (Nat × Nat), WF n ps → ∀ Acur : Nat, Inv n A Acur ps →
      goPrune pr n K ps Acur = true → leafOK n K A = true := by
  have hn12 : n ≤ 12 := (box_size hbox).2
  intro ps
  induction ps with
  | nil =>
      intro _ Acur hinv h
      rw [goPrune] at h
      rw [← leafOK_congr (n := n) (K := K) (X := Acur) (Y := A)
        (fun p hp q hq => hinv.agree p hp q hq (by simp [inPs]))]
      exact h
  | cons p ps ih =>
      obtain ⟨i, j⟩ := p
      intro hwf Acur hinv h
      by_cases hp : pr n K Acur ((i, j) :: ps) = true
      · exact hsound ((i, j) :: ps) Acur hwf hinv hp
      · rw [goPrune, if_neg hp, Bool.and_eq_true] at h
        obtain ⟨hskip, htake⟩ := h
        obtain ⟨hji0, hin0, hnotin, hwf'⟩ := hwf
        have hji : j < i := hji0
        have hin : i < n := hin0
        have hjn : j < n := Nat.lt_trans hji hin
        have hwfc : WF n ((i, j) :: ps) := ⟨hji0, hin0, hnotin, hwf'⟩
        by_cases hij : edg A i j = 1
        · have hji' : edg A j i = 1 := by rw [← box_edg_symm hbox hin hjn]; exact hij
          have hg : takeGuard n K Acur i j = true :=
            takeGuard_of_box hbox hinv hin hjn List.mem_cons_self hij
          rw [if_pos hg] at htake
          exact ih hwf' _ (inv_take hn12 hwfc hinv hij hji') htake
        · have hij0 : edg A i j = 0 := by have := edg_le_one A i j; omega
          have hji0' : edg A j i = 0 := by rw [← box_edg_symm hbox hin hjn]; exact hij0
          exact ih hwf' Acur (inv_skip hwfc hinv hij0 hji0') hskip

/-! ### The two searches -/

/-- The executed traversal: `goNP` plus the T-bound prune. -/
def goP (n K : Nat) : List (Nat × Nat) → Nat → Bool := goPrune pruneOK n K

def searchP (n K : Nat) : Bool := goP n K (pairList n) 0

theorem goP_nil (n K A : Nat) : goP n K [] A = leafOK n K A := rfl

theorem goP_cons (n K : Nat) (p : Nat × Nat) (ps : List (Nat × Nat)) (A : Nat) :
    goP n K (p :: ps) A =
      if pruneOK n K A (p :: ps) then true
      else goP n K ps A
        && (if takeGuard n K A p.1 p.2 then goP n K ps (addEdge A p.1 p.2) else true) := rfl

/-- **THE PRUNED SPIKE.**  Pruning loses nothing: `searchP` certifies exactly what the
    prune-free `searchNP leafOK` certifies (`Search.searchNP_leafOK_complete`). -/
theorem searchP_complete (n K A : Nat) (hbox : Box n K A = true) (h : searchP n K = true) :
    leafOK n K A = true :=
  goPrune_complete pruneOK hbox (fun _ _ hwf hinv hp => prune_sound hbox hwf hinv hp)
    (pairList n) (wf_pairList n n (Nat.le_refl n)) 0 (inv_zero hbox) h

/-- The same for the `w₂`-capped prune. -/
def goPW (n K : Nat) : List (Nat × Nat) → Nat → Bool := goPrune pruneOKW n K

def searchPW (n K : Nat) : Bool := goPW n K (pairList n) 0

theorem searchPW_complete (n K A : Nat) (hbox : Box n K A = true) (h : searchPW n K = true) :
    leafOK n K A = true :=
  goPrune_complete pruneOKW hbox (fun _ _ hwf hinv hp => prune_sound_w hbox hwf hinv hp)
    (pairList n) (wf_pairList n n (Nat.le_refl n)) 0 (inv_zero hbox) h

/-! ## 9.  Non-vacuity regressions (plan §6(e.6))

The failure mode plan §6(e) names is a *vacuous* check: a prune that fires everywhere makes
`searchP n K = true` for free and `searchP_complete` says nothing.  The witnesses below are
the `ModelArith` ones, and they pin the prune from both sides.

`decide` here is kernel evaluation of `Nat` arithmetic on literals — no `native_decide`. -/

/-- `K₄,₄`: the prune fires at the root, so the whole multiset is discharged at one node.
    This is the reference enumeration's per-multiset pre-filter
    (`if base2+2*min(len(p22),len(w2))<38: continue`), reproduced exactly. -/
theorem pruneOK_K44_root : pruneOK 3 4095 0 (pairList 3) = true := by decide

theorem searchP_K44 : searchP 3 4095 = true := by decide

/-- …and the prune-free search agrees, at the one multiset where both are cheap. -/
theorem searchNP_K44 : searchNP leafOK 3 4095 = true := by decide

/-- `C₁₂(2,3)`, the sharp Δ = 4 extremal shell (`2T = 40 ≥ 38`): the prune does **not**
    fire, at the root or at the leaf.  So `searchP` really does descend, and
    `searchP_complete` is not discharged by a prune that fires everywhere. -/
theorem pruneOK_C12_root : pruneOK 7 212362545 0 (pairList 7) = false := by decide

theorem pruneOK_C12_leaf :
    pruneOK 7 212362545 14172867997950680563816 [] = false := by decide

theorem pruneOKW_C12_root : pruneOKW 7 212362545 0 (pairList 7) = false := by decide

/-- The node-local quantities at that root, spelled out. -/
theorem prune_values_C12 :
    rem22 212362545 (pairList 7) = 2 ∧ w2count 7 212362545 = 5
      ∧ fixedSlack 7 212362545 0 (pairList 7) = 0 := by decide

/-- At a leaf nothing is undecided, so `fixedSlack` is the full slack sum — the prune test
    degenerates to the exact T-identity, and to `leafOK`'s own `2T < 38` gate. -/
theorem fixedSlack_leaf (n K A : Nat) : fixedSlack n K A [] = slackSum n K A := by
  rw [slackSum_def]
  exact sumUpto_congr fun x _ => by simp [touched]

/-- The mixed witness (all four terms of the identity nonzero) is discharged at its root. -/
theorem pruneOK_mixed_root : pruneOK 6 13346385 0 (pairList 6) = true := by decide

/-- `e₂₂ ≤ |w₂|` is not vacuous either: `2 ≤ 5` on `C₁₂(2,3)`. -/
theorem e22_le_w2count_C12 :
    e22 7 212362545 14172867997950680563816 ≤ w2count 7 212362545 :=
  e22_le_w2count box_witness_C12

end Delta4Model
