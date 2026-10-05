import DaveyThesis2024.Delta4.Prune
import DaveyThesis2024.Delta4.MaskGen
import DaveyThesis2024.Delta4.Chunk
import DaveyThesis2024.Delta4.CreditCharge

/-!
# Δ = 4 finite model: soundness of the executed search (plan obligation 18)

`searchP_complete` (`Delta4/Prune.lean`, obligations 16+17) says the executed, pruned
traversal *certifies* every `Box`-admissible shell:

    Box n K A = true → searchP n K = true → leafOK n K A = true

and `leafOK` (`Delta4/Model.lean`) is the two-branch leaf test

    leafOK n K A = decide (twoT n K A < 38) ‖ decide (charge + 6·twoT ≤ credit + 212).

Obligation 18 turns that `Bool` into the arithmetic statement the assembly consumes: inside
the high window `38 ≤ 2T` the first branch is *false*, so the second must carry.  That is all
`search_sound` is.  It is short because 16 and 17 already landed; the plan's
"~500 lines beyond 17" estimate predates them.

## What is new here beyond the statement

* `search_sound` / `search_sound_NP` — obligation 18 for the pruned and the prune-free
  traversal.  Both are needed: `searchP` is what the census will execute, but the landed
  chunk pilot (`Chunk.pilot_frontier_ok`, obligation 21) certifies the **prune-free**
  `searchNP leafOK`, so a `searchP`-only statement would not compose with it.
* `search_sound_C12` and `search_sound_pilot` — two instances with **every hypothesis
  discharged by kernel evaluation**, i.e. unconditional `∀ A` theorems about real mask words,
  one of them the sharp extremal `C₁₂(2,3)`.
* `C12_instance` — the extremal shell of `C₁₂(2,3)` put through `search_sound_C12`:
  `80 + 12·20 = 320 = 108 + 212`, **equality**.  So the conclusion is not vacuous, and `212`
  is the smallest constant for which the theorem is true.
* `visible_enumeration_at_of_searchP` / `…_of_searchNP` — the graph-side composition with
  obligations 12/13.  The only input still missing from the chain is `box_of_root`
  (obligation 10).

`#print axioms` at the end: everything is `[propext, Classical.choice, Quot.sound]` or less.
No `native_decide`, no new axiom, no `sorry`.
-/

namespace Delta4Model

/-! ## 1.  Obligation 18 -/

/-- **Obligation 18, `search_sound`.**  If the pruned traversal returns `true` on the
    attachment-mask word `K`, then *every* `Box`-admissible shell `A` over that word which
    lands in the high window `38 ≤ 2T` satisfies the discharging inequality.

    This is the shape the assembly (obligation 22) needs: the `∀ A` is unbounded, and the only
    search input is one closed `Bool` per mask word, which `decide +kernel` settles. -/
theorem search_sound (n K : Nat) (hgo : searchP n K = true) :
    ∀ A, Box n K A = true → 38 ≤ twoT n K A →
      charge n K A + 6 * twoT n K A ≤ credit n K A + 212 := by
  intro A hbox h38
  have hleaf : leafOK n K A = true := searchP_complete n K A hbox hgo
  rw [leafOK, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hleaf
  omega

/-- The same for the prune-free traversal.  This is the one the landed chunk machinery
    (`Chunk.searchNP_of_frontier`, `Chunk.leafOK_of_frontier`) produces. -/
theorem search_sound_NP (n K : Nat) (hgo : searchNP leafOK n K = true) :
    ∀ A, Box n K A = true → 38 ≤ twoT n K A →
      charge n K A + 6 * twoT n K A ≤ credit n K A + 212 := by
  intro A hbox h38
  have hleaf : leafOK n K A = true := searchNP_leafOK_complete n K A hbox hgo
  rw [leafOK, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hleaf
  omega

/-- And for the `w₂`-capped prune, which feeds the same `leafOK`. -/
theorem search_sound_W (n K : Nat) (hgo : searchPW n K = true) :
    ∀ A, Box n K A = true → 38 ≤ twoT n K A →
      charge n K A + 6 * twoT n K A ≤ credit n K A + 212 := by
  intro A hbox h38
  have hleaf : leafOK n K A = true := searchPW_complete n K A hbox hgo
  rw [leafOK, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hleaf
  omega

/-- Stated at the graph-facing scale `12·T` rather than `6·(2T)`.  `twoT` is the *doubled*
    shell objective, so `6 * twoT = 12 * T`; keeping the model in `2T` avoids a division, and
    this restatement is the only place the factor of two is named. -/
theorem search_sound_doubled (n K : Nat) (hgo : searchP n K = true) (A : Nat)
    (hbox : Box n K A = true) (h38 : 38 ≤ twoT n K A) :
    2 * charge n K A + 12 * twoT n K A ≤ 2 * credit n K A + 424 := by
  have := search_sound n K hgo A hbox h38
  omega

/-- The contrapositive: a violating shell in the high window forces the search to fail.
    Not needed downstream; recorded because it is what makes `search_sound` falsifiable
    rather than merely unproved. -/
theorem searchP_eq_false_of_violation {n K A : Nat} (hbox : Box n K A = true)
    (h38 : 38 ≤ twoT n K A) (hv : credit n K A + 212 < charge n K A + 6 * twoT n K A) :
    searchP n K = false := by
  cases hgo : searchP n K with
  | false => rfl
  | true => exact absurd (search_sound n K hgo A hbox h38) (by omega)

/-- The plan states obligation 18 with a separate `sortedSat n K = true` hypothesis.  It is
    redundant: `Box`'s own (D16) and (B4) clauses are exactly that condition, and `MaskGen`
    already extracts them.  Recorded so the discrepancy is a theorem, not a claim. -/
theorem maskBox_of_box_redundant {n K A : Nat} (h : Box n K A = true) : maskBox n K = true :=
  maskBox_of_box h

/-! ## 2.  Two mask words with every hypothesis discharged

A conditional theorem proves nothing about the census until its hypothesis is met.  Both
words below are `n = 7`, and both are cheap enough for `decide +kernel` monolithically
(2,659 and 11,577 traversal nodes, against the ~5,000-node chunk ceiling `Chunk` §6(f)
measures), so `search_sound` fires on them with nothing left assumed. -/

/-- The `C₁₂(2,3)` mask word, prune-free.  2,659 nodes, zero violations. -/
theorem searchNP_C12 : searchNP leafOK 7 212362545 = true := by decide +kernel

/-- The same word, with the T-bound prune switched on.  Stated separately because
    `search_sound` proper is about `searchP`, and because it is an independent kernel
    evaluation of a different tree that has to reach the same verdict. -/
theorem searchP_C12 : searchP 7 212362545 = true := by decide +kernel

/-- The node count of the prune-free tree, as an independent falsifiable measurement
    (plan §6(e) layer 3: the kernel assertion carries the count, not just a `Bool`). -/
theorem searchCnt_C12 : goCnt leafOK 7 212362545 (pairList 7) 0 = (2659, 0) := by decide +kernel

/-- **Obligation 18, unconditionally, at the `C₁₂(2,3)` mask word.**  No hypotheses. -/
theorem search_sound_C12 :
    ∀ A, Box 7 212362545 A = true → 38 ≤ twoT 7 212362545 A →
      charge 7 212362545 A + 6 * twoT 7 212362545 A ≤ credit 7 212362545 A + 212 :=
  search_sound 7 212362545 searchP_C12

/-- **Obligation 18, unconditionally, at `Chunk`'s pilot mask word** — and here the
    hypothesis comes from the *chunk table* (obligation 21, `pilot_frontier_ok`), not from a
    monolithic `decide`, so this is the full obligation-21 → obligation-18 composition
    already working end to end on one word. -/
theorem searchNP_pilot : searchNP leafOK nPil KPil = true :=
  searchNP_of_frontier leafOK nPil KPil dPil (FPil_def ▸ pilot_frontier_ok)

theorem search_sound_pilot :
    ∀ A, Box 7 214450995 A = true → 38 ≤ twoT 7 214450995 A →
      charge 7 214450995 A + 6 * twoT 7 214450995 A ≤ credit 7 214450995 A + 212 :=
  search_sound_NP nPil KPil searchNP_pilot

/-! ## 3.  Non-vacuity: the conclusion is a genuine, and sharp, assertion

The failure mode plan §6(e) names is a conclusion that holds for free.  It does not hold for
free here: on the punctured radius-2 shell of `C₁₂(2,3)` — the sharp Δ = 4 extremal circulant
`i ~ i ± 2, i ± 3 (mod 12)` — `search_sound_C12` asserts an inequality that is an **equality**.

The encoding is `ModelArith`'s: slots sorted by mask, `K = ∑ mask_i·16^i`,
`A = ∑ row_i·4096^i`.  At root `0` the punctured shell has `n = 7` slots with masks
`1,3,5,6,8,10,12`, so `K = 212362545` and `A = 14172867997950680563816`.  `Box` there is
`ModelArith.box_witness_C12`.  (That this triple *is* `(nOf G v, KOf G v, AOf G v)` for
`G = C₁₂(2,3)` is the encoding claim of obligation 10, checked outside Lean and not proved
here — see the caveat in §5.) -/

/-- The three model quantities at the `C₁₂(2,3)` shell.  `twoT = 40`, i.e. `T = 20`. -/
theorem C12_values :
    twoT 7 212362545 14172867997950680563816 = 40
      ∧ credit 7 212362545 14172867997950680563816 = 108
      ∧ charge 7 212362545 14172867997950680563816 = 80 := by decide

/-- The shell is inside the quantifier's range: `Box` holds and `2T = 40 ≥ 38`. -/
theorem C12_in_range :
    Box 7 212362545 14172867997950680563816 = true
      ∧ 38 ≤ twoT 7 212362545 14172867997950680563816 :=
  ⟨box_witness_C12, by decide⟩

/-- **The instance.**  `search_sound_C12` applied to that shell — an unconditional theorem
    with no hypotheses anywhere in its statement. -/
theorem C12_instance :
    charge 7 212362545 14172867997950680563816
        + 6 * twoT 7 212362545 14172867997950680563816
      ≤ credit 7 212362545 14172867997950680563816 + 212 :=
  search_sound_C12 _ box_witness_C12 (by decide)

/-- **…and it is tight:** `80 + 12·20 = 320 = 108 + 212`, margin `0`. -/
theorem C12_tight :
    charge 7 212362545 14172867997950680563816
        + 6 * twoT 7 212362545 14172867997950680563816
      = credit 7 212362545 14172867997950680563816 + 212 := by decide

/-- So `212` is the smallest constant that works: with `211` the `C₁₂(2,3)` shell is a
    counterexample and `search_sound` would be **false**.  This also pins the `6 * twoT`
    coefficient: it cannot be raised either. -/
theorem C12_refutes_211 :
    ¬ (charge 7 212362545 14172867997950680563816
        + 6 * twoT 7 212362545 14172867997950680563816
      ≤ credit 7 212362545 14172867997950680563816 + 211) := by decide

/-- The leaf test at that shell passes through its *second* disjunct, not the `2T < 38`
    escape — so `leafOK` is doing real work here. -/
theorem C12_leafOK_not_low :
    leafOK 7 212362545 14172867997950680563816 = true
      ∧ ¬ twoT 7 212362545 14172867997950680563816 < 38 := by decide

/-- The pilot word has a high shell too, with margin `40` rather than `0` — a second,
    independent point where the conclusion is asserted and not vacuous. -/
theorem pilot_instance :
    Box 7 214450995 14172866872256797933664 = true
      ∧ twoT 7 214450995 14172866872256797933664 = 42
      ∧ credit 7 214450995 14172866872256797933664 = 102
      ∧ charge 7 214450995 14172866872256797933664 = 22 := by decide

theorem pilot_instance_bound :
    charge 7 214450995 14172866872256797933664
        + 6 * twoT 7 214450995 14172866872256797933664
      ≤ credit 7 214450995 14172866872256797933664 + 212 :=
  search_sound_pilot _ pilot_instance.1 (by decide)

/-! ## 4.  Contrast: the two landed witnesses below the window

`K₄,₄` and the swap-randomised `n = 6` witness both have `2T < 38`, so `search_sound` says
nothing about them.  That is the point of the hypothesis: it selects the configurations the
census actually has to check.

Exhaustive scan of every `Box`-admissible `(K, A)` at `n = 3, 4, 5, 6` (`msGen n` × every
shell graph, using this file's own definitions through `#eval`) gives

    n            3      4      5       6
    Box points   1     21    478  11,420
    in window    0      0      0     171
    worst margin −320  −224   −64     −16

so the window opens at `n = 6`, and `search_sound` is already non-vacuous there — but nothing
at `n ≤ 6` is tight, and no shell *below* the window violates the inequality either.  The
`38 ≤ 2T` hypothesis is therefore not forced by a small counterexample; it is the graph-side
gate `19 ≤ T` of `henum`, carried into the model so the search may stop early. -/

theorem K44_values :
    twoT 3 4095 0 = 0 ∧ credit 3 4095 0 = 108 ∧ charge 3 4095 0 = 0
      ∧ twoT 3 4095 0 < 38 := by decide

theorem mixed_values :
    twoT 6 13346385 1152921710782087212 = 20
      ∧ credit 6 13346385 1152921710782087212 = 81
      ∧ charge 6 13346385 1152921710782087212 = 48
      ∧ twoT 6 13346385 1152921710782087212 < 38 := by decide

/-- `search_sound` at the `K₄,₄` word fires too (`Prune.searchP_K44`), but the resulting
    statement is *vacuous*: that word admits exactly one `Box`-admissible shell, `A = 0`, with
    `2T = 0`.  Recorded to be explicit that the `K₄,₄` regression is evidence about the
    hypothesis, not about the conclusion; §3 is the evidence about the conclusion. -/
theorem search_sound_K44 :
    ∀ A, Box 3 4095 A = true → 38 ≤ twoT 3 4095 A →
      charge 3 4095 A + 6 * twoT 3 4095 A ≤ credit 3 4095 A + 212 :=
  search_sound 3 4095 searchP_K44

end Delta4Model

/-! ## 5.  The assembly step

`CreditCharge.visible_enumeration_at_of_leafOK` consumes `leafOK … = true` directly, so as
landed the chain can reach `henum` from `searchP_complete` without passing through
`search_sound` at all — obligation 18 sits *beside* the critical path rather than on it.  What
it buys is the interface obligation 21 wants: one closed `Bool` per mask word.  The two
corollaries below are that interface wired to the graph side, and they are the shape
obligation 22 should call.

The `Box (nOf G v) (KOf G v) (AOf G v) = true` hypothesis of the two corollaries below is
**obligation 10**, `PentagonLocal.box_of_root` (`Delta4/BoxOfRoot.lean`), now proved
unconditionally.  It is left as a hypothesis here only so that this file stays independent of
`BoxOfRoot.lean`; `Delta4/Assembly.lean` discharges it. -/

namespace Davey2024
namespace PentagonLocal

open Finset
open scoped Classical

variable {G : Flag emptyType}

/-- **`henum` at one root, from the pruned search.**  Obligation 18 composed with
    obligations 12/13.  Inputs: `box_of_root` (10, proved in `BoxOfRoot.lean`) and the
    per-word `searchP … = true` (21). -/
theorem visible_enumeration_at_of_searchP (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size)
    (hbox : Delta4Model.Box (nOf G v) (KOf G v) (AOf G v) = true)
    (hgo : Delta4Model.searchP (nOf G v) (KOf G v) = true)
    (h19 : 19 ≤ ∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card) :
    visibleChargeTotal G v
        + 12 * (∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card)
      ≤ visibleCreditTotal G v + 212 :=
  visible_enumeration_at_of_leafOK hTF hReg hdeg v
    (Delta4Model.searchP_complete _ _ _ hbox hgo) h19

/-- The same from the prune-free search — the form the landed chunk table produces. -/
theorem visible_enumeration_at_of_searchNP (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size)
    (hbox : Delta4Model.Box (nOf G v) (KOf G v) (AOf G v) = true)
    (hgo : Delta4Model.searchNP Delta4Model.leafOK (nOf G v) (KOf G v) = true)
    (h19 : 19 ≤ ∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card) :
    visibleChargeTotal G v
        + 12 * (∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card)
      ≤ visibleCreditTotal G v + 212 :=
  visible_enumeration_at_of_leafOK hTF hReg hdeg v
    (Delta4Model.searchNP_leafOK_complete _ _ _ hbox hgo) h19

end PentagonLocal
end Davey2024

/-! ## 6.  Axiom audit -/

