import DaveyThesis2024.Delta4.BoxOfRoot
import DaveyThesis2024.Delta4.CreditCharge
import DaveyThesis2024.Delta4.MaskGen
import DaveyThesis2024.Delta4.Prune

/-!
# The Δ = 4 assembly is unconditional except for one closed `Bool`

An earlier version of this file was **vacuous**: every theorem was conditional on `BoxOfRoot`,
and `BoxOfRoot` was false for the encoding then landed.  `Delta4Model.Box` carries clause
(D16), "masks non-decreasing along slots", but `Transport.shellArr` ordered the shell by
*vertex index*, and nothing re-canonicalised — `C₁₀(1,3)` at root `0` gives masks `11, 7, 14,
13` in vertex order, and 97.7% of the 3,677 census roots violated (D16).

**That defect is repaired.**  `Transport.shellArr` now enumerates `S⁺(v)` in non-decreasing
attachment-mask order (`Transport` §7.1), which makes (D16) true by construction; the order is
used nowhere else, because every support lemma the transport needs is proved at `Transport`
§7.0 for an arbitrary duplicate-free enumeration.  `PentagonLocal.box_of_root` (obligation 10,
`Delta4/BoxOfRoot.lean`) is therefore unconditional, and `boxOfRoot_holds` below discharges the
hypothesis this file used to carry.  Nothing here is conditional on it any more.

What remains conditional is `checkAll = true` — one closed `Bool`, no graph in sight.  Its
bottom layers are discharged in §5 by `decide +kernel`; the upper layers are obligation 21's
chunk table.

The file also pins down two facts worth keeping: the chain consumes the search and the
generator only in the **completeness** direction (soundness is an anti-vacuity guard, not a
link), and the finite check is genuinely finite (`msGen n` is a concrete `List`, with lengths
`0,0,0,1,14,92,221,249,172,81,25,6,1` for `n = 0..12`).
-/

-- (BoxCore not needed: `Delta4Model.box_size` lives in Model.lean)

/-!
# Δ = 4, Stage 4: obligation 22 — ASSEMBLY

This file wires the landed Stage-4 pieces into one theorem that reduces `henum` — and hence
the sharp Δ = 4 pentagon bound `P(G) ≤ 4|G|` — to a **single closed `Bool`**, `checkAll`.

## The chain, as actually composed here

```
  box_of_root                    (obligation 10, PROVED, Delta4/BoxOfRoot.lean)
      ⟹  msGen_complete_of_box   (obligation 19, landed, MaskGen.lean)
      ⟹  box_size                (landed, Model.lean)        n ≤ 12
      ⟹  FiniteCheck             (the hypothesis: searchP n K = true on the generated list)
      ⟹  searchP_complete        (obligations 16+17, landed, Prune.lean)
      ⟹  leafOK (nOf, KOf, AOf) = true
      ⟹  visible_enumeration_at_of_leafOK  (obligations 12/13, landed, CreditCharge.lean)
      ⟹  henum
      ⟹  pentagon_bound_delta4_of_visible_enumeration  (landed, PentagonDelta4.lean)
```

## What is ASSUMED

Exactly **one** unproved input: `checkAll = true`, a closed `Bool`.  Obligation 10 —
`BoxOfRoot`, once a hypothesis of every theorem here — is discharged by `boxOfRoot_holds` from
`PentagonLocal.box_of_root`, so no graph-side hypothesis survives.

**`search_sound` (obligation 18) turned out NOT to be needed by the assembly.**  The chain
consumes the search only in the *completeness* direction (`searchP_complete`: `searchP n K =
true` plus `Box n K A = true` forces `leafOK n K A = true`), and likewise the generator only
in the *completeness* direction (`msGen_complete_of_box`).  Soundness of either is a
non-vacuity guard, not a link in the chain.  See `assembly_uses_only_completeness` below.

## The factor of two

The graph-side gate is `19 ≤ T`; the model-side leaf gate is `twoT < 38`.  This file never
touches that bookkeeping directly: `visible_enumeration_at_of_leafOK` (CreditCharge §9) does
it once, via `two_mul_shellObjective_eq_model`.  Every statement below is in the **graph's
`T`** (the `shellPairsLt` sum), matching `pentagon_bound_delta4_of_visible_enumeration`
verbatim.

No `native_decide`, no new axiom, no `sorry`.
-/

namespace Davey2024
namespace Delta4Assembly

open Finset
open scoped Classical
open PentagonLocal

set_option maxRecDepth 1000000

/-! ## 1.  The two inputs, named -/

/-- **The finite check.**  Every mask multiset the generator produces, at every admissible
    shell size, survives the pruned search.  This is a statement about `Nat` arithmetic on
    an explicit finite list: no graph, no `Flag`, no quantifier over `A`. -/
def FiniteCheck : Prop :=
  ∀ n K : ℕ, n ≤ 12 → K ∈ Delta4Model.msGen n → Delta4Model.searchP n K = true

/-- **Obligation 10.**  The encoding of a rooted triangle-free 4-regular ball lands in the
    search box.  Kept as a named `Prop` because the chain below is stated against it; it is
    no longer a hypothesis — `boxOfRoot_holds` proves it. -/
def BoxOfRoot : Prop :=
  ∀ H : Flag emptyType, IsTriangleFree H → IsRegular H → maxDegree H = 4 →
    ∀ v : Fin H.size, Delta4Model.Box (nOf H v) (KOf H v) (AOf H v) = true

/-- **Obligation 10, discharged.**  `PentagonLocal.box_of_root` proves all eleven clauses of
    `Delta4Model.Box` at every root of every triangle-free 4-regular graph, with no hypothesis
    on the vertex labelling: the shell enumeration is mask-sorted by construction, which is
    clause (D16). -/
theorem boxOfRoot_holds : BoxOfRoot :=
  fun _ hTF hReg hdeg v => box_of_root hTF hReg hdeg v

/-! ## 2.  The finite check as one closed `Bool`

`FiniteCheck` still has a `∀ n K`, but both ranges are finite and explicit, so it is the
truth of a single closed `Bool` term.  `checkAll` is that term; `msGen_eq_nil_of_thirteen_le`
is what makes `13` the right cutoff. -/

/-- The whole Stage-4 finite check, as one closed `Bool`. -/
def checkAll : Bool :=
  Delta4Model.allUpto (fun n => (Delta4Model.msGen n).all (fun K => Delta4Model.searchP n K)) 13

theorem finiteCheck_of_checkAll (h : checkAll = true) : FiniteCheck := by
  intro n K hn hK
  have hn13 : n < 13 := by omega
  have hall := (Delta4Model.allUpto_eq_true_iff).1 h n hn13
  exact List.all_eq_true.1 hall K hK

/-! ## 3.  Obligation 10 + the finite check ⟹ the model leaf test at every root -/

/-- **The model side collapses.**  From the box transport and the finite check, `leafOK`
    holds at the encoding of every root of every triangle-free 4-regular graph — which is
    exactly the hypothesis of `pentagon_bound_delta4_of_model_leaf`. -/
theorem leafOK_of_finite_check (hcheck : FiniteCheck)
    (H : Flag emptyType) (hTF : IsTriangleFree H) (hReg : IsRegular H)
    (hdeg : maxDegree H = 4) (v : Fin H.size) :
    Delta4Model.leafOK (nOf H v) (KOf H v) (AOf H v) = true := by
  have hb : Delta4Model.Box (nOf H v) (KOf H v) (AOf H v) = true :=
    boxOfRoot_holds H hTF hReg hdeg v
  have hn : nOf H v ≤ 12 := (Delta4Model.box_size hb).2
  have hK : KOf H v ∈ Delta4Model.msGen (nOf H v) := Delta4Model.msGen_complete_of_box hb
  exact Delta4Model.searchP_complete _ _ _ hb (hcheck _ _ hn hK)

/-! ## 4.  … and therefore `henum`, and therefore the sharp bound -/

/-- **`henum` from the finite check.**  Verbatim the hypothesis of
    `pentagon_bound_delta4_of_visible_enumeration`, now discharged from obligation 10 plus a
    finite `Nat` computation.  The `19 ≤ T` gate is the graph's `T`; the model's `2T < 38`
    branch is consumed inside `visible_enumeration_at_of_leafOK`. -/
theorem visible_enumeration_of_finite_check (hcheck : FiniteCheck) :
    ∀ H : Flag emptyType, IsTriangleFree H → IsRegular H → maxDegree H = 4 →
      ∀ v : Fin H.size,
        19 ≤ (∑ p ∈ shellPairsLt H v, (attachSet H v p.1).card * (attachSet H v p.2).card) →
        visibleChargeTotal H v
            + 12 * (∑ p ∈ shellPairsLt H v,
                (attachSet H v p.1).card * (attachSet H v p.2).card)
          ≤ visibleCreditTotal H v + 212 :=
  fun H hTF hReg hdeg v h19 =>
    visible_enumeration_at_of_leafOK hTF hReg hdeg v
      (leafOK_of_finite_check hcheck H hTF hReg hdeg v) h19

/-- **THE ASSEMBLY.**  `P(G) ≤ 4|G|` for every triangle-free graph of maximum degree at most
    four, from obligation 10 (`BoxOfRoot`, proved) plus the finite check alone. -/
theorem pentagon_bound_delta4_of_finite_check (hcheck : FiniteCheck)
    (G : Flag emptyType) (hTF : IsTriangleFree G) (hdeg : maxDegree G ≤ 4) :
    pentagonCount G ≤ 4 * G.size :=
  pentagon_bound_delta4_of_model_leaf
    (fun H hHTF hHReg hHdeg v => leafOK_of_finite_check hcheck H hHTF hHReg hHdeg v)
    G hTF hdeg

/-- The same, with the finite check in its single-`Bool` form.  Obligation 10 has landed, so
    the *entire* remaining gap between the Lean library and an unconditional
    `pentagon_bound_delta4` is `checkAll = true` — one closed `Bool`, no graph in sight. -/
theorem pentagon_bound_delta4_of_checkAll (hcheck : checkAll = true)
    (G : Flag emptyType) (hTF : IsTriangleFree G) (hdeg : maxDegree G ≤ 4) :
    pentagonCount G ≤ 4 * G.size :=
  pentagon_bound_delta4_of_finite_check (finiteCheck_of_checkAll hcheck) G hTF hdeg

/-! ## 5.  Guards

The assembly must not be vacuous in either of the two directions the plan worries about. -/

/-- **Guard 1 — the chain uses only completeness.**  Spelled out as a standalone fact: the
    step from the finite check to the leaf test needs `msGen_complete_of_box` and
    `searchP_complete` and nothing else about the generator or the search.  (This is the same
    proof as `leafOK_of_finite_check`, stated with `Box` as a bare hypothesis so that no
    graph, and in particular no appeal to obligation 10, appears.) -/
theorem assembly_uses_only_completeness (hcheck : FiniteCheck) {n K A : ℕ}
    (hb : Delta4Model.Box n K A = true) : Delta4Model.leafOK n K A = true :=
  Delta4Model.searchP_complete n K A hb
    (hcheck n K (Delta4Model.box_size hb).2 (Delta4Model.msGen_complete_of_box hb))

/-- **Guard 2 — the finite check is a real computation, not a tautology.**  Its bottom
    layers evaluate in the kernel, one declaration per shell size (the plan's §5 D10 chunking
    discipline, as in `MaskGen`'s `msGen_card_*`).  `n = 3` is the `K₄,₄` shell
    (`msGen 3 = [0xfff]`, `searchP 3 4095 = true`, both already landed).

    Measured wall clock for these four, on this machine: `n = 3,4` under a second each,
    `n = 5` ≈ 3 s, `n = 6` ≈ 14 s.  `n = 7` (249 masks, 21 shell pairs) did **not** finish:
    killed at 12 minutes with 1.7 GB resident and still growing.  That is the wall
    obligation 21's chunk table exists to break, and it is why no `checkAll = true`
    declaration appears in this file. -/
theorem checkAll_layer_three :
    (Delta4Model.msGen 3).all (fun K => Delta4Model.searchP 3 K) = true := by decide +kernel

theorem checkAll_layer_four :
    (Delta4Model.msGen 4).all (fun K => Delta4Model.searchP 4 K) = true := by decide +kernel

theorem checkAll_layer_five :
    (Delta4Model.msGen 5).all (fun K => Delta4Model.searchP 5 K) = true := by decide +kernel

theorem checkAll_layer_six :
    (Delta4Model.msGen 6).all (fun K => Delta4Model.searchP 6 K) = true := by decide +kernel

/-- **Guard 3 — the check is falsifiable above the cutoff too.**  There is nothing to check
    at `n = 13`, and that is a theorem about the generator rather than a convention baked
    into `checkAll`. -/
theorem checkAll_cutoff_sound {n : ℕ} (h : 13 ≤ n) :
    (Delta4Model.msGen n).all (fun K => Delta4Model.searchP n K) = true := by
  rw [Delta4Model.msGen_eq_nil_of_thirteen_le h]; rfl

end Delta4Assembly
end Davey2024

section AxiomCheck

end AxiomCheck
