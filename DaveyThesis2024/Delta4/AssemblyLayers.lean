import DaveyThesis2024.Delta4.Assembly

/-!
# Δ = 4: assembling the finite check into `checkAll = true`

`checkAll_of_entries` and `checkAll_of_layers` reduce `checkAll = true` to per-entry or
per-layer facts, and `pentagon_bound_delta4_sharp_of_checkAll` is the graph-side headline,
**conditional and named as such**.  Note the existing `PentagonLocal.pentagon_bound_delta4`
proves the *weaker* `5 * pentagonCount G ≤ 24 * G.size`; this is a different statement.

## ⚠️ `LayerOK n` does NOT pin the layer — use node counts instead

`LayerOK n` is `(msGen n).all (…) = true`, a closed decidable proposition, so it reduces to
`true = true`.  Consequently **a proof about one layer is defeq-accepted as a proof about
another**: `theorem hole : LayerOK 4 := checkAll_layer_three` typechecks, in 2.8 s, on
`[propext]`.  Verified directly.

This is not unsound — the elaborator really does evaluate the layer it is asked about, so
`LayerOK 4` genuinely holds — but it means **the layer lemmas carry no information about which
layer was checked**, and a mislabelled generated file would pass silently.  Any generation
scheme must therefore assert something that distinguishes the work: a node count, as in
`goAllPCnt … = (N, 0)`, where `(3764, 0)` and `(92, 0)` are different propositions and a
mislabelled or dropped chunk contradicts arithmetic.  Node counts in the assertion are not
belt-and-braces here; they are the only thing separating the layers.
-/

namespace Delta4Assembly
open Davey2024
abbrev LayerOK (n : Nat) : Prop :=
  (Delta4Model.msGen n).all (fun K => Delta4Model.searchP n K) = true


theorem checkAll_of_entries
    (h : ∀ n K : Nat, n ≤ 12 → K ∈ Delta4Model.msGen n → Delta4Model.searchP n K = true) :
    Delta4Assembly.checkAll = true := by
  refine Delta4Model.allUpto_eq_true_iff.2 ?_
  intro i hi
  exact List.all_eq_true.2 (fun K hK => h i K (by omega) hK)

theorem checkAll_of_layers
    (h3 : LayerOK 3) (h4 : LayerOK 4) (h5 : LayerOK 5) (h6 : LayerOK 6)
    (h7 : LayerOK 7) (h8 : LayerOK 8) (h9 : LayerOK 9) (h10 : LayerOK 10)
    (h11 : LayerOK 11) (h12 : LayerOK 12) :
    Delta4Assembly.checkAll = true := by
  refine Delta4Model.allUpto_eq_true_iff.2 ?_
  intro i hi
  match i, hi with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel
  | 2, _ => decide +kernel
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6
  | 7, _ => exact h7
  | 8, _ => exact h8
  | 9, _ => exact h9
  | 10, _ => exact h10
  | 11, _ => exact h11
  | 12, _ => exact h12


theorem pentagon_bound_delta4_sharp_of_checkAll (hcheck : Delta4Assembly.checkAll = true)
    (G : Flag emptyType) (hTF : IsTriangleFree G) (hdeg : maxDegree G ≤ 4) :
    pentagonCount G ≤ 4 * G.size :=
  Delta4Assembly.pentagon_bound_delta4_of_checkAll hcheck G hTF hdeg




end Delta4Assembly
