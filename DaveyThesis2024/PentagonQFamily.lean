import DaveyThesis2024.PentagonQWeights

/-!
# Item C1: the τ-anchored family, in Lean

`μ(H) ≠ 0` hands you a τ-embedding whose every out-of-image vertex is adjacent
to the root.  Relabelling so that image sits at `0 … k-1` (the permutation
`PentagonQSpikeC3.exists_perm_extending` builds) leaves only the edges *among*
the outside vertices, the edges from outside vertices to `1 … k-1`, and the
outside colours free.  That is the family this file enumerates: `2¹⁸·2⁴` for
`τ₁` and `2¹⁵·2³` for each of `τ₂`, `τ₃`, so `4718592` members.

Everything is in the `CG2` convention (`1 = black`), the one `tau1/tau2/tau3`
and `flagBasisCGraph` already use, so no colour translation happens anywhere in
this file.  `μ` is `PentagonQWeights.rootedCount` at the three patterns — the
same function obligation (b) ties to the certificate's weights.

**The milestone here is a cross-check, not a theorem about the bridge**: the
Lean family must enumerate exactly what `probes_completeness_tau_anchored.py`
enumerates — `1728` triangle-free configurations, `331` of them black-independent
with `μ ≠ 0`.  Agreement pins the encoding before anything is built on it.
-/

namespace Davey2024
namespace PentagonQFamily

open Davey2024.PentagonQBasis Davey2024.PentagonQWeights

/-- Edge slot for `{i,j}`, `i ≠ j`: the basis data's packing. -/
def eiN (i j : Nat) : Nat :=
  let a := min i j
  let b := max i j
  b * (b - 1) / 2 + a

/-- The pairs left free after the τ-image is pinned at `0 … k-1` and the root
is joined to every outside vertex: pairs among the outside, and pairs from the
outside to `1 … k-1`.  Vertex `0` is excluded — the root's edges are forced.

Every pair is stored **sorted**, so `famAdj` can look one up by `(min, max)`.
The cross pairs run outside-to-inside, so the smaller index comes second in the
generator and is put first here. -/
def freePairs (k : Nat) : List (Nat × Nat) :=
  let R := List.range' k (8 - k)
  (R.flatMap (fun a => (R.filter (fun b => a < b)).map (fun b => (a, b)))) ++
  (R.flatMap (fun a => (List.range' 1 (k - 1)).map (fun b => (b, a))))

/-- A family member, **declaratively**: outside the τ-image the graph is the
root joined to everything outside, plus whatever `mask` says about the free
pairs; inside it is the pattern.

Stated this way rather than as a fold so that C3 can characterise it — the
round trip `famGraph p (maskOf g) (cmOf g) = g` is a case split on which zone a
pair lies in, which an `Id.run do` loop would not give. -/
def famAdj (p : Pat) (mask : Nat) (i j : Nat) : Bool :=
  if i == j then false
  else if i < p.n && j < p.n then (p.padj[i]!)[j]!
  else if i == 0 || j == 0 then true
  else mask.testBit ((freePairs p.n).idxOf (min i j, max i j))

def famCol (p : Pat) (cm : Nat) (v : Nat) : Fin 2 :=
  if v < p.n then (if p.cols[v]! == 1 then 1 else 0)
  else if cm.testBit (v - p.n) then 1 else 0

/-- The family member as a `CGraph 8`, `CG2` convention. -/
def famGraph (p : Pat) (mask cm : Nat) : CGraph 8 where
  adj i j := famAdj p mask i.val j.val
  col v := famCol p cm v.val

def triangleFreeC (g : CGraph 8) : Bool :=
  (List.finRange 8).all (fun a => (List.finRange 8).all (fun b =>
    (List.finRange 8).all (fun c =>
      !(a.val < b.val && b.val < c.val && g.adj a b && g.adj b c && g.adj a c))))

def blackIndepC (g : CGraph 8) : Bool :=
  (List.finRange 8).all (fun a => (List.finRange 8).all (fun b =>
    !(a.val < b.val && g.adj a b && g.col a == 1 && g.col b == 1)))

/-- `μ`, on an arbitrary host: the same weighted sum of rooted counts that
`O_Q_weight_eq_combinatorial` matches to the certificate on the basis flags. -/
def muC (g : CGraph 8) : Nat :=
  4 * rootedCount g tau1 + rootedCount g tau2 + 2 * rootedCount g tau3

/-- `(triangle-free members, of those black-independent with μ ≠ 0)`. -/
def famCounts : Nat × Nat := Id.run do
  let mut tf := 0
  let mut nz := 0
  for p in [tau1, tau2, tau3] do
    let k := p.n
    let f := (freePairs k).length
    for mask in [0:2 ^ f] do
      for cm in [0:2 ^ (8 - k)] do
        let g := famGraph p mask cm
        if triangleFreeC g then
          tf := tf + 1
          if blackIndepC g && muC g != 0 then nz := nz + 1
  return (tf, nz)

/-- **C1 cross-check.**  The Lean family enumerates exactly what
`probes_completeness_tau_anchored.py` does. -/
theorem famCounts_eq : famCounts = (1728, 331) := by native_decide

end PentagonQFamily
end Davey2024
