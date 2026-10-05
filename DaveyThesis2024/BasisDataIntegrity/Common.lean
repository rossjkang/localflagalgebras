import DaveyThesis2024.SecBasis
import DaveyThesis2024.SecBipartiteBasis
import DaveyThesis2024.PentagonQBasis

/-!
# Shared definitions for the basis data-integrity regressions

The seven checks live one per module alongside this one, so Lake builds them
concurrently.  As a single module they ran serially and dominated the port's CI wall clock.
The theorems are independent and separately consumed, so splitting them needed
no proof work -- only relocation.

What the checks are for, and what they caught, is in `BasisDataIntegrity.lean`.
-/

namespace Davey2024
namespace BasisDataIntegrity

/-- Flag `k` of the pentagon-Q basis contains no triangle. -/
def pentagonFlagTriangleFree (k : Fin PentagonQBasis.basisSize) : Bool :=
  let g := PentagonQBasis.flagBasisCGraph k
  (List.finRange 8).all (fun a => (List.finRange 8).all (fun b =>
    (List.finRange 8).all (fun c => !(g.adj a b && g.adj b c && g.adj a c))))

/-- The colour-1 (black) vertices of pentagon-Q flag `k` are pairwise
non-adjacent — black is `N(v)` in a triangle-free host. -/
def pentagonFlagBlackIndependent (k : Fin PentagonQBasis.basisSize) : Bool :=
  let g := PentagonQBasis.flagBasisCGraph k
  (List.finRange 8).all (fun u => (List.finRange 8).all (fun v =>
    !(g.col u == 1 && g.col v == 1 && g.adj u v)))

/-- Reachability inside an 8-vertex flag; seven relaxation rounds suffice. -/
def reach8 (g : CGraph 8) (u v : Fin 8) : Bool :=
  let step : (Fin 8 → Bool) → (Fin 8 → Bool) :=
    fun s w => s w || (List.finRange 8).any (fun x => s x && g.adj x w)
  (step (step (step (step (step (step (step (fun w => w == u)))))))) v

/-- Every connected component of pentagon-Q flag `k` contains a black vertex. -/
def pentagonFlagAnchored (k : Fin PentagonQBasis.basisSize) : Bool :=
  let g := PentagonQBasis.flagBasisCGraph k
  (List.finRange 8).all (fun u =>
    (List.finRange 8).any (fun v => reach8 g u v && g.col v == 1))

/-- Reachability inside a 5-vertex flag; four relaxation rounds suffice. -/
def reach5 (g : CGraph22 5) (u v : Fin 5) : Bool :=
  let step : (Fin 5 → Bool) → (Fin 5 → Bool) :=
    fun s w => s w || (List.finRange 5).any (fun x => s x && g.adj x w)
  (step (step (step (step (fun w => w == u))))) v

/-- Every connected component of `g` contains a projected-colour-`0` vertex. -/
def everyComponentAnchored (g : CGraph22 5) : Bool :=
  (List.finRange 5).all (fun u =>
    (List.finRange 5).any (fun v => reach5 g u v && ((g.vertexCol v).val == 0)))
/-! ### A materialised reachability, equal to `reach8` and ~500x cheaper

`reach8` nests seven `step` **closures**, and each `step s w` calls `s` again --
once directly and up to eight times inside the `any`. Short-circuiting keeps
that from being the full `9^7`, but on a pair of vertices in different
components nothing short-circuits and the chain costs ~8^7 base evaluations.
`native_decide` runs the IR interpreter (there are no compiled dynlibs in
`.lake/build`), so the disconnected basis flags alone made this the single most
expensive module in the development.  Measured figures belong downstream, in
`PentagonQAssembleA`.

The fix is to pass the reachable set between rounds as **data**, which makes
it cheap. Note the trap:
a version that still returns `Fin 8 -> Bool` is eta-expanded to arity 2 by the
compiler, so the table is rebuilt on every lookup and the chain is exponential
again. `stepArr` takes and returns an `Array Bool`.

`reach8` stays as the readable specification; `reachArr` is proved equal to it
for **every** graph, so nothing rests on an instance check. -/

/-- Read a materialised 8-vertex set back as a predicate. -/
def toFun (a : Array Bool) : Fin 8 → Bool := fun w => a.getD w.val false

theorem toFun_ofFn (f : Fin 8 → Bool) : toFun (Array.ofFn f) = f := by
  funext w; simp [toFun, Array.getD_eq_getD_getElem?]

/-- One relaxation round, on data rather than closures. -/
def stepArr (g : CGraph 8) (a : Array Bool) : Array Bool :=
  Array.ofFn (fun w => toFun a w || (List.finRange 8).any (fun x => toFun a x && g.adj x w))

theorem toFun_stepArr (g : CGraph 8) (a : Array Bool) :
    toFun (stepArr g a)
      = fun w => toFun a w || (List.finRange 8).any (fun x => toFun a x && g.adj x w) := by
  unfold stepArr; rw [toFun_ofFn]

/-- Seven rounds, materialised. -/
def reachArr (g : CGraph 8) (u : Fin 8) : Array Bool :=
  stepArr g (stepArr g (stepArr g (stepArr g (stepArr g (stepArr g
    (stepArr g (Array.ofFn (fun w => w == u))))))))

theorem reachArr_eq (g : CGraph 8) (u v : Fin 8) : toFun (reachArr g u) v = reach8 g u v := by
  simp only [reachArr, reach8, toFun_stepArr, toFun_ofFn]

/-- `pentagonFlagAnchored`, computed once per `u` instead of once per `(u,v)`. -/
def pentagonFlagAnchoredFast (k : Fin PentagonQBasis.basisSize) : Bool :=
  let g := PentagonQBasis.flagBasisCGraph k
  (List.finRange 8).all (fun u =>
    let r := reachArr g u
    (List.finRange 8).any (fun v => toFun r v && g.col v == 1))

theorem pentagonFlagAnchoredFast_eq (k : Fin PentagonQBasis.basisSize) :
    pentagonFlagAnchoredFast k = pentagonFlagAnchored k := by
  simp only [pentagonFlagAnchoredFast, pentagonFlagAnchored, reachArr_eq]

end BasisDataIntegrity
end Davey2024
