import DaveyThesis2024.SecAsymBasis

/-!
# Structural regression for the asymmetric locality axiom

`SecAsymBridgeF.flagBasis_asym_isLocalFlag_F` asserts that **every** one of the
334 asymmetric basis flags is a local flag for `secAsymGenGraphClass4`.  Unlike
the gated axioms, it takes no hypothesis, so there is nothing for a non-vacuity
regression to check — its risk is *falsity*, not vacuity.

That risk is not hypothetical.  The pentagon analogue `flagBasis_isLocalFlag`
is a **theorem restricted to 69 of 9295 indices**.  The counterexample that
originally motivated that restriction -- an all-red empty 8-flag of unbounded
density -- was an artefact of the colour inversion repaired on 2026-09-27 and
does not exist: entry 0 is the all-BLACK empty flag, and every one of the 9295
is anchored (`BasisDataIntegrity.pentagon_basis_first_all_black`,
`pentagon_basis_allAnchored`).  The restriction is retained because the proof
and every consumer supply it; whether the unrestricted claim holds is
unproved.

The asymmetric axiom is defensible on different grounds — its justification is
that the generator emits only local flags — but that premise lived in a
docstring and was never checked.  This file checks it.

**The criterion.**  `secAsymGenGraphClass4` bounds the number of vertices of
colour `0` or `1` by `2·Δ` and leaves colours `2, 3` unbounded.  So colours
`0, 1` are the anchors, and the thesis locality criterion reads: every connected
component of the flag contains an anchor.  A component without one can be
duplicated freely at fixed `Δ`, which is exactly how the pentagon's counterexample
achieves unbounded density.

Checked by `native_decide`.  Kernel `decide` does not work here: the basis is
parsed from a string literal, so `flagBasisCGraph4` does not reduce in the
kernel.  That is the same reason the pentagon's analogous structural check
(`flagBasis_nonzero_vertexOrderProp`) uses `native_decide`, and the asymmetric
SEC headline already carries `Lean.ofReduceBool` / `Lean.trustCompiler` in any
case; the guard in `AxiomCheck.lean` records those two axioms explicitly.  Six of the 334 flags are edgeless — five singleton components each, the
shape of the pentagon counterexample — and all six are anchored throughout.
-/

namespace Davey2024
namespace SecAsymBasisAnchored

open Davey2024.SecAsymBasis

/-- Reachability inside a 5-vertex flag: four rounds of relaxation suffice to
close the transitive closure. -/
def reach (k : Fin basisSize) (u v : Fin flagOrder) : Bool :=
  let g := flagBasisCGraph4 k
  let step : (Fin flagOrder → Bool) → (Fin flagOrder → Bool) :=
    fun s w => s w || (List.finRange flagOrder).any (fun x => s x && g.adj x w)
  let s0 : Fin flagOrder → Bool := fun w => w == u
  (step (step (step (step s0)))) v

/-- The anchors of `secAsymGenGraphClass4` are the vertices of colour `0` or `1`;
their number is what the class bounds by `2·Δ`. -/
def isAnchor (k : Fin basisSize) (v : Fin flagOrder) : Bool :=
  let c := ((flagBasisCGraph4 k).vertexCol v).val
  c == 0 || c == 1

/-- Every connected component of flag `k` contains an anchor. -/
def everyComponentAnchored (k : Fin basisSize) : Bool :=
  (List.finRange flagOrder).all (fun u =>
    (List.finRange flagOrder).any (fun v => reach k u v && isAnchor k v))

set_option linter.style.nativeDecide false in
/-- **The regression.**  Every one of the 334 asymmetric basis flags satisfies
the locality criterion: each of its connected components contains a vertex of
colour `0` or `1`.

This is the structural premise on which
`SecAsymBridgeF.flagBasis_asym_isLocalFlag_F` rests.  If a future regeneration of
the basis emits a flag with an anchorless component, that axiom becomes false and
this theorem fails — which is the point. -/
theorem all_basis_flags_anchored :
    ∀ k : Fin basisSize, everyComponentAnchored k = true := by
  native_decide

end SecAsymBasisAnchored
end Davey2024
