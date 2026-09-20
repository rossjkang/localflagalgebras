import DaveyThesis2024.SecBasis
import DaveyThesis2024.SecBipartiteBasis
import DaveyThesis2024.PentagonQBasis

/-!
# Data-integrity regressions for the parsed flag bases

Each flag basis in this development is shipped as one long comma-separated hex
string literal and decoded at elaboration time.  Nothing downstream checks that
the decode is *faithful*: `AxiomCheck.lean` pins axiom names, and a basis is not
an axiom but a `def`.

On 2026-09-20 that gap bit.  The literals are wrapped across source lines, so the
token ending a line carried an embedded `'\n'`; `hexCharToNat` mapped it to `0`
but `parseHexStr` still applied `acc * 16`, shifting the packed integer left by
four bits.  **225** general-SEC, **117** pentagon-Q and **48** bipartite-SEC
entries decoded to a different flag than the generator emitted — and 104 of the
general ones carry a nonzero certificate coefficient.  The symptom was
misdiagnosed for most of a day as a falsity in the SEC locality axioms.

The theorems below pin, for each basis, a property that its **generator
guarantees by construction**.  They are cheap, they are `native_decide`, and any
one of them fails the moment the decode drifts again.

See the development notes.
-/

namespace Davey2024
namespace BasisDataIntegrity

/-! ## Pentagon-Q: every basis flag is triangle-free

`PentagonQBasis` enumerates *triangle-free* 2-coloured graphs on 8 vertices.
Under the broken parse, 68 of the 117 corrupted entries contained a triangle. -/

/-- Flag `k` of the pentagon-Q basis contains no triangle. -/
def pentagonFlagTriangleFree (k : Fin PentagonQBasis.basisSize) : Bool :=
  let g := PentagonQBasis.flagBasisCGraph k
  (List.finRange 8).all (fun a => (List.finRange 8).all (fun b =>
    (List.finRange 8).all (fun c => !(g.adj a b && g.adj b c && g.adj a c))))

set_option linter.style.nativeDecide false in
/-- **Regression.**  All 9,295 pentagon-Q basis flags are triangle-free, as the
Rust enumeration guarantees.  Fails if the hex decode drifts. -/
theorem pentagon_basis_triangleFree :
    ∀ k : Fin PentagonQBasis.basisSize, pentagonFlagTriangleFree k = true := by
  native_decide

/-! ## SEC: every basis flag satisfies the locality criterion

Both SEC generators filter on `flag.is_connected_to(|i| flag.color[i] == X)`:
every connected component contains an anchor.  The anchor is the colour the
class bounds, which both `secGenGraphClassF` and `secBipGenGraphClassF` take to
be projected colour `0`.  Under the broken parse, 35 general and 21 bipartite
flags appeared to violate this — the observation that was misread as the
locality axioms being false. -/

/-- Reachability inside a 5-vertex flag; four relaxation rounds suffice. -/
def reach5 (g : CGraph22 5) (u v : Fin 5) : Bool :=
  let step : (Fin 5 → Bool) → (Fin 5 → Bool) :=
    fun s w => s w || (List.finRange 5).any (fun x => s x && g.adj x w)
  (step (step (step (step (fun w => w == u))))) v

/-- Every connected component of `g` contains a projected-colour-`0` vertex. -/
def everyComponentAnchored (g : CGraph22 5) : Bool :=
  (List.finRange 5).all (fun u =>
    (List.finRange 5).any (fun v => reach5 g u v && ((g.vertexCol v).val == 0)))

set_option linter.style.nativeDecide false in
/-- **Regression.**  All 17,950 general-SEC basis flags are local: every
connected component contains an anchor.  This is the structural premise of
`SecBridgeF.flagBasis_sec_isLocalFlag_F`, and Paper 2's
`lem:basis-local-gen`. -/
theorem sec_basis_allAnchored :
    ∀ k : Fin SecBasis.basisSize,
      everyComponentAnchored (SecBasis.flagBasisCGraph22 k) = true := by
  native_decide

set_option linter.style.nativeDecide false in
/-- **Regression.**  All 3,808 bipartite-SEC basis flags are local.  Premise of
`SecBipartiteBridge.flagBasis_sec_bip_isLocalFlag_F` and Paper 2's
`lem:basis-local-bip`.  Here the projection sends the paper's `X_COLS = {0,1}`
to `0` and `Y_COLS = {2,3}` to `1`, so colour `0` is again the anchor. -/
theorem sec_bip_basis_allAnchored :
    ∀ k : Fin SecBipartiteBasis.basisSize,
      everyComponentAnchored (SecBipartiteBasis.flagBasisCGraph22 k) = true := by
  native_decide

/-! ## The general-SEC colour alphabet

`strong_edge_colouring.rs` uses `Colored<CGraph<3>, 2>`: two vertex colours, so
every raw vertex value is `0` or `1`.  The shifted parse moved edge bits into the
vertex window and produced the value `2` in 205 entries — the cheapest possible
detector, and the one that first exposed the defect. -/

set_option linter.style.nativeDecide false in
/-- **Regression.**  Every raw vertex value in the general-SEC basis lies in
`{0, 1}`, as its two-colour flag type requires. -/
theorem sec_basis_rawVertexColours_lt_two :
    ∀ k : Fin SecBasis.basisSize, ∀ v : Fin SecBasis.flagOrder,
      SecBasis.extractVertexRaw (SecBasis.basisAdjArr[k.val]!) v.val < 2 := by
  native_decide

end BasisDataIntegrity
end Davey2024
