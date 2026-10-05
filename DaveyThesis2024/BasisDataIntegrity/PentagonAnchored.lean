import DaveyThesis2024.BasisDataIntegrity.Common

namespace Davey2024
namespace BasisDataIntegrity

set_option linter.style.nativeDecide false in
/-- The compiled check, run on the materialised `reachArr` rather than on
`reach8`'s closure chain.  Same predicate: `pentagonFlagAnchoredFast_eq` proves
the two agree for every basis flag, from `reachArr_eq`, which holds for every
graph.  This is what took the module from the most expensive in the development to
one of the cheapest. -/
theorem pentagon_basis_allAnchoredFast :
    ∀ k : Fin PentagonQBasis.basisSize, pentagonFlagAnchoredFast k = true := by
  native_decide

/-- **Regression.**  All 9,295 pentagon-Q basis flags are anchored: every
connected component contains a black vertex, which is the generator's locality
filter (`bounded_pentagon_alt_approach.rs:26`) and what makes a flag local.
Held for only 7,905 flags under the inverted decode.

Statement unchanged; only the route to it is cheaper.  Note the check is sharp
in its round count -- at six rounds one flag fails, at five more do -- so a
weakened reachability would not quietly pass, but a `reach8` returning `true`
everywhere would, since every basis flag has a black vertex.  That is why the
fast version is proved equal rather than merely observed to agree. -/
theorem pentagon_basis_allAnchored :
    ∀ k : Fin PentagonQBasis.basisSize, pentagonFlagAnchored k = true :=
  fun k => (pentagonFlagAnchoredFast_eq k) ▸ (pentagon_basis_allAnchoredFast k)

end BasisDataIntegrity
end Davey2024
