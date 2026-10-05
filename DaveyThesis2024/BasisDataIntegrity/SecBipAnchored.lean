import DaveyThesis2024.BasisDataIntegrity.Common

namespace Davey2024
namespace BasisDataIntegrity

set_option linter.style.nativeDecide false in
/-- **Regression.**  All 3,808 bipartite-SEC basis flags are local.  Premise of
`SecBipartiteBridge.flagBasis_sec_bip_isLocalFlag_F` and Paper 2's
`lem:basis-local-bip`.  Here the projection sends the paper's `X_COLS = {0,1}`
to `0` and `Y_COLS = {2,3}` to `1`, so colour `0` is again the anchor. -/
theorem sec_bip_basis_allAnchored :
    ∀ k : Fin SecBipartiteBasis.basisSize,
      everyComponentAnchored (SecBipartiteBasis.flagBasisCGraph22 k) = true := by
  native_decide
end BasisDataIntegrity
end Davey2024
