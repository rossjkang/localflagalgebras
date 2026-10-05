import DaveyThesis2024.BasisDataIntegrity.Common

namespace Davey2024
namespace BasisDataIntegrity

set_option linter.style.nativeDecide false in
/-- **Regression.**  All 17,950 general-SEC basis flags are local: every
connected component contains an anchor.  This is the structural premise of
`SecBridge.flagBasis_sec_isLocalFlag_F`, and Paper 2's
`lem:basis-local-gen`. -/
theorem sec_basis_allAnchored :
    ∀ k : Fin SecBasis.basisSize,
      everyComponentAnchored (SecBasis.flagBasisCGraph22 k) = true := by
  native_decide
end BasisDataIntegrity
end Davey2024
