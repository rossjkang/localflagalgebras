import DaveyThesis2024.BasisDataIntegrity.Common

namespace Davey2024
namespace BasisDataIntegrity

set_option linter.style.nativeDecide false in
/-- **Regression.**  All 9,295 pentagon-Q basis flags are triangle-free, as the
Rust enumeration guarantees.  Fails if the hex decode drifts. -/
theorem pentagon_basis_triangleFree :
    ∀ k : Fin PentagonQBasis.basisSize, pentagonFlagTriangleFree k = true := by
  native_decide
end BasisDataIntegrity
end Davey2024
