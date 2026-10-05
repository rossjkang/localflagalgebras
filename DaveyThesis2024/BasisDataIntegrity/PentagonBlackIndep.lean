import DaveyThesis2024.BasisDataIntegrity.Common

namespace Davey2024
namespace BasisDataIntegrity

set_option linter.style.nativeDecide false in
/-- **Regression.**  In all 9,295 pentagon-Q basis flags the black vertices are
independent, as `bounded_pentagon_alt_approach.rs:30` guarantees.  Held for
only 557 flags under the inverted decode. -/
theorem pentagon_basis_blackIndependent :
    ∀ k : Fin PentagonQBasis.basisSize, pentagonFlagBlackIndependent k = true := by
  native_decide
end BasisDataIntegrity
end Davey2024
