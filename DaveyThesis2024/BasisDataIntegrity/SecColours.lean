import DaveyThesis2024.BasisDataIntegrity.Common

namespace Davey2024
namespace BasisDataIntegrity

set_option linter.style.nativeDecide false in
/-- **Regression.**  Every raw vertex value in the general-SEC basis lies in
`{0, 1}`, as its two-colour flag type requires. -/
theorem sec_basis_rawVertexColours_lt_two :
    ∀ k : Fin SecBasis.basisSize, ∀ v : Fin SecBasis.flagOrder,
      SecBasis.extractVertexRaw (SecBasis.basisAdjArr[k.val]!) v.val < 2 := by
  native_decide
end BasisDataIntegrity
end Davey2024
