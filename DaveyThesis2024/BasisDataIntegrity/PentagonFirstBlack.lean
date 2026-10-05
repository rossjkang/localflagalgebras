import DaveyThesis2024.BasisDataIntegrity.Common

namespace Davey2024
namespace BasisDataIntegrity

set_option linter.style.nativeDecide false in
/-- **Regression: orientation.**  Neither of the two above pins the direction
by itself: a decoder returning colour 0 everywhere passes independence (no
colour-1 vertex, so no colour-1 edge) but fails anchoring, and one returning
colour 1 everywhere passes anchoring but fails independence.  This entry pins
which way round the surviving reading is.  Entry 0 is the empty graph with every packed colour bit
clear; in `CG2` colours that is the **all-black** flag.  Eight mutually
independent blacks force the empty graph, which is why this entry is unique. -/
theorem pentagon_basis_first_all_black :
    (List.finRange 8).all (fun v =>
      (PentagonQBasis.flagBasisCGraph ⟨0, by decide⟩).col v == 1) = true := by
  native_decide
end BasisDataIntegrity
end Davey2024
