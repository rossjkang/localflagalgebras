import DaveyThesis2024.PentagonQCertificate
import DaveyThesis2024.PentagonQBasis

/-!
# The pentagon-Q objective coefficients, extracted

`O_Q_weight` and `O_Q_coef` lived in `PentagonQBridge`, which forced
`PentagonQWeights` — and through it the whole `(a)` chain — to depend on that
module.  That made it impossible to discharge
`pentagonQ_basis_combinatorial_identity_step1` in place: the proof of the axiom
sits downstream of its own declaration.

They need only the certificate's `target` and the basis size, so they extract
cleanly to a module upstream of both.  `PentagonQBridge` re-exports them, so its
33 existing uses are unaffected.
-/

/-! ## Why these definitions look the way they do

Moved here with the definitions on 2026-10-01.  One of this project's false
axioms — the 2026-09-26 rounded coefficients — was about exactly these
definitions, so the rationale below travels with them rather than staying behind
in `PentagonQBridge`.  (The 2026-09-27 colour inversion was a separate defect, in
the size-8 basis decoder, not here.)


**Sign convention (load-bearing).** The PentagonQ SDPA file
`DaveyThesis2024/certificates/bounded_pentagon_alt.sdpa` uses the
`min -(...)` objective:

```
Minimizing: -([|Σ f(F)F|] + [|Σ f(F)F|] + 2*[|Σ f(F)F|])
```

so SDPA's `c` vector represents the **negative** of the actual pentagon
flag coefficients. `emit_lean_cert.py` line 922 stores
`target_int = c_rat * DENOM_Y` directly (no sign flip), hence
`targetArr[k] ≤ 0` for every basis index `k` (empirically: 9295 entries,
0 positive). `O_Q_coef` flips this sign so it represents the TRUE
non-negative pentagon flag coefficient at basis index `k`:

```
O_Q_coef k = O_Q_weight k / 6720 = μ_k / 6720 ≥ 0
```

(The 12-digit rationalisation `-target[k] / linearScale` was the definition
until 2026-09-26, when it was found to make the basis combinatorial identity
false; see below.)

(`linearScale = 10^12` is the rationalisation precision used by
`local-flags-certificates/emit_lean_cert.py`.)

This sign flip makes the combinatorial identity
`pentagonQ/Δ⁵ = (1/2)·Σ O_Q_coef · density` sign-consistent: LHS ≥ 0
(pentagonQ count), and RHS ≥ 0 (both factors non-negative). Without
the flip, the identity is FALSE as stated (LHS ≥ 0, RHS ≤ 0); see
`project_pentagonQ_sign_convention.md` for the full diagnosis.

**Exact coefficients (repair of 2026-09-26).** Until this date the
coefficient was the 12-digit rounding `-target[k] / linearScale` itself.
That made `pentagonQ_basis_combinatorial_identity_step1` FALSE: the true
coefficient is the rational `μ_k / 6720`, with `μ_k = 4n₁ + n₂ + 2n₃` the
integer weight of the paper's basis combinatorial identity lemma, and all 69
non-zero targets differ
from `μ_k·10¹²/6720` by a non-zero rounding (none of the `μ_k` is divisible
by 21), so the limit of `2Q/Δ⁵ − Σ coef·ρ` along Clebsch blow-ups is
`−4.36·10⁻¹¹`, not `0`. The weight is recovered exactly from the target by
rounding, since `|target·6720/10¹² − μ_k| ≤ 6720/(2·10¹²) < 1/2`.  Both named
statements — the certificate output bound, still an axiom, and the basis
combinatorial identity, a theorem since 2026-10-01 — speak of the exact
objective, whose bound `≤ 0.4146` the 16-digit
verification covers (its decimal objective is within `2·10⁻¹⁹` per
coefficient of `μ_k/6720`, against a margin of `1.06·10⁻⁵`). -/

namespace Davey2024
namespace PentagonQObjective

/-- The cert's `target` vector cached as an `Array Int` for O(1) indexing. -/
def targetArr : Array Int :=
  (Davey2024.PentagonQCertificate.target).toArray

/-- The integer weight `μ_k = 4n₁ + n₂ + 2n₃`, recovered exactly from the
certificate's target by rounding. -/
def O_Q_weight (k : Fin Davey2024.PentagonQBasis.basisSize) : ℤ :=
  round ((-(targetArr[k.val]! : ℚ) * 6720) /
    (Davey2024.PentagonQCertificate.linearScale : ℚ))

/-- The ℝ coefficient for basis index `k`: exactly `μ_k / 6720`. -/
noncomputable def O_Q_coef (k : Fin Davey2024.PentagonQBasis.basisSize) : ℝ :=
  ((O_Q_weight k : ℤ) : ℝ) / 6720

end PentagonQObjective
end Davey2024
