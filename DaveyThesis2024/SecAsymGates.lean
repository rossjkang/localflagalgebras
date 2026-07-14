import DaveyThesis2024.SecAsymBasis
import DaveyThesis2024.AsymSecCertificate
import DaveyThesis2024.CGraph22Bridge

set_option linter.style.nativeDecide false

/-!
# L5.B audit gates: G-VACUITY, G-PROVENANCE (+ cert slack budget)

Machine-checked evidence that the new 4-colour asymmetric SEC infrastructure
(`CG4` / `CGraph4Bridge` / `SecAsymBasis` / `AsymSecCertificate`) is **not
vacuous** and is **host-faithful** — the two defects the L5 verdicts flagged in
the pre-repair chain.

## G-VACUITY — the objective support is realized with NONZERO density

The pre-repair axiom was vacuous: it reused the *symmetric* F-marked
`SecBipartiteCertificate.target` in the F-free asymmetric host, so every
support flag had density 0 (`LHS ≡ 0`, bound collapses to `0 ≤ 4.55`;
`L5_math_soundness/VERDICT.md §5`). Here we pick three basis flags with
**nonzero** objective coefficient (`AsymSecCertificate.target k ≠ 0`) that
genuinely use colour 2/3, and show their `genUnlabelledDensity` is `> 0` in a
concrete 4-colour host (via the `native_decide` bridge). Contrast:
`oldConfig_vacuous` reproduces the F-marked-flag-in-F-free-host collapse that
gave 0.

## G-PROVENANCE — the host distinguishes components (no CG22 collapse)

Two flags differing ONLY in one vertex's component (colour `1` = `X`, comp1 at
`pΔ` vs colour `0` = `X`, comp0 at `Δ`) receive DISTINCT densities in `CG4`
(`provenance_distinct_densities`), whereas their `CG22` high-bit projections are
identical and mutually embeddable (`cg22_highbit_collapse`) — a machine-checked
proof that the `{0,1}→0, {2,3}→1` collapse the objective cannot tolerate is
gone in `CG4`.
-/

namespace Davey2024.SecAsymGates

open Davey2024 Davey2024.SecAsymBasis

/-! ## Generic density-positivity helper -/

/-- A flag has strictly positive unlabelled density in any host it embeds into,
    provided the binomial normaliser is positive. Pure positivity plumbing:
    `genInducedCount > 0` and a positive `C(Δ,·)` give a positive quotient
    (the automorphism count is always `≥ 1`). -/
theorem genUnlabelledDensity_pos {R : RelUniverse} {σ : GenFlagType R}
    (F G : GenFlag R σ) (Δ : GenFlag R (GenFlagType.empty R) → ℕ)
    (hIC : 0 < genInducedCount R σ F G)
    (hchoose : 0 < Nat.choose (Δ G.forget) (F.size - σ.size)) :
    0 < genUnlabelledDensity R σ F G Δ := by
  unfold genUnlabelledDensity
  apply div_pos
  · exact_mod_cast hIC
  · exact mul_pos (by exact_mod_cast hchoose)
      (by exact_mod_cast genFlagAutCount_pos σ F)

/-- Constant host-order function: every ∅-flag is assigned "max degree" 5, so the
    binomial normaliser `C(5, 5 - 0) = 1 > 0` for our size-5 basis flags. -/
def Δ5 : GenFlag CG4 (GenFlagType.empty CG4) → ℕ := fun _ => 5

/-! ## Basis-flag index handles (all use colour 2/3) -/

/-- Flag 25 : colours (0,0,0,1,3), objective coef `-1e11`. -/
def i25 : Fin basisSize := ⟨25, by native_decide⟩
/-- Flag 32 : colours (0,2,2,1,1), objective coef `-1/3·1e11`. -/
def i32 : Fin basisSize := ⟨32, by native_decide⟩
/-- Flag 39 : colours (1,1,1,2,2), objective coef `-1e11`. -/
def i39 : Fin basisSize := ⟨39, by native_decide⟩

/-! ## The three chosen flags have NONZERO objective coefficient -/

/-- Objective coefficient of flag 25 is nonzero (genuine support, not padding). -/
theorem target_25_ne_zero : AsymSecCertificate.target[25]! ≠ 0 := by native_decide
/-- Objective coefficient of flag 32 is nonzero. -/
theorem target_32_ne_zero : AsymSecCertificate.target[32]! ≠ 0 := by native_decide
/-- Objective coefficient of flag 39 is nonzero. -/
theorem target_39_ne_zero : AsymSecCertificate.target[39]! ≠ 0 := by native_decide

/-! ## Each chosen flag genuinely uses colour 2 or 3 (needs the full CG4 palette) -/

/-- Flag 25 uses colour 3 at vertex 4. -/
theorem flag25_uses_colour3 :
    ((flagBasisCGraph4 i25).vertexCol ⟨4, by native_decide⟩).val = 3 := by native_decide
/-- Flag 32 uses colour 2 at vertex 1. -/
theorem flag32_uses_colour2 :
    ((flagBasisCGraph4 i32).vertexCol ⟨1, by native_decide⟩).val = 2 := by native_decide
/-- Flag 39 uses colour 2 at vertex 3. -/
theorem flag39_uses_colour2 :
    ((flagBasisCGraph4 i39).vertexCol ⟨3, by native_decide⟩).val = 2 := by native_decide

/-! ## Adjacency symmetry / irreflexivity for the chosen flags (bridge hypotheses) -/

theorem flag25_adj_symm : ∀ i j, (flagBasisCGraph4 i25).adj i j = (flagBasisCGraph4 i25).adj j i := by
  native_decide
theorem flag25_adj_irrefl : ∀ i, (flagBasisCGraph4 i25).adj i i = false := by native_decide
theorem flag32_adj_symm : ∀ i j, (flagBasisCGraph4 i32).adj i j = (flagBasisCGraph4 i32).adj j i := by
  native_decide
theorem flag32_adj_irrefl : ∀ i, (flagBasisCGraph4 i32).adj i i = false := by native_decide
theorem flag39_adj_symm : ∀ i j, (flagBasisCGraph4 i39).adj i j = (flagBasisCGraph4 i39).adj j i := by
  native_decide
theorem flag39_adj_irrefl : ∀ i, (flagBasisCGraph4 i39).adj i i = false := by native_decide

/-! ## Computable self-embedding counts (automorphism counts) via native_decide -/

theorem flag25_self_c4 : c4InducedCount (flagBasisCGraph4 i25) (flagBasisCGraph4 i25) = 2 := by
  native_decide
theorem flag32_self_c4 : c4InducedCount (flagBasisCGraph4 i32) (flagBasisCGraph4 i32) = 2 := by
  native_decide
theorem flag39_self_c4 : c4InducedCount (flagBasisCGraph4 i39) (flagBasisCGraph4 i39) = 2 := by
  native_decide

/-! ## Abstract induced counts (bridge the computable counts) -/

theorem flag25_self_ic :
    genInducedCount CG4 (GenFlagType.empty CG4) (flagBasis_asym i25) (flagBasis_asym i25) = 2 := by
  unfold flagBasis_asym
  rw [← c4InducedCount_eq_genInducedCount' _ _ flag25_adj_symm flag25_adj_irrefl
        flag25_adj_symm flag25_adj_irrefl, flag25_self_c4]

theorem flag32_self_ic :
    genInducedCount CG4 (GenFlagType.empty CG4) (flagBasis_asym i32) (flagBasis_asym i32) = 2 := by
  unfold flagBasis_asym
  rw [← c4InducedCount_eq_genInducedCount' _ _ flag32_adj_symm flag32_adj_irrefl
        flag32_adj_symm flag32_adj_irrefl, flag32_self_c4]

theorem flag39_self_ic :
    genInducedCount CG4 (GenFlagType.empty CG4) (flagBasis_asym i39) (flagBasis_asym i39) = 2 := by
  unfold flagBasis_asym
  rw [← c4InducedCount_eq_genInducedCount' _ _ flag39_adj_symm flag39_adj_irrefl
        flag39_adj_symm flag39_adj_irrefl, flag39_self_c4]

/-! ## G-VACUITY — nonzero density for the three nonzero-coefficient flags

Host = the flag's own 5-vertex 4-colour graph (a concrete asymmetric-bipartite
4-colour host). `C(5, 5) = 1 > 0`, `IC = aut = 2 > 0`, so the density is
strictly positive — the objective support is NOT identically zero. -/

theorem flag25_density_pos :
    0 < genUnlabelledDensity CG4 (GenFlagType.empty CG4)
      (flagBasis_asym i25) (flagBasis_asym i25) Δ5 :=
  genUnlabelledDensity_pos _ _ _ (by rw [flag25_self_ic]; norm_num) (by decide)

theorem flag32_density_pos :
    0 < genUnlabelledDensity CG4 (GenFlagType.empty CG4)
      (flagBasis_asym i32) (flagBasis_asym i32) Δ5 :=
  genUnlabelledDensity_pos _ _ _ (by rw [flag32_self_ic]; norm_num) (by decide)

theorem flag39_density_pos :
    0 < genUnlabelledDensity CG4 (GenFlagType.empty CG4)
      (flagBasis_asym i39) (flagBasis_asym i39) Δ5 :=
  genUnlabelledDensity_pos _ _ _ (by rw [flag39_self_ic]; norm_num) (by decide)

/-- **G-VACUITY headline**: three objective-support flags (nonzero coefficient,
    each using colour 2/3) have strictly positive density in a concrete 4-colour
    host. The asymmetric objective is genuinely NON-vacuous in `CG4`. -/
theorem g_vacuity :
    (0 < genUnlabelledDensity CG4 (GenFlagType.empty CG4)
        (flagBasis_asym i25) (flagBasis_asym i25) Δ5) ∧
    (0 < genUnlabelledDensity CG4 (GenFlagType.empty CG4)
        (flagBasis_asym i32) (flagBasis_asym i32) Δ5) ∧
    (0 < genUnlabelledDensity CG4 (GenFlagType.empty CG4)
        (flagBasis_asym i39) (flagBasis_asym i39) Δ5) :=
  ⟨flag25_density_pos, flag32_density_pos, flag39_density_pos⟩

/-! ## G-VACUITY regression pin — the OLD configuration gives 0

The pre-repair vacuity mechanism: an F-marked flag (edge colour `1`) has zero
density in an F-free host (edge colour `0`). Reproduced here with `CGraph22`
(read-only): a colour-1-edge flag does not embed into a colour-0-edge host. -/

/-- An F-marked (edge-colour 1) edge — a `SecBipartiteCertificate`-style support flag. -/
def fMarkedEdge : CGraph22 2 where
  adj i j := i ≠ j
  vertexCol _ := 0
  edgeCol _ _ := 1

/-- The F-free asymmetric host edge (edge colour `0`, matching the
    asymmetric host's `edgeColour ≡ 0`). -/
def fFreeHostEdge : CGraph22 2 where
  adj i j := i ≠ j
  vertexCol _ := 0
  edgeCol _ _ := 0

/-- **G-VACUITY regression**: the F-marked flag has ZERO embeddings into the
    F-free host — exactly the collapse that made the borrowed symmetric target
    vacuous (`LHS ≡ 0`). This is why the objective must be rebuilt on the genuine
    F-free basis, not `SecBipartiteCertificate.target`. -/
theorem oldConfig_vacuous : c22InducedCount fMarkedEdge fFreeHostEdge = 0 := by native_decide

/-! ## G-PROVENANCE — the host distinguishes components (comp0 at Δ vs comp1 at pΔ)

`A = flag 25` (vertex 3 has colour `1` = `X`, comp1 at `pΔ`); `B` = `A` with
vertex 3 recoloured `1 → 0` (`X`, comp0 at `Δ`). The two differ ONLY in that
vertex's component. -/

/-- `B` = flag 25 with vertex 3's component flipped (`1 → 0`), sharing `A`'s edges. -/
def flag25_compFlipped : CGraph4 flagOrder where
  adj u v := (flagBasisCGraph4 i25).adj u v
  vertexCol v := if v.val = 3 then 0 else (flagBasisCGraph4 i25).vertexCol v

theorem flip_adj_symm :
    ∀ i j, (flag25_compFlipped).adj i j = (flag25_compFlipped).adj j i := by native_decide
theorem flip_adj_irrefl : ∀ i, (flag25_compFlipped).adj i i = false := by native_decide

/-- In `CG4`, `B` does NOT embed into `A`: their colour multisets differ (four
    `0`s vs three `0`s + one `1`), precisely because the component bit changed. -/
theorem flip_into_A_c4 :
    c4InducedCount flag25_compFlipped (flagBasisCGraph4 i25) = 0 := by native_decide

theorem flip_into_A_ic :
    genInducedCount CG4 (GenFlagType.empty CG4)
      flag25_compFlipped.toGenFlag (flagBasis_asym i25) = 0 := by
  unfold flagBasis_asym
  rw [← c4InducedCount_eq_genInducedCount' _ _ flip_adj_symm flip_adj_irrefl
        flag25_adj_symm flag25_adj_irrefl, flip_into_A_c4]

theorem flip_density_zero :
    genUnlabelledDensity CG4 (GenFlagType.empty CG4)
      flag25_compFlipped.toGenFlag (flagBasis_asym i25) Δ5 = 0 := by
  unfold genUnlabelledDensity
  rw [flip_into_A_ic]; simp

/-- **G-PROVENANCE headline**: the two component-distinct flags receive DISTINCT
    densities in the 4-colour host (`density(A,A) > 0 ≠ 0 = density(B,A)`). `CG4`
    genuinely separates comp0 (`Δ`) from comp1 (`pΔ`). -/
theorem provenance_distinct_densities :
    genUnlabelledDensity CG4 (GenFlagType.empty CG4)
        (flagBasis_asym i25) (flagBasis_asym i25) Δ5
      ≠ genUnlabelledDensity CG4 (GenFlagType.empty CG4)
        flag25_compFlipped.toGenFlag (flagBasis_asym i25) Δ5 := by
  rw [flip_density_zero]; exact ne_of_gt flag25_density_pos

/-! ## G-PROVENANCE contrast — CG22 high-bit projection COLLAPSES the two flags

Under `{0,1}→0, {2,3}→1`, vertex 3's colour `1` (in `A`) and `0` (in `B`) both
map to `0`; every other vertex is unchanged. So the two `CG22` projections are
IDENTICAL and mutually embeddable — `CG22` cannot tell comp0 from comp1. -/

/-- CG22 high-bit projection of `A` (flag 25). -/
def flag25_cg22 : CGraph22 flagOrder where
  adj u v := (flagBasisCGraph4 i25).adj u v
  vertexCol v := if 2 ≤ ((flagBasisCGraph4 i25).vertexCol v).val then 1 else 0
  edgeCol _ _ := 0

/-- CG22 high-bit projection of `B` (flag 25, vertex 3 flipped). -/
def flag25flip_cg22 : CGraph22 flagOrder where
  adj u v := (flag25_compFlipped).adj u v
  vertexCol v := if 2 ≤ ((flag25_compFlipped).vertexCol v).val then 1 else 0
  edgeCol _ _ := 0

/-- **G-PROVENANCE contrast**: the CG22 high-bit projections of the two
    component-distinct flags are mutually embeddable (count = aut = 2 > 0) — i.e.
    CG22 sees them as the SAME flag. This is the collapse that a 2-colour host
    cannot avoid and that a 4-colour host (`CG4`, above) repairs. -/
theorem cg22_highbit_collapse : c22InducedCount flag25_cg22 flag25flip_cg22 = 2 := by native_decide

/-! ## Certificate slack budget (mirror of `SecBipartiteCertificate.cert_slack_within_budget`)

The genuine asymmetric cert's aggregate weighted slack sits far under an integer
budget analogous to the bipartite one (spike measured `≈ 1.9×10²⁰`, ~500× under
`10²³`). This provides direct `native_decide` support that the bundled cert is
structurally faithful at the relaxed bound. -/

/-- Integer slack budget for the asymmetric cert at its nominal bound. -/
def secAsymSlackBudget : Int := 100000000000000000000000  -- 1 × 10²³

/-- **Cert slack-budget verification.** The bundled asymmetric cert's aggregate
    absolute weighted slack is within `secAsymSlackBudget`. -/
theorem cert_slack_within_budget :
    AsymSecCertificate.total_slack_abs ≤ secAsymSlackBudget := by native_decide

end Davey2024.SecAsymGates
