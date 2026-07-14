import DaveyThesis2024.Basic
import DaveyThesis2024.FlagIso
import DaveyThesis2024.LocalFlagAlgebra

/-!
# `CG4`: the 4-vertex-colour, plain-edge graph `RelUniverse`

This file defines a `RelUniverse` for **plain graphs with a 4-valued vertex
colouring** (and *no* edge colour). It is the host universe for the
**asymmetric** strong-edge-colouring chain (Davey thesis §4.6, the F-free
all-vertex Molloy–Reed route).

## Why a new universe?

The asymmetric-bipartite SEC problem is generated in Rust as
`type G = Colored<Graph, 4>` (see
`local-flags-certificates/examples/asymmetric_bipartite_strong_density.rs`):
plain (uncoloured) edges together with **four** vertex colours with semantics

  * `COMP = [0, 1, 0, 1]`  — colours `{0, 2}` = component 0 (degree `Δ`),
    colours `{1, 3}` = component 1 (degree `pΔ`);
  * `X_COLS = {0, 1}`, `Y_COLS = {2, 3}` — the fixed-edge-neighbourhood marks.

The existing `CG22` universe (`CG22.lean`) has only `Fin 2` vertex colours plus
an edge colour. Projecting the four colours down to two via the high bit
(`{0,1} → 0`, `{2,3} → 1`) collapses `X`/`Y` correctly but **loses the
component bit** (comp0 at `Δ` vs comp1 at `pΔ`), which the asymmetric objective
depends on (296/334 basis flags use colour 2 or 3). So a genuine 4-colour host
is required. Because the edges are plain, `CG4` is *simpler* than `CG22` — it
drops the third (edge-colour) product factor.

## Design

`CG4.Str n := SimpleGraph (Fin n) × (Fin n → Fin 4)`.

Two product factors:
1. Underlying simple graph (plain edges).
2. Vertex colouring `Fin n → Fin 4` (raw Rust colour 0–3, no projection).

`comap f s = ⟨s.1.comap f, s.2 ∘ f⟩` — pull each component back through `f`,
mirroring `colouredGraphUniverse` and `colouredGraphUniverse22`.

## Compatibility

Because `GenFlag R σ`, `GenFlagIso`, `GenFlagAlg R σ`, `genFlagAutCount R σ`,
`genUnlabelledDensity`, etc. are all parameterised over an arbitrary
`RelUniverse R`, the entire flag-algebra machinery applies generically to `CG4`.
No new infrastructure is required at the abstract level — only this
`RelUniverse` instance plus an optional `CGraph4` computable bridge for
`native_decide` workflows (`CGraph4Bridge.lean`).
-/

namespace Davey2024

open Finset

/-! ## The CG4 RelUniverse -/

/-- The **4-vertex-colour plain-edge graph universe**: structures are a
    `SimpleGraph` plus a vertex colouring `Fin n → Fin 4` (raw Rust colour,
    no projection). Pullback acts on each component. Analog of `CG22` minus
    the edge-colour factor. -/
noncomputable def colouredGraphUniverse4 : RelUniverse where
  Str n := SimpleGraph (Fin n) × (Fin n → Fin 4)
  instFintype _ := inferInstance
  instDecEq _ := Classical.decEq _
  comap f s := ⟨s.1.comap f, s.2 ∘ f⟩
  comap_id s := by
    ext1
    · simp [SimpleGraph.comap]
    · rfl
  comap_comp f g s := by
    ext1
    · simp [SimpleGraph.comap, Function.comp]
    · rfl
  empty := ⟨⊥, Fin.elim0⟩
  comap_elim0 f _ := by
    ext1
    · ext u; exact Fin.elim0 u
    · exact Subsingleton.elim _ _

/-- The 4-vertex-colour plain-edge relational universe. Host for the
    asymmetric SEC chain. -/
noncomputable abbrev CG4 : RelUniverse := colouredGraphUniverse4

/-! ## CG4 structural lemmas -/

/-- Unfolding lemma: `CG4.Str n` is a pair. -/
@[simp] theorem CG4_Str (n : ℕ) :
    CG4.Str n = (SimpleGraph (Fin n) × (Fin n → Fin 4)) := rfl

/-- Unfolding lemma: `CG4.comap f s` projects each component. -/
theorem CG4_comap {m n : ℕ} (f : Fin m → Fin n) (s : CG4.Str n) :
    CG4.comap f s = ⟨s.1.comap f, s.2 ∘ f⟩ := rfl

/-- The empty CG4 structure on `Fin 0`.

    **Status**: Intentional standalone — foundational fact about `CG4.empty`;
    no consumer expected. -/
theorem CG4_empty : CG4.empty = (⟨⊥, Fin.elim0⟩ : CG4.Str 0) := rfl

/-- A CG4 structure equality factors through the two components. -/
theorem CG4_str_ext {n : ℕ} {s t : CG4.Str n}
    (h1 : s.1 = t.1) (h2 : s.2 = t.2) : s = t :=
  Prod.ext h1 h2

/-! ## Convenience: smoke-test instances

`GenFlagIso`, `GenFlagClass`, `genFlagAutCount`, etc. are defined generically
over an arbitrary `RelUniverse`, so they apply to `CG4` automatically. Below we
instantiate a few of the generic facts at `CG4` to confirm elaboration succeeds
(no missing instances). -/

/-- The empty `GenFlag CG4 (GenFlagType.empty CG4)`. -/
noncomputable def CG4.emptyFlag : GenFlag CG4 (GenFlagType.empty CG4) :=
  (GenFlagType.empty CG4).toFlag

@[simp] theorem CG4.emptyFlag_size : CG4.emptyFlag.size = 0 := rfl

/-- The empty `GenFlagAlg CG4 (GenFlagType.empty CG4)`. -/
noncomputable def CG4.emptyAlg : GenFlagAlg CG4 (GenFlagType.empty CG4) :=
  GenFlagAlg.single CG4.emptyFlag

/-- `genFlagAutCount` at the empty CG4 type/flag is `1`. -/
example : genFlagAutCount CG4 (GenFlagType.empty CG4)
    (GenFlagType.empty CG4).toFlag = 1 :=
  genFlagAutCount_toFlag _

/-- The empty CG4 flag has positive automorphism count. -/
example : 0 < genFlagAutCount CG4 (GenFlagType.empty CG4) (GenFlagType.empty CG4).toFlag :=
  genFlagAutCount_pos _ _

/-- `GenFlagIso` is reflexive on CG4 flags. -/
example : GenFlagIso (GenFlagType.empty CG4)
    (GenFlagType.empty CG4).toFlag (GenFlagType.empty CG4).toFlag :=
  GenFlagIso.refl _ _

/-- `GenFlagClass.mk` produces a class on CG4. -/
noncomputable example : GenFlagClass CG4 (GenFlagType.empty CG4) :=
  GenFlagClass.mk (GenFlagType.empty CG4).toFlag

end Davey2024
