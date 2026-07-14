import DaveyThesis2024.Basic
import DaveyThesis2024.FlagIso
import DaveyThesis2024.LocalFlagAlgebra

/-!
# `CG22`: the (2,2)-coloured graph `RelUniverse`

This file defines a `RelUniverse` for graphs with both vertex colourings and
edge colourings drawn from `Fin 2`. It is the SEC (strong edge colouring)
analog of `CG2 := colouredGraphUniverse 2` used in Pentagon Q.

## Why a new universe?

`StrongEdgeColouring.lean:404` introduces `ColouredGraph22`: a `SimpleGraph`
together with `vertexColour : Fin n → Fin 2` AND `edgeColour : Fin n → Fin n → Fin 2`
(with edge-colour symmetry). The reduction Davey uses (Thesis §4.3) routes through
this 2-component structure. Pentagon Q's `CG2` only carries a vertex colour,
so the SEC bridge cannot reuse `GenFlag CG2 σ` — the bridge needs a `RelUniverse`
whose `Str n` carries both colourings.

## Design

`CG22.Str n := SimpleGraph (Fin n) × (Fin n → Fin 2) × (Fin n → Fin n → Fin 2)`.

Three product factors:
1. Underlying simple graph (analogous to `CG2`'s first factor).
2. Vertex colouring `Fin n → Fin 2` (red=0, black=1 by SEC convention).
3. Edge colouring `Fin n → Fin n → Fin 2` (red=0, black=1).

Edge-colour symmetry (`edgeCol u v = edgeCol v u`) is **not** an invariant of the
`Str` itself; it is carried as a side hypothesis by structures that need it
(e.g. `CGraph22`'s bridge theorem mirrors `CGraph`'s `cInducedCount_eq_genInducedCount'`
which carries `hFs`/`hGs` symmetry hypotheses). This keeps `Fintype` and `DecidableEq`
free from `inferInstance` and pullback definitions clean.

## Comap

`comap f s = ⟨s.1.comap f, s.2.1 ∘ f, fun u v => s.2.2 (f u) (f v)⟩` —
pull each component back through `f`, exactly mirroring `colouredGraphUniverse`.

## Compatibility with the rest of the codebase

Because `GenFlag R σ`, `GenFlagIso`, `GenFlagAlg R σ`, `genFlagAutCount R σ`,
etc. are all parameterised over an arbitrary `RelUniverse R`, the entire flag
algebra machinery applies generically to `CG22`. No new infrastructure is
required at the abstract level — only this `RelUniverse` instance plus an
optional `CGraph22` computable bridge for `native_decide` workflows.
-/

namespace Davey2024

open Finset

/-! ## The CG22 RelUniverse -/

/-- The **(2,2)-coloured graph universe**: structures are a `SimpleGraph` plus a
    vertex colouring `Fin n → Fin 2` plus an edge colouring
    `Fin n → Fin n → Fin 2`. Pullback acts on each component. -/
noncomputable def colouredGraphUniverse22 : RelUniverse where
  Str n := SimpleGraph (Fin n) × (Fin n → Fin 2) × (Fin n → Fin n → Fin 2)
  instFintype _ := inferInstance
  instDecEq _ := Classical.decEq _
  comap f s := ⟨s.1.comap f, s.2.1 ∘ f, fun u v => s.2.2 (f u) (f v)⟩
  comap_id s := by
    -- Product of three pullbacks; each component reduces by `id`.
    ext1
    · simp [SimpleGraph.comap]
    · rfl
  comap_comp f g s := by
    ext1
    · simp [SimpleGraph.comap, Function.comp]
    · rfl
  empty := ⟨⊥, Fin.elim0, fun u _ => Fin.elim0 u⟩
  comap_elim0 f _ := by
    -- All three components vanish on `Fin 0`.
    ext1
    · ext u; exact Fin.elim0 u
    · exact Subsingleton.elim _ _

/-- The (2,2)-coloured graph relational universe. SEC analog of Pentagon Q's `CG2`. -/
noncomputable abbrev CG22 : RelUniverse := colouredGraphUniverse22

/-! ## CG22 structural lemmas -/

/-- Unfolding lemma: `CG22.Str n` is a 3-tuple. -/
@[simp] theorem CG22_Str (n : ℕ) :
    CG22.Str n = (SimpleGraph (Fin n) × (Fin n → Fin 2) × (Fin n → Fin n → Fin 2)) := rfl

/-- Unfolding lemma: `CG22.comap f s` projects each component. -/
theorem CG22_comap {m n : ℕ} (f : Fin m → Fin n) (s : CG22.Str n) :
    CG22.comap f s = ⟨s.1.comap f, s.2.1 ∘ f, fun u v => s.2.2 (f u) (f v)⟩ := rfl

/-- The empty CG22 structure on `Fin 0`.

    **Status**: Intentional standalone — foundational fact about
    `CG22.empty`; no consumer expected. -/
theorem CG22_empty : CG22.empty = (⟨⊥, Fin.elim0, fun u _ => Fin.elim0 u⟩ : CG22.Str 0) := rfl

/-- A CG22 structure equality factors through the three components. -/
theorem CG22_str_ext {n : ℕ} {s t : CG22.Str n}
    (h1 : s.1 = t.1) (h2 : s.2.1 = t.2.1) (h3 : s.2.2 = t.2.2) : s = t :=
  Prod.ext h1 (Prod.ext h2 h3)

/-! ## Convenience: smoke-test instance

A trivial example: the (2,2)-coloured `Fin 0` structure as a `GenFlag CG22 ∅`. -/

/-- The empty `GenFlag CG22 (GenFlagType.empty CG22)`. -/
noncomputable def CG22.emptyFlag : GenFlag CG22 (GenFlagType.empty CG22) :=
  (GenFlagType.empty CG22).toFlag

@[simp] theorem CG22.emptyFlag_size : CG22.emptyFlag.size = 0 := rfl

/-- The empty `GenFlagAlg CG22 (GenFlagType.empty CG22)`. -/
noncomputable def CG22.emptyAlg : GenFlagAlg CG22 (GenFlagType.empty CG22) :=
  GenFlagAlg.single CG22.emptyFlag

/-! ## Iso / aut machinery — smoke tests

`GenFlagIso`, `GenFlagClass`, `genFlagAutCount`, etc. are defined generically
over an arbitrary `RelUniverse`, so they apply to `CG22` automatically.
Below we instantiate a few of the generic facts at `CG22` to confirm
elaboration succeeds (no missing instances). -/

/-- `genFlagAutCount` at the empty CG22 type/flag is `1`. -/
example : genFlagAutCount CG22 (GenFlagType.empty CG22)
    (GenFlagType.empty CG22).toFlag = 1 :=
  genFlagAutCount_toFlag _

/-- The empty CG22 flag has positive automorphism count. -/
example : 0 < genFlagAutCount CG22 (GenFlagType.empty CG22) (GenFlagType.empty CG22).toFlag :=
  genFlagAutCount_pos _ _

/-- `GenFlagIso` is reflexive on CG22 flags. -/
example : GenFlagIso (GenFlagType.empty CG22)
    (GenFlagType.empty CG22).toFlag (GenFlagType.empty CG22).toFlag :=
  GenFlagIso.refl _ _

/-- `GenFlagClass.mk` produces a class on CG22. -/
noncomputable example : GenFlagClass CG22 (GenFlagType.empty CG22) :=
  GenFlagClass.mk (GenFlagType.empty CG22).toFlag

end Davey2024
