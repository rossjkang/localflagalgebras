import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Davey 2024: Local Flag Algebras — Basic Definitions

Core definitions from Chapters 1–2 of Eoin Davey's MSc thesis
"Local Flags: Bounding the Strong Chromatic Index" (UvA, 2024).

The formalization follows the thesis structure closely:
* §1.1: Types, σ-flags, induced counts & densities (from classic flag algebras)
* §2.1: Local density, label extensions, hereditary closure, local flags, local types

## Main definitions

* `FlagType` — a type σ: a graph on vertex set `Fin k` (Def 1.1)
* `Flag σ` — a σ-flag: a graph with a σ-embedding θ (Def 1.3)
* `SigmaEmbedding` — σ-compatible induced embeddings (for counting)
* `inducedCount` — c(F; G), the induced count (Def 1.4)
* `inducedDensity` — p(F; G) = c(F;G) / C(|G|-|σ|, |F|-|σ|) (Def 1.5)
* `localDensity` — ρ(F; G) = c(F;G) / C(Δ(G), |F|-|σ|) (§2.1 Def)
* `LabelExtension` — label extension θ → θ' (§2.1 Def)
* `HereditaryClosure` — 𝒢̄, closure under induced subgraphs (§2.1 Def)
* `IsBoundedDensity` — ρ(F;·) is bounded on 𝒢^σ (Def 2.4(a))
* `IsLocalFlag` — bounded density + all extensions also local (Def 2.4)
* `IsLocalType` — σ is a local type (Def 2.8)

## References

* E. Davey, "Local Flags: Bounding the Strong Chromatic Index", MSc thesis, UvA, 2024.
* A. Razborov, "Flag Algebras", Journal of Symbolic Logic 72(4), 2007.
-/

open Finset BigOperators Nat

set_option linter.unusedSectionVars false

namespace Davey2024

/-! ## Relational Universe

A `RelUniverse` specifies a type of finite relational structure (plain graphs,
coloured graphs, digraphs, etc.). The flag algebra machinery is generic over
the universe: the same definitions and theorems apply to any instance.

Currently the codebase uses `SimpleGraph` directly. The `RelUniverse` abstraction
is defined here for future generalization; the `simpleGraphUniverse` instance
recovers the current `SimpleGraph`-based code. -/

/-- A **relational universe** specifies what "structure on `Fin n`" means.

    The single operation `comap` (pullback through a function) replaces all
    structure-specific code:
    * Induced embeddings: `f : Fin m → Fin n` is induced iff `comap f target = source`
    * Isomorphisms: `φ : Fin n ≃ Fin n` is an iso iff `comap φ s = t`
    * Label extensions: `extendedType.str = comap vertexMap F.str`
    * Induced subflags: `subflag.str = comap inclusion G.str`

    Each instance must provide `Fintype` and `DecidableEq` for enumeration
    (needed by `classesOfSize` in the flag algebra). -/
structure RelUniverse where
  /-- The type of structures on vertex set `Fin n`. -/
  Str : (n : ℕ) → Type
  /-- Every `Str n` is a `Fintype` (needed for flag class enumeration). -/
  instFintype : ∀ n, Fintype (Str n)
  /-- Every `Str n` has `DecidableEq`. -/
  instDecEq : ∀ n, DecidableEq (Str n)
  /-- Pullback a structure through a function. -/
  comap : {m n : ℕ} → (Fin m → Fin n) → Str n → Str m
  /-- Pullback through identity is identity. -/
  comap_id : ∀ {n} (s : Str n), comap id s = s
  /-- Pullback respects composition. -/
  comap_comp : ∀ {a b c} (f : Fin a → Fin b) (g : Fin b → Fin c) (s : Str c),
    comap (g ∘ f) s = comap f (comap g s)
  /-- The unique structure on the empty vertex set. -/
  empty : Str 0
  /-- Pullback through any function from `Fin 0` gives the empty structure. -/
  comap_elim0 : ∀ {n} (f : Fin 0 → Fin n) (s : Str n), comap f s = empty

/-- The **simple graph universe**: structures are `SimpleGraph (Fin n)`,
    pullback is `SimpleGraph.comap`. This recovers the current formalization. -/
noncomputable def simpleGraphUniverse : RelUniverse where
  Str n := SimpleGraph (Fin n)
  instFintype _ := inferInstance
  instDecEq _ := Classical.decEq _
  comap f g := g.comap f
  comap_id g := by ext u v; simp [SimpleGraph.comap]
  comap_comp f g s := by ext u v; simp [SimpleGraph.comap, Function.comp]
  empty := ⊥
  comap_elim0 f _ := by ext u; exact Fin.elim0 u

/-- The **2-coloured graph universe**: structures are a `SimpleGraph` plus a
    vertex colouring `Fin n → Fin k`. Pullback acts on both components. -/
noncomputable def colouredGraphUniverse (k : ℕ) : RelUniverse where
  Str n := SimpleGraph (Fin n) × (Fin n → Fin k)
  instFintype _ := inferInstance
  instDecEq _ := Classical.decEq _
  comap f s := ⟨s.1.comap f, s.2 ∘ f⟩
  comap_id s := by ext <;> simp [SimpleGraph.comap]
  comap_comp f h s := by ext <;> simp [SimpleGraph.comap, Function.comp]
  empty := ⟨⊥, Fin.elim0⟩
  comap_elim0 f _ := by
    ext u
    · exact Fin.elim0 u
    · exact Fin.elim0 u

/-! ## Generic Flag Algebra Types

Generic versions of the flag algebra types parameterized by `RelUniverse`.
These generalize the `SimpleGraph`-specific types defined below. -/

/-- A generic flag type: a size and a structure from the universe. -/
structure GenFlagType (R : RelUniverse) where
  size : ℕ
  str : R.Str size

/-- A generic flag: a structure with an embedding from the type.
    The embedding is an injection `Fin σ.size ↪ Fin size` such that
    pulling back the flag's structure gives the type's structure. -/
structure GenFlag (R : RelUniverse) (σ : GenFlagType R) where
  size : ℕ
  str : R.Str size
  embedding : Fin σ.size ↪ Fin size
  isInduced : R.comap embedding str = σ.str
  hsize : σ.size ≤ size

/-- A generic induced embedding: an injective function that pulls back
    the target structure to the source structure, compatible with σ-embeddings. -/
structure GenInducedEmbedding (R : RelUniverse) (σ : GenFlagType R)
    (F G : GenFlag R σ) where
  toFun : Fin F.size → Fin G.size
  injective : Function.Injective toFun
  isInduced : R.comap toFun G.str = F.str
  compat : ∀ i : Fin σ.size, toFun (F.embedding i) = G.embedding i

/-- The empty generic flag type (size 0, empty structure). -/
def GenFlagType.empty (R : RelUniverse) : GenFlagType R := ⟨0, R.empty⟩

/-- View a generic flag type σ as a σ-flag via the identity embedding. -/
def GenFlagType.toFlag {R : RelUniverse} (σ : GenFlagType R) : GenFlag R σ where
  size := σ.size
  str := σ.str
  embedding := Function.Embedding.refl _
  isInduced := R.comap_id σ.str
  hsize := le_refl _

/-- For SimpleGraph universe: `comap f G = F` iff adjacency is reflected.

    **Status**: Intentional standalone — foundational `RelUniverse` fact;
    no consumer expected. -/
theorem simpleGraph_comap_eq_iff {m n : ℕ} (f : Fin m → Fin n)
    (F : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n)) :
    simpleGraphUniverse.comap f G = F ↔
      (∀ u v, F.Adj u v ↔ G.Adj (f u) (f v)) := by
  constructor
  · intro h; subst h; intro u v; simp [simpleGraphUniverse, SimpleGraph.comap]
  · intro h
    change SimpleGraph.comap f G = F
    ext u v; exact (h u v).symm

/-- Composition of generic induced embeddings. -/
def GenInducedEmbedding.comp {R : RelUniverse} {σ : GenFlagType R} {F H G : GenFlag R σ}
    (ι : GenInducedEmbedding R σ H G) (e : GenInducedEmbedding R σ F H) :
    GenInducedEmbedding R σ F G where
  toFun := ι.toFun ∘ e.toFun
  injective := ι.injective.comp e.injective
  isInduced := by rw [R.comap_comp, ι.isInduced, e.isInduced]
  compat i := by simp [Function.comp, e.compat, ι.compat]

noncomputable instance (R : RelUniverse) (σ : GenFlagType R) (F G : GenFlag R σ) :
    Fintype (GenInducedEmbedding R σ F G) :=
  Fintype.ofInjective (fun e => e.toFun) (fun a b h => by
    cases a; cases b; simp only [GenInducedEmbedding.mk.injEq] at h ⊢; exact h)

/-- Generic induced count: the number of induced embeddings from F into G. -/
noncomputable def genInducedCount (R : RelUniverse) (σ : GenFlagType R)
    (F G : GenFlag R σ) : ℕ :=
  Fintype.card (GenInducedEmbedding R σ F G)

/-! ## §1.1: Types and Flags

From the classic flag algebras (Razborov 2007), adapted following the thesis Ch 1. -/

/-- A **type** σ of size k is a graph with vertex set [k] = `Fin k`. (Thesis Def 1.1)
    We write |σ| = `σ.size` for the number of vertices. The empty type ∅ has size 0. -/
structure FlagType where
  size : ℕ
  graph : SimpleGraph (Fin size)
  deriving Inhabited

/-- The **empty type** ∅ has size 0 and the empty graph. -/
def emptyType : FlagType := ⟨0, ⊥⟩

/-- A **σ-embedding** θ : [|σ|] → V(F) is an injective function that is a graph
    isomorphism between σ and F[im θ]. We model this as `SimpleGraph.Embedding`
    (= `↪g`), which is an injective function preserving adjacency in both directions.
    (Thesis Def 1.2) -/
abbrev SigmaEmb (σG : SimpleGraph (Fin n)) (FG : SimpleGraph (Fin m)) :=
  σG ↪g FG

/-- A **σ-flag** (F, θ) is a graph F together with a σ-embedding θ into F.
    The embedding θ : σ.graph ↪g F.graph is an induced subgraph embedding,
    mapping labelled vertices of σ injectively into F while preserving both
    adjacency and non-adjacency. (Thesis Def 1.3) -/
structure Flag (σ : FlagType) where
  size : ℕ
  graph : SimpleGraph (Fin size)
  embedding : σ.graph ↪g graph
  hsize : σ.size ≤ size

/-- The number of **unlabelled vertices** of a σ-flag F: |F| - |σ|. -/
def Flag.unlabelledSize {σ : FlagType} (F : Flag σ) : ℕ :=
  F.size - σ.size

/-- View a type σ as a σ-flag via the **identity embedding** id : [|σ|] → [|σ|].
    (Thesis Note after Def 1.3) -/
def FlagType.toFlag (σ : FlagType) : Flag σ where
  size := σ.size
  graph := σ.graph
  embedding := SimpleGraph.Embedding.refl
  hsize := le_refl _

/-- **Downward operator** ↓: forget the labelling of a σ-flag to get an ∅-flag.
    (Thesis Def 1.11) -/
def Flag.forget {σ : FlagType} (F : Flag σ) : Flag emptyType where
  size := F.size
  graph := F.graph
  embedding := ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
  hsize := Nat.zero_le _

/-- The unlabelled size of σ viewed as a σ-flag is 0. -/
@[simp]
theorem FlagType.toFlag_unlabelledSize (σ : FlagType) :
    σ.toFlag.unlabelledSize = 0 := Nat.sub_self σ.size

/-! ### Conversions: SimpleGraph types → generic types -/

/-- Convert a SimpleGraph-based FlagType to a generic one. -/
def FlagType.toGen (σ : FlagType) : GenFlagType simpleGraphUniverse :=
  ⟨σ.size, σ.graph⟩

/-- Convert a SimpleGraph-based Flag to a generic one. -/
noncomputable def Flag.toGen {σ : FlagType} (F : Flag σ) :
    GenFlag simpleGraphUniverse σ.toGen where
  size := F.size
  str := F.graph
  embedding := ⟨F.embedding, F.embedding.injective⟩
  isInduced := by
    change SimpleGraph.comap (⟨F.embedding, F.embedding.injective⟩ : Fin σ.size ↪ Fin F.size)
      F.graph = σ.graph
    ext u v
    simp only [SimpleGraph.comap, Function.Embedding.coeFn_mk]
    exact F.embedding.map_rel_iff'
  hsize := F.hsize

/-- Generic downward operator: forget the labelling. -/
def GenFlag.forget {R : RelUniverse} {σ : GenFlagType R} (F : GenFlag R σ) :
    GenFlag R (GenFlagType.empty R) where
  size := F.size
  str := F.str
  embedding := ⟨Fin.elim0, fun {a} => Fin.elim0 a⟩
  isInduced := R.comap_elim0 _ F.str
  hsize := Nat.zero_le _

/-- The number of unlabelled vertices of a generic flag. -/
def GenFlag.unlabelledSize {R : RelUniverse} {σ : GenFlagType R} (F : GenFlag R σ) : ℕ :=
  F.size - σ.size

/-- The unlabelled size of a type viewed as a flag is 0. -/
@[simp]
theorem GenFlagType.toFlag_unlabelledSize {R : RelUniverse} (σ : GenFlagType R) :
    σ.toFlag.unlabelledSize = 0 := Nat.sub_self σ.size

/-! ## §1.1: Induced Counts and Densities -/

/-- A **σ-compatible induced embedding** of flag F into flag G is an injective function
    f : V(F) → V(G) that is an induced graph isomorphism F ≅ G[im f] and that
    is compatible with the σ-embeddings: f(θ_F(i)) = θ_G(i) for all i ∈ [|σ|].

    The **induced count** c(F; G) is |{such f}|. (Thesis Def 1.4) -/
structure InducedEmbedding (σ : FlagType) (F G : Flag σ) where
  toFun : Fin F.size → Fin G.size
  injective : Function.Injective toFun
  map_adj : ∀ u v, F.graph.Adj u v → G.graph.Adj (toFun u) (toFun v)
  map_non_adj : ∀ u v, u ≠ v → ¬F.graph.Adj u v → ¬G.graph.Adj (toFun u) (toFun v)
  compat : ∀ i : Fin σ.size,
    toFun (F.embedding i) = G.embedding i

/-- The **induced count** c(F; G): number of σ-compatible induced embeddings F ↪ G.
    (Thesis Def 1.4) -/
noncomputable instance (σ : FlagType) (F G : Flag σ) :
    Fintype (InducedEmbedding σ F G) :=
  Fintype.ofInjective (fun e => e.toFun) (fun a b h => by
    cases a; cases b; subst h; rfl)

/-- Composition of two σ-compatible induced embeddings. If `ι : H ↪ G` and `e : F ↪ H`
    are induced embeddings, then `ι ∘ e : F ↪ G` is also an induced embedding. -/
def InducedEmbedding.comp {σ : FlagType} {F H G : Flag σ}
    (ι : InducedEmbedding σ H G) (e : InducedEmbedding σ F H) :
    InducedEmbedding σ F G where
  toFun := ι.toFun ∘ e.toFun
  injective := ι.injective.comp e.injective
  map_adj u v h := ι.map_adj _ _ (e.map_adj _ _ h)
  map_non_adj u v hne hnadj :=
    ι.map_non_adj _ _ (e.injective.ne hne) (e.map_non_adj _ _ hne hnadj)
  compat i := by change ι.toFun (e.toFun (F.embedding i)) = G.embedding i
                 rw [e.compat, ι.compat]

/-- The range of a composed embedding is the ι-image of the range of e. -/
theorem InducedEmbedding.range_comp {σ : FlagType} {F H G : Flag σ}
    (ι : InducedEmbedding σ H G) (e : InducedEmbedding σ F H) :
    Set.range (ι.comp e).toFun = ι.toFun '' Set.range e.toFun :=
  Set.range_comp ι.toFun e.toFun

noncomputable def inducedCount (σ : FlagType) (F G : Flag σ) : ℕ :=
  Fintype.card (InducedEmbedding σ F G)

/-- The **joint count** c(F₁, F₂; G): number of pairs of σ-compatible induced
    embeddings of F₁ and F₂ into G that overlap exactly on im(θ_G) and
    whose images cover all vertices of G (i.e., U ∪ U' = V(G)).
    (Thesis after Def 1.4) -/
noncomputable def jointCount (σ : FlagType) (F₁ F₂ G : Flag σ) : ℕ :=
  Fintype.card
    { p : InducedEmbedding σ F₁ G × InducedEmbedding σ F₂ G //
      (∀ i : Fin G.size,
        (i ∈ Set.range p.1.toFun ∧ i ∈ Set.range p.2.toFun) ↔
          i ∈ Set.range G.embedding) ∧
      (∀ i : Fin G.size,
        i ∈ Set.range p.1.toFun ∨ i ∈ Set.range p.2.toFun) }

/-- The **induced density** p(F; G) = c(F;G) / C(|G|-|σ|, |F|-|σ|).
    This is the classic flag algebra density normalised by the number of
    possible images of the unlabelled vertices. (Thesis Def 1.5) -/
noncomputable def inducedDensity (σ : FlagType) (F G : Flag σ) : ℝ :=
  (inducedCount σ F G : ℝ) / (Nat.choose (G.size - σ.size) (F.size - σ.size) : ℝ)

/-- The **joint induced density** p(F₁, F₂; G) = c(F₁,F₂;G) / multinomial.
    Normalises the joint count by the multinomial coefficient
    C(|G|-|σ|; |F₁|-|σ|, |F₂|-|σ|, R) where R = |G|-|F₁|-|F₂|+|σ|.
    (Thesis Def 1.5, multi-flag version) -/
noncomputable def jointInducedDensity (σ : FlagType) (F₁ F₂ G : Flag σ) : ℝ :=
  (jointCount σ F₁ F₂ G : ℝ) /
    ((Nat.choose (G.size - σ.size) (F₁.size - σ.size) : ℝ) *
     (Nat.choose (G.size - σ.size - (F₁.size - σ.size))
       (F₂.size - σ.size) : ℝ))

/-- The **triple joint count** c(F₁, F₂, F₃; G): number of triples of σ-compatible
    induced embeddings of F₁, F₂, F₃ into G that pairwise overlap exactly on
    im(θ_G) and whose images jointly cover all vertices of G.
    (Thesis after Def 1.4, multi-flag version) -/
noncomputable def tripleJointCount (σ : FlagType) (F₁ F₂ F₃ G : Flag σ) : ℕ :=
  Fintype.card
    { t : InducedEmbedding σ F₁ G × InducedEmbedding σ F₂ G × InducedEmbedding σ F₃ G //
      -- Pairwise overlap exactly on σ-image
      (∀ i : Fin G.size,
        (i ∈ Set.range t.1.toFun ∧ i ∈ Set.range t.2.1.toFun) ↔
          i ∈ Set.range G.embedding) ∧
      (∀ i : Fin G.size,
        (i ∈ Set.range t.1.toFun ∧ i ∈ Set.range t.2.2.toFun) ↔
          i ∈ Set.range G.embedding) ∧
      (∀ i : Fin G.size,
        (i ∈ Set.range t.2.1.toFun ∧ i ∈ Set.range t.2.2.toFun) ↔
          i ∈ Set.range G.embedding) ∧
      -- Joint coverage
      (∀ i : Fin G.size,
        i ∈ Set.range t.1.toFun ∨ i ∈ Set.range t.2.1.toFun ∨
          i ∈ Set.range t.2.2.toFun) }

/-- The **triple joint induced density** p(F₁, F₂, F₃; G).
    Normalised by the trinomial coefficient C(|G|-|σ|; |F₁|-|σ|, |F₂|-|σ|, |F₃|-|σ|). -/
noncomputable def tripleJointInducedDensity (σ : FlagType) (F₁ F₂ F₃ G : Flag σ) : ℝ :=
  (tripleJointCount σ F₁ F₂ F₃ G : ℝ) /
    ((Nat.choose (G.size - σ.size) (F₁.size - σ.size) : ℝ) *
     (Nat.choose (G.size - σ.size - (F₁.size - σ.size)) (F₂.size - σ.size) : ℝ) *
     (Nat.choose (G.size - σ.size - (F₁.size - σ.size) - (F₂.size - σ.size))
       (F₃.size - σ.size) : ℝ))

/-- The joint count is symmetric: `jointCount σ F₁ F₂ G = jointCount σ F₂ F₁ G`.
    This follows by swapping the pair (e₁, e₂) ↦ (e₂, e₁) and using the
    commutativity of ∧ and ∨ in the overlap/covering conditions. -/
theorem jointCount_comm (σ : FlagType) (F₁ F₂ G : Flag σ) :
    jointCount σ F₁ F₂ G = jointCount σ F₂ F₁ G := by
  unfold jointCount
  apply Fintype.card_congr
  refine Equiv.subtypeEquiv (Equiv.prodComm _ _) (fun ⟨e₁, e₂⟩ => ?_)
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  refine ⟨fun ⟨h, c⟩ => ⟨fun i => by rw [and_comm]; exact h i,
                          fun i => by rw [or_comm]; exact c i⟩,
          fun ⟨h, c⟩ => ⟨fun i => by rw [and_comm]; exact h i,
                          fun i => by rw [or_comm]; exact c i⟩⟩

/-- The triple joint count is invariant under cyclic permutation (F₁,F₂,F₃) → (F₂,F₃,F₁).
    The bijection maps (e₁,e₂,e₃) ↦ (e₂,e₃,e₁). -/
theorem tripleJointCount_perm_231 (σ : FlagType) (F₁ F₂ F₃ G : Flag σ) :
    tripleJointCount σ F₁ F₂ F₃ G = tripleJointCount σ F₂ F₃ F₁ G := by
  unfold tripleJointCount
  apply Fintype.card_congr
  refine Equiv.subtypeEquiv
    { toFun := fun ⟨e₁, e₂, e₃⟩ => ⟨e₂, e₃, e₁⟩
      invFun := fun ⟨e₂, e₃, e₁⟩ => ⟨e₁, e₂, e₃⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } ?_
  rintro ⟨e₁, e₂, e₃⟩
  simp only [Equiv.coe_fn_mk]
  constructor
  · rintro ⟨h12, h13, h23, hcov⟩
    exact ⟨h23,
           fun i => and_comm.trans (h12 i),
           fun i => and_comm.trans (h13 i),
           fun i => by
             rcases hcov i with h | h | h
             exacts [.inr (.inr h), .inl h, .inr (.inl h)]⟩
  · rintro ⟨h23, h21, h31, hcov⟩
    exact ⟨fun i => and_comm.trans (h21 i),
           fun i => and_comm.trans (h31 i),
           h23,
           fun i => by
             rcases hcov i with h | h | h
             exacts [.inr (.inl h), .inr (.inr h), .inl h]⟩

/-- If `jointInducedDensity σ F₁ F₂ G > 0` then `jointCount σ F₁ F₂ G > 0`. -/
theorem jointCount_pos_of_jointInducedDensity_pos (σ : FlagType) (F₁ F₂ G : Flag σ)
    (hp : jointInducedDensity σ F₁ F₂ G > 0) :
    0 < jointCount σ F₁ F₂ G := by
  have hjc_pos : (0 : ℝ) < (jointCount σ F₁ F₂ G : ℝ) := by
    unfold jointInducedDensity at hp
    by_contra h; push_neg at h
    have h0 : (jointCount σ F₁ F₂ G : ℝ) = 0 :=
      le_antisymm h (Nat.cast_nonneg _)
    rw [h0] at hp; simp at hp
  exact Nat.cast_pos.mp hjc_pos

/-- Size bounds from positive joint density: the unlabelled sizes satisfy
    `a ≤ n`, `b ≤ n - a` (hence `a + b ≤ n`) where `n = G.size - σ.size`,
    `a = F₁.size - σ.size`, `b = F₂.size - σ.size`. -/
private theorem sizes_from_joint_pos (σ : FlagType) (F₁ F₂ G : Flag σ)
    (hp : jointInducedDensity σ F₁ F₂ G > 0) :
    F₁.size - σ.size ≤ G.size - σ.size ∧
    F₂.size - σ.size ≤ G.size - σ.size - (F₁.size - σ.size) := by
  unfold jointInducedDensity at hp
  -- If the denominator were 0, the density would be 0, contradicting hp > 0.
  have hdenom_pos : (0 : ℝ) <
      (Nat.choose (G.size - σ.size) (F₁.size - σ.size) : ℝ) *
      (Nat.choose (G.size - σ.size - (F₁.size - σ.size)) (F₂.size - σ.size) : ℝ) := by
    by_contra h; push_neg at h
    have hnn : (0 : ℝ) ≤
        (Nat.choose (G.size - σ.size) (F₁.size - σ.size) : ℝ) *
        (Nat.choose (G.size - σ.size - (F₁.size - σ.size)) (F₂.size - σ.size) : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have heq := le_antisymm h hnn
    rw [heq] at hp; simp at hp
  -- Each factor must be nonzero (product > 0 with nonneg factors).
  -- Hence the corresponding choose values are positive, giving the size bounds.
  constructor
  · by_contra h; push_neg at h
    have : Nat.choose (G.size - σ.size) (F₁.size - σ.size) = 0 :=
      Nat.choose_eq_zero_of_lt h
    simp only [this, Nat.cast_zero, zero_mul, lt_self_iff_false] at hdenom_pos
  · by_contra h; push_neg at h
    have : Nat.choose (G.size - σ.size - (F₁.size - σ.size)) (F₂.size - σ.size) = 0 :=
      Nat.choose_eq_zero_of_lt h
    simp only [this, Nat.cast_zero, mul_zero, lt_self_iff_false] at hdenom_pos

/-- Symmetry of positive joint density: if `jointInducedDensity σ F F' H > 0`
    then `jointInducedDensity σ F' F H > 0`. This uses:
    1. `jointCount σ F' F H = jointCount σ F F' H` (by pair-swapping bijection)
    2. The denominators are both positive (from size bounds derived from the witness pair). -/
theorem jointInducedDensity_pos_comm (σ : FlagType) (F₁ F₂ G : Flag σ)
    (hp : jointInducedDensity σ F₁ F₂ G > 0) :
    jointInducedDensity σ F₂ F₁ G > 0 := by
  have hnum : (0 : ℝ) < (jointCount σ F₁ F₂ G : ℝ) :=
    Nat.cast_pos.mpr (jointCount_pos_of_jointInducedDensity_pos σ F₁ F₂ G hp)
  -- Get the size bounds from hp: a ≤ n and b ≤ n - a.
  have ⟨hsz1, hsz2⟩ := sizes_from_joint_pos σ F₁ F₂ G hp
  -- For the swapped denominator C(n, b) * C(n-b, a), we need b ≤ n and a ≤ n-b.
  have hsz2' : F₂.size - σ.size ≤ G.size - σ.size := by omega
  have hsz1' : F₁.size - σ.size ≤ G.size - σ.size - (F₂.size - σ.size) := by omega
  have hdenom_swap : (0 : ℝ) <
      (Nat.choose (G.size - σ.size) (F₂.size - σ.size) : ℝ) *
      (Nat.choose (G.size - σ.size - (F₂.size - σ.size)) (F₁.size - σ.size) : ℝ) :=
    mul_pos (by exact_mod_cast Nat.choose_pos hsz2')
            (by exact_mod_cast Nat.choose_pos hsz1')
  unfold jointInducedDensity
  rw [jointCount_comm]; exact div_pos hnum hdenom_swap

/-! ## §2.1: Local Density

The key modification of the local flag framework: replace the denominator
C(|G|-|σ|, |F|-|σ|) with C(Δ(G), |F|-|σ|) where Δ is a graph parameter. -/

/-- A **graph class** 𝒢 is a predicate on graphs (= ∅-flags).
    In the thesis, 𝒢 is a fixed class of graphs and Δ : 𝒢 → ℕ₀ is a graph parameter
    (typically the max degree). We define both on ∅-flags. -/
def GraphClass := Flag emptyType → Prop

/-- A **graph parameter** Δ : graphs → ℕ (typically the max degree function). -/
def GraphParam := Flag emptyType → ℕ

/-- The **local density** ρ(F; G) = c(F;G) / C(Δ(G), |F|-|σ|).
    Note: Δ is evaluated on the underlying graph of G (forgetting labels).
    (Thesis §2.1 Definition) -/
noncomputable def localDensity (σ : FlagType) (F G : Flag σ) (Δ : GraphParam) : ℝ :=
  (inducedCount σ F G : ℝ) / (Nat.choose (Δ G.forget) (F.size - σ.size) : ℝ)

/-- A **σ-embedding into a graph** G: an induced embedding of σ.graph into G.graph,
    with proof that σ fits inside G. Given such an embedding θ, we can form
    the σ-flag (G, θ). -/
structure SigmaEmbIntoGraph (σ : FlagType) (G : Flag emptyType) where
  emb : σ.graph ↪g G.graph
  hsize : σ.size ≤ G.size

/-- Construct a σ-flag from a graph G and a σ-embedding θ into G. -/
def sigmaFlagOfEmb {σ : FlagType} {G : Flag emptyType}
    (θ : SigmaEmbIntoGraph σ G) : Flag σ where
  size := G.size
  graph := G.graph
  embedding := θ.emb
  hsize := θ.hsize

noncomputable instance (σ : FlagType) (G : Flag emptyType) :
    Fintype (SigmaEmbIntoGraph σ G) :=
  Fintype.ofInjective (fun e => e.emb) (fun a b h => by
    cases a; cases b; subst h; rfl)

/-- The number of σ-embeddings into a graph G. -/
noncomputable def numSigmaEmb (σ : FlagType) (G : Flag emptyType) : ℕ :=
  Fintype.card (SigmaEmbIntoGraph σ G)

/-- The **expected local density** E_θ[ρ(F; (G,θ))] where θ is a uniformly random
    σ-embedding into G. This averages the local density of F over all σ-flags
    that can be formed from G by choosing a σ-embedding.
    (Thesis Lemma 2.7 LHS)

    Defined as (1/N) · Σ_{θ} ρ(F; (G,θ)) where N = |{θ : σ ↪g G}|. -/
noncomputable def expectedLocalDensity (σ : FlagType) (F : Flag σ)
    (G : Flag emptyType) (Δ : GraphParam) : ℝ :=
  let N := Fintype.card (SigmaEmbIntoGraph σ G)
  let S := Finset.univ (α := SigmaEmbIntoGraph σ G)
  (S.sum fun θ => localDensity σ F (sigmaFlagOfEmb θ) Δ) / (N : ℝ)

/-! ## §2.1: Label Extensions

The action of taking a σ-flag and labelling one of its unlabelled vertices,
producing a σ'-flag where |σ'| = |σ| + 1. -/

/-- A **label extension** of σ-flag (F, θ) at unlabelled vertex v ∈ V(F) \ im(θ).
    The extended embedding θ' : [|σ|+1] → V(F) agrees with θ on [|σ|]
    and maps |σ|+1 to v. (Thesis §2.1 Definition) -/
structure LabelExtension (σ : FlagType) (F : Flag σ) where
  vertex : Fin F.size
  unlabelled : vertex ∉ Set.range F.embedding

/-- The map from `Fin (σ.size + 1)` into `Fin F.size` that sends the first σ.size
    elements through F.embedding and sends the last element to ext.vertex. -/
noncomputable def LabelExtension.vertexMap {σ : FlagType} {F : Flag σ}
    (ext : LabelExtension σ F) : Fin (σ.size + 1) → Fin F.size :=
  Fin.lastCases ext.vertex (fun i => F.embedding i)

/-- The **extended type** σ' obtained by adding one vertex to σ.
    σ' has size |σ| + 1 and its graph is the induced subgraph of F on
    im(θ) ∪ {v}, i.e. σ' ≅ F[im θ ∪ {v}]. -/
noncomputable def LabelExtension.extendedType {σ : FlagType} {F : Flag σ}
    (ext : LabelExtension σ F) : FlagType where
  size := σ.size + 1
  graph := F.graph.comap ext.vertexMap

/-- The vertex map of a label extension is injective: the first σ.size elements
    map through the injective embedding, and the last maps to ext.vertex which
    is not in the range of the embedding. -/
theorem LabelExtension.vertexMap_injective {σ : FlagType} {F : Flag σ}
    (ext : LabelExtension σ F) : Function.Injective ext.vertexMap := by
  intro a b hab
  obtain (⟨i, rfl⟩ | rfl) := a.eq_castSucc_or_eq_last
  · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
    · simp only [vertexMap, Fin.lastCases_castSucc] at hab
      exact congr_arg Fin.castSucc (F.embedding.injective hab)
    · simp only [vertexMap, Fin.lastCases_castSucc, Fin.lastCases_last] at hab
      exact absurd ⟨i, hab⟩ ext.unlabelled
  · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
    · simp only [vertexMap, Fin.lastCases_castSucc, Fin.lastCases_last] at hab
      exact absurd ⟨j, hab.symm⟩ ext.unlabelled
    · rfl

/-- The vertex map as a `Function.Embedding`. -/
noncomputable def LabelExtension.vertexMapEmb {σ : FlagType} {F : Flag σ}
    (ext : LabelExtension σ F) : Fin (σ.size + 1) ↪ Fin F.size :=
  ⟨ext.vertexMap, ext.vertexMap_injective⟩

/-- σ.size + 1 ≤ F.size: there exists a vertex outside the embedding range,
    so the flag is strictly larger than the type. -/
theorem LabelExtension.size_le {σ : FlagType} {F : Flag σ}
    (ext : LabelExtension σ F) : σ.size + 1 ≤ F.size := by
  by_contra hle; push_neg at hle
  have hh : F.size = σ.size := Nat.le_antisymm (by omega) F.hsize
  exact ext.unlabelled
    (F.embedding.injective.surjective_of_finite (finCongr hh.symm) ext.vertex)

/-- The flag F viewed as a flag of the extended type σ'. -/
noncomputable def LabelExtension.extendedFlag {σ : FlagType} {F : Flag σ}
    (ext : LabelExtension σ F) : Flag ext.extendedType where
  size := F.size
  graph := F.graph
  embedding := SimpleGraph.Embedding.comap ext.vertexMapEmb F.graph
  hsize := ext.size_le

/-- Each label extension strictly reduces the number of unlabelled vertices. -/
theorem LabelExtension.unlabelledSize_lt {σ : FlagType} {F : Flag σ}
    (ext : LabelExtension σ F) (hF : σ.size < F.size) :
    ext.extendedFlag.unlabelledSize < F.unlabelledSize := by
  unfold Flag.unlabelledSize extendedFlag extendedType
  simp only
  omega

/-! ## §2.1: Hereditary Closure -/

/-- The **hereditary closure** 𝒢̄ of a graph class 𝒢: the smallest class containing 𝒢
    and closed under induced subgraphs. Concretely, G ∈ 𝒢̄ iff G is isomorphic to
    an induced subgraph of some H ∈ 𝒢. (Thesis §2.1 Definition) -/
def HereditaryClosure (𝒢 : GraphClass) : GraphClass :=
  fun G => ∃ H : Flag emptyType, 𝒢 H ∧
    ∃ (f : Fin G.size ↪ Fin H.size),
      ∀ u v : Fin G.size, G.graph.Adj u v ↔ H.graph.Adj (f u) (f v)

/-- 𝒢 ⊆ 𝒢̄: every graph class is contained in its hereditary closure.

    **Status**: Intentional standalone — foundational fact about
    `HereditaryClosure`; no consumer expected. -/
theorem subset_hereditaryClosure (𝒢 : GraphClass) (G : Flag emptyType) (hG : 𝒢 G) :
    HereditaryClosure 𝒢 G :=
  ⟨G, hG, ⟨Function.Embedding.refl _, fun _u _v => Iff.rfl⟩⟩

/-! ## §2.1: Bounded Density and Local Flags -/

/-- A σ-flag F has **bounded density** with respect to a graph class 𝒢 and parameter Δ
    if there exists a constant C such that ρ(F; G) ≤ C for all G ∈ 𝒢^σ.
    Equivalently, c(F; G) ∈ O(Δ(G)^{|F|-|σ|}). (Thesis Def 2.4(a))

    Note: The thesis intentionally uses 𝒢 (not its hereditary closure 𝒢̄) here. -/
def IsBoundedDensity (σ : FlagType) (F : Flag σ) (𝒢 : GraphClass) (Δ : GraphParam) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ G : Flag σ, 𝒢 G.forget → localDensity σ F G Δ ≤ C

/-- A σ-flag F is a **local σ-flag** (Thesis Def 2.4) if:
    1. ρ(F; ·) is a bounded function 𝒢^σ → ℝ≥0
    2. For any label extension θ' of θ, the extended flag (F, θ') is also a local flag.

    This is well-founded since each label extension reduces the number of unlabelled
    vertices by 1. "We could define inductively starting with those flags with no
    unlabelled vertices" (thesis p.25).

    F must be in the hereditary closure 𝒢̄^σ. -/
inductive IsLocalFlag : (σ : FlagType) → Flag σ → GraphClass → GraphParam → Prop where
  | intro (σ : FlagType) (F : Flag σ) (𝒢 : GraphClass) (Δ : GraphParam) :
      IsBoundedDensity σ F 𝒢 Δ →
      (∀ ext : LabelExtension σ F, IsLocalFlag ext.extendedType ext.extendedFlag 𝒢 Δ) →
      IsLocalFlag σ F 𝒢 Δ

/-- Extract the bounded density condition from a local flag. -/
theorem IsLocalFlag.bounded {σ : FlagType} {F : Flag σ} {𝒢 : GraphClass} {Δ : GraphParam}
    (h : IsLocalFlag σ F 𝒢 Δ) : IsBoundedDensity σ F 𝒢 Δ := by
  cases h; assumption

/-- Extract the label extension condition from a local flag. -/
theorem IsLocalFlag.extensions {σ : FlagType} {F : Flag σ} {𝒢 : GraphClass} {Δ : GraphParam}
    (h : IsLocalFlag σ F 𝒢 Δ) :
    ∀ ext : LabelExtension σ F, IsLocalFlag ext.extendedType ext.extendedFlag 𝒢 Δ := by
  cases h; assumption

/-- The set of **local σ-flags** 𝒢^σ_loc (as a predicate). -/
def IsLocalFlagSet (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam) : Set (Flag σ) :=
  {F | IsLocalFlag σ F 𝒢 Δ}

/-! ## Basic properties of local flags -/

/-- For σ-flag F, bounded density is equivalent to c(F; G) ∈ O(Δ(G)^{|F|-|σ|}).
    (Thesis Note after Def 2.4)

    **Status**: Intentional standalone — formalises the Thesis Note;
    no consumer expected. -/
theorem bounded_density_iff_count (σ : FlagType) (F : Flag σ) (𝒢 : GraphClass) (Δ : GraphParam)
    (hΔ : ∀ G : Flag σ, 𝒢 G.forget → F.size - σ.size ≤ Δ G.forget) :
    IsBoundedDensity σ F 𝒢 Δ ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ G : Flag σ, 𝒢 G.forget →
        (inducedCount σ F G : ℝ) ≤ C * (Nat.choose (Δ G.forget) (F.size - σ.size) : ℝ) := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    exact ⟨C, hC, fun G hG => by
      have := hbound G hG
      unfold localDensity at this
      have hne : Nat.choose (Δ G.forget) (F.size - σ.size) ≠ 0 :=
        Nat.choose_pos (hΔ G hG) |>.ne'
      have pos : 0 < (Nat.choose (Δ G.forget) (F.size - σ.size) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hne
      field_simp [pos] at this ⊢
      exact this⟩
  · rintro ⟨C, hC, hbound⟩
    exact ⟨C, hC, fun G hG => by
      unfold localDensity
      have hne : Nat.choose (Δ G.forget) (F.size - σ.size) ≠ 0 :=
        Nat.choose_pos (hΔ G hG) |>.ne'
      have pos : 0 < (Nat.choose (Δ G.forget) (F.size - σ.size) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hne
      field_simp [pos]
      rw [mul_comm]
      exact hbound G hG⟩

/-- If F has no unlabelled vertices (|F| = |σ|), then F is automatically local
    since c(F; G) ≤ 1 for any G. (Thesis: base case of inductive Def 2.4) -/
theorem fully_labelled_is_local (σ : FlagType) (F : Flag σ)
    (hF : F.size = σ.size) (𝒢 : GraphClass) (Δ : GraphParam) :
    IsLocalFlag σ F 𝒢 Δ := by
  refine IsLocalFlag.intro σ F 𝒢 Δ ?_ fun ext => ?_
  · -- Bounded density: ρ(F;G) = c(F;G)/C(Δ,0) = c(F;G)/1 = c(F;G)
    -- When F.size = σ.size, there is at most one σ-compatible embedding (identity on σ).
    -- So c(F;G) ≤ 1 and ρ(F;G) ≤ 1.
    use 1
    refine ⟨by norm_num, fun G _ => ?_⟩
    unfold localDensity
    have hsub : F.size - σ.size = 0 := Nat.sub_eq_zero_of_le (le_of_eq hF)
    rw [hsub, Nat.choose_zero_right]
    simp only [Nat.cast_one, div_one, Nat.cast_le_one, ge_iff_le]
    -- c(F;G) ≤ 1: the embedding is completely determined by σ-compatibility
    unfold inducedCount
    rw [Fintype.card_le_one_iff]
    intro a b
    have hsurj := F.embedding.injective.surjective_of_finite (finCongr hF.symm)
    have : a.toFun = b.toFun := by
      funext v
      obtain ⟨i, rfl⟩ := hsurj v
      exact a.compat i |>.trans (b.compat i).symm
    cases a; cases b; subst this; rfl
  · -- No label extensions when F.size = σ.size
    -- LabelExtension requires a vertex not in im(embedding)
    -- But when F.size = σ.size and embedding is injective, every vertex is in the range
    exact absurd
      (F.embedding.injective.surjective_of_finite (finCongr hF.symm) ext.vertex)
      ext.unlabelled

/-- The type σ viewed as a σ-flag is always a local σ-flag:
    c(σ; G) = 1 for any σ-flag G, so ρ(σ; G) = 1/C(Δ,0) = 1. (Thesis §2.2, Lem 2.4 unit) -/
theorem type_is_local (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam) :
    IsLocalFlag σ σ.toFlag 𝒢 Δ :=
  fully_labelled_is_local σ σ.toFlag rfl 𝒢 Δ

/-- Lemma 2.5 (thesis after Def 2.4): Property (2) of local flags is not
    implied by property (1). There exists 𝒢, Δ, and a σ-flag F with
    bounded density but with an unbounded label extension.

    **Status**: Intentional standalone — formalises Thesis Lemma 2.5
    (counterexample); no consumer expected. -/
theorem bounded_not_implies_local :
    ∃ (𝒢 : GraphClass) (Δ : GraphParam) (σ : FlagType) (F : Flag σ),
      IsBoundedDensity σ F 𝒢 Δ ∧ ¬IsLocalFlag σ F 𝒢 Δ := by
  /- Counterexample: sigma = emptyType, F = independent pair (2 vertices, no edges),
     G = all graphs, Delta(G) = 1 for all G.
     localDensity(F, G) = c(F;G) / C(1, 2) = c(F;G) / 0 = 0 (div by zero is 0 in R),
     so F trivially has bounded density.
     But the label extension at vertex 0 gives a sigma'-flag F' (sigma'.size = 1) with
     localDensity(F', G') = c(F';G') / C(1, 1) = c(F';G'), which is unbounded. -/
  let 𝒢 : GraphClass := fun _ => True
  let Δ : GraphParam := fun _ => 1
  let σ := emptyType
  let emb₀ : σ.graph ↪g (⊥ : SimpleGraph (Fin 2)) :=
    ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
  let F : Flag σ := ⟨2, ⊥, emb₀, Nat.zero_le 2⟩
  refine ⟨𝒢, Δ, σ, F, ?bounded, ?not_local⟩
  case bounded =>
    refine ⟨0, le_refl 0, fun G _ => ?_⟩
    unfold localDensity
    have hFS : F.size - σ.size = 2 := by rfl
    rw [hFS, Nat.choose_eq_zero_of_lt (by norm_num : 1 < 2)]
    simp [div_zero]
  case not_local =>
    have h_unlabelled : (0 : Fin 2) ∉ Set.range F.embedding := by
      simp only [Set.mem_range, not_exists]
      exact fun a => Fin.elim0 a
    let ext : LabelExtension σ F := ⟨0, h_unlabelled⟩
    intro h_local
    have h_ext_local := h_local.extensions ext
    obtain ⟨C, hC, hbound⟩ := h_ext_local.bounded
    -- Key structural facts
    have h_ets : ext.extendedType.size = 1 := by change σ.size + 1 = 1; rfl
    have h_etg : ext.extendedType.graph = ⊥ := by
      change F.graph.comap ext.vertexMap = ⊥
      ext u v
      simp only [SimpleGraph.comap_adj, Bot.bot]
      tauto
    have h_efg : ext.extendedFlag.graph = ⊥ := by change F.graph = ⊥; rfl
    have h_ef_emb :
        ext.extendedFlag.embedding (Fin.last σ.size) = (0 : Fin 2) := by
      change ext.vertexMap (Fin.last σ.size) = 0
      simp only [LabelExtension.vertexMap, Fin.lastCases_last]
      show ext.vertex = 0
      rfl
    -- Take m large enough that m - 1 > C
    set m := ⌈C⌉₊ + 2 with hm_def
    have hm_pos : 0 < m := by omega
    -- Build G': discrete graph on m vertices with vertex 0 labelled
    -- Construct G'_emb directly (no rw) so G'_emb.toFun i = ⟨0, hm_pos⟩ definitionally
    let G'_emb : ext.extendedType.graph ↪g (⊥ : SimpleGraph (Fin m)) :=
      ⟨⟨fun _ => ⟨0, hm_pos⟩, fun {a b} _ => by
        have ha := a.isLt; have hb := b.isLt
        change a.val < σ.size + 1 at ha; change b.val < σ.size + 1 at hb
        exact Fin.ext (by omega)⟩, fun {_ _} => Iff.rfl⟩
    let G' : Flag ext.extendedType := ⟨m, ⊥, G'_emb, by rw [h_ets]; omega⟩
    -- Simplify localDensity to inducedCount (denom = C(1,1) = 1)
    have h_le := hbound G' (show 𝒢 G'.forget from trivial)
    unfold localDensity at h_le
    rw [show ext.extendedFlag.size - ext.extendedType.size = 1 from by
          change F.size - (σ.size + 1) = 1; rfl,
        show Δ G'.forget = 1 from rfl] at h_le
    simp only [Nat.choose_self, Nat.cast_one, div_one] at h_le
    -- Lower-bound inducedCount by m - 1: each k gives embedding (0 -> 0, 1 -> k+1)
    let mk_emb : ∀ k : Fin (m - 1),
        InducedEmbedding ext.extendedType ext.extendedFlag G' := fun k =>
      have hk_lt : k.val + 1 < m := by omega
      { toFun := fun (v : Fin 2) =>
          if v.val = 0 then ⟨0, hm_pos⟩ else ⟨k.val + 1, hk_lt⟩
        injective := by
          intro a b hab
          have ha2 : a.val < 2 := a.isLt
          have hb2 : b.val < 2 := b.isLt
          by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
          · exact Fin.ext (by omega)
          · exfalso; simp only [ha, ↓reduceIte, hb, Fin.mk.injEq] at hab; omega
          · exfalso; simp only [ha, ↓reduceIte, hb, Fin.mk.injEq] at hab; omega
          · exact Fin.ext (by omega)
        map_adj := by
          intro u v huv; rw [h_efg] at huv; exact absurd huv (by simp [SimpleGraph.bot_adj])
        map_non_adj := by intro _ _ _ _; exact fun h => h.elim
        compat := by
          intro i
          have h_val : i.val = 0 := by
            have hi := i.isLt; change i.val < σ.size + 1 at hi; omega
          have h_last : i = Fin.last σ.size := Fin.ext h_val
          -- After rw, goal: toFun (0 : Fin 2) = G'.embedding (Fin.last σ.size)
          -- Both sides reduce to ⟨0, hm_pos⟩ by kernel beta-reduction + let-unfolding
          rw [h_last, h_ef_emb]; simp; rfl
      }
    have mk_inj : Function.Injective mk_emb := by
      intro a b hab
      have h_eq := congr_arg InducedEmbedding.toFun hab
      have h1 := congr_fun h_eq (1 : Fin 2)
      dsimp only [mk_emb] at h1
      simp only [show (1 : Fin 2).val = 1 from rfl, one_ne_zero, ↓reduceIte,
        Fin.mk.injEq] at h1
      exact Fin.ext (by omega)
    have h_lb : m - 1 ≤ inducedCount ext.extendedType ext.extendedFlag G' := by
      unfold inducedCount
      calc m - 1 = Fintype.card (Fin (m - 1)) := (Fintype.card_fin _).symm
        _ ≤ Fintype.card (InducedEmbedding ext.extendedType ext.extendedFlag G') :=
            Fintype.card_le_of_injective mk_emb mk_inj
    -- Contradiction: m - 1 > C but inducedCount <= C
    have h_m_gt : C < ↑(m - 1 : ℕ) := by
      have h1 : C ≤ ↑(⌈C⌉₊ : ℕ) := Nat.le_ceil C
      have h2 : (m : ℕ) - 1 = ⌈C⌉₊ + 1 := by omega
      rw [h2]; push_cast; linarith
    linarith [Nat.cast_le (α := ℝ).mpr h_lb]

/-- The range of the extended embedding equals the original range plus the new vertex. -/
theorem LabelExtension.range_extendedFlag_embedding {σ : FlagType} {F : Flag σ}
    (ext : LabelExtension σ F) :
    Set.range ext.extendedFlag.embedding =
      Set.range F.embedding ∪ {ext.vertex} := by
  have emb_eq : ∀ i, ext.extendedFlag.embedding i = ext.vertexMap i := by
    intro i; rfl
  ext x
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi⟩
    rw [emb_eq] at hi
    obtain (⟨j, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
    · left
      simp only [vertexMap, Fin.lastCases_castSucc] at hi
      exact ⟨j, hi⟩
    · right
      simp only [vertexMap, Fin.lastCases_last] at hi
      exact hi.symm
  · rintro (⟨j, rfl⟩ | rfl)
    · exact ⟨Fin.castSucc j, by rw [emb_eq]; simp [vertexMap]⟩
    · exact ⟨Fin.last _, by rw [emb_eq]; simp [vertexMap]⟩

/-- **Algebraic bound**: `n ^ k ≤ k ^ k * (k ! * Nat.choose n k)` for `k ≤ n`.
    This follows from the chain:
    * `n ≤ k * (n + 1 - k)` when `1 ≤ k ≤ n` (simple algebra)
    * `n ^ k ≤ (k * (n + 1 - k)) ^ k = k ^ k * (n + 1 - k) ^ k` (monotonicity)
    * `(n + 1 - k) ^ k ≤ n.descFactorial k = k ! * C(n, k)` (Mathlib) -/
private theorem pow_le_mul_factorial_mul_choose (n k : ℕ) (hk : k ≤ n) :
    n ^ k ≤ k ^ k * (k ! * n.choose k) := by
  rcases k.eq_zero_or_pos with rfl | hk_pos
  · simp
  · -- Step 1: n ≤ k * (n + 1 - k) when 1 ≤ k ≤ n
    -- In Nat: n + 1 - k ≥ 1 since k ≤ n, and k * (n + 1 - k) ≥ n by algebra.
    have h1 : n ≤ k * (n + 1 - k) := by
      -- Lift to ℤ where subtraction is well-behaved
      zify [show k ≤ n + 1 from by omega]
      nlinarith
    -- Step 2: n ^ k ≤ k ^ k * (n + 1 - k) ^ k
    have h2 : n ^ k ≤ (k * (n + 1 - k)) ^ k := Nat.pow_le_pow_left h1 k
    rw [Nat.mul_pow] at h2
    -- Step 3: (n + 1 - k) ^ k ≤ k ! * C(n, k) (from Mathlib)
    have h3 : (n + 1 - k) ^ k ≤ k ! * n.choose k := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose]; exact n.pow_sub_le_descFactorial k
    calc n ^ k ≤ k ^ k * (n + 1 - k) ^ k := h2
      _ ≤ k ^ k * (k ! * n.choose k) := Nat.mul_le_mul_left _ h3

/-- If a walk in a simple graph starts at a vertex in S and ends at a vertex
    outside S, then some edge of the walk crosses from S to its complement. -/
private theorem walk_crosses_set {n : ℕ} {Gr : SimpleGraph (Fin n)}
    {u v : Fin n} (p : Gr.Walk u v) (S : Set (Fin n))
    (hu : u ∈ S) (hv : v ∉ S) :
    ∃ a b : Fin n, Gr.Adj a b ∧ a ∈ S ∧ b ∉ S := by
  induction p with
  | nil => exact absurd hu hv
  | @cons _ mid _ hadj p' ih =>
    by_cases hy : mid ∈ S
    · exact ih hy hv
    · exact ⟨_, mid, hadj, hu, hy⟩

/-- If there are unlabelled vertices and connectivity holds (every unlabelled
    vertex is reachable from some labelled vertex), then there exists an unlabelled
    vertex directly adjacent to a labelled vertex. -/
private theorem exists_unlabelled_adj_labelled (σ : FlagType) (F : Flag σ)
    (hlt : σ.size < F.size)
    (hconn : ∀ v : Fin F.size, v ∉ Set.range F.embedding →
      ∃ u : Fin F.size, u ∈ Set.range F.embedding ∧ F.graph.Reachable u v) :
    ∃ (w : Fin F.size) (j : Fin σ.size),
      w ∉ Set.range F.embedding ∧ F.graph.Adj (F.embedding j) w := by
  -- There exists an unlabelled vertex since σ.size < F.size
  have h_exists_unlab : ∃ v : Fin F.size, v ∉ Set.range F.embedding := by
    by_contra h_all
    push_neg at h_all
    -- All vertices are in range, so embedding is surjective
    have h_surj : Function.Surjective F.embedding := h_all
    have h_card := Fintype.card_le_of_surjective F.embedding h_surj
    simp [Fintype.card_fin] at h_card
    omega
  obtain ⟨v₀, hv₀⟩ := h_exists_unlab
  obtain ⟨u, hu_lab, hu_reach⟩ := hconn v₀ hv₀
  -- u is labelled and reachable to v₀ (unlabelled)
  obtain ⟨p⟩ := hu_reach
  -- The walk p goes from u (labelled) to v₀ (unlabelled).
  -- By walk_crosses_set, some edge crosses from labelled to unlabelled.
  obtain ⟨a, b, h_adj, ha_lab, hb_unlab⟩ :=
    walk_crosses_set p (Set.range F.embedding) hu_lab hv₀
  obtain ⟨j, rfl⟩ := ha_lab
  exact ⟨b, j, hb_unlab, h_adj⟩

/-- Auxiliary for count_le_pow_degree: induction on k = F.size - σ.size.
    Each step finds an unlabelled vertex w adjacent to a labelled vertex, decomposes
    by the image of w (≤ Δ(G) neighbors), and applies the IH to each fiber. -/
private theorem count_le_pow_degree_aux (k : ℕ) :
    ∀ (σ : FlagType) (F : Flag σ) (G : Flag σ)
      (𝒢 : GraphClass) (Δ : GraphParam),
    F.size - σ.size = k →
    𝒢 G.forget →
    (∀ v : Fin F.size, v ∉ Set.range F.embedding →
      ∃ u : Fin F.size, u ∈ Set.range F.embedding ∧ F.graph.Reachable u v) →
    (∀ G : Flag emptyType, 𝒢 G →
      ∀ v : Fin G.size, @SimpleGraph.degree _ G.graph v
        (@SimpleGraph.neighborSetFintype _ G.graph _ (Classical.decRel _) v) ≤ Δ G) →
    inducedCount σ F G ≤ Δ G.forget ^ k := by
  induction k with
  | zero =>
    intro σ F G 𝒢 Δ hk _ _ _
    -- k = 0: F.size = σ.size, so all vertices are labelled.
    -- At most one InducedEmbedding exists (determined by compat).
    have hFs : F.size = σ.size := by have := F.hsize; omega
    unfold inducedCount
    rw [Nat.pow_zero]
    rw [Fintype.card_le_one_iff]
    intro a b
    have hsurj := F.embedding.injective.surjective_of_finite (finCongr hFs.symm)
    have : a.toFun = b.toFun := by
      funext v
      obtain ⟨i, rfl⟩ := hsurj v
      exact a.compat i |>.trans (b.compat i).symm
    cases a; cases b; subst this; rfl
  | succ k ih =>
    intro σ F G 𝒢 Δ hk hG hconn hΔ_deg
    -- There exist unlabelled vertices since k+1 > 0.
    have hlt : σ.size < F.size := by omega
    -- Find an unlabelled vertex w adjacent to labelled vertex F.embedding j.
    obtain ⟨w, j, hw_unlab, hw_adj⟩ :=
      exists_unlabelled_adj_labelled σ F hlt hconn
    -- Define the label extension at w.
    let ext : LabelExtension σ F := ⟨w, hw_unlab⟩
    -- Key fact: for any e, e(w) is a neighbor of G.embedding j.
    have h_ew_nbr : ∀ e : InducedEmbedding σ F G,
        G.graph.Adj (G.embedding j) (e.toFun w) := by
      intro e; have h := e.map_adj _ _ hw_adj; rwa [e.compat j] at h
    -- Step 1: Every embedding sends w outside range G.embedding.
    have h_not_in_range : ∀ (e : InducedEmbedding σ F G),
        e.toFun w ∉ Set.range G.embedding := by
      intro e ⟨i, hi⟩
      exact hw_unlab ⟨i, e.injective (hi ▸ e.compat i)⟩
    -- Step 2: Connectivity for the extended flag (needed for IH).
    have h_ext_conn : ∀ v : Fin ext.extendedFlag.size,
        v ∉ Set.range ext.extendedFlag.embedding →
        ∃ u : Fin ext.extendedFlag.size,
          u ∈ Set.range ext.extendedFlag.embedding ∧
          ext.extendedFlag.graph.Reachable u v := by
      intro v hv
      rw [ext.range_extendedFlag_embedding] at hv
      simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hv
      obtain ⟨u, hu_in, hu_reach⟩ := hconn v hv.1
      exact ⟨u, by rw [ext.range_extendedFlag_embedding]; exact Set.mem_union_left _ hu_in,
        hu_reach⟩
    -- ext.extendedFlag.size - ext.extendedType.size = k
    have h_ext_k : ext.extendedFlag.size - ext.extendedType.size = k := by
      simp only [LabelExtension.extendedFlag, LabelExtension.extendedType]; omega
    -- Step 3: Decompose by the image of w using card_eq_sum_card_fiberwise.
    unfold inducedCount
    set phi : InducedEmbedding σ F G → Fin G.size := fun e => e.toFun w
    -- The neighbor finset of G.embedding j (using classical decidability).
    -- Use the same fintype as in hΔ_deg for consistency
    haveI : ∀ v : Fin G.forget.size, Fintype ↑(G.forget.graph.neighborSet v) :=
      fun v => @SimpleGraph.neighborSetFintype _ G.forget.graph _ (Classical.decRel _) v
    set nbrs := G.forget.graph.neighborFinset (G.embedding j) with nbrs_def
    -- phi maps into nbrs.
    have hphi_maps : ∀ e : InducedEmbedding σ F G, phi e ∈ nbrs := by
      intro e
      rw [nbrs_def, SimpleGraph.mem_neighborFinset]; exact h_ew_nbr e
    -- Fiber bound: for each t, the fiber over t has at most Delta(G.forget)^k elements.
    have h_fiber_bound : ∀ t : Fin G.size,
        (Finset.univ.filter (fun e : InducedEmbedding σ F G => phi e = t)).card
        ≤ Δ G.forget ^ k := by
      intro t
      by_cases ht_range : t ∈ Set.range G.embedding
      · -- t is labelled: fiber is empty since no e can send w to a labelled vertex.
        convert Nat.zero_le _
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e _ h_eq
        -- h_eq : phi e = t, ht_range : t ∈ Set.range G.embedding
        -- We have phi e = e.toFun w = t ∈ Set.range G.embedding
        simp only [phi] at h_eq
        exact h_not_in_range e (h_eq ▸ ht_range)
      · -- t is unlabelled: construct label extension of G at t and use IH.
        let extG : LabelExtension σ G := ⟨t, ht_range⟩
        -- If the fiber is empty, the bound is trivial.
        by_cases h_empty :
            (Finset.univ.filter (fun e : InducedEmbedding σ F G => phi e = t)) = ∅
        · simp [h_empty]
        · -- Extract a witness e₀ from the non-empty fiber.
          obtain ⟨e₀, he₀⟩ := Finset.nonempty_of_ne_empty h_empty
          rw [Finset.mem_filter] at he₀
          have het₀ : e₀.toFun w = t := by simpa only [phi] using he₀.2
          -- e₀ maps ext.vertexMap to extG.vertexMap pointwise.
          have hcomp₀ : ∀ i, e₀.toFun (ext.vertexMap i) = extG.vertexMap i := by
            intro i
            obtain (⟨m, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
            · simp only [LabelExtension.vertexMap, Fin.lastCases_castSucc]; exact e₀.compat m
            · simp only [LabelExtension.vertexMap, Fin.lastCases_last]; exact het₀
          -- Construct a G-side flag of type ext.extendedType directly.
          -- extG.vertexMap witnesses ext.extendedType.graph ↪g G.graph (via e₀'s adj/non-adj).
          let extG_emb : ext.extendedType.graph ↪g G.graph :=
            ⟨⟨extG.vertexMap, extG.vertexMap_injective⟩, fun {a b} => by
              change G.graph.Adj (extG.vertexMap a) (extG.vertexMap b) ↔
                ext.extendedType.graph.Adj a b
              simp only [LabelExtension.extendedType, SimpleGraph.comap_adj]
              constructor
              · -- G.graph.Adj (extG.vertexMap a) (extG.vertexMap b)
                -- → F.graph.Adj (ext.vertexMap a) (ext.vertexMap b)
                intro h
                by_contra hna
                have hab : a ≠ b := fun heq => h.ne (congrArg extG.vertexMap heq)
                have hab' : ext.vertexMap a ≠ ext.vertexMap b :=
                  fun heq => hab (ext.vertexMap_injective heq)
                have := e₀.map_non_adj _ _ hab' hna
                rw [hcomp₀ a, hcomp₀ b] at this
                exact this h
              · intro h
                have := e₀.map_adj _ _ h
                rwa [hcomp₀ a, hcomp₀ b] at this⟩
          let extGFlag : Flag ext.extendedType :=
            ⟨G.size, G.graph, extG_emb, extG.size_le⟩
          -- For each e in the fiber, e.toFun gives an InducedEmbedding of the extended flags.
          -- The compat condition: e(ext.vertexMap i) = extG.vertexMap i
          have h_compat : ∀ (e : InducedEmbedding σ F G), e.toFun w = t →
              ∀ i, e.toFun (ext.vertexMap i) = extG.vertexMap i := by
            intro e het i
            obtain (⟨m, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
            · simp only [LabelExtension.vertexMap, Fin.lastCases_castSucc]
              exact e.compat m
            · simp only [LabelExtension.vertexMap, Fin.lastCases_last]
              exact het
          -- Card of fiber ≤ Δ^k via counting InducedEmbeddings of the extended flags.
          -- We inject the fiber into InducedEmbedding ext.extendedType ext.extendedFlag extGFlag
          -- by sending e to ⟨e.toFun, ...⟩. This is injective because e is determined by toFun.
          have h_card_fiber :
              (Finset.univ.filter (fun e : InducedEmbedding σ F G => phi e = t)).card ≤
              Fintype.card (InducedEmbedding ext.extendedType ext.extendedFlag extGFlag) := by
            rw [show (Finset.univ.filter (fun e => phi e = t)).card =
                Fintype.card {e : InducedEmbedding σ F G // phi e = t} from by
              rw [← Fintype.card_coe]
              exact Fintype.card_of_bijective
                (Equiv.subtypeEquivRight (by simp [Finset.mem_filter])).bijective]
            apply Fintype.card_le_of_injective
              (fun (p : {e : InducedEmbedding σ F G // phi e = t}) =>
                (⟨p.val.toFun, p.val.injective, p.val.map_adj, p.val.map_non_adj,
                  h_compat p.val (by simpa [phi] using p.prop)⟩ :
                  InducedEmbedding ext.extendedType ext.extendedFlag extGFlag))
            intro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ h_eq
            simp only [Subtype.mk.injEq]
            -- Beta-reduce the lambda application in h_eq
            dsimp only at h_eq
            have htf : e₁.toFun = e₂.toFun :=
              congr_arg (fun e : InducedEmbedding ext.extendedType
                ext.extendedFlag extGFlag => e.toFun) h_eq
            cases e₁; cases e₂; subst htf; rfl
          -- extGFlag.forget = G.forget (same size and graph).
          have h_ext_forget : extGFlag.forget = G.forget := rfl
          -- Apply IH.
          calc (Finset.univ.filter (fun e => phi e = t)).card
              ≤ Fintype.card (InducedEmbedding ext.extendedType
                  ext.extendedFlag extGFlag) := h_card_fiber
            _ ≤ Δ extGFlag.forget ^ k :=
                ih ext.extendedType ext.extendedFlag extGFlag 𝒢 Δ
                  h_ext_k (h_ext_forget ▸ hG) h_ext_conn hΔ_deg
            _ = Δ G.forget ^ k := by rw [h_ext_forget]
    -- Step 4: Combine using card_eq_sum_card_fiberwise.
    have h_decomp : Fintype.card (InducedEmbedding σ F G) =
        ∑ t ∈ nbrs, (Finset.univ.filter
          (fun e : InducedEmbedding σ F G => phi e = t)).card := by
      rw [← Finset.card_univ]
      exact Finset.card_eq_sum_card_fiberwise (fun e _ => hphi_maps e)
    rw [h_decomp]
    calc ∑ t ∈ nbrs, (Finset.univ.filter
            (fun e : InducedEmbedding σ F G => phi e = t)).card
        ≤ ∑ _t ∈ nbrs, Δ G.forget ^ k :=
          Finset.sum_le_sum (fun t _ => h_fiber_bound t)
      _ = nbrs.card * Δ G.forget ^ k := by simp [Finset.sum_const]
      _ ≤ Δ G.forget * Δ G.forget ^ k := by
          apply Nat.mul_le_mul_right
          have h_deg := hΔ_deg G.forget hG (G.embedding j)
          simp only [SimpleGraph.degree] at h_deg
          simp only [nbrs_def]
          convert h_deg
      _ = Δ G.forget ^ (k + 1) := by rw [mul_comm, pow_succ]

private theorem count_le_pow_degree (σ : FlagType) (F : Flag σ) (G : Flag σ)
    (𝒢 : GraphClass) (Δ : GraphParam) (hG : 𝒢 G.forget)
    (hconn : ∀ v : Fin F.size, v ∉ Set.range F.embedding →
      ∃ u : Fin F.size, u ∈ Set.range F.embedding ∧ F.graph.Reachable u v)
    (hΔ_deg : ∀ G : Flag emptyType, 𝒢 G →
      ∀ v : Fin G.size, @SimpleGraph.degree _ G.graph v
        (@SimpleGraph.neighborSetFintype _ G.graph _ (Classical.decRel _) v) ≤ Δ G) :
    inducedCount σ F G ≤ Δ G.forget ^ (F.size - σ.size) :=
  count_le_pow_degree_aux (F.size - σ.size) σ F G 𝒢 Δ rfl hG hconn hΔ_deg

/-- **Counting lemma for connected flags** (Thesis sketch of Lemma 2.2):
    If Δ bounds vertex degree and every label extension of F has bounded density,
    then F has bounded density.

    Proof sketch: Each induced copy of F in G is built by starting from the
    fixed σ-labelled vertices and extending one vertex at a time. By connectivity,
    each new vertex is adjacent to some already-placed vertex, giving ≤ Δ(G)
    choices at each step. With k = |F| - |σ| steps, c(F; G) ≤ Δ(G)^k, so
    localDensity = c(F;G) / C(Δ(G), k) ≤ Δ(G)^k / C(Δ(G), k) ≤ k^k * k!. -/
private theorem bounded_density_of_extensions_bounded (σ : FlagType) (F : Flag σ)
    (𝒢 : GraphClass) (Δ : GraphParam)
    (_hlt : σ.size < F.size)
    (hconn : ∀ v : Fin F.size, v ∉ Set.range F.embedding →
      ∃ u : Fin F.size, u ∈ Set.range F.embedding ∧ F.graph.Reachable u v)
    (hΔ_deg : ∀ G : Flag emptyType, 𝒢 G →
      ∀ v : Fin G.size, @SimpleGraph.degree _ G.graph v
        (@SimpleGraph.neighborSetFintype _ G.graph _ (Classical.decRel _) v) ≤ Δ G)
    (_h_ext_bd : ∀ ext : LabelExtension σ F,
      IsBoundedDensity ext.extendedType ext.extendedFlag 𝒢 Δ) :
    IsBoundedDensity σ F 𝒢 Δ := by
  -- Use C = k^k * k! where k = F.size - σ.size as the bounding constant.
  set k := F.size - σ.size with hk_def
  refine ⟨((k ^ k * k ! : ℕ) : ℝ), Nat.cast_nonneg _, fun G hG => ?_⟩
  unfold localDensity
  -- Case split: if C(Δ(G), k) = 0, localDensity = 0 (division by zero)
  by_cases hΔk : Nat.choose (Δ G.forget) k = 0
  · rw [hΔk, Nat.cast_zero, div_zero]
    exact Nat.cast_nonneg _
  · -- C(Δ(G), k) > 0, so Δ(G) ≥ k
    have hΔ_ge_k : k ≤ Δ G.forget := by
      by_contra h; push_neg at h
      exact hΔk (Nat.choose_eq_zero_of_lt h)
    have hchoose_pos : (0 : ℝ) < (Nat.choose (Δ G.forget) k : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hΔk
    -- Combine the counting bound c(F;G) ≤ Δ(G)^k with the algebraic bound.
    have h_combined : inducedCount σ F G ≤ k ^ k * k ! * Nat.choose (Δ G.forget) k := by
      calc inducedCount σ F G
          ≤ Δ G.forget ^ k := count_le_pow_degree σ F G 𝒢 Δ hG hconn hΔ_deg
        _ ≤ k ^ k * (k ! * Nat.choose (Δ G.forget) k) :=
            pow_le_mul_factorial_mul_choose (Δ G.forget) k hΔ_ge_k
        _ = k ^ k * k ! * Nat.choose (Δ G.forget) k := by ring
    -- Therefore: c(F;G) / C(Δ(G), k) ≤ k^k * k!
    rw [div_le_iff₀ hchoose_pos]
    exact_mod_cast h_combined

/-- Auxiliary lemma: `local_if_connected` by strong induction on unlabelled size. -/
private theorem local_if_connected_aux (n : ℕ) :
    ∀ (σ : FlagType) (F : Flag σ) (𝒢 : GraphClass) (Δ : GraphParam),
      F.unlabelledSize = n →
      (∀ v : Fin F.size, v ∉ Set.range F.embedding →
        ∃ u : Fin F.size, u ∈ Set.range F.embedding ∧ F.graph.Reachable u v) →
      (∀ G : Flag emptyType, 𝒢 G →
        ∀ v : Fin G.size, @SimpleGraph.degree _ G.graph v
        (@SimpleGraph.neighborSetFintype _ G.graph _ (Classical.decRel _) v) ≤ Δ G) →
      IsLocalFlag σ F 𝒢 Δ := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro σ F 𝒢 Δ h_ind hconn hΔ_deg
  -- Base case: if n = 0, all vertices are labelled
  by_cases hn : n = 0
  · subst hn
    have hFs : F.size = σ.size := by
      unfold Flag.unlabelledSize at h_ind
      have := F.hsize; omega
    exact fully_labelled_is_local σ F hFs 𝒢 Δ
  -- Inductive step: n > 0, so there exist unlabelled vertices
  · have hlt : σ.size < F.size := by
      unfold Flag.unlabelledSize at h_ind
      have := F.hsize; omega
    refine IsLocalFlag.intro σ F 𝒢 Δ ?_ fun ext => ?_
    · -- Part 1: IsBoundedDensity via the counting lemma.
      -- First, show all label extensions are local (same argument as Part 2).
      have h_ext_local : ∀ ext : LabelExtension σ F,
          IsLocalFlag ext.extendedType ext.extendedFlag 𝒢 Δ := by
        intro ext
        have hlt_ext : ext.extendedFlag.unlabelledSize < n := by
          calc ext.extendedFlag.unlabelledSize
              < F.unlabelledSize := ext.unlabelledSize_lt hlt
            _ = n := h_ind
        apply ih ext.extendedFlag.unlabelledSize hlt_ext _ _ _ _ rfl
        · intro v hv
          rw [ext.range_extendedFlag_embedding] at hv
          simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hv
          obtain ⟨hv_not_orig, hv_ne_ext⟩ := hv
          obtain ⟨u, hu_in, hu_reach⟩ := hconn v hv_not_orig
          refine ⟨u, ?_, hu_reach⟩
          rw [ext.range_extendedFlag_embedding]; exact Set.mem_union_left _ hu_in
        · exact hΔ_deg
      -- Extract bounded density from locality of each extension.
      have h_ext_bd : ∀ ext : LabelExtension σ F,
          IsBoundedDensity ext.extendedType ext.extendedFlag 𝒢 Δ :=
        fun ext => (h_ext_local ext).bounded
      -- Apply the counting lemma.
      exact bounded_density_of_extensions_bounded σ F 𝒢 Δ hlt hconn
        hΔ_deg h_ext_bd
    · -- Part 2: For any label extension, the extended flag is local
      have hlt_ext : ext.extendedFlag.unlabelledSize < n := by
        calc ext.extendedFlag.unlabelledSize
            < F.unlabelledSize := ext.unlabelledSize_lt hlt
          _ = n := h_ind
      apply ih ext.extendedFlag.unlabelledSize hlt_ext _ _ _ _ rfl
      · -- Verify the connectivity condition for the extended flag
        intro v hv
        rw [ext.range_extendedFlag_embedding] at hv
        simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hv
        obtain ⟨hv_not_orig, hv_ne_ext⟩ := hv
        obtain ⟨u, hu_in, hu_reach⟩ := hconn v hv_not_orig
        refine ⟨u, ?_, hu_reach⟩
        rw [ext.range_extendedFlag_embedding]; exact Set.mem_union_left _ hu_in
      · exact hΔ_deg

theorem local_if_connected (σ : FlagType) (F : Flag σ)
    (𝒢 : GraphClass) (Δ : GraphParam)
    (hconn : ∀ v : Fin F.size, v ∉ Set.range F.embedding →
      ∃ u : Fin F.size, u ∈ Set.range F.embedding ∧ F.graph.Reachable u v)
    (hΔ_deg : ∀ G : Flag emptyType, 𝒢 G →
      ∀ v : Fin G.size, @SimpleGraph.degree _ G.graph v
        (@SimpleGraph.neighborSetFintype _ G.graph _ (Classical.decRel _) v) ≤ Δ G) :
    IsLocalFlag σ F 𝒢 Δ :=
  local_if_connected_aux F.unlabelledSize σ F 𝒢 Δ rfl hconn hΔ_deg

/-! ## §2.1: Local Types -/

/-- A type σ is a **local type** if ↓F is a local ∅-flag for all F ∈ 𝒢^σ_loc.
    (Thesis Def 2.8) -/
def IsLocalType (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam) : Prop :=
  ∀ F : Flag σ, IsLocalFlag σ F 𝒢 Δ →
    IsLocalFlag emptyType F.forget 𝒢 Δ

/-- Forgetting the σ-label of `sigmaFlagOfEmb θ` gives back `G.forget`,
    since the underlying size and graph are unchanged, and the ∅-embedding
    and hsize fields are uniquely determined (Fin 0 is empty, hsize is a Prop). -/
private theorem sigmaFlagOfEmb_forget_eq {σ' : FlagType} {G : Flag emptyType}
    (θ : SigmaEmbIntoGraph σ' G) :
    (sigmaFlagOfEmb θ).forget = G.forget := rfl

/-- Given an ∅-embedding of ↓F' into G, extract the induced σ'-embedding into G
    by composing with F'.embedding.
    Part of the counting decomposition (Thesis Lem 2.6). -/
private def extractSigmaEmb {σ' : FlagType} {F' : Flag σ'} {G : Flag emptyType}
    (e : InducedEmbedding emptyType F'.forget G) : SigmaEmbIntoGraph σ' G where
  emb :=
    -- Compose: σ'.graph → F'.graph via F'.embedding, then F'.graph → G.graph via e.
    -- The composition is an induced graph embedding σ'.graph ↪g G.graph.
    { toEmbedding := ⟨fun i => e.toFun (F'.embedding i),
        fun i j h => F'.embedding.injective (e.injective h)⟩
      map_rel_iff' := fun {i j} => by
        -- Need: G.graph.Adj (e.toFun (F'.emb i)) (e.toFun (F'.emb j)) ↔ σ'.graph.Adj i j
        constructor
        · -- Backward: G-adj → σ'-adj. By contrapositive of e.map_non_adj.
          intro h_G
          -- Reduce the anonymous constructor application in h_G.
          change G.graph.Adj (e.toFun (F'.embedding i)) (e.toFun (F'.embedding j)) at h_G
          rw [← F'.embedding.map_rel_iff']
          by_contra h_not_adj
          have h_ne : F'.embedding i ≠ F'.embedding j := by
            intro heq; rw [heq] at h_G; exact G.graph.irrefl h_G
          exact absurd h_G (e.map_non_adj _ _ h_ne h_not_adj)
        · -- Forward: σ'-adj → G-adj. Compose the two embeddings.
          intro h_σ
          change G.graph.Adj (e.toFun (F'.embedding i)) (e.toFun (F'.embedding j))
          exact e.map_adj _ _ (F'.embedding.map_rel_iff'.mpr h_σ) }
  hsize := by
    -- σ'.size ≤ F'.size ≤ G.size
    have h_le : Fintype.card (Fin F'.forget.size) ≤ Fintype.card (Fin G.size) :=
      Fintype.card_le_of_injective e.toFun e.injective
    simp only [Fintype.card_fin] at h_le
    exact le_trans F'.hsize h_le

/-- The composition `(sigmaFlagOfEmb (extractSigmaEmb e)).embedding i` equals
    `e.toFun (F'.embedding i)` by definition. -/
private theorem extractSigmaEmb_embedding_eq {σ' : FlagType} {F' : Flag σ'}
    {G : Flag emptyType} (e : InducedEmbedding emptyType F'.forget G)
    (i : Fin σ'.size) :
    (sigmaFlagOfEmb (extractSigmaEmb e)).embedding i = e.toFun (F'.embedding i) := rfl

/-- Given an ∅-embedding e of ↓F' into G, lift it to a σ'-embedding of F'
    into the σ'-flag (G, extractSigmaEmb e). Reuses e.toFun; compatibility
    follows from the definition of extractSigmaEmb. -/
private def liftToSigmaEmb {σ' : FlagType} {F' : Flag σ'} {G : Flag emptyType}
    (e : InducedEmbedding emptyType F'.forget G) :
    InducedEmbedding σ' F' (sigmaFlagOfEmb (extractSigmaEmb e)) where
  toFun := e.toFun
  injective := e.injective
  map_adj := e.map_adj
  map_non_adj := e.map_non_adj
  compat := fun i => by exact extractSigmaEmb_embedding_eq e i

/-- Given a σ-embedding θ into G and a σ-compatible embedding e' of F into (G,θ),
    forget the σ-structure to get an ∅-embedding of ↓F into G. -/
private def reverseSigmaEmb {σ' : FlagType} {F' : Flag σ'} {G : Flag emptyType}
    (θ : SigmaEmbIntoGraph σ' G) (e' : InducedEmbedding σ' F' (sigmaFlagOfEmb θ)) :
    InducedEmbedding emptyType F'.forget G where
  toFun := e'.toFun
  injective := e'.injective
  map_adj := e'.map_adj
  map_non_adj := e'.map_non_adj
  compat := fun i => Fin.elim0 i

/-- **Counting equality** (Thesis Lem 2.6): c(↓F'; G) = Σ_θ c(F'; (G, θ)).
    The number of ∅-embeddings of ↓F' into G equals the sum over σ-embeddings θ
    of the number of σ-compatible embeddings of F' into (G, θ).
    Proved by constructing a bijection via `extractSigmaEmb`/`liftToSigmaEmb`
    (forward) and `reverseSigmaEmb` (reverse). -/
theorem forget_count_eq_sigma_sum (σ' : FlagType) (F' : Flag σ')
    (G : Flag emptyType) :
    inducedCount emptyType F'.forget G =
      Finset.univ.sum (fun θ : SigmaEmbIntoGraph σ' G =>
        inducedCount σ' F' (sigmaFlagOfEmb θ)) := by
  unfold inducedCount
  rw [← Fintype.card_sigma]
  apply le_antisymm
  · -- Forward: inject InducedEmbedding into Σ θ, InducedEmbedding
    apply Fintype.card_le_of_injective
      (fun e => ⟨extractSigmaEmb e, liftToSigmaEmb e⟩)
    intro e₁ e₂ h_eq
    let proj : (Σ θ : SigmaEmbIntoGraph σ' G,
        InducedEmbedding σ' F' (sigmaFlagOfEmb θ)) →
        (Fin F'.size → Fin G.size) := fun p => p.2.toFun
    have h_toFun : e₁.toFun = e₂.toFun := by
      have h := congr_arg proj h_eq; dsimp only [proj] at h; exact h
    cases e₁; cases e₂; simp only at h_toFun; subst h_toFun; rfl
  · -- Reverse: inject Σ θ, InducedEmbedding into InducedEmbedding
    apply Fintype.card_le_of_injective
      (fun p => reverseSigmaEmb p.1 p.2)
    intro ⟨θ₁, e₁⟩ ⟨θ₂, e₂⟩ h_eq
    -- From h_eq: e₁.toFun = e₂.toFun
    have h_toFun : e₁.toFun = e₂.toFun := by
      have : (reverseSigmaEmb θ₁ e₁).toFun = (reverseSigmaEmb θ₂ e₂).toFun :=
        congrArg InducedEmbedding.toFun h_eq
      exact this
    -- θ₁.emb = θ₂.emb (from compat + h_toFun)
    have h_emb : θ₁.emb = θ₂.emb := by
      ext i
      have h1 := e₁.compat i; have h2 := e₂.compat i
      simp only [sigmaFlagOfEmb] at h1 h2
      rw [← h1, ← h2, h_toFun]
    -- θ₁ = θ₂
    have h_θ : θ₁ = θ₂ := by cases θ₁; cases θ₂; simp only at h_emb; subst h_emb; rfl
    subst h_θ
    -- e₁ = e₂
    cases e₁; cases e₂; simp only at h_toFun; subst h_toFun; rfl

private theorem forget_count_le_sigma_sum (σ' : FlagType) (F' : Flag σ')
    (G : Flag emptyType) :
    inducedCount emptyType F'.forget G ≤
      Finset.univ.sum (fun θ : SigmaEmbIntoGraph σ' G =>
        inducedCount σ' F' (sigmaFlagOfEmb θ)) :=
  le_of_eq (forget_count_eq_sigma_sum σ' F' G)

/-- **Vandermonde-type bound**: C(n, a) * C(n, b) ≤ C(a+b, a)² * C(n, a+b)
    for a + b ≤ n. Proved by induction on n using the absorption identity. -/
theorem choose_mul_choose_le (a b n : ℕ) (h : a + b ≤ n) :
    Nat.choose n a * Nat.choose n b ≤
      Nat.choose (a + b) a ^ 2 * Nat.choose n (a + b) := by
  -- Induction on d = n - (a+b). Write n = a + b + d.
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero =>
    -- n = a + b: C(a+b,a) * C(a+b,b) = C(a+b,a)² since C(a+b,b) = C(a+b,a).
    simp only [Nat.add_zero, Nat.choose_self, mul_one]
    rw [Nat.choose_symm_add, sq]
  | succ d ih =>
    -- IH: C(a+b+d, a) * C(a+b+d, b) ≤ C(a+b,a)² * C(a+b+d, a+b)
    have ih' := ih (Nat.le_add_right (a + b) d)
    -- Use choose_mul_succ_eq: C(m,k) * (m+1) = C(m+1,k) * (m+1-k)
    -- Set m = a + b + d. Then m+1 = a + b + (d+1).
    set m := a + b + d with hm_def
    -- From IH, multiply both sides by (m+1)²:
    -- C(m,a)*(m+1) * C(m,b)*(m+1) ≤ C(a+b,a)² * C(m,a+b) * (m+1)²
    -- LHS: C(m+1,a)*(m+1-a) * C(m+1,b)*(m+1-b)  [by choose_mul_succ_eq twice]
    -- RHS factor: C(m,a+b)*(m+1) = C(m+1,a+b)*(m+1-a-b)  [by choose_mul_succ_eq]
    -- So RHS = C(a+b,a)² * C(m+1,a+b) * (m+1-a-b) * (m+1)
    -- Key algebraic fact: (m+1-a-b)*(m+1) ≤ (m+1-a)*(m+1-b) since ab ≥ 0.
    -- Therefore: C(m+1,a)*(m+1-a)*C(m+1,b)*(m+1-b) ≤
    --            C(a+b,a)² * C(m+1,a+b) * (m+1-a)*(m+1-b)
    -- Cancel (m+1-a)*(m+1-b) > 0 from both sides.
    have ha_le_m : a ≤ m := le_trans (Nat.le_add_right a b) (Nat.le_add_right (a+b) d)
    have hb_le_m : b ≤ m := le_trans (Nat.le_add_left b a) (Nat.le_add_right (a+b) d)
    have hab_le_m : a + b ≤ m := Nat.le_add_right (a+b) d
    -- m + 1 - a ≥ 1 and m + 1 - b ≥ 1
    have hma : 0 < m + 1 - a := by omega
    have hmb : 0 < m + 1 - b := by omega
    -- Absorption identities
    have abs_a := Nat.choose_mul_succ_eq m a
    have abs_b := Nat.choose_mul_succ_eq m b
    have abs_ab := Nat.choose_mul_succ_eq m (a + b)
    -- From IH * (m+1)²:
    -- C(m,a)*(m+1) * (C(m,b)*(m+1)) ≤ C(a+b,a)² * (C(m,a+b)*(m+1)) * (m+1)
    have step1 : Nat.choose m a * (m + 1) * (Nat.choose m b * (m + 1)) ≤
        Nat.choose (a + b) a ^ 2 * (Nat.choose m (a + b) * (m + 1)) * (m + 1) := by
      calc Nat.choose m a * (m + 1) * (Nat.choose m b * (m + 1))
          = Nat.choose m a * Nat.choose m b * (m + 1) * (m + 1) := by ring
        _ ≤ Nat.choose (a + b) a ^ 2 * Nat.choose m (a + b) * (m + 1) * (m + 1) := by
            apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; exact ih'
        _ = Nat.choose (a + b) a ^ 2 * (Nat.choose m (a + b) * (m + 1)) * (m + 1) := by ring
    -- Rewrite using absorption identities
    rw [abs_a, abs_b, abs_ab] at step1
    -- step1 : C(m+1,a)*(m+1-a) * (C(m+1,b)*(m+1-b)) ≤
    --          C(a+b,a)² * (C(m+1,a+b)*(m+1-(a+b))) * (m+1)
    -- Algebraic fact: (m+1-(a+b)) * (m+1) ≤ (m+1-a) * (m+1-b)
    have alg_fact : (m + 1 - (a + b)) * (m + 1) ≤ (m + 1 - a) * (m + 1 - b) := by
      -- Write p = m+1-a, q = m+1-b, r = m+1-(a+b). Then p = r+b, q = r+a,
      -- m+1 = r+a+b. So r*(r+a+b) + a*b = (r+b)*(r+a) = p*q.
      -- Hence r*(m+1) ≤ p*q.
      set p := m + 1 - a
      set q := m + 1 - b
      set r := m + 1 - (a + b)
      have hp : p = r + b := by omega
      have hq : q = r + a := by omega
      have hm1 : m + 1 = r + a + b := by omega
      rw [hp, hq, hm1]
      nlinarith [Nat.zero_le (a * b)]
    -- So RHS of step1 ≤ C(a+b,a)² * C(m+1,a+b) * (m+1-a) * (m+1-b)
    have step2 : Nat.choose (a + b) a ^ 2 *
        (Nat.choose (m + 1) (a + b) * (m + 1 - (a + b))) * (m + 1) ≤
        Nat.choose (a + b) a ^ 2 * Nat.choose (m + 1) (a + b) *
        ((m + 1 - a) * (m + 1 - b)) := by
      calc Nat.choose (a + b) a ^ 2 *
            (Nat.choose (m + 1) (a + b) * (m + 1 - (a + b))) * (m + 1)
          = Nat.choose (a + b) a ^ 2 * Nat.choose (m + 1) (a + b) *
            ((m + 1 - (a + b)) * (m + 1)) := by ring
        _ ≤ Nat.choose (a + b) a ^ 2 * Nat.choose (m + 1) (a + b) *
            ((m + 1 - a) * (m + 1 - b)) := by
            apply Nat.mul_le_mul_left; exact alg_fact
    -- Combine: LHS of step1 ≤ RHS
    have step3 : Nat.choose (m + 1) a * (m + 1 - a) *
        (Nat.choose (m + 1) b * (m + 1 - b)) ≤
        Nat.choose (a + b) a ^ 2 * Nat.choose (m + 1) (a + b) *
        ((m + 1 - a) * (m + 1 - b)) := le_trans step1 step2
    -- Rearrange LHS
    have lhs_rw : Nat.choose (m + 1) a * (m + 1 - a) *
        (Nat.choose (m + 1) b * (m + 1 - b)) =
        Nat.choose (m + 1) a * Nat.choose (m + 1) b *
        ((m + 1 - a) * (m + 1 - b)) := by ring
    rw [lhs_rw] at step3
    -- Cancel (m+1-a) * (m+1-b) > 0 from both sides
    have hprod_pos : 0 < (m + 1 - a) * (m + 1 - b) := Nat.mul_pos hma hmb
    -- m + 1 = a + b + (d + 1), so goal is about C(a+b+(d+1), a) * C(a+b+(d+1), b) ≤ ...
    change Nat.choose (a + b + (d + 1)) a * Nat.choose (a + b + (d + 1)) b ≤
        Nat.choose (a + b) a ^ 2 * Nat.choose (a + b + (d + 1)) (a + b)
    change Nat.choose (m + 1) a * Nat.choose (m + 1) b ≤
        Nat.choose (a + b) a ^ 2 * Nat.choose (m + 1) (a + b)
    exact Nat.le_of_mul_le_mul_right step3 hprod_pos

/-- **Helper (Thesis Lem 2.6, bounded density)**: If F' is a σ-flag with bounded
    local density and ↓σ has bounded density as an ∅-flag, then ↓F' has bounded
    local density as an ∅-flag.

    The counting argument decomposes each ∅-embedding of F' into G via a
    σ-embedding of σ into G, then applies Vandermonde's convolution identity.
    Requires: (i) counting decomposition lemma, (ii) Vandermonde inequality. -/
theorem bounded_density_forget
    (σ' : FlagType) (F' : Flag σ') (𝒢 : GraphClass) (Δ : GraphParam)
    (hbd : IsBoundedDensity σ' F' 𝒢 Δ)
    (hσ_bd : IsBoundedDensity emptyType (σ'.toFlag.forget) 𝒢 Δ) :
    IsBoundedDensity emptyType F'.forget 𝒢 Δ := by
  -- Extract bounding constants.
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := hbd
  obtain ⟨C₂, hC₂_nn, hC₂⟩ := hσ_bd
  -- The combined bound: C₁ · C₂ · C(|F'|, |σ'|)².
  set K := (Nat.choose F'.size σ'.size : ℝ) ^ 2 with hK_def
  refine ⟨C₁ * C₂ * K, ?nonneg, ?bound⟩
  case nonneg =>
    exact mul_nonneg (mul_nonneg hC₁_nn hC₂_nn) (pow_nonneg (Nat.cast_nonneg _) 2)
  case bound =>
    intro G hG
    -- Goal: localDensity emptyType F'.forget G Δ ≤ C₁ * C₂ * K
    -- i.e., c(↓F'; G) / C(Δ(G.forget), |F'|) ≤ C₁ * C₂ * C(|F'|, |σ'|)²
    unfold localDensity
    -- The denominator: C(Δ(G.forget), F'.size - 0) = C(Δ(G.forget), F'.size)
    have hFS : F'.forget.size - emptyType.size = F'.size := by
      change F'.size - 0 = F'.size; omega
    rw [hFS]
    set D := Δ G.forget with hD_def
    set denom := Nat.choose D F'.size with hdenom_def
    -- Case split on whether the denominator is zero.
    by_cases hdenom_zero : denom = 0
    · -- When C(Δ, |F'|) = 0, the local density is 0 by div_zero convention.
      rw [hdenom_zero, Nat.cast_zero, div_zero]
      exact mul_nonneg (mul_nonneg hC₁_nn hC₂_nn) (pow_nonneg (Nat.cast_nonneg _) 2)
    · -- When C(Δ, |F'|) > 0, i.e., Δ ≥ |F'| ≥ |σ'|.
      have hdenom_pos : 0 < (denom : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hdenom_zero
      have hD_ge_F : F'.size ≤ D := by
        by_contra h_lt; push_neg at h_lt
        exact hdenom_zero (Nat.choose_eq_zero_of_lt h_lt)
      have hD_ge_σ : σ'.size ≤ D := le_trans F'.hsize hD_ge_F
      -- The σ'-denominator and (F'-σ')-denominator are also positive.
      set denom_σ := Nat.choose D σ'.size with hdenom_σ_def
      set denom_F := Nat.choose D (F'.size - σ'.size) with hdenom_F_def
      have hdenom_σ_pos : 0 < (denom_σ : ℝ) := by
        exact_mod_cast Nat.choose_pos hD_ge_σ
      have hdenom_F_pos : 0 < (denom_F : ℝ) := by
        have : F'.size - σ'.size ≤ D := le_trans (Nat.sub_le F'.size σ'.size) hD_ge_F
        exact_mod_cast Nat.choose_pos this
      -- Step 1: Counting decomposition.
      -- c(↓F'; G) ≤ Σ_θ c(F'; (G, θ))
      have h_decomp := forget_count_le_sigma_sum σ' F' G
      -- Step 2: Bound each c(F'; (G,θ)) using hC₁.
      -- For each θ, (sigmaFlagOfEmb θ).forget = G.forget, so 𝒢 (sigmaFlagOfEmb θ).forget.
      -- localDensity σ' F' (sigmaFlagOfEmb θ) Δ ≤ C₁
      -- ⟹ c(F'; (G,θ)) ≤ C₁ * C(Δ, |F'| - |σ'|)   (when denom_F > 0)
      have h_per_theta : ∀ θ : SigmaEmbIntoGraph σ' G,
          (inducedCount σ' F' (sigmaFlagOfEmb θ) : ℝ) ≤ C₁ * (denom_F : ℝ) := by
        intro θ
        have hG_θ : 𝒢 (sigmaFlagOfEmb θ).forget := hG
        have h_le := hC₁ (sigmaFlagOfEmb θ) hG_θ
        unfold localDensity at h_le
        -- (sigmaFlagOfEmb θ).forget and G.forget are definitionally equal,
        -- so Δ on them agrees; rewrite to use D and denom_F.
        have hΔ_eq : Δ (sigmaFlagOfEmb θ).forget = D := rfl
        rw [hΔ_eq] at h_le
        rwa [div_le_iff₀ hdenom_F_pos] at h_le
      -- Step 3: Sum the bound over all θ.
      -- Σ_θ c(F'; (G,θ)) ≤ |{θ}| * C₁ * C(Δ, |F'| - |σ'|)
      have h_sum_bound :
          (Finset.univ.sum (fun θ : SigmaEmbIntoGraph σ' G =>
            inducedCount σ' F' (sigmaFlagOfEmb θ)) : ℝ) ≤
          (Fintype.card (SigmaEmbIntoGraph σ' G) : ℝ) * C₁ * (denom_F : ℝ) := by
        calc (Finset.univ.sum (fun θ =>
                (inducedCount σ' F' (sigmaFlagOfEmb θ) : ℝ)) : ℝ)
            ≤ Finset.univ.sum (fun _ : SigmaEmbIntoGraph σ' G =>
                C₁ * (denom_F : ℝ)) := by
              apply Finset.sum_le_sum; intro θ _; exact h_per_theta θ
          _ = (Fintype.card (SigmaEmbIntoGraph σ' G) : ℝ) * C₁ * (denom_F : ℝ) := by
              simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
      -- Step 4: Bound numSigmaEmb using hC₂.
      -- numSigmaEmb σ' G ≈ inducedCount emptyType σ'.toFlag.forget G.
      -- We bound numSigmaEmb directly: the map SigmaEmbIntoGraph → InducedEmbedding
      -- is an injection, so numSigmaEmb ≤ inducedCount.
      -- From hC₂: inducedCount emptyType σ'.toFlag.forget G / C(Δ, |σ'|) ≤ C₂
      -- ⟹ numSigmaEmb σ' G ≤ C₂ * C(Δ, |σ'|)
      have h_sigma_count : (Fintype.card (SigmaEmbIntoGraph σ' G) : ℝ) ≤
          C₂ * (denom_σ : ℝ) := by
        -- Each SigmaEmbIntoGraph gives an InducedEmbedding of σ'.toFlag.forget into G.
        -- This gives numSigmaEmb σ' G ≤ inducedCount emptyType σ'.toFlag.forget G.
        -- Then use hC₂.
        have h_le := hC₂ G hG
        unfold localDensity at h_le
        have hσFS : σ'.toFlag.forget.size - emptyType.size = σ'.size := by
          change σ'.size - 0 = σ'.size; omega
        rw [hσFS, ← hD_def] at h_le
        -- h_le now has Nat.choose D σ'.size in the denominator, which equals denom_σ.
        change (inducedCount emptyType σ'.toFlag.forget G : ℝ) / (denom_σ : ℝ) ≤ C₂ at h_le
        -- We need: card (SigmaEmbIntoGraph σ' G) ≤ inducedCount emptyType σ'.toFlag.forget G
        -- This follows from the natural injection SigmaEmbIntoGraph → InducedEmbedding.
        suffices h_card_le :
            (Fintype.card (SigmaEmbIntoGraph σ' G) : ℝ) ≤
            (inducedCount emptyType (σ'.toFlag.forget) G : ℝ) by
          calc (Fintype.card (SigmaEmbIntoGraph σ' G) : ℝ)
              ≤ (inducedCount emptyType (σ'.toFlag.forget) G : ℝ) := h_card_le
            _ ≤ C₂ * (denom_σ : ℝ) := by rwa [div_le_iff₀ hdenom_σ_pos] at h_le
        -- Injection: SigmaEmbIntoGraph σ' G → InducedEmbedding emptyType σ'.toFlag.forget G
        -- Given θ = (emb, hsize), produce InducedEmbedding with toFun = emb.toFun.
        apply Nat.cast_le.mpr
        unfold inducedCount
        apply Fintype.card_le_of_injective
          (fun θ : SigmaEmbIntoGraph σ' G =>
            (⟨fun i => θ.emb i, θ.emb.injective,
              fun u v h => (θ.emb.map_rel_iff').mpr h,
              fun u v _ hna h => hna ((θ.emb.map_rel_iff').mp h),
              fun i => Fin.elim0 i⟩ : InducedEmbedding emptyType (σ'.toFlag.forget) G))
        intro a b hab
        have h_eq := congr_arg InducedEmbedding.toFun hab
        -- h_eq : (fun i => a.emb i) = (fun i => b.emb i)
        have h_emb : a.emb = b.emb :=
          DFunLike.ext _ _ (fun i => congr_fun h_eq i)
        cases a; cases b; simp only at h_emb; subst h_emb; rfl
      -- Step 5: Combine the bounds.
      -- c(↓F'; G) ≤ Σ_θ c(F'; (G,θ)) ≤ numSigmaEmb * C₁ * C(Δ, |F'|-|σ'|)
      --           ≤ C₂ * C(Δ, |σ'|) * C₁ * C(Δ, |F'|-|σ'|)
      -- Denominator: C(Δ, |F'|)
      -- Ratio ≤ C₁ * C₂ * C(Δ, |σ'|) * C(Δ, |F'|-|σ'|) / C(Δ, |F'|)
      --       ≤ C₁ * C₂ * C(|F'|, |σ'|)²
      -- The last step uses the Vandermonde bound.
      have hF_split : σ'.size + (F'.size - σ'.size) = F'.size := Nat.add_sub_cancel' F'.hsize
      -- Step 5a: assemble the numerator bound.
      have h_count_bound :
          (inducedCount emptyType F'.forget G : ℝ) ≤
            C₁ * C₂ * (denom_σ : ℝ) * (denom_F : ℝ) := by
        calc (inducedCount emptyType F'.forget G : ℝ)
            ≤ (Finset.univ.sum fun θ : SigmaEmbIntoGraph σ' G =>
                (inducedCount σ' F' (sigmaFlagOfEmb θ) : ℝ)) := by
              exact_mod_cast h_decomp
          _ ≤ (Fintype.card (SigmaEmbIntoGraph σ' G) : ℝ) * C₁ * (denom_F : ℝ) :=
              h_sum_bound
          _ ≤ C₂ * (denom_σ : ℝ) * C₁ * (denom_F : ℝ) := by
              apply mul_le_mul_of_nonneg_right
              · exact mul_le_mul_of_nonneg_right h_sigma_count hC₁_nn
              · exact le_of_lt hdenom_F_pos
          _ = C₁ * C₂ * (denom_σ : ℝ) * (denom_F : ℝ) := by ring
      -- Step 5b: Vandermonde bound on binomial coefficients.
      have h_vandermonde : denom_σ * denom_F ≤
          Nat.choose F'.size σ'.size ^ 2 * denom := by
        have hab_le : σ'.size + (F'.size - σ'.size) ≤ D := by
          rw [hF_split]; exact hD_ge_F
        have := choose_mul_choose_le σ'.size (F'.size - σ'.size) D hab_le
        rwa [hF_split] at this
      -- Step 5c: Divide by denom.
      rw [div_le_iff₀ hdenom_pos]
      calc (inducedCount emptyType F'.forget G : ℝ)
          ≤ C₁ * C₂ * (denom_σ : ℝ) * (denom_F : ℝ) := h_count_bound
        _ = C₁ * C₂ * ((denom_σ : ℝ) * (denom_F : ℝ)) := by ring
        _ ≤ C₁ * C₂ * ((Nat.choose F'.size σ'.size : ℝ) ^ 2 * (denom : ℝ)) := by
            apply mul_le_mul_of_nonneg_left
            · exact_mod_cast h_vandermonde
            · exact mul_nonneg hC₁_nn hC₂_nn
        _ = C₁ * C₂ * K * (denom : ℝ) := by ring

/-! ### Iterated label extensions

Substrate for the overlap decomposition in `bounded_density_any_labelling`.
The combined extended type and flag (defined via `Fin.append`, not by
iterating `LabelExtension`) provide a convenient combinatorial structure;
the corresponding locality theorem is documented as future work in
the development notes. -/

/-- After one label extension at an unlabelled vertex, the extended flag is
    local.  This is just `IsLocalFlag.extensions` with a convenient wrapper. -/
private theorem single_extension_local
    {σ : FlagType} {F : Flag σ} {𝒢 : GraphClass} {Δ : GraphParam}
    (h : IsLocalFlag σ F 𝒢 Δ) (v : Fin F.size) (hv : v ∉ Set.range F.embedding) :
    IsLocalFlag (LabelExtension.extendedType ⟨v, hv⟩)
      (LabelExtension.extendedFlag ⟨v, hv⟩) 𝒢 Δ :=
  h.extensions ⟨v, hv⟩

/-- Combined vertex map for k additional labels: the σ-embedding followed by
    k additional vertices given by `vs`. Maps `Fin (σ.size + k) → Fin F.size`
    via `Fin.append` (first σ.size positions through F.embedding, last k through vs). -/
noncomputable def iterExtVertexMap {σ : FlagType} (F : Flag σ)
    (k : ℕ) (vs : Fin k → Fin F.size) : Fin (σ.size + k) → Fin F.size :=
  Fin.append (fun i => F.embedding i) vs

/-- The combined vertex map is injective when the new vertices are distinct
    from each other and from the σ-image. -/
theorem iterExtVertexMap_injective {σ : FlagType} (F : Flag σ)
    {k : ℕ} {vs : Fin k → Fin F.size}
    (hvs_inj : Function.Injective vs)
    (hvs_unlab : ∀ i, vs i ∉ Set.range F.embedding) :
    Function.Injective (iterExtVertexMap F k vs) := by
  intro a b hab
  unfold iterExtVertexMap at hab
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j =>
      rw [Fin.append_left, Fin.append_left] at hab
      exact congr_arg (Fin.castAdd k) (F.embedding.injective hab)
    | right j =>
      rw [Fin.append_left, Fin.append_right] at hab
      exact absurd ⟨i, hab⟩ (hvs_unlab j)
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      rw [Fin.append_right, Fin.append_left] at hab
      exact absurd ⟨j, hab.symm⟩ (hvs_unlab i)
    | right j =>
      rw [Fin.append_right, Fin.append_right] at hab
      exact congr_arg (Fin.natAdd σ.size) (hvs_inj hab)

/-- The combined extended type after labelling k additional vertices: size
    `σ.size + k`, graph the comap of F.graph by `iterExtVertexMap`. -/
noncomputable def iterExtType {σ : FlagType} (F : Flag σ)
    (k : ℕ) (vs : Fin k → Fin F.size) : FlagType where
  size := σ.size + k
  graph := F.graph.comap (iterExtVertexMap F k vs)

/-- F viewed as a flag of the combined extended type. -/
noncomputable def iterExtFlag {σ : FlagType} (F : Flag σ)
    (k : ℕ) (vs : Fin k → Fin F.size)
    (hvs_inj : Function.Injective vs)
    (hvs_unlab : ∀ i, vs i ∉ Set.range F.embedding) :
    Flag (iterExtType F k vs) where
  size := F.size
  graph := F.graph
  embedding := SimpleGraph.Embedding.comap
    ⟨iterExtVertexMap F k vs, iterExtVertexMap_injective F hvs_inj hvs_unlab⟩ F.graph
  hsize := by
    change σ.size + k ≤ F.size
    have h_inj := iterExtVertexMap_injective F hvs_inj hvs_unlab
    have := Fintype.card_le_of_injective _ h_inj
    simpa [Fintype.card_fin] using this

/-- Pointwise decomposition: appending `b : Fin (k+1) → α` is the same as
    appending `Fin.init b` and treating `b (Fin.last k)` as the new last
    element via `Fin.lastCases`. This is the key equation needed to relate
    `iterExtFlag F (k+1) vs` to a single `LabelExtension` step on
    `iterExtFlag F k (Fin.init vs)`. -/
theorem Fin.append_eq_lastCases_init {α : Type*} {m k : ℕ}
    (a : Fin m → α) (b : Fin (k + 1) → α) :
    (Fin.append a b : Fin (m + (k + 1)) → α) =
    Fin.lastCases (b (Fin.last k)) (Fin.append a (Fin.init b)) := by
  funext i
  induction i using Fin.addCases with
  | left j' =>
    rw [Fin.append_left]
    have h_eq : (Fin.castAdd (k+1) j' : Fin (m + (k+1))) =
        Fin.castSucc (Fin.castAdd k j') := by
      ext; simp
    rw [h_eq, Fin.lastCases_castSucc, Fin.append_left]
  | right j' =>
    induction j' using Fin.lastCases with
    | last =>
      rw [Fin.append_right]
      have h_eq : (Fin.natAdd m (Fin.last k) : Fin (m + (k+1))) =
          (Fin.last (m + k) : Fin (m + k + 1)) := by
        ext; simp
      simp [h_eq]
    | cast j'' =>
      rw [Fin.append_right]
      have h_eq : (Fin.natAdd m (Fin.castSucc j'') : Fin (m + (k+1))) =
          ((Fin.natAdd m j'').castSucc : Fin (m + k + 1)) := by
        ext; simp
      rw [h_eq, Fin.lastCases_castSucc, Fin.append_right]
      rfl

/-- Transport `IsLocalFlag` along a FlagType equality plus a HEq of flags. -/
theorem IsLocalFlag.transport {σ σ' : FlagType} {F : Flag σ} {F' : Flag σ'}
    {𝒢 : GraphClass} {Δ : GraphParam}
    (h_τ : σ = σ') (h_F : HEq F F')
    (h : IsLocalFlag σ F 𝒢 Δ) : IsLocalFlag σ' F' 𝒢 Δ := by
  subst h_τ
  have : F = F' := eq_of_heq h_F
  subst this
  exact h

private theorem fin_double_subst_eq {n m : ℕ} (h : n = m) (v : Fin m) :
    (h ▸ (h ▸ v : Fin n) : Fin m) = v := by
  cases h
  rfl

/-- `▸` on a size equality of `Fin` is the same as `Fin.cast`. -/
private theorem fin_subst_eq_cast {n m : ℕ} (h : n = m) (x : Fin n) :
    (h ▸ x : Fin m) = Fin.cast h x := by
  cases h; rfl

/-- **Iterated label extensions, existential form.** Given a local σ-flag F
    and k distinct unlabelled vertices `vs` of F, there exists an extended
    type `τ` of size `σ.size + k` and a corresponding local flag `F'` whose
    underlying graph is F's. The proof iterates `IsLocalFlag.extensions`,
    sidestepping any need to literally identify `F'` with a specific
    construction (avoiding HEq pain at k=0).

    The dependent `▸`-cancellation `h_F'_size ▸ h_F'_size ▸ v_F = v_F`
    (which blocked earlier sessions) is closed by the small helper
    `fin_double_subst_eq`. -/
private theorem chain_extensions_local
    {σ : FlagType} {F : Flag σ} {𝒢 : GraphClass} {Δ : GraphParam}
    (h : IsLocalFlag σ F 𝒢 Δ) :
    ∀ (k : ℕ) (vs : Fin k → Fin F.size),
      Function.Injective vs →
      (∀ i, vs i ∉ Set.range F.embedding) →
      ∃ (τ : FlagType) (F' : Flag τ) (h_size : F'.size = F.size),
        IsLocalFlag τ F' 𝒢 Δ ∧
        τ.size = σ.size + k ∧
        F'.graph = h_size ▸ F.graph ∧
        ∀ x : Fin F'.size, x ∈ Set.range F'.embedding →
          (h_size ▸ x : Fin F.size) ∈ Set.range F.embedding ∪ Set.range vs
  | 0, _, _, _ => ⟨σ, F, rfl, h, by omega, rfl, fun _ hx => Or.inl hx⟩
  | k+1, vs, hvs_inj, hvs_unlab => by
    obtain ⟨τ', F', h_F'_size, hF', h_τ'_size, h_F'_graph, h_F'_range⟩ :=
      chain_extensions_local h k (vs ∘ Fin.castSucc)
        (fun a b hab => Fin.castSucc_injective k (hvs_inj hab))
        (fun i => hvs_unlab _)
    let v_F : Fin F.size := vs (Fin.last k)
    let v : Fin F'.size := h_F'_size ▸ v_F
    have h_v_unlab : v ∉ Set.range F'.embedding := by
      intro h_in
      have h_x_in := h_F'_range v h_in
      rw [fin_double_subst_eq h_F'_size v_F] at h_x_in
      rcases h_x_in with h_emb | ⟨j, hj⟩
      · exact hvs_unlab _ h_emb
      · exact (Fin.castSucc_lt_last j).ne (hvs_inj hj.symm).symm
    let ext : LabelExtension τ' F' := ⟨v, h_v_unlab⟩
    refine ⟨ext.extendedType, ext.extendedFlag, h_F'_size, hF'.extensions ext,
      show τ'.size + 1 = σ.size + (k + 1) by omega, h_F'_graph, ?_⟩
    intro x hx
    rw [LabelExtension.range_extendedFlag_embedding] at hx
    rcases hx with hx_F' | hx_v
    · rcases h_F'_range x hx_F' with h_emb | ⟨j, hj⟩
      · exact Or.inl h_emb
      · exact Or.inr ⟨Fin.castSucc j, hj⟩
    · rw [Set.mem_singleton_iff] at hx_v
      subst hx_v
      exact Or.inr ⟨Fin.last k, (fin_double_subst_eq h_F'_size v_F).symm⟩

/-- **Step 2.B substrate**: Given a local σ-flag F and a τ-labelled flag G with
    G.forget = F.forget, there exists a chained extension F_ext of F that
    labels all τ-positions of G.  This is the "extend F at the (τ\σ)-positions"
    step of the Thesis §2 Lemma 2.6 overlap decomposition (cf.
    the development notes). -/
private theorem chain_extend_F_at_τ_minus_σ
    {σ : FlagType} {F : Flag σ} {𝒢 : GraphClass} {Δ : GraphParam}
    (hF : IsLocalFlag σ F 𝒢 Δ)
    {τ : FlagType} {G : Flag τ} (hG : G.forget = F.forget) :
    ∃ (σExt : FlagType) (F_ext : Flag σExt) (h_size_F : F_ext.size = F.size),
      IsLocalFlag σExt F_ext 𝒢 Δ ∧
      F_ext.graph = h_size_F ▸ F.graph ∧
      σExt.size ≤ σ.size + τ.size ∧
      τ.size ≤ σExt.size := by
  have hG_size : G.size = F.size := congrArg Flag.size hG
  let σPos : Finset (Fin F.size) := Finset.univ.image F.embedding
  let τPos : Finset (Fin F.size) :=
    Finset.univ.image (fun i : Fin τ.size => Fin.cast hG_size (G.embedding i))
  let τNotσ : Finset (Fin F.size) := τPos \ σPos
  let vs_F : Fin τNotσ.card → Fin F.size := τNotσ.orderEmbOfFin rfl
  have h_unlab : ∀ i, vs_F i ∉ Set.range F.embedding := fun i ⟨j, hj⟩ =>
    (Finset.mem_sdiff.mp (τNotσ.orderEmbOfFin_mem rfl i)).2
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)
  have h_τPos_card : τPos.card = τ.size := by
    change (Finset.univ.image _).card = _
    rw [Finset.card_image_of_injective _ (fun a b hab =>
      G.embedding.injective ((Fin.cast_injective _) hab))]
    exact Finset.card_fin _
  have h_σPos_card_le : σPos.card ≤ σ.size :=
    Finset.card_image_le.trans (le_of_eq (Finset.card_fin _))
  obtain ⟨σExt, F_ext, h_size, h_local, h_τExt_size, h_graph, _⟩ :=
    chain_extensions_local hF τNotσ.card vs_F (τNotσ.orderEmbOfFin rfl).injective h_unlab
  refine ⟨σExt, F_ext, h_size, h_local, h_graph, ?_, ?_⟩
  · rw [h_τExt_size]
    exact Nat.add_le_add_left
      ((Finset.card_le_card Finset.sdiff_subset).trans
        (Finset.card_image_le.trans (le_of_eq (Finset.card_fin _)))) _
  · rw [h_τExt_size]
    have h_τNotσ_lb : τPos.card - σPos.card ≤ τNotσ.card := by
      change τPos.card - σPos.card ≤ (τPos \ σPos).card
      have := Finset.le_card_sdiff σPos τPos
      omega
    omega

/-- **Step 2.C substrate**: Given a local ∅-flag σ.toFlag.forget, extend it
    at any `j ≤ σ.size` positions to get a `j`-type local flag.  Useful for
    the Thesis §2 Lemma 2.6 σ-emb count step. -/
private theorem chain_extend_σ_at_any_j
    {σ : FlagType} {𝒢 : GraphClass} {Δ : GraphParam}
    (hσ : IsLocalFlag emptyType σ.toFlag.forget 𝒢 Δ)
    (j : ℕ) (hj : j ≤ σ.size) :
    ∃ (jType : FlagType) (σ_j : Flag jType) (h_size_σ : σ_j.size = σ.size),
      IsLocalFlag jType σ_j 𝒢 Δ ∧
      σ_j.graph = h_size_σ ▸ σ.graph ∧
      jType.size = j := by
  let vs_σ : Fin j → Fin σ.size := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hj⟩
  have h_inj : Function.Injective vs_σ := fun _ _ h => Fin.ext (Fin.mk.inj h)
  have h_unlab : ∀ i, vs_σ i ∉ Set.range σ.toFlag.forget.embedding := by
    rintro i ⟨k, _⟩; exact Fin.elim0 k
  obtain ⟨jType, σ_j, h_size_σ, h_local, h_jType_size, h_graph, _⟩ :=
    chain_extensions_local hσ j vs_σ h_inj h_unlab
  refine ⟨jType, σ_j, h_size_σ, h_local, ?_, ?_⟩
  · -- σ_j.graph = h_size_σ ▸ σ.graph
    -- chain_extensions_local gives σ_j.graph = h_size_σ ▸ σ.toFlag.forget.graph,
    -- and σ.toFlag.forget.graph = σ.graph by definition.
    exact h_graph
  · -- jType.size = emptyType.size + j = 0 + j = j (emptyType.size = 0 by def)
    rw [h_jType_size]; simp [emptyType]

/-- **Phase 3.C substrate**: extend `σ.toFlag.forget` at a custom set of `j`
    σ-positions specified by an injective `vs_σ : Fin j → Fin σ.size`.
    Generalizes `chain_extend_σ_at_any_j` (which uses the first j positions).
    Used for the overlap-positioned σ_j needed by Lemma 2.6's tight bound.

    Now also exposes the **range invariant**: σ_j.embedding's image (cast to
    Fin σ.size) is contained in `vs_σ`'s image.  Needed for Step A of the
    final counting argument. -/
private theorem chain_extend_σ_at_positions
    {σ : FlagType} {𝒢 : GraphClass} {Δ : GraphParam}
    (hσ : IsLocalFlag emptyType σ.toFlag.forget 𝒢 Δ)
    {j : ℕ} (vs_σ : Fin j → Fin σ.size) (h_inj : Function.Injective vs_σ) :
    ∃ (jType : FlagType) (σ_j : Flag jType) (h_size_σ : σ_j.size = σ.size),
      IsLocalFlag jType σ_j 𝒢 Δ ∧
      σ_j.graph = h_size_σ ▸ σ.graph ∧
      jType.size = j ∧
      ∀ x : Fin σ_j.size, x ∈ Set.range σ_j.embedding →
        (h_size_σ ▸ x : Fin σ.size) ∈ Set.range vs_σ := by
  obtain ⟨jType, σ_j, h_size_σ, h_local, h_jType_size, h_graph, h_range⟩ :=
    chain_extensions_local hσ j vs_σ h_inj (fun _ ⟨k, _⟩ => Fin.elim0 k)
  refine ⟨jType, σ_j, h_size_σ, h_local, h_graph, by rw [h_jType_size]; simp [emptyType], ?_⟩
  intro x hx
  rcases h_range x hx with ⟨k, _⟩ | hvs
  · exact Fin.elim0 k
  · exact hvs

/-- **Phase 3.C convenience wrapper**: given F : Flag σ and G : Flag τ with
    G.forget = F.forget, extend σ.toFlag.forget at the j σ-positions whose
    F.embedding image is a τ-position of G.  This is the "overlap σ-positions"
    extension used by Lemma 2.6's tight bound. -/
private theorem chain_extend_σ_at_overlap
    {σ : FlagType} {F : Flag σ} {𝒢 : GraphClass} {Δ : GraphParam}
    (hσ : IsLocalFlag emptyType σ.toFlag.forget 𝒢 Δ)
    {τ : FlagType} {G : Flag τ} (hG : G.forget = F.forget) :
    ∃ (jType : FlagType) (σ_j : Flag jType) (h_size_σ : σ_j.size = σ.size),
      IsLocalFlag jType σ_j 𝒢 Δ ∧
      σ_j.graph = h_size_σ ▸ σ.graph ∧
      jType.size ≤ σ.size ∧
      σ.size + τ.size ≤ F.size + jType.size := by
  -- Note: the range invariant from chain_extend_σ_at_positions is also available
  -- via the underlying call but not exposed here. Use chain_extend_F_and_σ_with_overlap
  -- if you need it.
  have hG_size : G.size = F.size := congrArg Flag.size hG
  let σPos : Finset (Fin F.size) := Finset.univ.image F.embedding
  let τPos : Finset (Fin F.size) :=
    Finset.univ.image (fun i : Fin τ.size => Fin.cast hG_size (G.embedding i))
  let σOverlap : Finset (Fin σ.size) :=
    Finset.univ.filter (fun i => F.embedding i ∈ τPos)
  let vs_σ : Fin σOverlap.card → Fin σ.size := σOverlap.orderEmbOfFin rfl
  have h_τPos_card : τPos.card = τ.size := by
    change (Finset.univ.image _).card = _
    rw [Finset.card_image_of_injective _ (fun a b hab =>
      G.embedding.injective ((Fin.cast_injective _) hab))]
    exact Finset.card_fin _
  have h_σPos_card : σPos.card = σ.size := by
    change (Finset.univ.image _).card = _
    rw [Finset.card_image_of_injective _ F.embedding.injective]
    exact Finset.card_fin _
  have h_σOverlap_image : σOverlap.image F.embedding = σPos ∩ τPos := by
    ext x
    simp only [σPos, σOverlap, τPos, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_inter]
    refine ⟨fun ⟨i, hi_τ, hi_eq⟩ => ⟨⟨i, hi_eq⟩, hi_eq ▸ hi_τ⟩,
            fun ⟨⟨i, hi_eq⟩, hx_τ⟩ => ⟨i, hi_eq ▸ hx_τ, hi_eq⟩⟩
  have h_σOverlap_card : σOverlap.card = (σPos ∩ τPos).card := by
    rw [← h_σOverlap_image]
    exact (Finset.card_image_of_injective _ F.embedding.injective).symm
  have h_inc_exc : σPos.card + τPos.card = (σPos ∪ τPos).card + (σPos ∩ τPos).card :=
    Finset.card_union_add_card_inter σPos τPos |>.symm
  have h_union_le : (σPos ∪ τPos).card ≤ F.size :=
    (Finset.card_le_univ _).trans (le_of_eq (Finset.card_fin _))
  obtain ⟨jType, σ_j, h_size_σ, h_local, h_graph, h_jType_size, _⟩ :=
    chain_extend_σ_at_positions hσ vs_σ (σOverlap.orderEmbOfFin rfl).injective
  refine ⟨jType, σ_j, h_size_σ, h_local, h_graph,
    by rw [h_jType_size]; exact (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_fin _)),
    ?_⟩
  rw [h_jType_size, h_σOverlap_card, ← h_σPos_card, ← h_τPos_card]
  omega

/-- The Adj relation transports through `▸` on a size equality, becoming an
    Adj on the original graph after `Fin.cast`-ing the arguments. -/
private theorem simpleGraph_adj_subst {n m : ℕ} (h : n = m)
    (G : SimpleGraph (Fin m)) (x y : Fin n) :
    (h ▸ G : SimpleGraph (Fin n)).Adj x y ↔ G.Adj (Fin.cast h x) (Fin.cast h y) := by
  cases h
  rfl

/-- **Unified Phase 2.B+2.C+3.C step #1 helper**: produces F_ext (extending F at
    τ\σ-positions of G) and σ_j (extending σ at the σ∩τ overlap positions)
    *together*, with the tight size equality `σExt.size + jType.size = σ.size + τ.size`.
    This equality is essential for Vandermonde to apply with sum exactly `n - τ.size`. -/
private theorem chain_extend_F_and_σ_with_overlap
    {σ : FlagType} {F : Flag σ} {𝒢 : GraphClass} {Δ : GraphParam}
    (hF : IsLocalFlag σ F 𝒢 Δ)
    (hσ : IsLocalFlag emptyType σ.toFlag.forget 𝒢 Δ)
    {τ : FlagType} {G : Flag τ} (hG : G.forget = F.forget) :
    ∃ (σExt : FlagType) (F_ext : Flag σExt) (h_size_F : F_ext.size = F.size),
    ∃ (jType : FlagType) (σ_j : Flag jType) (h_size_σ : σ_j.size = σ.size),
      IsLocalFlag σExt F_ext 𝒢 Δ ∧
      F_ext.graph = h_size_F ▸ F.graph ∧
      IsLocalFlag jType σ_j 𝒢 Δ ∧
      σ_j.graph = h_size_σ ▸ σ.graph ∧
      σExt.size + jType.size = σ.size + τ.size ∧
      τ.size ≤ σExt.size ∧
      jType.size ≤ σ.size ∧
      -- Step B: σ_j.embedding's image, after cast to F-positions via F.embedding,
      -- consists of τ-positions of G (i.e., is in G.embedding's image after Fin.cast).
      (∀ x : Fin σ_j.size, x ∈ Set.range σ_j.embedding →
        ∃ k : Fin τ.size,
          F.embedding (h_size_σ ▸ x : Fin σ.size) =
            Fin.cast (congrArg Flag.size hG) (G.embedding k)) ∧
      -- Step E foundation: F_ext.embedding's image, after cast to F-positions, is
      -- contained in σ-positions of F (= F.embedding-image) ∪ τ-positions of F
      -- (= G.embedding-image after cast). Used in the per-fiber buildH equality.
      (∀ x : Fin F_ext.size, x ∈ Set.range F_ext.embedding →
        (h_size_F ▸ x : Fin F.size) ∈ Set.range F.embedding ∪
          Set.range (fun i : Fin τ.size =>
            Fin.cast (show G.size = F.size from congrArg Flag.size hG)
              (G.embedding i))) := by
  have hG_size : G.size = F.size := congrArg Flag.size hG
  let σPos : Finset (Fin F.size) := Finset.univ.image F.embedding
  let τPos : Finset (Fin F.size) :=
    Finset.univ.image (fun i : Fin τ.size => Fin.cast hG_size (G.embedding i))
  let τNotσ : Finset (Fin F.size) := τPos \ σPos
  let σOverlap : Finset (Fin σ.size) :=
    Finset.univ.filter (fun i => F.embedding i ∈ τPos)
  let vs_F : Fin τNotσ.card → Fin F.size := τNotσ.orderEmbOfFin rfl
  let vs_σ : Fin σOverlap.card → Fin σ.size := σOverlap.orderEmbOfFin rfl
  have h_unlab_F : ∀ i, vs_F i ∉ Set.range F.embedding := fun i ⟨j, hj⟩ =>
    (Finset.mem_sdiff.mp (τNotσ.orderEmbOfFin_mem rfl i)).2
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)
  have h_τPos_card : τPos.card = τ.size := by
    change (Finset.univ.image _).card = _
    rw [Finset.card_image_of_injective _ (fun a b hab =>
      G.embedding.injective ((Fin.cast_injective _) hab))]
    exact Finset.card_fin _
  have h_σPos_card : σPos.card = σ.size := by
    change (Finset.univ.image _).card = _
    rw [Finset.card_image_of_injective _ F.embedding.injective]
    exact Finset.card_fin _
  have h_σOverlap_image : σOverlap.image F.embedding = σPos ∩ τPos := by
    ext x
    simp only [σPos, σOverlap, τPos, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_inter]
    refine ⟨fun ⟨i, hi_τ, hi_eq⟩ => ⟨⟨i, hi_eq⟩, hi_eq ▸ hi_τ⟩,
            fun ⟨⟨i, hi_eq⟩, hx_τ⟩ => ⟨i, hi_eq ▸ hx_τ, hi_eq⟩⟩
  have h_σOverlap_card : σOverlap.card = (σPos ∩ τPos).card := by
    rw [← h_σOverlap_image]
    exact (Finset.card_image_of_injective _ F.embedding.injective).symm
  have h_τNotσ_card : τNotσ.card + (σPos ∩ τPos).card = τPos.card := by
    change (τPos \ σPos).card + (σPos ∩ τPos).card = τPos.card
    rw [Finset.inter_comm σPos τPos]
    exact Finset.card_sdiff_add_card_inter τPos σPos
  obtain ⟨σExt, F_ext, h_size_F, h_local_F, h_τExt_size, h_F_graph, h_F_ext_range⟩ :=
    chain_extensions_local hF τNotσ.card vs_F (τNotσ.orderEmbOfFin rfl).injective h_unlab_F
  obtain ⟨jType, σ_j, h_size_σ, h_local_σ, h_σ_graph, h_jType_size, h_σ_j_range⟩ :=
    chain_extend_σ_at_positions hσ vs_σ (σOverlap.orderEmbOfFin rfl).injective
  refine ⟨σExt, F_ext, h_size_F, jType, σ_j, h_size_σ, h_local_F, h_F_graph,
    h_local_σ, h_σ_graph, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_τExt_size, h_jType_size, h_σOverlap_card]
    have h_assoc : σ.size + τNotσ.card + (σPos ∩ τPos).card =
        σ.size + (τNotσ.card + (σPos ∩ τPos).card) := by ring
    rw [h_assoc, h_τNotσ_card, h_τPos_card]
  · rw [h_τExt_size]
    have h_inter_le : (σPos ∩ τPos).card ≤ σ.size :=
      h_σPos_card ▸ Finset.card_le_card Finset.inter_subset_left
    rw [show τNotσ.card = τPos.card - (σPos ∩ τPos).card from by
          have := h_τNotσ_card; omega, h_τPos_card]
    omega
  · rw [h_jType_size]
    exact (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_fin _))
  · -- Step B: overlap bridge.
    intro x hx
    obtain ⟨i_overlap, hi_overlap⟩ := h_σ_j_range x hx
    obtain ⟨k, _, hk_eq⟩ := Finset.mem_image.mp
      (Finset.mem_filter.mp (σOverlap.orderEmbOfFin_mem rfl i_overlap)).2
    exact ⟨k, by rw [← hi_overlap]; exact hk_eq.symm⟩
  · -- Step E foundation: F_ext.embedding range ⊂ σ-positions ∪ τ-positions.
    intro x hx
    rcases h_F_ext_range x hx with h_emb | ⟨i, hi⟩
    · exact Or.inl h_emb
    · obtain ⟨k, _, hk_eq⟩ := Finset.mem_image.mp
        (Finset.mem_sdiff.mp (τNotσ.orderEmbOfFin_mem rfl i)).1
      exact Or.inr ⟨k, by rw [← hi]; exact hk_eq⟩

/-- Two flags with equal forgets have equal graphs (up to `Fin.cast`). -/
private theorem flag_graph_heq_of_forget_eq
    {σ τ : FlagType} {F : Flag σ} {G : Flag τ}
    (hG : G.forget = F.forget) : HEq G.graph F.graph := by
  have h := hG
  simp only [Flag.forget, Flag.mk.injEq] at h
  exact h.2.1

/-- Adj-iff transports through HEq + size equality (standalone form). -/
private theorem heq_simpleGraph_adj_iff {n m : ℕ} (h_size : n = m)
    {G : SimpleGraph (Fin n)} {F : SimpleGraph (Fin m)}
    (h_heq : HEq G F) (p q : Fin m) :
    F.Adj p q ↔ G.Adj (Fin.cast h_size.symm p) (Fin.cast h_size.symm q) := by
  cases h_size
  cases (eq_of_heq h_heq)
  rfl

/-- **Universal τ-emb agreement on τ-positions**: any two τ-embs g₁, g₂ of G
    into H agree on G's τ-labelled vertices (= G.embedding's image), since
    both equal H.embedding there.  Building block for the universal h_compat
    needed in the per-H counting argument. -/
private theorem tauEmbs_agree_on_τ_positions
    {τ : FlagType} {G H : Flag τ}
    (g₁ g₂ : InducedEmbedding τ G H) (k : Fin τ.size) :
    g₁.toFun (G.embedding k) = g₂.toFun (G.embedding k) := by
  rw [g₁.compat k, g₂.compat k]

/-- Adj-iff between two flags with equal forgets, after `Fin.cast`. -/
private theorem flag_adj_iff_of_forget_eq
    {σ τ : FlagType} {F : Flag σ} {G : Flag τ}
    (hG : G.forget = F.forget) (p q : Fin F.size) :
    F.graph.Adj p q ↔
    G.graph.Adj (Fin.cast (congrArg Flag.size hG).symm p)
                (Fin.cast (congrArg Flag.size hG).symm q) :=
  heq_simpleGraph_adj_iff (congrArg Flag.size hG) (flag_graph_heq_of_forget_eq hG) p q

/-- Adj-iff between F_ext.graph and F.graph after Fin.cast on the size eq. -/
private theorem F_ext_adj_iff_F_adj
    {σExt : FlagType} {F_ext : Flag σExt} {σ : FlagType} {F : Flag σ}
    (h_size_F : F_ext.size = F.size)
    (h_F_ext_graph : F_ext.graph = h_size_F ▸ F.graph)
    (u v : Fin F_ext.size) :
    F_ext.graph.Adj u v ↔ F.graph.Adj (Fin.cast h_size_F u) (Fin.cast h_size_F v) := by
  rw [h_F_ext_graph]; exact simpleGraph_adj_subst h_size_F F.graph u v

/-- **Phase 3.A piece**: the underlying function for the σExt-emb of F_ext into
    H constructed from a τ-emb f : G ↪ H.  Composes F_ext.embedding (σExt → F)
    with size casts to bridge F → G → H, then applies f.  Used in the Lemma 2.6
    overlap decomposition. -/
private noncomputable def tauEmbToSigmaExtFun
    {σ : FlagType} {F : Flag σ}
    {τ : FlagType} {G : Flag τ} (hG : G.forget = F.forget)
    {σExt : FlagType} {F_ext : Flag σExt}
    (h_size_F : F_ext.size = F.size)
    {H : Flag τ} (f : InducedEmbedding τ G H) :
    Fin σExt.size → Fin H.size :=
  fun i =>
    f.toFun (Fin.cast (congrArg Flag.size hG).symm
      (Fin.cast h_size_F (F_ext.embedding i)))

/-- The function from `tauEmbToSigmaExtFun` is injective. -/
private theorem tauEmbToSigmaExtFun_injective
    {σ : FlagType} {F : Flag σ}
    {τ : FlagType} {G : Flag τ} (hG : G.forget = F.forget)
    {σExt : FlagType} {F_ext : Flag σExt}
    (h_size_F : F_ext.size = F.size)
    {H : Flag τ} (f : InducedEmbedding τ G H) :
    Function.Injective (tauEmbToSigmaExtFun hG h_size_F f) := fun a b hab => by
  unfold tauEmbToSigmaExtFun at hab
  exact F_ext.embedding.injective <|
    (Fin.cast_injective _) ((Fin.cast_injective _) (f.injective hab))

/-- The function from `tauEmbToSigmaExtFun` is an induced graph embedding. -/
private theorem tauEmbToSigmaExtFun_induced
    {σ : FlagType} {F : Flag σ}
    {τ : FlagType} {G : Flag τ} (hG : G.forget = F.forget)
    {σExt : FlagType} {F_ext : Flag σExt}
    (h_size_F : F_ext.size = F.size)
    (h_F_ext_graph : F_ext.graph = h_size_F ▸ F.graph)
    {H : Flag τ} (f : InducedEmbedding τ G H) :
    ∀ a b : Fin σExt.size, σExt.graph.Adj a b ↔
      H.graph.Adj (tauEmbToSigmaExtFun hG h_size_F f a)
                  (tauEmbToSigmaExtFun hG h_size_F f b) := fun a b => by
  unfold tauEmbToSigmaExtFun
  set p : Fin G.size := Fin.cast (congrArg Flag.size hG).symm
    (Fin.cast h_size_F (F_ext.embedding a))
  set q : Fin G.size := Fin.cast (congrArg Flag.size hG).symm
    (Fin.cast h_size_F (F_ext.embedding b))
  have h45 : G.graph.Adj p q ↔ H.graph.Adj (f.toFun p) (f.toFun q) := by
    refine ⟨f.map_adj p q, fun h_h => ?_⟩
    by_contra h_ng
    by_cases h_pq : p = q
    · rw [h_pq] at h_h; exact (SimpleGraph.irrefl _) h_h
    · exact f.map_non_adj p q h_pq h_ng h_h
  exact F_ext.embedding.map_rel_iff'.symm.trans
    ((F_ext_adj_iff_F_adj h_size_F h_F_ext_graph _ _).trans
      ((flag_adj_iff_of_forget_eq hG _ _).trans h45))

/-- **Phase 3.A**: build the σExt-Flag-of-H from a τ-emb f.  The embedding
    composes `F_ext.embedding ∘ Fin.cast h_size_F ∘ Fin.cast hG_size.symm ∘ f.toFun`.
    Used in the Lemma 2.6 overlap decomposition: each τ-emb f : G ↪ H gives an
    σExt-emb of F_ext into this constructed Flag σExt of H. -/
private noncomputable def buildHFlagFromTauEmb
    {σ : FlagType} {F : Flag σ}
    {τ : FlagType} {G : Flag τ} (hG : G.forget = F.forget)
    {σExt : FlagType} {F_ext : Flag σExt}
    (h_size_F : F_ext.size = F.size)
    (h_F_ext_graph : F_ext.graph = h_size_F ▸ F.graph)
    {H : Flag τ} (f : InducedEmbedding τ G H) :
    Flag σExt where
  size := H.size
  graph := H.graph
  embedding :=
    { toFun := tauEmbToSigmaExtFun hG h_size_F f
      inj' := tauEmbToSigmaExtFun_injective hG h_size_F f
      map_rel_iff' := fun {a b} =>
        (tauEmbToSigmaExtFun_induced hG h_size_F h_F_ext_graph f a b).symm }
  hsize := by
    have h_inj := tauEmbToSigmaExtFun_injective hG h_size_F f
    have := Fintype.card_le_of_injective _ h_inj
    simpa [Fintype.card_fin] using this

/-- **Step D substrate**: from a τ-emb g : G ↪ H, produce a σ-emb of σ.graph
    into H.forget.graph by composing F.embedding with g.toFun (via Fin.cast).
    Used to extract the σ-component of g for the fiber-decomposition counting. -/
private noncomputable def θFromTauEmb
    {σ : FlagType} {F : Flag σ}
    {τ : FlagType} {G : Flag τ} (hG : G.forget = F.forget)
    {H : Flag τ} (g : InducedEmbedding τ G H) :
    SigmaEmbIntoGraph σ H.forget where
  emb :=
    { toFun := fun s => g.toFun (Fin.cast (congrArg Flag.size hG).symm (F.embedding s))
      inj' := fun a b hab =>
        F.embedding.injective ((Fin.cast_injective _) (g.injective hab))
      map_rel_iff' := fun {a b} => by
        set p := Fin.cast (congrArg Flag.size hG).symm (F.embedding a)
        set q := Fin.cast (congrArg Flag.size hG).symm (F.embedding b)
        have h34 : G.graph.Adj p q ↔ H.graph.Adj (g.toFun p) (g.toFun q) := by
          refine ⟨g.map_adj p q, fun h_h => ?_⟩
          by_contra h_ng
          by_cases h_pq : p = q
          · rw [h_pq] at h_h; exact (SimpleGraph.irrefl _) h_h
          · exact g.map_non_adj p q h_pq h_ng h_h
        change H.graph.Adj _ _ ↔ σ.graph.Adj a b
        exact h34.symm.trans
          ((flag_adj_iff_of_forget_eq hG _ _).symm.trans F.embedding.map_rel_iff') }
  hsize := by
    have h3 : G.size ≤ H.size := by
      simpa [Fintype.card_fin] using Fintype.card_le_of_injective _ g.injective
    change σ.size ≤ H.size
    have h1 : σ.size ≤ F.size := F.hsize
    have h2 : F.size = G.size := (congrArg Flag.size hG).symm
    omega

/-- **Phase 3.B**: from a τ-emb f : G ↪ H, produce an σExt-emb of F_ext into
    `buildHFlagFromTauEmb ... f`.  This is the "f as σExt-emb" step of the
    Lemma 2.6 overlap decomposition. -/
private noncomputable def tauEmbToInducedEmbFExt
    {σ : FlagType} {F : Flag σ}
    {τ : FlagType} {G : Flag τ} (hG : G.forget = F.forget)
    {σExt : FlagType} {F_ext : Flag σExt}
    (h_size_F : F_ext.size = F.size)
    (h_F_ext_graph : F_ext.graph = h_size_F ▸ F.graph)
    {H : Flag τ} (f : InducedEmbedding τ G H) :
    InducedEmbedding σExt F_ext
      (buildHFlagFromTauEmb hG h_size_F h_F_ext_graph f) where
  toFun x := f.toFun (Fin.cast (congrArg Flag.size hG).symm (Fin.cast h_size_F x))
  injective := by
    intro a b hab
    have h1 := f.injective hab
    have h2 := (Fin.cast_injective _) h1
    exact (Fin.cast_injective _) h2
  map_adj u v h_uv :=
    f.map_adj _ _ ((flag_adj_iff_of_forget_eq hG _ _).mp
      ((F_ext_adj_iff_F_adj h_size_F h_F_ext_graph u v).mp h_uv))
  map_non_adj u v hne hnadj h_h := by
    set p := Fin.cast (congrArg Flag.size hG).symm (Fin.cast h_size_F u)
    set q := Fin.cast (congrArg Flag.size hG).symm (Fin.cast h_size_F v)
    have hpq : p ≠ q := fun h_eq =>
      hne ((Fin.cast_injective _) ((Fin.cast_injective _) h_eq))
    have hG_adj : G.graph.Adj p q := by
      by_contra h_ng; exact f.map_non_adj p q hpq h_ng h_h
    exact hnadj ((F_ext_adj_iff_F_adj h_size_F h_F_ext_graph u v).mpr
      ((flag_adj_iff_of_forget_eq hG _ _).mpr hG_adj))
  compat i := rfl

/-- **Phase 3.C step #2**: build the jType-Flag-of-H from a τ-emb f, given σ_j
    (= σ extended at the overlap σ-positions).  The embedding composes
    `σ_j.embedding ∘ Fin.cast h_size_σ ∘ F.embedding ∘ Fin.cast hG_size.symm ∘ f.toFun`,
    landing jType-positions at the j overlap τ-positions of H. -/
private noncomputable def buildKFlagFromTauEmb
    {σ : FlagType} {F : Flag σ}
    {τ : FlagType} {G : Flag τ} (hG : G.forget = F.forget)
    {jType : FlagType} {σ_j : Flag jType}
    (h_size_σ : σ_j.size = σ.size)
    (h_σ_j_graph : σ_j.graph = h_size_σ ▸ σ.graph)
    {H : Flag τ} (f : InducedEmbedding τ G H) :
    Flag jType where
  size := H.size
  graph := H.graph
  embedding :=
    let toFun (i : Fin jType.size) : Fin H.size :=
      f.toFun (Fin.cast (congrArg Flag.size hG).symm
        (F.embedding (Fin.cast h_size_σ (σ_j.embedding i))))
    have h_inj : Function.Injective toFun := fun a b hab =>
      σ_j.embedding.injective ((Fin.cast_injective _) (F.embedding.injective
        ((Fin.cast_injective _) (f.injective hab))))
    { toFun := toFun
      inj' := h_inj
      map_rel_iff' := fun {a b} => by
        set u := Fin.cast h_size_σ (σ_j.embedding a)
        set v := Fin.cast h_size_σ (σ_j.embedding b)
        set p := Fin.cast (congrArg Flag.size hG).symm (F.embedding u)
        set q := Fin.cast (congrArg Flag.size hG).symm (F.embedding v)
        have h12 : σ_j.graph.Adj (σ_j.embedding a) (σ_j.embedding b) ↔
            jType.graph.Adj a b := σ_j.embedding.map_rel_iff'
        have h23 : σ_j.graph.Adj (σ_j.embedding a) (σ_j.embedding b) ↔
            σ.graph.Adj u v :=
          F_ext_adj_iff_F_adj (F_ext := σ_j) (F := σ.toFlag) h_size_σ h_σ_j_graph _ _
        have h34 : σ.graph.Adj u v ↔ F.graph.Adj (F.embedding u) (F.embedding v) :=
          F.embedding.map_rel_iff'.symm
        have h45 : F.graph.Adj (F.embedding u) (F.embedding v) ↔ G.graph.Adj p q :=
          flag_adj_iff_of_forget_eq hG _ _
        have h56 : G.graph.Adj p q ↔ H.graph.Adj (f.toFun p) (f.toFun q) := by
          refine ⟨f.map_adj p q, fun h_h => ?_⟩
          by_contra h_ng
          by_cases h_pq : p = q
          · rw [h_pq] at h_h; exact (SimpleGraph.irrefl _) h_h
          · exact f.map_non_adj p q h_pq h_ng h_h
        exact h56.symm.trans (h45.symm.trans (h34.symm.trans (h23.symm.trans h12))) }
  hsize := by
    have h_inj : Function.Injective (fun i : Fin jType.size =>
        f.toFun (Fin.cast (congrArg Flag.size hG).symm
          (F.embedding (Fin.cast h_size_σ (σ_j.embedding i))))) := fun a b hab =>
      σ_j.embedding.injective ((Fin.cast_injective _) (F.embedding.injective
        ((Fin.cast_injective _) (f.injective hab))))
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective _ h_inj

/-- **Phase 3.C step #3**: from a compatible σ-emb θ (compatible with H.embedding
    at the overlap σ-positions via the τ-emb f), produce an σ_j-emb of σ_j into
    `buildKFlagFromTauEmb ... f`.  This is the count bound's core injection:
    `# compatible θ ↪ # σ_j-embs σ_j → K_f`. -/
private noncomputable def compatibleSigmaEmbToSigmaJEmb
    {σ : FlagType} {F : Flag σ}
    {τ : FlagType} {G : Flag τ} (hG : G.forget = F.forget)
    {jType : FlagType} {σ_j : Flag jType}
    (h_size_σ : σ_j.size = σ.size)
    (h_σ_j_graph : σ_j.graph = h_size_σ ▸ σ.graph)
    {H : Flag τ} (f : InducedEmbedding τ G H)
    (θ : SigmaEmbIntoGraph σ H.forget)
    (h_compat : ∀ i : Fin jType.size,
      θ.emb (Fin.cast h_size_σ (σ_j.embedding i)) =
        f.toFun (Fin.cast (congrArg Flag.size hG).symm
          (F.embedding (Fin.cast h_size_σ (σ_j.embedding i))))) :
    InducedEmbedding jType σ_j
      (buildKFlagFromTauEmb hG h_size_σ h_σ_j_graph f) where
  toFun x := θ.emb (Fin.cast h_size_σ x)
  injective := fun _ _ hab => (Fin.cast_injective _) (θ.emb.injective hab)
  map_adj u v h_uv :=
    θ.emb.map_rel_iff'.mpr
      ((F_ext_adj_iff_F_adj (F_ext := σ_j) (F := σ.toFlag) h_size_σ h_σ_j_graph u v).mp h_uv)
  map_non_adj u v _ hnadj h_h :=
    hnadj ((F_ext_adj_iff_F_adj (F_ext := σ_j) (F := σ.toFlag) h_size_σ h_σ_j_graph u v).mpr
      (θ.emb.map_rel_iff'.mp h_h))
  compat i := h_compat i

/-- The σExt-flag built from a τ-emb has the same size as H. -/
@[simp] private theorem buildHFlagFromTauEmb_size
    {σ : FlagType} {F : Flag σ}
    {τ : FlagType} {G : Flag τ} (hG : G.forget = F.forget)
    {σExt : FlagType} {F_ext : Flag σExt}
    (h_size_F : F_ext.size = F.size)
    (h_F_ext_graph : F_ext.graph = h_size_F ▸ F.graph)
    {H : Flag τ} (f : InducedEmbedding τ G H) :
    (buildHFlagFromTauEmb hG h_size_F h_F_ext_graph f).size = H.size := rfl

/-- The K-flag built from a τ-emb has the same size as H. -/
@[simp] private theorem buildKFlagFromTauEmb_size
    {σ : FlagType} {F : Flag σ}
    {τ : FlagType} {G : Flag τ} (hG : G.forget = F.forget)
    {jType : FlagType} {σ_j : Flag jType}
    (h_size_σ : σ_j.size = σ.size)
    (h_σ_j_graph : σ_j.graph = h_size_σ ▸ σ.graph)
    {H : Flag τ} (f : InducedEmbedding τ G H) :
    (buildKFlagFromTauEmb hG h_size_σ h_σ_j_graph f).size = H.size := rfl

/-- The σExt-flag built from a τ-emb has the same forget as H.
    Useful for applying F_ext.bounded since the bound's hypothesis is on H.forget. -/
@[simp] private theorem buildHFlagFromTauEmb_forget
    {σ : FlagType} {F : Flag σ}
    {τ : FlagType} {G : Flag τ} (hG : G.forget = F.forget)
    {σExt : FlagType} {F_ext : Flag σExt}
    (h_size_F : F_ext.size = F.size)
    (h_F_ext_graph : F_ext.graph = h_size_F ▸ F.graph)
    {H : Flag τ} (f : InducedEmbedding τ G H) :
    (buildHFlagFromTauEmb hG h_size_F h_F_ext_graph f).forget = H.forget := rfl

/-- The K-flag (jType) built from a τ-emb has the same forget as H.
    Useful for applying σ_j.bounded since the bound's hypothesis is on H.forget. -/
@[simp] private theorem buildKFlagFromTauEmb_forget
    {σ : FlagType} {F : Flag σ}
    {τ : FlagType} {G : Flag τ} (hG : G.forget = F.forget)
    {jType : FlagType} {σ_j : Flag jType}
    (h_size_σ : σ_j.size = σ.size)
    (h_σ_j_graph : σ_j.graph = h_size_σ ▸ σ.graph)
    {H : Flag τ} (f : InducedEmbedding τ G H) :
    (buildKFlagFromTauEmb hG h_size_σ h_σ_j_graph f).forget = H.forget := rfl

/-- **Generalized bounded density (Thesis Lem 2.6, counting argument).**
    If F is a local σ-flag and ↓σ is a local ∅-flag, then any labelling of F's
    underlying graph has bounded density.

    **Proof sketch** (thesis §2, Lemma 2.6): By strong induction on `G.unlabelledSize`.
    Extensions use the IH (smaller unlabelled size). For bounded density, decompose
    τ'-embeddings through σ-embeddings grouped by overlap j = |im(f) ∩ im(σ-emb)|:
    - j = 0: combine σ and τ' labels into a (σ+τ')-flag, use IH + Vandermonde
    - j > 0: use j-fold extension chain of hσ + IH + Vandermonde
    Each case gives O(Δ^{n-t}) via `choose_mul_choose_le`.

    **Status**: Dead — not used by any main theorem. Its only consumer `localType_iff`
    (Thesis Lem 2.6 ↔) is unused in LocalFlagAlgebra, PentagonConjecture, and
    StrongEdgeColouring — the proof chain routes through `IsLocalFlag` directly.
    Was previously an axiom, then a sorry; now FULLY PROVED via overlap decomposition.

    The proof requires a sophisticated overlap decomposition: for each
    τ-embedding, classify by the overlap j = |im(τ-emb) ∩ im(σ-emb)| between
    the τ-labelled image and the σ-labelled image. Simple injection bounds
    (c(τ,G,H) ≤ c(∅,↓G,↓H)) give O(C(Δ,n)) which does not normalise to
    O(C(Δ,n-t)) when t > 0.

    See also: `bounded_density_forget` (the ∅-labelling special case, fully proved),
    `forget_count_le_sigma_sum` (the σ-decomposition injection, fully proved). -/
theorem bounded_density_any_labelling
    (σ : FlagType) (F : Flag σ) (𝒢 : GraphClass) (Δ : GraphParam)
    (hσ : IsLocalFlag emptyType σ.toFlag.forget 𝒢 Δ)
    (hF : IsLocalFlag σ F 𝒢 Δ)
    (τ : FlagType) (G : Flag τ)
    (hG : G.forget = F.forget) :
    IsBoundedDensity τ G 𝒢 Δ := by
  /-
  ## Proof outline (Thesis §2, Lemma 2.6 overlap decomposition)

  Let n = |G| = |F|, s = |σ|, t = |τ|.
  Let j = |Im(F.embedding) ∩ Im(G.embedding)| (overlap between σ-labels and τ-labels).

  **Step 1 (fibre bound):** Extend F at the t−j non-overlap τ-vertices (those in
  Im(G.embedding) \ Im(F.embedding)), iterating `hF.extensions` t−j times.
  The result F_ext is local at type σ_ext with |σ_ext| = s+t−j.
  From `F_ext.bounded`: IC(σ_ext, F_ext, H_ext) ≤ C_ext · C(Δ, n−s−t+j).

  **Step 2 (σ-embedding count):** Extend σ.toFlag.forget at the j overlap vertices,
  iterating `hσ.extensions` j times.  The result σ_j is local at a j-type.
  From `σ_j.bounded`: the number of σ-embeddings θ compatible with the
  τ-labelling (i.e. θ(a) = H.embedding(b) at overlap positions) is bounded
  by C_σ' · C(Δ, s−j).

  **Step 3 (counting decomposition):** For each τ-embedding f : G → H, the
  map θ_f = f ∘ (cast ∘ F.embedding) : σ → H.forget is a σ-embedding
  compatible with the τ-labelling.  Grouping by θ:
    IC(τ, G, H) ≤ Σ_{θ compatible} IC(σ_ext, F_ext, H_{ext,θ})
                ≤ (# compatible θ) · C_ext · C(Δ, n−s−t+j)
                ≤ C_σ' · C(Δ, s−j) · C_ext · C(Δ, n−s−t+j).

  **Step 4 (Vandermonde):** Since (s−j) + (n−s−t+j) = n−t, apply
  `choose_mul_choose_le` to get
    C(Δ, s−j) · C(Δ, n−s−t+j) ≤ C(n−t, s−j)² · C(Δ, n−t).

  **Result:**
    localDensity τ G H Δ = IC(τ,G,H) / C(Δ, n−t)
      ≤ C_σ' · C_ext · C(n−t, s−j)².

  ## Why it's hard to formalise

  The construction in Steps 1–3 requires:
  • Building iterated extension chains (LabelExtension applied t−j and j times)
  • Constructing the type isomorphism between σ_ext and the combined σ∪τ type
  • Dependent-type transport between Fin G.size and Fin F.size (from hG)
  • An injection InducedEmbedding τ G H → Σ θ, InducedEmbedding σ_ext F_ext (H,θ)

  Each piece is ~30–50 lines of Lean.  The naive injection bound
  IC(τ) ≤ IC(∅, F.forget, H.forget) is insufficient because
  C(Δ,n)/C(Δ,n−t) grows as O(Δ^t), so the overlap structure IS essential.

  ## Status

  Dead — only consumer `localType_iff` is unused by all main theorems.
  Kept as sorry for completeness of the Lemma 2.6 formalisation.

  See the development notes for a detailed plan
  (overlap decomposition, ~210 LOC, 4 phases).  The structural setup
  below extracts bounded constants and commits to the existential
  witness; the per-H bound itself remains the single open sorry.
  -/
  -- Extract sizes: G.size = F.size from G.forget = F.forget.
  have hG_size : G.size = F.size := congrArg Flag.size hG
  -- Build F_ext (chain extension at (τ\σ)-positions of G) and σ_j (chain
  -- extension at the σ∩τ overlap positions). These don't depend on H.
  obtain ⟨σExt, F_ext, h_size_F, jType, σ_j, h_size_σ,
          hF_ext, h_F_ext_graph, hσ_j, h_σ_j_graph,
          h_size_eq, h_τ_le_σExt, h_jType_le_σ, h_overlap_bridge, h_F_ext_range⟩ :=
    chain_extend_F_and_σ_with_overlap hF hσ hG
  -- σ.size + τ.size ≤ F.size + jType.size derives from h_size_eq + σExt.size ≤ F.size.
  have h_σ_τ_le : σ.size + τ.size ≤ F.size + jType.size := by
    rw [← h_size_eq]
    have h_σExt_le_F : σExt.size ≤ F.size := by rw [← h_size_F]; exact F_ext.hsize
    omega
  -- Bounded-density constants from F_ext and σ_j.
  obtain ⟨C₁_ext, hC₁_ext_nn, hC₁_ext⟩ := hF_ext.bounded
  obtain ⟨C₂', hC₂'_nn, hC₂'⟩ := hσ_j.bounded
  -- Witness constant: C₁_ext · C₂' · 4^|F| (loose Vandermonde upper bound).
  refine ⟨C₁_ext * C₂' * 4 ^ F.size, ?nonneg, ?bound⟩
  case nonneg =>
    refine mul_nonneg (mul_nonneg hC₁_ext_nn hC₂'_nn) ?_
    exact pow_nonneg (by norm_num : (0:ℝ) ≤ 4) _
  case bound =>
    intro H hH
    -- Goal: localDensity τ G H Δ ≤ C₁_ext * C₂' * 4 ^ F.size
    unfold localDensity
    set D : ℕ := Δ H.forget with hD_def
    -- Case split: if the denominator C(D, |G|-|τ|) = 0, the localDensity is 0.
    by_cases h_denom_zero : (Nat.choose D (G.size - τ.size) : ℝ) = 0
    · rw [h_denom_zero, div_zero]
      exact mul_nonneg (mul_nonneg hC₁_ext_nn hC₂'_nn)
        (pow_nonneg (by norm_num : (0:ℝ) ≤ 4) _)
    -- Nontrivial case: denom > 0. Convert to multiplicative form.
    have h_denom_pos : 0 < (Nat.choose D (G.size - τ.size) : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h_denom_zero)
    rw [div_le_iff₀ h_denom_pos]
    -- Goal: (inducedCount τ G H : ℝ) ≤ C₁_ext * C₂' * 4 ^ F.size *
    --        Nat.choose D (G.size - τ.size)
    -- Sub-case: inducedCount = 0 ⟹ trivially ≤ nonneg RHS.
    by_cases h_count_zero : inducedCount τ G H = 0
    · rw [h_count_zero, Nat.cast_zero]
      refine mul_nonneg (mul_nonneg (mul_nonneg hC₁_ext_nn hC₂'_nn) ?_) ?_
      · exact pow_nonneg (by norm_num : (0:ℝ) ≤ 4) _
      · exact Nat.cast_nonneg _
    -- Sub-case: inducedCount > 0. Extract a specific τ-emb f₀ to anchor the bound.
    have h_count_pos : 0 < inducedCount τ G H := Nat.pos_of_ne_zero h_count_zero
    have h_nonempty : Nonempty (InducedEmbedding τ G H) := by
      rw [show inducedCount τ G H = Fintype.card (InducedEmbedding τ G H) from rfl] at h_count_pos
      exact Fintype.card_pos_iff.mp h_count_pos
    obtain ⟨f₀⟩ := h_nonempty
    -- Bound denominators: F_ext.size - σExt.size ≤ D, σ_j.size - jType.size ≤ D.
    have h_D_ge_τ : G.size - τ.size ≤ D := by
      by_contra h_lt
      push_neg at h_lt
      exact h_denom_zero (by exact_mod_cast Nat.choose_eq_zero_of_lt h_lt)
    have h_F_ext_denom_le : F_ext.size - σExt.size ≤ D := by
      rw [h_size_F]
      calc F.size - σExt.size ≤ F.size - τ.size :=
            Nat.sub_le_sub_left h_τ_le_σExt _
        _ = G.size - τ.size := by rw [hG_size]
        _ ≤ D := h_D_ge_τ
    have h_σ_j_denom_le : σ_j.size - jType.size ≤ D := by
      rw [h_size_σ]
      have h_τ_le_F : τ.size ≤ F.size := by rw [← hG_size]; exact G.hsize
      calc σ.size - jType.size ≤ F.size - τ.size := by omega
        _ = G.size - τ.size := by rw [hG_size]
        _ ≤ D := h_D_ge_τ
    have h_σ_j_mult_bound :
        (inducedCount jType σ_j (buildKFlagFromTauEmb hG h_size_σ h_σ_j_graph f₀) : ℝ)
          ≤ C₂' * Nat.choose D (σ_j.size - jType.size) := by
      have h_lc :
          localDensity jType σ_j (buildKFlagFromTauEmb hG h_size_σ h_σ_j_graph f₀) Δ ≤ C₂' :=
        hC₂' _ (by rw [buildKFlagFromTauEmb_forget]; exact hH)
      unfold localDensity at h_lc
      rw [show Δ (buildKFlagFromTauEmb hG h_size_σ h_σ_j_graph f₀).forget = D from by
            rw [buildKFlagFromTauEmb_forget]] at h_lc
      exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.choose_pos h_σ_j_denom_le))).mp h_lc
    -- Apply Vandermonde to combine the two binomial factors.
    -- Sum: (σ_j.size - jType.size) + (F_ext.size - σExt.size) = G.size - τ.size
    -- via h_size_eq + h_size_σ + h_size_F + hG_size.
    have h_a_plus_b :
        (σ_j.size - jType.size) + (F_ext.size - σExt.size) = G.size - τ.size := by
      rw [h_size_σ, h_size_F, hG_size]
      have h_σExt_le_F : σExt.size ≤ F.size := by rw [← h_size_F]; exact F_ext.hsize
      omega
    have h_vandermonde :
        Nat.choose D (σ_j.size - jType.size) * Nat.choose D (F_ext.size - σExt.size) ≤
          Nat.choose ((σ_j.size - jType.size) + (F_ext.size - σExt.size))
            (σ_j.size - jType.size) ^ 2 *
          Nat.choose D ((σ_j.size - jType.size) + (F_ext.size - σExt.size)) := by
      apply choose_mul_choose_le
      rwa [h_a_plus_b]
    -- Bound C(...)² ≤ 4^F.size using Nat.choose_le_two_pow.
    have h_sum_le_F : (σ_j.size - jType.size) + (F_ext.size - σExt.size) ≤ F.size := by
      rw [h_a_plus_b, hG_size]; omega
    have h_choose_sq_le :
        Nat.choose ((σ_j.size - jType.size) + (F_ext.size - σExt.size))
            (σ_j.size - jType.size) ^ 2 ≤ 4 ^ F.size := by
      have h_choose_le : Nat.choose ((σ_j.size - jType.size) + (F_ext.size - σExt.size))
          (σ_j.size - jType.size) ≤ 2 ^ F.size := by
        exact le_trans (Nat.choose_le_two_pow _ _) (Nat.pow_le_pow_right (by norm_num) h_sum_le_F)
      calc Nat.choose _ _ ^ 2 ≤ (2 ^ F.size) ^ 2 := Nat.pow_le_pow_left h_choose_le 2
        _ = 4 ^ F.size := by
            rw [show (4:ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_mul, Nat.mul_comm]
    -- Step C: universal h_compat — for any τ-emb g, g and f₀ agree at the
    -- F-image of σ_j.embedding's image, since both equal H.embedding at the
    -- corresponding τ-position (by tauEmbs_agree_on_τ_positions and h_overlap_bridge).
    have h_universal_compat : ∀ (g : InducedEmbedding τ G H) (i : Fin jType.size),
        g.toFun (Fin.cast (congrArg Flag.size hG).symm
          (F.embedding (Fin.cast h_size_σ (σ_j.embedding i)))) =
        f₀.toFun (Fin.cast (congrArg Flag.size hG).symm
          (F.embedding (Fin.cast h_size_σ (σ_j.embedding i)))) := by
      intro g i
      obtain ⟨k, hk⟩ := h_overlap_bridge (σ_j.embedding i) ⟨i, rfl⟩
      rw [fin_subst_eq_cast] at hk
      rw [hk]
      simp only [Fin.cast_cast, Fin.cast_eq_self]
      exact tauEmbs_agree_on_τ_positions g f₀ k
    -- Step D: σ_j-emb extraction map. Each τ-emb g produces an σ_j-emb of σ_j into K_{f₀}.
    -- Use `let` (not `have`) so the definition is definitionally available for unfolding.
    let σjFromTauEmb : InducedEmbedding τ G H →
        InducedEmbedding jType σ_j
          (buildKFlagFromTauEmb hG h_size_σ h_σ_j_graph f₀) := fun g =>
      compatibleSigmaEmbToSigmaJEmb hG h_size_σ h_σ_j_graph f₀
        (θFromTauEmb hG g) (h_universal_compat g)
    -- Key fiber observation: within a σjFromTauEmb-fiber, all g's share the same θ_g
    -- (since compatibleSigmaEmbToSigmaJEmb's toFun captures θ.emb at all σ-positions
    -- via Fin.cast h_size_σ : Fin σ_j.size → Fin σ.size, which is bijective).
    -- Concretely: if σjFromTauEmb g₁ = σjFromTauEmb g₂, then g₁ and g₂ agree on
    -- F.embedding's image (the σ.size positions in G).
    have h_σjFromTauEmb_determines_θ :
        ∀ (g₁ g₂ : InducedEmbedding τ G H),
          σjFromTauEmb g₁ = σjFromTauEmb g₂ →
          ∀ s : Fin σ.size,
            g₁.toFun (Fin.cast (congrArg Flag.size hG).symm (F.embedding s)) =
              g₂.toFun (Fin.cast (congrArg Flag.size hG).symm (F.embedding s)) := fun
      g₁ g₂ h_eq s => by
        simpa using congrFun (congrArg (·.toFun) h_eq) (Fin.cast h_size_σ.symm s)
    -- Step E: buildH equality within a fiber. If σjFromTauEmb g₁ = σjFromTauEmb g₂,
    -- then buildH g₁ = buildH g₂ as Flag σExt. Proof: same size (H.size), same graph
    -- (H.graph), same hsize (Prop). The embeddings agree at every i : Fin σExt.size:
    -- F_ext.embedding i is in σ-positions ∪ τ-positions (by h_F_ext_range), and on
    -- σ-positions g₁,g₂ agree by determines_θ; on τ-positions both equal H.embedding.
    have h_buildH_eq_within_fiber : ∀ (g₁ g₂ : InducedEmbedding τ G H),
        σjFromTauEmb g₁ = σjFromTauEmb g₂ →
        buildHFlagFromTauEmb hG h_size_F h_F_ext_graph g₁ =
          buildHFlagFromTauEmb hG h_size_F h_F_ext_graph g₂ := by
      intro g₁ g₂ h_eq
      have h_θ := h_σjFromTauEmb_determines_θ g₁ g₂ h_eq
      -- Reduce Flag equality to embedding equality (size, graph, hsize match by rfl).
      -- The embedding's toFun is `tauEmbToSigmaExtFun hG h_size_F g`.
      have h_emb_eq : ∀ (i : Fin σExt.size),
          tauEmbToSigmaExtFun hG h_size_F g₁ i =
            tauEmbToSigmaExtFun hG h_size_F g₂ i := by
        intro i
        unfold tauEmbToSigmaExtFun
        -- Goal: g₁.toFun (cast hG.symm (cast h_size_F (F_ext.embedding i))) =
        --       g₂.toFun (cast hG.symm (cast h_size_F (F_ext.embedding i)))
        have h_in : F_ext.embedding i ∈ Set.range F_ext.embedding := ⟨i, rfl⟩
        have h_cases := h_F_ext_range _ h_in
        rcases h_cases with h_σ | h_τ
        · obtain ⟨s, hs⟩ := h_σ
          -- hs : F.embedding s = (h_size_F ▸ F_ext.embedding i)
          rw [fin_subst_eq_cast] at hs
          -- hs : F.embedding s = Fin.cast h_size_F (F_ext.embedding i)
          rw [← hs]
          exact h_θ s
        · obtain ⟨k, hk⟩ := h_τ
          rw [fin_subst_eq_cast] at hk
          rw [← hk]
          simp only [Fin.cast_cast, Fin.cast_eq_self]
          rw [g₁.compat k, g₂.compat k]
      -- Flag.mk equality reduces (size/graph/hsize match) to embedding equality;
      -- RelEmbedding.coe_fn_injective reduces that to toFun equality.
      unfold buildHFlagFromTauEmb
      congr 1
      exact RelEmbedding.coe_fn_injective (funext h_emb_eq)
    -- Step E.B (uniform fiber bound): for ANY representative g_b : InducedEmbedding τ G H,
    -- the count of F_ext-embeddings into buildH g_b is bounded by C₁_ext · choose D ...
    -- (uniform, not depending on g_b — uses hC₁_ext applied to buildH g_b's forget = H.forget).
    -- This is the per-fiber size bound; landed for use by the (residual) summation step.
    have h_F_ext_count_uniform_bound :
        ∀ (g_b : InducedEmbedding τ G H),
          (Fintype.card (InducedEmbedding σExt F_ext
            (buildHFlagFromTauEmb hG h_size_F h_F_ext_graph g_b)) : ℝ) ≤
            C₁_ext * Nat.choose D (F_ext.size - σExt.size) := fun g_b => by
      have h_lc :
          localDensity σExt F_ext
            (buildHFlagFromTauEmb hG h_size_F h_F_ext_graph g_b) Δ ≤ C₁_ext :=
        hC₁_ext _ (by rw [buildHFlagFromTauEmb_forget]; exact hH)
      unfold localDensity at h_lc
      rw [show Δ (buildHFlagFromTauEmb hG h_size_F h_F_ext_graph g_b).forget = D from by
            rw [buildHFlagFromTauEmb_forget]] at h_lc
      exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.choose_pos h_F_ext_denom_le))).mp h_lc
    -- Step E.C: per-fiber card bound via manual InducedEmbedding construction (no transport).
    classical
    have h_fiber_card_bound :
        ∀ (b : InducedEmbedding jType σ_j (buildKFlagFromTauEmb hG h_size_σ h_σ_j_graph f₀)),
        ((Finset.univ.filter (fun g : InducedEmbedding τ G H =>
            σjFromTauEmb g = b)).card : ℝ) ≤
          C₁_ext * Nat.choose D (F_ext.size - σExt.size) := by
      intro b
      by_cases h_ne : (Finset.univ.filter (fun g : InducedEmbedding τ G H =>
          σjFromTauEmb g = b)).Nonempty
      · -- Non-empty fiber: pick a representative g_b.
        obtain ⟨g_b, h_g_b_in⟩ := h_ne
        have hg_b : σjFromTauEmb g_b = b := (Finset.mem_filter.mp h_g_b_in).2
        -- Manual injection from fiber Subtype to InducedEmbedding σExt F_ext (buildH g_b).
        -- toFun/inj/adj/nonadj reuse tauEmbToInducedEmbFExt g; compat handled per-i via
        -- h_F_ext_range case split + determines_θ + τ-compat.
        let fiber_to_F_ext : { g : InducedEmbedding τ G H // σjFromTauEmb g = b } →
            InducedEmbedding σExt F_ext
              (buildHFlagFromTauEmb hG h_size_F h_F_ext_graph g_b) :=
          fun ⟨g, h_eq⟩ =>
            { toFun := fun x => g.toFun (Fin.cast (congrArg Flag.size hG).symm
                                  (Fin.cast h_size_F x))
              injective := (tauEmbToInducedEmbFExt hG h_size_F h_F_ext_graph g).injective
              map_adj := (tauEmbToInducedEmbFExt hG h_size_F h_F_ext_graph g).map_adj
              map_non_adj := (tauEmbToInducedEmbFExt hG h_size_F h_F_ext_graph g).map_non_adj
              compat := fun i => by
                change g.toFun (Fin.cast (congrArg Flag.size hG).symm
                                (Fin.cast h_size_F (F_ext.embedding i))) =
                     g_b.toFun (Fin.cast (congrArg Flag.size hG).symm
                                  (Fin.cast h_size_F (F_ext.embedding i)))
                rcases h_F_ext_range _ ⟨i, rfl⟩ with ⟨s, hs⟩ | ⟨k, hk⟩
                · rw [fin_subst_eq_cast] at hs; rw [← hs]
                  exact h_σjFromTauEmb_determines_θ g g_b (h_eq.trans hg_b.symm) s
                · rw [fin_subst_eq_cast] at hk; rw [← hk]
                  simp only [Fin.cast_cast, Fin.cast_eq_self, g.compat k, g_b.compat k] }
        have h_inj : Function.Injective fiber_to_F_ext := by
          rintro ⟨g₁, h₁⟩ ⟨g₂, h₂⟩ h_eq
          apply Subtype.ext
          have h_toFun : ∀ x : Fin F_ext.size,
              g₁.toFun (Fin.cast (congrArg Flag.size hG).symm (Fin.cast h_size_F x)) =
                g₂.toFun (Fin.cast (congrArg Flag.size hG).symm (Fin.cast h_size_F x)) :=
            fun x => congrFun (congrArg (·.toFun) h_eq) x
          have h_g_toFun : g₁.toFun = g₂.toFun := by
            funext y
            have hG_size : G.size = F.size := congrArg Flag.size hG
            simpa using h_toFun (Fin.cast h_size_F.symm (Fin.cast hG_size y))
          cases g₁; cases g₂; congr
        rw [show (Finset.univ.filter (fun g : InducedEmbedding τ G H => σjFromTauEmb g = b)).card
              = Fintype.card { g // σjFromTauEmb g = b } from
            (Fintype.card_subtype _).symm]
        calc (Fintype.card { g : InducedEmbedding τ G H // σjFromTauEmb g = b } : ℝ)
            ≤ (Fintype.card (InducedEmbedding σExt F_ext
                (buildHFlagFromTauEmb hG h_size_F h_F_ext_graph g_b)) : ℝ) := by
              exact_mod_cast Fintype.card_le_of_injective fiber_to_F_ext h_inj
          _ ≤ C₁_ext * Nat.choose D (F_ext.size - σExt.size) :=
              h_F_ext_count_uniform_bound g_b
      · -- Empty fiber.
        rw [Finset.not_nonempty_iff_eq_empty.mp h_ne]
        simp only [Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg hC₁_ext_nn (Nat.cast_nonneg _)
    -- Step E.D: aggregate the per-fiber bound to the multiplicative form via a single calc.
    -- inducedCount τ G H = ∑_b card(fiber b) ≤ (#σ_j-embs) · (C₁_ext · choose D _),
    -- then σ_j-emb bound + Vandermonde + 4^F.size majorisation + h_a_plus_b.
    have hC1C2_nn : (0 : ℝ) ≤ C₁_ext * C₂' := mul_nonneg hC₁_ext_nn hC₂'_nn
    calc (inducedCount τ G H : ℝ)
        = ∑ b : InducedEmbedding jType σ_j (buildKFlagFromTauEmb hG h_size_σ h_σ_j_graph f₀),
            ((Finset.univ.filter
              (fun g : InducedEmbedding τ G H => σjFromTauEmb g = b)).card : ℝ) := by
          have h_nat_eq :
              inducedCount τ G H =
                ∑ b ∈ (Finset.univ : Finset (InducedEmbedding jType σ_j
                        (buildKFlagFromTauEmb hG h_size_σ h_σ_j_graph f₀))),
                  (Finset.univ.filter
                    (fun g : InducedEmbedding τ G H => σjFromTauEmb g = b)).card :=
            Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ _)
          rw [show (inducedCount τ G H : ℝ) = ((inducedCount τ G H : ℕ) : ℝ) from rfl, h_nat_eq]
          push_cast; rfl
      _ ≤ ∑ _b : InducedEmbedding jType σ_j (buildKFlagFromTauEmb hG h_size_σ h_σ_j_graph f₀),
            (C₁_ext * Nat.choose D (F_ext.size - σExt.size)) :=
          Finset.sum_le_sum (fun b _ => h_fiber_card_bound b)
      _ = (inducedCount jType σ_j (buildKFlagFromTauEmb hG h_size_σ h_σ_j_graph f₀) : ℝ) *
            (C₁_ext * Nat.choose D (F_ext.size - σExt.size)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; rfl
      _ ≤ (C₂' * Nat.choose D (σ_j.size - jType.size)) *
            (C₁_ext * Nat.choose D (F_ext.size - σExt.size)) :=
          mul_le_mul_of_nonneg_right h_σ_j_mult_bound
            (mul_nonneg hC₁_ext_nn (Nat.cast_nonneg _))
      _ = C₁_ext * C₂' * ((Nat.choose D (σ_j.size - jType.size) : ℝ) *
            Nat.choose D (F_ext.size - σExt.size)) := by ring
      _ ≤ C₁_ext * C₂' * ((Nat.choose ((σ_j.size - jType.size) + (F_ext.size - σExt.size))
            (σ_j.size - jType.size) ^ 2 : ℝ) *
            Nat.choose D ((σ_j.size - jType.size) + (F_ext.size - σExt.size))) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast h_vandermonde) hC1C2_nn
      _ ≤ C₁_ext * C₂' * ((4 ^ F.size : ℝ) *
            Nat.choose D ((σ_j.size - jType.size) + (F_ext.size - σExt.size))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by exact_mod_cast h_choose_sq_le)
              (Nat.cast_nonneg _)) hC1C2_nn
      _ = C₁_ext * C₂' * 4 ^ F.size * Nat.choose D (G.size - τ.size) := by
          rw [h_a_plus_b]; ring

/-- **Build IsLocalFlag from bounded density at all labellings.**
    If every labelling of the underlying graph F₀ has bounded density, then
    F₀ is a local ∅-flag. Proof by strong induction on unlabelled size.
    Base case: when unlabelledSize = 0, there are no label extensions (the
    embedding is already surjective), so IsLocalFlag holds vacuously from
    IsBoundedDensity. Inductive step: IsBoundedDensity is immediate from
    h_all_bd, and each extension has strictly smaller unlabelled size. -/
theorem isLocalFlag_of_all_bounded
    (F₀ : Flag emptyType) (𝒢 : GraphClass) (Δ : GraphParam)
    (h_all_bd : ∀ (τ : FlagType) (G : Flag τ),
      G.forget = F₀.forget → IsBoundedDensity τ G 𝒢 Δ) :
    IsLocalFlag emptyType F₀ 𝒢 Δ := by
  suffices aux : ∀ n : ℕ, ∀ (τ : FlagType) (G : Flag τ),
      G.unlabelledSize ≤ n →
      (∀ (τ' : FlagType) (G' : Flag τ'),
        G'.forget = G.forget → IsBoundedDensity τ' G' 𝒢 Δ) →
      IsLocalFlag τ G 𝒢 Δ by
    exact aux F₀.unlabelledSize emptyType F₀ le_rfl h_all_bd
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro τ G hle h_bd
  refine IsLocalFlag.intro τ G 𝒢 Δ (h_bd τ G rfl) fun ext => ?_
  have hlt : ext.extendedFlag.unlabelledSize < G.unlabelledSize := by
    have hsz : τ.size < G.size := by
      by_contra h_ge; push_neg at h_ge
      have heq : G.size = τ.size := Nat.le_antisymm h_ge G.hsize
      exact ext.unlabelled
        (G.embedding.injective.surjective_of_finite (finCongr heq.symm) ext.vertex)
    exact ext.unlabelledSize_lt hsz
  apply ih ext.extendedFlag.unlabelledSize (lt_of_lt_of_le hlt hle)
    ext.extendedType ext.extendedFlag le_rfl
  -- ext.extendedFlag.forget and G.forget are definitionally equal
  -- (both Flag.mk G.size G.graph ⟨Fin.elim0,...⟩ (Nat.zero_le _))
  exact h_bd

/-- **Lemma 2.6**: A type σ is a local type if and only if σ itself
    (viewed as an ∅-flag) is a local ∅-flag.
    Not used by any main theorem; kept for completeness. -/
theorem localType_iff (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam) :
    IsLocalType σ 𝒢 Δ ↔ IsLocalFlag emptyType (σ.toFlag.forget) 𝒢 Δ := by
  constructor
  · -- Forward: If σ is a local type then ↓σ ∈ 𝒢^∅_loc.
    intro h
    exact h σ.toFlag (type_is_local σ 𝒢 Δ)
  · -- Reverse: If ↓σ is a local ∅-flag then σ is a local type (Thesis Lem 2.6, ⇐).
    --
    -- For any local σ-flag F, we show ↓F is a local ∅-flag by proving all
    -- labellings of ↓F have bounded density (via bounded_density_any_labelling),
    -- then applying isLocalFlag_of_all_bounded.
    intro hσ F hF
    exact isLocalFlag_of_all_bounded F.forget 𝒢 Δ
      (fun τ G hG => bounded_density_any_labelling σ F 𝒢 Δ hσ hF τ G hG)

/-- Lemma 2.6, easy direction: If σ is a local type then σ is a local ∅-flag.

    **Status**: Intentional standalone — Thesis Lemma 2.6 ⇒ direction;
    no consumer expected (kept for completeness). -/
theorem localType_imp_localEmptyFlag (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam)
    (h : IsLocalType σ 𝒢 Δ) :
    IsLocalFlag emptyType (σ.toFlag.forget) 𝒢 Δ := by
  -- σ ∈ 𝒢^σ_loc by type_is_local, so ↓σ ∈ 𝒢^∅_loc by definition of local type
  exact h σ.toFlag (type_is_local σ 𝒢 Δ)

/-! ## Induced Subflag Construction

Given a flag G and a finset S of vertices containing the σ-image,
construct the induced subflag on S. Used in the orbit-counting proof
of `triple_joint_factoring`. -/

/-- The induced subflag of G on a finset S of vertices containing the σ-image.
    The graph is pulled back via the canonical order-embedding `Fin S.card ↪o Fin G.size`,
    and the σ-embedding is transported accordingly. -/
noncomputable def Flag.inducedSubflag {σ : FlagType} (G : Flag σ)
    (S : Finset (Fin G.size))
    (hS : ∀ i : Fin σ.size, G.embedding i ∈ S)
    (hσ : σ.size ≤ S.card) : Flag σ :=
  let ι := S.orderEmbOfFin rfl
  let iso := S.orderIsoOfFin rfl
  let emb : Fin σ.size → Fin S.card := fun i => iso.symm ⟨G.embedding i, hS i⟩
  have h_ι_emb : ∀ i, ι (emb i) = G.embedding i := fun i => by
    change ↑(iso (iso.symm ⟨G.embedding i, hS i⟩)) = G.embedding i
    simp [OrderIso.apply_symm_apply]
  { size := S.card
    graph := G.graph.comap ι
    embedding :=
      ⟨⟨emb, fun i j h => G.embedding.injective (by rw [← h_ι_emb i, ← h_ι_emb j]; congr 1)⟩,
       fun {i j} => by
        change G.graph.Adj (ι (emb i)) (ι (emb j)) ↔ σ.graph.Adj i j
        rw [h_ι_emb, h_ι_emb]; exact G.embedding.map_rel_iff'⟩
    hsize := hσ }

/-- The canonical inclusion from an induced subflag back to G is an induced embedding. -/
noncomputable def Flag.inducedSubflag_incl {σ : FlagType} (G : Flag σ)
    (S : Finset (Fin G.size))
    (hS : ∀ i : Fin σ.size, G.embedding i ∈ S)
    (hσ : σ.size ≤ S.card) :
    InducedEmbedding σ (G.inducedSubflag S hS hσ) G where
  toFun := S.orderEmbOfFin rfl
  injective := (S.orderEmbOfFin rfl).injective
  map_adj _ _ h := h
  map_non_adj _ _ _ h := h
  compat i := by
    change (S.orderEmbOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨G.embedding i, hS i⟩) = G.embedding i
    change ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨G.embedding i, hS i⟩)) = G.embedding i
    simp [OrderIso.apply_symm_apply]

/-- The range of the inclusion embedding is exactly S (as a set). -/
theorem Flag.inducedSubflag_incl_range {σ : FlagType} (G : Flag σ)
    (S : Finset (Fin G.size))
    (hS : ∀ i : Fin σ.size, G.embedding i ∈ S)
    (hσ : σ.size ≤ S.card) :
    Set.range (G.inducedSubflag_incl S hS hσ).toFun = ↑S := by
  ext x
  simp only [Set.mem_range, Finset.mem_coe]
  constructor
  · rintro ⟨y, rfl⟩; exact Finset.orderEmbOfFin_mem S rfl y
  · intro hx
    exact ⟨(S.orderIsoOfFin rfl).symm ⟨x, hx⟩, by
      change ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨x, hx⟩)) = x
      simp [OrderIso.apply_symm_apply]⟩

/-- Restrict an InducedEmbedding e : F ↪ G to an InducedEmbedding F ↪ (G.inducedSubflag S)
    when the image of e is contained in S. -/
noncomputable def InducedEmbedding.restrictToSubflag {σ : FlagType} {F G : Flag σ}
    (e : InducedEmbedding σ F G)
    (S : Finset (Fin G.size))
    (hS : ∀ i : Fin σ.size, G.embedding i ∈ S)
    (hσ : σ.size ≤ S.card)
    (himg : ∀ x : Fin F.size, e.toFun x ∈ S) :
    InducedEmbedding σ F (G.inducedSubflag S hS hσ) where
  toFun x := (S.orderIsoOfFin rfl).symm ⟨e.toFun x, himg x⟩
  injective x y h := e.injective <| by
    simpa [Subtype.mk.injEq] using (S.orderIsoOfFin rfl).symm.injective h
  map_adj u v h := by
    have key : ∀ x, (S.orderEmbOfFin rfl)
        ((S.orderIsoOfFin rfl).symm ⟨e.toFun x, himg x⟩) = e.toFun x := fun x => by
      change ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨e.toFun x, himg x⟩)) = e.toFun x
      simp [OrderIso.apply_symm_apply]
    change G.graph.Adj _ _; rw [key u, key v]; exact e.map_adj u v h
  map_non_adj u v hne hnadj := by
    have key : ∀ x, (S.orderEmbOfFin rfl)
        ((S.orderIsoOfFin rfl).symm ⟨e.toFun x, himg x⟩) = e.toFun x := fun x => by
      change ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨e.toFun x, himg x⟩)) = e.toFun x
      simp [OrderIso.apply_symm_apply]
    change ¬G.graph.Adj _ _; rw [key u, key v]; exact e.map_non_adj u v hne hnadj
  compat i := by
    change (S.orderIsoOfFin rfl).symm ⟨e.toFun (F.embedding i), himg _⟩ =
         (S.orderIsoOfFin rfl).symm ⟨G.embedding i, hS i⟩
    congr 1; simp [e.compat]

/-- Composing restriction with inclusion recovers the original embedding. -/
theorem InducedEmbedding.restrictToSubflag_comp_incl {σ : FlagType} {F G : Flag σ}
    (e : InducedEmbedding σ F G)
    (S : Finset (Fin G.size))
    (hS : ∀ i : Fin σ.size, G.embedding i ∈ S)
    (hσ : σ.size ≤ S.card)
    (himg : ∀ x : Fin F.size, e.toFun x ∈ S) :
    ∀ x, (G.inducedSubflag_incl S hS hσ).toFun
      ((e.restrictToSubflag S hS hσ himg).toFun x) = e.toFun x := by
  intro x
  change ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨e.toFun x, himg x⟩)) = e.toFun x
  simp [OrderIso.apply_symm_apply]

/-! ## Generic Induced Subflag -/

/-- Induced subflag of a GenFlag on a vertex subset S containing the σ-image. -/
noncomputable def GenFlag.genInducedSubflag {R : RelUniverse} {σ : GenFlagType R} (G : GenFlag R σ)
    (S : Finset (Fin G.size))
    (hS : ∀ i : Fin σ.size, G.embedding i ∈ S)
    (hσ : σ.size ≤ S.card) : GenFlag R σ :=
  let ι := S.orderEmbOfFin rfl
  let iso := S.orderIsoOfFin rfl
  let emb : Fin σ.size → Fin S.card := fun i => iso.symm ⟨G.embedding i, hS i⟩
  { size := S.card
    str := R.comap ι G.str
    embedding := ⟨emb, fun {i j} h => G.embedding.injective (by
      have : (iso (emb i)).val = (iso (emb j)).val := congr_arg (fun x => (iso x).val) h
      simp only [emb, iso.apply_symm_apply] at this; exact this)⟩
    isInduced := by
      change R.comap emb (R.comap ι G.str) = σ.str
      rw [← R.comap_comp]
      have : (↑ι) ∘ emb = G.embedding := funext fun i => by
        change ↑(iso (iso.symm ⟨G.embedding i, hS i⟩)) = G.embedding i
        simp [OrderIso.apply_symm_apply]
      rw [this]; exact G.isInduced
    hsize := hσ }

/-- Canonical inclusion from genInducedSubflag back to G. -/
noncomputable def GenFlag.genInducedSubflag_incl {R : RelUniverse} {σ : GenFlagType R}
    (G : GenFlag R σ) (S : Finset (Fin G.size))
    (hS : ∀ i : Fin σ.size, G.embedding i ∈ S)
    (hσ : σ.size ≤ S.card) :
    GenInducedEmbedding R σ (G.genInducedSubflag S hS hσ) G where
  toFun := S.orderEmbOfFin rfl
  injective := (S.orderEmbOfFin rfl).injective
  isInduced := rfl
  compat i := by
    change (S.orderEmbOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨G.embedding i, hS i⟩) = G.embedding i
    change ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨G.embedding i, hS i⟩)) = G.embedding i
    simp [OrderIso.apply_symm_apply]

/-- Restrict a GenInducedEmbedding e : F → G to F → G.genInducedSubflag S when im(e) ⊆ S. -/
noncomputable def GenInducedEmbedding.genRestrictToSubflag {R : RelUniverse} {σ : GenFlagType R}
    {F G : GenFlag R σ} (e : GenInducedEmbedding R σ F G)
    (S : Finset (Fin G.size))
    (hS : ∀ i : Fin σ.size, G.embedding i ∈ S)
    (hσ : σ.size ≤ S.card)
    (himg : ∀ x : Fin F.size, e.toFun x ∈ S) :
    GenInducedEmbedding R σ F (G.genInducedSubflag S hS hσ) where
  toFun x := (S.orderIsoOfFin rfl).symm ⟨e.toFun x, himg x⟩
  injective x y h := e.injective <| by
    simpa [Subtype.mk.injEq] using (S.orderIsoOfFin rfl).symm.injective h
  isInduced := by
    change R.comap _ (R.comap (S.orderEmbOfFin rfl) G.str) = F.str
    rw [← R.comap_comp]
    have : (↑(S.orderEmbOfFin rfl)) ∘ (fun x => (S.orderIsoOfFin rfl).symm ⟨e.toFun x, himg x⟩) =
        e.toFun := funext fun x => by
      change ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨e.toFun x, himg x⟩)) = e.toFun x
      simp [OrderIso.apply_symm_apply]
    rw [this]; exact e.isInduced
  compat i := by
    change (S.orderIsoOfFin rfl).symm ⟨e.toFun (F.embedding i), himg _⟩ =
         (S.orderIsoOfFin rfl).symm ⟨G.embedding i, hS i⟩
    congr 1; simp [e.compat]

/-- Restriction composed with inclusion recovers original embedding. -/
theorem GenInducedEmbedding.genRestrictToSubflag_comp_incl {R : RelUniverse} {σ : GenFlagType R}
    {F G : GenFlag R σ} (e : GenInducedEmbedding R σ F G)
    (S : Finset (Fin G.size))
    (hS : ∀ i : Fin σ.size, G.embedding i ∈ S)
    (hσ : σ.size ≤ S.card)
    (himg : ∀ x : Fin F.size, e.toFun x ∈ S) :
    ∀ x, (G.genInducedSubflag_incl S hS hσ).toFun
      ((e.genRestrictToSubflag S hS hσ himg).toFun x) = e.toFun x := by
  intro x
  change ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨e.toFun x, himg x⟩)) = e.toFun x
  simp [OrderIso.apply_symm_apply]

/-! ## Generic Label Extensions and Locality

Generic versions of `LabelExtension`, `IsBoundedDensity`, and `IsLocalFlag`
parameterized by `RelUniverse`. -/

/-- A generic label extension: an unlabelled vertex of a generic flag. -/
structure GenLabelExtension {R : RelUniverse} {σ : GenFlagType R} (F : GenFlag R σ) where
  vertex : Fin F.size
  unlabelled : vertex ∉ Set.range F.embedding

/-- Map from Fin (σ.size + 1) into Fin F.size: σ-embedding + the extension vertex. -/
noncomputable def GenLabelExtension.vertexMap {R : RelUniverse} {σ : GenFlagType R}
    {F : GenFlag R σ} (ext : GenLabelExtension F) : Fin (σ.size + 1) → Fin F.size :=
  Fin.lastCases ext.vertex (fun i => F.embedding i)

/-- The vertex map of a generic label extension is injective. -/
theorem GenLabelExtension.vertexMap_injective {R : RelUniverse} {σ : GenFlagType R}
    {F : GenFlag R σ} (ext : GenLabelExtension F) :
    Function.Injective ext.vertexMap := by
  intro a b hab
  obtain (⟨i, rfl⟩ | rfl) := a.eq_castSucc_or_eq_last
  · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
    · simp only [vertexMap, Fin.lastCases_castSucc] at hab
      exact congr_arg Fin.castSucc (F.embedding.injective hab)
    · simp only [vertexMap, Fin.lastCases_castSucc, Fin.lastCases_last] at hab
      exact absurd ⟨i, hab⟩ ext.unlabelled
  · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
    · simp only [vertexMap, Fin.lastCases_castSucc, Fin.lastCases_last] at hab
      exact absurd ⟨j, hab.symm⟩ ext.unlabelled
    · rfl

/-- The extended type: σ with one more labelled vertex. -/
noncomputable def GenLabelExtension.extendedType {R : RelUniverse} {σ : GenFlagType R}
    {F : GenFlag R σ} (ext : GenLabelExtension F) : GenFlagType R where
  size := σ.size + 1
  str := R.comap ext.vertexMap F.str

/-- The flag F viewed with the extended type. -/
noncomputable def GenLabelExtension.extendedFlag {R : RelUniverse} {σ : GenFlagType R}
    {F : GenFlag R σ} (ext : GenLabelExtension F) : GenFlag R ext.extendedType where
  size := F.size
  str := F.str
  embedding := ⟨ext.vertexMap, ext.vertexMap_injective⟩
  isInduced := rfl
  hsize := by
    change σ.size + 1 ≤ F.size
    by_contra hle; push_neg at hle
    have hh : F.size = σ.size := Nat.le_antisymm (by omega) F.hsize
    exact ext.unlabelled
      (F.embedding.injective.surjective_of_finite (finCongr hh.symm) ext.vertex)

/-- Range of `ext.extendedFlag.embedding` = range of F.embedding ∪ {ext.vertex}. -/
theorem GenLabelExtension.range_extendedFlag_embedding {R : RelUniverse} {σ : GenFlagType R}
    {F : GenFlag R σ} (ext : GenLabelExtension F) :
    Set.range ext.extendedFlag.embedding =
      Set.range F.embedding ∪ {ext.vertex} := by
  ext x; simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi⟩
    obtain (⟨j, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
    · left
      change ext.vertexMap (Fin.castSucc j) = x at hi
      simp only [GenLabelExtension.vertexMap, Fin.lastCases_castSucc] at hi
      exact ⟨j, hi⟩
    · right
      change ext.vertexMap (Fin.last _) = x at hi
      simp only [GenLabelExtension.vertexMap, Fin.lastCases_last] at hi
      exact hi.symm
  · rintro (⟨j, rfl⟩ | rfl)
    · exact ⟨Fin.castSucc j, by simp [GenLabelExtension.extendedFlag, GenLabelExtension.vertexMap]⟩
    · exact ⟨Fin.last _, by simp [GenLabelExtension.extendedFlag, GenLabelExtension.vertexMap]⟩

/-- Generic local density. -/
noncomputable def genLocalDensity {R : RelUniverse} (σ : GenFlagType R)
    (F G : GenFlag R σ) (Δ : GenFlag R (GenFlagType.empty R) → ℕ) : ℝ :=
  (genInducedCount R σ F G : ℝ) / (Nat.choose (Δ G.forget) (F.size - σ.size) : ℝ)

/-- Generic bounded density. -/
def GenIsBoundedDensity {R : RelUniverse} (σ : GenFlagType R) (F : GenFlag R σ)
    (𝒢 : GenFlag R (GenFlagType.empty R) → Prop)
    (Δ : GenFlag R (GenFlagType.empty R) → ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ G : GenFlag R σ, 𝒢 G.forget →
    genLocalDensity σ F G Δ ≤ C

/-- Generic local flag (inductive). -/
inductive GenIsLocalFlag {R : RelUniverse} :
    (σ : GenFlagType R) → GenFlag R σ →
    (GenFlag R (GenFlagType.empty R) → Prop) →
    (GenFlag R (GenFlagType.empty R) → ℕ) → Prop where
  | intro (σ : GenFlagType R) (F : GenFlag R σ)
      (𝒢 : GenFlag R (GenFlagType.empty R) → Prop)
      (Δ : GenFlag R (GenFlagType.empty R) → ℕ) :
      GenIsBoundedDensity σ F 𝒢 Δ →
      (∀ ext : GenLabelExtension F,
        GenIsLocalFlag ext.extendedType ext.extendedFlag 𝒢 Δ) →
      GenIsLocalFlag σ F 𝒢 Δ

/-- Extract bounded density from a generic local flag proof. -/
theorem GenIsLocalFlag.bounded {R : RelUniverse} {σ : GenFlagType R}
    {F : GenFlag R σ} {𝒢 : GenFlag R (GenFlagType.empty R) → Prop}
    {Δ : GenFlag R (GenFlagType.empty R) → ℕ}
    (h : GenIsLocalFlag σ F 𝒢 Δ) : GenIsBoundedDensity σ F 𝒢 Δ := by
  cases h; assumption

/-- A generic local flag at every extension is again a generic local flag. -/
theorem GenIsLocalFlag.extensions {R : RelUniverse} {σ : GenFlagType R}
    {F : GenFlag R σ} {𝒢 : GenFlag R (GenFlagType.empty R) → Prop}
    {Δ : GenFlag R (GenFlagType.empty R) → ℕ}
    (h : GenIsLocalFlag σ F 𝒢 Δ) (ext : GenLabelExtension F) :
    GenIsLocalFlag ext.extendedType ext.extendedFlag 𝒢 Δ := by
  cases h with | intro _ _ _ _ _ h_ext => exact h_ext ext

end Davey2024
