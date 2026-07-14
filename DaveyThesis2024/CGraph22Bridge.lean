import DaveyThesis2024.CG22
import DaveyThesis2024.StrongEdgeColouring

/-!
# `CGraph22` ↔ `GenFlag CG22` bridge

Computable (`Bool`-valued) analog of `CG22` for `native_decide` verification,
mirroring `CGraph` ↔ `GenFlag CG2` in `CGraphBridge.lean`.

## Main definitions

* `CGraph22 n` — `Bool`-adjacency + `Fin 2`-vertex-colour + `Fin 2`-edge-colour
  on `Fin n`. All fields are computable for `native_decide` use.
* `CGraph22.toGenFlag` — `CGraph22 n → GenFlag CG22 (GenFlagType.empty CG22)`.
* `c22InducedCount` — computable count of induced colour-preserving embeddings.
* `c22InducedCount_eq_genInducedCount'` — bridge theorem: the computable count
  equals the abstract `genInducedCount CG22 ∅ F.toGenFlag G.toGenFlag` when
  both `CGraph22`s have symmetric, irreflexive `adj` (mirrors `CGraph` bridge).

The bridge for the edge-colour part requires only symmetry on `edgeCol`
(needed because `comap` pulls back `edgeCol` pointwise without any quotient).

## Smoke tests

A few small `CGraph22` examples at the bottom verify the structure builds
and `toGenFlag` typechecks.
-/

namespace Davey2024

open Finset

/-! ## Computable (2,2)-coloured graph -/

/-- A computable (2,2)-coloured graph on `Fin n` vertices.

    Fields use `Bool` for adjacency and `Fin 2` for both colourings so that
    `native_decide` can evaluate any function that consumes a `CGraph22`. -/
structure CGraph22 (n : Nat) where
  /-- Adjacency relation. Should be symmetric and irreflexive in practice;
      proofs that require this carry it as a side hypothesis (mirrors `CGraph`). -/
  adj : Fin n → Fin n → Bool
  /-- Vertex colouring. `0` = red, `1` = black by SEC convention. -/
  vertexCol : Fin n → Fin 2
  /-- Edge colouring. Should be symmetric (`edgeCol u v = edgeCol v u`);
      proofs that require this carry it as a side hypothesis. -/
  edgeCol : Fin n → Fin n → Fin 2

instance : Inhabited (CGraph22 n) :=
  ⟨⟨fun _ _ => false, fun _ => 0, fun _ _ => 0⟩⟩

/-- Computable count of (2,2)-coloured induced embeddings.

    Counts injective `f : Fin n₁ → Fin n₂` that preserve adjacency (Bool),
    vertex colour, and edge colour pointwise. Mirrors `cInducedCount` in
    `CGraphBridge.lean` with an extra edge-colour constraint. -/
def c22InducedCount {n₁ n₂ : Nat} (F : CGraph22 n₁) (G : CGraph22 n₂) : Nat :=
  (univ : Finset (Fin n₁ → Fin n₂)).filter (fun f =>
    (∀ i j : Fin n₁, f i = f j → i = j) ∧
    (∀ i : Fin n₁, F.vertexCol i = G.vertexCol (f i)) ∧
    (∀ i j : Fin n₁, F.adj i j = G.adj (f i) (f j)) ∧
    (∀ i j : Fin n₁, F.edgeCol i j = G.edgeCol (f i) (f j))) |>.card

/-! ## CGraph22 → GenFlag conversion -/

/-- Convert a `CGraph22 n` to a `GenFlag CG22 (GenFlagType.empty CG22)`. -/
noncomputable def CGraph22.toGenFlag {n : Nat} (G : CGraph22 n) :
    GenFlag CG22 (GenFlagType.empty CG22) where
  size := n
  str := (⟨SimpleGraph.fromRel (fun i j : Fin n => G.adj i j),
          G.vertexCol,
          fun u v => G.edgeCol u v⟩ : CG22.Str n)
  embedding := ⟨Fin.elim0, fun {a} => Fin.elim0 a⟩
  isInduced := by apply CG22.comap_elim0
  hsize := Nat.zero_le _

/-- The `str` of `CGraph22.toGenFlag` decomposes into the three components. -/
theorem CGraph22.toGenFlag_str {n : Nat} (G : CGraph22 n) :
    G.toGenFlag.str =
      (⟨SimpleGraph.fromRel (fun i j : Fin n => G.adj i j),
        G.vertexCol,
        fun u v => G.edgeCol u v⟩ : CG22.Str n) := rfl

/-- The `size` of `CGraph22.toGenFlag`. -/
theorem CGraph22.toGenFlag_size {n : Nat} (G : CGraph22 n) :
    G.toGenFlag.size = n := rfl

/-! ## Bridge theorem

`c22InducedCount F G = genInducedCount CG22 ∅ F.toGenFlag G.toGenFlag` when
both `CGraph22`s have symmetric and irreflexive `adj` (the adjacency
`SimpleGraph.fromRel` wraps Bool into Prop with symmetrisation + irreflexivity,
so equality up to `comap` requires the source to already match). The edge
colour bridge needs symmetry on its function too (no quotient to absorb). -/

/-- Bridge theorem: `c22InducedCount` matches the abstract `genInducedCount`. -/
theorem c22InducedCount_eq_genInducedCount' {n₁ n₂ : Nat}
    (F : CGraph22 n₁) (G : CGraph22 n₂)
    (hFs : ∀ i j, F.adj i j = F.adj j i)
    (hFi : ∀ i, F.adj i i = false)
    (hGs : ∀ i j, G.adj i j = G.adj j i)
    (hGi : ∀ i, G.adj i i = false) :
    c22InducedCount F G =
      genInducedCount CG22 (GenFlagType.empty CG22) F.toGenFlag G.toGenFlag := by
  unfold c22InducedCount genInducedCount
  -- Key bridge: (Bool adj + vertex col + edge col) ↔ `comap f` equality on CG22.Str
  have adj_iff : ∀ (f : Fin n₁ → Fin n₂), Function.Injective f →
      (((∀ i : Fin n₁, F.vertexCol i = G.vertexCol (f i)) ∧
        (∀ i j : Fin n₁, F.adj i j = G.adj (f i) (f j)) ∧
        (∀ i j : Fin n₁, F.edgeCol i j = G.edgeCol (f i) (f j))) ↔
      CG22.comap f G.toGenFlag.str = F.toGenFlag.str) := by
    intro f hinj
    -- Unfold to a Prod.mk equality on three components.
    rw [CG22_comap, CGraph22.toGenFlag_str, CGraph22.toGenFlag_str]
    constructor
    · rintro ⟨hcol, hadj, hec⟩
      refine CG22_str_ext ?_ ?_ ?_
      · -- Graph component (same argument as CGraphBridge).
        ext u v
        simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
        constructor
        · rintro ⟨hfne, h⟩
          refine ⟨fun huv => hfne (congr_arg f huv), ?_⟩
          rcases h with h | h
          · left; rw [hadj u v]; exact h
          · right; rw [hadj v u]; exact h
        · rintro ⟨hne, h⟩
          refine ⟨fun h' => hne (hinj h'), ?_⟩
          rcases h with h | h
          · left; rw [← hadj u v]; exact h
          · right; rw [← hadj v u]; exact h
      · -- Vertex colour: pointwise.
        funext u; exact (hcol u).symm
      · -- Edge colour: pointwise on two variables.
        funext u v; exact (hec u v).symm
    · intro hstr
      -- Decompose the structure equality.
      have hg := congr_arg (fun s : CG22.Str n₁ => s.1) hstr
      have hvc := congr_arg (fun s : CG22.Str n₁ => s.2.1) hstr
      have hec := congr_arg (fun s : CG22.Str n₁ => s.2.2) hstr
      -- Vertex colour: directly from the second component.
      refine ⟨fun i => ?_, fun i j => ?_, fun i j => ?_⟩
      · exact (congr_fun hvc i).symm
      · -- Adjacency: case-split on Bool. Same idea as CGraphBridge.
        by_cases hij : i = j
        · subst hij; simp only [hFi, hGi]
        · -- Use the graph equality at (i, j).
          have hge : ∀ a b : Fin n₁,
              (SimpleGraph.comap f (SimpleGraph.fromRel fun i j => ↑(G.adj i j))).Adj a b ↔
              (SimpleGraph.fromRel fun i j => ↑(F.adj i j)).Adj a b := by
            intro a b
            rw [show (SimpleGraph.fromRel fun i j => ↑(G.adj i j)).comap f =
                    SimpleGraph.fromRel fun i j => ↑(F.adj i j) from by exact_mod_cast hg]
          simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj] at hge
          have fne : f i ≠ f j := fun h => hij (hinj h)
          cases hF : F.adj i j <;> cases hGval : G.adj (f i) (f j)
          · rfl
          · exfalso
            obtain ⟨_, h3⟩ := (hge i j).mp ⟨fne, Or.inl (by simp [hGval])⟩
            cases h3 with
            | inl h => simp [hF] at h
            | inr h =>
              have : F.adj j i = false := by rw [← hFs i j]; exact hF
              exact absurd h (by rw [this]; exact Bool.false_ne_true)
          · exfalso
            obtain ⟨_, h3⟩ := (hge i j).mpr ⟨hij, Or.inl (by simp [hF])⟩
            cases h3 with
            | inl h => simp [hGval] at h
            | inr h =>
              have : G.adj (f j) (f i) = false := by rw [← hGs (f i) (f j)]; exact hGval
              exact absurd h (by rw [this]; exact Bool.false_ne_true)
          · rfl
      · -- Edge colour: pointwise from the third component.
        exact (congr_fun (congr_fun hec i) j).symm
  -- Build a Fintype.card_congr via the bridge.
  have : (Finset.filter (fun f =>
      (∀ i j : Fin n₁, f i = f j → i = j) ∧
      (∀ i : Fin n₁, F.vertexCol i = G.vertexCol (f i)) ∧
      (∀ i j : Fin n₁, F.adj i j = G.adj (f i) (f j)) ∧
      (∀ i j : Fin n₁, F.edgeCol i j = G.edgeCol (f i) (f j)))
    (Finset.univ : Finset (Fin n₁ → Fin n₂))).card =
    Fintype.card (GenInducedEmbedding CG22 (GenFlagType.empty CG22)
      F.toGenFlag G.toGenFlag) := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    exact {
      toFun := fun ⟨f, hf⟩ =>
        have hm := Finset.mem_filter.mp hf
        { toFun := f
          injective := hm.2.1
          isInduced := (adj_iff f hm.2.1).mp ⟨hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2⟩
          compat := fun i => Fin.elim0 i }
      invFun := fun e =>
        ⟨e.toFun,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.injective,
            ((adj_iff e.toFun e.injective).mpr e.isInduced).1,
            ((adj_iff e.toFun e.injective).mpr e.isInduced).2.1,
            ((adj_iff e.toFun e.injective).mpr e.isInduced).2.2⟩⟩
      left_inv := fun ⟨_, _⟩ => by simp
      right_inv := fun e => by cases e; rfl
    }
  exact this

/-! ## Pairwise distinctness for `GenFlagClass`

If `c22InducedCount F G = 0` for same-size CGraph22s with symmetric/irreflexive
`adj`, then their `GenFlagClass`es are distinct (since an induced embedding
between same-size finite sets is a bijection). Mirrors `cFlags_noniso_implies_genClass_ne`. -/

/-- If `c22InducedCount F G = 0` for same-size symmetric/irreflexive CGraph22s,
    then their `GenFlagClass`es differ.

    **Status**: Intentional standalone — bridge fact mirroring
    `cFlags_noniso_implies_genClass_ne` for CG22; no consumer expected
    in the current Pentagon Q proof chain. -/
theorem c22Flags_noniso_implies_genClass_ne {n : Nat}
    (F G : CGraph22 n)
    (hFs : ∀ i j, F.adj i j = F.adj j i) (hFi : ∀ i, F.adj i i = false)
    (hGs : ∀ i j, G.adj i j = G.adj j i) (hGi : ∀ i, G.adj i i = false)
    (h : c22InducedCount F G = 0) :
    GenFlagClass.mk F.toGenFlag ≠ GenFlagClass.mk G.toGenFlag := by
  intro heq
  have hiso : GenFlagIso (GenFlagType.empty CG22) F.toGenFlag G.toGenFlag :=
    Quotient.exact heq
  obtain ⟨φ, hstr, _⟩ := hiso
  have emb : GenInducedEmbedding CG22 (GenFlagType.empty CG22) F.toGenFlag G.toGenFlag :=
    { toFun := φ
      injective := φ.injective
      isInduced := hstr
      compat := fun i => Fin.elim0 i }
  have hpos : 0 < genInducedCount CG22 (GenFlagType.empty CG22)
      F.toGenFlag G.toGenFlag :=
    Fintype.card_pos_iff.mpr ⟨emb⟩
  rw [c22InducedCount_eq_genInducedCount' F G hFs hFi hGs hGi] at h
  omega

/-! ## ColouredGraph22 → GenFlag CG22 bridge (S3.E.1)

The `ColouredGraph22` struct in `StrongEdgeColouring.lean` is the
non-computable "math-level" analog of `CGraph22` used by the SEC
reduction (the F-faithful `SecBridge.colouredGraph22OfEdgeF` produces one
from `(G, F, u, w)`).
This section bridges from `ColouredGraph22` to `GenFlag CG22 ∅` in
direct analogy to `ColouredGraphClass.toGenFlag : ColouredGraphClass →
GenFlag CG2 ∅` in `PentagonConjecture.lean:1962`.

The bridge is used by `SecBridge.sec_seq_to_genFlag` (Phase S3.E.2) to
package the SEC reduction's coloured-graph output as a CG22-typed flag,
making it consumable by the SEC SDP basis. -/

/-- Convert a `ColouredGraph22` to a `GenFlag CG22 (GenFlagType.empty CG22)`
by extracting its three components (graph, vertex colour, edge colour)
into the CG22.Str triple.

This is the SEC analog of `ColouredGraphClass.toGenFlag` from
`PentagonConjecture.lean:1962`. The empty `embedding` reflects the ∅-type
context: every CG22 flag at `(GenFlagType.empty CG22)` has trivial type
embedding (vertices of `Fin 0` → vertices of `Fin n`).

The `isInduced` invariant is discharged by `CG22.comap_elim0` (the comap
along `Fin.elim0` collapses to the empty CG22 structure).

**Note on edge symmetry**: `ColouredGraph22` carries `edgeSymm`, but
`CG22.Str` itself does not require edge symmetry (it's a side hypothesis
in bridge theorems consuming the CG22 flag). The information is
preserved here as part of `G.edgeColour`. -/
noncomputable def ColouredGraph22.toGenFlag (G : ColouredGraph22) :
    GenFlag CG22 (GenFlagType.empty CG22) where
  size := G.graph.size
  str := (⟨G.graph.graph, G.vertexColour, G.edgeColour⟩ : CG22.Str G.graph.size)
  embedding := ⟨Fin.elim0, fun {a} => Fin.elim0 a⟩
  isInduced := by apply CG22.comap_elim0
  hsize := Nat.zero_le _

/-- The `str` of `ColouredGraph22.toGenFlag` decomposes into the three
underlying components. -/
@[simp] theorem ColouredGraph22.toGenFlag_str (G : ColouredGraph22) :
    G.toGenFlag.str =
      (⟨G.graph.graph, G.vertexColour, G.edgeColour⟩ : CG22.Str G.graph.size) := rfl

/-- The `size` of `ColouredGraph22.toGenFlag` equals the underlying graph's size. -/
@[simp] theorem ColouredGraph22.toGenFlag_size (G : ColouredGraph22) :
    G.toGenFlag.size = G.graph.size := rfl

/-! ## Smoke tests: small CGraph22 instances + verification -/

/-- The empty CGraph22 on 0 vertices. -/
def CGraph22.empty : CGraph22 0 where
  adj := fun i _ => Fin.elim0 i
  vertexCol := fun i => Fin.elim0 i
  edgeCol := fun i _ => Fin.elim0 i

/-- A single red vertex (no edges). -/
def CGraph22.singleRed : CGraph22 1 where
  adj := fun _ _ => false
  vertexCol := fun _ => 0
  edgeCol := fun _ _ => 0

/-- A single black vertex (no edges). -/
def CGraph22.singleBlack : CGraph22 1 where
  adj := fun _ _ => false
  vertexCol := fun _ => 1
  edgeCol := fun _ _ => 0

/-- Two vertices joined by a red edge: red vertices, red edge. -/
def CGraph22.redEdge : CGraph22 2 where
  adj := fun i j => i ≠ j
  vertexCol := fun _ => 0
  edgeCol := fun _ _ => 0

/-- Two vertices joined by a black edge: black vertices, black edge. -/
def CGraph22.blackEdge : CGraph22 2 where
  adj := fun i j => i ≠ j
  vertexCol := fun _ => 1
  edgeCol := fun _ _ => 1

/-- A two-vertex (2,2)-coloured graph with mixed vertex colours (R, B) and a
    black edge between them. Representative of an SEC neighbourhood edge. -/
def CGraph22.mixedBlackEdge : CGraph22 2 where
  adj := fun i j => i ≠ j
  vertexCol := fun i => if i.val = 1 then 1 else 0
  edgeCol := fun _ _ => 1

/-- `c22InducedCount` agrees with itself: a single red vertex has one
    self-embedding. (Tests `native_decide` works on `CGraph22`.) -/
example : c22InducedCount CGraph22.singleRed CGraph22.singleRed = 1 := by native_decide

/-- A red vertex does not embed into a black vertex. -/
example : c22InducedCount CGraph22.singleRed CGraph22.singleBlack = 0 := by native_decide

/-- A red edge has two self-embeddings (the two vertex permutations). -/
example : c22InducedCount CGraph22.redEdge CGraph22.redEdge = 2 := by native_decide

/-- The black edge does not embed into the red edge (vertex / edge colour mismatch). -/
example : c22InducedCount CGraph22.blackEdge CGraph22.redEdge = 0 := by native_decide

/-- The mixed black edge has only one self-embedding (the asymmetric vertex colouring
    rules out the swap). -/
example : c22InducedCount CGraph22.mixedBlackEdge CGraph22.mixedBlackEdge = 1 := by
  native_decide

end Davey2024
