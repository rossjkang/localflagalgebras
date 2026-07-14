import DaveyThesis2024.CG4

/-!
# `CGraph4` ↔ `GenFlag CG4` bridge

Computable (`Bool`-valued) analog of `CG4` for `native_decide` verification,
mirroring `CGraph22` ↔ `GenFlag CG22` in `CGraph22Bridge.lean` but **without the
edge-colour component** (the asymmetric SEC problem uses plain edges).

## Main definitions

* `CGraph4 n` — `Bool`-adjacency + `Fin 4`-vertex-colour on `Fin n`. All fields
  are computable for `native_decide` use.
* `CGraph4.toGenFlag` — `CGraph4 n → GenFlag CG4 (GenFlagType.empty CG4)`.
* `c4InducedCount` — computable count of induced colour-preserving embeddings.
* `c4InducedCount_eq_genInducedCount'` — bridge theorem: the computable count
  equals the abstract `genInducedCount CG4 ∅ F.toGenFlag G.toGenFlag` when both
  `CGraph4`s have symmetric, irreflexive `adj` (mirrors the `CGraph22` bridge,
  minus the edge-colour clause).

## Smoke tests

A few small `CGraph4` examples at the bottom verify the structure builds,
`toGenFlag` typechecks, and `native_decide` evaluates `c4InducedCount`. The
4-colour vertex colouring is genuinely tracked (a colour-2 vertex does not embed
into a colour-3 vertex, etc.).
-/

namespace Davey2024

open Finset

/-! ## Computable 4-vertex-colour plain-edge graph -/

/-- A computable 4-vertex-colour plain-edge graph on `Fin n` vertices.

    Fields use `Bool` for adjacency and `Fin 4` for the vertex colouring so that
    `native_decide` can evaluate any function that consumes a `CGraph4`. There is
    no edge colour (plain edges). -/
structure CGraph4 (n : Nat) where
  /-- Adjacency relation. Should be symmetric and irreflexive in practice;
      proofs that require this carry it as a side hypothesis (mirrors `CGraph22`). -/
  adj : Fin n → Fin n → Bool
  /-- Vertex colouring, raw Rust colour `0–3` (no projection). `COMP = [0,1,0,1]`,
      `X_COLS = {0,1}`, `Y_COLS = {2,3}` per the asymmetric SEC generator. -/
  vertexCol : Fin n → Fin 4

instance : Inhabited (CGraph4 n) :=
  ⟨⟨fun _ _ => false, fun _ => 0⟩⟩

/-- Computable count of 4-vertex-colour induced embeddings.

    Counts injective `f : Fin n₁ → Fin n₂` that preserve adjacency (Bool) and
    vertex colour pointwise. Mirrors `c22InducedCount` in `CGraph22Bridge.lean`
    minus the edge-colour constraint. -/
def c4InducedCount {n₁ n₂ : Nat} (F : CGraph4 n₁) (G : CGraph4 n₂) : Nat :=
  (univ : Finset (Fin n₁ → Fin n₂)).filter (fun f =>
    (∀ i j : Fin n₁, f i = f j → i = j) ∧
    (∀ i : Fin n₁, F.vertexCol i = G.vertexCol (f i)) ∧
    (∀ i j : Fin n₁, F.adj i j = G.adj (f i) (f j))) |>.card

/-! ## CGraph4 → GenFlag conversion -/

/-- Convert a `CGraph4 n` to a `GenFlag CG4 (GenFlagType.empty CG4)`. -/
noncomputable def CGraph4.toGenFlag {n : Nat} (G : CGraph4 n) :
    GenFlag CG4 (GenFlagType.empty CG4) where
  size := n
  str := (⟨SimpleGraph.fromRel (fun i j : Fin n => G.adj i j),
          G.vertexCol⟩ : CG4.Str n)
  embedding := ⟨Fin.elim0, fun {a} => Fin.elim0 a⟩
  isInduced := by apply CG4.comap_elim0
  hsize := Nat.zero_le _

/-- The `str` of `CGraph4.toGenFlag` decomposes into the two components. -/
theorem CGraph4.toGenFlag_str {n : Nat} (G : CGraph4 n) :
    G.toGenFlag.str =
      (⟨SimpleGraph.fromRel (fun i j : Fin n => G.adj i j),
        G.vertexCol⟩ : CG4.Str n) := rfl

/-- The `size` of `CGraph4.toGenFlag`. -/
theorem CGraph4.toGenFlag_size {n : Nat} (G : CGraph4 n) :
    G.toGenFlag.size = n := rfl

/-! ## Bridge theorem

`c4InducedCount F G = genInducedCount CG4 ∅ F.toGenFlag G.toGenFlag` when both
`CGraph4`s have symmetric and irreflexive `adj` (the adjacency
`SimpleGraph.fromRel` wraps Bool into Prop with symmetrisation + irreflexivity,
so equality up to `comap` requires the source to already match). Mirrors
`c22InducedCount_eq_genInducedCount'` minus the edge-colour clause. -/

/-- Bridge theorem: `c4InducedCount` matches the abstract `genInducedCount`. -/
theorem c4InducedCount_eq_genInducedCount' {n₁ n₂ : Nat}
    (F : CGraph4 n₁) (G : CGraph4 n₂)
    (hFs : ∀ i j, F.adj i j = F.adj j i)
    (hFi : ∀ i, F.adj i i = false)
    (hGs : ∀ i j, G.adj i j = G.adj j i)
    (hGi : ∀ i, G.adj i i = false) :
    c4InducedCount F G =
      genInducedCount CG4 (GenFlagType.empty CG4) F.toGenFlag G.toGenFlag := by
  unfold c4InducedCount genInducedCount
  -- Key bridge: (Bool adj + vertex col) ↔ `comap f` equality on CG4.Str
  have adj_iff : ∀ (f : Fin n₁ → Fin n₂), Function.Injective f →
      (((∀ i : Fin n₁, F.vertexCol i = G.vertexCol (f i)) ∧
        (∀ i j : Fin n₁, F.adj i j = G.adj (f i) (f j))) ↔
      CG4.comap f G.toGenFlag.str = F.toGenFlag.str) := by
    intro f hinj
    rw [CG4_comap, CGraph4.toGenFlag_str, CGraph4.toGenFlag_str]
    constructor
    · rintro ⟨hcol, hadj⟩
      refine CG4_str_ext ?_ ?_
      · -- Graph component (same argument as CGraph22 bridge).
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
    · intro hstr
      -- Decompose the structure equality.
      have hg := congr_arg (fun s : CG4.Str n₁ => s.1) hstr
      have hvc := congr_arg (fun s : CG4.Str n₁ => s.2) hstr
      refine ⟨fun i => ?_, fun i j => ?_⟩
      · exact (congr_fun hvc i).symm
      · -- Adjacency: case-split on Bool. Same idea as CGraph22 bridge.
        by_cases hij : i = j
        · subst hij; simp only [hFi, hGi]
        · have hge : ∀ a b : Fin n₁,
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
  -- Build a Fintype.card_congr via the bridge.
  have : (Finset.filter (fun f =>
      (∀ i j : Fin n₁, f i = f j → i = j) ∧
      (∀ i : Fin n₁, F.vertexCol i = G.vertexCol (f i)) ∧
      (∀ i j : Fin n₁, F.adj i j = G.adj (f i) (f j)))
    (Finset.univ : Finset (Fin n₁ → Fin n₂))).card =
    Fintype.card (GenInducedEmbedding CG4 (GenFlagType.empty CG4)
      F.toGenFlag G.toGenFlag) := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    exact {
      toFun := fun ⟨f, hf⟩ =>
        have hm := Finset.mem_filter.mp hf
        { toFun := f
          injective := hm.2.1
          isInduced := (adj_iff f hm.2.1).mp ⟨hm.2.2.1, hm.2.2.2⟩
          compat := fun i => Fin.elim0 i }
      invFun := fun e =>
        ⟨e.toFun,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.injective,
            ((adj_iff e.toFun e.injective).mpr e.isInduced).1,
            ((adj_iff e.toFun e.injective).mpr e.isInduced).2⟩⟩
      left_inv := fun ⟨_, _⟩ => by simp
      right_inv := fun e => by cases e; rfl
    }
  exact this

/-! ## Pairwise distinctness for `GenFlagClass`

If `c4InducedCount F G = 0` for same-size CGraph4s with symmetric/irreflexive
`adj`, then their `GenFlagClass`es are distinct (an induced embedding between
same-size finite sets is a bijection). Mirrors
`c22Flags_noniso_implies_genClass_ne`. -/

/-- If `c4InducedCount F G = 0` for same-size symmetric/irreflexive CGraph4s,
    then their `GenFlagClass`es differ.

    **Status**: Intentional standalone — bridge fact used by the G-PROVENANCE
    smoke test to certify that two component-distinct flags are non-isomorphic
    in `CG4` (the CG22 high-bit collapse is gone). -/
theorem c4Flags_noniso_implies_genClass_ne {n : Nat}
    (F G : CGraph4 n)
    (hFs : ∀ i j, F.adj i j = F.adj j i) (hFi : ∀ i, F.adj i i = false)
    (hGs : ∀ i j, G.adj i j = G.adj j i) (hGi : ∀ i, G.adj i i = false)
    (h : c4InducedCount F G = 0) :
    GenFlagClass.mk F.toGenFlag ≠ GenFlagClass.mk G.toGenFlag := by
  intro heq
  have hiso : GenFlagIso (GenFlagType.empty CG4) F.toGenFlag G.toGenFlag :=
    Quotient.exact heq
  obtain ⟨φ, hstr, _⟩ := hiso
  have emb : GenInducedEmbedding CG4 (GenFlagType.empty CG4) F.toGenFlag G.toGenFlag :=
    { toFun := φ
      injective := φ.injective
      isInduced := hstr
      compat := fun i => Fin.elim0 i }
  have hpos : 0 < genInducedCount CG4 (GenFlagType.empty CG4)
      F.toGenFlag G.toGenFlag :=
    Fintype.card_pos_iff.mpr ⟨emb⟩
  rw [c4InducedCount_eq_genInducedCount' F G hFs hFi hGs hGi] at h
  omega

/-! ## Smoke tests: small CGraph4 instances + verification -/

/-- A single colour-0 vertex (no edges). -/
def CGraph4.single0 : CGraph4 1 where
  adj := fun _ _ => false
  vertexCol := fun _ => 0

/-- A single colour-2 vertex (no edges). -/
def CGraph4.single2 : CGraph4 1 where
  adj := fun _ _ => false
  vertexCol := fun _ => 2

/-- A single colour-3 vertex (no edges). -/
def CGraph4.single3 : CGraph4 1 where
  adj := fun _ _ => false
  vertexCol := fun _ => 3

/-- Two adjacent vertices, colours (0, 2) — an X/Y cross edge. -/
def CGraph4.edge02 : CGraph4 2 where
  adj := fun i j => i ≠ j
  vertexCol := fun i => if i.val = 1 then 2 else 0

/-- `c4InducedCount` agrees with itself: a single colour-0 vertex has one
    self-embedding. (Tests `native_decide` works on `CGraph4`.) -/
example : c4InducedCount CGraph4.single0 CGraph4.single0 = 1 := by native_decide

/-- A colour-2 vertex does not embed into a colour-3 vertex — the full 4-colour
    palette is genuinely distinguished (not collapsed to a high bit). -/
example : c4InducedCount CGraph4.single2 CGraph4.single3 = 0 := by native_decide

/-- A colour-0 vertex does not embed into a colour-2 vertex. -/
example : c4InducedCount CGraph4.single0 CGraph4.single2 = 0 := by native_decide

/-- The (0,2) cross edge has exactly one self-embedding (the colours rule out
    the vertex swap). -/
example : c4InducedCount CGraph4.edge02 CGraph4.edge02 = 1 := by native_decide

end Davey2024
