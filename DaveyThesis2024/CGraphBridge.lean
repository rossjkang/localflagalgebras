import DaveyThesis2024.PentagonConjecture
import DaveyThesis2024.SdpFlags

-- Many proofs in this file enumerate over Fin 5 × Fin 5 (and larger) via

/-!
# CGraph ↔ GenFlag Bridge

Connects computable `CGraph` (Bool adjacency) to the abstract `GenFlag CG2`
framework, enabling `native_decide` verification of flag algebra computations.

## Main results

* `CGraph.toGenFlag` — convert CGraph to GenFlag CG2
* `cInducedCount_eq_genInducedCount` — embedding counts agree
* `cFlags_noniso_implies_genClass_ne` — distinct CGraph flags give distinct GenFlagClass
-/

namespace Davey2024

open Finset

/-! ## Computable coloured graph -/

/-- A computable 2-coloured graph on `Fin n` vertices. -/
structure CGraph (n : Nat) where
  adj : Fin n → Fin n → Bool
  col : Fin n → Fin 2

instance : Inhabited (CGraph n) := ⟨⟨fun _ _ => false, fun _ => 0⟩⟩

/-- Count induced embeddings from CGraph n₁ to CGraph n₂. -/
def cInducedCount {n₁ n₂ : Nat} (F : CGraph n₁) (G : CGraph n₂) : Nat :=
  (univ : Finset (Fin n₁ → Fin n₂)).filter (fun f =>
    (∀ i j : Fin n₁, f i = f j → i = j) ∧
    (∀ i : Fin n₁, F.col i = G.col (f i)) ∧
    (∀ i j : Fin n₁, F.adj i j = G.adj (f i) (f j))) |>.card

/-! ## CGraph → GenFlag conversion -/

/-- Convert a `CGraph n` to a `GenFlag CG2 (GenFlagType.empty CG2)`. -/
noncomputable def CGraph.toGenFlag {n : Nat} (G : CGraph n) :
    GenFlag CG2 (GenFlagType.empty CG2) where
  size := n
  str := (⟨SimpleGraph.fromRel (fun i j : Fin n => G.adj i j), G.col⟩ : CG2.Str n)
  embedding := ⟨Fin.elim0, fun {a} => Fin.elim0 a⟩
  isInduced := by apply CG2.comap_elim0
  hsize := Nat.zero_le _

/-- The `str` of `CGraph.toGenFlag` decomposes into graph and colouring. -/
theorem CGraph.toGenFlag_str {n : Nat} (G : CGraph n) :
    G.toGenFlag.str = (⟨SimpleGraph.fromRel (fun i j : Fin n => G.adj i j), G.col⟩ :
      CG2.Str n) := rfl

/-- The `size` of `CGraph.toGenFlag`. -/
theorem CGraph.toGenFlag_size {n : Nat} (G : CGraph n) :
    G.toGenFlag.size = n := rfl

/-! ## Embedding count correspondence

The key bridge theorem: `cInducedCount F G = genInducedCount CG2 ∅ F.toGenFlag G.toGenFlag`.

Both count injective functions `f : Fin n₁ → Fin n₂` that preserve:
- Adjacency: `F.adj i j = G.adj (f i) (f j)` (CGraph) ↔ `comap f G.graph = F.graph` (GenFlag)
- Colour: `F.col i = G.col (f i)` (both conventions)

The subtlety is that `SimpleGraph.fromRel` wraps Bool adjacency into Prop adjacency,
adding `i ≠ j` (irreflexivity) and symmetrization. For Bool functions that are
already symmetric and irreflexive, the correspondence is exact. -/

/-- The `cInducedCount` equals `genInducedCount` when the CGraph adjacency is
    symmetric and irreflexive. -/
theorem cInducedCount_eq_genInducedCount' {n₁ n₂ : Nat}
    (F : CGraph n₁) (G : CGraph n₂)
    (hFs : ∀ i j, F.adj i j = F.adj j i)
    (hFi : ∀ i, F.adj i i = false)
    (hGs : ∀ i j, G.adj i j = G.adj j i)
    (hGi : ∀ i, G.adj i i = false) :
    cInducedCount F G =
      genInducedCount CG2 (GenFlagType.empty CG2) F.toGenFlag G.toGenFlag := by
  unfold cInducedCount genInducedCount
  -- Key lemma: Bool adjacency conditions ↔ comap structure equality
  have adj_iff : ∀ (f : Fin n₁ → Fin n₂), Function.Injective f →
      (((∀ i : Fin n₁, F.col i = G.col (f i)) ∧
       (∀ i j : Fin n₁, F.adj i j = G.adj (f i) (f j))) ↔
      (colouredGraphUniverse 2).comap f G.toGenFlag.str = F.toGenFlag.str) := by
    intro f hinj
    simp only [colouredGraphUniverse, CGraph.toGenFlag]
    constructor
    · rintro ⟨hcol, hadj⟩
      apply Prod.ext
      · -- Graph: comap f (fromRel G.adj) = fromRel F.adj
        ext u v
        simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
        -- Both sides: (_ ≠ _) ∧ (Bool↑Prop ∨ Bool↑Prop)
        -- For injective f: f u ≠ f v ↔ u ≠ v
        -- Bool adj is preserved by hadj, symmetry makes Or redundant
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
      · funext u; exact (hcol u).symm
    · intro hstr
      obtain ⟨hg, hc⟩ := Prod.mk.inj hstr
      refine ⟨fun i => (congr_fun hc i).symm, fun i j => ?_⟩
      by_cases hij : i = j
      · subst hij; simp only [hFi, hGi]
      · -- Use the graph equality at (i,j)
        have hge : ∀ a b : Fin n₁,
            (SimpleGraph.comap f (SimpleGraph.fromRel fun i j => ↑(G.adj i j))).Adj a b ↔
            (SimpleGraph.fromRel fun i j => ↑(F.adj i j)).Adj a b := by
          have hge' := hg
          intro a b
          rw [show (SimpleGraph.fromRel fun i j => ↑(G.adj i j)).comap f =
                  SimpleGraph.fromRel fun i j => ↑(F.adj i j) from by exact_mod_cast hge']
        simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj] at hge
        -- Case split on Bool values
        have fne : f i ≠ f j := fun h => hij (hinj h)
        cases hF : F.adj i j <;> cases hG : G.adj (f i) (f j)
        · rfl
        · exfalso
          have h1 : (f i ≠ f j ∧ ((↑(G.adj (f i) (f j)) : Prop) ∨ (↑(G.adj (f j) (f i))))) := by
            exact ⟨fne, Or.inl (by simp [hG])⟩
          have h2 := (hge i j).mp h1
          obtain ⟨_, h3⟩ := h2
          cases h3 with
          | inl h => simp [hF] at h
          | inr h =>
            -- h : ↑(F.adj j i), but F.adj j i = F.adj i j = false
            have : F.adj j i = false := by rw [← hFs i j]; exact hF
            exact absurd h (by rw [this]; exact Bool.false_ne_true)
        · exfalso
          have h1 : (i ≠ j ∧ ((↑(F.adj i j) : Prop) ∨ (↑(F.adj j i)))) := by
            exact ⟨hij, Or.inl (by simp [hF])⟩
          have h2 := (hge i j).mpr h1
          obtain ⟨_, h3⟩ := h2
          cases h3 with
          | inl h => simp [hG] at h
          | inr h =>
            -- h : ↑(G.adj (f j) (f i)), but G.adj (f j) (f i) = G.adj (f i) (f j) = false
            have : G.adj (f j) (f i) = false := by rw [← hGs (f i) (f j)]; exact hG
            exact absurd h (by rw [this]; exact Bool.false_ne_true)
        · rfl
  -- Build the Fintype.card_congr
  have : (Finset.filter (fun f =>
      (∀ i j : Fin n₁, f i = f j → i = j) ∧
      (∀ i : Fin n₁, F.col i = G.col (f i)) ∧
      ∀ i j : Fin n₁, F.adj i j = G.adj (f i) (f j))
    (Finset.univ : Finset (Fin n₁ → Fin n₂))).card =
    Fintype.card (GenInducedEmbedding CG2 (GenFlagType.empty CG2) F.toGenFlag G.toGenFlag) := by
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
        ⟨e.toFun, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.injective,
          ((adj_iff e.toFun e.injective).mpr e.isInduced).1,
          ((adj_iff e.toFun e.injective).mpr e.isInduced).2⟩⟩
      left_inv := fun ⟨f, hf⟩ => by simp
      right_inv := fun e => by
        cases e; rfl
    }
  exact this

/-! ## Pairwise distinctness

For same-size CGraphs, `cInducedCount F G > 0` iff F ≅ G (since an induced
embedding between same-size finite sets is a bijection). So if
`cInducedCount F G = 0`, the GenFlagClasses are distinct. -/

/-- If `cInducedCount F G = 0` for same-size symmetric irreflexive CGraphs,
    then their GenFlagClasses are distinct. -/
theorem cFlags_noniso_implies_genClass_ne {n : Nat}
    (F G : CGraph n)
    (hFs : ∀ i j, F.adj i j = F.adj j i) (hFi : ∀ i, F.adj i i = false)
    (hGs : ∀ i j, G.adj i j = G.adj j i) (hGi : ∀ i, G.adj i i = false)
    (h : cInducedCount F G = 0) :
    GenFlagClass.mk F.toGenFlag ≠ GenFlagClass.mk G.toGenFlag := by
  intro heq
  -- If classes are equal, there exists a GenFlagIso
  have hiso : GenFlagIso (GenFlagType.empty CG2) F.toGenFlag G.toGenFlag :=
    Quotient.exact heq
  -- A GenFlagIso gives an Equiv φ with R.comap φ G.str = F.str
  obtain ⟨φ, hstr, _⟩ := hiso
  -- φ yields a GenInducedEmbedding (injective + induced + compat trivial for ∅)
  have emb : GenInducedEmbedding CG2 (GenFlagType.empty CG2) F.toGenFlag G.toGenFlag :=
    { toFun := φ
      injective := φ.injective
      isInduced := hstr
      compat := fun i => Fin.elim0 i }
  -- So genInducedCount > 0
  have hpos : 0 < genInducedCount CG2 (GenFlagType.empty CG2) F.toGenFlag G.toGenFlag :=
    Fintype.card_pos_iff.mpr ⟨emb⟩
  -- By the bridge theorem, cInducedCount > 0
  rw [cInducedCount_eq_genInducedCount' F G hFs hFi hGs hGi] at h
  omega

/-! ## Typed CGraph infrastructure

Extends the CGraph bridge to handle σ-typed flags, where the first `k` vertices
form the type embedding (via `Fin.castLE`). This enables `native_decide` verification
of typed flag computations (joint counts, normalisation factors, forget images). -/

/-- Convert a `CGraph n` to a typed `GenFlag CG2 σ` where the first `σ.size` vertices
    form the type embedding via `Fin.castLE`. -/
noncomputable def CGraph.toTypedGenFlag {n : Nat} (G : CGraph n)
    (σ : GenFlagType CG2) (hle : σ.size ≤ n)
    (hstr : CG2.comap (Fin.castLE hle) (⟨SimpleGraph.fromRel (fun i j : Fin n => G.adj i j),
      G.col⟩ : CG2.Str n) = σ.str) :
    GenFlag CG2 σ where
  size := n
  str := (⟨SimpleGraph.fromRel (fun i j : Fin n => G.adj i j), G.col⟩ : CG2.Str n)
  embedding := ⟨Fin.castLE hle, Fin.castLE_injective hle⟩
  isInduced := hstr
  hsize := hle

/-- The forget of a typed CGraph GenFlag equals the untyped CGraph GenFlag. -/
theorem CGraph.toTypedGenFlag_forget {n : Nat} (G : CGraph n)
    (σ : GenFlagType CG2) (hle : σ.size ≤ n) (hstr) :
    (G.toTypedGenFlag σ hle hstr).forget = G.toGenFlag :=
  GenFlag.empty_ext _ _ rfl rfl

/-- Count typed joint embeddings: pairs `(f₁, f₂)` of injective maps from
    `CGraph n₁` and `CGraph n₂` into `CGraph n₃` that preserve adjacency/colour,
    fix the first `k` vertices, and satisfy overlap = type, cover = all. -/
def tcJointCount (k : Nat) {n₁ n₂ n₃ : Nat}
    (F₁ : CGraph n₁) (F₂ : CGraph n₂) (G : CGraph n₃) : Nat :=
  ((univ : Finset (Fin n₁ → Fin n₃)) ×ˢ (univ : Finset (Fin n₂ → Fin n₃))).filter (fun p =>
    (∀ i j : Fin n₁, p.1 i = p.1 j → i = j) ∧
    (∀ i : Fin n₁, F₁.col i = G.col (p.1 i)) ∧
    (∀ i j : Fin n₁, F₁.adj i j = G.adj (p.1 i) (p.1 j)) ∧
    (∀ i : Fin n₁, i.val < k → (p.1 i).val = i.val) ∧
    (∀ i j : Fin n₂, p.2 i = p.2 j → i = j) ∧
    (∀ i : Fin n₂, F₂.col i = G.col (p.2 i)) ∧
    (∀ i j : Fin n₂, F₂.adj i j = G.adj (p.2 i) (p.2 j)) ∧
    (∀ i : Fin n₂, i.val < k → (p.2 i).val = i.val) ∧
    (∀ i : Fin n₃, ((∃ a : Fin n₁, p.1 a = i) ∧ (∃ b : Fin n₂, p.2 b = i)) ↔ i.val < k) ∧
    (∀ i : Fin n₃, (∃ a : Fin n₁, p.1 a = i) ∨ (∃ b : Fin n₂, p.2 b = i))) |>.card

/-- Concrete CGraph for csType7 (σ₇): 3 vertices, edges 0-1, 0-2, col [R,B,R]. -/
def cType7 : CGraph 3 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 0 && j.val == 2) || (i.val == 2 && j.val == 0)
  col := fun v => if v.val == 1 then 1 else 0

/-- Concrete CGraph for cs1Flag4: 4 vertices, edges 0-1, 0-2, 1-3, col [R,B,R,R]. -/
def cF4 : CGraph 4 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 0 && j.val == 2) || (i.val == 2 && j.val == 0) ||
                    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1)
  col := fun v => if v.val == 1 then 1 else 0

/-- Concrete CGraph for cs1Flag5: 4 vertices, edges 0-1, 0-2, 2-3, col [R,B,R,B]. -/
def cF5 : CGraph 4 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 0 && j.val == 2) || (i.val == 2 && j.val == 0) ||
                    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2)
  col := fun v => if v.val == 1 || v.val == 3 then 1 else 0

/-- Concrete CGraph for cs1Flag7: 4 vertices, edges 0-1, 0-2, 1-3, 2-3, col [R,B,R,R]. -/
def cF7 : CGraph 4 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 0 && j.val == 2) || (i.val == 2 && j.val == 0) ||
                    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
                    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2)
  col := fun v => if v.val == 1 then 1 else 0

/-! ### Verification: typed joint counts via native_decide

We verify the joint counts for all 6 products at each of the 12 typed CGraphs
(6 products × 2 values of adj(3,4)). -/

/-- Build the size-5 typed CGraph from two size-4 flags (pasting at the type).
    Vertices 0-3 come from `fi`, vertex 4 gets `fj`'s vertex-3 adjacencies/colour. -/
def tcGraph (fi fj : CGraph 4) (adj34 : Bool) : CGraph 5 where
  adj := fun i j =>
    if hi : i.val < 4 then
      if hj : j.val < 4 then fi.adj ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else if hi3 : i.val < 3 then fj.adj ⟨i.val, by omega⟩ ⟨3, by omega⟩
      else adj34
    else
      if hj : j.val < 4 then
        if hj3 : j.val < 3 then fj.adj ⟨j.val, by omega⟩ ⟨3, by omega⟩
        else adj34
      else false
  col := fun v =>
    if hv : v.val < 4 then fi.col ⟨v.val, hv⟩
    else fj.col ⟨3, by omega⟩

-- Spot-check: joint count for F4*F5 product at the adj34=false graph
example : tcJointCount 3 cF4 cF5 (tcGraph cF4 cF5 false) = 1 := by native_decide
-- Spot-check: joint count for F5*F7 at adj34=false
example : tcJointCount 3 cF5 cF7 (tcGraph cF5 cF7 false) = 1 := by native_decide
-- Spot-check: F4*F4 at adj34=false (symmetric, should be 2)
example : tcJointCount 3 cF4 cF4 (tcGraph cF4 cF4 false) = 2 := by native_decide

-- F7*F7 product: adj34=false has jc=2 (diagonal), adj34=true has triangle
example : tcJointCount 3 cF7 cF7 (tcGraph cF7 cF7 false) = 2 := by native_decide
example : tcJointCount 3 cF7 cF7 (tcGraph cF7 cF7 true) = 2 := by native_decide

-- Automorphism counts for F7*F7 adj34=false graph
-- aut_∅ (all permutations preserving adj+col)
example : cInducedCount (tcGraph cF7 cF7 false) (tcGraph cF7 cF7 false) = 6 := by native_decide
-- aut_σ (fixing first 3 vertices)
def tcAutCount (k : Nat) (G : CGraph n) : Nat :=
  (univ : Finset (Fin n → Fin n)).filter (fun f =>
    (∀ i j : Fin n, f i = f j → i = j) ∧
    (∀ i : Fin n, G.col i = G.col (f i)) ∧
    (∀ i j : Fin n, G.adj i j = G.adj (f i) (f j)) ∧
    (∀ i : Fin n, i.val < k → (f i).val = i.val)) |>.card

example : tcAutCount 3 (tcGraph cF7 cF7 false) = 2 := by native_decide

/-! ### Verify brrb_averaging_identity coefficient for F₃₇

The coefficient 1/10 for f₃₇ in brrb_averaging_identity comes from
normFactor(brrbExt_37) / normFactor(brrbGenType.toFlag) = (1/10).
We verify the automorphism counts independently. -/

/-- CGraph for brrbExt_37: path 0-1-2-3 plus edge 0-4, col [B,R,R,B,R]. -/
def cBrrbExt37 : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 1 && j.val == 2) || (i.val == 2 && j.val == 1) ||
                    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
                    (i.val == 0 && j.val == 4) || (i.val == 4 && j.val == 0)
  col := fun v => if v.val == 0 || v.val == 3 then 1 else 0

-- aut_∅ (all permutations preserving adj+col)
example : cInducedCount cBrrbExt37 cBrrbExt37 = 1 := by native_decide

-- aut_σ (fixing first 4 vertices = BRRB type)
example : tcAutCount 4 cBrrbExt37 = 1 := by native_decide

-- So normFactor = 1 / (1 * 120) = 1/120
-- Q = 1/12, ratio = (1/120)/(1/12) = 1/10 ✓

-- For comparison, check brrbExt_9:
def cBrrbExt9 : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 1 && j.val == 2) || (i.val == 2 && j.val == 1) ||
                    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
                    (i.val == 0 && j.val == 4) || (i.val == 4 && j.val == 0) ||
                    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2)
  col := fun v => if v.val == 0 || v.val == 3 then 1 else 0

example : cInducedCount cBrrbExt9 cBrrbExt9 = 2 := by native_decide
example : tcAutCount 4 cBrrbExt9 = 1 := by native_decide
-- normFactor = 2 / (1 * 120) = 1/60. ratio = (1/60)/(1/12) = 1/5 ✓

/-! ### Extension compatibility analysis

Enumerate ext₂ (v4 adj v1) flags at brrbGenType and identify their forgets. -/

/-- ext₂ flag a: v4(B) adj {v1}. Edges: 0-1,1-2,2-3,1-4. Col: [B,R,R,B,B]. -/
def cBrrbExt2a : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 1 && j.val == 2) || (i.val == 2 && j.val == 1) ||
                    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
                    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1)
  col := fun v => if v.val == 0 || v.val == 3 || v.val == 4 then 1 else 0

/-- ext₂ flag b: v4(R) adj {v1}. Edges: 0-1,1-2,2-3,1-4. Col: [B,R,R,B,R]. -/
def cBrrbExt2b : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 1 && j.val == 2) || (i.val == 2 && j.val == 1) ||
                    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
                    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1)
  col := fun v => if v.val == 0 || v.val == 3 then 1 else 0

/-- ext₂ flag c: v4(R) adj {v1,v3}. Edges: 0-1,1-2,2-3,1-4,3-4. Col: [B,R,R,B,R]. -/
def cBrrbExt2c : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 1 && j.val == 2) || (i.val == 2 && j.val == 1) ||
                    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
                    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
                    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val == 0 || v.val == 3 then 1 else 0

-- Automorphism counts for ext₂ flags
-- Use decide to find correct aut counts
example : cInducedCount cBrrbExt2a cBrrbExt2a = 2 := by native_decide
example : tcAutCount 4 cBrrbExt2a = 1 := by native_decide
-- nf(ext2_a) = 2/(1·120) = 1/60

example : cInducedCount cBrrbExt2b cBrrbExt2b = 1 := by native_decide
example : tcAutCount 4 cBrrbExt2b = 1 := by native_decide
-- nf(ext2_b) = 1/(1·120) = 1/120

example : cInducedCount cBrrbExt2c cBrrbExt2c = 2 := by native_decide
example : tcAutCount 4 cBrrbExt2c = 1 := by native_decide
-- nf(ext2_c) = 2/(1·120) = 1/60

-- Do any ext₂ forgets match ext₁ forgets?
-- ext₁ forgets: cBrrbExt37 (≅sdpFlag37), cBrrbExt9 (≅sdpFlag9), cBrrbExt55 (not yet as CGraph)
-- Check ext₂ forgets against ext₁ forgets
example : cInducedCount cBrrbExt2a cBrrbExt37 = 0 := by native_decide
example : cInducedCount cBrrbExt2b cBrrbExt37 = 0 := by native_decide
example : cInducedCount cBrrbExt2c cBrrbExt37 = 0 := by native_decide
example : cInducedCount cBrrbExt2a cBrrbExt9 = 0 := by native_decide
example : cInducedCount cBrrbExt2b cBrrbExt9 = 0 := by native_decide
-- ext2_c IS isomorphic to cBrrbExt9? Let me check:
example : cInducedCount cBrrbExt2c cBrrbExt9 = 2 := by native_decide

-- Do ext₂ forgets match EACH OTHER?
example : cInducedCount cBrrbExt2a cBrrbExt2b = 0 := by native_decide
example : cInducedCount cBrrbExt2a cBrrbExt2c = 0 := by native_decide
example : cInducedCount cBrrbExt2b cBrrbExt2c = 0 := by native_decide

-- Forget image identification: which ∅-type flag does each product graph match?
-- We define CGraph versions of the relevant SDP flags and check via cInducedCount.

/-- CGraph for Rust F33: K_{3,2} with col [R,R,R,B,B] (Rust [1,1,1,0,0]).
    Lean-converted: col [0,0,0,1,1] = [R,R,R,B,B]. -/
def cSdpF33_lean : CGraph 5 where
  adj := fun i j => (i.val < 3 && j.val ≥ 3) || (i.val ≥ 3 && j.val < 3)
  col := fun v => if v.val ≥ 3 then 1 else 0

/-- CGraph for Rust F34: K_{3,2} with col [R,R,R,R,B] (Rust [1,1,1,1,0]).
    Lean-converted: col [0,0,0,0,1] = [R,R,R,R,B]. -/
def cSdpF34_lean : CGraph 5 where
  adj := fun i j => (i.val < 3 && j.val ≥ 3) || (i.val ≥ 3 && j.val < 3)
  col := fun v => if v.val = 4 then 1 else 0

/-! ### Lean-converted CGraph definitions for ∅-type flags appearing in ⟦h²⟧

Each flag has Lean colours = 1-Rust colours (0=red, 1=black in Lean). -/

/-- sdpFlag9: edges {0-4,1-3,1-4,2-3,2-4}, col [B,R,R,B,R] (Lean [1,0,0,1,0]). -/
def cF9_lean : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 4) || (i.val == 4 && j.val == 0) ||
                    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
                    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
                    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
                    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2)
  col := fun v => if v.val == 0 || v.val == 3 then 1 else 0

/-- sdpFlag37: edges {0-2,1-3,2-4,3-4}, col [R,B,B,R,R] (Lean [0,1,1,0,0]). -/
def cF37_lean : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 2) || (i.val == 2 && j.val == 0) ||
                    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
                    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
                    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val == 1 || v.val == 2 then 1 else 0

/-- sdpFlag55: edges {0-1,0-2,1-3,2-4,3-4}, col [R,R,B,B,R] (Lean [0,0,1,1,0]). -/
def cF55_lean : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 0 && j.val == 2) || (i.val == 2 && j.val == 0) ||
                    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
                    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
                    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val == 2 || v.val == 3 then 1 else 0

/-! ### Forget identification for ALL h² product graphs via native_decide -/

-- F4*F4 adj34=F → which flag?
example : cInducedCount (tcGraph cF4 cF4 false) cF9_lean = 0 := by native_decide
example : cInducedCount (tcGraph cF4 cF4 false) cF37_lean = 0 := by native_decide
example : cInducedCount (tcGraph cF4 cF4 false) cF55_lean = 0 := by native_decide
example : cInducedCount (tcGraph cF4 cF4 false) cSdpF34_lean = 0 := by native_decide
-- F4*F4 has 4R+1B (v1 is B). Not any of the above. It's a NEW flag (F15 or F25).

-- F4*F5 adj34=F → sdpFlag37?
example : cInducedCount (tcGraph cF4 cF5 false) cF37_lean > 0 := by native_decide

-- F4*F5 adj34=T → sdpFlag55?
example : cInducedCount (tcGraph cF4 cF5 true) cF55_lean > 0 := by native_decide

-- F4*F7 adj34=F → which flag? 4R+1B, 5 edges.
example : cInducedCount (tcGraph cF4 cF7 false) cF9_lean = 0 := by native_decide
example : cInducedCount (tcGraph cF4 cF7 false) cF37_lean = 0 := by native_decide
example : cInducedCount (tcGraph cF4 cF7 false) cF55_lean = 0 := by native_decide
example : cInducedCount (tcGraph cF4 cF7 false) cSdpF34_lean = 0 := by native_decide
-- Not F9/F37/F55/F34. Need to identify. Define candidate flags:

/-- F15 Lean-converted: edges {0-4,1-3,1-4,2-3,2-4}, col [R,R,R,R,B] = [0,0,0,0,1]. -/
def cF15_lean : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 4) || (i.val == 4 && j.val == 0) ||
                    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
                    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
                    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
                    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2)
  col := fun v => if v.val == 4 then 1 else 0

/-- F16 Lean-converted: edges {0-3,1-4,2-4,3-4}, col [B,B,B,R,R] = [1,1,1,0,0]. -/
def cF16_lean : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0) ||
                    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
                    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
                    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val ≤ 2 then 1 else 0

/-- F25 Lean-converted: edges {0-3,1-4,2-4,3-4}, col [R,R,R,R,B] = [0,0,0,0,1]. -/
def cF25_lean : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0) ||
                    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
                    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
                    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val == 4 then 1 else 0

-- Forget identification verified:
example : cInducedCount (tcGraph cF4 cF7 false) cF15_lean > 0 := by native_decide  -- F4*F7 → F15 ✓
example : cInducedCount (tcGraph cF4 cF4 false) cF25_lean > 0 := by native_decide  -- F4*F4 → F25 ✓
example : cInducedCount (tcGraph cF5 cF5 false) cF16_lean > 0 := by native_decide  -- F5*F5 → F16 ✓

-- Aut counts for new flags (for normFactor computation)
example : cInducedCount cF15_lean cF15_lean = 2 := by native_decide  -- aut_∅(F15) = 2
example : cInducedCount cF16_lean cF16_lean = 2 := by native_decide  -- aut_∅(F16) = 2
example : cInducedCount cF25_lean cF25_lean = 2 := by native_decide  -- aut_∅(F25) = 2

-- All flags are pairwise distinct (no two match)
example : cInducedCount cF9_lean cF37_lean = 0 := by native_decide
example : cInducedCount cF9_lean cF55_lean = 0 := by native_decide
example : cInducedCount cF9_lean cF15_lean = 0 := by native_decide
example : cInducedCount cF9_lean cF16_lean = 0 := by native_decide
example : cInducedCount cF9_lean cF25_lean = 0 := by native_decide
example : cInducedCount cF9_lean cSdpF34_lean = 0 := by native_decide
example : cInducedCount cF37_lean cF55_lean = 0 := by native_decide
example : cInducedCount cF15_lean cF16_lean = 0 := by native_decide
example : cInducedCount cF15_lean cF25_lean = 0 := by native_decide

-- F5*F5 adj34=F → which flag? Has 2R+3B.
example : cInducedCount (tcGraph cF5 cF5 false) cF9_lean = 0 := by native_decide
example : cInducedCount (tcGraph cF5 cF5 false) cF37_lean = 0 := by native_decide

-- F5*F7 adj34=F → sdpFlag9?
example : cInducedCount (tcGraph cF5 cF7 false) cF9_lean > 0 := by native_decide

-- F7*F7 adj34=F → F34 (already verified)
example : cInducedCount (tcGraph cF7 cF7 false) cSdpF34_lean > 0 := by native_decide
-- NOT F33 (wrong colour count: 2B+3R vs 1B+4R)
example : cInducedCount (tcGraph cF7 cF7 false) cSdpF33_lean = 0 := by native_decide

-- F7*F7 adj34=true has a triangle (1-3-4 or 2-3-4), verify via triangle detection
def hasTriangle (G : CGraph n) : Bool :=
  ((univ : Finset (Fin n × Fin n × Fin n)).filter fun ⟨u, v, w⟩ =>
    u < v && v < w && G.adj u v && G.adj v w && G.adj u w).card > 0

example : hasTriangle (tcGraph cF7 cF7 true) = true := by native_decide
example : hasTriangle (tcGraph cF7 cF7 false) = false := by native_decide

/-! ### Full product evaluation pipeline

Now let's verify ALL 6 products × 2 adj34 values systematically.
For each, we check: joint count, triangle status, and forget match. -/

-- Product evaluation data: (fi, fj, adj34) → (jc, hasTriangle, matchesF?)
-- F4*F4
example : tcJointCount 3 cF4 cF4 (tcGraph cF4 cF4 false) = 2 := by native_decide
example : hasTriangle (tcGraph cF4 cF4 false) = false := by native_decide
example : hasTriangle (tcGraph cF4 cF4 true) = true := by native_decide

-- F4*F5
example : tcJointCount 3 cF4 cF5 (tcGraph cF4 cF5 false) = 1 := by native_decide
example : hasTriangle (tcGraph cF4 cF5 false) = false := by native_decide
example : tcJointCount 3 cF4 cF5 (tcGraph cF4 cF5 true) = 1 := by native_decide
example : hasTriangle (tcGraph cF4 cF5 true) = false := by native_decide

-- F4*F7
example : tcJointCount 3 cF4 cF7 (tcGraph cF4 cF7 false) = 1 := by native_decide
example : hasTriangle (tcGraph cF4 cF7 false) = false := by native_decide
example : hasTriangle (tcGraph cF4 cF7 true) = true := by native_decide

-- F5*F5
example : tcJointCount 3 cF5 cF5 (tcGraph cF5 cF5 false) = 2 := by native_decide
example : hasTriangle (tcGraph cF5 cF5 false) = false := by native_decide
example : hasTriangle (tcGraph cF5 cF5 true) = true := by native_decide

-- F5*F7
example : tcJointCount 3 cF5 cF7 (tcGraph cF5 cF7 false) = 1 := by native_decide
example : hasTriangle (tcGraph cF5 cF7 false) = false := by native_decide
example : hasTriangle (tcGraph cF5 cF7 true) = true := by native_decide

-- F7*F7 (already checked above)

-- Automorphism counts for triangle-free product graphs
example : cInducedCount (tcGraph cF4 cF4 false) (tcGraph cF4 cF4 false) = 2 := by native_decide
example : tcAutCount 3 (tcGraph cF4 cF4 false) = 2 := by native_decide

example : cInducedCount (tcGraph cF4 cF5 false) (tcGraph cF4 cF5 false) = 1 := by native_decide
example : tcAutCount 3 (tcGraph cF4 cF5 false) = 1 := by native_decide

example : cInducedCount (tcGraph cF4 cF5 true) (tcGraph cF4 cF5 true) = 2 := by native_decide
example : tcAutCount 3 (tcGraph cF4 cF5 true) = 1 := by native_decide

example : cInducedCount (tcGraph cF4 cF7 false) (tcGraph cF4 cF7 false) = 2 := by native_decide
example : tcAutCount 3 (tcGraph cF4 cF7 false) = 1 := by native_decide

example : cInducedCount (tcGraph cF5 cF5 false) (tcGraph cF5 cF5 false) = 2 := by native_decide
example : tcAutCount 3 (tcGraph cF5 cF5 false) = 2 := by native_decide

example : cInducedCount (tcGraph cF5 cF7 false) (tcGraph cF5 cF7 false) = 2 := by native_decide
example : tcAutCount 3 (tcGraph cF5 cF7 false) = 1 := by native_decide

/-! ### Typed embedding bridge

Connects the computable `tcJointCount` to the abstract `genJointCount`,
adapting the pattern of `cInducedCount_eq_genInducedCount'`. -/

/-- Helper: the Bool adjacency conditions for a single typed embedding are equivalent
    to `GenInducedEmbedding` + compat. Adapts `adj_iff` from the ∅-type bridge. -/
private theorem typed_emb_iff {n₁ n₃ : Nat} (k : Nat)
    (F : CGraph n₁) (G : CGraph n₃)
    (_hFs : ∀ i j, F.adj i j = F.adj j i) (_hFi : ∀ i, F.adj i i = false)
    (_hGs : ∀ i j, G.adj i j = G.adj j i) (_hGi : ∀ i, G.adj i i = false)
    (σ : GenFlagType CG2) (hle₁ : σ.size ≤ n₁) (hle₃ : σ.size ≤ n₃) (hk : k = σ.size)
    (hFstr : CG2.comap (Fin.castLE hle₁) (⟨SimpleGraph.fromRel (fun i j : Fin n₁ => F.adj i j),
      F.col⟩ : CG2.Str n₁) = σ.str)
    (hGstr : CG2.comap (Fin.castLE hle₃) (⟨SimpleGraph.fromRel (fun i j : Fin n₃ => G.adj i j),
      G.col⟩ : CG2.Str n₃) = σ.str)
    (f : Fin n₁ → Fin n₃) (hinj : Function.Injective f)
    (hcol : ∀ i, F.col i = G.col (f i))
    (hadj : ∀ i j, F.adj i j = G.adj (f i) (f j))
    (hfix : ∀ i : Fin n₁, i.val < k → (f i).val = i.val) :
    ∃ (e : GenInducedEmbedding CG2 σ (F.toTypedGenFlag σ hle₁ hFstr)
        (G.toTypedGenFlag σ hle₃ hGstr)), e.toFun = f := by
  refine ⟨⟨f, hinj, ?_, ?_⟩, rfl⟩
  · -- isInduced: CG2.comap f G.str = F.str
    simp only [CGraph.toTypedGenFlag, colouredGraphUniverse]
    apply Prod.ext
    · ext u v
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
    · funext u; exact (hcol u).symm
  · -- compat: f(F.embedding(i)) = G.embedding(i)
    intro i
    simp only [CGraph.toTypedGenFlag, Function.Embedding.coeFn_mk]
    apply Fin.ext
    exact hfix (Fin.castLE hle₁ i) (by rw [hk]; exact i.isLt)

/-- The `tcJointCount` equals `genJointCount` when the CGraph adjacencies are
    symmetric and irreflexive. -/
theorem tcJointCount_eq_genJointCount {n₁ n₂ n₃ : Nat}
    (F₁ : CGraph n₁) (F₂ : CGraph n₂) (G : CGraph n₃)
    (hF₁s : ∀ i j, F₁.adj i j = F₁.adj j i) (hF₁i : ∀ i, F₁.adj i i = false)
    (hF₂s : ∀ i j, F₂.adj i j = F₂.adj j i) (hF₂i : ∀ i, F₂.adj i i = false)
    (hGs : ∀ i j, G.adj i j = G.adj j i) (hGi : ∀ i, G.adj i i = false)
    (σ : GenFlagType CG2) (hle₁ : σ.size ≤ n₁) (hle₂ : σ.size ≤ n₂) (hle₃ : σ.size ≤ n₃)
    (hF₁str : CG2.comap (Fin.castLE hle₁) (⟨SimpleGraph.fromRel (fun i j : Fin n₁ => F₁.adj i j),
      F₁.col⟩ : CG2.Str n₁) = σ.str)
    (hF₂str : CG2.comap (Fin.castLE hle₂) (⟨SimpleGraph.fromRel (fun i j : Fin n₂ => F₂.adj i j),
      F₂.col⟩ : CG2.Str n₂) = σ.str)
    (hGstr : CG2.comap (Fin.castLE hle₃) (⟨SimpleGraph.fromRel (fun i j : Fin n₃ => G.adj i j),
      G.col⟩ : CG2.Str n₃) = σ.str) :
    tcJointCount σ.size F₁ F₂ G =
      genJointCount CG2 σ (F₁.toTypedGenFlag σ hle₁ hF₁str)
        (F₂.toTypedGenFlag σ hle₂ hF₂str) (G.toTypedGenFlag σ hle₃ hGstr) := by
  unfold tcJointCount genJointCount
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  -- Helper: Bool adj/col conditions ↔ comap structure equality (for F₁)
  have adj_iff₁ : ∀ (f : Fin n₁ → Fin n₃), Function.Injective f →
      (((∀ i : Fin n₁, F₁.col i = G.col (f i)) ∧
       (∀ i j : Fin n₁, F₁.adj i j = G.adj (f i) (f j))) ↔
      (colouredGraphUniverse 2).comap f
        (⟨SimpleGraph.fromRel (fun i j : Fin n₃ => G.adj i j), G.col⟩ : CG2.Str n₃) =
        (⟨SimpleGraph.fromRel (fun i j : Fin n₁ => F₁.adj i j), F₁.col⟩ : CG2.Str n₁)) := by
    intro f hinj
    simp only [colouredGraphUniverse]
    constructor
    · rintro ⟨hcol, hadj⟩
      apply Prod.ext
      · ext u v
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
      · funext u; exact (hcol u).symm
    · intro hstr
      obtain ⟨hg, hc⟩ := Prod.mk.inj hstr
      refine ⟨fun i => (congr_fun hc i).symm, fun i j => ?_⟩
      by_cases hij : i = j
      · subst hij; simp only [hF₁i, hGi]
      · have hge : ∀ a b : Fin n₁,
            (SimpleGraph.comap f (SimpleGraph.fromRel fun i j => ↑(G.adj i j))).Adj a b ↔
            (SimpleGraph.fromRel fun i j => ↑(F₁.adj i j)).Adj a b := by
          intro a b
          rw [show (SimpleGraph.fromRel fun i j => ↑(G.adj i j)).comap f =
                  SimpleGraph.fromRel fun i j => ↑(F₁.adj i j) from by exact_mod_cast hg]
        simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj] at hge
        have fne : f i ≠ f j := fun h => hij (hinj h)
        cases hF : F₁.adj i j <;> cases hG : G.adj (f i) (f j)
        · rfl
        · exfalso
          have h1 : (f i ≠ f j ∧ ((↑(G.adj (f i) (f j)) : Prop) ∨ (↑(G.adj (f j) (f i))))) :=
            ⟨fne, Or.inl (by simp [hG])⟩
          have h2 := (hge i j).mp h1
          obtain ⟨_, h3⟩ := h2
          cases h3 with
          | inl h => simp [hF] at h
          | inr h =>
            have : F₁.adj j i = false := by rw [← hF₁s i j]; exact hF
            exact absurd h (by rw [this]; exact Bool.false_ne_true)
        · exfalso
          have h1 : (i ≠ j ∧ ((↑(F₁.adj i j) : Prop) ∨ (↑(F₁.adj j i)))) :=
            ⟨hij, Or.inl (by simp [hF])⟩
          have h2 := (hge i j).mpr h1
          obtain ⟨_, h3⟩ := h2
          cases h3 with
          | inl h => simp [hG] at h
          | inr h =>
            have : G.adj (f j) (f i) = false := by rw [← hGs (f i) (f j)]; exact hG
            exact absurd h (by rw [this]; exact Bool.false_ne_true)
        · rfl
  -- Same for F₂
  have adj_iff₂ : ∀ (f : Fin n₂ → Fin n₃), Function.Injective f →
      (((∀ i : Fin n₂, F₂.col i = G.col (f i)) ∧
       (∀ i j : Fin n₂, F₂.adj i j = G.adj (f i) (f j))) ↔
      (colouredGraphUniverse 2).comap f
        (⟨SimpleGraph.fromRel (fun i j : Fin n₃ => G.adj i j), G.col⟩ : CG2.Str n₃) =
        (⟨SimpleGraph.fromRel (fun i j : Fin n₂ => F₂.adj i j), F₂.col⟩ : CG2.Str n₂)) := by
    intro f hinj
    simp only [colouredGraphUniverse]
    constructor
    · rintro ⟨hcol, hadj⟩
      apply Prod.ext
      · ext u v
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
      · funext u; exact (hcol u).symm
    · intro hstr
      obtain ⟨hg, hc⟩ := Prod.mk.inj hstr
      refine ⟨fun i => (congr_fun hc i).symm, fun i j => ?_⟩
      by_cases hij : i = j
      · subst hij; simp only [hF₂i, hGi]
      · have hge : ∀ a b : Fin n₂,
            (SimpleGraph.comap f (SimpleGraph.fromRel fun i j => ↑(G.adj i j))).Adj a b ↔
            (SimpleGraph.fromRel fun i j => ↑(F₂.adj i j)).Adj a b := by
          intro a b
          rw [show (SimpleGraph.fromRel fun i j => ↑(G.adj i j)).comap f =
                  SimpleGraph.fromRel fun i j => ↑(F₂.adj i j) from by exact_mod_cast hg]
        simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj] at hge
        have fne : f i ≠ f j := fun h => hij (hinj h)
        cases hF : F₂.adj i j <;> cases hG : G.adj (f i) (f j)
        · rfl
        · exfalso
          have h1 : (f i ≠ f j ∧ ((↑(G.adj (f i) (f j)) : Prop) ∨ (↑(G.adj (f j) (f i))))) :=
            ⟨fne, Or.inl (by simp [hG])⟩
          have h2 := (hge i j).mp h1
          obtain ⟨_, h3⟩ := h2
          cases h3 with
          | inl h => simp [hF] at h
          | inr h =>
            have : F₂.adj j i = false := by rw [← hF₂s i j]; exact hF
            exact absurd h (by rw [this]; exact Bool.false_ne_true)
        · exfalso
          have h1 : (i ≠ j ∧ ((↑(F₂.adj i j) : Prop) ∨ (↑(F₂.adj j i)))) :=
            ⟨hij, Or.inl (by simp [hF])⟩
          have h2 := (hge i j).mpr h1
          obtain ⟨_, h3⟩ := h2
          cases h3 with
          | inl h => simp [hG] at h
          | inr h =>
            have : G.adj (f j) (f i) = false := by rw [← hGs (f i) (f j)]; exact hG
            exact absurd h (by rw [this]; exact Bool.false_ne_true)
        · rfl
  -- Helper: i ∈ Set.range (Fin.castLE hle₃) ↔ i.val < σ.size
  have range_iff : ∀ i : Fin n₃, i ∈ Set.range (Fin.castLE hle₃) ↔ i.val < σ.size := by
    intro i
    rw [Fin.range_castLE]
    simp only [Set.mem_setOf_eq]
  -- Helper: extract Bool conditions from GenInducedEmbedding (for F₁)
  have emb_to_bool₁ : ∀ (e : GenInducedEmbedding CG2 σ (F₁.toTypedGenFlag σ hle₁ hF₁str)
      (G.toTypedGenFlag σ hle₃ hGstr)),
      (∀ i : Fin n₁, F₁.col i = G.col (e.toFun i)) ∧
      (∀ i j : Fin n₁, F₁.adj i j = G.adj (e.toFun i) (e.toFun j)) ∧
      (∀ i : Fin n₁, i.val < σ.size → (e.toFun i).val = i.val) := by
    intro e
    have hac := (adj_iff₁ e.toFun e.injective).mpr e.isInduced
    refine ⟨hac.1, hac.2, fun i hi => ?_⟩
    have := e.compat ⟨i.val, hi⟩
    simp only [CGraph.toTypedGenFlag, Function.Embedding.coeFn_mk] at this
    exact congr_arg Fin.val this
  -- Same for F₂
  have emb_to_bool₂ : ∀ (e : GenInducedEmbedding CG2 σ (F₂.toTypedGenFlag σ hle₂ hF₂str)
      (G.toTypedGenFlag σ hle₃ hGstr)),
      (∀ i : Fin n₂, F₂.col i = G.col (e.toFun i)) ∧
      (∀ i j : Fin n₂, F₂.adj i j = G.adj (e.toFun i) (e.toFun j)) ∧
      (∀ i : Fin n₂, i.val < σ.size → (e.toFun i).val = i.val) := by
    intro e
    have hac := (adj_iff₂ e.toFun e.injective).mpr e.isInduced
    refine ⟨hac.1, hac.2, fun i hi => ?_⟩
    have := e.compat ⟨i.val, hi⟩
    simp only [CGraph.toTypedGenFlag, Function.Embedding.coeFn_mk] at this
    exact congr_arg Fin.val this
  -- Helper: translate overlap condition
  have overlap_fwd : ∀ (f₁ : Fin n₁ → Fin n₃) (f₂ : Fin n₂ → Fin n₃),
      (∀ i : Fin n₃, ((∃ a, f₁ a = i) ∧ (∃ b, f₂ b = i)) ↔ i.val < σ.size) →
      ∀ i : Fin n₃, (i ∈ Set.range f₁ ∧ i ∈ Set.range f₂) ↔
        i ∈ Set.range (Fin.castLE hle₃) := by
    intro f₁ f₂ h i
    rw [Set.mem_range, Set.mem_range, range_iff]
    exact h i
  have overlap_bwd : ∀ (f₁ : Fin n₁ → Fin n₃) (f₂ : Fin n₂ → Fin n₃),
      (∀ i : Fin n₃, (i ∈ Set.range f₁ ∧ i ∈ Set.range f₂) ↔
        i ∈ Set.range (Fin.castLE hle₃)) →
      ∀ i : Fin n₃, ((∃ a, f₁ a = i) ∧ (∃ b, f₂ b = i)) ↔ i.val < σ.size := by
    intro f₁ f₂ h i
    rw [← Set.mem_range, ← Set.mem_range, ← range_iff]
    exact h i
  -- Helper: translate cover condition
  have cover_fwd : ∀ (f₁ : Fin n₁ → Fin n₃) (f₂ : Fin n₂ → Fin n₃),
      (∀ i : Fin n₃, (∃ a, f₁ a = i) ∨ (∃ b, f₂ b = i)) →
      ∀ i : Fin n₃, i ∈ Set.range f₁ ∨ i ∈ Set.range f₂ := by
    intro f₁ f₂ h i; rw [Set.mem_range, Set.mem_range]; exact h i
  have cover_bwd : ∀ (f₁ : Fin n₁ → Fin n₃) (f₂ : Fin n₂ → Fin n₃),
      (∀ i : Fin n₃, i ∈ Set.range f₁ ∨ i ∈ Set.range f₂) →
      ∀ i : Fin n₃, (∃ a, f₁ a = i) ∨ (∃ b, f₂ b = i) := by
    intro f₁ f₂ h i; rw [← Set.mem_range, ← Set.mem_range]; exact h i
  -- Helper: Bool compat condition → Fin.ext proof
  have compat_proof₁ : ∀ (f : Fin n₁ → Fin n₃)
      (hfix : ∀ i : Fin n₁, i.val < σ.size → (f i).val = i.val)
      (i : Fin σ.size),
      f ((F₁.toTypedGenFlag σ hle₁ hF₁str).embedding i) =
        (G.toTypedGenFlag σ hle₃ hGstr).embedding i := by
    intro f hfix i
    simp only [CGraph.toTypedGenFlag, Function.Embedding.coeFn_mk]
    exact Fin.ext (hfix (Fin.castLE hle₁ i) i.isLt)
  have compat_proof₂ : ∀ (f : Fin n₂ → Fin n₃)
      (hfix : ∀ i : Fin n₂, i.val < σ.size → (f i).val = i.val)
      (i : Fin σ.size),
      f ((F₂.toTypedGenFlag σ hle₂ hF₂str).embedding i) =
        (G.toTypedGenFlag σ hle₃ hGstr).embedding i := by
    intro f hfix i
    simp only [CGraph.toTypedGenFlag, Function.Embedding.coeFn_mk]
    exact Fin.ext (hfix (Fin.castLE hle₂ i) i.isLt)
  -- Build the equivalence using term-mode construction
  exact {
    toFun := fun ⟨⟨f₁, f₂⟩, hf⟩ =>
      ⟨⟨⟨f₁, (Finset.mem_filter.mp hf).2.1,
          (adj_iff₁ f₁ (Finset.mem_filter.mp hf).2.1).mp
            ⟨(Finset.mem_filter.mp hf).2.2.1, (Finset.mem_filter.mp hf).2.2.2.1⟩,
          compat_proof₁ f₁ (Finset.mem_filter.mp hf).2.2.2.2.1⟩,
        ⟨f₂, (Finset.mem_filter.mp hf).2.2.2.2.2.1,
          (adj_iff₂ f₂ (Finset.mem_filter.mp hf).2.2.2.2.2.1).mp
            ⟨(Finset.mem_filter.mp hf).2.2.2.2.2.2.1,
             (Finset.mem_filter.mp hf).2.2.2.2.2.2.2.1⟩,
          compat_proof₂ f₂ (Finset.mem_filter.mp hf).2.2.2.2.2.2.2.2.1⟩⟩,
       overlap_fwd f₁ f₂ (Finset.mem_filter.mp hf).2.2.2.2.2.2.2.2.2.1,
       cover_fwd f₁ f₂ (Finset.mem_filter.mp hf).2.2.2.2.2.2.2.2.2.2⟩
    invFun := fun x =>
      ⟨⟨x.val.1.toFun, x.val.2.toFun⟩, Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
         x.val.1.injective,
         (emb_to_bool₁ x.val.1).1, (emb_to_bool₁ x.val.1).2.1, (emb_to_bool₁ x.val.1).2.2,
         x.val.2.injective,
         (emb_to_bool₂ x.val.2).1, (emb_to_bool₂ x.val.2).2.1, (emb_to_bool₂ x.val.2).2.2,
         overlap_bwd x.val.1.toFun x.val.2.toFun x.prop.1,
         cover_bwd x.val.1.toFun x.val.2.toFun x.prop.2⟩⟩
    left_inv := fun ⟨⟨f₁, f₂⟩, hf⟩ => Subtype.ext rfl
    right_inv := fun ⟨⟨e₁, e₂⟩, h⟩ => by
      have gie_ext : ∀ {F₀ G₀ : GenFlag CG2 σ} (a b : GenInducedEmbedding CG2 σ F₀ G₀),
            a.toFun = b.toFun → a = b := by
        intro F₀ G₀ a b hab; cases a; cases b; simp only [GenInducedEmbedding.mk.injEq]; exact hab
      apply Subtype.ext; apply Prod.ext
      · apply gie_ext
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_imp]
      · apply gie_ext
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_imp]
  }

/-! ### Bridge proofs for F77_witness numerical facts

These proofs connect the abstract GenFlag counts (genFlagAutCount, genJointCount)
to computable CGraph counts (cInducedCount, tcJointCount) via the bridge theorems,
then verify by native_decide. -/

private theorem F77_witness_forget_eq_toGenFlag :
    F77_witness.forget = (tcGraph cF7 cF7 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, F77_witness, CGraph.toGenFlag, tcGraph, cF7]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem F77_witness_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F77_witness.forget = 6 := by
  rw [F77_witness_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cF7 cF7 false) (tcGraph cF7 cF7 false) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem cs1Flag7_eq_cF7_toTypedGenFlag :
    cs1Flag7 = cF7.toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, cF7]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [cs1Flag7, CGraph.toTypedGenFlag, cF7]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

private theorem F77_witness_eq_tcGraph_toTypedGenFlag :
    F77_witness = (tcGraph cF7 cF7 false).toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, tcGraph, cF7]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [F77_witness, CGraph.toTypedGenFlag, tcGraph, cF7]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem F77_witness_jointCount_bridge :
    genJointCount CG2 csType7 cs1Flag7 cs1Flag7 F77_witness = 2 := by
  rw [cs1Flag7_eq_cF7_toTypedGenFlag, F77_witness_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cF7 cF7 (tcGraph cF7 cF7 false) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  change tcJointCount 3 cF7 cF7 (tcGraph cF7 cF7 false) = 2
  native_decide

/-! ### Bridge proofs for cs1Flag4 and cs1Flag5 -/

private theorem cs1Flag4_eq_cF4_toTypedGenFlag :
    cs1Flag4 = cF4.toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, cF4]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [cs1Flag4, CGraph.toTypedGenFlag, cF4]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

private theorem cs1Flag5_eq_cF5_toTypedGenFlag :
    cs1Flag5 = cF5.toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, cF5]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [cs1Flag5, CGraph.toTypedGenFlag, cF5]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

/-! ### Bridge proofs for F44_witness -/

private theorem F44_witness_forget_eq_toGenFlag :
    F44_witness.forget = (tcGraph cF4 cF4 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, F44_witness, CGraph.toGenFlag, tcGraph, cF4]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem F44_witness_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F44_witness.forget = 2 := by
  rw [F44_witness_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cF4 cF4 false) (tcGraph cF4 cF4 false) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem F44_witness_eq_tcGraph_toTypedGenFlag :
    F44_witness = (tcGraph cF4 cF4 false).toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, tcGraph, cF4]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [F44_witness, CGraph.toTypedGenFlag, tcGraph, cF4]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem F44_witness_jointCount_bridge :
    genJointCount CG2 csType7 cs1Flag4 cs1Flag4 F44_witness = 2 := by
  rw [cs1Flag4_eq_cF4_toTypedGenFlag, F44_witness_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cF4 cF4 (tcGraph cF4 cF4 false) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  change tcJointCount 3 cF4 cF4 (tcGraph cF4 cF4 false) = 2
  native_decide

/-! ### Bridge proofs for F47_witness -/

private theorem F47_witness_forget_eq_toGenFlag :
    F47_witness.forget = (tcGraph cF4 cF7 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, F47_witness, CGraph.toGenFlag, tcGraph, cF4, cF7]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem F47_witness_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F47_witness.forget = 2 := by
  rw [F47_witness_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cF4 cF7 false) (tcGraph cF4 cF7 false) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem F47_witness_eq_tcGraph_toTypedGenFlag :
    F47_witness = (tcGraph cF4 cF7 false).toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, tcGraph, cF4, cF7]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [F47_witness, CGraph.toTypedGenFlag, tcGraph, cF4, cF7]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem F47_witness_jointCount_bridge :
    genJointCount CG2 csType7 cs1Flag4 cs1Flag7 F47_witness = 1 := by
  rw [cs1Flag4_eq_cF4_toTypedGenFlag, cs1Flag7_eq_cF7_toTypedGenFlag,
      F47_witness_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cF4 cF7 (tcGraph cF4 cF7 false) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  change tcJointCount 3 cF4 cF7 (tcGraph cF4 cF7 false) = 1
  native_decide

/-! ### Bridge proofs for F55_witness -/

private theorem F55_witness_forget_eq_toGenFlag :
    F55_witness.forget = (tcGraph cF5 cF5 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, F55_witness, CGraph.toGenFlag, tcGraph, cF5]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem F55_witness_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F55_witness.forget = 2 := by
  rw [F55_witness_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cF5 cF5 false) (tcGraph cF5 cF5 false) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem F55_witness_eq_tcGraph_toTypedGenFlag :
    F55_witness = (tcGraph cF5 cF5 false).toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, tcGraph, cF5]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [F55_witness, CGraph.toTypedGenFlag, tcGraph, cF5]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem F55_witness_jointCount_bridge :
    genJointCount CG2 csType7 cs1Flag5 cs1Flag5 F55_witness = 2 := by
  rw [cs1Flag5_eq_cF5_toTypedGenFlag, F55_witness_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cF5 cF5 (tcGraph cF5 cF5 false) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  change tcJointCount 3 cF5 cF5 (tcGraph cF5 cF5 false) = 2
  native_decide

/-! ### Bridge proofs for F57_witness -/

private theorem F57_witness_forget_eq_toGenFlag :
    F57_witness.forget = (tcGraph cF5 cF7 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, F57_witness, CGraph.toGenFlag, tcGraph, cF5, cF7]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem F57_witness_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F57_witness.forget = 2 := by
  rw [F57_witness_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cF5 cF7 false) (tcGraph cF5 cF7 false) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem F57_witness_eq_tcGraph_toTypedGenFlag :
    F57_witness = (tcGraph cF5 cF7 false).toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, tcGraph, cF5, cF7]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [F57_witness, CGraph.toTypedGenFlag, tcGraph, cF5, cF7]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem F57_witness_jointCount_bridge :
    genJointCount CG2 csType7 cs1Flag5 cs1Flag7 F57_witness = 1 := by
  rw [cs1Flag5_eq_cF5_toTypedGenFlag, cs1Flag7_eq_cF7_toTypedGenFlag,
      F57_witness_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cF5 cF7 (tcGraph cF5 cF7 false) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  change tcJointCount 3 cF5 cF7 (tcGraph cF5 cF7 false) = 1
  native_decide

/-! ### Bridge proofs for F45_witness_false -/

private theorem F45_witness_false_forget_eq_toGenFlag :
    F45_witness_false.forget = (tcGraph cF4 cF5 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, F45_witness_false, CGraph.toGenFlag, tcGraph, cF4, cF5]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem F45_witness_false_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F45_witness_false.forget = 1 := by
  rw [F45_witness_false_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cF4 cF5 false) (tcGraph cF4 cF5 false) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem F45_witness_false_eq_tcGraph_toTypedGenFlag :
    F45_witness_false = (tcGraph cF4 cF5 false).toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, tcGraph, cF4, cF5]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [F45_witness_false, CGraph.toTypedGenFlag, tcGraph, cF4, cF5]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem F45_witness_false_jointCount_bridge :
    genJointCount CG2 csType7 cs1Flag4 cs1Flag5 F45_witness_false = 1 := by
  rw [cs1Flag4_eq_cF4_toTypedGenFlag, cs1Flag5_eq_cF5_toTypedGenFlag,
      F45_witness_false_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cF4 cF5 (tcGraph cF4 cF5 false) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  change tcJointCount 3 cF4 cF5 (tcGraph cF4 cF5 false) = 1
  native_decide

/-! ### Bridge proofs for F45_witness_true -/

private theorem F45_witness_true_forget_eq_toGenFlag :
    F45_witness_true.forget = (tcGraph cF4 cF5 true).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, F45_witness_true, CGraph.toGenFlag, tcGraph, cF4, cF5]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem F45_witness_true_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F45_witness_true.forget = 2 := by
  rw [F45_witness_true_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cF4 cF5 true) (tcGraph cF4 cF5 true) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem F45_witness_true_eq_tcGraph_toTypedGenFlag :
    F45_witness_true = (tcGraph cF4 cF5 true).toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, tcGraph, cF4, cF5]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [F45_witness_true, CGraph.toTypedGenFlag, tcGraph, cF4, cF5]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem F45_witness_true_jointCount_bridge :
    genJointCount CG2 csType7 cs1Flag4 cs1Flag5 F45_witness_true = 1 := by
  rw [cs1Flag4_eq_cF4_toTypedGenFlag, cs1Flag5_eq_cF5_toTypedGenFlag,
      F45_witness_true_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cF4 cF5 (tcGraph cF4 cF5 true) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  change tcJointCount 3 cF4 cF5 (tcGraph cF4 cF5 true) = 1
  native_decide

/-! ### cs1Flag3 CGraph and ℓ² product data -/

/-- Concrete CGraph for cs1Flag3: 4 vertices, edges 0-1, 0-2, 0-3, col [R,B,R,R]. -/
def cF3 : CGraph 4 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 0 && j.val == 2) || (i.val == 2 && j.val == 0) ||
                    (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0)
  col := fun v => if v.val == 1 then 1 else 0

/-! ### F3×F3 product data -/

-- F33 adj34=false: star graph {0-1,0-2,0-3,0-4}, col [R,B,R,R,R]
example : tcJointCount 3 cF3 cF3 (tcGraph cF3 cF3 false) = 2 := by native_decide
example : hasTriangle (tcGraph cF3 cF3 false) = false := by native_decide
-- F33 adj34=true: {0-1,0-2,0-3,0-4,3-4}, has triangle {0,3,4}
example : hasTriangle (tcGraph cF3 cF3 true) = true := by native_decide

-- Automorphism counts for F33 adj34=false
example : cInducedCount (tcGraph cF3 cF3 false) (tcGraph cF3 cF3 false) = 6 := by native_decide
example : tcAutCount 3 (tcGraph cF3 cF3 false) = 2 := by native_decide

/-! ### F3×F4 product data -/

-- F34 adj34=false: {0-1,0-2,0-3,1-4}, col [R,B,R,R,R]
example : tcJointCount 3 cF3 cF4 (tcGraph cF3 cF4 false) = 1 := by native_decide
example : hasTriangle (tcGraph cF3 cF4 false) = false := by native_decide
-- F34 adj34=true: {0-1,0-2,0-3,1-4,3-4}, triangle-free
example : tcJointCount 3 cF3 cF4 (tcGraph cF3 cF4 true) = 1 := by native_decide
example : hasTriangle (tcGraph cF3 cF4 true) = false := by native_decide

-- Automorphism counts
example : cInducedCount (tcGraph cF3 cF4 false) (tcGraph cF3 cF4 false) = 2 := by native_decide
example : tcAutCount 3 (tcGraph cF3 cF4 false) = 1 := by native_decide
example : cInducedCount (tcGraph cF3 cF4 true) (tcGraph cF3 cF4 true) = 1 := by native_decide
example : tcAutCount 3 (tcGraph cF3 cF4 true) = 1 := by native_decide

/-! ### F3×F5 product data -/

-- F35 adj34=false: {0-1,0-2,0-3,2-4}, col [R,B,R,R,B]
example : tcJointCount 3 cF3 cF5 (tcGraph cF3 cF5 false) = 1 := by native_decide
example : hasTriangle (tcGraph cF3 cF5 false) = false := by native_decide
-- F35 adj34=true: {0-1,0-2,0-3,2-4,3-4}, triangle-free
example : tcJointCount 3 cF3 cF5 (tcGraph cF3 cF5 true) = 1 := by native_decide
example : hasTriangle (tcGraph cF3 cF5 true) = false := by native_decide

-- Automorphism counts
example : cInducedCount (tcGraph cF3 cF5 false) (tcGraph cF3 cF5 false) = 1 := by native_decide
example : tcAutCount 3 (tcGraph cF3 cF5 false) = 1 := by native_decide
example : cInducedCount (tcGraph cF3 cF5 true) (tcGraph cF3 cF5 true) = 2 := by native_decide
example : tcAutCount 3 (tcGraph cF3 cF5 true) = 1 := by native_decide

/-! ### F3×F7 product data -/

-- F37 adj34=false: {0-1,0-2,0-3,1-4,2-4}, col [R,B,R,R,R]
example : tcJointCount 3 cF3 cF7 (tcGraph cF3 cF7 false) = 1 := by native_decide
example : hasTriangle (tcGraph cF3 cF7 false) = false := by native_decide
-- F37 adj34=true: {0-1,0-2,0-3,1-4,2-4,3-4}, triangle-free
example : tcJointCount 3 cF3 cF7 (tcGraph cF3 cF7 true) = 1 := by native_decide
example : hasTriangle (tcGraph cF3 cF7 true) = false := by native_decide

-- Automorphism counts
example : cInducedCount (tcGraph cF3 cF7 false) (tcGraph cF3 cF7 false) = 1 := by native_decide
example : tcAutCount 3 (tcGraph cF3 cF7 false) = 1 := by native_decide
example : cInducedCount (tcGraph cF3 cF7 true) (tcGraph cF3 cF7 true) = 4 := by native_decide
example : tcAutCount 3 (tcGraph cF3 cF7 true) = 1 := by native_decide

/-! ### Forget identification for ℓ² product graphs -/

-- New CGraph definitions for flags appearing in ℓ² that are NOT in h²

/-- Rust F5 (Lean-converted): star K_{1,4}, edges {0-4,1-4,2-4,3-4},
    col Rust [1,1,1,0,1] = Lean [0,0,0,1,0]. Center at v4. -/
def cRustF5_lean : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 4) || (i.val == 4 && j.val == 0) ||
                    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
                    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
                    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val == 3 then 1 else 0

/-- Rust F12 (Lean-converted): edges {0-4,1-3,1-4,2-3,2-4},
    col Rust [1,1,0,1,1] = Lean [0,0,1,0,0]. -/
def cRustF12_lean : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 4) || (i.val == 4 && j.val == 0) ||
                    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
                    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
                    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
                    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2)
  col := fun v => if v.val == 2 then 1 else 0

/-- Rust F17 (Lean-converted): edges {0-3,1-4,2-4,3-4},
    col Rust [0,1,0,1,1] = Lean [1,0,1,0,0]. -/
def cRustF17_lean : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0) ||
                    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
                    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
                    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val == 0 || v.val == 2 then 1 else 0

/-- Rust F24 (Lean-converted): edges {0-3,1-4,2-4,3-4},
    col Rust [1,1,1,0,1] = Lean [0,0,0,1,0]. -/
def cRustF24_lean : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0) ||
                    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
                    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
                    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val == 3 then 1 else 0

/-- Rust F32 (Lean-converted): K_{3,2}, edges {0-3,0-4,1-3,1-4,2-3,2-4},
    col Rust [1,1,0,1,1] = Lean [0,0,1,0,0]. -/
def cRustF32_lean : CGraph 5 where
  adj := fun i j => (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0) ||
                    (i.val == 0 && j.val == 4) || (i.val == 4 && j.val == 0) ||
                    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
                    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
                    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
                    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2)
  col := fun v => if v.val == 2 then 1 else 0

-- Aut counts for new flags
example : cInducedCount cRustF5_lean cRustF5_lean = 6 := by native_decide
example : cInducedCount cRustF12_lean cRustF12_lean = 1 := by native_decide
example : cInducedCount cRustF17_lean cRustF17_lean = 1 := by native_decide
example : cInducedCount cRustF24_lean cRustF24_lean = 2 := by native_decide
example : cInducedCount cRustF32_lean cRustF32_lean = 4 := by native_decide

-- Forget identification: verified positive matches
-- F33_false → Rust F5 (star K_{1,4}, 1B)
example : cInducedCount (tcGraph cF3 cF3 false) cRustF5_lean > 0 := by native_decide
-- F34_false → Rust F24 (4 edges, 1B)
example : cInducedCount (tcGraph cF3 cF4 false) cRustF24_lean > 0 := by native_decide
-- F34_true → Rust F12 (5 edges, 1B)
example : cInducedCount (tcGraph cF3 cF4 true) cRustF12_lean > 0 := by native_decide
-- F35_false → Rust F17 (4 edges, 2B)
example : cInducedCount (tcGraph cF3 cF5 false) cRustF17_lean > 0 := by native_decide
-- F35_true → sdpFlag9 (5 edges, 2B)
example : cInducedCount (tcGraph cF3 cF5 true) cF9_lean > 0 := by native_decide
-- F37_false → Rust F12 (5 edges, 1B) — SAME as F34_true
example : cInducedCount (tcGraph cF3 cF7 false) cRustF12_lean > 0 := by native_decide
-- F37_true → Rust F32 (K_{3,2}, 1B)
example : cInducedCount (tcGraph cF3 cF7 true) cRustF32_lean > 0 := by native_decide
-- F34_true ≅ F37_false (both map to F12)
example : cInducedCount (tcGraph cF3 cF4 true) (tcGraph cF3 cF7 false) > 0 := by native_decide

-- New flags are pairwise distinct from each other and from known flags
example : cInducedCount cRustF5_lean cRustF12_lean = 0 := by native_decide
example : cInducedCount cRustF5_lean cRustF17_lean = 0 := by native_decide
example : cInducedCount cRustF5_lean cRustF24_lean = 0 := by native_decide
example : cInducedCount cRustF5_lean cRustF32_lean = 0 := by native_decide
example : cInducedCount cRustF12_lean cRustF17_lean = 0 := by native_decide
example : cInducedCount cRustF12_lean cRustF24_lean = 0 := by native_decide
example : cInducedCount cRustF12_lean cRustF32_lean = 0 := by native_decide
example : cInducedCount cRustF17_lean cRustF24_lean = 0 := by native_decide
example : cInducedCount cRustF17_lean cRustF32_lean = 0 := by native_decide
example : cInducedCount cRustF24_lean cRustF32_lean = 0 := by native_decide

-- Non-iso checks for dual-witness pairs
-- F34: false and true witnesses are non-isomorphic
example : cInducedCount (tcGraph cF3 cF4 false) (tcGraph cF3 cF4 true) = 0 := by native_decide
-- F35: false and true witnesses are non-isomorphic
example : cInducedCount (tcGraph cF3 cF5 false) (tcGraph cF3 cF5 true) = 0 := by native_decide
-- F37: false and true witnesses are non-isomorphic
example : cInducedCount (tcGraph cF3 cF7 false) (tcGraph cF3 cF7 true) = 0 := by native_decide

/-! ### Bridge proofs for F33_witness -/

private theorem cs1Flag3_eq_cF3_toTypedGenFlag :
    cs1Flag3 = cF3.toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, cF3]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [cs1Flag3, CGraph.toTypedGenFlag, cF3]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

private theorem F33_witness_forget_eq_toGenFlag :
    F33_witness.forget = (tcGraph cF3 cF3 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, F33_witness, CGraph.toGenFlag, tcGraph, cF3]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem F33_witness_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F33_witness.forget = 6 := by
  rw [F33_witness_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cF3 cF3 false) (tcGraph cF3 cF3 false)
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

private theorem F33_witness_eq_tcGraph_toTypedGenFlag :
    F33_witness = (tcGraph cF3 cF3 false).toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, tcGraph, cF3]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [F33_witness, CGraph.toTypedGenFlag, tcGraph, cF3]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem F33_witness_jointCount_bridge :
    genJointCount CG2 csType7 cs1Flag3 cs1Flag3 F33_witness = 2 := by
  rw [cs1Flag3_eq_cF3_toTypedGenFlag, F33_witness_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cF3 cF3 (tcGraph cF3 cF3 false) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  change tcJointCount 3 cF3 cF3 (tcGraph cF3 cF3 false) = 2
  native_decide

/-! ### Bridge proofs for F34_witness_false -/

private theorem F34_witness_false_forget_eq_toGenFlag :
    F34_witness_false.forget = (tcGraph cF3 cF4 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, F34_witness_false, CGraph.toGenFlag, tcGraph, cF3, cF4]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem F34_witness_false_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F34_witness_false.forget = 2 := by
  rw [F34_witness_false_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cF3 cF4 false) (tcGraph cF3 cF4 false) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem F34_witness_false_eq_tcGraph_toTypedGenFlag :
    F34_witness_false = (tcGraph cF3 cF4 false).toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, tcGraph, cF3, cF4]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [F34_witness_false, CGraph.toTypedGenFlag, tcGraph, cF3, cF4]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem F34_witness_false_jointCount_bridge :
    genJointCount CG2 csType7 cs1Flag3 cs1Flag4 F34_witness_false = 1 := by
  rw [cs1Flag3_eq_cF3_toTypedGenFlag, cs1Flag4_eq_cF4_toTypedGenFlag,
      F34_witness_false_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cF3 cF4 (tcGraph cF3 cF4 false) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  change tcJointCount 3 cF3 cF4 (tcGraph cF3 cF4 false) = 1
  native_decide

/-! ### Bridge proofs for F34_witness_true -/

private theorem F34_witness_true_forget_eq_toGenFlag :
    F34_witness_true.forget = (tcGraph cF3 cF4 true).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, F34_witness_true, CGraph.toGenFlag, tcGraph, cF3, cF4]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem F34_witness_true_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F34_witness_true.forget = 1 := by
  rw [F34_witness_true_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cF3 cF4 true) (tcGraph cF3 cF4 true) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem F34_witness_true_eq_tcGraph_toTypedGenFlag :
    F34_witness_true = (tcGraph cF3 cF4 true).toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, tcGraph, cF3, cF4]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [F34_witness_true, CGraph.toTypedGenFlag, tcGraph, cF3, cF4]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem F34_witness_true_jointCount_bridge :
    genJointCount CG2 csType7 cs1Flag3 cs1Flag4 F34_witness_true = 1 := by
  rw [cs1Flag3_eq_cF3_toTypedGenFlag, cs1Flag4_eq_cF4_toTypedGenFlag,
      F34_witness_true_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cF3 cF4 (tcGraph cF3 cF4 true) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  change tcJointCount 3 cF3 cF4 (tcGraph cF3 cF4 true) = 1
  native_decide

/-! ### Bridge proofs for F35_witness_false -/

private theorem F35_witness_false_forget_eq_toGenFlag :
    F35_witness_false.forget = (tcGraph cF3 cF5 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, F35_witness_false, CGraph.toGenFlag, tcGraph, cF3, cF5]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem F35_witness_false_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F35_witness_false.forget = 1 := by
  rw [F35_witness_false_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cF3 cF5 false) (tcGraph cF3 cF5 false) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem F35_witness_false_eq_tcGraph_toTypedGenFlag :
    F35_witness_false = (tcGraph cF3 cF5 false).toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, tcGraph, cF3, cF5]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [F35_witness_false, CGraph.toTypedGenFlag, tcGraph, cF3, cF5]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem F35_witness_false_jointCount_bridge :
    genJointCount CG2 csType7 cs1Flag3 cs1Flag5 F35_witness_false = 1 := by
  rw [cs1Flag3_eq_cF3_toTypedGenFlag, cs1Flag5_eq_cF5_toTypedGenFlag,
      F35_witness_false_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cF3 cF5 (tcGraph cF3 cF5 false) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  change tcJointCount 3 cF3 cF5 (tcGraph cF3 cF5 false) = 1
  native_decide

/-! ### Bridge proofs for F35_witness_true -/

private theorem F35_witness_true_forget_eq_toGenFlag :
    F35_witness_true.forget = (tcGraph cF3 cF5 true).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, F35_witness_true, CGraph.toGenFlag, tcGraph, cF3, cF5]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem F35_witness_true_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F35_witness_true.forget = 2 := by
  rw [F35_witness_true_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cF3 cF5 true) (tcGraph cF3 cF5 true) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem F35_witness_true_eq_tcGraph_toTypedGenFlag :
    F35_witness_true = (tcGraph cF3 cF5 true).toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, tcGraph, cF3, cF5]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [F35_witness_true, CGraph.toTypedGenFlag, tcGraph, cF3, cF5]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem F35_witness_true_jointCount_bridge :
    genJointCount CG2 csType7 cs1Flag3 cs1Flag5 F35_witness_true = 1 := by
  rw [cs1Flag3_eq_cF3_toTypedGenFlag, cs1Flag5_eq_cF5_toTypedGenFlag,
      F35_witness_true_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cF3 cF5 (tcGraph cF3 cF5 true) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  change tcJointCount 3 cF3 cF5 (tcGraph cF3 cF5 true) = 1
  native_decide

/-! ### Bridge proofs for F37_witness_false -/

private theorem F37_witness_false_forget_eq_toGenFlag :
    F37_witness_false.forget = (tcGraph cF3 cF7 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, F37_witness_false, CGraph.toGenFlag, tcGraph, cF3, cF7]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem F37_witness_false_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F37_witness_false.forget = 1 := by
  rw [F37_witness_false_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cF3 cF7 false) (tcGraph cF3 cF7 false) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem F37_witness_false_eq_tcGraph_toTypedGenFlag :
    F37_witness_false = (tcGraph cF3 cF7 false).toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, tcGraph, cF3, cF7]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [F37_witness_false, CGraph.toTypedGenFlag, tcGraph, cF3, cF7]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem F37_witness_false_jointCount_bridge :
    genJointCount CG2 csType7 cs1Flag3 cs1Flag7 F37_witness_false = 1 := by
  rw [cs1Flag3_eq_cF3_toTypedGenFlag, cs1Flag7_eq_cF7_toTypedGenFlag,
      F37_witness_false_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cF3 cF7 (tcGraph cF3 cF7 false) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  change tcJointCount 3 cF3 cF7 (tcGraph cF3 cF7 false) = 1
  native_decide

/-! ### Bridge proofs for F37_witness_true -/

private theorem F37_witness_true_forget_eq_toGenFlag :
    F37_witness_true.forget = (tcGraph cF3 cF7 true).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, F37_witness_true, CGraph.toGenFlag, tcGraph, cF3, cF7]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem F37_witness_true_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F37_witness_true.forget = 4 := by
  rw [F37_witness_true_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cF3 cF7 true) (tcGraph cF3 cF7 true) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem F37_witness_true_eq_tcGraph_toTypedGenFlag :
    F37_witness_true = (tcGraph cF3 cF7 true).toTypedGenFlag csType7 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType7, tcGraph, cF3, cF7]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [F37_witness_true, CGraph.toTypedGenFlag, tcGraph, cF3, cF7]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem F37_witness_true_jointCount_bridge :
    genJointCount CG2 csType7 cs1Flag3 cs1Flag7 F37_witness_true = 1 := by
  rw [cs1Flag3_eq_cF3_toTypedGenFlag, cs1Flag7_eq_cF7_toTypedGenFlag,
      F37_witness_true_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cF3 cF7 (tcGraph cF3 cF7 true) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  change tcJointCount 3 cF3 cF7 (tcGraph cF3 cF7 true) = 1
  native_decide

/-! ### csType6 (σ₆) CGraph and cs0 flag products -/

/-- Concrete CGraph for csType6 (σ₆): 3 vertices, edges 0-1, 0-2, col [R,B,B]. -/
def cType6 : CGraph 3 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 0 && j.val == 2) || (i.val == 2 && j.val == 0)
  col := fun v => if v.val == 0 then 0 else 1

/-- Concrete CGraph for cs0Flag3: 4 vertices, edges {0-1, 0-2, 0-3}, col [R,B,B,R]. -/
def cS0F3 : CGraph 4 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 0 && j.val == 2) || (i.val == 2 && j.val == 0) ||
                    (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0)
  col := fun v => if v.val == 1 || v.val == 2 then 1 else 0

/-- Concrete CGraph for cs0Flag4: 4 vertices, edges {0-1, 0-2, 1-3}, col [R,B,B,R]. -/
def cS0F4 : CGraph 4 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 0 && j.val == 2) || (i.val == 2 && j.val == 0) ||
                    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1)
  col := fun v => if v.val == 1 || v.val == 2 then 1 else 0

/-- Concrete CGraph for cs0Flag5: 4 vertices, edges {0-1, 0-2, 2-3}, col [R,B,B,R]. -/
def cS0F5 : CGraph 4 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 0 && j.val == 2) || (i.val == 2 && j.val == 0) ||
                    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2)
  col := fun v => if v.val == 1 || v.val == 2 then 1 else 0

/-- Concrete CGraph for cs0Flag6: 4 vertices, edges {0-1, 0-2, 1-3, 2-3}, col [R,B,B,R]. -/
def cS0F6 : CGraph 4 where
  adj := fun i j => (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
                    (i.val == 0 && j.val == 2) || (i.val == 2 && j.val == 0) ||
                    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
                    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2)
  col := fun v => if v.val == 1 || v.val == 2 then 1 else 0

/-! ### cs0 product computations via native_decide

For each product pair, we compute:
- tcJointCount for adj34=false/true
- hasTriangle for both
- Automorphism counts (empty + sigma)
These are used to determine witness structures and numerical coefficients. -/

-- S0F3×S0F3
#eval (tcJointCount 3 cS0F3 cS0F3 (tcGraph cS0F3 cS0F3 false),
       hasTriangle (tcGraph cS0F3 cS0F3 false),
       hasTriangle (tcGraph cS0F3 cS0F3 true),
       cInducedCount (tcGraph cS0F3 cS0F3 false) (tcGraph cS0F3 cS0F3 false),
       tcAutCount 3 (tcGraph cS0F3 cS0F3 false))
-- S0F3×S0F4
#eval (tcJointCount 3 cS0F3 cS0F4 (tcGraph cS0F3 cS0F4 false),
       hasTriangle (tcGraph cS0F3 cS0F4 false),
       hasTriangle (tcGraph cS0F3 cS0F4 true),
       cInducedCount (tcGraph cS0F3 cS0F4 false) (tcGraph cS0F3 cS0F4 false),
       tcAutCount 3 (tcGraph cS0F3 cS0F4 false))
-- S0F3×S0F5
#eval (tcJointCount 3 cS0F3 cS0F5 (tcGraph cS0F3 cS0F5 false),
       hasTriangle (tcGraph cS0F3 cS0F5 false),
       hasTriangle (tcGraph cS0F3 cS0F5 true),
       cInducedCount (tcGraph cS0F3 cS0F5 false) (tcGraph cS0F3 cS0F5 false),
       tcAutCount 3 (tcGraph cS0F3 cS0F5 false))
-- S0F3×S0F6
#eval (tcJointCount 3 cS0F3 cS0F6 (tcGraph cS0F3 cS0F6 false),
       hasTriangle (tcGraph cS0F3 cS0F6 false),
       hasTriangle (tcGraph cS0F3 cS0F6 true),
       cInducedCount (tcGraph cS0F3 cS0F6 false) (tcGraph cS0F3 cS0F6 false),
       tcAutCount 3 (tcGraph cS0F3 cS0F6 false))
-- S0F4×S0F4
#eval (tcJointCount 3 cS0F4 cS0F4 (tcGraph cS0F4 cS0F4 false),
       hasTriangle (tcGraph cS0F4 cS0F4 false),
       hasTriangle (tcGraph cS0F4 cS0F4 true),
       cInducedCount (tcGraph cS0F4 cS0F4 false) (tcGraph cS0F4 cS0F4 false),
       tcAutCount 3 (tcGraph cS0F4 cS0F4 false),
       cInducedCount (tcGraph cS0F4 cS0F4 true) (tcGraph cS0F4 cS0F4 true),
       tcAutCount 3 (tcGraph cS0F4 cS0F4 true))
-- S0F4×S0F5
#eval (tcJointCount 3 cS0F4 cS0F5 (tcGraph cS0F4 cS0F5 false),
       hasTriangle (tcGraph cS0F4 cS0F5 false),
       hasTriangle (tcGraph cS0F4 cS0F5 true),
       cInducedCount (tcGraph cS0F4 cS0F5 false) (tcGraph cS0F4 cS0F5 false),
       tcAutCount 3 (tcGraph cS0F4 cS0F5 false),
       cInducedCount (tcGraph cS0F4 cS0F5 true) (tcGraph cS0F4 cS0F5 true),
       tcAutCount 3 (tcGraph cS0F4 cS0F5 true))
-- S0F4×S0F6
#eval (tcJointCount 3 cS0F4 cS0F6 (tcGraph cS0F4 cS0F6 false),
       hasTriangle (tcGraph cS0F4 cS0F6 false),
       hasTriangle (tcGraph cS0F4 cS0F6 true),
       cInducedCount (tcGraph cS0F4 cS0F6 false) (tcGraph cS0F4 cS0F6 false),
       tcAutCount 3 (tcGraph cS0F4 cS0F6 false))
-- S0F5×S0F5
#eval (tcJointCount 3 cS0F5 cS0F5 (tcGraph cS0F5 cS0F5 false),
       hasTriangle (tcGraph cS0F5 cS0F5 false),
       hasTriangle (tcGraph cS0F5 cS0F5 true),
       cInducedCount (tcGraph cS0F5 cS0F5 false) (tcGraph cS0F5 cS0F5 false),
       tcAutCount 3 (tcGraph cS0F5 cS0F5 false),
       cInducedCount (tcGraph cS0F5 cS0F5 true) (tcGraph cS0F5 cS0F5 true),
       tcAutCount 3 (tcGraph cS0F5 cS0F5 true))
-- S0F5×S0F6
#eval (tcJointCount 3 cS0F5 cS0F6 (tcGraph cS0F5 cS0F6 false),
       hasTriangle (tcGraph cS0F5 cS0F6 false),
       hasTriangle (tcGraph cS0F5 cS0F6 true),
       cInducedCount (tcGraph cS0F5 cS0F6 false) (tcGraph cS0F5 cS0F6 false),
       tcAutCount 3 (tcGraph cS0F5 cS0F6 false))
-- S0F6×S0F6
#eval (tcJointCount 3 cS0F6 cS0F6 (tcGraph cS0F6 cS0F6 false),
       hasTriangle (tcGraph cS0F6 cS0F6 false),
       hasTriangle (tcGraph cS0F6 cS0F6 true),
       cInducedCount (tcGraph cS0F6 cS0F6 false) (tcGraph cS0F6 cS0F6 false),
       tcAutCount 3 (tcGraph cS0F6 cS0F6 false))
-- Dual-witness aut counts for adj34=true cases
-- S0F3×S0F4 true
#eval (tcJointCount 3 cS0F3 cS0F4 (tcGraph cS0F3 cS0F4 true),
       cInducedCount (tcGraph cS0F3 cS0F4 true) (tcGraph cS0F3 cS0F4 true),
       tcAutCount 3 (tcGraph cS0F3 cS0F4 true))
-- S0F3×S0F5 true
#eval (tcJointCount 3 cS0F3 cS0F5 (tcGraph cS0F3 cS0F5 true),
       cInducedCount (tcGraph cS0F3 cS0F5 true) (tcGraph cS0F3 cS0F5 true),
       tcAutCount 3 (tcGraph cS0F3 cS0F5 true))
-- S0F3×S0F6 true
#eval (tcJointCount 3 cS0F3 cS0F6 (tcGraph cS0F3 cS0F6 true),
       cInducedCount (tcGraph cS0F3 cS0F6 true) (tcGraph cS0F3 cS0F6 true),
       tcAutCount 3 (tcGraph cS0F3 cS0F6 true))

/-! ### cs0 product data verified via native_decide -/

-- S0F3×S0F3: adj34=false only (adj34=true has triangle)
example : tcJointCount 3 cS0F3 cS0F3
    (tcGraph cS0F3 cS0F3 false) = 2 := by native_decide
example : hasTriangle
    (tcGraph cS0F3 cS0F3 false) = false := by native_decide
example : hasTriangle
    (tcGraph cS0F3 cS0F3 true) = true := by native_decide
example : cInducedCount (tcGraph cS0F3 cS0F3 false)
    (tcGraph cS0F3 cS0F3 false) = 4 := by native_decide
example : tcAutCount 3
    (tcGraph cS0F3 cS0F3 false) = 2 := by native_decide

-- S0F3×S0F4: both tri-free (dual witness)
example : tcJointCount 3 cS0F3 cS0F4
    (tcGraph cS0F3 cS0F4 false) = 1 := by native_decide
example : hasTriangle
    (tcGraph cS0F3 cS0F4 false) = false := by native_decide
example : hasTriangle
    (tcGraph cS0F3 cS0F4 true) = false := by native_decide
example : cInducedCount (tcGraph cS0F3 cS0F4 false)
    (tcGraph cS0F3 cS0F4 false) = 1 := by native_decide
example : tcAutCount 3
    (tcGraph cS0F3 cS0F4 false) = 1 := by native_decide
example : tcJointCount 3 cS0F3 cS0F4
    (tcGraph cS0F3 cS0F4 true) = 1 := by native_decide
example : cInducedCount (tcGraph cS0F3 cS0F4 true)
    (tcGraph cS0F3 cS0F4 true) = 1 := by native_decide
example : tcAutCount 3
    (tcGraph cS0F3 cS0F4 true) = 1 := by native_decide

-- S0F3×S0F5: both tri-free (dual witness)
example : tcJointCount 3 cS0F3 cS0F5
    (tcGraph cS0F3 cS0F5 false) = 1 := by native_decide
example : hasTriangle
    (tcGraph cS0F3 cS0F5 false) = false := by native_decide
example : hasTriangle
    (tcGraph cS0F3 cS0F5 true) = false := by native_decide
example : cInducedCount (tcGraph cS0F3 cS0F5 false)
    (tcGraph cS0F3 cS0F5 false) = 1 := by native_decide
example : tcAutCount 3
    (tcGraph cS0F3 cS0F5 false) = 1 := by native_decide
example : tcJointCount 3 cS0F3 cS0F5
    (tcGraph cS0F3 cS0F5 true) = 1 := by native_decide
example : cInducedCount (tcGraph cS0F3 cS0F5 true)
    (tcGraph cS0F3 cS0F5 true) = 1 := by native_decide
example : tcAutCount 3
    (tcGraph cS0F3 cS0F5 true) = 1 := by native_decide

-- S0F3×S0F6: both tri-free (dual witness)
example : tcJointCount 3 cS0F3 cS0F6
    (tcGraph cS0F3 cS0F6 false) = 1 := by native_decide
example : hasTriangle
    (tcGraph cS0F3 cS0F6 false) = false := by native_decide
example : hasTriangle
    (tcGraph cS0F3 cS0F6 true) = false := by native_decide
example : cInducedCount (tcGraph cS0F3 cS0F6 false)
    (tcGraph cS0F3 cS0F6 false) = 2 := by native_decide
example : tcAutCount 3
    (tcGraph cS0F3 cS0F6 false) = 1 := by native_decide
example : tcJointCount 3 cS0F3 cS0F6
    (tcGraph cS0F3 cS0F6 true) = 1 := by native_decide
example : cInducedCount (tcGraph cS0F3 cS0F6 true)
    (tcGraph cS0F3 cS0F6 true) = 4 := by native_decide
example : tcAutCount 3
    (tcGraph cS0F3 cS0F6 true) = 1 := by native_decide

-- S0F4×S0F4: adj34=false only (adj34=true has triangle)
example : tcJointCount 3 cS0F4 cS0F4
    (tcGraph cS0F4 cS0F4 false) = 2 := by native_decide
example : hasTriangle
    (tcGraph cS0F4 cS0F4 false) = false := by native_decide
example : hasTriangle
    (tcGraph cS0F4 cS0F4 true) = true := by native_decide
example : cInducedCount (tcGraph cS0F4 cS0F4 false)
    (tcGraph cS0F4 cS0F4 false) = 2 := by native_decide
example : tcAutCount 3
    (tcGraph cS0F4 cS0F4 false) = 2 := by native_decide

-- S0F4×S0F5: both tri-free (dual witness)
example : tcJointCount 3 cS0F4 cS0F5
    (tcGraph cS0F4 cS0F5 false) = 1 := by native_decide
example : hasTriangle
    (tcGraph cS0F4 cS0F5 false) = false := by native_decide
example : hasTriangle
    (tcGraph cS0F4 cS0F5 true) = false := by native_decide
example : cInducedCount (tcGraph cS0F4 cS0F5 false)
    (tcGraph cS0F4 cS0F5 false) = 2 := by native_decide
example : tcAutCount 3
    (tcGraph cS0F4 cS0F5 false) = 1 := by native_decide
example : tcJointCount 3 cS0F4 cS0F5
    (tcGraph cS0F4 cS0F5 true) = 1 := by native_decide
example : cInducedCount (tcGraph cS0F4 cS0F5 true)
    (tcGraph cS0F4 cS0F5 true) = 2 := by native_decide
example : tcAutCount 3
    (tcGraph cS0F4 cS0F5 true) = 1 := by native_decide

-- S0F4×S0F6: adj34=false only (adj34=true has triangle)
example : tcJointCount 3 cS0F4 cS0F6
    (tcGraph cS0F4 cS0F6 false) = 1 := by native_decide
example : hasTriangle
    (tcGraph cS0F4 cS0F6 false) = false := by native_decide
example : hasTriangle
    (tcGraph cS0F4 cS0F6 true) = true := by native_decide
example : cInducedCount (tcGraph cS0F4 cS0F6 false)
    (tcGraph cS0F4 cS0F6 false) = 2 := by native_decide
example : tcAutCount 3
    (tcGraph cS0F4 cS0F6 false) = 1 := by native_decide

-- S0F5×S0F5: adj34=false only (adj34=true has triangle)
example : tcJointCount 3 cS0F5 cS0F5
    (tcGraph cS0F5 cS0F5 false) = 2 := by native_decide
example : hasTriangle
    (tcGraph cS0F5 cS0F5 false) = false := by native_decide
example : hasTriangle
    (tcGraph cS0F5 cS0F5 true) = true := by native_decide
example : cInducedCount (tcGraph cS0F5 cS0F5 false)
    (tcGraph cS0F5 cS0F5 false) = 2 := by native_decide
example : tcAutCount 3
    (tcGraph cS0F5 cS0F5 false) = 2 := by native_decide

-- S0F5×S0F6: adj34=false only (adj34=true has triangle)
example : tcJointCount 3 cS0F5 cS0F6
    (tcGraph cS0F5 cS0F6 false) = 1 := by native_decide
example : hasTriangle
    (tcGraph cS0F5 cS0F6 false) = false := by native_decide
example : hasTriangle
    (tcGraph cS0F5 cS0F6 true) = true := by native_decide
example : cInducedCount (tcGraph cS0F5 cS0F6 false)
    (tcGraph cS0F5 cS0F6 false) = 2 := by native_decide
example : tcAutCount 3
    (tcGraph cS0F5 cS0F6 false) = 1 := by native_decide

-- S0F6×S0F6: adj34=false only (adj34=true has triangle)
example : tcJointCount 3 cS0F6 cS0F6
    (tcGraph cS0F6 cS0F6 false) = 2 := by native_decide
example : hasTriangle
    (tcGraph cS0F6 cS0F6 false) = false := by native_decide
example : hasTriangle
    (tcGraph cS0F6 cS0F6 true) = true := by native_decide
example : cInducedCount (tcGraph cS0F6 cS0F6 false)
    (tcGraph cS0F6 cS0F6 false) = 12 := by native_decide
example : tcAutCount 3
    (tcGraph cS0F6 cS0F6 false) = 2 := by native_decide

/-! ### cs0Flag CGraph-to-GenFlag bridge theorems -/

private theorem cs0Flag3_eq_cS0F3_toTypedGenFlag :
    cs0Flag3 = cS0F3.toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, cS0F3]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [cs0Flag3, CGraph.toTypedGenFlag, cS0F3]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

private theorem cs0Flag4_eq_cS0F4_toTypedGenFlag :
    cs0Flag4 = cS0F4.toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, cS0F4]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [cs0Flag4, CGraph.toTypedGenFlag, cS0F4]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

private theorem cs0Flag5_eq_cS0F5_toTypedGenFlag :
    cs0Flag5 = cS0F5.toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, cS0F5]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [cs0Flag5, CGraph.toTypedGenFlag, cS0F5]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

private theorem cs0Flag6_eq_cS0F6_toTypedGenFlag :
    cs0Flag6 = cS0F6.toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, cS0F6]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [cs0Flag6, CGraph.toTypedGenFlag, cS0F6]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

/-! ### S0F33 bridge -/

private theorem S0F33_witness_forget_eq_toGenFlag :
    S0F33_witness.forget = (tcGraph cS0F3 cS0F3 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, S0F33_witness, CGraph.toGenFlag, tcGraph, cS0F3]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem S0F33_witness_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F33_witness.forget = 4 := by
  rw [S0F33_witness_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cS0F3 cS0F3 false) (tcGraph cS0F3 cS0F3 false) (by decide)
    (by decide) (by decide) (by decide)]
  native_decide

private theorem S0F33_witness_eq_tcGraph_toTypedGenFlag :
    S0F33_witness = (tcGraph cS0F3 cS0F3 false).toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, tcGraph, cS0F3]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [S0F33_witness, CGraph.toTypedGenFlag, tcGraph, cS0F3]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem S0F33_witness_jointCount_bridge :
    genJointCount CG2 csType6 cs0Flag3 cs0Flag3 S0F33_witness = 2 := by
  rw [cs0Flag3_eq_cS0F3_toTypedGenFlag, S0F33_witness_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cS0F3 cS0F3 (tcGraph cS0F3 cS0F3 false) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  change tcJointCount 3 cS0F3 cS0F3 (tcGraph cS0F3 cS0F3 false) = 2
  native_decide

/-! ### S0F34 bridge (dual) -/

private theorem S0F34_witness_false_forget_eq_toGenFlag :
    S0F34_witness_false.forget = (tcGraph cS0F3 cS0F4 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, S0F34_witness_false, CGraph.toGenFlag, tcGraph, cS0F3, cS0F4]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem S0F34_witness_false_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F34_witness_false.forget = 1 := by
  rw [S0F34_witness_false_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cS0F3 cS0F4 false) (tcGraph cS0F3 cS0F4 false) (by decide)
    (by decide) (by decide) (by decide)]
  native_decide

private theorem S0F34_witness_false_eq_tcGraph_toTypedGenFlag :
    S0F34_witness_false = (tcGraph cS0F3 cS0F4 false).toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, tcGraph, cS0F3, cS0F4]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [S0F34_witness_false, CGraph.toTypedGenFlag, tcGraph, cS0F3, cS0F4]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem S0F34_witness_false_jointCount_bridge :
    genJointCount CG2 csType6 cs0Flag3 cs0Flag4 S0F34_witness_false = 1 := by
  rw [cs0Flag3_eq_cS0F3_toTypedGenFlag, cs0Flag4_eq_cS0F4_toTypedGenFlag,
      S0F34_witness_false_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cS0F3 cS0F4 (tcGraph cS0F3 cS0F4 false) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  change tcJointCount 3 cS0F3 cS0F4 (tcGraph cS0F3 cS0F4 false) = 1
  native_decide

private theorem S0F34_witness_true_forget_eq_toGenFlag :
    S0F34_witness_true.forget = (tcGraph cS0F3 cS0F4 true).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, S0F34_witness_true, CGraph.toGenFlag, tcGraph, cS0F3, cS0F4]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem S0F34_witness_true_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F34_witness_true.forget = 1 := by
  rw [S0F34_witness_true_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cS0F3 cS0F4 true) (tcGraph cS0F3 cS0F4 true) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem S0F34_witness_true_eq_tcGraph_toTypedGenFlag :
    S0F34_witness_true = (tcGraph cS0F3 cS0F4 true).toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, tcGraph, cS0F3, cS0F4]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [S0F34_witness_true, CGraph.toTypedGenFlag, tcGraph, cS0F3, cS0F4]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem S0F34_witness_true_jointCount_bridge :
    genJointCount CG2 csType6 cs0Flag3 cs0Flag4 S0F34_witness_true = 1 := by
  rw [cs0Flag3_eq_cS0F3_toTypedGenFlag, cs0Flag4_eq_cS0F4_toTypedGenFlag,
      S0F34_witness_true_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cS0F3 cS0F4 (tcGraph cS0F3 cS0F4 true) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  change tcJointCount 3 cS0F3 cS0F4 (tcGraph cS0F3 cS0F4 true) = 1
  native_decide

/-! ### S0F35 bridge (dual) -/

private theorem S0F35_witness_false_forget_eq_toGenFlag :
    S0F35_witness_false.forget = (tcGraph cS0F3 cS0F5 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, S0F35_witness_false, CGraph.toGenFlag, tcGraph, cS0F3, cS0F5]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem S0F35_witness_false_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F35_witness_false.forget = 1 := by
  rw [S0F35_witness_false_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cS0F3 cS0F5 false) (tcGraph cS0F3 cS0F5 false) (by decide)
    (by decide) (by decide) (by decide)]
  native_decide

private theorem S0F35_witness_false_eq_tcGraph_toTypedGenFlag :
    S0F35_witness_false = (tcGraph cS0F3 cS0F5 false).toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, tcGraph, cS0F3, cS0F5]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [S0F35_witness_false, CGraph.toTypedGenFlag, tcGraph, cS0F3, cS0F5]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem S0F35_witness_false_jointCount_bridge :
    genJointCount CG2 csType6 cs0Flag3 cs0Flag5 S0F35_witness_false = 1 := by
  rw [cs0Flag3_eq_cS0F3_toTypedGenFlag, cs0Flag5_eq_cS0F5_toTypedGenFlag,
      S0F35_witness_false_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cS0F3 cS0F5 (tcGraph cS0F3 cS0F5 false) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  change tcJointCount 3 cS0F3 cS0F5 (tcGraph cS0F3 cS0F5 false) = 1
  native_decide

private theorem S0F35_witness_true_forget_eq_toGenFlag :
    S0F35_witness_true.forget = (tcGraph cS0F3 cS0F5 true).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, S0F35_witness_true, CGraph.toGenFlag, tcGraph, cS0F3, cS0F5]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem S0F35_witness_true_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F35_witness_true.forget = 1 := by
  rw [S0F35_witness_true_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cS0F3 cS0F5 true) (tcGraph cS0F3 cS0F5 true) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem S0F35_witness_true_eq_tcGraph_toTypedGenFlag :
    S0F35_witness_true = (tcGraph cS0F3 cS0F5 true).toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, tcGraph, cS0F3, cS0F5]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [S0F35_witness_true, CGraph.toTypedGenFlag, tcGraph, cS0F3, cS0F5]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem S0F35_witness_true_jointCount_bridge :
    genJointCount CG2 csType6 cs0Flag3 cs0Flag5 S0F35_witness_true = 1 := by
  rw [cs0Flag3_eq_cS0F3_toTypedGenFlag, cs0Flag5_eq_cS0F5_toTypedGenFlag,
      S0F35_witness_true_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cS0F3 cS0F5 (tcGraph cS0F3 cS0F5 true) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  change tcJointCount 3 cS0F3 cS0F5 (tcGraph cS0F3 cS0F5 true) = 1
  native_decide

/-! ### S0F36 bridge (dual) -/

private theorem S0F36_witness_false_forget_eq_toGenFlag :
    S0F36_witness_false.forget = (tcGraph cS0F3 cS0F6 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, S0F36_witness_false, CGraph.toGenFlag, tcGraph, cS0F3, cS0F6]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem S0F36_witness_false_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F36_witness_false.forget = 2 := by
  rw [S0F36_witness_false_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cS0F3 cS0F6 false) (tcGraph cS0F3 cS0F6 false) (by decide)
    (by decide) (by decide) (by decide)]
  native_decide

private theorem S0F36_witness_false_eq_tcGraph_toTypedGenFlag :
    S0F36_witness_false = (tcGraph cS0F3 cS0F6 false).toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, tcGraph, cS0F3, cS0F6]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [S0F36_witness_false, CGraph.toTypedGenFlag, tcGraph, cS0F3, cS0F6]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem S0F36_witness_false_jointCount_bridge :
    genJointCount CG2 csType6 cs0Flag3 cs0Flag6 S0F36_witness_false = 1 := by
  rw [cs0Flag3_eq_cS0F3_toTypedGenFlag, cs0Flag6_eq_cS0F6_toTypedGenFlag,
      S0F36_witness_false_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cS0F3 cS0F6 (tcGraph cS0F3 cS0F6 false) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  change tcJointCount 3 cS0F3 cS0F6 (tcGraph cS0F3 cS0F6 false) = 1
  native_decide

private theorem S0F36_witness_true_forget_eq_toGenFlag :
    S0F36_witness_true.forget = (tcGraph cS0F3 cS0F6 true).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, S0F36_witness_true, CGraph.toGenFlag, tcGraph, cS0F3, cS0F6]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem S0F36_witness_true_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F36_witness_true.forget = 4 := by
  rw [S0F36_witness_true_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cS0F3 cS0F6 true) (tcGraph cS0F3 cS0F6 true) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem S0F36_witness_true_eq_tcGraph_toTypedGenFlag :
    S0F36_witness_true = (tcGraph cS0F3 cS0F6 true).toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, tcGraph, cS0F3, cS0F6]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [S0F36_witness_true, CGraph.toTypedGenFlag, tcGraph, cS0F3, cS0F6]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem S0F36_witness_true_jointCount_bridge :
    genJointCount CG2 csType6 cs0Flag3 cs0Flag6 S0F36_witness_true = 1 := by
  rw [cs0Flag3_eq_cS0F3_toTypedGenFlag, cs0Flag6_eq_cS0F6_toTypedGenFlag,
      S0F36_witness_true_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cS0F3 cS0F6 (tcGraph cS0F3 cS0F6 true) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  change tcJointCount 3 cS0F3 cS0F6 (tcGraph cS0F3 cS0F6 true) = 1
  native_decide

/-! ### S0F44 bridge -/

private theorem S0F44_witness_forget_eq_toGenFlag :
    S0F44_witness.forget = (tcGraph cS0F4 cS0F4 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, S0F44_witness, CGraph.toGenFlag, tcGraph, cS0F4]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem S0F44_witness_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F44_witness.forget = 2 := by
  rw [S0F44_witness_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cS0F4 cS0F4 false) (tcGraph cS0F4 cS0F4 false) (by decide)
    (by decide) (by decide) (by decide)]
  native_decide

private theorem S0F44_witness_eq_tcGraph_toTypedGenFlag :
    S0F44_witness = (tcGraph cS0F4 cS0F4 false).toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, tcGraph, cS0F4]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [S0F44_witness, CGraph.toTypedGenFlag, tcGraph, cS0F4]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem S0F44_witness_jointCount_bridge :
    genJointCount CG2 csType6 cs0Flag4 cs0Flag4 S0F44_witness = 2 := by
  rw [cs0Flag4_eq_cS0F4_toTypedGenFlag, S0F44_witness_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cS0F4 cS0F4 (tcGraph cS0F4 cS0F4 false) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  change tcJointCount 3 cS0F4 cS0F4 (tcGraph cS0F4 cS0F4 false) = 2
  native_decide

/-! ### S0F45 bridge (dual) -/

private theorem S0F45_witness_false_forget_eq_toGenFlag :
    S0F45_witness_false.forget = (tcGraph cS0F4 cS0F5 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, S0F45_witness_false, CGraph.toGenFlag, tcGraph, cS0F4, cS0F5]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem S0F45_witness_false_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F45_witness_false.forget = 2 := by
  rw [S0F45_witness_false_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cS0F4 cS0F5 false) (tcGraph cS0F4 cS0F5 false) (by decide)
    (by decide) (by decide) (by decide)]
  native_decide

private theorem S0F45_witness_false_eq_tcGraph_toTypedGenFlag :
    S0F45_witness_false = (tcGraph cS0F4 cS0F5 false).toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, tcGraph, cS0F4, cS0F5]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [S0F45_witness_false, CGraph.toTypedGenFlag, tcGraph, cS0F4, cS0F5]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem S0F45_witness_false_jointCount_bridge :
    genJointCount CG2 csType6 cs0Flag4 cs0Flag5 S0F45_witness_false = 1 := by
  rw [cs0Flag4_eq_cS0F4_toTypedGenFlag, cs0Flag5_eq_cS0F5_toTypedGenFlag,
      S0F45_witness_false_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cS0F4 cS0F5 (tcGraph cS0F4 cS0F5 false) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  change tcJointCount 3 cS0F4 cS0F5 (tcGraph cS0F4 cS0F5 false) = 1
  native_decide

private theorem S0F45_witness_true_forget_eq_toGenFlag :
    S0F45_witness_true.forget = (tcGraph cS0F4 cS0F5 true).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, S0F45_witness_true, CGraph.toGenFlag, tcGraph, cS0F4, cS0F5]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem S0F45_witness_true_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F45_witness_true.forget = 2 := by
  rw [S0F45_witness_true_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cS0F4 cS0F5 true) (tcGraph cS0F4 cS0F5 true) (by decide) (by decide)
    (by decide) (by decide)]
  native_decide

private theorem S0F45_witness_true_eq_tcGraph_toTypedGenFlag :
    S0F45_witness_true = (tcGraph cS0F4 cS0F5 true).toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, tcGraph, cS0F4, cS0F5]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [S0F45_witness_true, CGraph.toTypedGenFlag, tcGraph, cS0F4, cS0F5]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem S0F45_witness_true_jointCount_bridge :
    genJointCount CG2 csType6 cs0Flag4 cs0Flag5 S0F45_witness_true = 1 := by
  rw [cs0Flag4_eq_cS0F4_toTypedGenFlag, cs0Flag5_eq_cS0F5_toTypedGenFlag,
      S0F45_witness_true_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cS0F4 cS0F5 (tcGraph cS0F4 cS0F5 true) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  change tcJointCount 3 cS0F4 cS0F5 (tcGraph cS0F4 cS0F5 true) = 1
  native_decide

/-! ### S0F46 bridge -/

private theorem S0F46_witness_forget_eq_toGenFlag :
    S0F46_witness.forget = (tcGraph cS0F4 cS0F6 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, S0F46_witness, CGraph.toGenFlag, tcGraph, cS0F4, cS0F6]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem S0F46_witness_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F46_witness.forget = 2 := by
  rw [S0F46_witness_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cS0F4 cS0F6 false) (tcGraph cS0F4 cS0F6 false) (by decide)
    (by decide) (by decide) (by decide)]
  native_decide

private theorem S0F46_witness_eq_tcGraph_toTypedGenFlag :
    S0F46_witness = (tcGraph cS0F4 cS0F6 false).toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, tcGraph, cS0F4, cS0F6]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [S0F46_witness, CGraph.toTypedGenFlag, tcGraph, cS0F4, cS0F6]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem S0F46_witness_jointCount_bridge :
    genJointCount CG2 csType6 cs0Flag4 cs0Flag6 S0F46_witness = 1 := by
  rw [cs0Flag4_eq_cS0F4_toTypedGenFlag, cs0Flag6_eq_cS0F6_toTypedGenFlag,
      S0F46_witness_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cS0F4 cS0F6 (tcGraph cS0F4 cS0F6 false) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  change tcJointCount 3 cS0F4 cS0F6 (tcGraph cS0F4 cS0F6 false) = 1
  native_decide

/-! ### S0F55 bridge -/

private theorem S0F55_witness_forget_eq_toGenFlag :
    S0F55_witness.forget = (tcGraph cS0F5 cS0F5 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, S0F55_witness, CGraph.toGenFlag, tcGraph, cS0F5]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem S0F55_witness_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F55_witness.forget = 2 := by
  rw [S0F55_witness_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cS0F5 cS0F5 false) (tcGraph cS0F5 cS0F5 false) (by decide)
    (by decide) (by decide) (by decide)]
  native_decide

private theorem S0F55_witness_eq_tcGraph_toTypedGenFlag :
    S0F55_witness = (tcGraph cS0F5 cS0F5 false).toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, tcGraph, cS0F5]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [S0F55_witness, CGraph.toTypedGenFlag, tcGraph, cS0F5]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem S0F55_witness_jointCount_bridge :
    genJointCount CG2 csType6 cs0Flag5 cs0Flag5 S0F55_witness = 2 := by
  rw [cs0Flag5_eq_cS0F5_toTypedGenFlag, S0F55_witness_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cS0F5 cS0F5 (tcGraph cS0F5 cS0F5 false) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  change tcJointCount 3 cS0F5 cS0F5 (tcGraph cS0F5 cS0F5 false) = 2
  native_decide

/-! ### S0F56 bridge -/

private theorem S0F56_witness_forget_eq_toGenFlag :
    S0F56_witness.forget = (tcGraph cS0F5 cS0F6 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, S0F56_witness, CGraph.toGenFlag, tcGraph, cS0F5, cS0F6]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem S0F56_witness_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F56_witness.forget = 2 := by
  rw [S0F56_witness_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cS0F5 cS0F6 false) (tcGraph cS0F5 cS0F6 false) (by decide)
    (by decide) (by decide) (by decide)]
  native_decide

private theorem S0F56_witness_eq_tcGraph_toTypedGenFlag :
    S0F56_witness = (tcGraph cS0F5 cS0F6 false).toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, tcGraph, cS0F5, cS0F6]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [S0F56_witness, CGraph.toTypedGenFlag, tcGraph, cS0F5, cS0F6]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem S0F56_witness_jointCount_bridge :
    genJointCount CG2 csType6 cs0Flag5 cs0Flag6 S0F56_witness = 1 := by
  rw [cs0Flag5_eq_cS0F5_toTypedGenFlag, cs0Flag6_eq_cS0F6_toTypedGenFlag,
      S0F56_witness_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cS0F5 cS0F6 (tcGraph cS0F5 cS0F6 false) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  change tcJointCount 3 cS0F5 cS0F6 (tcGraph cS0F5 cS0F6 false) = 1
  native_decide

/-! ### S0F66 bridge -/

private theorem S0F66_witness_forget_eq_toGenFlag :
    S0F66_witness.forget = (tcGraph cS0F6 cS0F6 false).toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [GenFlag.forget, S0F66_witness, CGraph.toGenFlag, tcGraph, cS0F6]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
theorem S0F66_witness_emptyAutCount_bridge :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F66_witness.forget = 12 := by
  rw [S0F66_witness_forget_eq_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' (tcGraph cS0F6 cS0F6 false) (tcGraph cS0F6 cS0F6 false) (by decide)
    (by decide) (by decide) (by decide)]
  native_decide

private theorem S0F66_witness_eq_tcGraph_toTypedGenFlag :
    S0F66_witness = (tcGraph cS0F6 cS0F6 false).toTypedGenFlag csType6 (by decide) (by
      refine Prod.ext ?_ (by ext i; fin_cases i <;> rfl)
      simp only [colouredGraphUniverse, csType6, tcGraph, cS0F6]
      ext u v; fin_cases u <;> fin_cases v <;> simp [Fin.castLE]) := by
  simp only [S0F66_witness, CGraph.toTypedGenFlag, tcGraph, cS0F6]
  congr 1
  refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
  ext u v; simp only [SimpleGraph.fromRel_adj]
  fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 1600000 in
theorem S0F66_witness_jointCount_bridge :
    genJointCount CG2 csType6 cs0Flag6 cs0Flag6 S0F66_witness = 2 := by
  rw [cs0Flag6_eq_cS0F6_toTypedGenFlag, S0F66_witness_eq_tcGraph_toTypedGenFlag]
  rw [← tcJointCount_eq_genJointCount cS0F6 cS0F6 (tcGraph cS0F6 cS0F6 false) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  change tcJointCount 3 cS0F6 cS0F6 (tcGraph cS0F6 cS0F6 false) = 2
  native_decide

/-! ## certF1, certF6 automorphism counts (Phase 2 of `b1_nonneg` discharge)

Compute aut(certF1) = 5! = 120 and aut(certF6) = 4! = 24 via the CGraph bridge
plus `native_decide`. These are needed to identify `genUnlabelledDensity`. -/

/-- certF1 as a `CGraph 5`: all 5 vertices coloured black (colour 1), no edges. -/
def cCertF1 : CGraph 5 where
  adj := fun _ _ => false
  col := fun _ => 1

/-- certF6 as a `CGraph 5`: K_{1,4} with centre at vertex 4 (black),
    leaves at {0,1,2,3} (red). Edges: 0-4, 1-4, 2-4, 3-4. -/
def cCertF6 : CGraph 5 where
  adj := fun i j =>
    (i.val < 4 && j.val == 4) || (j.val < 4 && i.val == 4)
  col := fun v => if v.val == 4 then 1 else 0

/-- certF1 (a noncomputable GenFlag) equals `cCertF1.toGenFlag`. -/
private theorem certF1_eq_cCertF1_toGenFlag :
    certF1 = cCertF1.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; rfl)
    simp only [certF1, CGraph.toGenFlag, cCertF1]
    ext u v; simp (config := { decide := true })

/-- certF6 (a noncomputable GenFlag) equals `cCertF6.toGenFlag`. -/
private theorem certF6_eq_cCertF6_toGenFlag :
    certF6 = cCertF6.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [certF6, CGraph.toGenFlag, cCertF6]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
/-- aut(certF1) = 120 = 5!: all 5 black vertices permute freely. -/
theorem certF1_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) certF1 = 120 := by
  rw [certF1_eq_cCertF1_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cCertF1 cCertF1
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

set_option maxHeartbeats 800000 in
/-- aut(certF6) = 24 = 4!: 4 red leaves permute freely; centre fixed. -/
theorem certF6_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) certF6 = 24 := by
  rw [certF6_eq_cCertF6_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cCertF6 cCertF6
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

/-! ## σ₁-4-B: aut counts for 5 named flags (certF4, flag5, flag12, flag24, flag32)

Each is computed via the CGraph bridge + native_decide pattern. -/

/-- certF4 as a `CGraph 5`: K_{1,4} centred at v4, colours [B,B,R,R,B] (Lean: 0,0,1,1,0). -/
def cCertF4 : CGraph 5 where
  adj := fun i j =>
    (i.val < 4 && j.val == 4) || (j.val < 4 && i.val == 4)
  col := fun v => if v.val = 0 ∨ v.val = 1 ∨ v.val = 4 then (0 : Fin 2) else 1

/-- flag5 as a `CGraph 5`: K_{1,4} centred at v4, col v3=R(1), others B(0). -/
def cFlag5 : CGraph 5 where
  adj := fun i j =>
    (i.val < 4 && j.val == 4) || (j.val < 4 && i.val == 4)
  col := fun v => if v.val = 3 then (1 : Fin 2) else 0

/-- flag12 as a `CGraph 5`: edges {0-4,1-3,1-4,2-3,2-4}, col v2=R(1). -/
def cFlag12 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 4) || (i.val == 4 && j.val == 0) ||
    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2)
  col := fun v => if v.val = 2 then (1 : Fin 2) else 0

/-- flag24 as a `CGraph 5`: edges {0-3,1-4,2-4,3-4}, col v3=R(1). -/
def cFlag24 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0) ||
    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val = 3 then (1 : Fin 2) else 0

/-- flag32 as a `CGraph 5`: K_{3,2} edges {0-3,0-4,1-3,1-4,2-3,2-4}, col v2=R(1). -/
def cFlag32 : CGraph 5 where
  adj := fun i j =>
    ((i.val < 3 && j.val ≥ 3) || (j.val < 3 && i.val ≥ 3)) && i.val ≠ j.val
  col := fun v => if v.val = 2 then (1 : Fin 2) else 0

/-- certF4 = cCertF4.toGenFlag. -/
private theorem certF4_eq_cCertF4_toGenFlag :
    certF4 = cCertF4.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [certF4, CGraph.toGenFlag, cCertF4]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

/-- flag5 = cFlag5.toGenFlag. -/
private theorem flag5_eq_cFlag5_toGenFlag :
    flag5 = cFlag5.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [flag5, CGraph.toGenFlag, cFlag5]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

/-- flag12 = cFlag12.toGenFlag. -/
private theorem flag12_eq_cFlag12_toGenFlag :
    flag12 = cFlag12.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [flag12, CGraph.toGenFlag, cFlag12]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

/-- flag24 = cFlag24.toGenFlag. -/
private theorem flag24_eq_cFlag24_toGenFlag :
    flag24 = cFlag24.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [flag24, CGraph.toGenFlag, cFlag24]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

/-- flag32 = cFlag32.toGenFlag. -/
private theorem flag32_eq_cFlag32_toGenFlag :
    flag32 = cFlag32.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [flag32, CGraph.toGenFlag, cFlag32]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
/-- aut(certF4) = 4: K_{1,4} with two colour-X leaves {v0,v1} and two colour-Y
    leaves {v2,v3}; centre fixed; (2!)·(2!) = 4. -/
theorem certF4_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) certF4 = 4 := by
  rw [certF4_eq_cCertF4_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cCertF4 cCertF4
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

set_option maxHeartbeats 800000 in
/-- aut(flag5) = 6 = 3!: K_{1,4}, centre v4 fixed, distinguished red leaf v3 fixed,
    other 3 leaves {v0,v1,v2} permute freely. -/
theorem flag5_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) flag5 = 6 := by
  rw [flag5_eq_cFlag5_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cFlag5 cFlag5
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

set_option maxHeartbeats 800000 in
/-- aut(flag12) = 1: all vertices have unique invariants (degree+colour
    distinguishes each, no swap preserves edges). -/
theorem flag12_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) flag12 = 1 := by
  rw [flag12_eq_cFlag12_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cFlag12 cFlag12
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

set_option maxHeartbeats 800000 in
/-- aut(flag24) = 2: v3 (col 1) and v0,v4 (degree-distinguished) all fixed;
    {v1,v2} both have only nbr v4, swappable. -/
theorem flag24_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) flag24 = 2 := by
  rw [flag24_eq_cFlag24_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cFlag24 cFlag24
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

set_option maxHeartbeats 800000 in
/-- aut(flag32) = 4: K_{3,2}; v2 (col 1) fixed; {v0,v1} swappable, {v3,v4}
    swappable; (2!)·(2!) = 4. -/
theorem flag32_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) flag32 = 4 := by
  rw [flag32_eq_cFlag32_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cFlag32 cFlag32
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

/-! ## σ₅-1: aut counts for 4 named flags (flag16, flag17, sdpFlag37, sdpFlag55)

σ₅ named-flag combo: `[-2F₁₆, -F₁₇, F₃₇, 2F₅₅]` (BrrbCertificate sig5x2/2).
Same CGraph + native_decide pattern as σ₁-4-B. -/

/-- flag16 as a `CGraph 5`: edges {0-3, 1-4, 2-4, 3-4}, col v.val ≤ 2 → B(1). -/
def cFlag16 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0) ||
    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val ≤ 2 then (1 : Fin 2) else 0

/-- flag17 as a `CGraph 5`: edges {0-3, 1-4, 2-4, 3-4}, col v.val = 0 ∨ 2 → B(1). -/
def cFlag17 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0) ||
    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val = 0 ∨ v.val = 2 then (1 : Fin 2) else 0

/-- sdpFlag37 as a `CGraph 5`: edges {0-2, 1-3, 2-4, 3-4}, col v.val = 1 ∨ 2 → B(1). -/
def cSdpFlag37 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 2) || (i.val == 2 && j.val == 0) ||
    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val = 1 ∨ v.val = 2 then (1 : Fin 2) else 0

/-- sdpFlag55 as a `CGraph 5`: edges {0-1, 0-2, 1-3, 2-4, 3-4},
    col v.val = 2 ∨ 3 → B(1). -/
def cSdpFlag55 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 1) || (i.val == 1 && j.val == 0) ||
    (i.val == 0 && j.val == 2) || (i.val == 2 && j.val == 0) ||
    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val = 2 ∨ v.val = 3 then (1 : Fin 2) else 0

/-- flag16 = cFlag16.toGenFlag. -/
private theorem flag16_eq_cFlag16_toGenFlag :
    flag16 = cFlag16.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [flag16, CGraph.toGenFlag, cFlag16]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

/-- flag17 = cFlag17.toGenFlag. -/
private theorem flag17_eq_cFlag17_toGenFlag :
    flag17 = cFlag17.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [flag17, CGraph.toGenFlag, cFlag17]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

/-- sdpFlag37 = cSdpFlag37.toGenFlag. -/
private theorem sdpFlag37_eq_cSdpFlag37_toGenFlag :
    sdpFlag37 = cSdpFlag37.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [sdpFlag37, CGraph.toGenFlag, cSdpFlag37]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

/-- sdpFlag55 = cSdpFlag55.toGenFlag. -/
private theorem sdpFlag55_eq_cSdpFlag55_toGenFlag :
    sdpFlag55 = cSdpFlag55.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [sdpFlag55, CGraph.toGenFlag, cSdpFlag55]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
/-- aut(flag16) = 4: K_{1,4}-like graph on B vertices {v0,v1,v2}, R vertices
    {v3,v4}; v3 fixed (degree 2 to v0,v4 makes it the only deg-2 R), v4 fixed
    (centre to {v1,v2,v3}); {v1,v2} swappable (both deg-1 B-leaves of v4);
    v0 fixed (only B with edge to v3). aut = 2. (Verified by native_decide.) -/
theorem flag16_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) flag16 = 2 := by
  rw [flag16_eq_cFlag16_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cFlag16 cFlag16
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

set_option maxHeartbeats 800000 in
/-- aut(flag17): same edges as flag16 but col [B,R,B,R,R].
    Verified by native_decide. -/
theorem flag17_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) flag17 = 1 := by
  rw [flag17_eq_cFlag17_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cFlag17 cFlag17
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

set_option maxHeartbeats 800000 in
/-- aut(sdpFlag37) = 1: edges {0-2, 1-3, 2-4, 3-4}, col [R,B,B,R,R];
    every vertex degree-distinguished + colour-distinguished, no swap.
    Verified by native_decide. -/
theorem sdpFlag37_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) sdpFlag37 = 1 := by
  rw [sdpFlag37_eq_cSdpFlag37_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cSdpFlag37 cSdpFlag37
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

set_option maxHeartbeats 800000 in
/-- aut(sdpFlag55) = 2: 5-cycle 0-1-3-4-2-0 with col [R,R,B,B,R];
    swap (v0↔v1, v2↔v3, v4 fixed) preserves edges + colours.
    Verified by native_decide. -/
theorem sdpFlag55_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) sdpFlag55 = 2 := by
  rw [sdpFlag55_eq_cSdpFlag55_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cSdpFlag55 cSdpFlag55
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

/-! ### σ₂-1: CGraph bridges for the 6 σ₂ named flags

Adds CGraph + aut theorems for sdpF7, flag15, sdpF20, flag25, sdpF30,
flag34 — the 6 named flags appearing in `sigma2_nonneg`'s goal RHS
(the 7th, certF6, was bridged earlier). -/

/-- sdpF7 as `CGraph 5`: edges {0-4, 1-3, 1-4, 2-3, 2-4}, cols [R,R,R,B,B]. -/
def cSdpF7 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 4) || (i.val == 4 && j.val == 0) ||
    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2)
  col := fun v => if v.val = 3 ∨ v.val = 4 then (1 : Fin 2) else 0

/-- flag15 as `CGraph 5`: same edges as sdpF7, cols [R,R,R,R,B]. -/
def cFlag15 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 4) || (i.val == 4 && j.val == 0) ||
    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2)
  col := fun v => if v.val = 4 then (1 : Fin 2) else 0

/-- sdpF20 as `CGraph 5`: edges {0-3, 1-4, 2-4, 3-4}, cols [B,R,R,R,B]. -/
def cSdpF20 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0) ||
    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val = 0 ∨ v.val = 4 then (1 : Fin 2) else 0

/-- flag25 as `CGraph 5`: same edges as sdpF20, cols [R,R,R,R,B]. -/
def cFlag25 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0) ||
    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val = 4 then (1 : Fin 2) else 0

/-- sdpF30 as `CGraph 5`: K_{3,2} with edges {0-3, 0-4, 1-3, 1-4, 2-3, 2-4},
    cols [R,R,R,B,B]. -/
def cSdpF30 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0) ||
    (i.val == 0 && j.val == 4) || (i.val == 4 && j.val == 0) ||
    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2)
  col := fun v => if v.val = 3 ∨ v.val = 4 then (1 : Fin 2) else 0

/-- flag34 as `CGraph 5`: K_{3,2} same edges as sdpF30, cols [R,R,R,R,B]. -/
def cFlag34 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0) ||
    (i.val == 0 && j.val == 4) || (i.val == 4 && j.val == 0) ||
    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2)
  col := fun v => if v.val = 4 then (1 : Fin 2) else 0

private theorem sdpF7_eq_cSdpF7_toGenFlag :
    sdpF7 = cSdpF7.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [sdpF7, CGraph.toGenFlag, cSdpF7]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

private theorem flag15_eq_cFlag15_toGenFlag :
    flag15 = cFlag15.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [flag15, CGraph.toGenFlag, cFlag15]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

private theorem sdpF20_eq_cSdpF20_toGenFlag :
    sdpF20 = cSdpF20.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [sdpF20, CGraph.toGenFlag, cSdpF20]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

private theorem flag25_eq_cFlag25_toGenFlag :
    flag25 = cFlag25.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [flag25, CGraph.toGenFlag, cFlag25]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

private theorem sdpF30_eq_cSdpF30_toGenFlag :
    sdpF30 = cSdpF30.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [sdpF30, CGraph.toGenFlag, cSdpF30]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

private theorem flag34_eq_cFlag34_toGenFlag :
    flag34 = cFlag34.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [flag34, CGraph.toGenFlag, cFlag34]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
/-- aut(sdpF7) = 2: v1 ↔ v2 swap (both R deg 2 with nbrs {v3, v4}). -/
theorem sdpF7_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) sdpF7 = 2 := by
  rw [sdpF7_eq_cSdpF7_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cSdpF7 cSdpF7
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

set_option maxHeartbeats 800000 in
/-- aut(flag15) = 2: v1 ↔ v2 swap (both R deg 2 with nbrs {v3, v4}). -/
theorem flag15_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) flag15 = 2 := by
  rw [flag15_eq_cFlag15_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cFlag15 cFlag15
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

set_option maxHeartbeats 800000 in
/-- aut(sdpF20) = 2: v1 ↔ v2 swap (both R deg 1 with nbr v4). -/
theorem sdpF20_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) sdpF20 = 2 := by
  rw [sdpF20_eq_cSdpF20_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cSdpF20 cSdpF20
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

set_option maxHeartbeats 800000 in
/-- aut(flag25) = 2: v1 ↔ v2 swap (both R deg 1 with nbr v4). -/
theorem flag25_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) flag25 = 2 := by
  rw [flag25_eq_cFlag25_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cFlag25 cFlag25
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

set_option maxHeartbeats 800000 in
/-- aut(sdpF30) = 12: K_{3,2} with R-side {v0,v1,v2} (S₃) + B-side {v3,v4} (S₂). -/
theorem sdpF30_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) sdpF30 = 12 := by
  rw [sdpF30_eq_cSdpF30_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cSdpF30 cSdpF30
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

set_option maxHeartbeats 800000 in
/-- aut(flag34) = 6: K_{3,2} with R-side {v0,v1,v2} (S₃); v3 R deg 3, v4 B deg 3. -/
theorem flag34_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) flag34 = 6 := by
  rw [flag34_eq_cFlag34_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cFlag34 cFlag34
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

/-! ### σ₃-1: CGraph bridges for σ₃-only named flags (certF11, certF22) -/

/-- certF11 as `CGraph 5`: edges {0-4, 1-3, 1-4, 2-3, 2-4}, cols [R,B,B,R,R]. -/
def cCertF11 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 4) || (i.val == 4 && j.val == 0) ||
    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2)
  col := fun v => if v.val = 1 ∨ v.val = 2 then (1 : Fin 2) else 0

/-- certF22 as `CGraph 5`: edges {0-3, 1-4, 2-4, 3-4}, cols [R,R,B,B,R]. -/
def cCertF22 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0) ||
    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2) ||
    (i.val == 3 && j.val == 4) || (i.val == 4 && j.val == 3)
  col := fun v => if v.val = 2 ∨ v.val = 3 then (1 : Fin 2) else 0

private theorem certF11_eq_cCertF11_toGenFlag :
    certF11 = cCertF11.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [certF11, CGraph.toGenFlag, cCertF11]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

private theorem certF22_eq_cCertF22_toGenFlag :
    certF22 = cCertF22.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [certF22, CGraph.toGenFlag, cCertF22]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
/-- aut(certF11) = 2: v1↔v2 swap (both B deg 2 with nbrs {v3, v4}). -/
theorem certF11_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) certF11 = 2 := by
  rw [certF11_eq_cCertF11_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cCertF11 cCertF11
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

set_option maxHeartbeats 800000 in
/-- aut(certF22) = 1: every vertex distinguished. -/
theorem certF22_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) certF22 = 1 := by
  rw [certF22_eq_cCertF22_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cCertF22 cCertF22
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

/-! ### σ₄-1: CGraph bridges for σ₄-only named flags (certF8, certF31) -/

/-- certF8 as `CGraph 5`: edges {0-4, 1-3, 1-4, 2-3, 2-4}, cols [B,R,B,R,R]. -/
def cCertF8 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 4) || (i.val == 4 && j.val == 0) ||
    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2)
  col := fun v => if v.val = 1 ∨ v.val = 3 ∨ v.val = 4 then (0 : Fin 2) else 1

/-- certF31 as `CGraph 5`: K_{3,2} edges {0-3, 0-4, 1-3, 1-4, 2-3, 2-4},
    cols [R,B,B,R,R]. -/
def cCertF31 : CGraph 5 where
  adj := fun i j =>
    (i.val == 0 && j.val == 3) || (i.val == 3 && j.val == 0) ||
    (i.val == 0 && j.val == 4) || (i.val == 4 && j.val == 0) ||
    (i.val == 1 && j.val == 3) || (i.val == 3 && j.val == 1) ||
    (i.val == 1 && j.val == 4) || (i.val == 4 && j.val == 1) ||
    (i.val == 2 && j.val == 3) || (i.val == 3 && j.val == 2) ||
    (i.val == 2 && j.val == 4) || (i.val == 4 && j.val == 2)
  col := fun v => if v.val = 0 ∨ v.val = 3 ∨ v.val = 4 then (0 : Fin 2) else 1

private theorem certF8_eq_cCertF8_toGenFlag :
    certF8 = cCertF8.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [certF8, CGraph.toGenFlag, cCertF8]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

private theorem certF31_eq_cCertF31_toGenFlag :
    certF31 = cCertF31.toGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    refine Prod.ext ?_ (by ext v; fin_cases v <;> rfl)
    simp only [certF31, CGraph.toGenFlag, cCertF31]
    ext u v; fin_cases u <;> fin_cases v <;> simp (config := { decide := true })

set_option maxHeartbeats 800000 in
/-- aut(certF8) = 1: every vertex distinguished by colour/degree. -/
theorem certF8_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) certF8 = 1 := by
  rw [certF8_eq_cCertF8_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cCertF8 cCertF8
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

set_option maxHeartbeats 800000 in
/-- aut(certF31) = 4: K_{3,2} with R-side {3,4} swappable, B-side {1,2}
    swappable; v0=R distinguished from v1=v2=B. (2!)·(2!) = 4. -/
theorem certF31_aut :
    genFlagAutCount CG2 (GenFlagType.empty CG2) certF31 = 4 := by
  rw [certF31_eq_cCertF31_toGenFlag]; unfold genFlagAutCount
  rw [← cInducedCount_eq_genInducedCount' cCertF31 cCertF31
    (by decide) (by decide) (by decide) (by decide)]
  native_decide

end Davey2024
