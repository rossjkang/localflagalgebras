import DaveyThesis2024.StrongEdgeColouring

/-!
# `SecFPadding`: degree-scale σ-sparse colouring lemma via `K_{D,D}` padding

**Phase L3.3 of the development notes.** This file proves
`hurley_colouring_scale`, a **degree-scale** version of the σ-sparse
colouring lemma, as a *theorem* from the verbatim HJK axiom
`hurley_colouring_lemma` (`StrongEdgeColouring.lean`). It is the Lean
counterpart of paper 2's `cor:hjk-scale` (padding proof, P0 commit on main).

## Statement shape

The verbatim axiom bounds `χ(G)` in terms of the *intrinsic* maximum degree
`Δ(G)` of the whole graph. The SEC application needs a version where

* the colouring is only required to be proper on a vertex subset `S`
  (`chromaticNumberOn`),
* the degree/sparsity scale `D` is supplied *externally* (with only
  `deg_S(v) ≤ D` for `v ∈ S`), and
* the local edge counts are taken within `S` (`fEdgesOn`, shaped exactly like
  `Davey2024.SecBridge.fEdgesInNeighbourhood`).

## Proof: disjoint-union padding with `K_{D,D}`

Given `H`, `S` and `D ≥ 1`, build `paddedFlag H S D` on
`H.size + 2*D` vertices: the *head* is `H` restricted to `S` (all edges with
an endpoint outside `S` are dropped), and the *tail* is a complete bipartite
graph `K_{D,D}` on the last `2*D` vertices, with no edges between head and
tail. Then:

* every tail vertex has degree exactly `D`, so `Δ(padded) = D` (the head
  degrees are ≤ `D` by hypothesis);
* a tail vertex's neighbourhood is one side of `K_{D,D}`, which is
  independent, so its local edge count is `0`;
* a head vertex's neighbourhood is (a lift of) its `S`-neighbourhood in `H`,
  so its local edge count is `fEdgesOn` (or `0` for head vertices outside
  `S`);
* any proper colouring of the padded graph restricts to an `S`-proper
  colouring of `H`.

Applying the verbatim axiom to the padded graph therefore yields the
degree-scale bound at the exact scale `D`.
-/

namespace Davey2024

open Finset BigOperators Nat Classical in
noncomputable section

set_option linter.unusedSectionVars false

/-! ## §1. Subset-colouring vocabulary -/

/-- A colouring `col` is **proper on `S`** if adjacent vertices *inside `S`*
receive different colours (adjacencies leaving `S` are unconstrained). -/
def IsProperOn (H : Flag emptyType) (S : Finset (Fin H.size))
    (col : Fin H.size → ℕ) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, H.graph.Adj i j → col i ≠ col j

/-- The **chromatic number on a subset** `S`: the least `k` admitting a
colouring that is proper on `S` and uses colours `< k` on `S`. -/
noncomputable def chromaticNumberOn (H : Flag emptyType)
    (S : Finset (Fin H.size)) : ℕ :=
  sInf {k : ℕ | ∃ col : Fin H.size → ℕ, IsProperOn H S col ∧ ∀ i ∈ S, col i < k}

/-- The defining infimum of `chromaticNumberOn` is attained: there is a
colouring proper on `S` using colours `< chromaticNumberOn H S` on `S`.
(The defining set is nonempty: `col := Fin.val` is proper with bound
`H.size`.) -/
theorem chromaticNumberOn_witness (H : Flag emptyType) (S : Finset (Fin H.size)) :
    ∃ col : Fin H.size → ℕ, IsProperOn H S col ∧
      ∀ i ∈ S, col i < chromaticNumberOn H S := by
  have hne : {k : ℕ | ∃ col : Fin H.size → ℕ,
      IsProperOn H S col ∧ ∀ i ∈ S, col i < k}.Nonempty := by
    refine ⟨H.size, fun i => i.val, ?_, fun i _ => i.isLt⟩
    intro i _ j _ hadj hcol
    exact hadj.ne (Fin.ext hcol)
  exact Nat.sInf_mem hne

/-- Any explicit `S`-proper colouring with colours `< k` on `S` bounds
`chromaticNumberOn H S` by `k`. -/
theorem chromaticNumberOn_le (H : Flag emptyType) (S : Finset (Fin H.size))
    (k : ℕ) (col : Fin H.size → ℕ) (h1 : IsProperOn H S col)
    (h2 : ∀ i ∈ S, col i < k) : chromaticNumberOn H S ≤ k :=
  Nat.sInf_le ⟨col, h1, h2⟩

/-- The defining infimum of `chromaticNumber` is attained: every finite graph
has a proper colouring using colours `< chromaticNumber G`. -/
theorem chromaticNumber_witness (G : Flag emptyType) :
    ∃ c : Fin G.size → ℕ,
      (∀ u v : Fin G.size, G.graph.Adj u v → c u ≠ c v) ∧
      ∀ v : Fin G.size, c v < chromaticNumber G := by
  have hne : {k : ℕ | ∃ c : Fin G.size → ℕ,
      (∀ u v : Fin G.size, G.graph.Adj u v → c u ≠ c v) ∧
      ∀ v : Fin G.size, c v < k}.Nonempty := by
    refine ⟨G.size, fun i => i.val, ?_, fun v => v.isLt⟩
    intro u v hadj hcol
    exact hadj.ne (Fin.ext hcol)
  exact Nat.sInf_mem hne

/-! ## §2. Subset local edge count -/

/-- The number of edges of `H` inside the `S`-neighbourhood of `v`. Shaped
exactly like `Davey2024.SecBridge.fEdgesInNeighbourhood` (same filter shapes)
for definitional compatibility. -/
noncomputable def fEdgesOn (H : Flag emptyType) (S : Finset (Fin H.size))
    (v : Fin H.size) : ℕ :=
  let nbrs := S.filter (fun i => H.graph.Adj v i)
  ((nbrs ×ˢ nbrs).filter
    (fun p => p.1 < p.2 ∧ H.graph.Adj p.1 p.2)).card

/-! ## §3. The padded flag -/

/-- The **padded flag**: the head (`[0, H.size)`) carries `H` restricted to
`S`; the tail carries `K_{D,D}` between `[H.size, H.size + D)` and
`[H.size + D, H.size + 2D)`; there are no head–tail edges. -/
def paddedFlag (H : Flag emptyType) (S : Finset (Fin H.size)) (D : ℕ) :
    Flag emptyType where
  size := H.size + 2 * D
  graph :=
    { Adj := fun i j =>
        (∃ hi : i.val < H.size, ∃ hj : j.val < H.size,
          (⟨i.val, hi⟩ : Fin H.size) ∈ S ∧ (⟨j.val, hj⟩ : Fin H.size) ∈ S ∧
          H.graph.Adj ⟨i.val, hi⟩ ⟨j.val, hj⟩)
        ∨ (H.size ≤ i.val ∧ i.val < H.size + D ∧ H.size + D ≤ j.val)
        ∨ (H.size ≤ j.val ∧ j.val < H.size + D ∧ H.size + D ≤ i.val)
      symm := by
        intro i j h
        rcases h with ⟨hi, hj, hiS, hjS, hadj⟩ | h | h
        · exact Or.inl ⟨hj, hi, hjS, hiS, hadj.symm⟩
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
      loopless := ⟨fun i h => by
        rcases h with ⟨hi, hj, _, _, hadj⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · exact H.graph.irrefl hadj
        · omega
        · omega⟩ }
  embedding := ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
  hsize := Nat.zero_le _

/-- Lift a head vertex of `H` into the padded flag. -/
private def liftHead (H : Flag emptyType) (D : ℕ) (i : Fin H.size) :
    Fin (H.size + 2 * D) :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right H.size (2 * D))⟩

private lemma liftHead_injective (H : Flag emptyType) (D : ℕ) :
    Function.Injective (liftHead H D) := by
  intro a b h
  have h' := congrArg Fin.val h
  exact Fin.ext h'

/-! ## §4. Structure lemmas: neighbourhoods in the padded flag -/

/-- The padded neighbourhood of a head vertex `w` with `⟨w.val, _⟩ ∈ S` is
exactly the head-lift of its `S`-neighbourhood in `H`. -/
private lemma padded_nbhd_eq_image (H : Flag emptyType) (S : Finset (Fin H.size))
    (D : ℕ) (w : Fin (H.size + 2 * D)) (hw : w.val < H.size)
    (hS : (⟨w.val, hw⟩ : Fin H.size) ∈ S) :
    Finset.univ.filter (fun u => (paddedFlag H S D).graph.Adj w u)
      = (S.filter (fun i => H.graph.Adj ⟨w.val, hw⟩ i)).image (liftHead H D) := by
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hadj
    rcases hadj with ⟨hi, hj, hiS, hjS, hadj'⟩ | ⟨h1, _, _⟩ | ⟨_, _, h3⟩
    · exact ⟨⟨u.val, hj⟩, ⟨hjS, hadj'⟩, rfl⟩
    · exfalso; omega
    · exfalso; omega
  · rintro ⟨i, ⟨hiS, hiadj⟩, rfl⟩
    exact Or.inl ⟨hw, i.isLt, hS, hiS, hiadj⟩

/-- **D1**: the padded degree of a head vertex in `S` equals its
`S`-degree in `H`. -/
lemma paddedFlag_degree_headS (H : Flag emptyType) (S : Finset (Fin H.size))
    (D : ℕ) (w : Fin (H.size + 2 * D)) (hw : w.val < H.size)
    (hS : (⟨w.val, hw⟩ : Fin H.size) ∈ S) :
    (Finset.univ.filter (fun u => (paddedFlag H S D).graph.Adj w u)).card
      = (S.filter (fun i => H.graph.Adj ⟨w.val, hw⟩ i)).card := by
  rw [padded_nbhd_eq_image H S D w hw hS,
    Finset.card_image_of_injective _ (liftHead_injective H D)]

/-- The padded neighbourhood of a head vertex outside `S` is empty. -/
private lemma padded_nbhd_eq_empty (H : Flag emptyType) (S : Finset (Fin H.size))
    (D : ℕ) (w : Fin (H.size + 2 * D)) (hw : w.val < H.size)
    (hS : (⟨w.val, hw⟩ : Fin H.size) ∉ S) :
    Finset.univ.filter (fun u => (paddedFlag H S D).graph.Adj w u) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro u _ hadj
  rcases hadj with ⟨hi, _, hiS, _, _⟩ | ⟨h1, _, _⟩ | ⟨_, _, h3⟩
  · exact hS hiS
  · omega
  · omega

/-- **D2**: the padded degree of a head vertex outside `S` is `0`. -/
lemma paddedFlag_degree_head_nonS (H : Flag emptyType) (S : Finset (Fin H.size))
    (D : ℕ) (w : Fin (H.size + 2 * D)) (hw : w.val < H.size)
    (hS : (⟨w.val, hw⟩ : Fin H.size) ∉ S) :
    (Finset.univ.filter (fun u => (paddedFlag H S D).graph.Adj w u)).card = 0 := by
  rw [padded_nbhd_eq_empty H S D w hw hS, Finset.card_empty]

/-- **D3**: every tail vertex of the padded flag has degree exactly `D`.
(No `1 ≤ D` hypothesis needed: the existence of the tail vertex `w` already
forces `1 ≤ D`.) -/
lemma paddedFlag_degree_tail (H : Flag emptyType) (S : Finset (Fin H.size))
    (D : ℕ) (w : Fin (H.size + 2 * D)) (hw : H.size ≤ w.val) :
    (Finset.univ.filter (fun u => (paddedFlag H S D).graph.Adj w u)).card = D := by
  have hwlt : w.val < H.size + 2 * D := w.isLt
  by_cases hw2 : w.val < H.size + D
  · -- lower tail: neighbours are the upper tail interval `[H.size + D, H.size + 2D)`
    have hlt : H.size + D < H.size + 2 * D := by omega
    have hset : Finset.univ.filter (fun u => (paddedFlag H S D).graph.Adj w u)
        = Finset.Ici (⟨H.size + D, hlt⟩ : Fin (H.size + 2 * D)) := by
      ext u
      rw [Finset.mem_filter, Finset.mem_Ici]
      simp only [Finset.mem_univ, true_and]
      constructor
      · intro hadj
        change H.size + D ≤ u.val
        rcases hadj with ⟨hi, _, _, _, _⟩ | ⟨_, _, h3⟩ | ⟨_, _, h3⟩
        · omega
        · exact h3
        · omega
      · intro h
        have h' : H.size + D ≤ u.val := h
        exact Or.inr (Or.inl ⟨hw, hw2, h'⟩)
    rw [hset, Fin.card_Ici]
    change H.size + 2 * D - (H.size + D) = D
    omega
  · -- upper tail: neighbours are the lower tail interval `[H.size, H.size + D)`
    have h0 : H.size < H.size + 2 * D := by omega
    have hltD : H.size + D < H.size + 2 * D := by omega
    have hset : Finset.univ.filter (fun u => (paddedFlag H S D).graph.Adj w u)
        = Finset.Ico (⟨H.size, h0⟩ : Fin (H.size + 2 * D)) ⟨H.size + D, hltD⟩ := by
      ext u
      rw [Finset.mem_filter, Finset.mem_Ico]
      simp only [Finset.mem_univ, true_and]
      constructor
      · intro hadj
        change H.size ≤ u.val ∧ u.val < H.size + D
        rcases hadj with ⟨hi, _, _, _, _⟩ | ⟨_, h2, _⟩ | ⟨h1, h2, _⟩
        · omega
        · omega
        · exact ⟨h1, h2⟩
      · intro h
        have h1 : H.size ≤ u.val := h.1
        have h2 : u.val < H.size + D := h.2
        exact Or.inr (Or.inr ⟨h1, h2, by omega⟩)
    rw [hset, Fin.card_Ico]
    change H.size + D - H.size = D
    omega

/-- **D4**: `Δ(paddedFlag H S D) = D`, given `D ≥ 1` and that every `v ∈ S`
has `S`-degree at most `D` in `H`. -/
lemma paddedFlag_maxDegree (H : Flag emptyType) (S : Finset (Fin H.size))
    (D : ℕ) (hD : 1 ≤ D)
    (hSdeg : ∀ v ∈ S, (S.filter (fun i => H.graph.Adj v i)).card ≤ D) :
    maxDegree (paddedFlag H S D) = D := by
  apply le_antisymm
  · unfold maxDegree
    apply Finset.sup_le
    intro w _
    by_cases hw : w.val < H.size
    · by_cases hSw : (⟨w.val, hw⟩ : Fin H.size) ∈ S
      · exact le_trans (le_of_eq (paddedFlag_degree_headS H S D w hw hSw))
          (hSdeg ⟨w.val, hw⟩ hSw)
      · exact le_trans (le_of_eq (paddedFlag_degree_head_nonS H S D w hw hSw))
          (Nat.zero_le D)
    · exact le_of_eq (paddedFlag_degree_tail H S D w (by omega))
  · have h0 : H.size < H.size + 2 * D := by omega
    have htail := paddedFlag_degree_tail H S D
      (⟨H.size, h0⟩ : Fin (H.size + 2 * D)) le_rfl
    calc D = (Finset.univ.filter (fun u => (paddedFlag H S D).graph.Adj
          (⟨H.size, h0⟩ : Fin (H.size + 2 * D)) u)).card := htail.symm
      _ ≤ maxDegree (paddedFlag H S D) :=
          degree_le_maxDegree (paddedFlag H S D) ⟨H.size, h0⟩

/-! ## §5. Structure lemmas: local edge counts in the padded flag -/

/-- **D5**: the local edge count of the padded flag at a head vertex in `S`
equals the `S`-local edge count of `H`. -/
lemma paddedFlag_edges_headS (H : Flag emptyType) (S : Finset (Fin H.size))
    (D : ℕ) (w : Fin (H.size + 2 * D)) (hw : w.val < H.size)
    (hS : (⟨w.val, hw⟩ : Fin H.size) ∈ S) :
    edgesInNeighbourhood (paddedFlag H S D) w = fEdgesOn H S ⟨w.val, hw⟩ := by
  change ((Finset.univ.filter (fun u => (paddedFlag H S D).graph.Adj w u) ×ˢ
      Finset.univ.filter (fun u => (paddedFlag H S D).graph.Adj w u)).filter
      (fun p => p.1 < p.2 ∧ (paddedFlag H S D).graph.Adj p.1 p.2)).card
    = ((S.filter (fun i => H.graph.Adj ⟨w.val, hw⟩ i) ×ˢ
        S.filter (fun i => H.graph.Adj ⟨w.val, hw⟩ i)).filter
      (fun p => p.1 < p.2 ∧ H.graph.Adj p.1 p.2)).card
  rw [padded_nbhd_eq_image H S D w hw hS, ← Finset.prodMap_image_product,
    Finset.filter_image,
    Finset.card_image_of_injective _
      ((liftHead_injective H D).prodMap (liftHead_injective H D))]
  congr 1
  refine Finset.filter_congr ?_
  rintro ⟨a, b⟩ hp
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  have haS : a ∈ S := (Finset.mem_filter.mp ha).1
  have hbS : b ∈ S := (Finset.mem_filter.mp hb).1
  constructor
  · rintro ⟨hlt, hadj⟩
    have hlt' : a < b := hlt
    refine ⟨hlt', ?_⟩
    rcases hadj with ⟨hi', hj', _, _, hadj'⟩ | ⟨h1, _, _⟩ | ⟨_, _, h3⟩
    · exact hadj'
    · exfalso
      have h1' : H.size ≤ a.val := h1
      have := a.isLt
      omega
    · exfalso
      have h3' : H.size + D ≤ a.val := h3
      have := a.isLt
      omega
  · rintro ⟨hlt, hadj⟩
    have hlt' : liftHead H D a < liftHead H D b := hlt
    exact ⟨hlt', Or.inl ⟨a.isLt, b.isLt, haS, hbS, hadj⟩⟩

/-- **D6**: the local edge count at a head vertex outside `S` is `0`. -/
lemma paddedFlag_edges_head_nonS (H : Flag emptyType) (S : Finset (Fin H.size))
    (D : ℕ) (w : Fin (H.size + 2 * D)) (hw : w.val < H.size)
    (hS : (⟨w.val, hw⟩ : Fin H.size) ∉ S) :
    edgesInNeighbourhood (paddedFlag H S D) w = 0 := by
  change ((Finset.univ.filter (fun u => (paddedFlag H S D).graph.Adj w u) ×ˢ
      Finset.univ.filter (fun u => (paddedFlag H S D).graph.Adj w u)).filter
      (fun p => p.1 < p.2 ∧ (paddedFlag H S D).graph.Adj p.1 p.2)).card = 0
  rw [padded_nbhd_eq_empty H S D w hw hS]
  simp

/-- Adjacency in the padded flag pins down the endpoint value ranges. -/
private lemma padded_adj_val_ranges (H : Flag emptyType) (S : Finset (Fin H.size))
    (D : ℕ) (i j : Fin (H.size + 2 * D))
    (h : (paddedFlag H S D).graph.Adj i j) :
    (i.val < H.size ∧ j.val < H.size)
    ∨ (H.size ≤ i.val ∧ i.val < H.size + D ∧ H.size + D ≤ j.val)
    ∨ (H.size ≤ j.val ∧ j.val < H.size + D ∧ H.size + D ≤ i.val) := by
  rcases h with ⟨hi, hj, _, _, _⟩ | h | h
  · exact Or.inl ⟨hi, hj⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **D7**: the local edge count at a tail vertex is `0` (its neighbourhood
is one side of `K_{D,D}`, which is independent). -/
lemma paddedFlag_edges_tail (H : Flag emptyType) (S : Finset (Fin H.size))
    (D : ℕ) (w : Fin (H.size + 2 * D)) (hw : H.size ≤ w.val) :
    edgesInNeighbourhood (paddedFlag H S D) w = 0 := by
  change ((Finset.univ.filter (fun u => (paddedFlag H S D).graph.Adj w u) ×ˢ
      Finset.univ.filter (fun u => (paddedFlag H S D).graph.Adj w u)).filter
      (fun p => p.1 < p.2 ∧ (paddedFlag H S D).graph.Adj p.1 p.2)).card = 0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp hq
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  have h1 := padded_adj_val_ranges H S D w p.1 (Finset.mem_filter.mp hp1).2
  have h2 := padded_adj_val_ranges H S D w p.2 (Finset.mem_filter.mp hp2).2
  have h3 := padded_adj_val_ranges H S D p.1 p.2 hq.2
  omega

/-! ## §6. Colouring transfer -/

/-- **D8**: restricting a proper colouring of the padded flag to the head
bounds the subset chromatic number. -/
theorem chromaticNumberOn_le_padded (H : Flag emptyType)
    (S : Finset (Fin H.size)) (D : ℕ) :
    chromaticNumberOn H S ≤ chromaticNumber (paddedFlag H S D) := by
  obtain ⟨c, hproper, hbound⟩ := chromaticNumber_witness (paddedFlag H S D)
  refine chromaticNumberOn_le H S _ (fun v => c (liftHead H D v)) ?_ ?_
  · intro i hi j hj hadj
    exact hproper (liftHead H D i) (liftHead H D j)
      (Or.inl ⟨i.isLt, j.isLt, hi, hj, hadj⟩)
  · intro i _
    exact hbound _

/-! ## §7. The degree-scale σ-sparse colouring lemma -/

/-- **Degree-scale σ-sparse colouring lemma** (paper 2's `cor:hjk-scale`,
proved from the verbatim HJK axiom `hurley_colouring_lemma` by disjoint-union
padding with `K_{D,D}`). For every `0 < σ ≤ 1` and `ι > 0` there is `X₀` such
that: whenever every `v ∈ S` has `S`-degree at most `D ≥ X₀` and `S`-local
edge count at most `(1-σ)·C(D,2)`, the subset chromatic number satisfies
`χ_S(H) ≤ (1 - ε(σ) + ι)·D`. -/
theorem hurley_colouring_scale (sigma iota : ℝ)
    (hsigma : 0 < sigma) (hsigma1 : sigma ≤ 1) (hiota : 0 < iota) :
    ∃ X₀ : ℕ, ∀ (H : Flag emptyType) (S : Finset (Fin H.size)) (D : ℕ),
      X₀ ≤ D →
      (∀ v ∈ S, (S.filter (fun i => H.graph.Adj v i)).card ≤ D) →
      (∀ v ∈ S, (fEdgesOn H S v : ℝ) ≤ (1 - sigma) * (Nat.choose D 2 : ℝ)) →
      (chromaticNumberOn H S : ℝ) ≤ (1 - colouringEps sigma + iota) * (D : ℝ) := by
  obtain ⟨X₀, hX⟩ := hurley_colouring_lemma sigma iota hsigma hsigma1 hiota
  refine ⟨max X₀ 1, ?_⟩
  intro H S D hD hSdeg hSsparse
  have hD1 : 1 ≤ D := le_trans (le_max_right X₀ 1) hD
  have hX₀D : X₀ ≤ D := le_trans (le_max_left X₀ 1) hD
  have hmax : maxDegree (paddedFlag H S D) = D :=
    paddedFlag_maxDegree H S D hD1 hSdeg
  have hRHSnn : (0 : ℝ) ≤ (1 - sigma) * (Nat.choose D 2 : ℝ) :=
    mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hsparse : ∀ w : Fin (paddedFlag H S D).size,
      (edgesInNeighbourhood (paddedFlag H S D) w : ℝ) ≤
        (1 - sigma) * (Nat.choose (maxDegree (paddedFlag H S D)) 2 : ℝ) := by
    intro w
    rw [hmax]
    by_cases hw : w.val < H.size
    · by_cases hSw : (⟨w.val, hw⟩ : Fin H.size) ∈ S
      · rw [paddedFlag_edges_headS H S D w hw hSw]
        exact hSsparse ⟨w.val, hw⟩ hSw
      · rw [paddedFlag_edges_head_nonS H S D w hw hSw]
        simpa using hRHSnn
    · rw [paddedFlag_edges_tail H S D w (by omega)]
      simpa using hRHSnn
  have hdeg : X₀ ≤ maxDegree (paddedFlag H S D) := by rw [hmax]; exact hX₀D
  have hchrom := hX (paddedFlag H S D) hdeg hsparse
  rw [hmax] at hchrom
  exact le_trans (Nat.cast_le.mpr (chromaticNumberOn_le_padded H S D)) hchrom

end

end Davey2024

-- Audit: must list `Davey2024.hurley_colouring_lemma` plus only standard axioms.
#print axioms Davey2024.hurley_colouring_scale
