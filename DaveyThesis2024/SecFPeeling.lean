import DaveyThesis2024.SecBridge

/-!
# F-peeling and the degeneracy-greedy colouring extension (B1 repair, L3.1 + L3.2)

Phase L3.1/L3.2 of the development notes: the F-peeling construction
and the degeneracy-greedy colouring extension for the B1 repair of the SEC
chain.

* **L3.1 (F-peeling).** `peelAux G t S` iteratively deletes from `S` any
  `L(G)²`-vertex whose strong F-degree *within the current set* is below
  the threshold `t`, terminating (well-foundedly, on `S.card`) at a subset
  on which every element has strong F-degree ≥ t. `maximalStrongF G t`
  is the result of peeling from `Finset.univ`; it is the unique maximal
  such subset (`maximalStrongF_min_degree` + `subset_maximalStrongF`).

* **L3.2 (degeneracy greedy).** `peelAux_extend_colouring` extends a proper
  `c`-colouring of `peelAux G t S` to a proper `c`-colouring of all of `S`
  (for `c ≥ t`), by re-inserting the peeled vertices in reverse deletion
  order and colouring each greedily: at re-insertion time a peeled vertex
  has fewer than `t ≤ c` coloured neighbours, so a free colour in
  `Finset.range c` exists. `chromaticNumber_le_of_maximalStrongF_colouring`
  assembles this at `S = Finset.univ` into a bound on
  `chromaticNumber (lineGraphSqFlag G)`.

The file ends with the L3.1/L3.2 gates: a K₃,₃ peeling sanity check
(`maximalStrongF k33 16 = ∅`, via the crude bound
`strongFDegree ≤ |F| ≤ |E(K₃,₃)| ≤ 15`) and the toy tightness corollary
`chromaticNumber (lineGraphSqFlag k33) ≤ 20` through the generic zero-case
`chromaticNumber_le_of_maximalStrongF_empty`.

This file is intended to be imported by `StrongChromaticIndex.lean` in a
later phase; it declares no axioms and contains no `sorry`.
-/

namespace Davey2024

open Finset BigOperators Nat Classical in
noncomputable section

set_option linter.unusedSectionVars false

open Davey2024.SecBridge

/-! ## §1. F-peeling (L3.1) -/

/-- **F-peeling step function**: repeatedly delete from `S` a vertex of
`L(G)²` whose strong F-degree within the current set is `< t`, until none
remains. Terminates because each step strictly shrinks `S`. -/
noncomputable def peelAux (G : Flag emptyType) (t : ℕ)
    (S : Finset (Fin (lineGraphSqFlag G).size)) :
    Finset (Fin (lineGraphSqFlag G).size) :=
  if h : ∃ e ∈ S, SecBridge.strongFDegree G S e < t then
    peelAux G t (S.erase h.choose)
  else S
termination_by S.card
decreasing_by exact Finset.card_erase_lt_of_mem h.choose_spec.1

/-- The **maximal strong-F set** at threshold `t`: peel from the full vertex
set of `L(G)²`. Every element has strong F-degree ≥ t within the set
(`maximalStrongF_min_degree`), and it contains every subset with that
property (`subset_maximalStrongF`). -/
noncomputable def maximalStrongF (G : Flag emptyType) (t : ℕ) :
    Finset (Fin (lineGraphSqFlag G).size) :=
  peelAux G t Finset.univ

/-- Recursion equation for `peelAux`, positive case. -/
private theorem peelAux_of_pos {G : Flag emptyType} {t : ℕ}
    {S : Finset (Fin (lineGraphSqFlag G).size)}
    (h : ∃ e ∈ S, SecBridge.strongFDegree G S e < t) :
    peelAux G t S = peelAux G t (S.erase h.choose) := by
  rw [peelAux]
  exact dif_pos h

/-- Recursion equation for `peelAux`, negative case. -/
private theorem peelAux_of_neg {G : Flag emptyType} {t : ℕ}
    {S : Finset (Fin (lineGraphSqFlag G).size)}
    (h : ¬∃ e ∈ S, SecBridge.strongFDegree G S e < t) :
    peelAux G t S = S := by
  rw [peelAux]
  exact dif_neg h

/-- Peeling only deletes: `peelAux G t S ⊆ S`. -/
theorem peelAux_subset (G : Flag emptyType) (t : ℕ)
    (S : Finset (Fin (lineGraphSqFlag G).size)) :
    peelAux G t S ⊆ S := by
  induction S using peelAux.induct G t with
  | case1 S h ih =>
    rw [peelAux_of_pos h]
    exact ih.trans (Finset.erase_subset _ _)
  | case2 S h =>
    rw [peelAux_of_neg h]

/-- The result of peeling has min strong-F-degree ≥ t (general `S` form). -/
theorem peelAux_min_degree (G : Flag emptyType) (t : ℕ)
    (S : Finset (Fin (lineGraphSqFlag G).size)) :
    ∀ e ∈ peelAux G t S, t ≤ SecBridge.strongFDegree G (peelAux G t S) e := by
  induction S using peelAux.induct G t with
  | case1 S h ih =>
    rw [peelAux_of_pos h]
    exact ih
  | case2 S h =>
    rw [peelAux_of_neg h]
    intro e he
    by_contra hlt
    exact h ⟨e, he, by omega⟩

/-- **L3.1 min-degree gate**: every element of `maximalStrongF G t` has
strong F-degree ≥ t within `maximalStrongF G t`. -/
theorem maximalStrongF_min_degree (G : Flag emptyType) (t : ℕ) :
    ∀ e ∈ maximalStrongF G t,
      t ≤ SecBridge.strongFDegree G (maximalStrongF G t) e :=
  peelAux_min_degree G t Finset.univ

/-- Strong F-degree is monotone in the F-set. -/
theorem strongFDegree_mono (G : Flag emptyType)
    {S T : Finset (Fin (lineGraphSqFlag G).size)} (h : S ⊆ T)
    (e : Fin (lineGraphSqFlag G).size) :
    SecBridge.strongFDegree G S e ≤ SecBridge.strongFDegree G T e :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- Peeling never deletes an element of a subset `T ⊆ S` that already has
min strong-F-degree ≥ t within `T` (general `S` form). -/
theorem subset_peelAux (G : Flag emptyType) (t : ℕ)
    {T : Finset (Fin (lineGraphSqFlag G).size)}
    (hT : ∀ e ∈ T, t ≤ SecBridge.strongFDegree G T e)
    (S : Finset (Fin (lineGraphSqFlag G).size)) :
    T ⊆ S → T ⊆ peelAux G t S := by
  induction S using peelAux.induct G t with
  | case1 S h ih =>
    intro hTS
    rw [peelAux_of_pos h]
    refine ih ?_
    intro x hx
    refine Finset.mem_erase.mpr ⟨?_, hTS hx⟩
    rintro rfl
    have h1 := hT _ hx
    have h2 := strongFDegree_mono G hTS h.choose
    have h3 := h.choose_spec.2
    omega
  | case2 S h =>
    intro hTS
    rw [peelAux_of_neg h]
    exact hTS

/-- **Maximality of `maximalStrongF`**: it contains every subset all of
whose elements have strong F-degree ≥ t within the subset. -/
theorem subset_maximalStrongF (G : Flag emptyType) (t : ℕ)
    (T : Finset (Fin (lineGraphSqFlag G).size))
    (hT : ∀ e ∈ T, t ≤ SecBridge.strongFDegree G T e) :
    T ⊆ maximalStrongF G t :=
  subset_peelAux G t hT Finset.univ (Finset.subset_univ T)

/-! ## §2. Degeneracy-greedy colouring extension (L3.2) -/

/-- **Degeneracy greedy**: a proper colouring of `peelAux G t S` with
colours `< c` (for `c ≥ t`) extends to a proper colouring of all of `S`
with colours `< c`. Each peeled vertex had, at its deletion time, fewer
than `t ≤ c` neighbours in the then-current set, so re-inserting the peeled
vertices in reverse deletion order always leaves a free colour in
`Finset.range c`. -/
theorem peelAux_extend_colouring (G : Flag emptyType) (t : ℕ)
    (S : Finset (Fin (lineGraphSqFlag G).size)) (c : ℕ) (htc : t ≤ c)
    (col : Fin (lineGraphSqFlag G).size → ℕ)
    (hproper : ∀ i ∈ peelAux G t S, ∀ j ∈ peelAux G t S,
      (lineGraphSqFlag G).graph.Adj i j → col i ≠ col j)
    (hlt : ∀ i ∈ peelAux G t S, col i < c) :
    ∃ col' : Fin (lineGraphSqFlag G).size → ℕ,
      (∀ i ∈ S, ∀ j ∈ S, (lineGraphSqFlag G).graph.Adj i j → col' i ≠ col' j) ∧
      (∀ i ∈ S, col' i < c) := by
  induction S using peelAux.induct G t generalizing col with
  | case1 S h ih =>
    rw [peelAux_of_pos h] at hproper hlt
    obtain ⟨col'', hp'', hl''⟩ := ih col hproper hlt
    -- the forbidden colours at the re-inserted vertex `h.choose`
    have hforb_card :
        (((S.erase h.choose).filter
          (fun j => (lineGraphSqFlag G).graph.Adj h.choose j)).image col'').card
          < c := by
      have h1 : (((S.erase h.choose).filter
          (fun j => (lineGraphSqFlag G).graph.Adj h.choose j)).image col'').card
          ≤ ((S.erase h.choose).filter
            (fun j => (lineGraphSqFlag G).graph.Adj h.choose j)).card :=
        Finset.card_image_le
      have h2 : ((S.erase h.choose).filter
          (fun j => (lineGraphSqFlag G).graph.Adj h.choose j)).card
          ≤ (S.filter (fun j => (lineGraphSqFlag G).graph.Adj h.choose j)).card :=
        Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
      have h3 : (S.filter
          (fun j => (lineGraphSqFlag G).graph.Adj h.choose j)).card
          = SecBridge.strongFDegree G S h.choose := rfl
      have h4 := h.choose_spec.2
      omega
    -- pick a free colour `a < c`
    have hex : ∃ a, a ∈ Finset.range c ∧
        a ∉ ((S.erase h.choose).filter
          (fun j => (lineGraphSqFlag G).graph.Adj h.choose j)).image col'' := by
      by_contra hno
      push_neg at hno
      have hsub : Finset.range c ⊆
          ((S.erase h.choose).filter
            (fun j => (lineGraphSqFlag G).graph.Adj h.choose j)).image col'' :=
        fun a ha => hno a ha
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_range] at hcard
      omega
    obtain ⟨a, ha_mem, ha_not⟩ := hex
    have ha_lt : a < c := Finset.mem_range.mp ha_mem
    refine ⟨fun i => if i = h.choose then a else col'' i, ?_, ?_⟩
    · intro i hi j hj hadj
      change (if i = h.choose then a else col'' i)
        ≠ (if j = h.choose then a else col'' j)
      by_cases hix : i = h.choose <;> by_cases hjx : j = h.choose
      · -- both equal the re-inserted vertex: impossible (adjacency irreflexive)
        exfalso
        rw [hix, hjx] at hadj
        exact ((lineGraphSqFlag G).graph.ne_of_adj hadj) rfl
      · -- i is the re-inserted vertex, j is not
        rw [if_pos hix, if_neg hjx]
        intro heq
        apply ha_not
        rw [heq]
        exact Finset.mem_image_of_mem col''
          (Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨hjx, hj⟩, hix ▸ hadj⟩)
      · -- j is the re-inserted vertex, i is not
        rw [if_neg hix, if_pos hjx]
        intro heq
        apply ha_not
        rw [← heq]
        exact Finset.mem_image_of_mem col''
          (Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨hix, hi⟩, (hjx ▸ hadj).symm⟩)
      · -- neither: the IH colouring is proper on `S.erase h.choose`
        rw [if_neg hix, if_neg hjx]
        exact hp'' i (Finset.mem_erase.mpr ⟨hix, hi⟩)
          j (Finset.mem_erase.mpr ⟨hjx, hj⟩) hadj
    · intro i hi
      change (if i = h.choose then a else col'' i) < c
      by_cases hix : i = h.choose
      · rw [if_pos hix]
        exact ha_lt
      · rw [if_neg hix]
        exact hl'' i (Finset.mem_erase.mpr ⟨hix, hi⟩)
  | case2 S h =>
    rw [peelAux_of_neg h] at hproper hlt
    exact ⟨col, hproper, hlt⟩

/-! ## §3. Assembly: chromatic-number bound from a `maximalStrongF` colouring -/

/-- **L3.2 assembly**: a proper `c`-colouring of `maximalStrongF G t` (with
`c ≥ t`) extends greedily to all of `L(G)²`, so
`chromaticNumber (lineGraphSqFlag G) ≤ c`. -/
theorem chromaticNumber_le_of_maximalStrongF_colouring (G : Flag emptyType)
    (t c : ℕ) (htc : t ≤ c) (col : Fin (lineGraphSqFlag G).size → ℕ)
    (hproper : ∀ i ∈ maximalStrongF G t, ∀ j ∈ maximalStrongF G t,
      (lineGraphSqFlag G).graph.Adj i j → col i ≠ col j)
    (hlt : ∀ i ∈ maximalStrongF G t, col i < c) :
    chromaticNumber (lineGraphSqFlag G) ≤ c := by
  obtain ⟨col', hp, hl⟩ :=
    peelAux_extend_colouring G t Finset.univ c htc col hproper hlt
  exact Nat.sInf_le ⟨col',
    fun u v hadj => hp u (Finset.mem_univ u) v (Finset.mem_univ v) hadj,
    fun v => hl v (Finset.mem_univ v)⟩

/-- **Zero-case corollary** (genuine tightness content of the toy gate):
if peeling at threshold `t` empties the vertex set, the greedy colouring
alone gives `chromaticNumber (lineGraphSqFlag G) ≤ t`. -/
theorem chromaticNumber_le_of_maximalStrongF_empty (G : Flag emptyType)
    (t : ℕ) (h : maximalStrongF G t = ∅) :
    chromaticNumber (lineGraphSqFlag G) ≤ t := by
  refine chromaticNumber_le_of_maximalStrongF_colouring G t t le_rfl
    (fun _ => 0) ?_ ?_
  · intro i hi
    rw [h] at hi
    exact absurd hi (Finset.notMem_empty i)
  · intro i hi
    rw [h] at hi
    exact absurd hi (Finset.notMem_empty i)

/-! ## §4. Gates: K₃,₃ peeling sanity (L3.1) + toy tightness test (L3.2) -/

/-- `K₃,₃` on vertex set `Fin 6`: left side `{0, 1, 2}`, right side
`{3, 4, 5}`, with all cross edges (the `m = 3` instance of the `K_{m,m}`
family that refuted the retired `sec_combinatorial_identity_step1`, inlined
with literals; see the development notes §0 item 4). -/
def k33 : Flag emptyType where
  size := 6
  graph :=
    { Adj := fun i j => (i.val < 3 ∧ 3 ≤ j.val) ∨ (j.val < 3 ∧ 3 ≤ i.val)
      symm := fun _ _ h => Or.symm h
      loopless := ⟨fun i h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega⟩ }
  embedding := ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
  hsize := Nat.zero_le _

/-- `K₃,₃` has at most `C(6,2) = 15` canonical edges (crude bound: canonical
edges are pairs with `e.1 < e.2` over `Fin 6 × Fin 6`). -/
private lemma card_edgeFinset_k33_le : (edgeFinset k33).card ≤ 15 := by
  have hsub : edgeFinset k33 ⊆
      (Finset.univ : Finset (Fin k33.size × Fin k33.size)).filter
        (fun p => p.1 < p.2) := by
    intro p hp
    unfold edgeFinset at hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.2⟩
  have hcard : ((Finset.univ : Finset (Fin k33.size × Fin k33.size)).filter
      (fun p => p.1 < p.2)).card = 15 := by
    change ((Finset.univ : Finset (Fin 6 × Fin 6)).filter
      (fun p => p.1 < p.2)).card = 15
    decide
  calc (edgeFinset k33).card
      ≤ _ := Finset.card_le_card hsub
    _ = 15 := hcard

/-- Strong F-degree is at most `|F|`. -/
theorem strongFDegree_le_card (G : Flag emptyType)
    (F : Finset (Fin (lineGraphSqFlag G).size))
    (e : Fin (lineGraphSqFlag G).size) :
    SecBridge.strongFDegree G F e ≤ F.card :=
  Finset.card_filter_le _ _

/-- **Gate L3.1 (K₃,₃ peeling sanity)**: at any threshold `t ≥ 16` the
peeling of `K₃,₃` empties, since `L(K₃,₃)²` has only `|E(K₃,₃)| ≤ 15`
vertices and `strongFDegree ≤ |F|`. -/
lemma maximalStrongF_k33_empty (t : ℕ) (ht : 16 ≤ t) :
    maximalStrongF k33 t = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  have h1 : t ≤ SecBridge.strongFDegree k33 (maximalStrongF k33 t) e :=
    maximalStrongF_min_degree k33 t e he
  have h2 : SecBridge.strongFDegree k33 (maximalStrongF k33 t) e
      ≤ (maximalStrongF k33 t).card :=
    strongFDegree_le_card k33 (maximalStrongF k33 t) e
  have h3 : (maximalStrongF k33 t).card
      ≤ (Finset.univ : Finset (Fin (lineGraphSqFlag k33).size)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  have h4 : (Finset.univ : Finset (Fin (lineGraphSqFlag k33).size)).card
      = (edgeFinset k33).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    rfl
  have h5 := card_edgeFinset_k33_le
  omega

-- Gate L3.1: peeling `K₃,₃` at threshold 16 empties the vertex set.
example : maximalStrongF k33 16 = ∅ := maximalStrongF_k33_empty 16 le_rfl

-- Gate L3.2 (toy tightness test): with `t = 20` the peeled set is empty,
-- the colouring hypotheses hold vacuously, and the degeneracy greedy alone
-- yields `χ(L(K₃,₃)²) ≤ 20`.
example : chromaticNumber (lineGraphSqFlag k33) ≤ 20 :=
  chromaticNumber_le_of_maximalStrongF_empty k33 20
    (maximalStrongF_k33_empty 20 (by omega))

end

end Davey2024
