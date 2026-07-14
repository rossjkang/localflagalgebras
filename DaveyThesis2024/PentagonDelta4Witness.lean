import DaveyThesis2024.PentagonDelta4
import DaveyThesis2024.PentagonUnique


/-!
# The Δ = 4 conjectural extremum: the circulant `C₁₂(2,3)`

The circulant graph `C₁₂(2,3)` on `Fin 12` (`i ~ i ± 2, i ± 3`) is the conjectured Δ = 4
pentagon extremum: it is triangle-free, 4-regular, and has `pentagonCount = 48`, i.e.
ratio `P/(n·Δ⁴) = 48/(12·256) = 1/64`.

The exact count uses vertex-transitivity (translation is an automorphism) plus the
provable per-vertex bound `pentagonCountAt_le_24`: vertex-transitivity gives
`5·P = 12·P(0)`, and `20 ≤ P(0) ≤ 24` together with `5 ∣ 12·P(0)` force `P(0) = 20`,
`P = 48`. (So the conjectured extremum sits at `P = 4n`, inside the honest provable bound
`P ≤ 24n/5 = 4.8n` of `pentagon_bound_delta4`.)
-/

namespace Davey2024

open Finset
open scoped Classical

/-- The 24 edges of `C₁₂(2,3)` (one orientation each; `fromRel` symmetrises). -/
def c12Edges : Finset (ℕ × ℕ) :=
  {(0, 2), (0, 3), (0, 9), (0, 10), (1, 3), (1, 4), (1, 10), (1, 11),
   (2, 4), (2, 5), (2, 11), (3, 5), (3, 6), (4, 6), (4, 7), (5, 7),
   (5, 8), (6, 8), (6, 9), (7, 9), (7, 10), (8, 10), (8, 11), (9, 11)}

/-- The circulant `C₁₂(2,3)` on `Fin 12`. -/
def c12Graph : SimpleGraph (Fin 12) :=
  SimpleGraph.fromRel (fun u v => (u.val, v.val) ∈ c12Edges)

instance instDecRelC12 : DecidableRel c12Graph.Adj := by
  unfold c12Graph
  intro u v
  rw [SimpleGraph.fromRel_adj]
  exact instDecidableAnd

/-- `C₁₂(2,3)` as a `Flag emptyType`. -/
def c12Flag : Flag emptyType where
  size := 12
  graph := c12Graph
  embedding := ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
  hsize := Nat.zero_le _

instance : DecidableRel c12Flag.graph.Adj := instDecRelC12

lemma c12_triangleFree : IsTriangleFree c12Flag := by
  unfold IsTriangleFree
  decide

lemma c12_maxDegree_le : maxDegree c12Flag ≤ 4 := by
  rw [maxDegree]
  refine Finset.sup_le fun v _ => ?_
  rw [Finset.filter_congr_decidable]
  revert v
  decide

/-- Translation `u ↦ u + a (mod 12)`, an automorphism of the circulant. -/
def c12Translate (a u : Fin 12) : Fin 12 :=
  ⟨(u.val + a.val) % 12, Nat.mod_lt _ (by norm_num)⟩

/-- Vertex-transitivity: every vertex of `C₁₂(2,3)` lies on the same number of pentagons. -/
lemma pentagonCountAt_c12_const (a : Fin 12) :
    pentagonCountAt c12Flag a = pentagonCountAt c12Flag (0 : Fin 12) := by
  have hinj : ∀ a : Fin 12, Function.Injective (c12Translate a) := by decide
  have hiff : ∀ a i j : Fin 12, c12Graph.Adj i j ↔
      c12Graph.Adj (c12Translate a i) (c12Translate a j) := by decide
  have hsurj : ∀ a u : Fin 12, ∃ w, c12Translate a w = u := by decide
  have htr0 : ∀ a : Fin 12, c12Translate a 0 = a := by decide
  have ht := pentagonCountAt_transfer (H := c12Flag) (G := c12Flag) (c12Translate a)
    (hinj a) (hiff a) (fun _ u _ => hsurj a u) (0 : Fin 12)
  rw [htr0 a] at ht
  exact ht

/-- The 20 pentagons through vertex `0` of `C₁₂(2,3)`. -/
def c12PentagonsAtZero : Finset (Finset (Fin 12)) :=
  {{0, 1, 2, 3, 4}, {0, 1, 2, 3, 11}, {0, 1, 2, 4, 10}, {0, 1, 2, 10, 11},
   {0, 1, 3, 9, 11}, {0, 1, 9, 10, 11}, {0, 2, 3, 4, 6}, {0, 2, 4, 6, 9},
   {0, 2, 4, 7, 9}, {0, 2, 4, 7, 10}, {0, 2, 5, 7, 9}, {0, 2, 5, 7, 10},
   {0, 2, 5, 8, 10}, {0, 2, 8, 10, 11}, {0, 3, 5, 7, 9}, {0, 3, 5, 7, 10},
   {0, 3, 5, 8, 10}, {0, 3, 6, 8, 10}, {0, 6, 8, 9, 10}, {0, 8, 9, 10, 11}}

lemma c12PentagonsAtZero_card : c12PentagonsAtZero.card = 20 := by decide

open scoped Classical in
set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
lemma c12PentagonsAtZero_sub : c12PentagonsAtZero ⊆
    Finset.univ.filter fun S => IsPentagon c12Flag S ∧ (0 : Fin 12) ∈ S := by
  intro S hS
  simp only [c12PentagonsAtZero, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 2, 4, 1, 3] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 2, 11, 1, 3] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 2, 4, 1, 10] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 2, 11, 1, 10] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 9, 11, 1, 3] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 9, 11, 1, 10] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 2, 4, 6, 3] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 9, 6, 4, 2] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 9, 7, 4, 2] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 2, 4, 7, 10] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 9, 7, 5, 2] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 2, 5, 7, 10] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 2, 5, 8, 10] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 2, 11, 8, 10] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 9, 7, 5, 3] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 10, 7, 5, 3] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 10, 8, 5, 3] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 10, 8, 6, 3] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 9, 6, 8, 10] : Fin 5 → Fin 12), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![0, 9, 11, 8, 10] : Fin 5 → Fin 12), by decide⟩, by decide⟩

/-- **`C₁₂(2,3)` has exactly 48 pentagons.** Vertex-transitivity gives `5·P = 12·P(0)`;
    `20 ≤ P(0)` (explicit list) and `P(0) ≤ 24` (the Δ=4 bound), with `5 ∣ 12·P(0)`, force
    `P(0) = 20` and `P = 48`. -/
theorem pentagonCount_c12 : pentagonCount c12Flag = 48 := by
  have hsum := pentagonCount_sum c12Flag
  rw [Finset.sum_congr rfl (fun a _ => pentagonCountAt_c12_const a), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  -- hsum : 12 * pentagonCountAt c12Flag 0 = 5 * pentagonCount c12Flag
  have hge : 20 ≤ pentagonCountAt c12Flag (0 : Fin 12) := by
    rw [pentagonCountAt]
    calc (20 : ℕ) = c12PentagonsAtZero.card := c12PentagonsAtZero_card.symm
      _ ≤ _ := Finset.card_le_card c12PentagonsAtZero_sub
  have hle : pentagonCountAt c12Flag (0 : Fin 12) ≤ 24 :=
    pentagonCountAt_le_24_of_maxDegree_le_four c12Flag c12_triangleFree c12_maxDegree_le
      (0 : Fin 12)
  omega

/-- **The Δ = 4 conjectural extremum is realised**: there is a triangle-free graph of
    maximum degree ≤ 4 with `P·64 = |G|·4⁴`, i.e. pentagon ratio exactly `1/64`. (Witness:
    `C₁₂(2,3)`, `P = 48`, `n = 12`.) -/
theorem pentagon_delta4_witness :
    ∃ G : Flag emptyType, IsTriangleFree G ∧ maxDegree G ≤ 4 ∧
      pentagonCount G * 64 = G.size * 4 ^ 4 :=
  ⟨c12Flag, c12_triangleFree, c12_maxDegree_le, by rw [pentagonCount_c12]; decide⟩

/-! ## Tightness of the local bound: a vertex on exactly 24 pentagons

The per-vertex bound `pentagonCountAt_le_24` is tight: this 11-vertex triangle-free graph
of maximum degree 4 (`geng` graph6 `J?B@xzoyEo?`) has a vertex (`5`) lying on exactly 24
pentagons — matching the fibre-LP maximum. So the density bound `P ≤ 24n/5 = 4.8n` is the
best obtainable from any per-vertex argument. -/

/-- The 22 edges of the local-tightness witness graph on `Fin 11`. -/
def g24Edges : Finset (ℕ × ℕ) :=
  {(0, 5), (0, 8), (0, 9), (0, 10), (1, 5), (1, 8), (1, 9), (1, 10),
   (2, 6), (2, 7), (2, 8), (2, 9), (3, 6), (3, 7), (3, 8), (3, 10),
   (4, 6), (4, 7), (4, 9), (4, 10), (5, 6), (5, 7)}

/-- A triangle-free, maximum-degree-4 graph on `Fin 11` with a vertex on 24 pentagons. -/
def g24Graph : SimpleGraph (Fin 11) :=
  SimpleGraph.fromRel (fun u v => (u.val, v.val) ∈ g24Edges)

instance instDecRelG24 : DecidableRel g24Graph.Adj := by
  unfold g24Graph
  intro u v
  rw [SimpleGraph.fromRel_adj]
  exact instDecidableAnd

def g24Flag : Flag emptyType where
  size := 11
  graph := g24Graph
  embedding := ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
  hsize := Nat.zero_le _

instance : DecidableRel g24Flag.graph.Adj := instDecRelG24

lemma g24_triangleFree : IsTriangleFree g24Flag := by
  unfold IsTriangleFree
  decide

lemma g24_maxDegree_le : maxDegree g24Flag ≤ 4 := by
  rw [maxDegree]
  refine Finset.sup_le fun v _ => ?_
  rw [Finset.filter_congr_decidable]
  revert v
  decide

/-- The 24 pentagons through vertex `5` of `g24Flag`. -/
def g24PentagonsAtFive : Finset (Finset (Fin 11)) :=
  {{0, 2, 5, 6, 8}, {0, 2, 5, 6, 9}, {0, 2, 5, 7, 8}, {0, 2, 5, 7, 9},
   {0, 3, 5, 6, 8}, {0, 3, 5, 6, 10}, {0, 3, 5, 7, 8}, {0, 3, 5, 7, 10},
   {0, 4, 5, 6, 9}, {0, 4, 5, 6, 10}, {0, 4, 5, 7, 9}, {0, 4, 5, 7, 10},
   {1, 2, 5, 6, 8}, {1, 2, 5, 6, 9}, {1, 2, 5, 7, 8}, {1, 2, 5, 7, 9},
   {1, 3, 5, 6, 8}, {1, 3, 5, 6, 10}, {1, 3, 5, 7, 8}, {1, 3, 5, 7, 10},
   {1, 4, 5, 6, 9}, {1, 4, 5, 6, 10}, {1, 4, 5, 7, 9}, {1, 4, 5, 7, 10}}

lemma g24PentagonsAtFive_card : g24PentagonsAtFive.card = 24 := by decide

open scoped Classical in
set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
lemma g24PentagonsAtFive_sub : g24PentagonsAtFive ⊆
    Finset.univ.filter fun S => IsPentagon g24Flag S ∧ (5 : Fin 11) ∈ S := by
  intro S hS
  simp only [g24PentagonsAtFive, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 0, 8, 2, 6] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 0, 9, 2, 6] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 0, 8, 2, 7] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 0, 9, 2, 7] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 0, 8, 3, 6] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 0, 10, 3, 6] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 0, 8, 3, 7] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 0, 10, 3, 7] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 0, 9, 4, 6] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 0, 10, 4, 6] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 0, 9, 4, 7] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 0, 10, 4, 7] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 1, 8, 2, 6] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 1, 9, 2, 6] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 1, 8, 2, 7] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 1, 9, 2, 7] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 1, 8, 3, 6] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 1, 10, 3, 6] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 1, 8, 3, 7] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 1, 10, 3, 7] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 1, 9, 4, 6] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 1, 10, 4, 6] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 1, 9, 4, 7] : Fin 5 → Fin 11), by decide⟩, by decide⟩
  · exact mem_filter.mpr ⟨mem_univ _, ⟨(![5, 1, 10, 4, 7] : Fin 5 → Fin 11), by decide⟩, by decide⟩

/-- **The Petersen-style per-vertex bound at Δ = 4 is tight**: vertex `5` of `g24Flag`
    lies on exactly 24 pentagons (`≤ 24` by `pentagonCountAt_le_24`, `≥ 24` by the list). -/
theorem pentagonCountAt_g24_five : pentagonCountAt g24Flag (5 : Fin 11) = 24 := by
  refine le_antisymm
    (pentagonCountAt_le_24_of_maxDegree_le_four g24Flag g24_triangleFree g24_maxDegree_le
      (5 : Fin 11)) ?_
  rw [pentagonCountAt]
  calc (24 : ℕ) = g24PentagonsAtFive.card := g24PentagonsAtFive_card.symm
    _ ≤ _ := Finset.card_le_card g24PentagonsAtFive_sub

/-- **Tightness of the local (per-vertex) Δ = 4 bound**: there is a triangle-free graph of
    maximum degree ≤ 4 with a vertex on exactly 24 pentagons. Hence `pentagonCountAt_le_24`
    and the resulting density bound `P ≤ 24n/5` are the best the per-vertex method gives. -/
theorem pentagonCountAt_le_24_tight :
    ∃ (G : Flag emptyType) (v : Fin G.size),
      IsTriangleFree G ∧ maxDegree G ≤ 4 ∧ pentagonCountAt G v = 24 :=
  ⟨g24Flag, (5 : Fin 11), g24_triangleFree, g24_maxDegree_le, pentagonCountAt_g24_five⟩

end Davey2024
