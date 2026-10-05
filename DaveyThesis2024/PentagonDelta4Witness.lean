import DaveyThesis2024.PentagonDelta4
import DaveyThesis2024.PentagonUnique


/-!
# A Δ = 4 extremal graph: the circulant `C₁₂(2,3)`

The circulant graph `C₁₂(2,3)` on `Fin 12` (`i ~ i ± 2, i ± 3`) attains the Δ = 4 pentagon
extremum: it is triangle-free, 4-regular, and has `pentagonCount = 48`, i.e. ratio
`P/(n·Δ⁴) = 48/(12·256) = 1/64`.  The bound `P ≤ 4|G|` it attains is proved as
`Delta4Gen.pentagon_bound_delta4_sharp` in `DaveyThesis2024/Delta4/`; `C₁₃(2,3)` attains it
too, with `52`, so `C₁₂(2,3)` is not the unique extremal graph and equality is not
classified.

The exact count uses vertex-transitivity (translation is an automorphism) plus the
provable per-vertex bound `pentagonCountAt_le_24`: vertex-transitivity gives
`5·P = 12·P(0)`, and `20 ≤ P(0) ≤ 24` together with `5 ∣ 12·P(0)` force `P(0) = 20`,
`P = 48`. (So the extremum sits at `P = 4n`, inside the weaker bound
`P ≤ 24n/5 = 4.8n` that `pentagon_bound_delta4` proves outright.)
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

/-- The root vertex `0`, typed through `c12Flag.size`. -/
def c12Root : Fin c12Flag.size := ⟨0, by norm_num [c12Flag]⟩

/-- Every vertex of `C₁₂(2,3)` has degree exactly four. -/
lemma c12_vertexDegree (v : Fin c12Flag.size) : vertexDegree c12Flag v = 4 := by
  rw [vertexDegree, Finset.filter_congr_decidable]
  revert v
  decide

/-- `C₁₂(2,3)` has maximum degree exactly four. -/
lemma c12_maxDegree : maxDegree c12Flag = 4 := by
  refine le_antisymm c12_maxDegree_le ?_
  calc (4 : ℕ) = vertexDegree c12Flag c12Root := (c12_vertexDegree c12Root).symm
    _ ≤ maxDegree c12Flag := vertexDegree_le_maxDegree c12Flag c12Root

/-- `C₁₂(2,3)` is four-regular. -/
lemma c12_isRegular : IsRegular c12Flag := by
  intro v
  rw [c12_maxDegree]
  exact c12_vertexDegree v

/-! ### Non-vacuity of the saturation lemmas

`sum_attach_card_eq_twelve` and `attach_multiplicity_eq_three` assume a triangle-free
*four-regular* graph.  `C₁₂(2,3)` satisfies all three hypotheses, so neither statement is
vacuous, and the shell of its root really does spend the full attachment budget. -/

/-- Non-vacuity witness: saturation holds at the root of `C₁₂(2,3)`. -/
theorem c12_sum_attach_card_eq_twelve :
    ∑ x ∈ PentagonLocal.shellSet c12Flag c12Root,
      (PentagonLocal.attachSet c12Flag c12Root x).card = 12 :=
  PentagonLocal.sum_attach_card_eq_twelve c12_triangleFree c12_isRegular c12_maxDegree c12Root

/-- Non-vacuity witness: the shell T-identity instantiates at the root of `C₁₂(2,3)`. -/
theorem c12_shellObjective_identity :
    2 * (∑ p ∈ PentagonLocal.shellPairsLt c12Flag c12Root,
          (PentagonLocal.attachSet c12Flag c12Root p.1).card
            * (PentagonLocal.attachSet c12Flag c12Root p.2).card)
        + 4 * ((PentagonLocal.shellPos c12Flag c12Root).filter
            fun x => (PentagonLocal.attachSet c12Flag c12Root x).card = 3).card
        + 12 * ((PentagonLocal.shellPos c12Flag c12Root).filter
            fun x => (PentagonLocal.attachSet c12Flag c12Root x).card = 4).card
        + ∑ x ∈ PentagonLocal.shellPos c12Flag c12Root,
            (2 * (PentagonLocal.attachSet c12Flag c12Root x).card - 1)
              * PentagonLocal.shellSlack c12Flag c12Root x
      = 36 + 2 * PentagonLocal.e22 c12Flag c12Root :=
  PentagonLocal.shellObjective_identity c12_triangleFree c12_isRegular c12_maxDegree c12Root

/-- Non-vacuity witness: `e₂₂ ≤ 6` at the root of `C₁₂(2,3)`. -/
theorem c12_e22_le_six : PentagonLocal.e22 c12Flag c12Root ≤ 6 :=
  PentagonLocal.e22_le_six c12_triangleFree c12_isRegular c12_maxDegree c12Root

/-- Non-vacuity witness: the per-letter saturation count at the root of `C₁₂(2,3)`. -/
theorem c12_attach_multiplicity_eq_three {a : Fin c12Flag.size}
    (hva : c12Flag.graph.Adj c12Root a) :
    ((PentagonLocal.shellSet c12Flag c12Root).filter
      fun x => a ∈ PentagonLocal.attachSet c12Flag c12Root x).card = 3 :=
  PentagonLocal.attach_multiplicity_eq_three c12_triangleFree c12_isRegular c12_maxDegree hva

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

/-- **The Δ = 4 extremal ratio is attained**: there is a triangle-free graph of maximum
    degree ≤ 4 with `P·64 = |G|·4⁴`, i.e. pentagon ratio exactly `1/64`. (Witness:
    `C₁₂(2,3)`, `P = 48`, `n = 12`; `C₁₃(2,3)` attains it too, so the extremal graph is not
    unique and equality is not classified.) -/
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


/-! ## `K₄,₄`: a second Δ = 4 witness, and non-vacuity of the low branch

`C₁₂(2,3)` cannot witness the low branch of the rerooting row: its shell objective is at
least `20`, above the `18` threshold.  `K₄,₄` is the complementary extreme — bipartite,
triangle-free, four-regular, with no pentagons at all and an empty shell edge set, so its
shell objective is `0`.  It is therefore the witness that `pentagonQ_le_160_of_shellObjective_le_eighteen'`
actually fires on something. -/

/-- Filter cards differing only in the `Decidable` instance agree.  Needed whenever a
    `decide`-friendly instance meets the classical one used by `maxDegree`. -/
theorem card_filter_inst {α : Type*} (s : Finset α) (p : α → Prop)
    (d1 d2 : DecidablePred p) :
    (@Finset.filter α p d1 s).card = (@Finset.filter α p d2 s).card := by
  have h : d1 = d2 := Subsingleton.elim _ _
  subst h; rfl

/-- `K₄,₄` on `Fin 8`: `u ~ v` iff exactly one of `u, v` lies in the low half. -/
def k44Graph : SimpleGraph (Fin 8) :=
  SimpleGraph.fromRel (fun u v => (u.val < 4) ≠ (v.val < 4))

instance instDecK44 : DecidableRel k44Graph.Adj := by
  unfold k44Graph; intro u v; rw [SimpleGraph.fromRel_adj]; exact instDecidableAnd

/-- `K₄,₄` as a `Flag emptyType`. -/
def k44Flag : Flag emptyType where
  size := 8
  graph := k44Graph
  embedding := ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
  hsize := Nat.zero_le _

section Decide
local instance instDecK44Flag : DecidableRel k44Flag.graph.Adj := instDecK44

theorem k44_triangleFree : IsTriangleFree k44Flag := by
  intro u v w; revert u v w; decide

theorem k44_deg (v : Fin k44Flag.size) :
    (Finset.univ.filter (fun u => k44Flag.graph.Adj v u)).card = 4 := by
  revert v; decide

/-- `K₄,₄` is bipartite: two vertices both non-adjacent to `v` and distinct from `v` lie on
    the same side as `v`, hence are non-adjacent to each other. -/
theorem k44_shell_indep (v x y : Fin k44Flag.size)
    (hx : x ≠ v) (hnx : ¬ k44Flag.graph.Adj v x)
    (hy : y ≠ v) (hny : ¬ k44Flag.graph.Adj v y) : ¬ k44Flag.graph.Adj x y := by
  revert v x y; decide

end Decide

theorem k44_maxDegree : maxDegree k44Flag = 4 := by
  unfold maxDegree
  apply le_antisymm
  · refine Finset.sup_le (fun v _ => ?_)
    exact le_trans (le_of_eq (card_filter_inst _ _ _ _)) (k44_deg v).le
  · refine le_trans ?_ (Finset.le_sup (Finset.mem_univ (⟨0, by decide⟩ : Fin k44Flag.size)))
    exact le_of_eq ((k44_deg _).symm.trans (card_filter_inst _ _ _ _))

theorem k44_isRegular : IsRegular k44Flag := by
  intro v
  rw [k44_maxDegree]
  exact (card_filter_inst _ _ _ _).trans (k44_deg v)

/-- `K₄,₄` is bipartite, so its shell carries no edges and the shell objective vanishes. -/
theorem k44_shellObjective_eq_zero (v : Fin k44Flag.size) :
    ∑ p ∈ PentagonLocal.shellPairsLt k44Flag v,
      (PentagonLocal.attachSet k44Flag v p.1).card
        * (PentagonLocal.attachSet k44Flag v p.2).card = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  exfalso
  rw [PentagonLocal.shellPairsLt, Finset.mem_filter, Finset.mem_product,
    PentagonLocal.shellSet, Finset.mem_filter, Finset.mem_filter] at hp
  obtain ⟨⟨⟨-, hp1v, hnp1⟩, ⟨-, hp2v, hnp2⟩⟩, -, hadj⟩ := hp
  exact k44_shell_indep v p.1 p.2 hp1v hnp1 hp2v hnp2 hadj

/-- **Non-vacuity of the low branch.**  `K₄,₄` is triangle-free, four-regular, and has
    shell objective `0 ≤ 18` at every vertex, so the low-branch hypothesis is satisfiable
    and the theorem really does fire. -/
theorem k44_pentagonQ_le_160 (v : Fin k44Flag.size) : pentagonQ k44Flag v ≤ 160 :=
  pentagonQ_le_160_of_shellObjective_le_eighteen' k44_triangleFree k44_maxDegree v
    (by rw [k44_shellObjective_eq_zero]; norm_num)

end Davey2024
