import DaveyThesis2024.SecBridge

/-!
# Phase L1 smoke test — anti-vacuity of the F-faithful SEC bridge (NOT a build target)

**Audit gate L1(b)** of the development notes: for a small concrete host,
the F-faithful construction `colouredGraph22OfEdgeF` / `SecFSeqItem.toGenFlag`
(SecBridge.lean §8) yields **nonzero** induced counts AND **nonzero**
`genUnlabelledDensity` on ≥ 3 objective-support flags — killing a recurrence
of the vacuity bug (the old F-free bridge host had `edgeColour ≡ 0`, so ALL
7,794 objective-support flags had density 0; see plan §0 item 4).

This file is quarantined: NOT imported by `DaveyThesis2024.lean` or any
build target. It exists as the gate artifact. (The companion
`SecIdentityRefutation.lean` that mechanised the `K_{3,3}` refutation of the
old false axiom was deleted in L4.2 together with that axiom; its content is
summarised in the development notes §0.)

## The concrete host

`K_{5,5}` (so that `Δ = 5` and the `C(Δ,5)` density denominator is nonzero),
with `F` = all 25 edges except `{4, 9}`, designated edge `{0, 5} ∈ F`.
Then `N(u) ∪ N(w)` = all 10 vertices (every vertex colour 0 = black/X), and
the edge colouring is 1 except on `{4,9}`. Exactly three basis flags in the
cert objective support embed (found by exhaustive `#eval` search over all
17,950 basis flags, session scratchpad `discover*.lean`):

| j | shape | induced count | `targetArr[j]` |
|---|---|---|---|
| 1714 | `K_{2,3}`, all-X, all 6 edges F | 1824 | −200000000000 |
| 7784 | `K_{2,3}`, all-X, 5 F-edges + 1 non-F | 96 | −133333333333 |
| 8559 | `K_{1,4}`, all-X, all 4 edges F | 1008 | −100000000000 |

(With F = ALL 25 edges only two support flags embed — 1714 and 8559 — since
`K_{2,3}` and `K_{1,4}` are the only all-X/all-F bipartite size-5 shapes;
dropping one edge from F admits the third, mixed-colour flag 7784.)

## Consistency with L0

The same host with `F = ∅` gives induced count **0** on the same three flags
(each carries an F-edge, the host has none) — the L0 refutation's
`native_decide` check (`sec_objective_support_has_F_edge`, since deleted with
the refutation file) showed this for the ENTIRE support.
-/

namespace Davey2024

open Finset BigOperators Nat Classical in
noncomputable section

set_option linter.unusedSectionVars false

namespace SecSmokeL1

open Davey2024.SecBridge Davey2024.SecBasis

/-! ## §1. The host graph `K_{5,5}` and its F-set -/

/-- `K_{5,5}` on `Fin 10`: left side `{0,…,4}`, right side `{5,…,9}`. -/
def k55 : Flag emptyType where
  size := 10
  graph :=
    { Adj := fun i j => (i.val < 5 ∧ 5 ≤ j.val) ∨ (j.val < 5 ∧ 5 ≤ i.val)
      symm := fun _ _ h => Or.symm h
      loopless := ⟨fun i h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega⟩ }
  embedding := ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
  hsize := Nat.zero_le _

/-- Vertex-index helper (`k55.size` is definitionally `10`). -/
private def hlt10 : ∀ a : ℕ, a < 10 → a < k55.size := fun _ h => h

/-- Left endpoint `0` of the designated edge. -/
def u0 : Fin k55.size := ⟨0, hlt10 0 (by omega)⟩
/-- Right endpoint `5` of the designated edge. -/
def w5 : Fin k55.size := ⟨5, hlt10 5 (by omega)⟩
/-- Left endpoint `4` of the excluded (non-F) edge. -/
def u4 : Fin k55.size := ⟨4, hlt10 4 (by omega)⟩
/-- Right endpoint `9` of the excluded (non-F) edge. -/
def w9 : Fin k55.size := ⟨9, hlt10 9 (by omega)⟩

/-- Cross pairs are canonical edges of `K_{5,5}`. -/
lemma k55_mem_edgeFinset {a b : Fin k55.size} (ha : a.val < 5) (hb : 5 ≤ b.val) :
    (a, b) ∈ edgeFinset k55 := by
  unfold edgeFinset
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨ha, hb⟩, ?_⟩
  show a.val < b.val
  omega

/-- The designated edge `(0, 5)` as an element of `edgeFinset k55`. -/
lemma mem_e05 : (u0, w5) ∈ edgeFinset k55 :=
  k55_mem_edgeFinset (show (0 : ℕ) < 5 by omega) (show (5 : ℕ) ≤ 5 by omega)

/-- The excluded edge `(4, 9)` as an element of `edgeFinset k55`. -/
lemma mem_e49 : (u4, w9) ∈ edgeFinset k55 :=
  k55_mem_edgeFinset (show (4 : ℕ) < 5 by omega) (show (5 : ℕ) ≤ 9 by omega)

/-- The `L(K_{5,5})²`-vertex of the designated edge `{0, 5}`. -/
noncomputable def i05 : Fin (lineGraphSqFlag k55).size :=
  (edgeFinset k55).equivFin ⟨(u0, w5), mem_e05⟩

/-- The `L(K_{5,5})²`-vertex of the excluded edge `{4, 9}`. -/
noncomputable def i49 : Fin (lineGraphSqFlag k55).size :=
  (edgeFinset k55).equivFin ⟨(u4, w9), mem_e49⟩

/-- The F-set: all 25 edges of `K_{5,5}` except `{4, 9}`. -/
noncomputable def F24 : Finset (Fin (lineGraphSqFlag k55).size) :=
  (Finset.univ : Finset (Fin (lineGraphSqFlag k55).size)).erase i49

/-- The designated vertex is an F-edge. -/
lemma i05_mem_F24 : i05 ∈ F24 := by
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
  intro h
  have h2 := (edgeFinset k55).equivFin.injective h
  simp only [Subtype.mk.injEq, Prod.mk.injEq] at h2
  have h3 := congrArg Fin.val h2.1
  have hu : u0.val = 0 := rfl
  have hu' : u4.val = 4 := rfl
  omega

/-- **The smoke-test item**: `K_{5,5}` with `F = E ∖ {{4,9}}`, designated
vertex `{0,5} ∈ F`. -/
noncomputable def smokeItem : SecFSeqItem := ⟨k55, F24, i05, i05_mem_F24⟩

/-! ## §2. Computable twins of the two hosts -/

/-- Computable `CGraph22` twin of `smokeItem.toColouredGraph22`:
`K_{5,5}`, all vertices colour 0 (black/X — `N(u0) ∪ N(w5)` is everything),
edge colour 1 on every edge except `{4, 9}`. -/
def hostF24CG : CGraph22 10 where
  adj i j := decide ((i.val < 5 ∧ 5 ≤ j.val) ∨ (j.val < 5 ∧ 5 ≤ i.val))
  vertexCol _ := 0
  edgeCol i j :=
    if ((i.val < 5 ∧ 5 ≤ j.val) ∨ (j.val < 5 ∧ 5 ≤ i.val)) ∧
       ¬((i.val = 4 ∧ j.val = 9) ∨ (i.val = 9 ∧ j.val = 4)) then 1 else 0

/-- Computable twin of the `F = ∅` construction (edge colour identically 0). -/
def hostNoFCG : CGraph22 10 where
  adj i j := decide ((i.val < 5 ∧ 5 ≤ j.val) ∨ (j.val < 5 ∧ 5 ≤ i.val))
  vertexCol _ := 0
  edgeCol _ _ := 0

lemma hostF24CG_sym : ∀ i j, hostF24CG.adj i j = hostF24CG.adj j i := by decide
lemma hostF24CG_irrefl : ∀ i, hostF24CG.adj i i = false := by decide
lemma hostNoFCG_sym : ∀ i j, hostNoFCG.adj i j = hostNoFCG.adj j i := by decide
lemma hostNoFCG_irrefl : ∀ i, hostNoFCG.adj i i = false := by decide

/-! ## §3. The construction equals its computable twin -/

/-- `IsFEdge` on the smoke host, characterised arithmetically:
`{a,b}` is a cross pair other than `{4, 9}`. -/
lemma isFEdge_smoke_iff (a b : Fin k55.size) :
    IsFEdge k55 F24 a b ↔
      (((a.val < 5 ∧ 5 ≤ b.val) ∨ (b.val < 5 ∧ 5 ≤ a.val)) ∧
       ¬((a.val = 4 ∧ b.val = 9) ∨ (a.val = 9 ∧ b.val = 4))) := by
  have hu4 : u4.val = 4 := rfl
  have hw9 : w9.val = 9 := rfl
  constructor
  · rintro ⟨i, hi, hc | hc⟩ <;>
      obtain ⟨-, hadj, hlt⟩ :=
        Finset.mem_filter.mp ((edgeFinset k55).equivFin.symm i).property
    · rw [hc] at hadj hlt
      have hlt' : a.val < b.val := hlt
      refine ⟨hadj, ?_⟩
      rintro (⟨h4, h9⟩ | ⟨h4, h9⟩)
      · -- the pair IS `{4,9}`: contradicts `i ≠ i49`
        have hsub : (edgeFinset k55).equivFin.symm i = ⟨(u4, w9), mem_e49⟩ := by
          apply Subtype.ext
          rw [hc]
          show (a, b) = (u4, w9)
          exact Prod.ext (Fin.ext (show a.val = u4.val by omega))
            (Fin.ext (show b.val = w9.val by omega))
        have : i = i49 := by
          have := congrArg (edgeFinset k55).equivFin hsub
          rwa [Equiv.apply_symm_apply] at this
        exact absurd this (Finset.mem_erase.mp hi).1
      · omega
    · rw [hc] at hadj hlt
      have hlt' : b.val < a.val := hlt
      refine ⟨Or.symm hadj, ?_⟩
      rintro (⟨h4, h9⟩ | ⟨h4, h9⟩)
      · omega
      · have hsub : (edgeFinset k55).equivFin.symm i = ⟨(u4, w9), mem_e49⟩ := by
          apply Subtype.ext
          rw [hc]
          show (b, a) = (u4, w9)
          exact Prod.ext (Fin.ext (show b.val = u4.val by omega))
            (Fin.ext (show a.val = w9.val by omega))
        have : i = i49 := by
          have := congrArg (edgeFinset k55).equivFin hsub
          rwa [Equiv.apply_symm_apply] at this
        exact absurd this (Finset.mem_erase.mp hi).1
  · rintro ⟨hadj, hne⟩
    have hADJ : k55.graph.Adj a b := hadj
    have hab : a.val ≠ b.val := by omega
    rcases Nat.lt_or_ge a.val b.val with hlt | hge
    · -- canonical orientation (a, b)
      have hmem : (a, b) ∈ edgeFinset k55 := by
        unfold edgeFinset
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hADJ, hlt⟩
      refine ⟨(edgeFinset k55).equivFin ⟨(a, b), hmem⟩, ?_, Or.inl ?_⟩
      · refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        intro h
        have h2 := (edgeFinset k55).equivFin.injective h
        simp only [Subtype.mk.injEq, Prod.mk.injEq] at h2
        have h3 := congrArg Fin.val h2.1
        have h4 := congrArg Fin.val h2.2
        rw [hu4] at h3
        rw [hw9] at h4
        exact hne (Or.inl ⟨h3, h4⟩)
      · rw [Equiv.symm_apply_apply]
    · -- canonical orientation (b, a)
      have hblt : b.val < a.val := by omega
      have hmem : (b, a) ∈ edgeFinset k55 := by
        unfold edgeFinset
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hADJ.symm, hblt⟩
      refine ⟨(edgeFinset k55).equivFin ⟨(b, a), hmem⟩, ?_, Or.inr ?_⟩
      · refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        intro h
        have h2 := (edgeFinset k55).equivFin.injective h
        simp only [Subtype.mk.injEq, Prod.mk.injEq] at h2
        have h3 := congrArg Fin.val h2.1
        have h4 := congrArg Fin.val h2.2
        rw [hu4] at h3
        rw [hw9] at h4
        exact hne (Or.inr ⟨h4, h3⟩)
      · rw [Equiv.symm_apply_apply]

/-- The item's designated edge is `(0, 5)`. -/
lemma smokeItem_designatedEdge : smokeItem.designatedEdge = (u0, w5) := by
  show ((edgeFinset k55).equivFin.symm
    ((edgeFinset k55).equivFin ⟨(u0, w5), mem_e05⟩)).val = (u0, w5)
  rw [Equiv.symm_apply_apply]

/-- The underlying `SimpleGraph` of `k55` matches the computable host's
`fromRel` adjacency. -/
lemma k55_graph_eq : k55.graph =
    SimpleGraph.fromRel (fun i j : Fin 10 => hostF24CG.adj i j) := by
  ext a b
  simp only [SimpleGraph.fromRel_adj, hostF24CG, decide_eq_true_eq, ne_eq,
    Fin.ext_iff]
  rw [show k55.graph.Adj a b ↔
    ((a.val < 5 ∧ 5 ≤ b.val) ∨ (b.val < 5 ∧ 5 ≤ a.val)) from Iff.rfl]
  omega

/-- **Key equality**: the F-faithful construction on the smoke item IS the
computable twin, as a `GenFlag CG22 ∅`. -/
lemma smoke_flag_eq :
    smokeItem.toGenFlag = hostF24CG.toGenFlag := by
  have hcg : smokeItem.toColouredGraph22 =
      colouredGraph22OfEdgeF k55 F24 u0 w5 := by
    unfold SecFSeqItem.toColouredGraph22
    rw [smokeItem_designatedEdge]
    exact rfl
  unfold SecFSeqItem.toGenFlag
  rw [hcg]
  refine GenFlag.empty_ext _ _ rfl (CG22_str_ext ?_ ?_ ?_)
  · -- graph component
    exact k55_graph_eq
  · -- vertex colours: N(0) ∪ N(5) is everything, so identically 0
    funext x
    show (if k55.graph.Adj u0 x ∨ k55.graph.Adj w5 x then (0 : Fin 2) else 1) = 0
    refine if_pos ?_
    rcases Nat.lt_or_ge x.val 5 with h | h
    · exact Or.inr (Or.inr ⟨h, show (5 : ℕ) ≤ 5 by omega⟩)
    · exact Or.inl (Or.inl ⟨show (0 : ℕ) < 5 by omega, h⟩)
  · -- edge colours: F-edges ↔ the computable condition
    funext a b
    show (if IsFEdge k55 F24 a b then (1 : Fin 2) else 0) = hostF24CG.edgeCol a b
    by_cases h : (((a.val < 5 ∧ 5 ≤ b.val) ∨ (b.val < 5 ∧ 5 ≤ a.val)) ∧
       ¬((a.val = 4 ∧ b.val = 9) ∨ (a.val = 9 ∧ b.val = 4)))
    · rw [if_pos ((isFEdge_smoke_iff a b).mpr h)]
      show (1 : Fin 2) =
        if (((a.val < 5 ∧ 5 ≤ b.val) ∨ (b.val < 5 ∧ 5 ≤ a.val)) ∧
          ¬((a.val = 4 ∧ b.val = 9) ∨ (a.val = 9 ∧ b.val = 4))) then 1 else 0
      rw [if_pos h]
    · rw [if_neg (fun hf => h ((isFEdge_smoke_iff a b).mp hf))]
      show (0 : Fin 2) =
        if (((a.val < 5 ∧ 5 ≤ b.val) ∨ (b.val < 5 ∧ 5 ≤ a.val)) ∧
          ¬((a.val = 4 ∧ b.val = 9) ∨ (a.val = 9 ∧ b.val = 4))) then 1 else 0
      rw [if_neg h]

/-- The `.forget` variant (the shape the axioms' RHS uses). -/
lemma smoke_flag_forget_eq :
    smokeItem.toGenFlag.forget = hostF24CG.toGenFlag := by
  have h1 : smokeItem.toGenFlag.forget = smokeItem.toGenFlag :=
    GenFlag.empty_ext _ _ rfl rfl
  rw [h1, smoke_flag_eq]

/-- The `F = ∅` construction equals the no-F computable twin. -/
lemma smoke_noF_flag_eq :
    (colouredGraph22OfEdgeF k55 ∅ u0 w5).toGenFlag = hostNoFCG.toGenFlag := by
  refine GenFlag.empty_ext _ _ rfl (CG22_str_ext ?_ ?_ ?_)
  · exact k55_graph_eq
  · funext x
    show (if k55.graph.Adj u0 x ∨ k55.graph.Adj w5 x then (0 : Fin 2) else 1) = 0
    refine if_pos ?_
    rcases Nat.lt_or_ge x.val 5 with h | h
    · exact Or.inr (Or.inr ⟨h, show (5 : ℕ) ≤ 5 by omega⟩)
    · exact Or.inl (Or.inl ⟨show (0 : ℕ) < 5 by omega, h⟩)
  · funext a b
    show (if IsFEdge k55 (∅ : Finset (Fin (lineGraphSqFlag k55).size)) a b
      then (1 : Fin 2) else 0) = 0
    refine if_neg ?_
    rintro ⟨i, hi, -⟩
    exact absurd hi (Finset.notMem_empty i)

/-! ## §4. Nonzero induced counts on three objective-support flags -/

/-- Transfer: positivity of the computable count gives positivity of the
abstract `genInducedCount` on the construction's flag. -/
lemma count_pos_of_c22 (j : Fin secBasisSize)
    (hFs : ∀ a b, (flagBasisCGraph22 j).adj a b = (flagBasisCGraph22 j).adj b a)
    (hFi : ∀ a, (flagBasisCGraph22 j).adj a a = false)
    (hc : 0 < c22InducedCount (flagBasisCGraph22 j) hostF24CG) :
    0 < genInducedCount CG22 (GenFlagType.empty CG22)
      (SecBasis.flagBasis_sec j) smokeItem.toGenFlag.forget := by
  rw [smoke_flag_forget_eq,
    show SecBasis.flagBasis_sec j = (flagBasisCGraph22 j).toGenFlag from rfl,
    ← c22InducedCount_eq_genInducedCount' _ _ hFs hFi hostF24CG_sym
      hostF24CG_irrefl]
  exact hc

/-- Transfer for the `F = ∅` zero counts. -/
lemma count_zero_of_c22 (j : Fin secBasisSize)
    (hFs : ∀ a b, (flagBasisCGraph22 j).adj a b = (flagBasisCGraph22 j).adj b a)
    (hFi : ∀ a, (flagBasisCGraph22 j).adj a a = false)
    (hc : c22InducedCount (flagBasisCGraph22 j) hostNoFCG = 0) :
    genInducedCount CG22 (GenFlagType.empty CG22)
      (SecBasis.flagBasis_sec j)
      (colouredGraph22OfEdgeF k55 ∅ u0 w5).toGenFlag = 0 := by
  rw [smoke_noF_flag_eq,
    show SecBasis.flagBasis_sec j = (flagBasisCGraph22 j).toGenFlag from rfl,
    ← c22InducedCount_eq_genInducedCount' _ _ hFs hFi hostNoFCG_sym
      hostNoFCG_irrefl]
  exact hc

/-- Support flag 1714 (`K_{2,3}`, all-X, all-F; target −2·10¹¹): nonzero count. -/
theorem smoke_count_1714_pos :
    0 < genInducedCount CG22 (GenFlagType.empty CG22)
      (SecBasis.flagBasis_sec ⟨1714, by decide⟩) smokeItem.toGenFlag.forget :=
  count_pos_of_c22 _ (by native_decide) (by native_decide) (by native_decide)

/-- Support flag 7784 (`K_{2,3}`, all-X, 5 F + 1 non-F; target −1.3̄·10¹¹):
nonzero count. -/
theorem smoke_count_7784_pos :
    0 < genInducedCount CG22 (GenFlagType.empty CG22)
      (SecBasis.flagBasis_sec ⟨7784, by decide⟩) smokeItem.toGenFlag.forget :=
  count_pos_of_c22 _ (by native_decide) (by native_decide) (by native_decide)

/-- Support flag 8559 (`K_{1,4}`, all-X, all-F; target −10¹¹): nonzero count. -/
theorem smoke_count_8559_pos :
    0 < genInducedCount CG22 (GenFlagType.empty CG22)
      (SecBasis.flagBasis_sec ⟨8559, by decide⟩) smokeItem.toGenFlag.forget :=
  count_pos_of_c22 _ (by native_decide) (by native_decide) (by native_decide)

/-- These three flags are in the cert objective support (`targetArr ≠ 0`,
hence `O_sec_coef ≠ 0`). -/
theorem smoke_flags_in_support :
    targetArr[(1714 : ℕ)]! ≠ 0 ∧ targetArr[(7784 : ℕ)]! ≠ 0 ∧
      targetArr[(8559 : ℕ)]! ≠ 0 := by
  native_decide

/-! ## §5. Nonzero densities (gate L1(b) proper) -/

/-- `Δ ≥ 5` on the smoke host (vertex 0 has the full right side as
neighbours), so the `C(Δ, 5)` density denominator is positive. -/
lemma five_le_delta :
    5 ≤ secGenDelta smokeItem.toGenFlag.forget.forget := by
  have h5 : (5 : ℕ) < k55.size := hlt10 5 (by omega)
  have hIci : (Finset.univ.filter (k55.graph.Adj u0)) =
      Finset.Ici (⟨5, h5⟩ : Fin k55.size) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici,
      Fin.le_def]
    rw [show k55.graph.Adj u0 x ↔
      ((u0.val < 5 ∧ 5 ≤ x.val) ∨ (x.val < 5 ∧ 5 ≤ u0.val)) from Iff.rfl]
    have hu : u0.val = 0 := rfl
    omega
  have hdeg : 5 ≤ (Finset.univ.filter (k55.graph.Adj u0)).card := by
    rw [hIci, Fin.card_Ici]
    show 5 ≤ 10 - 5
    omega
  exact le_trans hdeg (Finset.le_sup
    (f := fun v => (Finset.univ.filter (k55.graph.Adj v)).card)
    (Finset.mem_univ u0))

/-- Count positivity lifts to density positivity (the `C(Δ,5)·Aut`
denominator is positive on this host — unlike `K_{3,3}`, where `C(3,5) = 0`). -/
lemma density_pos_of_count (j : Fin secBasisSize)
    (hc : 0 < genInducedCount CG22 (GenFlagType.empty CG22)
      (SecBasis.flagBasis_sec j) smokeItem.toGenFlag.forget) :
    0 < genUnlabelledDensity CG22 (GenFlagType.empty CG22)
      (SecBasis.flagBasis_sec j) smokeItem.toGenFlag.forget secGenDelta := by
  unfold genUnlabelledDensity
  apply _root_.div_pos
  · exact_mod_cast hc
  · apply mul_pos
    · have hpos : 0 < Nat.choose (secGenDelta smokeItem.toGenFlag.forget.forget)
          ((SecBasis.flagBasis_sec j).size - (GenFlagType.empty CG22).size) :=
        Nat.choose_pos five_le_delta
      exact_mod_cast hpos
    · exact_mod_cast genFlagAutCount_pos (GenFlagType.empty CG22)
        (SecBasis.flagBasis_sec j)

/-- **Gate L1(b), flag 1714**: nonzero density on an objective-support flag. -/
theorem smoke_density_1714_pos :
    0 < genUnlabelledDensity CG22 (GenFlagType.empty CG22)
      (SecBasis.flagBasis_sec ⟨1714, by decide⟩)
      smokeItem.toGenFlag.forget secGenDelta :=
  density_pos_of_count _ smoke_count_1714_pos

/-- **Gate L1(b), flag 7784**. -/
theorem smoke_density_7784_pos :
    0 < genUnlabelledDensity CG22 (GenFlagType.empty CG22)
      (SecBasis.flagBasis_sec ⟨7784, by decide⟩)
      smokeItem.toGenFlag.forget secGenDelta :=
  density_pos_of_count _ smoke_count_7784_pos

/-- **Gate L1(b), flag 8559**. -/
theorem smoke_density_8559_pos :
    0 < genUnlabelledDensity CG22 (GenFlagType.empty CG22)
      (SecBasis.flagBasis_sec ⟨8559, by decide⟩)
      smokeItem.toGenFlag.forget secGenDelta :=
  density_pos_of_count _ smoke_count_8559_pos

/-! ## §6. Consistency with L0: `F = ∅` kills the same three flags -/

/-- With `F = ∅` the same host graph gives count 0 on flag 1714. -/
theorem smoke_noF_count_1714_zero :
    genInducedCount CG22 (GenFlagType.empty CG22)
      (SecBasis.flagBasis_sec ⟨1714, by decide⟩)
      (colouredGraph22OfEdgeF k55 ∅ u0 w5).toGenFlag = 0 :=
  count_zero_of_c22 _ (by native_decide) (by native_decide) (by native_decide)

/-- With `F = ∅`: count 0 on flag 7784. -/
theorem smoke_noF_count_7784_zero :
    genInducedCount CG22 (GenFlagType.empty CG22)
      (SecBasis.flagBasis_sec ⟨7784, by decide⟩)
      (colouredGraph22OfEdgeF k55 ∅ u0 w5).toGenFlag = 0 :=
  count_zero_of_c22 _ (by native_decide) (by native_decide) (by native_decide)

/-- With `F = ∅`: count 0 on flag 8559. -/
theorem smoke_noF_count_8559_zero :
    genInducedCount CG22 (GenFlagType.empty CG22)
      (SecBasis.flagBasis_sec ⟨8559, by decide⟩)
      (colouredGraph22OfEdgeF k55 ∅ u0 w5).toGenFlag = 0 :=
  count_zero_of_c22 _ (by native_decide) (by native_decide) (by native_decide)

/-! ## §7. Class membership (gate L1(d) dry-run) -/

/-- The smoke item lies in the new F-faithful class. -/
example : SecBridge.secGenGraphClassF smokeItem.toGenFlag.forget :=
  smokeItem.toGenFlag_mem_classF

end SecSmokeL1

end

end Davey2024

-- Axiom hygiene: the smoke theorems must use only standard axioms
-- (native_decide adds Lean.ofReduceBool / Lean.trustCompiler) — in
-- particular NO dependence on the (false) SEC identity axioms.
#print axioms Davey2024.SecSmokeL1.smoke_density_1714_pos
#print axioms Davey2024.SecSmokeL1.smoke_density_7784_pos
#print axioms Davey2024.SecSmokeL1.smoke_density_8559_pos
#print axioms Davey2024.SecSmokeL1.smoke_noF_count_1714_zero
