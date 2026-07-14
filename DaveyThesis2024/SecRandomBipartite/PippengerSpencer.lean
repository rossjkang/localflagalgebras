/-
Copyright (c) 2026 Ross Kang.
Released under Apache 2.0 license.

# Wake PS — Pippenger-Spencer + Kim-Vu axioms

This file collects two cited, well-known extremal-combinatorics theorems as
named axioms, supporting the F.7 Pippenger-Spencer plan
(the development notes).

The intent is to **isolate the math gap** of `perPairCover_fks_aas_axiom`
(project-specific FKS-shape assertion) into two famous theorems with crisp
literature citations. Both axioms have 3-section docstrings
(Statement / Why needed / Why correct) per the project pattern.

## Status

* PS.1 (this commit): `pippenger_spencer_covering` (Kahn 1996 / Pippenger-Spencer 1989).
* PS.2 (next commit): `kim_vu_concentration_for_edge_polynomials` (Kim-Vu 2000).
* PS.3-PS.8 (future): construction of `H_k`, expectation computations, concentration
  applications, hypothesis verification, derivation of FKS-shape SCI bound.

The end state replaces `perPairCover_fks_aas_axiom` with a theorem proved from these
two axioms plus bipartite-specific computations.
-/

import DaveyThesis2024.BipartiteRandomGraph
import DaveyThesis2024.SecRandomBipartite.PairPacking
import DaveyThesis2024.SecRandomBipartite.PairPackingConcentration
import DaveyThesis2024.SecRandomBipartite.SlotConcentration
import DaveyThesis2024.SecRandomBipartite.KimVuDischarge
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace DaveyThesis2024.SecRandomBipartite.PippengerSpencer

open MeasureTheory

/-! ## PS.1: Pippenger-Spencer / Kahn covering theorem -/

/-- **Pippenger–Spencer covering — verbatim restatement** (survey Thm 2.2 / 2.3, the
almost-regular nibble form). For every uniformity `k` and target leftover fraction `ε > 0`,
there exist a codegree-slack `δ > 0` and a degree threshold `D₀` such that: any `k`-uniform
hypergraph that is `(1±δ)`-degree-regular with codegree `≤ δ·D` and `D ≥ D₀` has a matching
(pairwise-disjoint hyperedges) covering all but at most `⌈ε·n⌉` vertices.

This replaces the previous `pippenger_spencer_covering`, which conflated the codegree slack and
the leftover fraction into a single `ε` and dropped the `D → ∞` (D ≥ D₀) requirement — i.e. it
was **too strong** (not a verbatim corollary). The decoupled `δ` (chosen after `ε`) and the
`D₀` threshold are exactly Pippenger–Spencer's quantification: `∀ k ε, ∃ δ`.

**Citation.** Pippenger, N., and Spencer, J. "Asymptotic behavior of the chromatic index for
hypergraphs." *J. Combin. Theory Ser. A* 51 (1989), 24–42 (almost-regular nibble form); cf.
the survey arXiv:2106.13733, Theorems 2.2/2.3. Cited as an axiom (Mathlib has no nibble
infrastructure). -/
axiom pippenger_spencer_covering_verbatim
    (k : ℕ) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ D₀ : ℝ,
    ∀ {α : Type*} [Fintype α] [DecidableEq α]
      (V : Finset α)
      (H : Finset (Finset α))
      (_h_sub : ∀ S ∈ H, S ⊆ V)
      (_h_uniform : ∀ S ∈ H, S.card = k)
      (D : ℝ) (_h_D_ge : D₀ ≤ D)
      (_h_D_regular : ∀ v ∈ V, |((H.filter (fun S => v ∈ S)).card : ℝ) - D| ≤ δ * D)
      (_h_codegree : ∀ u ∈ V, ∀ v ∈ V, u ≠ v →
        ((H.filter (fun S => u ∈ S ∧ v ∈ S)).card : ℝ) ≤ δ * D),
      ∃ cover : Finset (Finset α),
        cover ⊆ H ∧
        (cover : Set (Finset α)).PairwiseDisjoint id ∧
        (V \ cover.biUnion id).card ≤ ⌈ε * (V.card : ℝ)⌉₊

/-! ## PS.3: SCI hypergraph H_k construction

The Pippenger-Spencer axiom (PS.1) takes a hypergraph `H : Finset (Finset α)` on a
finite vertex set `α`. The SCI application uses `α = Fin n_A × Fin n_B` (cross-pair
indices, i.e. potential bipartite edges) with hyperedges given by induced bipartite
matchings of size `k`. PS.3 constructs this hypergraph and proves basic membership /
uniformity / subset lemmas; PS.4 will compute its expected per-vertex degree `D(e)`
and codegree `C(e_1, e_2)`. -/

/-- The Finset of size-`k` induced bipartite matchings of `G[S, T_set]`.

A member `M` is a set of `k` cross-block pairs lying in
`crossBlockPairs G S T_set` such that the pairs form a bipartite *induced*
matching (vertex-disjoint with no bridging `G`-edges). -/
noncomputable def inducedKMatchings
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B))
    (k : ℕ) :
    Finset (Finset (Fin n_A × Fin n_B)) :=
  letI : DecidablePred (fun M : Finset (Fin n_A × Fin n_B) =>
      DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G M) :=
    fun _ => Classical.propDecidable _
  ((DaveyThesis2024.SecRandomBipartite.crossBlockPairs G S T_set).powersetCard k).filter
    (fun M => DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G M)

/-- Membership characterisation for `inducedKMatchings`: `M ∈ inducedKMatchings G S T_set k`
iff `M` is a subset of `crossBlockPairs G S T_set` of cardinality `k` that is an
induced bipartite matching. -/
lemma mem_inducedKMatchings_iff
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B)) (k : ℕ)
    (M : Finset (Fin n_A × Fin n_B)) :
    M ∈ inducedKMatchings G S T_set k ↔
      M ⊆ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G S T_set ∧
      M.card = k ∧
      DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G M := by
  letI : DecidablePred (fun M : Finset (Fin n_A × Fin n_B) =>
      DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G M) :=
    fun _ => Classical.propDecidable _
  unfold inducedKMatchings
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  tauto

/-! ## PS.3.2: SCI hypergraph alias -/

/-- The SCI hypergraph `H_k` for bipartite `G[S, T_set]`.

* **Vertex type**: `Fin n_A × Fin n_B` (cross-pair indices, i.e. potential bipartite
  edges between `S` and `T_set`).
* **Hyperedges**: size-`k` induced bipartite matchings.

This is the hypergraph whose chromatic number bounds `χ'_s(G[S, T_set])`: a proper
hyperedge colouring assigns disjoint induced matchings to colour classes, and the
Pippenger-Spencer covering theorem (PS.1) provides such a colouring once we verify
the regularity + codegree hypotheses (PS.6, via Kim-Vu in PS.5).

This is a simple alias of `inducedKMatchings`; the rename improves readability at
PS.4+ call sites where `SCIHypergraph_k` is the conceptual object. -/
noncomputable def SCIHypergraph_k
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B))
    (k : ℕ) :
    Finset (Finset (Fin n_A × Fin n_B)) :=
  inducedKMatchings G S T_set k

/-! ## PS.3.3: Uniformity and subset lemmas -/

/-- `SCIHypergraph_k` is `k`-uniform: every hyperedge has cardinality exactly `k`. -/
lemma SCIHypergraph_k_uniform
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B)) (k : ℕ)
    (M : Finset (Fin n_A × Fin n_B)) (h_mem : M ∈ SCIHypergraph_k G S T_set k) :
    M.card = k := by
  rw [SCIHypergraph_k] at h_mem
  exact ((mem_inducedKMatchings_iff G S T_set k M).mp h_mem).2.1

/-- Every hyperedge of `SCIHypergraph_k` is a subset of `crossBlockPairs G S T_set`. -/
lemma SCIHypergraph_k_subset_cross
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B)) (k : ℕ)
    (M : Finset (Fin n_A × Fin n_B)) (h_mem : M ∈ SCIHypergraph_k G S T_set k) :
    M ⊆ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G S T_set := by
  rw [SCIHypergraph_k] at h_mem
  exact ((mem_inducedKMatchings_iff G S T_set k M).mp h_mem).1

/-- Every hyperedge of `SCIHypergraph_k` is an induced bipartite matching of `G`. -/
lemma SCIHypergraph_k_isInducedMatching
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B)) (k : ℕ)
    (M : Finset (Fin n_A × Fin n_B)) (h_mem : M ∈ SCIHypergraph_k G S T_set k) :
    DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G M := by
  rw [SCIHypergraph_k] at h_mem
  exact ((mem_inducedKMatchings_iff G S T_set k M).mp h_mem).2.2

/-! ## PS.4: D(e) and codegree C(e_1, e_2) expectation formulas

This section computes the expected per-vertex degree `D(e)` and codegree
`C(e_1, e_2)` of the SCI hypergraph `H_k = SCIHypergraph_k G univ univ k` under
the random bipartite graph `G ~ G(n_A, n_B, p)`.

The math content (from the development notes
§3.4-3.5):

* **D(e) formula** (conditional on `e = (a,b) ∈ E(G)`):
  `E[D(e) | e ∈ E(G)] = C(n_A - 1, k - 1) · C(n_B - 1, k - 1) · (k - 1)! · p^{k-1} · (1-p)^{k(k-1)}`

  Derivation: choose `k - 1` additional A-vertices, `k - 1` additional B-vertices,
  match them (`(k - 1)!` ways), and require `k - 1` matching edges present
  (`p^{k-1}`) plus all `k(k-1)` cross-edges absent (`(1-p)^{k(k-1)}`).

* **Codegree case analysis**: for distinct edges `e_1 ≠ e_2`,
  * (i) `a_1 = a_2` or `b_1 = b_2` (share a vertex): `C(e_1, e_2) = 0`.
  * (ii) Distinct rows + distinct cols, but a bridging cross-edge present in `G`:
        `C(e_1, e_2) = 0` (matching is not induced).
  * (iii) Distinct rows, distinct cols, no bridging edges:
        `E[C(e_1, e_2) | good case] = C(n_A - 2, k - 2) · C(n_B - 2, k - 2)`
                                     `· (k - 2)! · p^{k-2} · (1-p)^{k(k-1) - 4}`.

* **Ratio bound**: `C(e_1, e_2) / D(e_1) = O(k / (n_A · n_B · p))`, which `→ 0` as
  `n^* → ∞` with `k = O(log n^*)` and `p` constant. -/

/-! ### Expected-value formulas as definitions -/

/-- The expected per-edge degree formula:
`E[D(e) | e ∈ E(G)] = C(n_A - 1, k - 1) · C(n_B - 1, k - 1)`
                    `· (k - 1)! · p^{k-1} · (1-p)^{k(k-1)}`. -/
noncomputable def expectedDegreeFormula
    (n_A n_B k : ℕ) (p : ℝ) : ℝ :=
  (Nat.choose (n_A - 1) (k - 1) : ℝ) * (Nat.choose (n_B - 1) (k - 1) : ℝ)
    * (Nat.factorial (k - 1) : ℝ) * p ^ (k - 1) * (1 - p) ^ (k * (k - 1))

/-- The expected codegree formula for the "good" case (distinct rows, distinct cols,
no bridging cross-edges): `E[C(e_1, e_2) | good case] = C(n_A - 2, k - 2) · C(n_B - 2, k - 2) ·
(k - 2)! · p^{k-2} · (1-p)^{k(k-1) - 4}`. -/
noncomputable def expectedCodegreeFormula
    (n_A n_B k : ℕ) (p : ℝ) : ℝ :=
  (Nat.choose (n_A - 2) (k - 2) : ℝ) * (Nat.choose (n_B - 2) (k - 2) : ℝ)
    * (Nat.factorial (k - 2) : ℝ) * p ^ (k - 2) * (1 - p) ^ (k * (k - 1) - 4)

/-- Both formulas are non-negative for `p ∈ [0, 1]`. -/
lemma expectedDegreeFormula_nonneg
    (n_A n_B k : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp_le : p ≤ 1) :
    0 ≤ expectedDegreeFormula n_A n_B k p := by
  unfold expectedDegreeFormula
  have h1 : (0 : ℝ) ≤ Nat.choose (n_A - 1) (k - 1) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ Nat.choose (n_B - 1) (k - 1) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ Nat.factorial (k - 1) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ p ^ (k - 1) := pow_nonneg hp _
  have h5 : (0 : ℝ) ≤ (1 - p) ^ (k * (k - 1)) := pow_nonneg (by linarith) _
  positivity

lemma expectedCodegreeFormula_nonneg
    (n_A n_B k : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp_le : p ≤ 1) :
    0 ≤ expectedCodegreeFormula n_A n_B k p := by
  unfold expectedCodegreeFormula
  have h1 : (0 : ℝ) ≤ Nat.choose (n_A - 2) (k - 2) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ Nat.choose (n_B - 2) (k - 2) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ Nat.factorial (k - 2) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ p ^ (k - 2) := pow_nonneg hp _
  have h5 : (0 : ℝ) ≤ (1 - p) ^ (k * (k - 1) - 4) := pow_nonneg (by linarith) _
  positivity

/-! ### Step 2 (structural): codegree-zero case analysis

When two edges `e_1 = (a_1, b_1)` and `e_2 = (a_2, b_2)` share a vertex
(`a_1 = a_2` or `b_1 = b_2`), they cannot both appear in any induced matching.
This is a *deterministic* statement, holding for every graph `G`.

The third codegree-zero case — "distinct rows + cols but a bridging cross-edge
is present in `G`" — is also handled at the deterministic level: any matching
containing both `e_1` and `e_2` would fail the induced condition. -/

/-- **Codegree-zero case (i): shared A-vertex.** If `e_1 = (a, b_1)` and
`e_2 = (a, b_2)` share the same A-vertex, then no induced bipartite matching
contains both. Consequently the codegree is `0` for any graph `G`. -/
lemma codegree_zero_shared_A
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B)) (k : ℕ)
    (a : Fin n_A) (b_1 b_2 : Fin n_B) (h_distinct : b_1 ≠ b_2) :
    ((inducedKMatchings G S T_set k).filter
        (fun M => (a, b_1) ∈ M ∧ (a, b_2) ∈ M)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro M h_mem ⟨h_e1, h_e2⟩
  have h_match : DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G M :=
    ((mem_inducedKMatchings_iff G S T_set k M).mp h_mem).2.2
  have h_ne : (a, b_1) ≠ (a, b_2) := by
    intro h; exact h_distinct (by simpa using h)
  have h_neA : (a, b_1).1 ≠ (a, b_2).1 := (h_match (a, b_1) h_e1 (a, b_2) h_e2 h_ne).1
  exact h_neA rfl

/-- **Codegree-zero case (ii): shared B-vertex.** Symmetric to case (i). -/
lemma codegree_zero_shared_B
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B)) (k : ℕ)
    (a_1 a_2 : Fin n_A) (b : Fin n_B) (h_distinct : a_1 ≠ a_2) :
    ((inducedKMatchings G S T_set k).filter
        (fun M => (a_1, b) ∈ M ∧ (a_2, b) ∈ M)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro M h_mem ⟨h_e1, h_e2⟩
  have h_match : DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G M :=
    ((mem_inducedKMatchings_iff G S T_set k M).mp h_mem).2.2
  have h_ne : (a_1, b) ≠ (a_2, b) := by
    intro h; exact h_distinct (by simpa using h)
  have h_neB : (a_1, b).2 ≠ (a_2, b).2 := (h_match (a_1, b) h_e1 (a_2, b) h_e2 h_ne).2.1
  exact h_neB rfl

/-- **Codegree-zero case (iii): bridging cross-edge present.** Distinct A-vertices
`a_1 ≠ a_2` and distinct B-vertices `b_1 ≠ b_2`, but the bridging edge
`(a_1, b_2)` is present in `G`. Then no induced bipartite matching contains both
edges (the induced condition would require `(a_1, b_2)` absent). -/
lemma codegree_zero_bridge_a1b2
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B)) (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_distinct_A : a_1 ≠ a_2) (_h_distinct_B : b_1 ≠ b_2)
    (h_bridge : G.Adj (Sum.inl a_1) (Sum.inr b_2)) :
    ((inducedKMatchings G S T_set k).filter
        (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro M h_mem ⟨h_e1, h_e2⟩
  have h_match : DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G M :=
    ((mem_inducedKMatchings_iff G S T_set k M).mp h_mem).2.2
  have h_ne : (a_1, b_1) ≠ (a_2, b_2) := by
    intro h
    have : a_1 = a_2 := by simpa using congrArg Prod.fst h
    exact h_distinct_A this
  -- The induced condition forces `(a_1, b_2)` to be absent in `G`.
  have h_no_bridge : ¬ G.Adj (Sum.inl (a_1, b_1).1) (Sum.inr (a_2, b_2).2) :=
    (h_match (a_1, b_1) h_e1 (a_2, b_2) h_e2 h_ne).2.2.1
  exact h_no_bridge h_bridge

/-- **Codegree-zero case (iii'): bridging cross-edge `(a_2, b_1)` present.** -/
lemma codegree_zero_bridge_a2b1
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B)) (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_distinct_A : a_1 ≠ a_2) (_h_distinct_B : b_1 ≠ b_2)
    (h_bridge : G.Adj (Sum.inl a_2) (Sum.inr b_1)) :
    ((inducedKMatchings G S T_set k).filter
        (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro M h_mem ⟨h_e1, h_e2⟩
  have h_match : DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G M :=
    ((mem_inducedKMatchings_iff G S T_set k M).mp h_mem).2.2
  have h_ne : (a_1, b_1) ≠ (a_2, b_2) := by
    intro h
    have : a_1 = a_2 := by simpa using congrArg Prod.fst h
    exact h_distinct_A this
  have h_no_bridge : ¬ G.Adj (Sum.inl (a_2, b_2).1) (Sum.inr (a_1, b_1).2) :=
    (h_match (a_1, b_1) h_e1 (a_2, b_2) h_e2 h_ne).2.2.2
  exact h_no_bridge h_bridge

/-! ### Step 3: Pascal-style choose ratio infrastructure (algebraic)

The asymptotic ratio `C / D = O(k / (n_A · n_B · p))` from investigation §3.5
follows from the elementary Pascal identity

  `(k - 1) · C(n - 1, k - 1) = (n - 1) · C(n - 2, k - 2)`  (for `k ≥ 2`, `n ≥ k`)

applied to both `n = n_A` and `n = n_B`, combined with the factorial split
`(k - 1)! = (k - 1) · (k - 2)!` (for `k ≥ 2`) and the power splits
`p^{k-1} = p^{k-2} · p` (for `k ≥ 2`) and
`(1 - p)^{k(k-1)} = (1 - p)^{k(k-1) - 4} · (1 - p)^4` (for `k ≥ 3`).

We record the algebraic infrastructure here. PS.5 will combine these with the
integral identity to obtain the full `C / D` asymptotic bound. -/

/-- **Pascal identity (used for the C/D ratio).** For `k ≥ 2` and `n ≥ k`,
`(k - 1) · C(n - 1, k - 1) = (n - 1) · C(n - 2, k - 2)`. -/
lemma choose_pascal_pred
    (n k : ℕ) (hk2 : 2 ≤ k) (h_kn : k ≤ n) :
    (k - 1) * Nat.choose (n - 1) (k - 1) = (n - 1) * Nat.choose (n - 2) (k - 2) := by
  -- Standard identity Nat.succ_mul_choose_eq:
  --   (n + 1) * C n k = C (n + 1) (k + 1) * (k + 1)
  -- with n := n - 2, k := k - 2 gives:
  --   (n - 1) * C (n - 2) (k - 2) = C (n - 1) (k - 1) * (k - 1)
  have h_eq := Nat.add_one_mul_choose_eq (n - 2) (k - 2)
  -- h_eq : (n - 2 + 1) * (n - 2).choose (k - 2) = ... * (k - 2 + 1)
  have hn1 : n - 2 + 1 = n - 1 := by omega
  have hk1 : k - 2 + 1 = k - 1 := by omega
  rw [hn1, hk1] at h_eq
  linarith [h_eq]

/-- **Cast version** of `choose_pascal_pred` to `ℝ`. -/
lemma choose_pascal_pred_real
    (n k : ℕ) (hk2 : 2 ≤ k) (h_kn : k ≤ n) :
    ((k - 1 : ℕ) : ℝ) * (Nat.choose (n - 1) (k - 1) : ℝ)
      = ((n - 1 : ℕ) : ℝ) * (Nat.choose (n - 2) (k - 2) : ℝ) := by
  exact_mod_cast choose_pascal_pred n k hk2 h_kn

/-- **Factorial step**: `(k - 1)! = (k - 1) · (k - 2)!` for `k ≥ 2`. -/
lemma factorial_pred_eq
    (k : ℕ) (hk2 : 2 ≤ k) :
    (Nat.factorial (k - 1) : ℝ) = ((k - 1 : ℕ) : ℝ) * Nat.factorial (k - 2) := by
  have h_eq : Nat.factorial (k - 1) = (k - 1) * Nat.factorial (k - 2) := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, Nat.factorial_succ]
  exact_mod_cast h_eq

/-- **`p`-power step**: `p^{k - 1} = p^{k - 2} · p` for `k ≥ 2`. -/
lemma pow_p_kmin1_split
    (k : ℕ) (hk2 : 2 ≤ k) (p : ℝ) :
    p ^ (k - 1) = p ^ (k - 2) * p := by
  have : k - 1 = k - 2 + 1 := by omega
  rw [this, pow_succ]

/-- **Codegree exponent reduction**:
`(1 - p)^{k(k-1)} = (1 - p)^{k(k-1) - 4} · (1 - p)^4` for `k ≥ 3`. -/
lemma pow_one_sub_p_kmin1_split
    (k : ℕ) (hk3 : 3 ≤ k) (p : ℝ) :
    (1 - p) ^ (k * (k - 1)) = (1 - p) ^ (k * (k - 1) - 4) * (1 - p) ^ 4 := by
  rw [← pow_add]
  congr 1
  -- k ≥ 3, so k - 1 ≥ 2, and k * (k - 1) ≥ 6 ≥ 4.
  have h6 : 6 ≤ k * (k - 1) := by
    have h1 : 3 ≤ k := hk3
    have h2 : 2 ≤ k - 1 := by omega
    calc 6 = 3 * 2 := by ring
      _ ≤ k * (k - 1) := Nat.mul_le_mul h1 h2
  omega

/-! ### Investigation §3.5 ratio decomposition

Combining the four building blocks above, the ratio `C / D` equals an explicit
polynomial expression in `(k - 1), (n_A - 1), (n_B - 1), p, (1 - p)`. We record
the cleared-denominators identity below. -/

/-- **Ratio identity (Investigation §3.5).** For `k ≥ 3`, `n_A ≥ k`, `n_B ≥ k`:

  `(k - 1) · D = (n_A - 1) · (n_B - 1) · p · (1 - p)^4 · C`

where `D = expectedDegreeFormula`, `C = expectedCodegreeFormula`. Dividing by
`D · (n_A - 1) · (n_B - 1) · p · (1 - p)^4` recovers
`C / D = (k - 1) / ((n_A - 1) · (n_B - 1) · p · (1 - p)^4)`, which for constant
`p, 1 - p` and `k = O(log n^*)` is `O(k / (n_A · n_B))` ≃ `0`.

The proof uses both Pascal identities (`choose_pascal_pred`), factorial split,
and the two power splits — combined via `linear_combination`. -/
lemma ratio_identity
    (n_A n_B k : ℕ) (p : ℝ)
    (hk3 : 3 ≤ k) (h_kA : k ≤ n_A) (h_kB : k ≤ n_B) :
    ((k - 1 : ℕ) : ℝ) * expectedDegreeFormula n_A n_B k p
    = ((n_A - 1 : ℕ) : ℝ) * ((n_B - 1 : ℕ) : ℝ) * p * (1 - p) ^ 4
        * expectedCodegreeFormula n_A n_B k p := by
  unfold expectedDegreeFormula expectedCodegreeFormula
  have hA := choose_pascal_pred_real n_A k (by omega) h_kA
  have hB := choose_pascal_pred_real n_B k (by omega) h_kB
  have h_fact := factorial_pred_eq k (by omega)
  have h_pow_p := pow_p_kmin1_split k (by omega) p
  have h_pow_1mp := pow_one_sub_p_kmin1_split k hk3 p
  -- Rewrite LHS factorial / powers in terms of (k - 2)-flavoured factors,
  -- so that Pascal substitutions can equate the choose products.
  rw [h_pow_p, h_pow_1mp, h_fact]
  -- After rewrites:
  -- LHS = (k-1) * [C(n_A-1, k-1) * C(n_B-1, k-1) * ((k-1) * (k-2)!)
  --                * (p^(k-2) * p) * ((1-p)^(k(k-1)-4) * (1-p)^4)]
  --     = (k-1)^2 * C(n_A-1) * C(n_B-1) * (k-2)! * p^(k-1) * (1-p)^(k(k-1))
  -- RHS = (n_A-1) * (n_B-1) * p * (1-p)^4 * [C(n_A-2, k-2) * C(n_B-2, k-2)
  --                * (k-2)! * p^(k-2) * (1-p)^(k(k-1)-4)]
  --     = (n_A-1) * (n_B-1) * C(n_A-2) * C(n_B-2) * (k-2)! * p^(k-1) * (1-p)^(k(k-1))
  -- Using Pascal: (k-1) * C(n_A-1) = (n_A-1) * C(n_A-2)
  --                 and (k-1) * C(n_B-1) = (n_B-1) * C(n_B-2)
  -- gives  (k-1)^2 * C(n_A-1) * C(n_B-1) = (k-1) * (n_A-1) * C(n_A-2) * C(n_B-1)
  --                                        = (n_A-1) * (n_B-1) * C(n_A-2) * C(n_B-2)
  -- which is exactly the equality of the two coefficient products.
  -- We close via `linear_combination` over hA and hB.
  linear_combination
    (((k - 1 : ℕ) : ℝ) * (Nat.choose (n_B - 1) (k - 1) : ℝ)
      * (Nat.factorial (k - 2) : ℝ)
      * (p ^ (k - 2) * p)
      * ((1 - p) ^ (k * (k - 1) - 4) * (1 - p) ^ 4)) * hA
    + (((n_A - 1 : ℕ) : ℝ) * (Nat.choose (n_A - 2) (k - 2) : ℝ)
        * (Nat.factorial (k - 2) : ℝ)
        * (p ^ (k - 2) * p)
        * ((1 - p) ^ (k * (k - 1) - 4) * (1 - p) ^ 4)) * hB

/-! ## PS.4.b.1: matching-edge equiv infrastructure

For the integral identity `expectation_inducedKMatchings_with_edge` we will rewrite the
filter `{M : inducedKMatchings | (a, b) ∈ M}` as `{N : Finset (Fin n_A × Fin n_B) | ...}`
via the bijection `M ↦ M.erase (a, b)`, then sum over candidate `N`. This subsection
records the deterministic (graph-independent) part of the bijection. -/

/-- Erasing `(a, b)` from a `k`-induced-matching containing `(a, b)` yields a
`(k-1)`-subset of `Fin n_A × Fin n_B \ {(a, b)}` that, when reunited with `(a, b)`,
recovers the original matching. This is the deterministic (forward) direction. -/
lemma inducedKMatching_erase_insert
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B)) (k : ℕ)
    (a : Fin n_A) (b : Fin n_B)
    (M : Finset (Fin n_A × Fin n_B))
    (_h_mem : M ∈ inducedKMatchings G S T_set k) (h_ab : (a, b) ∈ M) :
    insert (a, b) (M.erase (a, b)) = M := by
  exact Finset.insert_erase h_ab

/-- The cardinality of `M.erase (a, b)` is `k - 1` when `M` is in `inducedKMatchings G ... k`
and `(a, b) ∈ M`. -/
lemma inducedKMatching_erase_card
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B)) (k : ℕ)
    (a : Fin n_A) (b : Fin n_B)
    (M : Finset (Fin n_A × Fin n_B))
    (h_mem : M ∈ inducedKMatchings G S T_set k) (h_ab : (a, b) ∈ M) :
    (M.erase (a, b)).card = k - 1 := by
  have h_card : M.card = k := ((mem_inducedKMatchings_iff G S T_set k M).mp h_mem).2.1
  rw [Finset.card_erase_of_mem h_ab, h_card]

/-- Predicate (decidable via `Classical`) on `N ⊆ crossBlockPairs \ {(a, b)}` of size
`k - 1`: `insert (a, b) N` is an induced matching and `(a, b)` itself lies in
`crossBlockPairs`. This is the abstracted RHS of the matching-erase bijection. -/
noncomputable def validErasePartner
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B))
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B)) : Prop :=
  (a, b) ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G S T_set ∧
  DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G (insert (a, b) N)

noncomputable instance validErasePartner_decidable
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B))
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B)) :
    Decidable (validErasePartner G S T_set a b N) :=
  Classical.propDecidable _

/-- Convert a filter on `inducedKMatchings` containing `(a, b)` to a filter on the
ambient `powersetCard` by erasing `(a, b)`.

This converts `{M : inducedKMatchings | (a,b) ∈ M}` to `{N : (k-1)-subsets of
crossBlockPairs \ {(a,b)} | insert (a,b) N is an induced matching}`, via the bijection
`M ↦ M.erase (a, b)`. -/
lemma inducedKMatchings_filter_mem_image_erase
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B)) (k : ℕ) (_h_k_pos : 0 < k)
    (a : Fin n_A) (b : Fin n_B) :
    ((inducedKMatchings G S T_set k).filter (fun M => (a, b) ∈ M)).card
      = ((((DaveyThesis2024.SecRandomBipartite.crossBlockPairs G S T_set).erase (a, b)).powersetCard (k - 1)).filter
            (validErasePartner G S T_set a b)).card := by
  classical
  apply Finset.card_bij (fun M (_h : M ∈ _) => M.erase (a, b))
  · -- maps into the target Finset
    intro M hM
    simp only [Finset.mem_filter] at hM
    obtain ⟨h_mem, h_ab⟩ := hM
    have h_iff := (mem_inducedKMatchings_iff G S T_set k M).mp h_mem
    have h_sub : M ⊆ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G S T_set := h_iff.1
    have h_card : M.card = k := h_iff.2.1
    have h_match : DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G M := h_iff.2.2
    have h_ab_cross : (a, b) ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G S T_set := h_sub h_ab
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
      · -- M.erase (a, b) ⊆ crossBlockPairs.erase (a, b)
        intro x hx
        rw [Finset.mem_erase] at hx ⊢
        exact ⟨hx.1, h_sub hx.2⟩
      · rw [Finset.card_erase_of_mem h_ab, h_card]
    · refine ⟨h_ab_cross, ?_⟩
      rw [Finset.insert_erase h_ab]
      exact h_match
  · -- injectivity
    intro M₁ hM₁ M₂ hM₂ h_eq
    simp only [Finset.mem_filter] at hM₁ hM₂
    have h₁ := Finset.insert_erase hM₁.2
    have h₂ := Finset.insert_erase hM₂.2
    rw [← h₁, ← h₂, h_eq]
  · -- surjectivity
    intro N hN
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hN
    obtain ⟨⟨h_sub, h_card⟩, h_ab_cross, h_match⟩ := hN
    have h_not_mem : (a, b) ∉ N := by
      intro h_mem
      have := h_sub h_mem
      exact (Finset.mem_erase.mp this).1 rfl
    refine ⟨insert (a, b) N, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, Finset.mem_insert_self _ _⟩
      refine (mem_inducedKMatchings_iff G S T_set k _).mpr ⟨?_, ?_, h_match⟩
      · intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with hx | hx
        · rw [hx]; exact h_ab_cross
        · exact (Finset.mem_erase.mp (h_sub hx)).2
      · rw [Finset.card_insert_of_notMem h_not_mem, h_card]
        omega
    · rw [Finset.erase_insert h_not_mem]

/-! ## PS.4.b.3: structural extraction from `validErasePartner`

When `N` is a valid erase-partner of `(a, b)` — i.e., `insert (a, b) N` is an induced
bipartite matching — we extract three structural facts useful for the integrand
decomposition in PS.4.b.4+:

* No element of `N` has A-coord equal to `a`.
* No element of `N` has B-coord equal to `b`.
* The A-coords of `N` are pairwise distinct; similarly the B-coords. -/

/-- If `N` is a valid erase-partner of `(a, b)`, no `(a', b') ∈ N` has `a' = a`. -/
lemma validErasePartner_A_coord_ne
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B))
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_valid : validErasePartner G S T_set a b N)
    (h_notMem : (a, b) ∉ N)
    (ab' : Fin n_A × Fin n_B) (h_in : ab' ∈ N) :
    ab'.1 ≠ a := by
  intro h_eq_a
  have h_match := h_valid.2
  have h_ab_in : (a, b) ∈ insert (a, b) N := Finset.mem_insert_self _ _
  have h_ab'_in : ab' ∈ insert (a, b) N := Finset.mem_insert_of_mem h_in
  have h_ne : (a, b) ≠ ab' := by
    intro h; rw [← h] at h_in; exact h_notMem h_in
  exact (h_match (a, b) h_ab_in ab' h_ab'_in h_ne).1 h_eq_a.symm

/-- If `N` is a valid erase-partner of `(a, b)`, no `(a', b') ∈ N` has `b' = b`. -/
lemma validErasePartner_B_coord_ne
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B))
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_valid : validErasePartner G S T_set a b N)
    (h_notMem : (a, b) ∉ N)
    (ab' : Fin n_A × Fin n_B) (h_in : ab' ∈ N) :
    ab'.2 ≠ b := by
  intro h_eq_b
  have h_match := h_valid.2
  have h_ab_in : (a, b) ∈ insert (a, b) N := Finset.mem_insert_self _ _
  have h_ab'_in : ab' ∈ insert (a, b) N := Finset.mem_insert_of_mem h_in
  have h_ne : (a, b) ≠ ab' := by
    intro h; rw [← h] at h_in; exact h_notMem h_in
  exact (h_match (a, b) h_ab_in ab' h_ab'_in h_ne).2.1 h_eq_b.symm

/-- The A-coordinates of a valid erase-partner `N` are pairwise distinct. -/
lemma validErasePartner_A_coords_inj
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B))
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_valid : validErasePartner G S T_set a b N)
    (ab₁ ab₂ : Fin n_A × Fin n_B) (h₁ : ab₁ ∈ N) (h₂ : ab₂ ∈ N) (h_ne : ab₁ ≠ ab₂) :
    ab₁.1 ≠ ab₂.1 := by
  have h_match := h_valid.2
  exact (h_match ab₁ (Finset.mem_insert_of_mem h₁) ab₂ (Finset.mem_insert_of_mem h₂) h_ne).1

/-- The B-coordinates of a valid erase-partner `N` are pairwise distinct. -/
lemma validErasePartner_B_coords_inj
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B))
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_valid : validErasePartner G S T_set a b N)
    (ab₁ ab₂ : Fin n_A × Fin n_B) (h₁ : ab₁ ∈ N) (h₂ : ab₂ ∈ N) (h_ne : ab₁ ≠ ab₂) :
    ab₁.2 ≠ ab₂.2 := by
  have h_match := h_valid.2
  exact (h_match ab₁ (Finset.mem_insert_of_mem h₁) ab₂ (Finset.mem_insert_of_mem h₂) h_ne).2.1

/-! ## PS.4.b.4+: integral identity — Step B (graph-independent N-universe)

The proof plan rewrites the LHS count via:

* The bijection `inducedKMatchings_filter_mem_image_erase` (PS.4.b.2 above)
  gives `count(g) = | ((crossBlockPairs g).erase (a,b)).powersetCard (k-1) |`
  filtered by `validErasePartner g`.
* Multiplied by `1[g(a,b)]`, this equals a sum over the **graph-independent**
  universe `((univ : Finset (Fin n_A × Fin n_B)).erase (a,b)).powersetCard (k-1)`
  of an indicator product on `g`. The g-dependence is encoded as a real-valued
  indicator function. -/

/-- **Structural (graph-independent) candidate predicate** on a `(k-1)`-subset
`N` of `(univ : Finset (Fin n_A × Fin n_B)).erase (a, b)`: no element has
A-coord `a`, no element has B-coord `b`, A-coords are pairwise distinct,
B-coords are pairwise distinct.

Only valid candidates can correspond to actual induced matchings of size
`k` containing `(a, b)`. For non-candidates, the `matchingIndicator` collapses
to `0`. -/
def CandidatePartner
    {n_A n_B : ℕ} (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B)) : Prop :=
  (∀ x ∈ N, x.1 ≠ a) ∧
  (∀ x ∈ N, x.2 ≠ b) ∧
  (∀ x ∈ N, ∀ y ∈ N, x ≠ y → x.1 ≠ y.1) ∧
  (∀ x ∈ N, ∀ y ∈ N, x ≠ y → x.2 ≠ y.2)

noncomputable instance CandidatePartner_decidable
    {n_A n_B : ℕ} (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B)) :
    Decidable (CandidatePartner a b N) := Classical.propDecidable _

/-- The graph-independent universe of candidate erase-partners for `(a, b)`. -/
noncomputable def candidatePartnerSet
    (n_A n_B : ℕ) (k : ℕ) (a : Fin n_A) (b : Fin n_B) :
    Finset (Finset (Fin n_A × Fin n_B)) :=
  ((Finset.univ.erase (a, b)).powersetCard (k - 1)).filter (CandidatePartner a b)

lemma mem_candidatePartnerSet_iff
    {n_A n_B : ℕ} (k : ℕ) (a : Fin n_A) (b : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) :
    N ∈ candidatePartnerSet n_A n_B k a b ↔
      N ⊆ Finset.univ.erase (a, b) ∧ N.card = k - 1 ∧ CandidatePartner a b N := by
  unfold candidatePartnerSet
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  tauto

/-- **Real-valued indicator** of `M ∈ inducedKMatchings g univ univ k ∧ (a,b) ∈ M`.

For a fixed `(k-1)`-subset `N` of `(univ : Finset (Fin n_A × Fin n_B)).erase (a,b)`,
this is the indicator of the event "insert (a,b) N is in inducedKMatchings g
univ univ k", computed entirely from `g`. The product structure decomposes into:

* `1[g(a,b)] · ∏_{(α,β) ∈ N} 1[g(α,β)]` — all matching edges present.
* `∏_{(α,β) ∈ N} (1 - 1[g(a,β)]) · (1 - 1[g(α,b)])` — bridges to (a,b) absent.
* `∏_{(x,y) ∈ N×N, x≠y} (1 - 1[g(x.1, y.2)])` — within-N bridges absent.

Each factor is a `(0,1)`-indicator, so the whole product is `0` or `1`. -/
noncomputable def matchingIndicator
    {n_A n_B : ℕ} (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (g : Fin n_A × Fin n_B → Bool) : ℝ :=
  (if g (a, b) = true then (1 : ℝ) else 0) *
  (∏ x ∈ N, if g x = true then (1 : ℝ) else 0) *
  (∏ x ∈ N, if g (a, x.2) = true then (0 : ℝ) else 1) *
  (∏ x ∈ N, if g (x.1, b) = true then (0 : ℝ) else 1) *
  (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
      if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1)

/-- Helper: a finite product of `{0,1}`-valued factors lies in `{0,1}`. -/
private lemma prod_of_zero_one_in_zero_one {α : Type*}
    (s : Finset α) (f : α → ℝ) (h : ∀ x ∈ s, f x = 0 ∨ f x = 1) :
    (∏ x ∈ s, f x) = 0 ∨ (∏ x ∈ s, f x) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => right; simp
  | insert a' s' h_notMem ih =>
    rw [Finset.prod_insert h_notMem]
    have h_a := h a' (Finset.mem_insert_self a' s')
    have h_rest : ∀ x ∈ s', f x = 0 ∨ f x = 1 := fun x hx => h x (Finset.mem_insert_of_mem hx)
    rcases h_a with h_a | h_a
    · left; rw [h_a]; ring
    · rcases ih h_rest with h_p | h_p
      · left; rw [h_p]; ring
      · right; rw [h_a, h_p]; ring

/-- The `matchingIndicator` is either `0` or `1`. -/
lemma matchingIndicator_eq_zero_or_one
    {n_A n_B : ℕ} (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (g : Fin n_A × Fin n_B → Bool) :
    matchingIndicator a b N g = 0 ∨ matchingIndicator a b N g = 1 := by
  classical
  unfold matchingIndicator
  have h1 : ((if g (a, b) = true then (1 : ℝ) else 0)) = 0 ∨
            ((if g (a, b) = true then (1 : ℝ) else 0)) = 1 := by
    by_cases h : g (a, b) = true <;> simp [h]
  have h2 := prod_of_zero_one_in_zero_one N (fun x => if g x = true then (1 : ℝ) else 0)
    (fun x _ => by by_cases h : g x = true <;> simp [h])
  have h3 := prod_of_zero_one_in_zero_one N (fun x => if g (a, x.2) = true then (0 : ℝ) else 1)
    (fun x _ => by by_cases h : g (a, x.2) = true <;> simp [h])
  have h4 := prod_of_zero_one_in_zero_one N (fun x => if g (x.1, b) = true then (0 : ℝ) else 1)
    (fun x _ => by by_cases h : g (x.1, b) = true <;> simp [h])
  have h5 := prod_of_zero_one_in_zero_one ((N ×ˢ N).filter (fun p => p.1 ≠ p.2))
    (fun p => if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1)
    (fun p _ => by by_cases h : g (p.1.1, p.2.2) = true <;> simp [h])
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
    <;> rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5
    <;> simp [h1, h2, h3, h4, h5]

/-- **Key pointwise identity for Step B**: for any `g`, the integrand
`count · 1[g(a,b)]` decomposes as a sum over all `(k-1)`-subsets `N` of
`univ.erase (a,b)` (a graph-independent universe!) of `matchingIndicator a b N g`. -/
lemma count_mul_indicator_eq_sum_matchingIndicator
    {n_A n_B : ℕ} (k : ℕ) (h_k_pos : 0 < k)
    (a : Fin n_A) (b : Fin n_B) (g : Fin n_A × Fin n_B → Bool) :
    ((((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
        (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
        Finset.univ Finset.univ k).filter (fun M => (a, b) ∈ M)).card : ℝ) *
        (if g (a, b) = true then (1 : ℝ) else 0))
      = ∑ N ∈ ((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a, b)).powersetCard (k - 1),
          matchingIndicator a b N g := by
  classical
  set G := DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g with hG
  -- Case split on g(a,b).
  by_cases h_ab : g (a, b) = true
  · rw [if_pos h_ab, mul_one]
    -- Apply the existing bijection: count = card of validErasePartner filter on
    -- ((crossBlockPairs G).erase (a,b)).powersetCard (k - 1).
    rw [inducedKMatchings_filter_mem_image_erase G Finset.univ Finset.univ k h_k_pos a b]
    -- Now: card of filter over (crossBlockPairs G).erase (a,b) ... = sum over univ.erase (a,b).
    -- Strategy: show the RHS sum equals the LHS card via:
    -- For N ∈ univ.erase(a,b) of size k-1, matchingIndicator = 1 iff N is a valid erase-partner.
    -- And every valid erase-partner (under N ⊆ crossBlockPairs.erase(a,b)) corresponds to a unique
    -- universe element with matchingIndicator = 1.
    -- We use Finset.card_filter + Finset.sum_filter to rewrite each side.
    -- LHS = sum N ∈ (cross.erase (a,b)).powersetCard (k-1), 1[validErasePartner G univ univ a b N]
    rw [Finset.card_filter]
    push_cast
    -- Now need to equate two sums. The LHS sums over (crossBlockPairs G).erase (a,b)
    -- subsets; the RHS over univ.erase (a,b) subsets. The LHS universe is a subset of RHS.
    -- We expand RHS to all N, then show: matchingIndicator = 0 for N not in LHS universe.
    have h_LHS_eq :
        (∑ N ∈ ((DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ).erase
                  (a, b)).powersetCard (k - 1),
            (if DaveyThesis2024.SecRandomBipartite.PippengerSpencer.validErasePartner
                  G Finset.univ Finset.univ a b N
                then (1 : ℝ) else 0))
        = ∑ N ∈ ((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a, b)).powersetCard (k - 1),
              matchingIndicator a b N g := by
      -- Show termwise equality: for N in the LHS universe, both terms agree; for N
      -- outside the LHS universe but inside the RHS universe, the RHS term is 0.
      -- We use sum_subset.
      rw [← Finset.sum_subset (s₁ :=
        ((DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ).erase
          (a, b)).powersetCard (k - 1))
        (s₂ := ((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a, b)).powersetCard (k - 1))
        (h := fun N hN => by
          rw [Finset.mem_powersetCard] at hN ⊢
          refine ⟨?_, hN.2⟩
          intro x hx
          have := hN.1 hx
          rw [Finset.mem_erase] at this ⊢
          exact ⟨this.1, Finset.mem_univ _⟩)
        (f := fun N => matchingIndicator a b N g)]
      · -- Equal on s₁ = (crossBlockPairs.erase (a,b)).powersetCard (k-1).
        apply Finset.sum_congr rfl
        intro N hN
        rw [Finset.mem_powersetCard] at hN
        obtain ⟨h_sub_cross, h_N_card⟩ := hN
        -- N ⊆ (crossBlockPairs G).erase (a,b), so for all x ∈ N, x.1 cross-edge in G with g x = true.
        have h_N_g_true : ∀ x ∈ N, g x = true := by
          intro x hx
          have hx_cross := h_sub_cross hx
          rw [Finset.mem_erase] at hx_cross
          have hx_in_cross : x ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ :=
            hx_cross.2
          rw [DaveyThesis2024.SecRandomBipartite.mem_crossBlockPairs] at hx_in_cross
          have h_adj : G.Adj (Sum.inl x.1) (Sum.inr x.2) := hx_in_cross.2.2
          rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr] at h_adj
          exact h_adj
        -- Now compute matchingIndicator.
        -- The first factor is 1 (since g(a,b)=true).
        -- The second factor is 1 (since g x = true for all x ∈ N).
        -- The remaining three factors are 1 iff validErasePartner holds.
        unfold matchingIndicator
        rw [if_pos h_ab]
        have h_prod_present : (∏ x ∈ N, if g x = true then (1 : ℝ) else 0) = 1 := by
          apply Finset.prod_eq_one
          intro x hx
          rw [if_pos (h_N_g_true x hx)]
        rw [h_prod_present]
        -- Now goal: 1 * 1 * (prod1) * (prod2) * (prod3) = if validErasePartner then 1 else 0.
        -- The three remaining products together encode the IsBipartiteInducedMatching condition.
        -- Equivalence: validErasePartner G univ univ a b N ↔ (∏1 = 1 ∧ ∏2 = 1 ∧ ∏3 = 1).
        by_cases h_valid : DaveyThesis2024.SecRandomBipartite.PippengerSpencer.validErasePartner
            G Finset.univ Finset.univ a b N
        · rw [if_pos h_valid]
          -- All three products should be 1.
          have h_match : DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G (insert (a, b) N) :=
            h_valid.2
          have h_ab_notMem : (a, b) ∉ N := by
            intro h
            have := h_sub_cross h
            rw [Finset.mem_erase] at this
            exact this.1 rfl
          -- Product 1: ∏_{x ∈ N} 1[g(a, x.2) = false] = 1 — bridge (a, x.2) absent.
          have h_p1 : (∏ x ∈ N, if g (a, x.2) = true then (0 : ℝ) else 1) = 1 := by
            apply Finset.prod_eq_one
            intro x hx
            -- From matching condition on (a,b), x: need ¬G.Adj (inl a) (inr x.2)
            have hx_in : x ∈ insert (a, b) N := Finset.mem_insert_of_mem hx
            have hab_in : (a, b) ∈ insert (a, b) N := Finset.mem_insert_self _ _
            have h_ne : (a, b) ≠ x := by
              intro h; rw [← h] at hx; exact h_ab_notMem hx
            have h_match_ab_x := h_match (a, b) hab_in x hx_in h_ne
            -- The 3rd component: ¬G.Adj (inl a) (inr x.2)
            have h_no_bridge : ¬ G.Adj (Sum.inl (a, b).1) (Sum.inr x.2) := h_match_ab_x.2.2.1
            rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr] at h_no_bridge
            cases hg : g (a, x.2) with
            | false => simp
            | true => exact absurd hg h_no_bridge
          rw [h_p1]
          -- Product 2: ∏_{x ∈ N} 1[g(x.1, b) = false] = 1 — bridge (x.1, b) absent.
          have h_p2 : (∏ x ∈ N, if g (x.1, b) = true then (0 : ℝ) else 1) = 1 := by
            apply Finset.prod_eq_one
            intro x hx
            have hx_in : x ∈ insert (a, b) N := Finset.mem_insert_of_mem hx
            have hab_in : (a, b) ∈ insert (a, b) N := Finset.mem_insert_self _ _
            have h_ne : (a, b) ≠ x := by
              intro h; rw [← h] at hx; exact h_ab_notMem hx
            have h_match_ab_x := h_match (a, b) hab_in x hx_in h_ne
            -- The 4th component: ¬G.Adj (inl x.1) (inr (a,b).2 = inr b)
            have h_no_bridge : ¬ G.Adj (Sum.inl x.1) (Sum.inr (a, b).2) := h_match_ab_x.2.2.2
            rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr] at h_no_bridge
            cases hg : g (x.1, b) with
            | false => simp
            | true => exact absurd hg h_no_bridge
          rw [h_p2]
          -- Product 3: ∏_{(p1,p2) ∈ N×N, p1≠p2} 1[g(p1.1, p2.2) = false] = 1 — within-N bridges absent.
          have h_p3 : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
              if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1) = 1 := by
            apply Finset.prod_eq_one
            intro p hp
            rw [Finset.mem_filter, Finset.mem_product] at hp
            obtain ⟨⟨h_p1_in, h_p2_in⟩, h_p_ne⟩ := hp
            have hp1_in_insert : p.1 ∈ insert (a, b) N := Finset.mem_insert_of_mem h_p1_in
            have hp2_in_insert : p.2 ∈ insert (a, b) N := Finset.mem_insert_of_mem h_p2_in
            have h_match_p := h_match p.1 hp1_in_insert p.2 hp2_in_insert h_p_ne
            have h_no_bridge : ¬ G.Adj (Sum.inl p.1.1) (Sum.inr p.2.2) := h_match_p.2.2.1
            rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr] at h_no_bridge
            cases hg : g (p.1.1, p.2.2) with
            | false => simp
            | true => exact absurd hg h_no_bridge
          rw [h_p3]; ring
        · rw [if_neg h_valid]
          -- One of the three products is 0.
          -- validErasePartner = (a,b) ∈ crossBlockPairs ∧ IsBipartiteInducedMatching (insert (a,b) N).
          -- (a,b) ∈ crossBlockPairs G univ univ holds because g(a,b) = true.
          have h_ab_in_cross : (a, b) ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs
              G Finset.univ Finset.univ := by
            rw [DaveyThesis2024.SecRandomBipartite.mem_crossBlockPairs]
            refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
            rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr]
            exact h_ab
          have h_not_match :
              ¬ DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G (insert (a, b) N) := by
            intro h_match
            exact h_valid ⟨h_ab_in_cross, h_match⟩
          -- Unfold the failure of IsBipartiteInducedMatching.
          unfold DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching at h_not_match
          push_neg at h_not_match
          obtain ⟨ab₁, hab₁_in, ab₂, hab₂_in, hab_ne, h_violation⟩ := h_not_match
          have h_ab_notMem : (a, b) ∉ N := by
            intro h
            have := h_sub_cross h
            rw [Finset.mem_erase] at this
            exact this.1 rfl
          rw [Finset.mem_insert] at hab₁_in hab₂_in
          -- h_violation has chained-implication form:
          -- (ab₁.1 ≠ ab₂.1) → (ab₁.2 ≠ ab₂.2) → ¬G.Adj (inl ab₁.1) (inr ab₂.2) → G.Adj (inl ab₂.1) (inr ab₁.2)
          -- Strategy: show that for ALL possible violations, the matchingIndicator product is 0
          -- by finding a specific zero factor.
          -- Case-split on which violation occurs by examining the chain.
          -- Sub-strategy: peel off conditions until we hit a "true" zero.
          -- If ab₁.1 = ab₂.1, then both have the same A-coord. Among (a,b), ab₁, ab₂ at least
          -- one element of N has either x.1 = a or shares A-coord with another N element.
          -- We handle by direct case analysis on the (a,b) ∈ {ab₁, ab₂} status.
          rcases hab₁_in with h₁ | h₁ <;> rcases hab₂_in with h₂ | h₂
          · exact absurd (h₁.trans h₂.symm) hab_ne
          · -- ab₁ = (a,b), ab₂ ∈ N.
            subst h₁
            -- Conditions reduce: (a,b).1 ≠ ab₂.1 means a ≠ ab₂.1; (a,b).2 ≠ ab₂.2 means b ≠ ab₂.2.
            -- We don't have these as facts. If a = ab₂.1, then ab₂.1 = a, and the product
            -- ∏ x∈N, 1[g(x.1, b) = false] includes a term for ab₂ with x.1 = a, but
            -- but g(a, b) = true, so g(x.1, b) = g(a, b) = true makes the factor 0 — wait
            -- only if x.1 = a AND x.2 = b, which contradicts (a,b) ∉ N.
            -- Hmm. Let's just split on the conditions of h_violation.
            by_cases hA : (a, b).1 = ab₂.1
            · -- ab₂.1 = a. Then b1 product has (a, b) appearing when x = ab₂; g(x.1,b) = g(a,b) = true.
              -- So the factor is `if true then 0 else 1` = 0.
              -- Wait actually we need g(ab₂.1, b) = g(a, b) = true. The corresponding factor
              -- in the b-bridge product is `if g(ab₂.1, b) = true then 0 else 1` = 0.
              have h_p2_zero : (∏ x ∈ N, if g (x.1, b) = true then (0 : ℝ) else 1) = 0 := by
                apply Finset.prod_eq_zero h₂
                have : g (ab₂.1, b) = g ((a, b).1, b) := by rw [hA]
                rw [this]
                change (if g ((a, b).1, b) = true then (0 : ℝ) else 1) = 0
                have : g ((a, b).1, b) = true := by change g (a, b) = true; exact h_ab
                rw [if_pos this]
              rw [h_p2_zero]; ring
            · -- a ≠ ab₂.1. Continue to next condition.
              by_cases hB : (a, b).2 = ab₂.2
              · have h_p1_zero : (∏ x ∈ N, if g (a, x.2) = true then (0 : ℝ) else 1) = 0 := by
                  apply Finset.prod_eq_zero h₂
                  have : g (a, ab₂.2) = g (a, (a, b).2) := by rw [hB]
                  rw [this]
                  change (if g (a, (a, b).2) = true then (0 : ℝ) else 1) = 0
                  have : g (a, (a, b).2) = true := by change g (a, b) = true; exact h_ab
                  rw [if_pos this]
                rw [h_p1_zero]; ring
              · -- All bridge conditions hold; final-step gives g-edge in G — translate to indicator.
                have h_step3 := h_violation hA hB
                -- h_step3 : ¬ G.Adj (inl (a,b).1) (inr ab₂.2) → G.Adj (inl ab₂.1) (inr (a,b).2)
                by_cases h_bridge1 : G.Adj (Sum.inl (a, b).1) (Sum.inr ab₂.2)
                · -- G.Adj (inl a) (inr ab₂.2). This means g(a, ab₂.2) = true.
                  -- The a-bridge product has factor `if g(a, ab₂.2) = true then 0 else 1` = 0.
                  rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr] at h_bridge1
                  have h_p1_zero : (∏ x ∈ N, if g (a, x.2) = true then (0 : ℝ) else 1) = 0 := by
                    apply Finset.prod_eq_zero h₂
                    change (if g (a, ab₂.2) = true then (0 : ℝ) else 1) = 0
                    rw [if_pos h_bridge1]
                  rw [h_p1_zero]; ring
                · -- ¬ G.Adj... so h_step3 gives G.Adj (inl ab₂.1) (inr b).
                  have h_step4 := h_step3 h_bridge1
                  rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr] at h_step4
                  have h_p2_zero : (∏ x ∈ N, if g (x.1, b) = true then (0 : ℝ) else 1) = 0 := by
                    apply Finset.prod_eq_zero h₂
                    change (if g (ab₂.1, b) = true then (0 : ℝ) else 1) = 0
                    rw [if_pos h_step4]
                  rw [h_p2_zero]; ring
          · -- ab₁ ∈ N, ab₂ = (a,b). Symmetric.
            subst h₂
            by_cases hA : ab₁.1 = (a, b).1
            · have h_p2_zero : (∏ x ∈ N, if g (x.1, b) = true then (0 : ℝ) else 1) = 0 := by
                apply Finset.prod_eq_zero h₁
                change (if g (ab₁.1, b) = true then (0 : ℝ) else 1) = 0
                have : g (ab₁.1, b) = g ((a, b).1, b) := by rw [hA]
                rw [this]
                have : g ((a, b).1, b) = true := by change g (a, b) = true; exact h_ab
                rw [if_pos this]
              rw [h_p2_zero]; ring
            · by_cases hB : ab₁.2 = (a, b).2
              · have h_p1_zero : (∏ x ∈ N, if g (a, x.2) = true then (0 : ℝ) else 1) = 0 := by
                  apply Finset.prod_eq_zero h₁
                  change (if g (a, ab₁.2) = true then (0 : ℝ) else 1) = 0
                  have : g (a, ab₁.2) = g (a, (a, b).2) := by rw [hB]
                  rw [this]
                  have : g (a, (a, b).2) = true := by change g (a, b) = true; exact h_ab
                  rw [if_pos this]
                rw [h_p1_zero]; ring
              · have h_step3 := h_violation hA hB
                by_cases h_bridge1 : G.Adj (Sum.inl ab₁.1) (Sum.inr (a, b).2)
                · rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr] at h_bridge1
                  have h_p2_zero : (∏ x ∈ N, if g (x.1, b) = true then (0 : ℝ) else 1) = 0 := by
                    apply Finset.prod_eq_zero h₁
                    change (if g (ab₁.1, b) = true then (0 : ℝ) else 1) = 0
                    rw [if_pos h_bridge1]
                  rw [h_p2_zero]; ring
                · have h_step4 := h_step3 h_bridge1
                  rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr] at h_step4
                  have h_p1_zero : (∏ x ∈ N, if g (a, x.2) = true then (0 : ℝ) else 1) = 0 := by
                    apply Finset.prod_eq_zero h₁
                    change (if g (a, ab₁.2) = true then (0 : ℝ) else 1) = 0
                    rw [if_pos h_step4]
                  rw [h_p1_zero]; ring
          · -- ab₁ ∈ N, ab₂ ∈ N.
            -- (ab₁, ab₂) is in (N ×ˢ N).filter (fun p => p.1 ≠ p.2).
            have h_pair_in : (ab₁, ab₂) ∈ (N ×ˢ N).filter
                (fun p : (Fin n_A × Fin n_B) × _ => p.1 ≠ p.2) := by
              rw [Finset.mem_filter, Finset.mem_product]
              exact ⟨⟨h₁, h₂⟩, hab_ne⟩
            have h_pair_swap_in : (ab₂, ab₁) ∈ (N ×ˢ N).filter
                (fun p : (Fin n_A × Fin n_B) × _ => p.1 ≠ p.2) := by
              rw [Finset.mem_filter, Finset.mem_product]
              exact ⟨⟨h₂, h₁⟩, fun h => hab_ne h.symm⟩
            -- If ab₁.1 = ab₂.1, then ab₁ and ab₂ have same A-coord. Consider (ab₁, ab₂) in p3:
            -- product contains `if g(ab₁.1, ab₂.2) then 0 else 1`. Since (ab₁.1, ab₂.2) = (ab₂.1, ab₂.2) = ab₂,
            -- and ab₂ ∈ N so g(ab₂) = true. Hence factor = 0.
            by_cases hA : ab₁.1 = ab₂.1
            · have h_p3_zero : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
                  if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1) = 0 := by
                apply Finset.prod_eq_zero h_pair_in
                change (if g (ab₁.1, ab₂.2) = true then (0 : ℝ) else 1) = 0
                have h_eq : (ab₁.1, ab₂.2) = ab₂ := Prod.ext hA rfl
                rw [h_eq]
                rw [if_pos (h_N_g_true ab₂ h₂)]
              rw [h_p3_zero]; ring
            · by_cases hB : ab₁.2 = ab₂.2
              · have h_p3_zero : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
                    if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1) = 0 := by
                  apply Finset.prod_eq_zero h_pair_in
                  change (if g (ab₁.1, ab₂.2) = true then (0 : ℝ) else 1) = 0
                  have h_eq : (ab₁.1, ab₂.2) = ab₁ := Prod.ext rfl hB.symm
                  rw [h_eq]
                  rw [if_pos (h_N_g_true ab₁ h₁)]
                rw [h_p3_zero]; ring
              · have h_step3 := h_violation hA hB
                by_cases h_bridge1 : G.Adj (Sum.inl ab₁.1) (Sum.inr ab₂.2)
                · rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr] at h_bridge1
                  have h_p3_zero : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
                      if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1) = 0 := by
                    apply Finset.prod_eq_zero h_pair_in
                    change (if g (ab₁.1, ab₂.2) = true then (0 : ℝ) else 1) = 0
                    rw [if_pos h_bridge1]
                  rw [h_p3_zero]; ring
                · have h_step4 := h_step3 h_bridge1
                  rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr] at h_step4
                  have h_p3_zero : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
                      if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1) = 0 := by
                    apply Finset.prod_eq_zero h_pair_swap_in
                    change (if g (ab₂.1, ab₁.2) = true then (0 : ℝ) else 1) = 0
                    rw [if_pos h_step4]
                  rw [h_p3_zero]; ring
      · -- For N ∈ univ.erase (a,b) \ (crossBlockPairs G).erase (a,b), matchingIndicator = 0.
        intro N hN_univ hN_notIn
        rw [Finset.mem_powersetCard] at hN_univ
        obtain ⟨h_sub_univ, h_N_card⟩ := hN_univ
        -- N is not in (crossBlockPairs.erase (a,b)).powersetCard (k-1), but in
        -- (univ.erase (a,b)).powersetCard (k-1). Hence some x ∈ N is not in crossBlockPairs G,
        -- i.e., g x = false.
        have h_not_sub_cross : ¬ (N ⊆ (DaveyThesis2024.SecRandomBipartite.crossBlockPairs
            G Finset.univ Finset.univ).erase (a, b)) := by
          intro h_sub
          apply hN_notIn
          rw [Finset.mem_powersetCard]
          exact ⟨h_sub, h_N_card⟩
        rw [Finset.not_subset] at h_not_sub_cross
        obtain ⟨x, hx_in, hx_notIn⟩ := h_not_sub_cross
        -- x ∈ N, so x ∈ univ.erase(a,b), so x ≠ (a,b). x ∉ (crossBlockPairs.erase(a,b))
        -- means either x = (a,b) (impossible since x ∈ N ⊆ univ.erase(a,b)) or
        -- x ∉ crossBlockPairs G. So g x = false.
        have hx_not_ab : x ≠ (a, b) := by
          have := h_sub_univ hx_in
          rw [Finset.mem_erase] at this
          exact this.1
        have hx_not_cross : x ∉ DaveyThesis2024.SecRandomBipartite.crossBlockPairs
            G Finset.univ Finset.univ := by
          intro h
          apply hx_notIn
          rw [Finset.mem_erase]
          exact ⟨hx_not_ab, h⟩
        rw [DaveyThesis2024.SecRandomBipartite.mem_crossBlockPairs] at hx_not_cross
        push_neg at hx_not_cross
        have hx_no_adj := hx_not_cross (Finset.mem_univ _) (Finset.mem_univ _)
        rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr] at hx_no_adj
        have hx_g_false : g x = false := by
          cases hg : g x with
          | false => rfl
          | true => exact absurd hg hx_no_adj
        -- Now matchingIndicator a b N g = 0 (second factor is 0 since x ∈ N has g x = false).
        unfold matchingIndicator
        have h_p_present_zero : (∏ x' ∈ N, if g x' = true then (1 : ℝ) else 0) = 0 := by
          apply Finset.prod_eq_zero hx_in
          rw [hx_g_false]; simp
        rw [h_p_present_zero]
        ring
    exact h_LHS_eq
  · -- g (a, b) = false case.
    rw [if_neg h_ab, mul_zero]
    -- All terms on the RHS are 0 (first factor of matchingIndicator is 0).
    symm
    apply Finset.sum_eq_zero
    intro N _hN
    unfold matchingIndicator
    rw [if_neg h_ab]; ring

/-! ## PS.4.b.7: per-N integration (Step C)

For each `N ∈ candidatePartnerSet`, integrate `matchingIndicator a b N g`
over the bipartite measure to obtain `p^k · (1-p)^(k(k-1))`. The k² slots
collapse pairwise-distinctly into `Fin n_A × Fin n_B`. For invalid N (not
a candidate), `matchingIndicator a b N g = 0` for all g, so integral is 0.

This is the most technically involved step: we use Mathlib's `iIndepFun`
precomposed with an injection from a `k²`-element indexed type into
`Fin n_A × Fin n_B`. -/

/-- For an `N` outside `candidatePartnerSet`, `matchingIndicator a b N g = 0`
for every `g`. The argument is: violating any candidate condition forces
some sub-product to contain a zero factor.

Specifically:
* If `(a, b) ∈ N`, the bridge-A factor at `(a, b)` is `if g(a, b)=true then 0 else 1`;
  combined with the present-edge factor for `(a, b) ∈ N` giving `if g(a, b)=true then 1 else 0`,
  the product is `0` regardless of `g(a, b)`.
* If `x ∈ N` has `x.1 = a`, the bridge `(x.1, b) = (a, b)` overlaps with the (a,b) slot itself,
  forcing both `g(a,b)=true` and `g(a,b)=false` — contradiction yields 0.
* Similar for `x.2 = b`, and for overlap of A- or B-coords within N. -/
lemma matchingIndicator_eq_zero_of_not_candidate
    {n_A n_B : ℕ} (k : ℕ) (_h_k_pos : 0 < k)
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ ((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a, b)).powersetCard (k - 1))
    (h_not_cand : N ∉ candidatePartnerSet n_A n_B k a b)
    (g : Fin n_A × Fin n_B → Bool) :
    matchingIndicator a b N g = 0 := by
  classical
  -- Unfold candidatePartnerSet membership.
  unfold candidatePartnerSet at h_not_cand
  rw [Finset.mem_filter] at h_not_cand
  push_neg at h_not_cand
  have h_not_part := h_not_cand hN
  unfold CandidatePartner at h_not_part
  push_neg at h_not_part
  -- h_not_part is now in chained-implication form:
  -- P1 → P2 → P3 → (∃ x ∈ N, ∃ y ∈ N, x ≠ y ∧ x.2 = y.2)
  rw [Finset.mem_powersetCard] at hN
  obtain ⟨h_sub, _h_card⟩ := hN
  -- Case-split on which condition fails.
  by_cases h_no_a : ∀ x ∈ N, x.1 ≠ a
  · by_cases h_no_b : ∀ x ∈ N, x.2 ≠ b
    · by_cases h_A_inj :
        ∀ x ∈ N, ∀ y ∈ N, x ≠ y → x.1 ≠ y.1
      · have h_B_fail := h_not_part h_no_a h_no_b h_A_inj
        obtain ⟨x, hx, y, hy, hxy, hxy_B⟩ := h_B_fail
        -- B-coords equal: x.2 = y.2 (and x ≠ y).
        -- Within-N bridge product has term at (y, x) (if x ≠ y) with slot (y.1, x.2) = (y.1, y.2) = y.
        -- y ∈ N. Hmm we don't have g(y) = true here; we have g arbitrary.
        -- The trick: the present-edge product at y is `if g(y) = true then 1 else 0`.
        -- The within-N bridge product at (x, y) is at slot (x.1, y.2). And at slot (y.1, x.2).
        -- Since x.2 = y.2: bridge slot (x.1, y.2) = (x.1, x.2) = x; and (y.1, x.2) = (y.1, y.2) = y.
        -- So the bridge factor at (x,y) is `if g(x.1, y.2) = true then 0 else 1` = `if g(x) then 0 else 1`.
        -- Combined with present-edge factor at x: `if g(x) then 1 else 0`. Their product over the
        -- 5-factor matchingIndicator is 0 regardless of g(x).
        unfold matchingIndicator
        -- Show: present-edge product * within-N bridge product = 0.
        -- Use Finset.prod_eq_zero in each.
        by_cases h_gx : g x = true
        · -- Present factor at x is 1; bridge factor at (x,y) is 0.
          have h_pair_in : (x, y) ∈ (N ×ˢ N).filter (fun p : (Fin n_A × Fin n_B) × _ => p.1 ≠ p.2) := by
            rw [Finset.mem_filter, Finset.mem_product]
            exact ⟨⟨hx, hy⟩, hxy⟩
          have h_p3_zero : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
              if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1) = 0 := by
            apply Finset.prod_eq_zero h_pair_in
            change (if g (x.1, y.2) = true then (0 : ℝ) else 1) = 0
            have h_eq : (x.1, y.2) = x := Prod.ext rfl hxy_B.symm
            rw [h_eq, if_pos h_gx]
          rw [h_p3_zero]; ring
        · -- Present factor at x is 0.
          have h_p_present_zero : (∏ x' ∈ N, if g x' = true then (1 : ℝ) else 0) = 0 := by
            apply Finset.prod_eq_zero hx
            have h_false : g x = false := by
              cases hg : g x with | false => rfl | true => exact absurd hg h_gx
            rw [if_neg]; intro h; rw [h_false] at h; exact Bool.false_ne_true h
          rw [h_p_present_zero]; ring
      · push_neg at h_A_inj
        obtain ⟨x, hx, y, hy, hxy, hxy_A⟩ := h_A_inj
        -- A-coords equal: x.1 = y.1, x ≠ y.
        unfold matchingIndicator
        by_cases h_gy : g y = true
        · -- Within-N bridge at (x, y): slot (x.1, y.2) = (y.1, y.2) = y. Factor is 0.
          have h_pair_in : (x, y) ∈ (N ×ˢ N).filter (fun p : (Fin n_A × Fin n_B) × _ => p.1 ≠ p.2) := by
            rw [Finset.mem_filter, Finset.mem_product]
            exact ⟨⟨hx, hy⟩, hxy⟩
          have h_p3_zero : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
              if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1) = 0 := by
            apply Finset.prod_eq_zero h_pair_in
            change (if g (x.1, y.2) = true then (0 : ℝ) else 1) = 0
            have h_eq : (x.1, y.2) = y := Prod.ext hxy_A rfl
            rw [h_eq, if_pos h_gy]
          rw [h_p3_zero]; ring
        · -- Present factor at y is 0.
          have h_p_present_zero : (∏ x' ∈ N, if g x' = true then (1 : ℝ) else 0) = 0 := by
            apply Finset.prod_eq_zero hy
            have h_false : g y = false := by
              cases hg : g y with | false => rfl | true => exact absurd hg h_gy
            rw [if_neg]; intro h; rw [h_false] at h; exact Bool.false_ne_true h
          rw [h_p_present_zero]; ring
    · -- ¬ (∀ x ∈ N, x.2 ≠ b), so ∃ x ∈ N, x.2 = b.
      push_neg at h_no_b
      obtain ⟨x, hx, hx_b⟩ := h_no_b
      -- The bridge-B product at x has factor `if g(x.1, b) = true then 0 else 1`.
      -- And bridge-A product at x has factor `if g(a, x.2) = true then 0 else 1` = `if g(a, b) then 0 else 1`.
      -- Present-edge product at x has factor `if g(x.1, b) = true then 1 else 0` (since x = (x.1, b)).
      -- Wait, present-edge factor is at x = (x.1, x.2) with x.2 = b, so slot (x.1, b) = x.
      -- The bridge-B factor at x is also at slot (x.1, b) = x. So we have both
      -- `if g x = true then 1 else 0` and `if g x = true then 0 else 1`, product is 0.
      unfold matchingIndicator
      by_cases h_gx : g x = true
      · have h_p2_zero : (∏ x' ∈ N, if g (x'.1, b) = true then (0 : ℝ) else 1) = 0 := by
          apply Finset.prod_eq_zero hx
          have h_eq : (x.1, b) = x := Prod.ext rfl hx_b.symm
          rw [h_eq, if_pos h_gx]
        rw [h_p2_zero]; ring
      · have h_p_present_zero : (∏ x' ∈ N, if g x' = true then (1 : ℝ) else 0) = 0 := by
          apply Finset.prod_eq_zero hx
          have h_false : g x = false := by
            cases hg : g x with | false => rfl | true => exact absurd hg h_gx
          rw [if_neg]; intro h; rw [h_false] at h; exact Bool.false_ne_true h
        rw [h_p_present_zero]; ring
  · -- ¬ (∀ x ∈ N, x.1 ≠ a), so ∃ x ∈ N, x.1 = a.
    push_neg at h_no_a
    obtain ⟨x, hx, hx_a⟩ := h_no_a
    unfold matchingIndicator
    by_cases h_gx : g x = true
    · have h_p1_zero : (∏ x' ∈ N, if g (a, x'.2) = true then (0 : ℝ) else 1) = 0 := by
        apply Finset.prod_eq_zero hx
        have h_eq : (a, x.2) = x := Prod.ext hx_a.symm rfl
        rw [h_eq, if_pos h_gx]
      rw [h_p1_zero]; ring
    · have h_p_present_zero : (∏ x' ∈ N, if g x' = true then (1 : ℝ) else 0) = 0 := by
        apply Finset.prod_eq_zero hx
        have h_false : g x = false := by
          cases hg : g x with | false => rfl | true => exact absurd hg h_gx
        rw [if_neg]; intro h; rw [h_false] at h; exact Bool.false_ne_true h
      rw [h_p_present_zero]; ring

/-! ## PS.4.b.5: per-candidate integration (Step C-final)

For each `N ∈ candidatePartnerSet n_A n_B k a b`, we prove

  `∫ matchingIndicator a b N g ∂μ = p^k · (1 - p)^(k * (k - 1))`.

Strategy: Express `matchingIndicator a b N g` as `∏ ab ∈ presentSlots, edgeIndicator ab.1 ab.2 g
  * ∏ ab ∈ absentSlots, (1 - edgeIndicator ab.1 ab.2 g)`,
where `presentSlots` and `absentSlots` are disjoint Finsets of cardinalities `k` and
`k(k-1)` respectively. The slot indicators across `Fin n_A × Fin n_B` are mutually
independent under `bipartiteEdgeChoice`, so the integral factors as `p^k · (1-p)^{k(k-1)}`.

The disjointness + cardinality facts follow from the `CandidatePartner` properties:
no A-coord equals `a`, no B-coord equals `b`, and A/B-coords within `N` are pairwise distinct. -/

/-- The "present" slots for a candidate `N`: the slot `(a, b)` plus the slots of `N`. -/
noncomputable def presentSlots {n_A n_B : ℕ} (a : Fin n_A) (b : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) : Finset (Fin n_A × Fin n_B) :=
  insert (a, b) N

/-- The "A-bridge absent" slots: `{(a, x.2) | x ∈ N}` via the injection `x ↦ (a, x.2)`. -/
noncomputable def aBridgeSlots {n_A n_B : ℕ} (a : Fin n_A)
    (N : Finset (Fin n_A × Fin n_B)) : Finset (Fin n_A × Fin n_B) :=
  N.image (fun x => (a, x.2))

/-- The "B-bridge absent" slots: `{(x.1, b) | x ∈ N}` via the injection `x ↦ (x.1, b)`. -/
noncomputable def bBridgeSlots {n_A n_B : ℕ} (b : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) : Finset (Fin n_A × Fin n_B) :=
  N.image (fun x => (x.1, b))

/-- The "within-N absent" slots: `{(p₁.1, p₂.2) | p₁ ≠ p₂ ∈ N}`. -/
noncomputable def withinNSlots {n_A n_B : ℕ}
    (N : Finset (Fin n_A × Fin n_B)) : Finset (Fin n_A × Fin n_B) :=
  ((N ×ˢ N).filter (fun p => p.1 ≠ p.2)).image (fun p => (p.1.1, p.2.2))

/-- The "absent" slots: union of A-bridge, B-bridge, within-N. -/
noncomputable def absentSlots {n_A n_B : ℕ} (a : Fin n_A) (b : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) : Finset (Fin n_A × Fin n_B) :=
  aBridgeSlots a N ∪ bBridgeSlots b N ∪ withinNSlots N

/-- `aBridgeSlots a N` has cardinality `N.card` when `N` is a candidate (B-coords distinct). -/
lemma aBridgeSlots_card_of_candidate {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) :
    (aBridgeSlots a N).card = N.card := by
  classical
  unfold aBridgeSlots
  apply Finset.card_image_of_injOn
  intro x hx y hy h_eq
  -- (a, x.2) = (a, y.2) → x.2 = y.2.
  have h_b_eq : x.2 = y.2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
  -- For candidates, distinct N-elements have distinct B-coords. So x = y.
  by_contra h_ne
  exact (h_cand.2.2.2 x hx y hy h_ne) h_b_eq

/-- `bBridgeSlots b N` has cardinality `N.card` when `N` is a candidate (A-coords distinct). -/
lemma bBridgeSlots_card_of_candidate {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) :
    (bBridgeSlots b N).card = N.card := by
  classical
  unfold bBridgeSlots
  apply Finset.card_image_of_injOn
  intro x hx y hy h_eq
  have h_a_eq : x.1 = y.1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
  by_contra h_ne
  exact (h_cand.2.2.1 x hx y hy h_ne) h_a_eq

/-- `aBridgeSlots a N ∩ bBridgeSlots b N = ∅` when `N` is a candidate (no A-coord = a,
no B-coord = b). -/
lemma aBridgeSlots_disjoint_bBridgeSlots {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) :
    Disjoint (aBridgeSlots a N) (bBridgeSlots b N) := by
  classical
  rw [Finset.disjoint_left]
  intro ab h_a h_b
  unfold aBridgeSlots at h_a
  unfold bBridgeSlots at h_b
  rw [Finset.mem_image] at h_a h_b
  obtain ⟨x, hx, h_eq_x⟩ := h_a
  obtain ⟨y, hy, h_eq_y⟩ := h_b
  -- ab = (a, x.2) = (y.1, b), so a = y.1 and x.2 = b.
  rw [← h_eq_x] at h_eq_y
  have h_a_eq : y.1 = a := (Prod.mk.injEq _ _ _ _).mp h_eq_y |>.1
  exact (h_cand.1 y hy) h_a_eq

/-- `aBridgeSlots ∩ withinNSlots = ∅`: within-N slots have A-coord in N (not `a`). -/
lemma aBridgeSlots_disjoint_withinNSlots {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) :
    Disjoint (aBridgeSlots a N) (withinNSlots N) := by
  classical
  rw [Finset.disjoint_left]
  intro ab h_a h_w
  unfold aBridgeSlots at h_a
  unfold withinNSlots at h_w
  rw [Finset.mem_image] at h_a h_w
  obtain ⟨x, hx, h_eq_x⟩ := h_a
  obtain ⟨p, hp, h_eq_p⟩ := h_w
  rw [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hp1, _⟩, _⟩ := hp
  -- ab = (a, x.2) = (p.1.1, p.2.2), so a = p.1.1, contradicting p.1 ∈ N having A-coord ≠ a.
  rw [← h_eq_x] at h_eq_p
  have h_a_eq : p.1.1 = a := (Prod.mk.injEq _ _ _ _).mp h_eq_p |>.1
  exact (h_cand.1 p.1 hp1) h_a_eq

/-- `bBridgeSlots ∩ withinNSlots = ∅`: within-N slots have B-coord in N (not `b`). -/
lemma bBridgeSlots_disjoint_withinNSlots {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) :
    Disjoint (bBridgeSlots b N) (withinNSlots N) := by
  classical
  rw [Finset.disjoint_left]
  intro ab h_b h_w
  unfold bBridgeSlots at h_b
  unfold withinNSlots at h_w
  rw [Finset.mem_image] at h_b h_w
  obtain ⟨x, hx, h_eq_x⟩ := h_b
  obtain ⟨p, hp, h_eq_p⟩ := h_w
  rw [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨_, hp2⟩, _⟩ := hp
  rw [← h_eq_x] at h_eq_p
  have h_b_eq : p.2.2 = b := (Prod.mk.injEq _ _ _ _).mp h_eq_p |>.2
  exact (h_cand.2.1 p.2 hp2) h_b_eq

/-- For candidate N: `withinNSlots ⊆ Nᶜ` element-wise (no within-N slot equals an element of N).
The key: if `(p₁.1, p₂.2) = y ∈ N`, then `p₁.1 = y.1` and `p₂.2 = y.2`. By A-coord injectivity,
`p₁ = y`; by B-coord injectivity, `p₂ = y`. So `p₁ = p₂`, contradicting `p₁ ≠ p₂`. -/
lemma withinNSlots_disjoint_N {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) :
    Disjoint (withinNSlots N) N := by
  classical
  rw [Finset.disjoint_left]
  intro ab h_w h_N
  unfold withinNSlots at h_w
  rw [Finset.mem_image] at h_w
  obtain ⟨p, hp, h_eq⟩ := h_w
  rw [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hp1, hp2⟩, h_p_ne⟩ := hp
  -- (p.1.1, p.2.2) = ab ∈ N. So ab.1 = p.1.1, ab.2 = p.2.2.
  have h_eq_1 : p.1.1 = ab.1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
  have h_eq_2 : p.2.2 = ab.2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
  -- A-coord of p.1 equals A-coord of ab; both in N. By A-coord-inj, either p.1 = ab or A-coord-clash.
  by_cases h_p1_eq_ab : p.1 = ab
  · -- then p.2.2 = ab.2 = p.1.2 (since p.1 = ab).
    have h_p2_b_eq : p.2.2 = p.1.2 := by rw [h_eq_2, h_p1_eq_ab]
    -- B-coord-inj: if p.1 ≠ p.2 then p.1.2 ≠ p.2.2.
    have h_p_ne' : p.1 ≠ p.2 := h_p_ne
    exact (h_cand.2.2.2 p.1 hp1 p.2 hp2 h_p_ne') h_p2_b_eq.symm
  · exact (h_cand.2.2.1 p.1 hp1 ab h_N h_p1_eq_ab) h_eq_1

/-- The filter `(N ×ˢ N).filter (fun p => p.1 ≠ p.2)` equals `N.offDiag`. -/
lemma filter_ne_eq_offDiag {n_A n_B : ℕ} (N : Finset (Fin n_A × Fin n_B)) :
    (N ×ˢ N).filter (fun p : (Fin n_A × Fin n_B) × _ => p.1 ≠ p.2) = N.offDiag := by
  ext p
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
  tauto

/-- For candidate N: `withinNSlots` has cardinality `N.card * (N.card - 1)`. The injection
`(p₁, p₂) ↦ (p₁.1, p₂.2)` on the off-diagonal is injective by A-coord and B-coord injectivity. -/
lemma withinNSlots_card_of_candidate {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) :
    (withinNSlots N).card = N.card * (N.card - 1) := by
  classical
  unfold withinNSlots
  rw [filter_ne_eq_offDiag]
  rw [Finset.card_image_of_injOn]
  · -- offDiag card. Goal: N.card * N.card - N.card = N.card * (N.card - 1).
    rw [Finset.offDiag_card]
    rcases Nat.eq_zero_or_pos N.card with h0 | hp
    · simp [h0]
    · rw [Nat.mul_sub_one]
  · -- Injectivity of (p₁, p₂) ↦ (p₁.1, p₂.2) on the off-diagonal.
    intro p hp q hq h_eq
    simp only [Finset.coe_offDiag, Set.mem_offDiag] at hp hq
    obtain ⟨hp1, hp2, _⟩ := hp
    obtain ⟨hq1, hq2, _⟩ := hq
    -- (p.1.1, p.2.2) = (q.1.1, q.2.2) → p.1.1 = q.1.1 and p.2.2 = q.2.2.
    have h_A : p.1.1 = q.1.1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
    have h_B : p.2.2 = q.2.2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
    have h_p1_eq : p.1 = q.1 := by
      by_contra h_ne
      exact (h_cand.2.2.1 p.1 hp1 q.1 hq1 h_ne) h_A
    have h_p2_eq : p.2 = q.2 := by
      by_contra h_ne
      exact (h_cand.2.2.2 p.2 hp2 q.2 hq2 h_ne) h_B
    exact Prod.ext h_p1_eq h_p2_eq

/-- `(a, b) ∉ presentSlots ∩ aBridgeSlots`: but more importantly, `aBridgeSlots ⊆ {(a, _)}`
and `(a, b) ∈ presentSlots`. We need: `(a, b) ∉ aBridgeSlots` is FALSE (it could be).
Actually for candidates: no element of N has B-coord = b, so `(a, b) ∉ aBridgeSlots`. -/
lemma ab_not_mem_aBridgeSlots {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) :
    (a, b) ∉ aBridgeSlots a N := by
  classical
  unfold aBridgeSlots
  rw [Finset.mem_image]
  rintro ⟨x, hx, h_eq⟩
  -- (a, x.2) = (a, b), so x.2 = b. But x ∈ N has B-coord ≠ b.
  have h_b_eq : x.2 = b := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
  exact (h_cand.2.1 x hx) h_b_eq

lemma ab_not_mem_bBridgeSlots {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) :
    (a, b) ∉ bBridgeSlots b N := by
  classical
  unfold bBridgeSlots
  rw [Finset.mem_image]
  rintro ⟨x, hx, h_eq⟩
  have h_a_eq : x.1 = a := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
  exact (h_cand.1 x hx) h_a_eq

lemma ab_not_mem_withinNSlots {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) :
    (a, b) ∉ withinNSlots N := by
  classical
  unfold withinNSlots
  rw [Finset.mem_image]
  rintro ⟨p, hp, h_eq⟩
  rw [Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hp1, _⟩, _⟩ := hp
  -- (p.1.1, p.2.2) = (a, b), so p.1.1 = a. But p.1 ∈ N has A-coord ≠ a.
  have h_a_eq : p.1.1 = a := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
  exact (h_cand.1 p.1 hp1) h_a_eq

/-- For candidate N: `presentSlots ∩ absentSlots = ∅`.

`presentSlots = insert (a,b) N`. We show: `(a,b) ∉ absentSlots` and `N ∩ absentSlots = ∅`.
- `(a,b) ∉ aBridge` (B-coord clash), `(a,b) ∉ bBridge` (A-coord clash), `(a,b) ∉ withinN` (A-coord clash).
- For x ∈ N: x ∉ aBridge (else x.1 = a), x ∉ bBridge (else x.2 = b), x ∉ withinN (proven). -/
lemma presentSlots_disjoint_absentSlots {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) :
    Disjoint (presentSlots a b N) (absentSlots a b N) := by
  classical
  unfold presentSlots absentSlots
  rw [Finset.disjoint_left]
  intro ab h_pres h_abs
  -- ab ∈ insert (a,b) N. Case-split.
  rw [Finset.mem_insert] at h_pres
  rw [Finset.mem_union, Finset.mem_union] at h_abs
  rcases h_pres with h_ab_eq | h_in_N
  · -- ab = (a, b). Show ab ∉ absent slots.
    rw [h_ab_eq] at h_abs
    rcases h_abs with (h_ab | h_bb) | h_wb
    · exact ab_not_mem_aBridgeSlots a b N h_cand h_ab
    · exact ab_not_mem_bBridgeSlots a b N h_cand h_bb
    · exact ab_not_mem_withinNSlots a b N h_cand h_wb
  · -- ab ∈ N. Show ab ∉ absent slots.
    rcases h_abs with (h_ab | h_bb) | h_wb
    · -- ab ∈ aBridgeSlots: then ab.1 = a, contradicting candidate.
      unfold aBridgeSlots at h_ab
      rw [Finset.mem_image] at h_ab
      obtain ⟨x, _, h_eq⟩ := h_ab
      have h_a : ab.1 = a := by rw [← h_eq]
      exact (h_cand.1 ab h_in_N) h_a
    · -- ab ∈ bBridgeSlots: then ab.2 = b.
      unfold bBridgeSlots at h_bb
      rw [Finset.mem_image] at h_bb
      obtain ⟨x, _, h_eq⟩ := h_bb
      have h_b' : ab.2 = b := by rw [← h_eq]
      exact (h_cand.2.1 ab h_in_N) h_b'
    · -- ab ∈ withinNSlots ∩ N: contradiction by withinNSlots_disjoint_N.
      have := (Finset.disjoint_left.mp (withinNSlots_disjoint_N a b N h_cand)) h_wb
      exact this h_in_N

/-- `(a, b) ∉ N` when `N ∈ candidatePartnerSet`. -/
lemma ab_not_mem_of_candidate {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePartnerSet n_A n_B k a b) :
    (a, b) ∉ N := by
  rw [mem_candidatePartnerSet_iff] at hN
  obtain ⟨h_sub, _, _⟩ := hN
  intro h
  have := h_sub h
  rw [Finset.mem_erase] at this
  exact this.1 rfl

/-- For candidate N with `N.card = k - 1` and `k ≥ 1`:
`presentSlots.card = k`. -/
lemma presentSlots_card_of_candidate {n_A n_B : ℕ} (k : ℕ) (h_k_pos : 0 < k)
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePartnerSet n_A n_B k a b) :
    (presentSlots a b N).card = k := by
  classical
  unfold presentSlots
  have h_ab : (a, b) ∉ N := ab_not_mem_of_candidate k a b N hN
  rw [Finset.card_insert_of_notMem h_ab]
  have h_N_card : N.card = k - 1 := by
    rw [mem_candidatePartnerSet_iff] at hN
    exact hN.2.1
  rw [h_N_card]
  omega

/-- For candidate N with `N.card = k - 1`: `absentSlots.card = k(k-1)`. -/
lemma absentSlots_card_of_candidate {n_A n_B : ℕ} (k : ℕ) (h_k_pos : 0 < k)
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePartnerSet n_A n_B k a b) :
    (absentSlots a b N).card = k * (k - 1) := by
  classical
  rw [mem_candidatePartnerSet_iff] at hN
  obtain ⟨_, h_N_card, h_cand⟩ := hN
  unfold absentSlots
  -- absentSlots = (aBridgeSlots ∪ bBridgeSlots) ∪ withinNSlots
  have h_disjoint_outer : Disjoint (aBridgeSlots a N ∪ bBridgeSlots b N) (withinNSlots N) := by
    rw [Finset.disjoint_union_left]
    exact ⟨aBridgeSlots_disjoint_withinNSlots a b N h_cand,
           bBridgeSlots_disjoint_withinNSlots a b N h_cand⟩
  have h_disjoint_inner : Disjoint (aBridgeSlots a N) (bBridgeSlots b N) :=
    aBridgeSlots_disjoint_bBridgeSlots a b N h_cand
  rw [Finset.card_union_of_disjoint h_disjoint_outer]
  rw [Finset.card_union_of_disjoint h_disjoint_inner]
  rw [aBridgeSlots_card_of_candidate a b N h_cand,
      bBridgeSlots_card_of_candidate a b N h_cand,
      withinNSlots_card_of_candidate a b N h_cand,
      h_N_card]
  -- (k - 1) + (k - 1) + (k - 1) * (k - 1 - 1) = k * (k - 1).
  rcases Nat.lt_or_ge 1 k with h_k_ge_2 | h_k_le_1
  · -- k ≥ 2: standard algebra.
    have h_k_eq : k = (k - 1) + 1 := by omega
    have h_k1_eq : k - 1 = (k - 1 - 1) + 1 := by omega
    -- (k-1) + (k-1) + (k-1)*((k-1)-1)
    nlinarith [Nat.sub_add_cancel (show 1 ≤ k from h_k_pos),
               Nat.sub_add_cancel (show 1 ≤ k - 1 by omega)]
  · -- k = 1: 0 + 0 + 0 * 0 = 0 = 1 * 0 ✓
    interval_cases k
    simp

/-- For candidate N: A-bridge product equals product over the image. Injectivity from
B-coord injectivity of CandidatePartner. -/
lemma aBridge_prod_eq_image_prod {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) (f : Fin n_A × Fin n_B → ℝ) :
    (∏ x ∈ N, f (a, x.2))
      = ∏ ab ∈ aBridgeSlots a N, f ab := by
  classical
  unfold aBridgeSlots
  rw [Finset.prod_image]
  intro x hx y hy h_eq
  have h_B : x.2 = y.2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
  by_contra h_ne
  exact (h_cand.2.2.2 x hx y hy h_ne) h_B

/-- B-bridge product equals product over the image. -/
lemma bBridge_prod_eq_image_prod {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) (f : Fin n_A × Fin n_B → ℝ) :
    (∏ x ∈ N, f (x.1, b))
      = ∏ ab ∈ bBridgeSlots b N, f ab := by
  classical
  unfold bBridgeSlots
  rw [Finset.prod_image]
  intro x hx y hy h_eq
  have h_A : x.1 = y.1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
  by_contra h_ne
  exact (h_cand.2.2.1 x hx y hy h_ne) h_A

/-- Within-N product equals product over the image (using offDiag). -/
lemma withinN_prod_eq_image_prod {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) (f : Fin n_A × Fin n_B → ℝ) :
    (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2), f (p.1.1, p.2.2))
      = ∏ ab ∈ withinNSlots N, f ab := by
  classical
  unfold withinNSlots
  rw [Finset.prod_image]
  intro p hp q hq h_eq
  -- hp, hq are now in Finset.mem form
  have hp' : p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2) := hp
  have hq' : q ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2) := hq
  rw [Finset.mem_filter, Finset.mem_product] at hp' hq'
  obtain ⟨⟨hp1, hp2⟩, _⟩ := hp'
  obtain ⟨⟨hq1, hq2⟩, _⟩ := hq'
  have h_A : p.1.1 = q.1.1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
  have h_B : p.2.2 = q.2.2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
  have h_p1_eq : p.1 = q.1 := by
    by_contra h_ne
    exact (h_cand.2.2.1 p.1 hp1 q.1 hq1 h_ne) h_A
  have h_p2_eq : p.2 = q.2 := by
    by_contra h_ne
    exact (h_cand.2.2.2 p.2 hp2 q.2 hq2 h_ne) h_B
  exact Prod.ext h_p1_eq h_p2_eq

/-- Re-express `if g y = true then 1 else 0` as `edgeIndicator y.1 y.2 g`. -/
lemma if_eq_edgeIndicator {n_A n_B : ℕ} (y : Fin n_A × Fin n_B)
    (g : Fin n_A × Fin n_B → Bool) :
    (if g y = true then (1 : ℝ) else 0)
      = DaveyThesis2024.BipartiteRandomGraph.edgeIndicator y.1 y.2 g := by
  unfold DaveyThesis2024.BipartiteRandomGraph.edgeIndicator
  show (if g y = true then (1 : ℝ) else 0) = if g (y.1, y.2) = true then 1 else 0
  congr 1

lemma if_eq_one_minus_edgeIndicator {n_A n_B : ℕ} (y : Fin n_A × Fin n_B)
    (g : Fin n_A × Fin n_B → Bool) :
    (if g y = true then (0 : ℝ) else 1)
      = 1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator y.1 y.2 g := by
  unfold DaveyThesis2024.BipartiteRandomGraph.edgeIndicator
  show (if g y = true then (0 : ℝ) else 1) = 1 - if g (y.1, y.2) = true then 1 else 0
  by_cases h : g y = true
  · rw [if_pos h]
    have : g (y.1, y.2) = true := h
    rw [if_pos this]; ring
  · rw [if_neg h]
    have : ¬ g (y.1, y.2) = true := h
    rw [if_neg this]; ring

/-- For candidate N: pointwise factoring of `matchingIndicator` as two products
(over presentSlots and absentSlots respectively). -/
lemma matchingIndicator_eq_product_form {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) (h_ab_notMem : (a, b) ∉ N)
    (g : Fin n_A × Fin n_B → Bool) :
    matchingIndicator a b N g
      = (∏ ab ∈ presentSlots a b N,
            DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g) *
        (∏ ab ∈ absentSlots a b N,
            (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g)) := by
  classical
  -- Step 1: rewrite first two factors as product over `presentSlots = insert (a,b) N`.
  have h_presentProd :
      (if g (a, b) = true then (1 : ℝ) else 0) * (∏ x ∈ N, if g x = true then (1 : ℝ) else 0)
        = ∏ ab ∈ presentSlots a b N,
            DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g := by
    unfold presentSlots
    rw [Finset.prod_insert h_ab_notMem]
    rw [if_eq_edgeIndicator (a, b) g]
    have h_N_re : (∏ x ∈ N, if g x = true then (1 : ℝ) else 0)
        = ∏ x ∈ N, DaveyThesis2024.BipartiteRandomGraph.edgeIndicator x.1 x.2 g := by
      apply Finset.prod_congr rfl
      intro x _; exact if_eq_edgeIndicator x g
    rw [h_N_re]
  -- Step 2: rewrite remaining 3 factors as product over absentSlots.
  have h_absentProd :
      (∏ x ∈ N, if g (a, x.2) = true then (0 : ℝ) else 1) *
      (∏ x ∈ N, if g (x.1, b) = true then (0 : ℝ) else 1) *
      (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
          if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1)
        = ∏ ab ∈ absentSlots a b N,
            (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g) := by
    -- Step 2a: convert each `if` factor to `1 - edgeIndicator`.
    have h_a_re : (∏ x ∈ N, if g (a, x.2) = true then (0 : ℝ) else 1)
        = ∏ x ∈ N,
            (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator (a, x.2).1 (a, x.2).2 g) := by
      apply Finset.prod_congr rfl
      intro x _; exact if_eq_one_minus_edgeIndicator (a, x.2) g
    have h_b_re : (∏ x ∈ N, if g (x.1, b) = true then (0 : ℝ) else 1)
        = ∏ x ∈ N,
            (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator (x.1, b).1 (x.1, b).2 g) := by
      apply Finset.prod_congr rfl
      intro x _; exact if_eq_one_minus_edgeIndicator (x.1, b) g
    have h_w_re : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
            if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1)
        = ∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
            (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator
                  (p.1.1, p.2.2).1 (p.1.1, p.2.2).2 g) := by
      apply Finset.prod_congr rfl
      intro p _; exact if_eq_one_minus_edgeIndicator (p.1.1, p.2.2) g
    rw [h_a_re, h_b_re, h_w_re]
    -- Step 2b: convert each product into a product over the image (aBridge / bBridge / within).
    rw [aBridge_prod_eq_image_prod a b N h_cand
        (fun ab => 1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g)]
    rw [bBridge_prod_eq_image_prod a b N h_cand
        (fun ab => 1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g)]
    rw [withinN_prod_eq_image_prod a b N h_cand
        (fun ab => 1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g)]
    -- Step 2c: combine the three image products into one product over the disjoint union.
    have h_disjoint_outer : Disjoint (aBridgeSlots a N ∪ bBridgeSlots b N) (withinNSlots N) := by
      rw [Finset.disjoint_union_left]
      exact ⟨aBridgeSlots_disjoint_withinNSlots a b N h_cand,
             bBridgeSlots_disjoint_withinNSlots a b N h_cand⟩
    have h_disjoint_inner : Disjoint (aBridgeSlots a N) (bBridgeSlots b N) :=
      aBridgeSlots_disjoint_bBridgeSlots a b N h_cand
    unfold absentSlots
    rw [Finset.prod_union h_disjoint_outer]
    rw [Finset.prod_union h_disjoint_inner]
  unfold matchingIndicator
  rw [← h_presentProd, ← h_absentProd]
  ring

/-! ### Per-candidate integration -/

open DaveyThesis2024.BipartiteRandomGraph in
/-- **Per-candidate integration formula (Step C-final).**

For a candidate `N ∈ candidatePartnerSet n_A n_B k a b`, the integral of `matchingIndicator a b N g`
over the bipartite edge-choice measure equals `p.toReal^k * (1 - p.toReal)^(k * (k - 1))`.

Strategy: rewrite `matchingIndicator` as a product over `allSlots = presentSlots ∪ absentSlots`
(a Finset of `k²` distinct slots). On `presentSlots` the factor is `edgeIndicator ab.1 ab.2`,
on `absentSlots` it is `1 - edgeIndicator ab.1 ab.2`. Both depend only on the slot `ab`, so they
are independent across the slot index `ab`. Apply `iIndepFun.integral_fun_prod_eq_prod_integral`
to factor the integral and evaluate each per-slot integral (`p.toReal` or `1 - p.toReal`). -/
lemma integral_matchingIndicator_eq
    {n_A n_B : ℕ} (k : ℕ) (h_k_pos : 0 < k)
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_candidate : N ∈ candidatePartnerSet n_A n_B k a b)
    (p : ENNReal) (hp_le : p ≤ 1) :
    ∫ g, matchingIndicator a b N g
        ∂((bipartiteEdgeChoice n_A n_B p hp_le).toMeasure)
      = p.toReal ^ k * (1 - p.toReal) ^ (k * (k - 1)) := by
  classical
  set μ := (bipartiteEdgeChoice n_A n_B p hp_le).toMeasure with hμ
  have h_cand : CandidatePartner a b N := (mem_candidatePartnerSet_iff k a b N |>.mp h_candidate).2.2
  have h_ab_notMem : (a, b) ∉ N := ab_not_mem_of_candidate k a b N h_candidate
  -- Step 1: rewrite matchingIndicator pointwise as a product over present/absent slots.
  have h_pres_card : (presentSlots a b N).card = k :=
    presentSlots_card_of_candidate k h_k_pos a b N h_candidate
  have h_abs_card : (absentSlots a b N).card = k * (k - 1) :=
    absentSlots_card_of_candidate k h_k_pos a b N h_candidate
  have h_disj : Disjoint (presentSlots a b N) (absentSlots a b N) :=
    presentSlots_disjoint_absentSlots a b N h_cand
  -- Step 2: define per-slot function g_slot and per-slot random variable X_slot.
  -- We index by ↥(presentSlots ∪ absentSlots).
  let S : Finset (Fin n_A × Fin n_B) := presentSlots a b N ∪ absentSlots a b N
  let g_slot : ↥S → ℝ → ℝ := fun i x =>
    if i.val ∈ presentSlots a b N then x else 1 - x
  let X_slot : ↥S → (Fin n_A × Fin n_B → Bool) → ℝ :=
    fun i f => edgeIndicator i.val.1 i.val.2 f
  -- Step 3: pointwise factorisation: matchingIndicator = ∏ i : ↥S, g_slot i (X_slot i f).
  have h_pointwise : ∀ f, matchingIndicator a b N f = ∏ i : ↥S, g_slot i (X_slot i f) := by
    intro f
    rw [matchingIndicator_eq_product_form a b N h_cand h_ab_notMem f]
    -- The RHS is a product over S = presentSlots ∪ absentSlots via the attach equivalence.
    have h_univ : (Finset.univ : Finset ↥S) = S.attach := rfl
    rw [h_univ, Finset.prod_attach S (fun ab : Fin n_A × Fin n_B =>
      if ab ∈ presentSlots a b N then edgeIndicator ab.1 ab.2 f
      else 1 - edgeIndicator ab.1 ab.2 f)]
    change (∏ ab ∈ presentSlots a b N, edgeIndicator ab.1 ab.2 f) *
         (∏ ab ∈ absentSlots a b N, (1 - edgeIndicator ab.1 ab.2 f))
       = ∏ ab ∈ presentSlots a b N ∪ absentSlots a b N,
          if ab ∈ presentSlots a b N then edgeIndicator ab.1 ab.2 f
          else 1 - edgeIndicator ab.1 ab.2 f
    rw [Finset.prod_union h_disj]
    -- Split each sub-product to use the if-then-else.
    have h_pres_re :
        (∏ ab ∈ presentSlots a b N, edgeIndicator ab.1 ab.2 f)
          = ∏ ab ∈ presentSlots a b N,
              if ab ∈ presentSlots a b N then edgeIndicator ab.1 ab.2 f
              else 1 - edgeIndicator ab.1 ab.2 f := by
      apply Finset.prod_congr rfl
      intro ab h_ab_in
      rw [if_pos h_ab_in]
    have h_abs_re :
        (∏ ab ∈ absentSlots a b N, (1 - edgeIndicator ab.1 ab.2 f))
          = ∏ ab ∈ absentSlots a b N,
              if ab ∈ presentSlots a b N then edgeIndicator ab.1 ab.2 f
              else 1 - edgeIndicator ab.1 ab.2 f := by
      apply Finset.prod_congr rfl
      intro ab h_ab_in
      have h_notIn : ab ∉ presentSlots a b N :=
        fun h => Finset.disjoint_left.mp h_disj h h_ab_in
      rw [if_neg h_notIn]
    rw [h_pres_re, h_abs_re]
  -- Step 4: integrate using iIndepFun.
  -- iIndepFun X_slot via .precomp on the full edgeIndicator iIndepFun.
  have h_inj : Function.Injective (fun i : ↥S => i.val) := Subtype.val_injective
  have h_iIndep_X : ProbabilityTheory.iIndepFun X_slot μ := by
    have h_full := DaveyThesis2024.SecRandomBipartite.edgeIndicator_full_iIndepFun (n_A := n_A) (n_B := n_B) p hp_le
    -- The full iIndepFun is indexed by Fin n_A × Fin n_B; precompose with Subtype.val.
    have h_pre := h_full.precomp (g := fun i : ↥S => i.val) h_inj
    -- h_pre : iIndepFun (fun i f => edgeIndicator (i.val).1 (i.val).2 f) μ
    -- but X_slot i f = edgeIndicator i.val.1 i.val.2 f. Defn equality.
    exact h_pre
  -- Measurability of g_slot per index.
  have h_g_meas : ∀ i, Measurable (g_slot i) := fun i => by
    by_cases h : i.val ∈ presentSlots a b N
    · simp only [g_slot, h, if_true]; exact measurable_id
    · simp only [g_slot, h, if_false]; fun_prop
  have h_X_meas : ∀ i, Measurable (X_slot i) := fun i =>
    measurable_edgeIndicator i.val.1 i.val.2
  -- iIndepFun (g_slot i ∘ X_slot i) via .comp.
  have h_iIndep_gX : ProbabilityTheory.iIndepFun
      (fun i f => g_slot i (X_slot i f)) μ := h_iIndep_X.comp g_slot h_g_meas
  -- Step 5: apply integral_fun_prod_eq_prod_integral.
  have h_aestrong : ∀ i, MeasureTheory.AEStronglyMeasurable (fun f => g_slot i (X_slot i f)) μ :=
    fun i => ((h_g_meas i).comp (h_X_meas i)).aestronglyMeasurable
  have h_int_eq :
      ∫ f, matchingIndicator a b N f ∂μ = ∫ f, ∏ i : ↥S, g_slot i (X_slot i f) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with f using h_pointwise f
  rw [h_int_eq]
  rw [h_iIndep_gX.integral_fun_prod_eq_prod_integral h_aestrong]
  -- Step 6: evaluate each per-slot integral.
  have h_each : ∀ i : ↥S,
      ∫ f, g_slot i (X_slot i f) ∂μ
        = if i.val ∈ presentSlots a b N then p.toReal else 1 - p.toReal := by
    intro i
    by_cases h : i.val ∈ presentSlots a b N
    · simp only [g_slot, h, if_true, X_slot, hμ]
      exact integral_edgeIndicator_eq p hp_le i.val.1 i.val.2
    · simp only [g_slot, h, if_false, X_slot, hμ]
      exact DaveyThesis2024.SecRandomBipartite.integral_complementEdgeIndicator_eq p hp_le i.val.1 i.val.2
  rw [Finset.prod_congr rfl (fun i _ => h_each i)]
  -- Step 7: ∏ i : ↥S, (if i.val ∈ pres then p else 1 - p) = p^k · (1-p)^(k(k-1)).
  have h_univ : (Finset.univ : Finset ↥S) = S.attach := rfl
  rw [h_univ]
  rw [Finset.prod_attach S (fun ab : Fin n_A × Fin n_B =>
    if ab ∈ presentSlots a b N then p.toReal else 1 - p.toReal)]
  change (∏ ab ∈ presentSlots a b N ∪ absentSlots a b N,
          if ab ∈ presentSlots a b N then p.toReal else 1 - p.toReal)
       = p.toReal ^ k * (1 - p.toReal) ^ (k * (k - 1))
  rw [Finset.prod_union h_disj]
  -- Split: ∏ ab ∈ pres, p · ∏ ab ∈ abs, (1-p) = p^|pres| · (1-p)^|abs|.
  have h_pres_eval :
      (∏ ab ∈ presentSlots a b N,
          if ab ∈ presentSlots a b N then p.toReal else 1 - p.toReal)
        = p.toReal ^ (presentSlots a b N).card := by
    rw [Finset.prod_congr rfl (fun ab h_ab => if_pos h_ab)]
    rw [Finset.prod_const]
  have h_abs_eval :
      (∏ ab ∈ absentSlots a b N,
          if ab ∈ presentSlots a b N then p.toReal else 1 - p.toReal)
        = (1 - p.toReal) ^ (absentSlots a b N).card := by
    apply Eq.trans
    · apply Finset.prod_congr rfl
      intro ab h_ab
      have h_notIn : ab ∉ presentSlots a b N :=
        fun h => Finset.disjoint_left.mp h_disj h h_ab
      rw [if_neg h_notIn]
    · rw [Finset.prod_const]
  rw [h_pres_eval, h_abs_eval, h_pres_card, h_abs_card]

/-! ## PS.4.b.6: cardinality of candidatePartnerSet (Step D)

`candidatePartnerSet n_A n_B k a b` has cardinality
`C(n_A - 1, k - 1) * C(n_B - 1, k - 1) * (k - 1)!`.

Strategy: build a bijection from candidates `N` to pairs `(A_set, f)` where
`A_set ⊆ univ.erase a` is a `(k-1)`-subset and `f : A_set ↪ univ.erase b` is
an injection. Each candidate `N` gives `A_set = N.image fst` (size `k-1` by
A-coord injectivity) and `f` extracts the unique B-coord paired with each A-coord. -/

/-- For a candidate N: `N.image fst ⊆ univ.erase a`. -/
lemma candidate_image_fst_subset {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePartnerSet n_A n_B k a b) :
    N.image Prod.fst ⊆ Finset.univ.erase a := by
  classical
  rw [mem_candidatePartnerSet_iff] at hN
  obtain ⟨_, _, h_cand⟩ := hN
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨y, hy, h_eq⟩ := hx
  rw [Finset.mem_erase]
  refine ⟨?_, Finset.mem_univ _⟩
  rw [← h_eq]
  exact h_cand.1 y hy

/-- For a candidate N: `(N.image fst).card = k - 1`. -/
lemma candidate_image_fst_card {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePartnerSet n_A n_B k a b) :
    (N.image Prod.fst).card = k - 1 := by
  classical
  rw [mem_candidatePartnerSet_iff] at hN
  obtain ⟨_, h_N_card, h_cand⟩ := hN
  rw [Finset.card_image_of_injOn, h_N_card]
  intro x hx y hy h_eq
  by_contra h_ne
  exact (h_cand.2.2.1 x hx y hy h_ne) h_eq

/-- For a candidate N: `N.image snd ⊆ univ.erase b` (B-coords distinct from `b`). -/
lemma candidate_image_snd_subset {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePartnerSet n_A n_B k a b) :
    N.image Prod.snd ⊆ Finset.univ.erase b := by
  classical
  rw [mem_candidatePartnerSet_iff] at hN
  obtain ⟨_, _, h_cand⟩ := hN
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨y, hy, h_eq⟩ := hx
  rw [Finset.mem_erase]
  refine ⟨?_, Finset.mem_univ _⟩
  rw [← h_eq]
  exact h_cand.2.1 y hy

/-- For a candidate N: `(N.image snd).card = k - 1`. -/
lemma candidate_image_snd_card {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePartnerSet n_A n_B k a b) :
    (N.image Prod.snd).card = k - 1 := by
  classical
  rw [mem_candidatePartnerSet_iff] at hN
  obtain ⟨_, h_N_card, h_cand⟩ := hN
  rw [Finset.card_image_of_injOn, h_N_card]
  intro x hx y hy h_eq
  by_contra h_ne
  exact (h_cand.2.2.2 x hx y hy h_ne) h_eq

/-- For each candidate N and each A-coord `x ∈ N.image fst`, there is a unique
B-coord paired with it: the B-coord of the element of N projecting to x. -/
noncomputable def candidatePairing_witness {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (_hN : N ∈ candidatePartnerSet n_A n_B k a b)
    (x : ↥(N.image Prod.fst)) :
    {y : Fin n_A × Fin n_B // y ∈ N ∧ y.1 = x.val} := by
  classical
  have hx : x.val ∈ N.image Prod.fst := x.property
  rw [Finset.mem_image] at hx
  exact ⟨Classical.choose hx,
    (Classical.choose_spec hx).1, (Classical.choose_spec hx).2⟩

noncomputable def candidatePairing {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePartnerSet n_A n_B k a b) :
    ↥(N.image Prod.fst) → Fin n_B :=
  fun x => (candidatePairing_witness k a b N hN x).val.2

/-- `candidatePairing` returns the B-coord of the corresponding N-element. -/
lemma candidatePairing_spec {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePartnerSet n_A n_B k a b)
    (x : ↥(N.image Prod.fst)) :
    (x.val, candidatePairing k a b N hN x) ∈ N := by
  classical
  unfold candidatePairing
  have h_props := (candidatePairing_witness k a b N hN x).property
  have h_in : (candidatePairing_witness k a b N hN x).val ∈ N := h_props.1
  have h_fst : (candidatePairing_witness k a b N hN x).val.1 = x.val := h_props.2
  -- Goal: (x.val, _.val.2) ∈ N.
  -- Use: _.val = (_.val.1, _.val.2) = (x.val, _.val.2).
  set y := (candidatePairing_witness k a b N hN x).val with hy_def
  have h_eq : (x.val, y.2) = y := by
    rw [← h_fst]
  rw [h_eq]
  exact h_in

/-- The candidatePairing lands in univ.erase b. -/
lemma candidatePairing_mem_erase {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePartnerSet n_A n_B k a b)
    (x : ↥(N.image Prod.fst)) :
    candidatePairing k a b N hN x ∈ (Finset.univ.erase b : Finset (Fin n_B)) := by
  classical
  have h_cand : CandidatePartner a b N := (mem_candidatePartnerSet_iff k a b N |>.mp hN).2.2
  have h_in : (x.val, candidatePairing k a b N hN x) ∈ N :=
    candidatePairing_spec k a b N hN x
  rw [Finset.mem_erase]
  refine ⟨?_, Finset.mem_univ _⟩
  -- B-coord ≠ b by candidate property.
  exact h_cand.2.1 (x.val, candidatePairing k a b N hN x) h_in

/-- The candidatePairing function (as injection) is injective. -/
lemma candidatePairing_injective {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePartnerSet n_A n_B k a b) :
    Function.Injective (candidatePairing k a b N hN) := by
  classical
  have h_cand : CandidatePartner a b N := (mem_candidatePartnerSet_iff k a b N |>.mp hN).2.2
  intro x y h_eq
  have hx_in : (x.val, candidatePairing k a b N hN x) ∈ N := candidatePairing_spec k a b N hN x
  have hy_in : (y.val, candidatePairing k a b N hN y) ∈ N := candidatePairing_spec k a b N hN y
  -- If x ≠ y as subtypes, then x.val ≠ y.val.
  by_contra h_ne_sub
  have h_val_ne : x.val ≠ y.val := fun h_eq_val => h_ne_sub (Subtype.ext h_eq_val)
  -- Two elements with same B-coord but different A-coords are forbidden.
  have h_xy_ne : ((x.val, candidatePairing k a b N hN x) : Fin n_A × Fin n_B)
      ≠ (y.val, candidatePairing k a b N hN y) := by
    intro h
    exact h_val_ne ((Prod.mk.injEq _ _ _ _).mp h).1
  -- B-coords equal: h_eq.
  exact (h_cand.2.2.2 _ hx_in _ hy_in h_xy_ne) h_eq

/-- Given A_set ⊆ univ.erase a of size k-1 and an embedding f : ↥A_set ↪ univ.erase b,
the constructed Finset of pairs (x, f x). -/
noncomputable def embToFiber {n_A n_B : ℕ}
    (b : Fin n_B) (A_set : Finset (Fin n_A))
    (f : ↥A_set ↪ ↥((Finset.univ.erase b : Finset (Fin n_B))))
    : Finset (Fin n_A × Fin n_B) :=
  A_set.attach.image (fun x => (x.val, (f x).val))

/-- Membership in `embToFiber`. -/
lemma mem_embToFiber {n_A n_B : ℕ}
    (b : Fin n_B) (A_set : Finset (Fin n_A))
    (f : ↥A_set ↪ ↥((Finset.univ.erase b : Finset (Fin n_B))))
    (ab : Fin n_A × Fin n_B) :
    ab ∈ embToFiber b A_set f ↔
      ∃ (h : ab.1 ∈ A_set), ab.2 = (f ⟨ab.1, h⟩).val := by
  classical
  unfold embToFiber
  rw [Finset.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, _, h_eq⟩
    have h1 : x.val = ab.1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
    have h2 : (f x).val = ab.2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
    have h_ab1_in : ab.1 ∈ A_set := h1 ▸ x.property
    refine ⟨h_ab1_in, ?_⟩
    -- Need: ab.2 = (f ⟨ab.1, h_ab1_in⟩).val.
    have h_x_eq : x = ⟨ab.1, h_ab1_in⟩ := Subtype.ext h1
    rw [← h2, h_x_eq]
  · rintro ⟨h, h_eq⟩
    refine ⟨⟨ab.1, h⟩, Finset.mem_attach _ _, ?_⟩
    change (ab.1, (f ⟨ab.1, h⟩).val) = ab
    rw [← h_eq]

/-- `embToFiber` is in `candidatePartnerSet`. -/
lemma embToFiber_mem_candidatePartnerSet {n_A n_B : ℕ} (k : ℕ) (_h_k_pos : 0 < k)
    (a : Fin n_A) (b : Fin n_B)
    (A_set : Finset (Fin n_A))
    (h_A_sub : A_set ⊆ Finset.univ.erase a) (h_A_card : A_set.card = k - 1)
    (f : ↥A_set ↪ ↥((Finset.univ.erase b : Finset (Fin n_B)))) :
    embToFiber b A_set f ∈ candidatePartnerSet n_A n_B k a b := by
  classical
  rw [mem_candidatePartnerSet_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- N ⊆ univ.erase (a, b).
    intro ab h_ab
    rw [mem_embToFiber] at h_ab
    obtain ⟨h_in_A, _⟩ := h_ab
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    have h_A_neq_a : ab.1 ≠ a := by
      have h_in_erase := h_A_sub h_in_A
      rw [Finset.mem_erase] at h_in_erase
      exact h_in_erase.1
    intro h; rw [Prod.mk.injEq] at h; exact h_A_neq_a h.1
  · -- card = k - 1.
    unfold embToFiber
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_attach, h_A_card]
    · intro x y h_eq
      exact Subtype.ext ((Prod.mk.injEq _ _ _ _).mp h_eq |>.1)
  · -- CandidatePartner: A-coord ≠ a.
    intro x h_x
    rw [mem_embToFiber] at h_x
    obtain ⟨h_in_A, _⟩ := h_x
    have h_in_erase := h_A_sub h_in_A
    rw [Finset.mem_erase] at h_in_erase
    exact h_in_erase.1
  · -- B-coord ≠ b.
    intro x h_x
    rw [mem_embToFiber] at h_x
    obtain ⟨h_in_A, h_eq⟩ := h_x
    rw [h_eq]
    have := (f ⟨x.1, h_in_A⟩).property
    rw [Finset.mem_erase] at this
    exact this.1
  · -- A-coords pairwise distinct.
    intro x h_x y h_y h_ne
    rw [mem_embToFiber] at h_x h_y
    obtain ⟨h_x_in, h_x_eq⟩ := h_x
    obtain ⟨h_y_in, h_y_eq⟩ := h_y
    -- Suppose x.1 = y.1, then x = y, contradicting h_ne.
    intro h_a_eq  -- h_a_eq : x.1 = y.1
    apply h_ne
    -- Need x = y.
    have h_sub_eq : (⟨x.1, h_x_in⟩ : ↥A_set) = ⟨y.1, h_y_in⟩ := Subtype.ext h_a_eq
    have h_2 : x.2 = y.2 := by
      rw [h_x_eq, h_y_eq, h_sub_eq]
    exact Prod.ext h_a_eq h_2
  · -- B-coords pairwise distinct.
    intro x h_x y h_y h_ne
    rw [mem_embToFiber] at h_x h_y
    obtain ⟨h_x_in, h_x_eq⟩ := h_x
    obtain ⟨h_y_in, h_y_eq⟩ := h_y
    intro h_b_eq  -- h_b_eq : x.2 = y.2
    apply h_ne
    rw [h_x_eq, h_y_eq] at h_b_eq
    have h_sub_eq : f ⟨x.1, h_x_in⟩ = f ⟨y.1, h_y_in⟩ := Subtype.ext h_b_eq
    have h_pre_eq : ((⟨x.1, h_x_in⟩ : ↥A_set)) = ⟨y.1, h_y_in⟩ := f.injective h_sub_eq
    have h_fst_eq : x.1 = y.1 := congrArg Subtype.val h_pre_eq
    have h_2 : x.2 = y.2 := by
      rw [h_x_eq, h_y_eq, h_pre_eq]
    exact Prod.ext h_fst_eq h_2

/-- `embToFiber b A_set f` has A-projection equal to `A_set`. -/
lemma embToFiber_image_fst {n_A n_B : ℕ}
    (b : Fin n_B) (A_set : Finset (Fin n_A))
    (f : ↥A_set ↪ ↥((Finset.univ.erase b : Finset (Fin n_B)))) :
    (embToFiber b A_set f).image Prod.fst = A_set := by
  classical
  ext x
  rw [Finset.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨ab, h_ab, h_eq⟩
    rw [mem_embToFiber] at h_ab
    obtain ⟨h_in, _⟩ := h_ab
    rw [← h_eq]; exact h_in
  · intro h_x
    refine ⟨(x, (f ⟨x, h_x⟩).val), ?_, rfl⟩
    rw [mem_embToFiber]
    exact ⟨h_x, rfl⟩

open Finset in
/-- **Step D: cardinality of `candidatePartnerSet`.**

`(candidatePartnerSet n_A n_B k a b).card = C(n_A - 1, k - 1) * C(n_B - 1, k - 1) * (k - 1)!`.

Strategy: fiber decomposition over A-projection. The number of A-sets of size k-1 in
`univ.erase a` is `C(n_A - 1, k - 1)`. Each A-set has fiber of size
`(n_B - 1).descFactorial (k - 1) = (k - 1)! * C(n_B - 1, k - 1)`. -/
lemma candidatePartnerSet_card
    {n_A n_B : ℕ} (k : ℕ) (h_k_pos : 0 < k) (_h_k_le_A : k ≤ n_A) (_h_k_le_B : k ≤ n_B)
    (a : Fin n_A) (b : Fin n_B) :
    (candidatePartnerSet n_A n_B k a b).card
      = Nat.choose (n_A - 1) (k - 1) * Nat.choose (n_B - 1) (k - 1) * Nat.factorial (k - 1) := by
  classical
  -- Step 1: fiber decomposition by A-projection.
  have h_fiber :
      Set.MapsTo (fun N : Finset (Fin n_A × Fin n_B) => N.image Prod.fst)
        ((candidatePartnerSet n_A n_B k a b : Finset _) : Set _)
        (((Finset.univ.erase a : Finset (Fin n_A)).powersetCard (k - 1) : Finset _) : Set _) := by
    intro N hN
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    have hN' : N ∈ candidatePartnerSet n_A n_B k a b := hN
    exact ⟨candidate_image_fst_subset k a b N hN', candidate_image_fst_card k a b N hN'⟩
  rw [Finset.card_eq_sum_card_fiberwise h_fiber]
  -- Step 2: each fiber has the same size = (n_B - 1).descFactorial (k - 1).
  have h_each_fiber : ∀ A_set ∈ (Finset.univ.erase a : Finset (Fin n_A)).powersetCard (k - 1),
      ((candidatePartnerSet n_A n_B k a b).filter (fun N => N.image Prod.fst = A_set)).card
        = (n_B - 1).descFactorial (k - 1) := by
    intro A_set h_A_set
    rw [Finset.mem_powersetCard] at h_A_set
    obtain ⟨h_A_sub, h_A_card⟩ := h_A_set
    -- Express RHS as Fintype.card of embeddings.
    rw [show (n_B - 1).descFactorial (k - 1)
          = Fintype.card (↥A_set ↪ ↥((Finset.univ.erase b : Finset (Fin n_B)))) by
      rw [Fintype.card_embedding_eq]
      have hA_card : Fintype.card ↥A_set = k - 1 := by rw [Fintype.card_coe, h_A_card]
      have hB_card : Fintype.card ↥((Finset.univ.erase b : Finset (Fin n_B))) = n_B - 1 := by
        rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _),
            Finset.card_univ, Fintype.card_fin]
      rw [hA_card, hB_card]]
    -- Use Finset.card_bij with the forward direction N ↦ candidatePairing N.
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    -- Construct the bijection.
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- toFun: N ↦ embedding via candidatePairing.
      intro N
      have h_N_mem := N.property
      have h_N_cand : N.val ∈ candidatePartnerSet n_A n_B k a b :=
        (Finset.mem_filter.mp h_N_mem).1
      have h_N_image : N.val.image Prod.fst = A_set :=
        (Finset.mem_filter.mp h_N_mem).2
      refine
        { toFun := fun x => ⟨candidatePairing k a b N.val h_N_cand ⟨x.val, ?_⟩, ?_⟩,
          inj' := ?_ }
      · rw [h_N_image]; exact x.property
      · exact candidatePairing_mem_erase k a b N.val h_N_cand _
      · intro x y h_eq
        have h_inj := candidatePairing_injective k a b N.val h_N_cand
        -- h_eq : ⟨candidatePairing ..., _⟩ = ⟨candidatePairing ..., _⟩ (as Subtype of erase b).
        -- Extract: candidatePairing x_in = candidatePairing y_in.
        have h_pair_eq : candidatePairing k a b N.val h_N_cand ⟨x.val, by rw [h_N_image]; exact x.property⟩
            = candidatePairing k a b N.val h_N_cand ⟨y.val, by rw [h_N_image]; exact y.property⟩ :=
          congrArg Subtype.val h_eq
        have h_sub_eq :
            ((⟨x.val, by rw [h_N_image]; exact x.property⟩ : ↥(N.val.image Prod.fst)))
              = ⟨y.val, by rw [h_N_image]; exact y.property⟩ := h_inj h_pair_eq
        -- h_sub_eq is equality of two Subtype elements; extract their val equality.
        have h_val_eq : x.val = y.val := by
          have := congrArg Subtype.val h_sub_eq
          exact this
        exact Subtype.ext h_val_eq
    · -- invFun: f ↦ embToFiber b A_set f.
      intro f
      refine ⟨embToFiber b A_set f, ?_⟩
      refine Finset.mem_filter.mpr
        ⟨embToFiber_mem_candidatePartnerSet k h_k_pos a b A_set h_A_sub h_A_card f,
         embToFiber_image_fst b A_set f⟩
    · -- left_inv: fiberToEmb (embToFiber f) = f, viewing in the coerced fiber subset.
      -- This is `LeftInverse invFun toFun`, i.e. for each N, invFun (toFun N) = N.
      intro N
      apply Subtype.ext
      have h_N_mem := N.property
      have h_N_cand : N.val ∈ candidatePartnerSet n_A n_B k a b :=
        (Finset.mem_filter.mp h_N_mem).1
      have h_N_image : N.val.image Prod.fst = A_set :=
        (Finset.mem_filter.mp h_N_mem).2
      have h_N_card_eq : N.val.card = k - 1 := (mem_candidatePartnerSet_iff k a b _).mp h_N_cand |>.2.1
      -- Define the embedding produced by toFun.
      let toF : ↥A_set ↪ ↥(Finset.univ.erase b : Finset (Fin n_B)) :=
        { toFun := fun x => ⟨candidatePairing k a b N.val h_N_cand ⟨x.val, by
              rw [h_N_image]; exact x.property⟩,
            candidatePairing_mem_erase k a b N.val h_N_cand _⟩,
          inj' := by
            intro x y h_eq
            have h_inj := candidatePairing_injective k a b N.val h_N_cand
            have h_pair_eq : candidatePairing k a b N.val h_N_cand
                ⟨x.val, by rw [h_N_image]; exact x.property⟩
              = candidatePairing k a b N.val h_N_cand
                ⟨y.val, by rw [h_N_image]; exact y.property⟩ :=
              congrArg Subtype.val h_eq
            have h_sub_eq :
                ((⟨x.val, by rw [h_N_image]; exact x.property⟩ : ↥(N.val.image Prod.fst)))
                  = ⟨y.val, by rw [h_N_image]; exact y.property⟩ := h_inj h_pair_eq
            have h_val_eq : x.val = y.val := by
              have := congrArg Subtype.val h_sub_eq
              exact this
            exact Subtype.ext h_val_eq }
      -- Goal: embToFiber b A_set toF = N.val.
      change embToFiber b A_set toF = N.val
      have h_sub : embToFiber b A_set toF ⊆ N.val := by
        intro ab h_ab
        rw [mem_embToFiber] at h_ab
        obtain ⟨h_in_A, h_eq⟩ := h_ab
        -- h_eq : ab.2 = (toF ⟨ab.1, h_in_A⟩).val.
        -- (toF ⟨ab.1, h_in_A⟩).val = candidatePairing _ _ _ _ ⟨ab.1, _⟩ by defn of toF.
        have h_pair := candidatePairing_spec k a b N.val h_N_cand
          ⟨ab.1, by rw [h_N_image]; exact h_in_A⟩
        have h_b_eq : ab.2 = candidatePairing k a b N.val h_N_cand
            ⟨ab.1, by rw [h_N_image]; exact h_in_A⟩ := h_eq
        have h_ab_eq : ab = (ab.1, candidatePairing k a b N.val h_N_cand
            ⟨ab.1, by rw [h_N_image]; exact h_in_A⟩) :=
          Prod.ext rfl h_b_eq
        rw [h_ab_eq]
        exact h_pair
      have h_card_eq :
          (embToFiber b A_set toF).card = N.val.card := by
        unfold embToFiber
        rw [Finset.card_image_of_injective, Finset.card_attach, h_A_card, h_N_card_eq]
        intro x y h_eq
        exact Subtype.ext ((Prod.mk.injEq _ _ _ _).mp h_eq |>.1)
      exact Finset.eq_of_subset_of_card_le h_sub h_card_eq.ge
    · -- right_inv: for each f, fiberToEmb (embToFiber f) = f.
      intro f
      apply DFunLike.ext
      intro x
      apply Subtype.ext
      -- Need: (toFun ⟨embToFiber b A_set f, _⟩ x).val = (f x).val.
      -- toFun produces ⟨candidatePairing _ ⟨x.val, _⟩, _⟩, whose .val is candidatePairing's output.
      -- candidatePairing_spec gives that (x.val, candidatePairing output) ∈ N = embToFiber.
      -- By def of embToFiber, the unique pair with A-coord x.val is (x.val, (f x).val).
      -- By candidate A-coord injectivity: candidatePairing output = (f x).val.
      set N := embToFiber b A_set f
      have h_N_in_filter : N ∈ (candidatePartnerSet n_A n_B k a b).filter
          (fun N' => N'.image Prod.fst = A_set) :=
        Finset.mem_filter.mpr ⟨embToFiber_mem_candidatePartnerSet k h_k_pos a b A_set
            h_A_sub h_A_card f, embToFiber_image_fst b A_set f⟩
      have h_N_cand : N ∈ candidatePartnerSet n_A n_B k a b := (Finset.mem_filter.mp h_N_in_filter).1
      have h_N_image : N.image Prod.fst = A_set := (Finset.mem_filter.mp h_N_in_filter).2
      have h_pair := candidatePairing_spec k a b N h_N_cand
        ⟨x.val, by rw [h_N_image]; exact x.property⟩
      -- h_pair : (x.val, candidatePairing _) ∈ N.
      -- N = embToFiber b A_set f, so (x.val, (f x).val) ∈ N.
      have h_target : (x.val, (f x).val) ∈ N := by
        rw [show N = embToFiber b A_set f from rfl, mem_embToFiber]
        exact ⟨x.property, rfl⟩
      -- A-coord injectivity in N: if two elements share A-coord, they're equal.
      have h_cand_prop : CandidatePartner a b N := (mem_candidatePartnerSet_iff k a b N).mp h_N_cand |>.2.2
      have h_uniq : (x.val, candidatePairing k a b N h_N_cand
          ⟨x.val, by rw [h_N_image]; exact x.property⟩) = (x.val, (f x).val) := by
        by_contra h_ne
        have h_A_clash : (x.val, candidatePairing k a b N h_N_cand
            ⟨x.val, by rw [h_N_image]; exact x.property⟩).1 ≠ (x.val, (f x).val).1 :=
          h_cand_prop.2.2.1 _ h_pair _ h_target h_ne
        exact h_A_clash rfl
      exact ((Prod.mk.injEq _ _ _ _).mp h_uniq).2
  rw [Finset.sum_congr rfl h_each_fiber]
  rw [Finset.sum_const]
  rw [Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  ring

/-! ## PS.4.b.7: headline integral identity (Step E)

Combining Steps B, C-final, and D:
`∫ count(g) * 1[g(a,b)] dμ = |candidatePartnerSet| * p^k * (1-p)^(k(k-1))`
`= C(n_A-1, k-1) * C(n_B-1, k-1) * (k-1)! * p^k * (1-p)^(k(k-1))`
`= p * expectedDegreeFormula n_A n_B k p.toReal`.

Note: the factor `p^k` (not `p^(k-1)`) arises because the integration includes the
edge `(a,b)` itself as a "present" slot. This means the integral identity yields
`p · E[D(e) | (a,b) ∈ E(G)]` (the unconditional expectation), matching the docstring
form `E[D(e)] = p · E[D(e) | (a,b) ∈ E(G)]`. The `(k - 1)` exponent in
`expectedDegreeFormula` reflects the *conditional* expectation. -/

open DaveyThesis2024.BipartiteRandomGraph in
open MeasureTheory in
/-- **Headline integral identity (Step E).**

For a random bipartite graph `G ~ G(n_A, n_B, p)` and a fixed edge slot `(a, b)`:

  `E[|{ M ∈ F_k(G) : (a, b) ∈ M }| · 1[(a, b) ∈ E(G)]]`
    `= |candidatePartnerSet n_A n_B k a b| · p^k · (1 - p)^(k * (k - 1))`
    `= p · expectedDegreeFormula n_A n_B k p`.

Strategy: composition of Steps B (`count_mul_indicator_eq_sum_matchingIndicator`),
C-final (`integral_matchingIndicator_eq`), and D (`candidatePartnerSet_card`). -/
theorem expectation_inducedKMatchings_with_edge
    {n_A n_B : ℕ}
    (k : ℕ) (h_k_pos : 0 < k) (_h_k_le_A : k ≤ n_A) (_h_k_le_B : k ≤ n_B)
    (p : ENNReal) (hp_le : p ≤ 1)
    (a : Fin n_A) (b : Fin n_B) :
    ∫ g, (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
        (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
        Finset.univ Finset.univ k).filter (fun M => (a, b) ∈ M)).card : ℝ) *
        (if g (a, b) = true then (1 : ℝ) else 0)
      ∂((bipartiteEdgeChoice n_A n_B p hp_le).toMeasure)
    = p.toReal ^ k * (1 - p.toReal) ^ (k * (k - 1))
        * ((Nat.choose (n_A - 1) (k - 1) : ℝ)
            * (Nat.choose (n_B - 1) (k - 1) : ℝ)
            * (Nat.factorial (k - 1) : ℝ)) := by
  classical
  set μ := (bipartiteEdgeChoice n_A n_B p hp_le).toMeasure with hμ_def
  -- Step B: pointwise rewriting.
  have h_pointwise : ∀ g,
      (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
          (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
          Finset.univ Finset.univ k).filter (fun M => (a, b) ∈ M)).card : ℝ) *
          (if g (a, b) = true then (1 : ℝ) else 0)
        = ∑ N ∈ ((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a, b)).powersetCard (k - 1),
            matchingIndicator a b N g := by
    intro g
    exact count_mul_indicator_eq_sum_matchingIndicator k h_k_pos a b g
  -- Step B (cont'd): swap integral and pointwise rewriting.
  have h_int_pointwise :
      ∫ g, (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
          (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
          Finset.univ Finset.univ k).filter (fun M => (a, b) ∈ M)).card : ℝ) *
          (if g (a, b) = true then (1 : ℝ) else 0)
        ∂μ
      = ∫ g, (∑ N ∈ ((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a, b)).powersetCard (k - 1),
              matchingIndicator a b N g) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with g using h_pointwise g
  rw [h_int_pointwise]
  -- Step B (cont'd): pull integral inside the finite sum.
  -- Use MeasureTheory.integral_finset_sum.
  have h_integrable : ∀ N ∈ ((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a, b)).powersetCard (k - 1),
      MeasureTheory.Integrable (fun g => matchingIndicator a b N g) μ := by
    intro N _
    refine (MeasureTheory.integrable_const (1 : ℝ)).mono'
      (by exact Measurable.of_discrete.aestronglyMeasurable) ?_
    filter_upwards with g
    rcases matchingIndicator_eq_zero_or_one a b N g with h | h
    · rw [h]; simp
    · rw [h]; simp
  rw [MeasureTheory.integral_finset_sum _ h_integrable]
  -- Now: ∑ N, ∫ matchingIndicator a b N g dμ = expectedDegreeFormula form.
  -- For N ∈ candidatePartnerSet: integral = p^k * (1-p)^(k(k-1)).
  -- For N ∉ candidatePartnerSet: integral = 0.
  -- Restrict to candidatePartnerSet and combine.
  have h_each_integral :
      ∀ N ∈ ((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a, b)).powersetCard (k - 1),
        ∫ g, matchingIndicator a b N g ∂μ
          = if N ∈ candidatePartnerSet n_A n_B k a b then
              p.toReal ^ k * (1 - p.toReal) ^ (k * (k - 1))
            else 0 := by
    intro N hN
    by_cases h_cand : N ∈ candidatePartnerSet n_A n_B k a b
    · rw [if_pos h_cand]
      exact integral_matchingIndicator_eq k h_k_pos a b N h_cand p hp_le
    · rw [if_neg h_cand]
      -- ∫ matchingIndicator = ∫ 0 = 0 via matchingIndicator_eq_zero_of_not_candidate.
      have h_zero : (fun g => matchingIndicator a b N g) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
        filter_upwards with g
        exact matchingIndicator_eq_zero_of_not_candidate k h_k_pos a b N hN h_cand g
      rw [MeasureTheory.integral_congr_ae h_zero, MeasureTheory.integral_zero]
  rw [Finset.sum_congr rfl h_each_integral]
  -- Now: ∑ N, (if N ∈ candidatePartnerSet then ... else 0)
  -- = ∑ N ∈ candidatePartnerSet, p^k * (1-p)^(k(k-1)) using sum_filter.
  -- candidatePartnerSet ⊆ (univ.erase (a,b)).powersetCard (k-1) by construction.
  rw [← Finset.sum_filter]
  -- The filtered set is exactly candidatePartnerSet.
  have h_filter_eq :
      (((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a, b)).powersetCard (k - 1)).filter
        (fun N => N ∈ candidatePartnerSet n_A n_B k a b)
      = candidatePartnerSet n_A n_B k a b := by
    ext N
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, h_in⟩
      exact h_in
    · intro h_in
      refine ⟨?_, h_in⟩
      rw [mem_candidatePartnerSet_iff] at h_in
      rw [Finset.mem_powersetCard]
      exact ⟨h_in.1, h_in.2.1⟩
  rw [h_filter_eq]
  rw [Finset.sum_const]
  rw [candidatePartnerSet_card k h_k_pos _h_k_le_A _h_k_le_B a b]
  ring

/-! ## PS.4.c: codegree integral identity

This section mirrors PS.4.b but for two fixed edges `e_1 = (a_1, b_1)` and
`e_2 = (a_2, b_2)` with distinct A-coords, distinct B-coords, and no bridging
cross-edges in `G`. The target identity is

  `E[|{ M ∈ F_k(G) : e_1, e_2 ∈ M }| · 1[e_1 ∈ E(G)] · 1[e_2 ∈ E(G)]
        · 1[(a_1, b_2) ∉ E(G)] · 1[(a_2, b_1) ∉ E(G)]]
    = |candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2| · p^k · (1 - p)^(k * (k - 1))
    = C(n_A - 2, k - 2) · C(n_B - 2, k - 2) · (k - 2)! · p^k · (1 - p)^(k * (k - 1))`.

The codegree analog is structurally parallel to PS.4.b: bijection on matchings
containing both edges → graph-independent candidate universe with pairwise-distinct
A-coords / B-coords / avoiding `{a_1, a_2}` / `{b_1, b_2}` → per-candidate integration
over `k` present slots and `k(k-1)` absent slots → cardinality count via `(k-2)`-subset
fiber decomposition.

The integration includes the two given edges themselves as "present" slots, plus
the two "no-bridge" cross-edges `(a_1, b_2), (a_2, b_1)` as "absent" slots. Hence
the total exponent budget is `k` present + `k(k-1)` absent = `k^2`, matching the
PS.4.b structure with the two-edge anchor. -/

/-- Erasing `(a_1, b_1)` and `(a_2, b_2)` from a `k`-induced-matching containing
both yields a `(k-2)`-subset. -/
lemma inducedKMatching_erase_pair_card
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B)) (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (M : Finset (Fin n_A × Fin n_B))
    (h_mem : M ∈ inducedKMatchings G S T_set k)
    (h_e1 : (a_1, b_1) ∈ M) (h_e2 : (a_2, b_2) ∈ M)
    (h_distinct : (a_1, b_1) ≠ (a_2, b_2)) :
    ((M.erase (a_1, b_1)).erase (a_2, b_2)).card = k - 2 := by
  have h_card : M.card = k := ((mem_inducedKMatchings_iff G S T_set k M).mp h_mem).2.1
  have h_e2_in_erase : (a_2, b_2) ∈ M.erase (a_1, b_1) := by
    rw [Finset.mem_erase]; exact ⟨fun h => h_distinct h.symm, h_e2⟩
  rw [Finset.card_erase_of_mem h_e2_in_erase, Finset.card_erase_of_mem h_e1, h_card]
  -- k - 1 - 1 = k - 2 requires no positivity since Nat subtraction handles negatives by 0.
  omega

/-- Predicate (decidable via `Classical`) on `N`: `insert (a_1,b_1) (insert (a_2,b_2) N)`
is an induced matching, and both edges lie in `crossBlockPairs G`. This is the
abstracted RHS of the pair matching-erase bijection. -/
noncomputable def validErasePairPartner
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B))
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) : Prop :=
  (a_1, b_1) ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G S T_set ∧
  (a_2, b_2) ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G S T_set ∧
  DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G
    (insert (a_1, b_1) (insert (a_2, b_2) N))

noncomputable instance validErasePairPartner_decidable
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B))
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) :
    Decidable (validErasePairPartner G S T_set a_1 a_2 b_1 b_2 N) :=
  Classical.propDecidable _

/-- Convert a filter on `inducedKMatchings` containing both `(a_1,b_1)` and `(a_2,b_2)`
to a filter on the ambient `powersetCard` by erasing both. -/
lemma inducedKMatchings_filter_mem_pair_image_erase
    {n_A n_B : ℕ}
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B)) (k : ℕ) (_h_k_ge_2 : 2 ≤ k)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_a_distinct : a_1 ≠ a_2) (_h_b_distinct : b_1 ≠ b_2) :
    ((inducedKMatchings G S T_set k).filter
        (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card
      = (((((DaveyThesis2024.SecRandomBipartite.crossBlockPairs G S T_set).erase (a_1, b_1)).erase
            (a_2, b_2)).powersetCard (k - 2)).filter
          (validErasePairPartner G S T_set a_1 a_2 b_1 b_2)).card := by
  classical
  have h_e_distinct : (a_1, b_1) ≠ (a_2, b_2) := fun h =>
    h_a_distinct (by simpa using congrArg Prod.fst h)
  apply Finset.card_bij
    (fun M (_h : M ∈ _) => (M.erase (a_1, b_1)).erase (a_2, b_2))
  · -- maps into the target Finset
    intro M hM
    simp only [Finset.mem_filter] at hM
    obtain ⟨h_mem, h_e1, h_e2⟩ := hM
    have h_iff := (mem_inducedKMatchings_iff G S T_set k M).mp h_mem
    have h_sub : M ⊆ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G S T_set := h_iff.1
    have h_card : M.card = k := h_iff.2.1
    have h_match : DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G M := h_iff.2.2
    have h_e1_cross : (a_1, b_1) ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G S T_set := h_sub h_e1
    have h_e2_cross : (a_2, b_2) ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G S T_set := h_sub h_e2
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
      · -- (M.erase (a_1,b_1)).erase (a_2,b_2) ⊆ ((cross).erase (a_1,b_1)).erase (a_2,b_2)
        intro x hx
        rw [Finset.mem_erase] at hx
        obtain ⟨hx_ne2, hx_in1⟩ := hx
        rw [Finset.mem_erase] at hx_in1
        obtain ⟨hx_ne1, hx_in⟩ := hx_in1
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨hx_ne2, hx_ne1, h_sub hx_in⟩
      · exact inducedKMatching_erase_pair_card G S T_set k a_1 a_2 b_1 b_2 M h_mem h_e1 h_e2
          h_e_distinct
    · refine ⟨h_e1_cross, h_e2_cross, ?_⟩
      -- insert (a_1,b_1) (insert (a_2,b_2) ((M.erase ..).erase ..)) = M
      have h_step : insert (a_2, b_2) ((M.erase (a_1, b_1)).erase (a_2, b_2))
          = M.erase (a_1, b_1) := by
        apply Finset.insert_erase
        rw [Finset.mem_erase]
        exact ⟨fun h => h_e_distinct h.symm, h_e2⟩
      rw [h_step, Finset.insert_erase h_e1]
      exact h_match
  · -- injectivity
    intro M₁ hM₁ M₂ hM₂ h_eq
    simp only [Finset.mem_filter] at hM₁ hM₂
    obtain ⟨_, h_e1₁, h_e2₁⟩ := hM₁
    obtain ⟨_, h_e1₂, h_e2₂⟩ := hM₂
    -- Recover M₁ = insert e1 (insert e2 (M₁.erase e1).erase e2) and same for M₂.
    have h_e2₁_in : (a_2, b_2) ∈ M₁.erase (a_1, b_1) := by
      rw [Finset.mem_erase]; exact ⟨fun h => h_e_distinct h.symm, h_e2₁⟩
    have h_e2₂_in : (a_2, b_2) ∈ M₂.erase (a_1, b_1) := by
      rw [Finset.mem_erase]; exact ⟨fun h => h_e_distinct h.symm, h_e2₂⟩
    have h₁ : insert (a_2, b_2) ((M₁.erase (a_1, b_1)).erase (a_2, b_2)) = M₁.erase (a_1, b_1) :=
      Finset.insert_erase h_e2₁_in
    have h₂ : insert (a_2, b_2) ((M₂.erase (a_1, b_1)).erase (a_2, b_2)) = M₂.erase (a_1, b_1) :=
      Finset.insert_erase h_e2₂_in
    have h_step1 : M₁.erase (a_1, b_1) = M₂.erase (a_1, b_1) := by
      rw [← h₁, ← h₂, h_eq]
    have h_M₁ : insert (a_1, b_1) (M₁.erase (a_1, b_1)) = M₁ := Finset.insert_erase h_e1₁
    have h_M₂ : insert (a_1, b_1) (M₂.erase (a_1, b_1)) = M₂ := Finset.insert_erase h_e1₂
    rw [← h_M₁, ← h_M₂, h_step1]
  · -- surjectivity
    intro N hN
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hN
    obtain ⟨⟨h_sub, h_card⟩, h_e1_cross, h_e2_cross, h_match⟩ := hN
    -- Construct M = insert (a_1, b_1) (insert (a_2, b_2) N).
    have h_e2_notMem_N : (a_2, b_2) ∉ N := by
      intro h
      have := h_sub h
      rw [Finset.mem_erase] at this
      exact this.1 rfl
    have h_e1_notMem_N : (a_1, b_1) ∉ N := by
      intro h
      have := h_sub h
      rw [Finset.mem_erase] at this
      rw [Finset.mem_erase] at this  -- inner erase too
      exact this.2.1 rfl
    have h_e1_notMem_step : (a_1, b_1) ∉ insert (a_2, b_2) N := by
      rw [Finset.mem_insert]
      push_neg
      exact ⟨h_e_distinct, h_e1_notMem_N⟩
    refine ⟨insert (a_1, b_1) (insert (a_2, b_2) N), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩
      · refine (mem_inducedKMatchings_iff G S T_set k _).mpr ⟨?_, ?_, h_match⟩
        · intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with hx | hx
          · rw [hx]; exact h_e1_cross
          · rw [Finset.mem_insert] at hx
            rcases hx with hx | hx
            · rw [hx]; exact h_e2_cross
            · -- x ∈ N ⊆ ((cross).erase e1).erase e2 ⊆ cross
              have := h_sub hx
              rw [Finset.mem_erase, Finset.mem_erase] at this
              exact this.2.2
        · rw [Finset.card_insert_of_notMem h_e1_notMem_step,
              Finset.card_insert_of_notMem h_e2_notMem_N, h_card]
          omega
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · -- (insert e1 (insert e2 N)).erase e1).erase e2 = N
      have h_erase1 : (insert (a_1, b_1) (insert (a_2, b_2) N)).erase (a_1, b_1)
          = insert (a_2, b_2) N :=
        Finset.erase_insert h_e1_notMem_step
      rw [h_erase1, Finset.erase_insert h_e2_notMem_N]

/-! ## PS.4.c.2: candidatePairPartnerSet + matchingPairIndicator

Graph-independent universe of `(k-2)`-subsets that could complete a `k`-induced
matching containing `{(a_1, b_1), (a_2, b_2)}`. The candidate predicate forbids
`a_1`, `a_2` from N's A-coords, forbids `b_1`, `b_2` from N's B-coords, and
demands pairwise distinctness of A-coords and B-coords within N. -/

/-- Structural (graph-independent) candidate predicate for a `(k-2)`-subset N
that, together with `{(a_1, b_1), (a_2, b_2)}`, could form a `k`-induced
matching. -/
def CandidatePairPartner
    {n_A n_B : ℕ} (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) : Prop :=
  (∀ x ∈ N, x.1 ≠ a_1) ∧
  (∀ x ∈ N, x.1 ≠ a_2) ∧
  (∀ x ∈ N, x.2 ≠ b_1) ∧
  (∀ x ∈ N, x.2 ≠ b_2) ∧
  (∀ x ∈ N, ∀ y ∈ N, x ≠ y → x.1 ≠ y.1) ∧
  (∀ x ∈ N, ∀ y ∈ N, x ≠ y → x.2 ≠ y.2)

noncomputable instance CandidatePairPartner_decidable
    {n_A n_B : ℕ} (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) :
    Decidable (CandidatePairPartner a_1 a_2 b_1 b_2 N) := Classical.propDecidable _

/-- The graph-independent universe of candidate pair erase-partners for
`{(a_1, b_1), (a_2, b_2)}`: `(k-2)`-subsets of
`((univ.erase (a_1, b_1)).erase (a_2, b_2))` satisfying `CandidatePairPartner`. -/
noncomputable def candidatePairPartnerSet
    (n_A n_B : ℕ) (k : ℕ) (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) :
    Finset (Finset (Fin n_A × Fin n_B)) :=
  (((Finset.univ.erase (a_1, b_1)).erase (a_2, b_2)).powersetCard (k - 2)).filter
    (CandidatePairPartner a_1 a_2 b_1 b_2)

lemma mem_candidatePairPartnerSet_iff
    {n_A n_B : ℕ} (k : ℕ) (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) :
    N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2 ↔
      N ⊆ (Finset.univ.erase (a_1, b_1)).erase (a_2, b_2) ∧
      N.card = k - 2 ∧
      CandidatePairPartner a_1 a_2 b_1 b_2 N := by
  unfold candidatePairPartnerSet
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  tauto

/-- `(a_1, b_1) ∉ N` and `(a_2, b_2) ∉ N` when `N ∈ candidatePairPartnerSet`. -/
lemma e1_e2_notMem_of_candidatePair {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2) :
    (a_1, b_1) ∉ N ∧ (a_2, b_2) ∉ N := by
  rw [mem_candidatePairPartnerSet_iff] at hN
  obtain ⟨h_sub, _, _⟩ := hN
  refine ⟨?_, ?_⟩
  · intro h
    have := h_sub h
    rw [Finset.mem_erase, Finset.mem_erase] at this
    exact this.2.1 rfl
  · intro h
    have := h_sub h
    rw [Finset.mem_erase, Finset.mem_erase] at this
    exact this.1 rfl

/-- **Real-valued indicator** of `M = insert (a_1,b_1) (insert (a_2,b_2) N) ∈
inducedKMatchings g univ univ k` with both anchor edges in `M`.

For a fixed `(k-2)`-subset `N`, this is the indicator computed entirely from `g`:

* `1[g(a_1,b_1)] · 1[g(a_2,b_2)]` — both anchor edges present.
* `∏_{x ∈ N} 1[g(x)]` — all matching edges present.
* `1[¬g(a_1,b_2)] · 1[¬g(a_2,b_1)]` — anchor-anchor bridges absent.
* `∏_{x ∈ N} 1[¬g(a_1, x.2)] · 1[¬g(a_2, x.2)] · 1[¬g(x.1, b_1)] · 1[¬g(x.1, b_2)]` —
  anchor-N bridges absent (4 per N-element).
* `∏_{(x,y) ∈ N×N, x≠y} 1[¬g(x.1, y.2)]` — within-N bridges absent. -/
noncomputable def matchingPairIndicator
    {n_A n_B : ℕ} (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B))
    (g : Fin n_A × Fin n_B → Bool) : ℝ :=
  (if g (a_1, b_1) = true then (1 : ℝ) else 0) *
  (if g (a_2, b_2) = true then (1 : ℝ) else 0) *
  (∏ x ∈ N, if g x = true then (1 : ℝ) else 0) *
  (if g (a_1, b_2) = true then (0 : ℝ) else 1) *
  (if g (a_2, b_1) = true then (0 : ℝ) else 1) *
  (∏ x ∈ N, if g (a_1, x.2) = true then (0 : ℝ) else 1) *
  (∏ x ∈ N, if g (a_2, x.2) = true then (0 : ℝ) else 1) *
  (∏ x ∈ N, if g (x.1, b_1) = true then (0 : ℝ) else 1) *
  (∏ x ∈ N, if g (x.1, b_2) = true then (0 : ℝ) else 1) *
  (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
      if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1)

/-- The `matchingPairIndicator` is either `0` or `1`. Proven by an incremental
chain: assemble pairwise products and apply the helper
`mul_zero_one_in_zero_one` (a 2-factor case) repeatedly, avoiding any 1024-case
`rcases ... simp` blowup. -/
lemma matchingPairIndicator_eq_zero_or_one
    {n_A n_B : ℕ} (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B))
    (g : Fin n_A × Fin n_B → Bool) :
    matchingPairIndicator a_1 a_2 b_1 b_2 N g = 0 ∨
      matchingPairIndicator a_1 a_2 b_1 b_2 N g = 1 := by
  classical
  -- Helper: product of two {0,1} values is {0,1}.
  have h_mul : ∀ x y : ℝ, (x = 0 ∨ x = 1) → (y = 0 ∨ y = 1) → x * y = 0 ∨ x * y = 1 := by
    intro x y hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · left; rw [hx]; ring
    · left; rw [hx]; ring
    · left; rw [hy]; ring
    · right; rw [hx, hy]; ring
  have h_if1 : ∀ (P : Prop) [Decidable P], (if P then (1 : ℝ) else 0) = 0 ∨
      (if P then (1 : ℝ) else 0) = 1 := fun P _ => by by_cases h : P <;> simp [h]
  have h_if0 : ∀ (P : Prop) [Decidable P], (if P then (0 : ℝ) else 1) = 0 ∨
      (if P then (0 : ℝ) else 1) = 1 := fun P _ => by by_cases h : P <;> simp [h]
  have h1 := h_if1 (g (a_1, b_1) = true)
  have h2 := h_if1 (g (a_2, b_2) = true)
  have h3 := prod_of_zero_one_in_zero_one N (fun x => if g x = true then (1 : ℝ) else 0)
    (fun x _ => h_if1 (g x = true))
  have h4 := h_if0 (g (a_1, b_2) = true)
  have h5 := h_if0 (g (a_2, b_1) = true)
  have h6 := prod_of_zero_one_in_zero_one N (fun x => if g (a_1, x.2) = true then (0 : ℝ) else 1)
    (fun x _ => h_if0 (g (a_1, x.2) = true))
  have h7 := prod_of_zero_one_in_zero_one N (fun x => if g (a_2, x.2) = true then (0 : ℝ) else 1)
    (fun x _ => h_if0 (g (a_2, x.2) = true))
  have h8 := prod_of_zero_one_in_zero_one N (fun x => if g (x.1, b_1) = true then (0 : ℝ) else 1)
    (fun x _ => h_if0 (g (x.1, b_1) = true))
  have h9 := prod_of_zero_one_in_zero_one N (fun x => if g (x.1, b_2) = true then (0 : ℝ) else 1)
    (fun x _ => h_if0 (g (x.1, b_2) = true))
  have h10 := prod_of_zero_one_in_zero_one ((N ×ˢ N).filter (fun p => p.1 ≠ p.2))
    (fun p => if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1)
    (fun p _ => h_if0 (g (p.1.1, p.2.2) = true))
  -- Multiply pairwise.
  have h12 := h_mul _ _ h1 h2
  have h123 := h_mul _ _ h12 h3
  have h1234 := h_mul _ _ h123 h4
  have h12345 := h_mul _ _ h1234 h5
  have h123456 := h_mul _ _ h12345 h6
  have h1234567 := h_mul _ _ h123456 h7
  have h12345678 := h_mul _ _ h1234567 h8
  have h123456789 := h_mul _ _ h12345678 h9
  have h_all := h_mul _ _ h123456789 h10
  exact h_all

/-! ## PS.4.c.3: pointwise Step B for the codegree integrand -/

/-- **Key pointwise identity for codegree Step B**: the codegree integrand
(count · four anchor-edge indicators) equals a sum over `(k-2)`-subsets of
`(univ.erase (a_1, b_1)).erase (a_2, b_2)` of `matchingPairIndicator`.

Strategy mirrors `count_mul_indicator_eq_sum_matchingIndicator`. Case-split on
the four anchor-slot values; only one branch is non-trivial. -/
lemma count_pair_mul_indicator_eq_sum_matchingPairIndicator
    {n_A n_B : ℕ} (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_a_distinct : a_1 ≠ a_2) (h_b_distinct : b_1 ≠ b_2)
    (g : Fin n_A × Fin n_B → Bool) :
    ((((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
        (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
        Finset.univ Finset.univ k).filter
          (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card : ℝ) *
        (if g (a_1, b_1) = true then (1 : ℝ) else 0) *
        (if g (a_2, b_2) = true then (1 : ℝ) else 0) *
        (if g (a_1, b_2) = true then (0 : ℝ) else 1) *
        (if g (a_2, b_1) = true then (0 : ℝ) else 1))
      = ∑ N ∈ (((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a_1, b_1)).erase
                (a_2, b_2)).powersetCard (k - 2),
          matchingPairIndicator a_1 a_2 b_1 b_2 N g := by
  classical
  set G := DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g with hG
  -- Case-split on each anchor-slot value; only the (true, true, false, false) branch
  -- is non-trivial.
  by_cases h_e1 : g (a_1, b_1) = true
  swap
  · -- LHS first anchor-indicator is 0; RHS factor in matchingPairIndicator is 0.
    have h_lhs : (((inducedKMatchings G Finset.univ Finset.univ k).filter
        (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card : ℝ) *
        (if g (a_1, b_1) = true then (1 : ℝ) else 0) *
        (if g (a_2, b_2) = true then (1 : ℝ) else 0) *
        (if g (a_1, b_2) = true then (0 : ℝ) else 1) *
        (if g (a_2, b_1) = true then (0 : ℝ) else 1) = 0 := by
      rw [if_neg h_e1]; ring
    rw [h_lhs]
    symm; apply Finset.sum_eq_zero
    intro N _hN
    unfold matchingPairIndicator
    rw [if_neg h_e1]; ring
  by_cases h_e2 : g (a_2, b_2) = true
  swap
  · have h_lhs : (((inducedKMatchings G Finset.univ Finset.univ k).filter
        (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card : ℝ) *
        (if g (a_1, b_1) = true then (1 : ℝ) else 0) *
        (if g (a_2, b_2) = true then (1 : ℝ) else 0) *
        (if g (a_1, b_2) = true then (0 : ℝ) else 1) *
        (if g (a_2, b_1) = true then (0 : ℝ) else 1) = 0 := by
      rw [if_neg h_e2]; ring
    rw [h_lhs]
    symm; apply Finset.sum_eq_zero
    intro N _hN
    unfold matchingPairIndicator
    rw [if_neg h_e2]; ring
  by_cases h_a1b2 : g (a_1, b_2) = true
  · have h_lhs : (((inducedKMatchings G Finset.univ Finset.univ k).filter
        (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card : ℝ) *
        (if g (a_1, b_1) = true then (1 : ℝ) else 0) *
        (if g (a_2, b_2) = true then (1 : ℝ) else 0) *
        (if g (a_1, b_2) = true then (0 : ℝ) else 1) *
        (if g (a_2, b_1) = true then (0 : ℝ) else 1) = 0 := by
      rw [if_pos h_a1b2]; ring
    rw [h_lhs]
    symm; apply Finset.sum_eq_zero
    intro N _hN
    unfold matchingPairIndicator
    rw [if_pos h_a1b2]; ring
  by_cases h_a2b1 : g (a_2, b_1) = true
  · have h_lhs : (((inducedKMatchings G Finset.univ Finset.univ k).filter
        (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card : ℝ) *
        (if g (a_1, b_1) = true then (1 : ℝ) else 0) *
        (if g (a_2, b_2) = true then (1 : ℝ) else 0) *
        (if g (a_1, b_2) = true then (0 : ℝ) else 1) *
        (if g (a_2, b_1) = true then (0 : ℝ) else 1) = 0 := by
      rw [if_pos h_a2b1]; ring
    rw [h_lhs]
    symm; apply Finset.sum_eq_zero
    intro N _hN
    unfold matchingPairIndicator
    rw [if_pos h_a2b1]; ring
  -- All four anchor conditions hold: both anchor edges present, no bridges.
  rw [if_pos h_e1, if_pos h_e2, if_neg h_a1b2, if_neg h_a2b1]
  -- LHS reduces to count.
  conv_lhs => rw [show ((((inducedKMatchings G Finset.univ Finset.univ k).filter
      (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card : ℝ) * 1 * 1 * 1 * 1) =
    ((inducedKMatchings G Finset.univ Finset.univ k).filter
      (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card from by ring]
  -- Apply the bijection: count = card of validErasePairPartner filter on
  -- ((cross G).erase (a_1, b_1)).erase (a_2, b_2)).powersetCard (k - 2).
  rw [inducedKMatchings_filter_mem_pair_image_erase G Finset.univ Finset.univ k h_k_ge_2
      a_1 a_2 b_1 b_2 h_a_distinct h_b_distinct]
  rw [Finset.card_filter]
  push_cast
  -- Compare the resulting sum (over (cross.erase.erase).powersetCard (k-2)) to the
  -- universe sum (over (univ.erase.erase).powersetCard (k-2)): for N outside the
  -- LHS universe, matchingPairIndicator a_1 a_2 b_1 b_2 N g = 0.
  rw [← Finset.sum_subset (s₁ :=
    (((DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ).erase
      (a_1, b_1)).erase (a_2, b_2)).powersetCard (k - 2))
    (s₂ := (((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a_1, b_1)).erase
      (a_2, b_2)).powersetCard (k - 2))
    (h := fun N hN => by
      rw [Finset.mem_powersetCard] at hN ⊢
      refine ⟨?_, hN.2⟩
      intro x hx
      have := hN.1 hx
      rw [Finset.mem_erase, Finset.mem_erase] at this ⊢
      exact ⟨this.1, this.2.1, Finset.mem_univ _⟩)
    (f := fun N => matchingPairIndicator a_1 a_2 b_1 b_2 N g)]
  · -- For N in the LHS universe: matchingPairIndicator = if validErasePairPartner then 1 else 0.
    apply Finset.sum_congr rfl
    intro N hN
    rw [Finset.mem_powersetCard] at hN
    obtain ⟨h_sub_cross, _h_N_card⟩ := hN
    -- For all x ∈ N, x is in crossBlockPairs G, so g x = true.
    have h_N_g_true : ∀ x ∈ N, g x = true := by
      intro x hx
      have hx_cross := h_sub_cross hx
      rw [Finset.mem_erase, Finset.mem_erase] at hx_cross
      have hx_in_cross : x ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ :=
        hx_cross.2.2
      rw [DaveyThesis2024.SecRandomBipartite.mem_crossBlockPairs] at hx_in_cross
      have h_adj : G.Adj (Sum.inl x.1) (Sum.inr x.2) := hx_in_cross.2.2
      rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr] at h_adj
      exact h_adj
    unfold matchingPairIndicator
    rw [if_pos h_e1, if_pos h_e2, if_neg h_a1b2, if_neg h_a2b1]
    have h_prod_present : (∏ x ∈ N, if g x = true then (1 : ℝ) else 0) = 1 := by
      apply Finset.prod_eq_one
      intro x hx
      rw [if_pos (h_N_g_true x hx)]
    rw [h_prod_present]
    by_cases h_valid : validErasePairPartner G Finset.univ Finset.univ a_1 a_2 b_1 b_2 N
    · rw [if_pos h_valid]
      have h_match : DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G
          (insert (a_1, b_1) (insert (a_2, b_2) N)) := h_valid.2.2
      have h_e_distinct : (a_1, b_1) ≠ (a_2, b_2) := fun h =>
        h_a_distinct (by simpa using congrArg Prod.fst h)
      have h_e1_notMem_N : (a_1, b_1) ∉ N := by
        intro h
        have := h_sub_cross h
        rw [Finset.mem_erase, Finset.mem_erase] at this
        exact this.2.1 rfl
      have h_e2_notMem_N : (a_2, b_2) ∉ N := by
        intro h
        have := h_sub_cross h
        rw [Finset.mem_erase, Finset.mem_erase] at this
        exact this.1 rfl
      have h_M := h_match
      set M := insert (a_1, b_1) (insert (a_2, b_2) N) with hM_def
      have h_e1_in : (a_1, b_1) ∈ M := Finset.mem_insert_self _ _
      have h_e2_in : (a_2, b_2) ∈ M :=
        Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      -- Bridge product 1: ∏ x ∈ N, if g(a_1, x.2) then 0 else 1 = 1.
      have h_p_a1 : (∏ x ∈ N, if g (a_1, x.2) = true then (0 : ℝ) else 1) = 1 := by
        apply Finset.prod_eq_one
        intro x hx
        have hx_in : x ∈ M :=
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
        have h_ne : (a_1, b_1) ≠ x := by
          intro h; rw [← h] at hx; exact h_e1_notMem_N hx
        have h_match_e1_x := h_M (a_1, b_1) h_e1_in x hx_in h_ne
        have h_no_bridge : ¬ G.Adj (Sum.inl (a_1, b_1).1) (Sum.inr x.2) := h_match_e1_x.2.2.1
        rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr]
          at h_no_bridge
        cases hg : g (a_1, x.2) with
        | false => simp
        | true => exact absurd hg h_no_bridge
      rw [h_p_a1]
      -- Bridge product 2: ∏ x ∈ N, if g(a_2, x.2) then 0 else 1 = 1.
      have h_p_a2 : (∏ x ∈ N, if g (a_2, x.2) = true then (0 : ℝ) else 1) = 1 := by
        apply Finset.prod_eq_one
        intro x hx
        have hx_in : x ∈ M :=
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
        have h_ne : (a_2, b_2) ≠ x := by
          intro h; rw [← h] at hx; exact h_e2_notMem_N hx
        have h_match_e2_x := h_M (a_2, b_2) h_e2_in x hx_in h_ne
        have h_no_bridge : ¬ G.Adj (Sum.inl (a_2, b_2).1) (Sum.inr x.2) := h_match_e2_x.2.2.1
        rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr]
          at h_no_bridge
        cases hg : g (a_2, x.2) with
        | false => simp
        | true => exact absurd hg h_no_bridge
      rw [h_p_a2]
      -- Bridge product 3: ∏ x ∈ N, if g(x.1, b_1) then 0 else 1 = 1.
      have h_p_b1 : (∏ x ∈ N, if g (x.1, b_1) = true then (0 : ℝ) else 1) = 1 := by
        apply Finset.prod_eq_one
        intro x hx
        have hx_in : x ∈ M :=
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
        have h_ne : (a_1, b_1) ≠ x := by
          intro h; rw [← h] at hx; exact h_e1_notMem_N hx
        have h_match_e1_x := h_M (a_1, b_1) h_e1_in x hx_in h_ne
        have h_no_bridge : ¬ G.Adj (Sum.inl x.1) (Sum.inr (a_1, b_1).2) := h_match_e1_x.2.2.2
        rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr]
          at h_no_bridge
        cases hg : g (x.1, b_1) with
        | false => simp
        | true => exact absurd hg h_no_bridge
      rw [h_p_b1]
      -- Bridge product 4: ∏ x ∈ N, if g(x.1, b_2) then 0 else 1 = 1.
      have h_p_b2 : (∏ x ∈ N, if g (x.1, b_2) = true then (0 : ℝ) else 1) = 1 := by
        apply Finset.prod_eq_one
        intro x hx
        have hx_in : x ∈ M :=
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
        have h_ne : (a_2, b_2) ≠ x := by
          intro h; rw [← h] at hx; exact h_e2_notMem_N hx
        have h_match_e2_x := h_M (a_2, b_2) h_e2_in x hx_in h_ne
        have h_no_bridge : ¬ G.Adj (Sum.inl x.1) (Sum.inr (a_2, b_2).2) := h_match_e2_x.2.2.2
        rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr]
          at h_no_bridge
        cases hg : g (x.1, b_2) with
        | false => simp
        | true => exact absurd hg h_no_bridge
      rw [h_p_b2]
      -- Within-N bridge product.
      have h_p_within : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
          if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1) = 1 := by
        apply Finset.prod_eq_one
        intro p hp
        rw [Finset.mem_filter, Finset.mem_product] at hp
        obtain ⟨⟨h_p1_in, h_p2_in⟩, h_p_ne⟩ := hp
        have hp1_in_M : p.1 ∈ M :=
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h_p1_in)
        have hp2_in_M : p.2 ∈ M :=
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h_p2_in)
        have h_match_p := h_M p.1 hp1_in_M p.2 hp2_in_M h_p_ne
        have h_no_bridge : ¬ G.Adj (Sum.inl p.1.1) (Sum.inr p.2.2) := h_match_p.2.2.1
        rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr]
          at h_no_bridge
        cases hg : g (p.1.1, p.2.2) with
        | false => simp
        | true => exact absurd hg h_no_bridge
      rw [h_p_within]; ring
    · -- ¬ validErasePairPartner: some bridge factor is 0.
      rw [if_neg h_valid]
      -- validErasePairPartner = (a_1, b_1) ∈ cross ∧ (a_2, b_2) ∈ cross ∧ IsBipartiteInducedMatching
      have h_e1_cross : (a_1, b_1) ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs
          G Finset.univ Finset.univ := by
        rw [DaveyThesis2024.SecRandomBipartite.mem_crossBlockPairs]
        refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
        rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr]
        exact h_e1
      have h_e2_cross : (a_2, b_2) ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs
          G Finset.univ Finset.univ := by
        rw [DaveyThesis2024.SecRandomBipartite.mem_crossBlockPairs]
        refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
        rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr]
        exact h_e2
      have h_not_match : ¬ DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G
          (insert (a_1, b_1) (insert (a_2, b_2) N)) := by
        intro h_match
        exact h_valid ⟨h_e1_cross, h_e2_cross, h_match⟩
      -- Extract a violation pair.
      unfold DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching at h_not_match
      push_neg at h_not_match
      obtain ⟨ab₁, hab₁_in, ab₂, hab₂_in, hab_ne, h_violation⟩ := h_not_match
      have h_e_distinct : (a_1, b_1) ≠ (a_2, b_2) := fun h =>
        h_a_distinct (by simpa using congrArg Prod.fst h)
      have h_e1_notMem_N : (a_1, b_1) ∉ N := by
        intro h
        have := h_sub_cross h
        rw [Finset.mem_erase, Finset.mem_erase] at this
        exact this.2.1 rfl
      have h_e2_notMem_N : (a_2, b_2) ∉ N := by
        intro h
        have := h_sub_cross h
        rw [Finset.mem_erase, Finset.mem_erase] at this
        exact this.1 rfl
      -- Generic resolution: peel off the chained implications and find a zero factor.
      -- Use a helper: anchor-anchor bridge contradicts h_a1b2/h_a2b1; anchor-N bridge gives
      -- factor 0; N-N bridge gives within-N factor 0.
      -- Convert chained insert membership to a clean 3-way disjunction.
      have h_mem3 : ∀ ab, ab ∈ insert (a_1, b_1) (insert (a_2, b_2) N) ↔
          ab = (a_1, b_1) ∨ ab = (a_2, b_2) ∨ ab ∈ N := by
        intro ab; simp [Finset.mem_insert]
      rw [h_mem3] at hab₁_in hab₂_in
      -- Helper to discharge each violation pair (ab₁, ab₂):
      -- if a-coords equal, then there's a slot clash; if b-coords equal, similar;
      -- else bridge (ab₁.1, ab₂.2) or (ab₂.1, ab₁.2) must be present, killing some factor.
      -- We handle each of the 9 sub-cases (3 choices for ab₁ × 3 for ab₂).
      -- Strategy: in every case, find a factor whose product is 0 by Finset.prod_eq_zero.
      --
      -- For brevity define a function: given (ab₁, ab₂) ∈ M × M with ab₁ ≠ ab₂ and the chained
      -- implication chain not satisfiable, exhibit a zero factor.
      -- We split: A-coord clash (h_violation does NOT hold at hyp1) vs. proceed.
      by_cases hA : ab₁.1 = ab₂.1
      · -- A-coord clash: ab₁ and ab₂ share A-coord.
        -- Cases of (ab₁ ∈ {e1, e2, N}) × (ab₂ ∈ {e1, e2, N}).
        rcases hab₁_in with hab₁_e1 | hab₁_in1
        · -- ab₁ = (a_1, b_1).
          subst hab₁_e1
          rcases hab₂_in with hab₂_e1 | hab₂_in1
          · -- ab₂ = (a_1, b_1) = ab₁ → contradicts hab_ne.
            exact absurd hab₂_e1 (hab_ne ∘ Eq.symm)
          rcases hab₂_in1 with hab₂_e2 | hab₂_inN
          · -- ab₂ = (a_2, b_2). hA: (a_1, b_1).1 = (a_2, b_2).1, i.e., a_1 = a_2 — contradicts.
            exact absurd (by rw [hab₂_e2] at hA; exact hA) h_a_distinct
          · -- ab₂ ∈ N. hA: (a_1, b_1).1 = ab₂.1, i.e., ab₂.1 = a_1.
            -- The product h_p_b1 (over N) has factor `if g(ab₂.1, b_1) then 0 else 1`.
            -- ab₂.1 = a_1, b_1 = b_1, so g(a_1, b_1) = true makes the factor 0.
            -- Conclude: matchingPairIndicator = 0 via Finset.prod_eq_zero on N at ab₂.
            have h_zero : (∏ x ∈ N, if g (x.1, b_1) = true then (0 : ℝ) else 1) = 0 := by
              apply Finset.prod_eq_zero hab₂_inN
              have : g (ab₂.1, b_1) = g ((a_1, b_1).1, b_1) := by rw [hA]
              rw [this]
              change (if g ((a_1, b_1).1, b_1) = true then (0 : ℝ) else 1) = 0
              have : g ((a_1, b_1).1, b_1) = true := h_e1
              rw [if_pos this]
            rw [h_zero]; ring
        rcases hab₁_in1 with hab₁_e2 | hab₁_inN
        · -- ab₁ = (a_2, b_2).
          subst hab₁_e2
          rcases hab₂_in with hab₂_e1 | hab₂_in1
          · -- ab₂ = (a_1, b_1). hA: a_2 = a_1.
            exact absurd (by rw [hab₂_e1] at hA; exact hA.symm) h_a_distinct
          rcases hab₂_in1 with hab₂_e2 | hab₂_inN
          · exact absurd hab₂_e2 (hab_ne ∘ Eq.symm)
          · -- ab₂ ∈ N. hA: a_2 = ab₂.1. Use product h_p_b2: factor at ab₂ is g(a_2, b_2)=true → 0.
            have h_zero : (∏ x ∈ N, if g (x.1, b_2) = true then (0 : ℝ) else 1) = 0 := by
              apply Finset.prod_eq_zero hab₂_inN
              have : g (ab₂.1, b_2) = g ((a_2, b_2).1, b_2) := by rw [hA]
              rw [this]
              change (if g ((a_2, b_2).1, b_2) = true then (0 : ℝ) else 1) = 0
              have : g ((a_2, b_2).1, b_2) = true := h_e2
              rw [if_pos this]
            rw [h_zero]; ring
        · -- ab₁ ∈ N.
          rcases hab₂_in with hab₂_e1 | hab₂_in1
          · subst hab₂_e1
            -- hA: ab₁.1 = a_1. Use h_p_b1 at ab₁: factor g(a_1, b_1) = true → 0.
            have h_zero : (∏ x ∈ N, if g (x.1, b_1) = true then (0 : ℝ) else 1) = 0 := by
              apply Finset.prod_eq_zero hab₁_inN
              have : g (ab₁.1, b_1) = g (a_1, b_1) := by rw [hA]
              rw [this, if_pos h_e1]
            rw [h_zero]; ring
          rcases hab₂_in1 with hab₂_e2 | hab₂_inN
          · subst hab₂_e2
            have h_zero : (∏ x ∈ N, if g (x.1, b_2) = true then (0 : ℝ) else 1) = 0 := by
              apply Finset.prod_eq_zero hab₁_inN
              have : g (ab₁.1, b_2) = g (a_2, b_2) := by rw [hA]
              rw [this, if_pos h_e2]
            rw [h_zero]; ring
          · -- Both ab₁, ab₂ ∈ N, hA: ab₁.1 = ab₂.1.
            -- Use h_p_within product at (ab₁, ab₂): slot (ab₁.1, ab₂.2) = (ab₂.1, ab₂.2) = ab₂.
            -- ab₂ ∈ N so g ab₂ = true, factor = 0.
            have h_pair_in : (ab₁, ab₂) ∈ (N ×ˢ N).filter
                (fun p : (Fin n_A × Fin n_B) × _ => p.1 ≠ p.2) := by
              rw [Finset.mem_filter, Finset.mem_product]
              exact ⟨⟨hab₁_inN, hab₂_inN⟩, hab_ne⟩
            have h_zero : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
                if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1) = 0 := by
              apply Finset.prod_eq_zero h_pair_in
              change (if g (ab₁.1, ab₂.2) = true then (0 : ℝ) else 1) = 0
              have h_eq : (ab₁.1, ab₂.2) = ab₂ := Prod.ext hA rfl
              rw [h_eq]
              have : g ab₂ = true := h_N_g_true ab₂ hab₂_inN
              rw [if_pos this]
            rw [h_zero]; ring
      · -- hA: ab₁.1 ≠ ab₂.1. Check B-coord clash.
        by_cases hB : ab₁.2 = ab₂.2
        · -- B-coord clash. Symmetric to A.
          rcases hab₁_in with hab₁_e1 | hab₁_in1
          · subst hab₁_e1
            rcases hab₂_in with hab₂_e1 | hab₂_in1
            · exact absurd hab₂_e1 (hab_ne ∘ Eq.symm)
            rcases hab₂_in1 with hab₂_e2 | hab₂_inN
            · exact absurd (by rw [hab₂_e2] at hB; exact hB) h_b_distinct
            · -- hB: (a_1, b_1).2 = ab₂.2, i.e., ab₂.2 = b_1. Use h_p_a1 at ab₂.
              have h_zero : (∏ x ∈ N, if g (a_1, x.2) = true then (0 : ℝ) else 1) = 0 := by
                apply Finset.prod_eq_zero hab₂_inN
                have : g (a_1, ab₂.2) = g (a_1, (a_1, b_1).2) := by rw [hB]
                rw [this]
                change (if g (a_1, (a_1, b_1).2) = true then (0 : ℝ) else 1) = 0
                have : g (a_1, (a_1, b_1).2) = true := h_e1
                rw [if_pos this]
              rw [h_zero]; ring
          rcases hab₁_in1 with hab₁_e2 | hab₁_inN
          · subst hab₁_e2
            rcases hab₂_in with hab₂_e1 | hab₂_in1
            · exact absurd (by rw [hab₂_e1] at hB; exact hB.symm) h_b_distinct
            rcases hab₂_in1 with hab₂_e2 | hab₂_inN
            · exact absurd hab₂_e2 (hab_ne ∘ Eq.symm)
            · -- hB: b_2 = ab₂.2. Use h_p_a2 at ab₂.
              have h_zero : (∏ x ∈ N, if g (a_2, x.2) = true then (0 : ℝ) else 1) = 0 := by
                apply Finset.prod_eq_zero hab₂_inN
                have : g (a_2, ab₂.2) = g (a_2, (a_2, b_2).2) := by rw [hB]
                rw [this]
                change (if g (a_2, (a_2, b_2).2) = true then (0 : ℝ) else 1) = 0
                have : g (a_2, (a_2, b_2).2) = true := h_e2
                rw [if_pos this]
              rw [h_zero]; ring
          · rcases hab₂_in with hab₂_e1 | hab₂_in1
            · subst hab₂_e1
              -- hB: ab₁.2 = b_1. Use h_p_a1 at ab₁.
              have h_zero : (∏ x ∈ N, if g (a_1, x.2) = true then (0 : ℝ) else 1) = 0 := by
                apply Finset.prod_eq_zero hab₁_inN
                have : g (a_1, ab₁.2) = g (a_1, b_1) := by rw [hB]
                rw [this, if_pos h_e1]
              rw [h_zero]; ring
            rcases hab₂_in1 with hab₂_e2 | hab₂_inN
            · subst hab₂_e2
              -- hB: ab₁.2 = b_2.
              have h_zero : (∏ x ∈ N, if g (a_2, x.2) = true then (0 : ℝ) else 1) = 0 := by
                apply Finset.prod_eq_zero hab₁_inN
                have : g (a_2, ab₁.2) = g (a_2, b_2) := by rw [hB]
                rw [this, if_pos h_e2]
              rw [h_zero]; ring
            · -- both in N, hB: ab₁.2 = ab₂.2.
              have h_pair_in : (ab₁, ab₂) ∈ (N ×ˢ N).filter
                  (fun p : (Fin n_A × Fin n_B) × _ => p.1 ≠ p.2) := by
                rw [Finset.mem_filter, Finset.mem_product]
                exact ⟨⟨hab₁_inN, hab₂_inN⟩, hab_ne⟩
              have h_zero : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
                  if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1) = 0 := by
                apply Finset.prod_eq_zero h_pair_in
                change (if g (ab₁.1, ab₂.2) = true then (0 : ℝ) else 1) = 0
                have h_eq : (ab₁.1, ab₂.2) = ab₁ := Prod.ext rfl hB.symm
                rw [h_eq]
                have : g ab₁ = true := h_N_g_true ab₁ hab₁_inN
                rw [if_pos this]
              rw [h_zero]; ring
        · -- Neither A nor B coord clash. h_violation gives chained implication; resolve via bridges.
          have h_step3 := h_violation hA hB
          -- h_step3 : ¬ G.Adj (inl ab₁.1) (inr ab₂.2) → G.Adj (inl ab₂.1) (inr ab₁.2)
          by_cases h_bridge1 : G.Adj (Sum.inl ab₁.1) (Sum.inr ab₂.2)
          · -- Bridge (ab₁.1, ab₂.2) is present in G, i.e., g(ab₁.1, ab₂.2) = true.
            rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr]
              at h_bridge1
            -- The slot (ab₁.1, ab₂.2) is one of: anchor-anchor / anchor-N / N-N.
            -- Cases on which kind of slot.
            -- All cases use Finset.prod_eq_zero on some product.
            rcases hab₁_in with hab₁_e1 | hab₁_in1
            · subst hab₁_e1
              rcases hab₂_in with hab₂_e1 | hab₂_in1
              · exact absurd hab₂_e1 (hab_ne ∘ Eq.symm)
              rcases hab₂_in1 with hab₂_e2 | hab₂_inN
              · subst hab₂_e2
                -- bridge (a_1, b_2) = true, but h_a1b2 says g (a_1, b_2) = false → contradiction.
                exact absurd h_bridge1 h_a1b2
              · -- bridge (a_1, ab₂.2) = true; ab₂ ∈ N. Use h_p_a1 at ab₂.
                have h_zero : (∏ x ∈ N, if g (a_1, x.2) = true then (0 : ℝ) else 1) = 0 := by
                  apply Finset.prod_eq_zero hab₂_inN
                  change (if g (a_1, ab₂.2) = true then (0 : ℝ) else 1) = 0
                  have : g ((a_1, b_1).1, ab₂.2) = g (a_1, ab₂.2) := rfl
                  rw [← this]
                  exact if_pos h_bridge1
                rw [h_zero]; ring
            rcases hab₁_in1 with hab₁_e2 | hab₁_inN
            · subst hab₁_e2
              rcases hab₂_in with hab₂_e1 | hab₂_in1
              · subst hab₂_e1
                -- bridge (a_2, b_1) = true, but h_a2b1 says false → contradiction.
                exact absurd h_bridge1 h_a2b1
              rcases hab₂_in1 with hab₂_e2 | hab₂_inN
              · exact absurd hab₂_e2 (hab_ne ∘ Eq.symm)
              · -- bridge (a_2, ab₂.2) true; use h_p_a2 at ab₂.
                have h_zero : (∏ x ∈ N, if g (a_2, x.2) = true then (0 : ℝ) else 1) = 0 := by
                  apply Finset.prod_eq_zero hab₂_inN
                  change (if g (a_2, ab₂.2) = true then (0 : ℝ) else 1) = 0
                  have : g ((a_2, b_2).1, ab₂.2) = g (a_2, ab₂.2) := rfl
                  rw [← this]
                  exact if_pos h_bridge1
                rw [h_zero]; ring
            · -- ab₁ ∈ N.
              rcases hab₂_in with hab₂_e1 | hab₂_in1
              · subst hab₂_e1
                -- bridge (ab₁.1, b_1) = true; use h_p_b1 at ab₁.
                have h_zero : (∏ x ∈ N, if g (x.1, b_1) = true then (0 : ℝ) else 1) = 0 := by
                  apply Finset.prod_eq_zero hab₁_inN
                  change (if g (ab₁.1, b_1) = true then (0 : ℝ) else 1) = 0
                  have : g (ab₁.1, (a_1, b_1).2) = g (ab₁.1, b_1) := rfl
                  rw [← this]
                  exact if_pos h_bridge1
                rw [h_zero]; ring
              rcases hab₂_in1 with hab₂_e2 | hab₂_inN
              · subst hab₂_e2
                have h_zero : (∏ x ∈ N, if g (x.1, b_2) = true then (0 : ℝ) else 1) = 0 := by
                  apply Finset.prod_eq_zero hab₁_inN
                  change (if g (ab₁.1, b_2) = true then (0 : ℝ) else 1) = 0
                  have : g (ab₁.1, (a_2, b_2).2) = g (ab₁.1, b_2) := rfl
                  rw [← this]
                  exact if_pos h_bridge1
                rw [h_zero]; ring
              · -- both in N: bridge (ab₁.1, ab₂.2); use h_p_within.
                have h_pair_in : (ab₁, ab₂) ∈ (N ×ˢ N).filter
                    (fun p : (Fin n_A × Fin n_B) × _ => p.1 ≠ p.2) := by
                  rw [Finset.mem_filter, Finset.mem_product]
                  exact ⟨⟨hab₁_inN, hab₂_inN⟩, hab_ne⟩
                have h_zero : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
                    if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1) = 0 := by
                  apply Finset.prod_eq_zero h_pair_in
                  change (if g (ab₁.1, ab₂.2) = true then (0 : ℝ) else 1) = 0
                  exact if_pos h_bridge1
                rw [h_zero]; ring
          · -- ¬ G.Adj (inl ab₁.1) (inr ab₂.2). Use h_step3 → bridge (ab₂.1, ab₁.2).
            have h_step4 := h_step3 h_bridge1
            rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr]
              at h_step4
            -- bridge (ab₂.1, ab₁.2) is present. Same case-split.
            rcases hab₁_in with hab₁_e1 | hab₁_in1
            · subst hab₁_e1
              rcases hab₂_in with hab₂_e1 | hab₂_in1
              · exact absurd hab₂_e1 (hab_ne ∘ Eq.symm)
              rcases hab₂_in1 with hab₂_e2 | hab₂_inN
              · subst hab₂_e2
                -- bridge (a_2, b_1) = true, but h_a2b1 false → contradiction.
                exact absurd h_step4 h_a2b1
              · -- bridge (ab₂.1, b_1) true; use h_p_b1 at ab₂.
                have h_zero : (∏ x ∈ N, if g (x.1, b_1) = true then (0 : ℝ) else 1) = 0 := by
                  apply Finset.prod_eq_zero hab₂_inN
                  change (if g (ab₂.1, b_1) = true then (0 : ℝ) else 1) = 0
                  have : g (ab₂.1, (a_1, b_1).2) = g (ab₂.1, b_1) := rfl
                  rw [← this]
                  exact if_pos h_step4
                rw [h_zero]; ring
            rcases hab₁_in1 with hab₁_e2 | hab₁_inN
            · subst hab₁_e2
              rcases hab₂_in with hab₂_e1 | hab₂_in1
              · subst hab₂_e1
                exact absurd h_step4 h_a1b2
              rcases hab₂_in1 with hab₂_e2 | hab₂_inN
              · exact absurd hab₂_e2 (hab_ne ∘ Eq.symm)
              · -- bridge (ab₂.1, b_2) true; use h_p_b2 at ab₂.
                have h_zero : (∏ x ∈ N, if g (x.1, b_2) = true then (0 : ℝ) else 1) = 0 := by
                  apply Finset.prod_eq_zero hab₂_inN
                  change (if g (ab₂.1, b_2) = true then (0 : ℝ) else 1) = 0
                  have : g (ab₂.1, (a_2, b_2).2) = g (ab₂.1, b_2) := rfl
                  rw [← this]
                  exact if_pos h_step4
                rw [h_zero]; ring
            · rcases hab₂_in with hab₂_e1 | hab₂_in1
              · subst hab₂_e1
                -- bridge (a_1, ab₁.2) true; use h_p_a1 at ab₁.
                have h_zero : (∏ x ∈ N, if g (a_1, x.2) = true then (0 : ℝ) else 1) = 0 := by
                  apply Finset.prod_eq_zero hab₁_inN
                  change (if g (a_1, ab₁.2) = true then (0 : ℝ) else 1) = 0
                  have : g ((a_1, b_1).1, ab₁.2) = g (a_1, ab₁.2) := rfl
                  rw [← this]
                  exact if_pos h_step4
                rw [h_zero]; ring
              rcases hab₂_in1 with hab₂_e2 | hab₂_inN
              · subst hab₂_e2
                have h_zero : (∏ x ∈ N, if g (a_2, x.2) = true then (0 : ℝ) else 1) = 0 := by
                  apply Finset.prod_eq_zero hab₁_inN
                  change (if g (a_2, ab₁.2) = true then (0 : ℝ) else 1) = 0
                  have : g ((a_2, b_2).1, ab₁.2) = g (a_2, ab₁.2) := rfl
                  rw [← this]
                  exact if_pos h_step4
                rw [h_zero]; ring
              · -- both in N: bridge (ab₂.1, ab₁.2); use h_p_within with swapped pair.
                have h_pair_swap_in : (ab₂, ab₁) ∈ (N ×ˢ N).filter
                    (fun p : (Fin n_A × Fin n_B) × _ => p.1 ≠ p.2) := by
                  rw [Finset.mem_filter, Finset.mem_product]
                  exact ⟨⟨hab₂_inN, hab₁_inN⟩, fun h => hab_ne h.symm⟩
                have h_zero : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
                    if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1) = 0 := by
                  apply Finset.prod_eq_zero h_pair_swap_in
                  change (if g (ab₂.1, ab₁.2) = true then (0 : ℝ) else 1) = 0
                  exact if_pos h_step4
                rw [h_zero]; ring
  · -- For N in (univ.erase.erase).powersetCard (k-2) \ (cross.erase.erase).powersetCard (k-2):
    -- some element x ∈ N has g x = false, so matchingPairIndicator factor at x is 0.
    intro N hN_univ hN_notIn
    rw [Finset.mem_powersetCard] at hN_univ
    obtain ⟨h_sub_univ, h_N_card⟩ := hN_univ
    have h_not_sub_cross : ¬ (N ⊆ ((DaveyThesis2024.SecRandomBipartite.crossBlockPairs
        G Finset.univ Finset.univ).erase (a_1, b_1)).erase (a_2, b_2)) := by
      intro h_sub
      apply hN_notIn
      rw [Finset.mem_powersetCard]
      exact ⟨h_sub, h_N_card⟩
    rw [Finset.not_subset] at h_not_sub_cross
    obtain ⟨x, hx_in, hx_notIn⟩ := h_not_sub_cross
    have hx_not_e1 : x ≠ (a_1, b_1) := by
      have := h_sub_univ hx_in
      rw [Finset.mem_erase, Finset.mem_erase] at this
      exact this.2.1
    have hx_not_e2 : x ≠ (a_2, b_2) := by
      have := h_sub_univ hx_in
      rw [Finset.mem_erase, Finset.mem_erase] at this
      exact this.1
    have hx_not_cross : x ∉ DaveyThesis2024.SecRandomBipartite.crossBlockPairs
        G Finset.univ Finset.univ := by
      intro h
      apply hx_notIn
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨hx_not_e2, hx_not_e1, h⟩
    rw [DaveyThesis2024.SecRandomBipartite.mem_crossBlockPairs] at hx_not_cross
    push_neg at hx_not_cross
    have hx_no_adj := hx_not_cross (Finset.mem_univ _) (Finset.mem_univ _)
    rw [hG, DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr] at hx_no_adj
    have hx_g_false : g x = false := by
      cases hg : g x with
      | false => rfl
      | true => exact absurd hg hx_no_adj
    unfold matchingPairIndicator
    have h_p_present_zero : (∏ x' ∈ N, if g x' = true then (1 : ℝ) else 0) = 0 := by
      apply Finset.prod_eq_zero hx_in
      rw [hx_g_false]; simp
    rw [h_p_present_zero]
    ring

/-! ## PS.4.c.4: matchingPairIndicator = 0 for non-candidate N -/

/-- For `N` in the universe `((univ.erase e_1).erase e_2).powersetCard (k - 2)` but
NOT in `candidatePairPartnerSet`, `matchingPairIndicator a_1 a_2 b_1 b_2 N g = 0`
for every `g`.

Strategy: parallels `matchingIndicator_eq_zero_of_not_candidate`. Case-split on
which candidate condition fails (A-coord = a_1 or a_2, B-coord = b_1 or b_2,
A-coord clash within N, B-coord clash within N) and find a zero factor. -/
lemma matchingPairIndicator_eq_zero_of_not_candidate
    {n_A n_B : ℕ} (k : ℕ) (_h_k_ge_2 : 2 ≤ k)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ (((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a_1, b_1)).erase
            (a_2, b_2)).powersetCard (k - 2))
    (h_not_cand : N ∉ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2)
    (g : Fin n_A × Fin n_B → Bool) :
    matchingPairIndicator a_1 a_2 b_1 b_2 N g = 0 := by
  classical
  unfold candidatePairPartnerSet at h_not_cand
  rw [Finset.mem_filter] at h_not_cand
  push_neg at h_not_cand
  have h_not_part := h_not_cand hN
  unfold CandidatePairPartner at h_not_part
  push_neg at h_not_part
  -- h_not_part has chained-implication form.
  -- Helpers: 'present zero' = the per-N present-edge product hits 0 at some x with g x = false.
  -- 'bridge zero at slot' = some bridge product hits 0 at some witness.
  by_cases h_no_a1 : ∀ x ∈ N, x.1 ≠ a_1
  case neg =>
    -- ∃ x ∈ N, x.1 = a_1. Slot collision: present factor `g x = true` AND bridge
    -- factor `g (a_1, x.2)` (which equals `g x`) being false force opposite values.
    push_neg at h_no_a1
    obtain ⟨x, hx, hx_a1⟩ := h_no_a1
    unfold matchingPairIndicator
    by_cases h_gx : g x = true
    · -- bridge h_p_a1 at x: (a_1, x.2) = x. Factor = if g x = true then 0 else 1 = 0.
      have h_zero : (∏ x' ∈ N, if g (a_1, x'.2) = true then (0 : ℝ) else 1) = 0 := by
        apply Finset.prod_eq_zero hx
        have h_eq : (a_1, x.2) = x := Prod.ext hx_a1.symm rfl
        rw [h_eq, if_pos h_gx]
      rw [h_zero]; ring
    · -- present product at x is 0.
      have h_zero : (∏ x' ∈ N, if g x' = true then (1 : ℝ) else 0) = 0 := by
        apply Finset.prod_eq_zero hx
        have h_false : g x = false := by
          cases hg : g x with | false => rfl | true => exact absurd hg h_gx
        rw [if_neg]; intro h; rw [h_false] at h; exact Bool.false_ne_true h
      rw [h_zero]; ring
  -- h_no_a1 holds.
  by_cases h_no_a2 : ∀ x ∈ N, x.1 ≠ a_2
  case neg =>
    push_neg at h_no_a2
    obtain ⟨x, hx, hx_a2⟩ := h_no_a2
    unfold matchingPairIndicator
    by_cases h_gx : g x = true
    · have h_zero : (∏ x' ∈ N, if g (a_2, x'.2) = true then (0 : ℝ) else 1) = 0 := by
        apply Finset.prod_eq_zero hx
        have h_eq : (a_2, x.2) = x := Prod.ext hx_a2.symm rfl
        rw [h_eq, if_pos h_gx]
      rw [h_zero]; ring
    · have h_zero : (∏ x' ∈ N, if g x' = true then (1 : ℝ) else 0) = 0 := by
        apply Finset.prod_eq_zero hx
        have h_false : g x = false := by
          cases hg : g x with | false => rfl | true => exact absurd hg h_gx
        rw [if_neg]; intro h; rw [h_false] at h; exact Bool.false_ne_true h
      rw [h_zero]; ring
  by_cases h_no_b1 : ∀ x ∈ N, x.2 ≠ b_1
  case neg =>
    push_neg at h_no_b1
    obtain ⟨x, hx, hx_b1⟩ := h_no_b1
    unfold matchingPairIndicator
    by_cases h_gx : g x = true
    · have h_zero : (∏ x' ∈ N, if g (x'.1, b_1) = true then (0 : ℝ) else 1) = 0 := by
        apply Finset.prod_eq_zero hx
        have h_eq : (x.1, b_1) = x := Prod.ext rfl hx_b1.symm
        rw [h_eq, if_pos h_gx]
      rw [h_zero]; ring
    · have h_zero : (∏ x' ∈ N, if g x' = true then (1 : ℝ) else 0) = 0 := by
        apply Finset.prod_eq_zero hx
        have h_false : g x = false := by
          cases hg : g x with | false => rfl | true => exact absurd hg h_gx
        rw [if_neg]; intro h; rw [h_false] at h; exact Bool.false_ne_true h
      rw [h_zero]; ring
  by_cases h_no_b2 : ∀ x ∈ N, x.2 ≠ b_2
  case neg =>
    push_neg at h_no_b2
    obtain ⟨x, hx, hx_b2⟩ := h_no_b2
    unfold matchingPairIndicator
    by_cases h_gx : g x = true
    · have h_zero : (∏ x' ∈ N, if g (x'.1, b_2) = true then (0 : ℝ) else 1) = 0 := by
        apply Finset.prod_eq_zero hx
        have h_eq : (x.1, b_2) = x := Prod.ext rfl hx_b2.symm
        rw [h_eq, if_pos h_gx]
      rw [h_zero]; ring
    · have h_zero : (∏ x' ∈ N, if g x' = true then (1 : ℝ) else 0) = 0 := by
        apply Finset.prod_eq_zero hx
        have h_false : g x = false := by
          cases hg : g x with | false => rfl | true => exact absurd hg h_gx
        rw [if_neg]; intro h; rw [h_false] at h; exact Bool.false_ne_true h
      rw [h_zero]; ring
  by_cases h_A_inj : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → x.1 ≠ y.1
  case neg =>
    push_neg at h_A_inj
    obtain ⟨x, hx, y, hy, hxy, hxy_A⟩ := h_A_inj
    unfold matchingPairIndicator
    by_cases h_gy : g y = true
    · -- within-N at (x, y): slot (x.1, y.2) = (y.1, y.2) = y. Factor = 0.
      have h_pair_in : (x, y) ∈ (N ×ˢ N).filter
          (fun p : (Fin n_A × Fin n_B) × _ => p.1 ≠ p.2) := by
        rw [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hx, hy⟩, hxy⟩
      have h_zero : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
          if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1) = 0 := by
        apply Finset.prod_eq_zero h_pair_in
        change (if g (x.1, y.2) = true then (0 : ℝ) else 1) = 0
        have h_eq : (x.1, y.2) = y := Prod.ext hxy_A rfl
        rw [h_eq, if_pos h_gy]
      rw [h_zero]; ring
    · have h_zero : (∏ x' ∈ N, if g x' = true then (1 : ℝ) else 0) = 0 := by
        apply Finset.prod_eq_zero hy
        have h_false : g y = false := by
          cases hg : g y with | false => rfl | true => exact absurd hg h_gy
        rw [if_neg]; intro h; rw [h_false] at h; exact Bool.false_ne_true h
      rw [h_zero]; ring
  -- h_no_a1, h_no_a2, h_no_b1, h_no_b2, h_A_inj all hold. Remaining condition fails.
  have h_B_fail := h_not_part h_no_a1 h_no_a2 h_no_b1 h_no_b2 h_A_inj
  obtain ⟨x, hx, y, hy, hxy, hxy_B⟩ := h_B_fail
  unfold matchingPairIndicator
  by_cases h_gx : g x = true
  · -- within-N at (x, y): slot (x.1, y.2) = (x.1, x.2) = x. Factor = 0.
    have h_pair_in : (x, y) ∈ (N ×ˢ N).filter
        (fun p : (Fin n_A × Fin n_B) × _ => p.1 ≠ p.2) := by
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hx, hy⟩, hxy⟩
    have h_zero : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
        if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1) = 0 := by
      apply Finset.prod_eq_zero h_pair_in
      change (if g (x.1, y.2) = true then (0 : ℝ) else 1) = 0
      have h_eq : (x.1, y.2) = x := Prod.ext rfl hxy_B.symm
      rw [h_eq, if_pos h_gx]
    rw [h_zero]; ring
  · have h_zero : (∏ x' ∈ N, if g x' = true then (1 : ℝ) else 0) = 0 := by
      apply Finset.prod_eq_zero hx
      have h_false : g x = false := by
        cases hg : g x with | false => rfl | true => exact absurd hg h_gx
      rw [if_neg]; intro h; rw [h_false] at h; exact Bool.false_ne_true h
    rw [h_zero]; ring

/-! ## PS.4.c.5: per-candidate integration (Step C-final, pair case)

For each `N ∈ candidatePairPartnerSet`, integrate `matchingPairIndicator g`
over the bipartite measure to obtain `p^k · (1-p)^(k(k-1))`. The k(k-1) absent
slots come from 4 anchor-anchor + 4·(k-2) anchor-N + (k-2)(k-3) within-N
bridges = k(k-1) total. The k present slots are {e_1, e_2} ∪ N.

We use the existing PS.4.b.5 building blocks (`presentSlots`, `aBridgeSlots`,
`bBridgeSlots`, `withinNSlots`, `if_eq_edgeIndicator`,
`if_eq_one_minus_edgeIndicator`, etc.) for the N-side, augmenting with two
new anchor slots and the second anchor's bridge slots. -/

/-- Present slots for the pair case: `{(a_1, b_1), (a_2, b_2)} ∪ N`. -/
noncomputable def presentSlotsPair {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) : Finset (Fin n_A × Fin n_B) :=
  insert (a_1, b_1) (insert (a_2, b_2) N)

/-- Absent slots for the pair case: 4 anchor-anchor + 4·|N| anchor-N + within-N
bridges. We use the unions of 7 pieces:
* `{(a_1, b_2)}`, `{(a_2, b_1)}` — two anchor-anchor bridges.
* `aBridgeSlots a_1 N`, `aBridgeSlots a_2 N` — anchor-row bridges.
* `bBridgeSlots b_1 N`, `bBridgeSlots b_2 N` — anchor-column bridges.
* `withinNSlots N` — within-N bridges. -/
noncomputable def absentSlotsPair {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) : Finset (Fin n_A × Fin n_B) :=
  insert (a_1, b_2) (insert (a_2, b_1)
    (aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
      bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N ∪ withinNSlots N))

/-- The **N-derived** pair-bridge slots only — `absentSlotsPair` WITHOUT the two fixed
anchor-anchor bridges `(a₁,b₂)`, `(a₂,b₁)`. The codegree polynomial is built over this set
(treating `e₁,e₂` present AND `(a₁,b₂),(a₂,b₁)` absent as fixed), so its partial-derivative
effects exclude the anchor slots, keeping `E'` codegree-scale. -/
noncomputable def absentSlotsPairCore {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) : Finset (Fin n_A × Fin n_B) :=
  aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
    bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N ∪ withinNSlots N

/-- `absentSlotsPair = insert (a₁,b₂) (insert (a₂,b₁) absentSlotsPairCore)` — definitional. -/
lemma absentSlotsPair_eq_insert_core {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (N : Finset (Fin n_A × Fin n_B)) :
    absentSlotsPair a_1 a_2 b_1 b_2 N
      = insert (a_1, b_2) (insert (a_2, b_1) (absentSlotsPairCore a_1 a_2 b_1 b_2 N)) := rfl

/-- For a `CandidatePairPartner`, `(a_1, b_2) ∉` any of the N-derived absent slots. -/
lemma a1b2_not_mem_N_absent {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_a_distinct : a_1 ≠ a_2) (h_b_distinct : b_1 ≠ b_2)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) :
    (a_1, b_2) ∉ aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
      bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N ∪ withinNSlots N := by
  classical
  obtain ⟨h_a1, h_a2, h_b1, h_b2, h_A_inj, h_B_inj⟩ := h_cand
  intro h_in
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union] at h_in
  rcases h_in with ((((h_a1' | h_a2') | h_b1') | h_b2') | h_w)
  · rw [aBridgeSlots, Finset.mem_image] at h_a1'
    obtain ⟨x, hx, h_eq⟩ := h_a1'
    have h_b_eq : x.2 = b_2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
    exact (h_b2 x hx) h_b_eq
  · rw [aBridgeSlots, Finset.mem_image] at h_a2'
    obtain ⟨_, _, h_eq⟩ := h_a2'
    have h_a_eq : a_2 = a_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
    exact h_a_distinct h_a_eq.symm
  · rw [bBridgeSlots, Finset.mem_image] at h_b1'
    obtain ⟨_, _, h_eq⟩ := h_b1'
    have h_b_eq : b_1 = b_2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
    exact h_b_distinct h_b_eq
  · rw [bBridgeSlots, Finset.mem_image] at h_b2'
    obtain ⟨x, hx, h_eq⟩ := h_b2'
    have h_a_eq : x.1 = a_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
    exact (h_a1 x hx) h_a_eq
  · rw [withinNSlots, Finset.mem_image] at h_w
    obtain ⟨p, hp, h_eq⟩ := h_w
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, _⟩, _⟩ := hp
    have h_a_eq : p.1.1 = a_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
    exact (h_a1 p.1 hp1) h_a_eq

/-- For a `CandidatePairPartner`, `(a_2, b_1) ∉` any of the N-derived absent slots. -/
lemma a2b1_not_mem_N_absent {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_a_distinct : a_1 ≠ a_2) (h_b_distinct : b_1 ≠ b_2)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) :
    (a_2, b_1) ∉ aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
      bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N ∪ withinNSlots N := by
  classical
  obtain ⟨h_a1, h_a2, h_b1, h_b2, h_A_inj, h_B_inj⟩ := h_cand
  intro h_in
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union] at h_in
  rcases h_in with ((((h_a1' | h_a2') | h_b1') | h_b2') | h_w)
  · rw [aBridgeSlots, Finset.mem_image] at h_a1'
    obtain ⟨_, _, h_eq⟩ := h_a1'
    have h_a_eq : a_1 = a_2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
    exact h_a_distinct h_a_eq
  · rw [aBridgeSlots, Finset.mem_image] at h_a2'
    obtain ⟨x, hx, h_eq⟩ := h_a2'
    have h_b_eq : x.2 = b_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
    exact (h_b1 x hx) h_b_eq
  · rw [bBridgeSlots, Finset.mem_image] at h_b1'
    obtain ⟨x, hx, h_eq⟩ := h_b1'
    have h_a_eq : x.1 = a_2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
    exact (h_a2 x hx) h_a_eq
  · rw [bBridgeSlots, Finset.mem_image] at h_b2'
    obtain ⟨_, _, h_eq⟩ := h_b2'
    have h_b_eq : b_2 = b_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
    exact h_b_distinct h_b_eq.symm
  · rw [withinNSlots, Finset.mem_image] at h_w
    obtain ⟨p, hp, h_eq⟩ := h_w
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨_, hp2⟩, _⟩ := hp
    have h_b_eq : p.2.2 = b_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
    exact (h_b1 p.2 hp2) h_b_eq

/-- `(a_1, b_2) ≠ (a_2, b_1)` when `a_1 ≠ a_2`. -/
lemma a1b2_ne_a2b1 {n_A n_B : ℕ} (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_a_distinct : a_1 ≠ a_2) :
    (a_1, b_2) ≠ (a_2, b_1) := by
  intro h
  exact h_a_distinct ((Prod.mk.injEq _ _ _ _).mp h).1

/-- The pair-case present slots and N-derived absent slots are disjoint. -/
lemma presentSlotsPair_disjoint_N_absent {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_a_distinct : a_1 ≠ a_2) (h_b_distinct : b_1 ≠ b_2)
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) :
    Disjoint (presentSlotsPair a_1 a_2 b_1 b_2 N)
      (aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
        bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N ∪ withinNSlots N) := by
  classical
  obtain ⟨h_a1, h_a2, h_b1, h_b2, h_A_inj, h_B_inj⟩ := h_cand
  unfold presentSlotsPair
  rw [Finset.disjoint_left]
  intro ab h_pres h_abs
  rw [Finset.mem_insert, Finset.mem_insert] at h_pres
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union] at h_abs
  rcases h_pres with h_e1 | h_e2 | h_inN
  · subst h_e1
    -- (a_1, b_1) ∉ any of the N-derived absent slots.
    rcases h_abs with ((((h | h) | h) | h) | h)
    · rw [aBridgeSlots, Finset.mem_image] at h
      obtain ⟨x, hx, h_eq⟩ := h
      have : x.2 = b_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
      exact (h_b1 x hx) this
    · rw [aBridgeSlots, Finset.mem_image] at h
      obtain ⟨_, _, h_eq⟩ := h
      have : a_2 = a_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
      exact h_a_distinct this.symm
    · rw [bBridgeSlots, Finset.mem_image] at h
      obtain ⟨x, hx, h_eq⟩ := h
      have : x.1 = a_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
      exact (h_a1 x hx) this
    · rw [bBridgeSlots, Finset.mem_image] at h
      obtain ⟨_, _, h_eq⟩ := h
      have : b_2 = b_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
      exact h_b_distinct this.symm
    · rw [withinNSlots, Finset.mem_image] at h
      obtain ⟨p, hp, h_eq⟩ := h
      rw [Finset.mem_filter, Finset.mem_product] at hp
      have : p.1.1 = a_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
      exact (h_a1 p.1 hp.1.1) this
  · subst h_e2
    rcases h_abs with ((((h | h) | h) | h) | h)
    · rw [aBridgeSlots, Finset.mem_image] at h
      obtain ⟨_, _, h_eq⟩ := h
      have : a_1 = a_2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
      exact h_a_distinct this
    · rw [aBridgeSlots, Finset.mem_image] at h
      obtain ⟨x, hx, h_eq⟩ := h
      have : x.2 = b_2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
      exact (h_b2 x hx) this
    · rw [bBridgeSlots, Finset.mem_image] at h
      obtain ⟨_, _, h_eq⟩ := h
      have : b_1 = b_2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
      exact h_b_distinct this
    · rw [bBridgeSlots, Finset.mem_image] at h
      obtain ⟨x, hx, h_eq⟩ := h
      have : x.1 = a_2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
      exact (h_a2 x hx) this
    · rw [withinNSlots, Finset.mem_image] at h
      obtain ⟨p, hp, h_eq⟩ := h
      rw [Finset.mem_filter, Finset.mem_product] at hp
      have : p.1.1 = a_2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
      exact (h_a2 p.1 hp.1.1) this
  · -- ab ∈ N.
    rcases h_abs with ((((h | h) | h) | h) | h)
    · rw [aBridgeSlots, Finset.mem_image] at h
      obtain ⟨_, _, h_eq⟩ := h
      have : ab.1 = a_1 := by rw [← h_eq]
      exact (h_a1 ab h_inN) this
    · rw [aBridgeSlots, Finset.mem_image] at h
      obtain ⟨_, _, h_eq⟩ := h
      have : ab.1 = a_2 := by rw [← h_eq]
      exact (h_a2 ab h_inN) this
    · rw [bBridgeSlots, Finset.mem_image] at h
      obtain ⟨_, _, h_eq⟩ := h
      have : ab.2 = b_1 := by rw [← h_eq]
      exact (h_b1 ab h_inN) this
    · rw [bBridgeSlots, Finset.mem_image] at h
      obtain ⟨_, _, h_eq⟩ := h
      have : ab.2 = b_2 := by rw [← h_eq]
      exact (h_b2 ab h_inN) this
    · exact (Finset.disjoint_left.mp (withinNSlots_disjoint_N a_1 b_1 N
        ⟨h_a1, h_b1, h_A_inj, h_B_inj⟩)) h h_inN

/-- presentSlotsPair has cardinality k. -/
lemma presentSlotsPair_card {n_A n_B : ℕ} (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_a_distinct : a_1 ≠ a_2)
    (hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2) :
    (presentSlotsPair a_1 a_2 b_1 b_2 N).card = k := by
  classical
  unfold presentSlotsPair
  have h_N_card : N.card = k - 2 :=
    (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp hN |>.2.1
  have h_e1_notMem : (a_1, b_1) ∉ N := (e1_e2_notMem_of_candidatePair k _ _ _ _ N hN).1
  have h_e2_notMem : (a_2, b_2) ∉ N := (e1_e2_notMem_of_candidatePair k _ _ _ _ N hN).2
  have h_e_distinct : (a_1, b_1) ≠ (a_2, b_2) := fun h =>
    h_a_distinct (by simpa using congrArg Prod.fst h)
  have h_e1_notMem_step : (a_1, b_1) ∉ insert (a_2, b_2) N := by
    rw [Finset.mem_insert]; push_neg; exact ⟨h_e_distinct, h_e1_notMem⟩
  rw [Finset.card_insert_of_notMem h_e1_notMem_step,
      Finset.card_insert_of_notMem h_e2_notMem, h_N_card]
  omega

/-- Disjointness within the 5-piece N-derived absent slot union: aBridge a_1 vs aBridge a_2. -/
lemma aBridge_a1_disjoint_aBridge_a2 {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (h_a_distinct : a_1 ≠ a_2)
    (N : Finset (Fin n_A × Fin n_B)) :
    Disjoint (aBridgeSlots a_1 N) (aBridgeSlots a_2 N) := by
  classical
  rw [Finset.disjoint_left]
  intro ab h1 h2
  rw [aBridgeSlots, Finset.mem_image] at h1 h2
  obtain ⟨_, _, h_eq_x⟩ := h1
  obtain ⟨_, _, h_eq_y⟩ := h2
  rw [← h_eq_x] at h_eq_y
  exact h_a_distinct ((Prod.mk.injEq _ _ _ _).mp h_eq_y).1.symm

/-- bBridge b_1 vs bBridge b_2. -/
lemma bBridge_b1_disjoint_bBridge_b2 {n_A n_B : ℕ}
    (b_1 b_2 : Fin n_B) (h_b_distinct : b_1 ≠ b_2)
    (N : Finset (Fin n_A × Fin n_B)) :
    Disjoint (bBridgeSlots b_1 N) (bBridgeSlots b_2 N) := by
  classical
  rw [Finset.disjoint_left]
  intro ab h1 h2
  rw [bBridgeSlots, Finset.mem_image] at h1 h2
  obtain ⟨_, _, h_eq_x⟩ := h1
  obtain ⟨_, _, h_eq_y⟩ := h2
  rw [← h_eq_x] at h_eq_y
  exact h_b_distinct ((Prod.mk.injEq _ _ _ _).mp h_eq_y).2.symm

/-- aBridge a_1 ∪ aBridge a_2 has card 2·|N| (under candidate-pair distinctness). -/
lemma aBridges_pair_card {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_a_distinct : a_1 ≠ a_2)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) :
    (aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N).card = 2 * N.card := by
  classical
  obtain ⟨h_a1, h_a2, h_b1, h_b2, h_A_inj, h_B_inj⟩ := h_cand
  rw [Finset.card_union_of_disjoint (aBridge_a1_disjoint_aBridge_a2 a_1 a_2 h_a_distinct N)]
  rw [aBridgeSlots_card_of_candidate a_1 b_1 N ⟨h_a1, h_b1, h_A_inj, h_B_inj⟩,
      aBridgeSlots_card_of_candidate a_2 b_1 N ⟨h_a2, h_b1, h_A_inj, h_B_inj⟩]
  ring

/-- bBridge b_1 ∪ bBridge b_2 has card 2·|N|. -/
lemma bBridges_pair_card {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_b_distinct : b_1 ≠ b_2)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) :
    (bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N).card = 2 * N.card := by
  classical
  obtain ⟨h_a1, h_a2, h_b1, h_b2, h_A_inj, h_B_inj⟩ := h_cand
  rw [Finset.card_union_of_disjoint (bBridge_b1_disjoint_bBridge_b2 b_1 b_2 h_b_distinct N)]
  rw [bBridgeSlots_card_of_candidate a_1 b_1 N ⟨h_a1, h_b1, h_A_inj, h_B_inj⟩,
      bBridgeSlots_card_of_candidate a_1 b_2 N ⟨h_a1, h_b2, h_A_inj, h_B_inj⟩]
  ring

/-- aBridges (a_1 ∪ a_2) are disjoint from bBridges (b_1 ∪ b_2). -/
lemma aBridges_disjoint_bBridges_pair {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) :
    Disjoint (aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N)
      (bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N) := by
  classical
  obtain ⟨h_a1, h_a2, h_b1, h_b2, _, _⟩ := h_cand
  rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  -- aBridge a_1 vs bBridge b_1: (a_1, x.2) vs (y.1, b_1). If equal, y.1 = a_1. y ∈ N has y.1 ≠ a_1.
  · rw [Finset.disjoint_left]
    intro ab h1 h2
    rw [aBridgeSlots, Finset.mem_image] at h1
    rw [bBridgeSlots, Finset.mem_image] at h2
    obtain ⟨_, _, h_eq_x⟩ := h1
    obtain ⟨y, hy, h_eq_y⟩ := h2
    rw [← h_eq_x] at h_eq_y
    have : y.1 = a_1 := (Prod.mk.injEq _ _ _ _).mp h_eq_y |>.1
    exact (h_a1 y hy) this
  · rw [Finset.disjoint_left]
    intro ab h1 h2
    rw [aBridgeSlots, Finset.mem_image] at h1
    rw [bBridgeSlots, Finset.mem_image] at h2
    obtain ⟨_, _, h_eq_x⟩ := h1
    obtain ⟨y, hy, h_eq_y⟩ := h2
    rw [← h_eq_x] at h_eq_y
    have : y.1 = a_1 := (Prod.mk.injEq _ _ _ _).mp h_eq_y |>.1
    exact (h_a1 y hy) this
  · rw [Finset.disjoint_left]
    intro ab h1 h2
    rw [aBridgeSlots, Finset.mem_image] at h1
    rw [bBridgeSlots, Finset.mem_image] at h2
    obtain ⟨_, _, h_eq_x⟩ := h1
    obtain ⟨y, hy, h_eq_y⟩ := h2
    rw [← h_eq_x] at h_eq_y
    have : y.1 = a_2 := (Prod.mk.injEq _ _ _ _).mp h_eq_y |>.1
    exact (h_a2 y hy) this
  · rw [Finset.disjoint_left]
    intro ab h1 h2
    rw [aBridgeSlots, Finset.mem_image] at h1
    rw [bBridgeSlots, Finset.mem_image] at h2
    obtain ⟨_, _, h_eq_x⟩ := h1
    obtain ⟨y, hy, h_eq_y⟩ := h2
    rw [← h_eq_x] at h_eq_y
    have : y.1 = a_2 := (Prod.mk.injEq _ _ _ _).mp h_eq_y |>.1
    exact (h_a2 y hy) this

/-- (aBridge a_1 ∪ aBridge a_2 ∪ bBridge b_1 ∪ bBridge b_2) is disjoint from withinNSlots. -/
lemma aBridges_bBridges_disjoint_withinN_pair {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) :
    Disjoint (aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
      bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N) (withinNSlots N) := by
  classical
  obtain ⟨h_a1, h_a2, h_b1, h_b2, h_A_inj, h_B_inj⟩ := h_cand
  -- Use the per-anchor `aBridgeSlots_disjoint_withinNSlots` and similar.
  rw [Finset.disjoint_union_left, Finset.disjoint_union_left, Finset.disjoint_union_left]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact aBridgeSlots_disjoint_withinNSlots a_1 b_1 N ⟨h_a1, h_b1, h_A_inj, h_B_inj⟩
  · exact aBridgeSlots_disjoint_withinNSlots a_2 b_1 N ⟨h_a2, h_b1, h_A_inj, h_B_inj⟩
  · exact bBridgeSlots_disjoint_withinNSlots a_1 b_1 N ⟨h_a1, h_b1, h_A_inj, h_B_inj⟩
  · exact bBridgeSlots_disjoint_withinNSlots a_1 b_2 N ⟨h_a1, h_b2, h_A_inj, h_B_inj⟩

/-- N-derived absent slots have card `4·|N| + |N|·(|N|-1)`. -/
lemma N_derived_absent_card {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_a_distinct : a_1 ≠ a_2) (h_b_distinct : b_1 ≠ b_2)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) :
    (aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
      bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N ∪ withinNSlots N).card
      = 4 * N.card + N.card * (N.card - 1) := by
  classical
  have h_cand_copy := h_cand
  obtain ⟨h_a1, h_a2, h_b1, h_b2, h_A_inj, h_B_inj⟩ := h_cand
  -- Disjointness chain.
  have h_disj_outer :
      Disjoint (aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
        bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N) (withinNSlots N) :=
    aBridges_bBridges_disjoint_withinN_pair a_1 a_2 b_1 b_2 N h_cand_copy
  -- aBridges_pair ∪ bBridges_pair: disjoint by aBridges_disjoint_bBridges_pair.
  have h_disj_ab : Disjoint (aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N)
      (bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N) :=
    aBridges_disjoint_bBridges_pair a_1 a_2 b_1 b_2 N h_cand_copy
  -- Compute step by step.
  rw [Finset.card_union_of_disjoint h_disj_outer]
  -- LHS first: ((aB a_1 ∪ aB a_2) ∪ bB b_1) ∪ bB b_2 — but this is the bBridge pair, written
  -- as (aBs) ∪ (bB b_1) ∪ (bB b_2). Regroup using the associativity.
  have h_re : (aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
    bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N) =
    (aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N) ∪
      (bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N) := by
    rw [Finset.union_assoc, Finset.union_assoc]
  rw [h_re]
  rw [Finset.card_union_of_disjoint h_disj_ab]
  rw [aBridges_pair_card a_1 a_2 b_1 b_2 h_a_distinct N h_cand_copy,
      bBridges_pair_card a_1 a_2 b_1 b_2 h_b_distinct N h_cand_copy,
      withinNSlots_card_of_candidate a_1 b_1 N ⟨h_a1, h_b1, h_A_inj, h_B_inj⟩]
  ring

/-- `absentSlotsPair` has cardinality `k(k-1)`. -/
lemma absentSlotsPair_card {n_A n_B : ℕ} (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_a_distinct : a_1 ≠ a_2) (h_b_distinct : b_1 ≠ b_2)
    (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2) :
    (absentSlotsPair a_1 a_2 b_1 b_2 N).card = k * (k - 1) := by
  classical
  have h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N :=
    (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp hN |>.2.2
  have h_N_card : N.card = k - 2 :=
    (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp hN |>.2.1
  unfold absentSlotsPair
  -- Insert (a_1, b_2) then insert (a_2, b_1) then the 5-union.
  -- First need: (a_1, b_2) ∉ insert (a_2, b_1) (5-union).
  have h_a1b2_ne_a2b1 := a1b2_ne_a2b1 a_1 a_2 b_1 b_2 h_a_distinct
  have h_a1b2_not_5 : (a_1, b_2) ∉ aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
      bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N ∪ withinNSlots N :=
    a1b2_not_mem_N_absent a_1 a_2 b_1 b_2 h_a_distinct h_b_distinct N h_cand
  have h_a1b2_not_step : (a_1, b_2) ∉ insert (a_2, b_1) (aBridgeSlots a_1 N ∪
      aBridgeSlots a_2 N ∪ bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N ∪ withinNSlots N) := by
    rw [Finset.mem_insert]; push_neg; exact ⟨h_a1b2_ne_a2b1, h_a1b2_not_5⟩
  have h_a2b1_not_5 : (a_2, b_1) ∉ aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
      bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N ∪ withinNSlots N :=
    a2b1_not_mem_N_absent a_1 a_2 b_1 b_2 h_a_distinct h_b_distinct N h_cand
  rw [Finset.card_insert_of_notMem h_a1b2_not_step,
      Finset.card_insert_of_notMem h_a2b1_not_5,
      N_derived_absent_card a_1 a_2 b_1 b_2 h_a_distinct h_b_distinct N h_cand,
      h_N_card]
  -- 1 + 1 + 4(k-2) + (k-2)(k-3) = k(k-1).
  -- For k ≥ 2:
  rcases Nat.lt_or_ge 2 k with h_gt | h_eq
  · -- k ≥ 3.
    have h1 : k - 2 + 1 = k - 1 := by omega
    have h2 : k - 2 + 2 = k := by omega
    have h3 : k - 2 - 1 + 1 = k - 2 := by omega
    nlinarith [Nat.sub_add_cancel (show 2 ≤ k from h_k_ge_2),
               Nat.sub_add_cancel (show 1 ≤ k - 2 by omega),
               Nat.sub_add_cancel (show 1 ≤ k by omega)]
  · -- k = 2.
    interval_cases k
    simp

/-- presentSlotsPair is disjoint from absentSlotsPair. -/
lemma presentSlotsPair_disjoint_absentSlotsPair {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_a_distinct : a_1 ≠ a_2) (h_b_distinct : b_1 ≠ b_2)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) :
    Disjoint (presentSlotsPair a_1 a_2 b_1 b_2 N) (absentSlotsPair a_1 a_2 b_1 b_2 N) := by
  classical
  unfold presentSlotsPair absentSlotsPair
  rw [Finset.disjoint_left]
  intro ab h_pres h_abs
  rw [Finset.mem_insert, Finset.mem_insert] at h_pres
  rw [Finset.mem_insert, Finset.mem_insert] at h_abs
  rcases h_pres with h_e1 | h_e2 | h_inN
  · subst h_e1
    -- (a_1, b_1) ∉ absentSlotsPair: not e1-bridge, not e2-bridge, not in N-derived.
    rcases h_abs with h | h
    · -- (a_1, b_1) = (a_1, b_2) → b_1 = b_2.
      exact h_b_distinct ((Prod.mk.injEq _ _ _ _).mp h).2
    rcases h with h | h
    · -- (a_1, b_1) = (a_2, b_1) → a_1 = a_2.
      exact h_a_distinct ((Prod.mk.injEq _ _ _ _).mp h).1
    · -- (a_1, b_1) ∈ 5-piece N-derived absent.
      obtain ⟨h_a1, _, h_b1, _, _, _⟩ := h_cand
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union] at h
      rcases h with ((((h | h) | h) | h) | h)
      · rw [aBridgeSlots, Finset.mem_image] at h
        obtain ⟨x, hx, h_eq⟩ := h
        have : x.2 = b_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
        exact (h_b1 x hx) this
      · rw [aBridgeSlots, Finset.mem_image] at h
        obtain ⟨_, _, h_eq⟩ := h
        have : a_2 = a_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
        exact h_a_distinct this.symm
      · rw [bBridgeSlots, Finset.mem_image] at h
        obtain ⟨x, hx, h_eq⟩ := h
        have : x.1 = a_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
        exact (h_a1 x hx) this
      · rw [bBridgeSlots, Finset.mem_image] at h
        obtain ⟨_, _, h_eq⟩ := h
        have : b_2 = b_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
        exact h_b_distinct this.symm
      · rw [withinNSlots, Finset.mem_image] at h
        obtain ⟨p, hp, h_eq⟩ := h
        rw [Finset.mem_filter, Finset.mem_product] at hp
        have : p.1.1 = a_1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
        exact (h_a1 p.1 hp.1.1) this
  · subst h_e2
    rcases h_abs with h | h
    · exact h_a_distinct ((Prod.mk.injEq _ _ _ _).mp h).1.symm
    rcases h with h | h
    · exact h_b_distinct ((Prod.mk.injEq _ _ _ _).mp h).2.symm
    · obtain ⟨_, h_a2, _, h_b2, _, _⟩ := h_cand
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union] at h
      rcases h with ((((h | h) | h) | h) | h)
      · rw [aBridgeSlots, Finset.mem_image] at h
        obtain ⟨_, _, h_eq⟩ := h
        have : a_1 = a_2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
        exact h_a_distinct this
      · rw [aBridgeSlots, Finset.mem_image] at h
        obtain ⟨x, hx, h_eq⟩ := h
        have : x.2 = b_2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
        exact (h_b2 x hx) this
      · rw [bBridgeSlots, Finset.mem_image] at h
        obtain ⟨_, _, h_eq⟩ := h
        have : b_1 = b_2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
        exact h_b_distinct this
      · rw [bBridgeSlots, Finset.mem_image] at h
        obtain ⟨x, hx, h_eq⟩ := h
        have : x.1 = a_2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
        exact (h_a2 x hx) this
      · rw [withinNSlots, Finset.mem_image] at h
        obtain ⟨p, hp, h_eq⟩ := h
        rw [Finset.mem_filter, Finset.mem_product] at hp
        have : p.1.1 = a_2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
        exact (h_a2 p.1 hp.1.1) this
  · -- ab ∈ N. (ab) ∉ absentSlotsPair.
    rcases h_abs with h | h
    · -- ab = (a_1, b_2). N's elements have A-coord ≠ a_1.
      obtain ⟨h_a1, _, _, _, _, _⟩ := h_cand
      apply h_a1 ab h_inN
      rw [h]
    rcases h with h | h
    · obtain ⟨_, h_a2, _, _, _, _⟩ := h_cand
      apply h_a2 ab h_inN
      rw [h]
    · -- ab ∈ N ∩ 5-piece N-derived absent slots. We need ab ∉ each N-derived piece.
      obtain ⟨h_a1, h_a2, h_b1, h_b2, h_A_inj, h_B_inj⟩ := h_cand
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union] at h
      rcases h with ((((h | h) | h) | h) | h)
      · rw [aBridgeSlots, Finset.mem_image] at h
        obtain ⟨_, _, h_eq⟩ := h
        have : ab.1 = a_1 := by rw [← h_eq]
        exact (h_a1 ab h_inN) this
      · rw [aBridgeSlots, Finset.mem_image] at h
        obtain ⟨_, _, h_eq⟩ := h
        have : ab.1 = a_2 := by rw [← h_eq]
        exact (h_a2 ab h_inN) this
      · rw [bBridgeSlots, Finset.mem_image] at h
        obtain ⟨_, _, h_eq⟩ := h
        have : ab.2 = b_1 := by rw [← h_eq]
        exact (h_b1 ab h_inN) this
      · rw [bBridgeSlots, Finset.mem_image] at h
        obtain ⟨_, _, h_eq⟩ := h
        have : ab.2 = b_2 := by rw [← h_eq]
        exact (h_b2 ab h_inN) this
      · exact (Finset.disjoint_left.mp (withinNSlots_disjoint_N a_1 b_1 N
          ⟨h_a1, h_b1, h_A_inj, h_B_inj⟩)) h h_inN

/-! ## PS.4.c.5: per-candidate integration formula -/

/-- For a candidate N: the bridge-(a_1, _) product equals product over the image. -/
lemma aBridge_a1_prod_eq_image_prod {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) (f : Fin n_A × Fin n_B → ℝ) :
    (∏ x ∈ N, f (a_1, x.2)) = ∏ ab ∈ aBridgeSlots a_1 N, f ab := by
  classical
  obtain ⟨h_a1, _, h_b1, _, h_A_inj, h_B_inj⟩ := h_cand
  exact aBridge_prod_eq_image_prod a_1 b_1 N ⟨h_a1, h_b1, h_A_inj, h_B_inj⟩ f

lemma aBridge_a2_prod_eq_image_prod {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) (f : Fin n_A × Fin n_B → ℝ) :
    (∏ x ∈ N, f (a_2, x.2)) = ∏ ab ∈ aBridgeSlots a_2 N, f ab := by
  classical
  obtain ⟨_, h_a2, h_b1, _, h_A_inj, h_B_inj⟩ := h_cand
  exact aBridge_prod_eq_image_prod a_2 b_1 N ⟨h_a2, h_b1, h_A_inj, h_B_inj⟩ f

lemma bBridge_b1_prod_eq_image_prod {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) (f : Fin n_A × Fin n_B → ℝ) :
    (∏ x ∈ N, f (x.1, b_1)) = ∏ ab ∈ bBridgeSlots b_1 N, f ab := by
  classical
  obtain ⟨h_a1, _, h_b1, _, h_A_inj, h_B_inj⟩ := h_cand
  exact bBridge_prod_eq_image_prod a_1 b_1 N ⟨h_a1, h_b1, h_A_inj, h_B_inj⟩ f

lemma bBridge_b2_prod_eq_image_prod {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) (f : Fin n_A × Fin n_B → ℝ) :
    (∏ x ∈ N, f (x.1, b_2)) = ∏ ab ∈ bBridgeSlots b_2 N, f ab := by
  classical
  obtain ⟨h_a1, _, _, h_b2, h_A_inj, h_B_inj⟩ := h_cand
  exact bBridge_prod_eq_image_prod a_1 b_2 N ⟨h_a1, h_b2, h_A_inj, h_B_inj⟩ f

lemma withinN_prod_pair_eq_image_prod {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) (f : Fin n_A × Fin n_B → ℝ) :
    (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2), f (p.1.1, p.2.2))
      = ∏ ab ∈ withinNSlots N, f ab := by
  classical
  obtain ⟨h_a1, _, h_b1, _, h_A_inj, h_B_inj⟩ := h_cand
  exact withinN_prod_eq_image_prod a_1 b_1 N ⟨h_a1, h_b1, h_A_inj, h_B_inj⟩ f

/-- For candidate pair N: pointwise factoring of `matchingPairIndicator` as two products. -/
lemma matchingPairIndicator_eq_product_form {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_a_distinct : a_1 ≠ a_2) (h_b_distinct : b_1 ≠ b_2)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N)
    (h_e1_notMem : (a_1, b_1) ∉ N) (h_e2_notMem : (a_2, b_2) ∉ N)
    (g : Fin n_A × Fin n_B → Bool) :
    matchingPairIndicator a_1 a_2 b_1 b_2 N g
      = (∏ ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N,
            DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g) *
        (∏ ab ∈ absentSlotsPair a_1 a_2 b_1 b_2 N,
            (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g)) := by
  classical
  -- Rewrite presentSlotsPair = insert (a_1, b_1) (insert (a_2, b_2) N).
  have h_e_distinct : (a_1, b_1) ≠ (a_2, b_2) := fun h =>
    h_a_distinct (by simpa using congrArg Prod.fst h)
  have h_e1_notMem_step : (a_1, b_1) ∉ insert (a_2, b_2) N := by
    rw [Finset.mem_insert]; push_neg; exact ⟨h_e_distinct, h_e1_notMem⟩
  have h_presentProd :
      (if g (a_1, b_1) = true then (1 : ℝ) else 0) *
      (if g (a_2, b_2) = true then (1 : ℝ) else 0) *
      (∏ x ∈ N, if g x = true then (1 : ℝ) else 0)
        = ∏ ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N,
            DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g := by
    unfold presentSlotsPair
    rw [Finset.prod_insert h_e1_notMem_step, Finset.prod_insert h_e2_notMem]
    rw [if_eq_edgeIndicator (a_1, b_1) g, if_eq_edgeIndicator (a_2, b_2) g]
    have h_N_re : (∏ x ∈ N, if g x = true then (1 : ℝ) else 0)
        = ∏ x ∈ N, DaveyThesis2024.BipartiteRandomGraph.edgeIndicator x.1 x.2 g := by
      apply Finset.prod_congr rfl
      intro x _; exact if_eq_edgeIndicator x g
    rw [h_N_re]
    ring
  -- Rewrite absentSlotsPair = insert (a_1, b_2) (insert (a_2, b_1) (5-union)).
  have h_a1b2_ne_a2b1 := a1b2_ne_a2b1 a_1 a_2 b_1 b_2 h_a_distinct
  have h_a1b2_not_5 : (a_1, b_2) ∉ aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
      bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N ∪ withinNSlots N :=
    a1b2_not_mem_N_absent a_1 a_2 b_1 b_2 h_a_distinct h_b_distinct N h_cand
  have h_a1b2_not_step : (a_1, b_2) ∉ insert (a_2, b_1) (aBridgeSlots a_1 N ∪
      aBridgeSlots a_2 N ∪ bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N ∪ withinNSlots N) := by
    rw [Finset.mem_insert]; push_neg; exact ⟨h_a1b2_ne_a2b1, h_a1b2_not_5⟩
  have h_a2b1_not_5 : (a_2, b_1) ∉ aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
      bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N ∪ withinNSlots N :=
    a2b1_not_mem_N_absent a_1 a_2 b_1 b_2 h_a_distinct h_b_distinct N h_cand
  -- Compute the absent product.
  -- absentSlotsPair = insert (a_1, b_2) (insert (a_2, b_1) (5-union)).
  -- Hence ∏ ab ∈ absentSlotsPair, ... = (f at (a_1, b_2)) * (f at (a_2, b_1)) * ∏ over 5-union.
  -- The 5-union splits as aBridge_a1 ∪ aBridge_a2 ∪ bBridge_b1 ∪ bBridge_b2 ∪ withinN.
  -- Disjointness chain (use the previously-proven lemmas).
  have h_disj_outer :
      Disjoint (aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
        bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N) (withinNSlots N) :=
    aBridges_bBridges_disjoint_withinN_pair a_1 a_2 b_1 b_2 N h_cand
  have h_disj_ab : Disjoint (aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N)
      (bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N) :=
    aBridges_disjoint_bBridges_pair a_1 a_2 b_1 b_2 N h_cand
  have h_disj_aa := aBridge_a1_disjoint_aBridge_a2 a_1 a_2 h_a_distinct N
  have h_disj_bb := bBridge_b1_disjoint_bBridge_b2 b_1 b_2 h_b_distinct N
  have h_absentProd :
      (if g (a_1, b_2) = true then (0 : ℝ) else 1) *
      (if g (a_2, b_1) = true then (0 : ℝ) else 1) *
      (∏ x ∈ N, if g (a_1, x.2) = true then (0 : ℝ) else 1) *
      (∏ x ∈ N, if g (a_2, x.2) = true then (0 : ℝ) else 1) *
      (∏ x ∈ N, if g (x.1, b_1) = true then (0 : ℝ) else 1) *
      (∏ x ∈ N, if g (x.1, b_2) = true then (0 : ℝ) else 1) *
      (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
          if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1)
        = ∏ ab ∈ absentSlotsPair a_1 a_2 b_1 b_2 N,
            (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g) := by
    -- Convert each `if` factor to `1 - edgeIndicator`.
    rw [if_eq_one_minus_edgeIndicator (a_1, b_2) g,
        if_eq_one_minus_edgeIndicator (a_2, b_1) g]
    have h_a1_re : (∏ x ∈ N, if g (a_1, x.2) = true then (0 : ℝ) else 1)
        = ∏ x ∈ N, (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator
                          (a_1, x.2).1 (a_1, x.2).2 g) := by
      apply Finset.prod_congr rfl; intro x _; exact if_eq_one_minus_edgeIndicator (a_1, x.2) g
    have h_a2_re : (∏ x ∈ N, if g (a_2, x.2) = true then (0 : ℝ) else 1)
        = ∏ x ∈ N, (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator
                          (a_2, x.2).1 (a_2, x.2).2 g) := by
      apply Finset.prod_congr rfl; intro x _; exact if_eq_one_minus_edgeIndicator (a_2, x.2) g
    have h_b1_re : (∏ x ∈ N, if g (x.1, b_1) = true then (0 : ℝ) else 1)
        = ∏ x ∈ N, (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator
                          (x.1, b_1).1 (x.1, b_1).2 g) := by
      apply Finset.prod_congr rfl; intro x _; exact if_eq_one_minus_edgeIndicator (x.1, b_1) g
    have h_b2_re : (∏ x ∈ N, if g (x.1, b_2) = true then (0 : ℝ) else 1)
        = ∏ x ∈ N, (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator
                          (x.1, b_2).1 (x.1, b_2).2 g) := by
      apply Finset.prod_congr rfl; intro x _; exact if_eq_one_minus_edgeIndicator (x.1, b_2) g
    have h_w_re : (∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
            if g (p.1.1, p.2.2) = true then (0 : ℝ) else 1)
        = ∏ p ∈ (N ×ˢ N).filter (fun p => p.1 ≠ p.2),
            (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator
                  (p.1.1, p.2.2).1 (p.1.1, p.2.2).2 g) := by
      apply Finset.prod_congr rfl; intro p _; exact if_eq_one_minus_edgeIndicator (p.1.1, p.2.2) g
    rw [h_a1_re, h_a2_re, h_b1_re, h_b2_re, h_w_re]
    -- Convert each product over N to product over the image (aBridge / bBridge / within).
    rw [aBridge_a1_prod_eq_image_prod a_1 a_2 b_1 b_2 N h_cand
        (fun ab => 1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g),
        aBridge_a2_prod_eq_image_prod a_1 a_2 b_1 b_2 N h_cand
        (fun ab => 1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g),
        bBridge_b1_prod_eq_image_prod a_1 a_2 b_1 b_2 N h_cand
        (fun ab => 1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g),
        bBridge_b2_prod_eq_image_prod a_1 a_2 b_1 b_2 N h_cand
        (fun ab => 1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g),
        withinN_prod_pair_eq_image_prod a_1 a_2 b_1 b_2 N h_cand
        (fun ab => 1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g)]
    -- Combine into product over absentSlotsPair = insert (a_1, b_2) (insert (a_2, b_1) (5-union)).
    unfold absentSlotsPair
    rw [Finset.prod_insert h_a1b2_not_step, Finset.prod_insert h_a2b1_not_5]
    -- RHS form: (1 - e_a1b2) * ((1 - e_a2b1) * ∏ over 5-union). The 5-union is the
    -- left-associated `((((aB a_1) ∪ aB a_2) ∪ bB b_1) ∪ bB b_2) ∪ withinN`.
    -- Replace ∏ over 5-union by the product split via the disjointness lemmas.
    have h_split :
        (∏ ab ∈ aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
            bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N ∪ withinNSlots N,
            (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g))
        = (∏ ab ∈ aBridgeSlots a_1 N,
              (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g)) *
          (∏ ab ∈ aBridgeSlots a_2 N,
              (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g)) *
          (∏ ab ∈ bBridgeSlots b_1 N,
              (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g)) *
          (∏ ab ∈ bBridgeSlots b_2 N,
              (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g)) *
          (∏ ab ∈ withinNSlots N,
              (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g)) := by
      -- Disjointness of bB b_1 and bB b_2 (used in the final split below).
      -- We split iteratively from outside in: first peel off withinN, then split aBs and bBs.
      rw [Finset.prod_union h_disj_outer]
      -- Goal: ∏ over (aB a_1 ∪ aB a_2 ∪ bB b_1 ∪ bB b_2) * ∏ over withinN = RHS.
      -- Re-associate the inner union: aB a_1 ∪ aB a_2 ∪ bB b_1 ∪ bB b_2
      --   = (aB a_1 ∪ aB a_2) ∪ (bB b_1 ∪ bB b_2)
      have h_inner : aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N ∪
          bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N =
          (aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N) ∪
            (bBridgeSlots b_1 N ∪ bBridgeSlots b_2 N) := by
        rw [Finset.union_assoc (aBridgeSlots a_1 N ∪ aBridgeSlots a_2 N)
              (bBridgeSlots b_1 N) (bBridgeSlots b_2 N)]
      rw [h_inner]
      rw [Finset.prod_union h_disj_ab,
          Finset.prod_union h_disj_aa,
          Finset.prod_union h_disj_bb]
      ring
    rw [h_split]
    ring
  unfold matchingPairIndicator
  rw [← h_presentProd, ← h_absentProd]
  ring

open DaveyThesis2024.BipartiteRandomGraph in
/-- **Per-candidate integration formula (Step C-final, pair case).**

For a candidate `N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2`, the integral
of `matchingPairIndicator g` over the bipartite edge-choice measure equals
`p^k · (1-p)^(k(k-1))`. -/
lemma integral_matchingPairIndicator_eq
    {n_A n_B : ℕ} (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_a_distinct : a_1 ≠ a_2) (h_b_distinct : b_1 ≠ b_2)
    (N : Finset (Fin n_A × Fin n_B))
    (h_candidate : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2)
    (p : ENNReal) (hp_le : p ≤ 1) :
    ∫ g, matchingPairIndicator a_1 a_2 b_1 b_2 N g
        ∂((bipartiteEdgeChoice n_A n_B p hp_le).toMeasure)
      = p.toReal ^ k * (1 - p.toReal) ^ (k * (k - 1)) := by
  classical
  set μ := (bipartiteEdgeChoice n_A n_B p hp_le).toMeasure with hμ
  have h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N :=
    (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp h_candidate |>.2.2
  have h_e1_notMem : (a_1, b_1) ∉ N :=
    (e1_e2_notMem_of_candidatePair k a_1 a_2 b_1 b_2 N h_candidate).1
  have h_e2_notMem : (a_2, b_2) ∉ N :=
    (e1_e2_notMem_of_candidatePair k a_1 a_2 b_1 b_2 N h_candidate).2
  have h_pres_card : (presentSlotsPair a_1 a_2 b_1 b_2 N).card = k :=
    presentSlotsPair_card k h_k_ge_2 a_1 a_2 b_1 b_2 N h_a_distinct h_candidate
  have h_abs_card : (absentSlotsPair a_1 a_2 b_1 b_2 N).card = k * (k - 1) :=
    absentSlotsPair_card k h_k_ge_2 a_1 a_2 b_1 b_2 h_a_distinct h_b_distinct N h_candidate
  have h_disj : Disjoint (presentSlotsPair a_1 a_2 b_1 b_2 N)
      (absentSlotsPair a_1 a_2 b_1 b_2 N) :=
    presentSlotsPair_disjoint_absentSlotsPair a_1 a_2 b_1 b_2 h_a_distinct h_b_distinct N h_cand
  let S : Finset (Fin n_A × Fin n_B) :=
    presentSlotsPair a_1 a_2 b_1 b_2 N ∪ absentSlotsPair a_1 a_2 b_1 b_2 N
  let g_slot : ↥S → ℝ → ℝ := fun i x =>
    if i.val ∈ presentSlotsPair a_1 a_2 b_1 b_2 N then x else 1 - x
  let X_slot : ↥S → (Fin n_A × Fin n_B → Bool) → ℝ :=
    fun i f => edgeIndicator i.val.1 i.val.2 f
  -- Pointwise factorisation.
  have h_pointwise : ∀ f, matchingPairIndicator a_1 a_2 b_1 b_2 N f =
      ∏ i : ↥S, g_slot i (X_slot i f) := by
    intro f
    rw [matchingPairIndicator_eq_product_form a_1 a_2 b_1 b_2
        h_a_distinct h_b_distinct N h_cand h_e1_notMem h_e2_notMem f]
    have h_univ : (Finset.univ : Finset ↥S) = S.attach := rfl
    rw [h_univ, Finset.prod_attach S (fun ab : Fin n_A × Fin n_B =>
      if ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N then edgeIndicator ab.1 ab.2 f
      else 1 - edgeIndicator ab.1 ab.2 f)]
    change (∏ ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N, edgeIndicator ab.1 ab.2 f) *
         (∏ ab ∈ absentSlotsPair a_1 a_2 b_1 b_2 N, (1 - edgeIndicator ab.1 ab.2 f))
       = ∏ ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N ∪ absentSlotsPair a_1 a_2 b_1 b_2 N,
          if ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N then edgeIndicator ab.1 ab.2 f
          else 1 - edgeIndicator ab.1 ab.2 f
    rw [Finset.prod_union h_disj]
    have h_pres_re : (∏ ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N, edgeIndicator ab.1 ab.2 f)
        = ∏ ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N,
            if ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N then edgeIndicator ab.1 ab.2 f
            else 1 - edgeIndicator ab.1 ab.2 f := by
      apply Finset.prod_congr rfl; intro ab h_ab; rw [if_pos h_ab]
    have h_abs_re : (∏ ab ∈ absentSlotsPair a_1 a_2 b_1 b_2 N,
            (1 - edgeIndicator ab.1 ab.2 f))
        = ∏ ab ∈ absentSlotsPair a_1 a_2 b_1 b_2 N,
            if ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N then edgeIndicator ab.1 ab.2 f
            else 1 - edgeIndicator ab.1 ab.2 f := by
      apply Finset.prod_congr rfl; intro ab h_ab
      have h_notIn : ab ∉ presentSlotsPair a_1 a_2 b_1 b_2 N :=
        fun h => Finset.disjoint_left.mp h_disj h h_ab
      rw [if_neg h_notIn]
    rw [h_pres_re, h_abs_re]
  have h_inj : Function.Injective (fun i : ↥S => i.val) := Subtype.val_injective
  have h_iIndep_X : ProbabilityTheory.iIndepFun X_slot μ := by
    have h_full := DaveyThesis2024.SecRandomBipartite.edgeIndicator_full_iIndepFun (n_A := n_A) (n_B := n_B) p hp_le
    exact h_full.precomp (g := fun i : ↥S => i.val) h_inj
  have h_g_meas : ∀ i, Measurable (g_slot i) := fun i => by
    by_cases h : i.val ∈ presentSlotsPair a_1 a_2 b_1 b_2 N
    · simp only [g_slot, h, if_true]; exact measurable_id
    · simp only [g_slot, h, if_false]; fun_prop
  have h_X_meas : ∀ i, Measurable (X_slot i) := fun i =>
    measurable_edgeIndicator i.val.1 i.val.2
  have h_iIndep_gX : ProbabilityTheory.iIndepFun
      (fun i f => g_slot i (X_slot i f)) μ := h_iIndep_X.comp g_slot h_g_meas
  have h_aestrong : ∀ i, MeasureTheory.AEStronglyMeasurable
      (fun f => g_slot i (X_slot i f)) μ :=
    fun i => ((h_g_meas i).comp (h_X_meas i)).aestronglyMeasurable
  have h_int_eq :
      ∫ f, matchingPairIndicator a_1 a_2 b_1 b_2 N f ∂μ =
        ∫ f, ∏ i : ↥S, g_slot i (X_slot i f) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with f using h_pointwise f
  rw [h_int_eq]
  rw [h_iIndep_gX.integral_fun_prod_eq_prod_integral h_aestrong]
  have h_each : ∀ i : ↥S,
      ∫ f, g_slot i (X_slot i f) ∂μ
        = if i.val ∈ presentSlotsPair a_1 a_2 b_1 b_2 N then p.toReal else 1 - p.toReal := by
    intro i
    by_cases h : i.val ∈ presentSlotsPair a_1 a_2 b_1 b_2 N
    · simp only [g_slot, h, if_true, X_slot, hμ]
      exact integral_edgeIndicator_eq p hp_le i.val.1 i.val.2
    · simp only [g_slot, h, if_false, X_slot, hμ]
      exact DaveyThesis2024.SecRandomBipartite.integral_complementEdgeIndicator_eq p hp_le i.val.1 i.val.2
  rw [Finset.prod_congr rfl (fun i _ => h_each i)]
  have h_univ : (Finset.univ : Finset ↥S) = S.attach := rfl
  rw [h_univ]
  rw [Finset.prod_attach S (fun ab : Fin n_A × Fin n_B =>
    if ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N then p.toReal else 1 - p.toReal)]
  change (∏ ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N ∪ absentSlotsPair a_1 a_2 b_1 b_2 N,
          if ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N then p.toReal else 1 - p.toReal)
       = p.toReal ^ k * (1 - p.toReal) ^ (k * (k - 1))
  rw [Finset.prod_union h_disj]
  have h_pres_eval :
      (∏ ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N,
          if ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N then p.toReal else 1 - p.toReal)
        = p.toReal ^ (presentSlotsPair a_1 a_2 b_1 b_2 N).card := by
    rw [Finset.prod_congr rfl (fun ab h_ab => if_pos h_ab)]
    rw [Finset.prod_const]
  have h_abs_eval :
      (∏ ab ∈ absentSlotsPair a_1 a_2 b_1 b_2 N,
          if ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N then p.toReal else 1 - p.toReal)
        = (1 - p.toReal) ^ (absentSlotsPair a_1 a_2 b_1 b_2 N).card := by
    apply Eq.trans
    · apply Finset.prod_congr rfl
      intro ab h_ab
      have h_notIn : ab ∉ presentSlotsPair a_1 a_2 b_1 b_2 N :=
        fun h => Finset.disjoint_left.mp h_disj h h_ab
      rw [if_neg h_notIn]
    · rw [Finset.prod_const]
  rw [h_pres_eval, h_abs_eval, h_pres_card, h_abs_card]

/-! ## PS.4.c.6: cardinality of candidatePairPartnerSet -/

/-- For a candidate pair N: `N.image fst ⊆ (univ.erase a_1).erase a_2`. -/
lemma candidatePair_image_fst_subset {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2) :
    N.image Prod.fst ⊆ (Finset.univ.erase a_1).erase a_2 := by
  classical
  rw [mem_candidatePairPartnerSet_iff] at hN
  obtain ⟨_, _, h_a1, h_a2, _, _, _, _⟩ := hN
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨y, hy, h_eq⟩ := hx
  rw [Finset.mem_erase, Finset.mem_erase]
  refine ⟨?_, ?_, Finset.mem_univ _⟩
  · rw [← h_eq]; exact h_a2 y hy
  · rw [← h_eq]; exact h_a1 y hy

/-- For a candidate pair N: `(N.image fst).card = k - 2`. -/
lemma candidatePair_image_fst_card {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2) :
    (N.image Prod.fst).card = k - 2 := by
  classical
  rw [mem_candidatePairPartnerSet_iff] at hN
  obtain ⟨_, h_N_card, _, _, _, _, h_A_inj, _⟩ := hN
  rw [Finset.card_image_of_injOn, h_N_card]
  intro x hx y hy h_eq
  by_contra h_ne
  exact (h_A_inj x hx y hy h_ne) h_eq

/-- For a candidate pair N and an A-coord x ∈ N.image fst, the unique B-coord. -/
noncomputable def candidatePairPairing_witness {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (_hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2)
    (x : ↥(N.image Prod.fst)) :
    {y : Fin n_A × Fin n_B // y ∈ N ∧ y.1 = x.val} := by
  classical
  have hx : x.val ∈ N.image Prod.fst := x.property
  rw [Finset.mem_image] at hx
  exact ⟨Classical.choose hx,
    (Classical.choose_spec hx).1, (Classical.choose_spec hx).2⟩

noncomputable def candidatePairPairing {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2) :
    ↥(N.image Prod.fst) → Fin n_B :=
  fun x => (candidatePairPairing_witness k a_1 a_2 b_1 b_2 N hN x).val.2

lemma candidatePairPairing_spec {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2)
    (x : ↥(N.image Prod.fst)) :
    (x.val, candidatePairPairing k a_1 a_2 b_1 b_2 N hN x) ∈ N := by
  classical
  unfold candidatePairPairing
  have h_props := (candidatePairPairing_witness k a_1 a_2 b_1 b_2 N hN x).property
  have h_in := h_props.1
  have h_fst := h_props.2
  set y := (candidatePairPairing_witness k a_1 a_2 b_1 b_2 N hN x).val with hy_def
  have h_eq : (x.val, y.2) = y := by rw [← h_fst]
  rw [h_eq]; exact h_in

lemma candidatePairPairing_mem_erase {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2)
    (x : ↥(N.image Prod.fst)) :
    candidatePairPairing k a_1 a_2 b_1 b_2 N hN x ∈
      ((Finset.univ.erase b_1).erase b_2 : Finset (Fin n_B)) := by
  classical
  have h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N :=
    (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp hN |>.2.2
  have h_in : (x.val, candidatePairPairing k a_1 a_2 b_1 b_2 N hN x) ∈ N :=
    candidatePairPairing_spec k a_1 a_2 b_1 b_2 N hN x
  rw [Finset.mem_erase, Finset.mem_erase]
  refine ⟨?_, ?_, Finset.mem_univ _⟩
  · exact h_cand.2.2.2.1 (x.val, _) h_in
  · exact h_cand.2.2.1 (x.val, _) h_in

lemma candidatePairPairing_injective {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2) :
    Function.Injective (candidatePairPairing k a_1 a_2 b_1 b_2 N hN) := by
  classical
  have h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N :=
    (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp hN |>.2.2
  intro x y h_eq
  have hx_in := candidatePairPairing_spec k a_1 a_2 b_1 b_2 N hN x
  have hy_in := candidatePairPairing_spec k a_1 a_2 b_1 b_2 N hN y
  by_contra h_ne_sub
  have h_val_ne : x.val ≠ y.val := fun h_eq_val => h_ne_sub (Subtype.ext h_eq_val)
  have h_xy_ne : ((x.val, candidatePairPairing k a_1 a_2 b_1 b_2 N hN x) : Fin n_A × Fin n_B)
      ≠ (y.val, candidatePairPairing k a_1 a_2 b_1 b_2 N hN y) := by
    intro h
    exact h_val_ne ((Prod.mk.injEq _ _ _ _).mp h).1
  exact (h_cand.2.2.2.2.2 _ hx_in _ hy_in h_xy_ne) h_eq

/-- The inverse direction: given A_set + embedding f, construct an N candidate. -/
noncomputable def embToPairFiber {n_A n_B : ℕ}
    (b_1 b_2 : Fin n_B) (A_set : Finset (Fin n_A))
    (f : ↥A_set ↪ ↥(((Finset.univ.erase b_1).erase b_2 : Finset (Fin n_B))))
    : Finset (Fin n_A × Fin n_B) :=
  A_set.attach.image (fun x => (x.val, (f x).val))

lemma mem_embToPairFiber {n_A n_B : ℕ}
    (b_1 b_2 : Fin n_B) (A_set : Finset (Fin n_A))
    (f : ↥A_set ↪ ↥(((Finset.univ.erase b_1).erase b_2 : Finset (Fin n_B))))
    (ab : Fin n_A × Fin n_B) :
    ab ∈ embToPairFiber b_1 b_2 A_set f ↔
      ∃ (h : ab.1 ∈ A_set), ab.2 = (f ⟨ab.1, h⟩).val := by
  classical
  unfold embToPairFiber
  rw [Finset.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, _, h_eq⟩
    have h1 : x.val = ab.1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
    have h2 : (f x).val = ab.2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
    have h_ab1_in : ab.1 ∈ A_set := h1 ▸ x.property
    refine ⟨h_ab1_in, ?_⟩
    have h_x_eq : x = ⟨ab.1, h_ab1_in⟩ := Subtype.ext h1
    rw [← h2, h_x_eq]
  · rintro ⟨h, h_eq⟩
    refine ⟨⟨ab.1, h⟩, Finset.mem_attach _ _, ?_⟩
    change (ab.1, (f ⟨ab.1, h⟩).val) = ab
    rw [← h_eq]

lemma embToPairFiber_mem_candidatePairPartnerSet {n_A n_B : ℕ} (k : ℕ) (_h_k_ge_2 : 2 ≤ k)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (A_set : Finset (Fin n_A))
    (h_A_sub : A_set ⊆ (Finset.univ.erase a_1).erase a_2) (h_A_card : A_set.card = k - 2)
    (f : ↥A_set ↪ ↥(((Finset.univ.erase b_1).erase b_2 : Finset (Fin n_B)))) :
    embToPairFiber b_1 b_2 A_set f ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2 := by
  classical
  rw [mem_candidatePairPartnerSet_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- N ⊆ (univ.erase a_1, b_1).erase (a_2, b_2)
    intro ab h_ab
    rw [mem_embToPairFiber] at h_ab
    obtain ⟨h_in_A, h_eq⟩ := h_ab
    rw [Finset.mem_erase, Finset.mem_erase]
    have h_in_erase := h_A_sub h_in_A
    rw [Finset.mem_erase, Finset.mem_erase] at h_in_erase
    have h_a_ne_a1 : ab.1 ≠ a_1 := h_in_erase.2.1
    have h_a_ne_a2 : ab.1 ≠ a_2 := h_in_erase.1
    refine ⟨?_, ?_, Finset.mem_univ _⟩
    · intro h; rw [Prod.mk.injEq] at h; exact h_a_ne_a2 h.1
    · intro h; rw [Prod.mk.injEq] at h; exact h_a_ne_a1 h.1
  · -- card = k - 2
    unfold embToPairFiber
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_attach, h_A_card]
    · intro x y h_eq
      exact Subtype.ext ((Prod.mk.injEq _ _ _ _).mp h_eq |>.1)
  · -- A-coord ≠ a_1
    intro x h_x
    rw [mem_embToPairFiber] at h_x
    obtain ⟨h_in_A, _⟩ := h_x
    have h_in_erase := h_A_sub h_in_A
    rw [Finset.mem_erase, Finset.mem_erase] at h_in_erase
    exact h_in_erase.2.1
  · -- A-coord ≠ a_2
    intro x h_x
    rw [mem_embToPairFiber] at h_x
    obtain ⟨h_in_A, _⟩ := h_x
    have h_in_erase := h_A_sub h_in_A
    rw [Finset.mem_erase, Finset.mem_erase] at h_in_erase
    exact h_in_erase.1
  · -- B-coord ≠ b_1
    intro x h_x
    rw [mem_embToPairFiber] at h_x
    obtain ⟨h_in_A, h_eq⟩ := h_x
    rw [h_eq]
    have := (f ⟨x.1, h_in_A⟩).property
    rw [Finset.mem_erase, Finset.mem_erase] at this
    exact this.2.1
  · -- B-coord ≠ b_2
    intro x h_x
    rw [mem_embToPairFiber] at h_x
    obtain ⟨h_in_A, h_eq⟩ := h_x
    rw [h_eq]
    have := (f ⟨x.1, h_in_A⟩).property
    rw [Finset.mem_erase, Finset.mem_erase] at this
    exact this.1
  · -- A-coords pairwise distinct
    intro x h_x y h_y h_ne
    rw [mem_embToPairFiber] at h_x h_y
    obtain ⟨h_x_in, h_x_eq⟩ := h_x
    obtain ⟨h_y_in, h_y_eq⟩ := h_y
    intro h_a_eq
    apply h_ne
    have h_sub_eq : (⟨x.1, h_x_in⟩ : ↥A_set) = ⟨y.1, h_y_in⟩ := Subtype.ext h_a_eq
    have h_2 : x.2 = y.2 := by rw [h_x_eq, h_y_eq, h_sub_eq]
    exact Prod.ext h_a_eq h_2
  · -- B-coords pairwise distinct
    intro x h_x y h_y h_ne
    rw [mem_embToPairFiber] at h_x h_y
    obtain ⟨h_x_in, h_x_eq⟩ := h_x
    obtain ⟨h_y_in, h_y_eq⟩ := h_y
    intro h_b_eq
    apply h_ne
    rw [h_x_eq, h_y_eq] at h_b_eq
    have h_sub_eq : f ⟨x.1, h_x_in⟩ = f ⟨y.1, h_y_in⟩ := Subtype.ext h_b_eq
    have h_pre_eq : ((⟨x.1, h_x_in⟩ : ↥A_set)) = ⟨y.1, h_y_in⟩ := f.injective h_sub_eq
    have h_fst_eq : x.1 = y.1 := congrArg Subtype.val h_pre_eq
    have h_2 : x.2 = y.2 := by rw [h_x_eq, h_y_eq, h_pre_eq]
    exact Prod.ext h_fst_eq h_2

lemma embToPairFiber_image_fst {n_A n_B : ℕ}
    (b_1 b_2 : Fin n_B) (A_set : Finset (Fin n_A))
    (f : ↥A_set ↪ ↥(((Finset.univ.erase b_1).erase b_2 : Finset (Fin n_B)))) :
    (embToPairFiber b_1 b_2 A_set f).image Prod.fst = A_set := by
  classical
  ext x
  rw [Finset.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨ab, h_ab, h_eq⟩
    rw [mem_embToPairFiber] at h_ab
    obtain ⟨h_in, _⟩ := h_ab
    rw [← h_eq]; exact h_in
  · intro h_x
    refine ⟨(x, (f ⟨x, h_x⟩).val), ?_, rfl⟩
    rw [mem_embToPairFiber]
    exact ⟨h_x, rfl⟩

open Finset in
/-- **Step D (pair case): cardinality of `candidatePairPartnerSet`.** -/
lemma candidatePairPartnerSet_card
    {n_A n_B : ℕ} (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (h_k_le_A : k ≤ n_A) (h_k_le_B : k ≤ n_B)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_a_distinct : a_1 ≠ a_2) (h_b_distinct : b_1 ≠ b_2) :
    (candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card
      = Nat.choose (n_A - 2) (k - 2) * Nat.choose (n_B - 2) (k - 2) * Nat.factorial (k - 2) := by
  classical
  -- Step 1: fiber decomposition by A-projection.
  have h_fiber :
      Set.MapsTo (fun N : Finset (Fin n_A × Fin n_B) => N.image Prod.fst)
        ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2 : Finset _) : Set _)
        ((((Finset.univ.erase a_1).erase a_2 : Finset (Fin n_A)).powersetCard (k - 2) :
          Finset _) : Set _) := by
    intro N hN
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    have hN' : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2 := hN
    exact ⟨candidatePair_image_fst_subset k a_1 a_2 b_1 b_2 N hN',
           candidatePair_image_fst_card k a_1 a_2 b_1 b_2 N hN'⟩
  rw [Finset.card_eq_sum_card_fiberwise h_fiber]
  -- Step 2: each fiber has size (n_B - 2).descFactorial (k - 2).
  have h_each_fiber : ∀ A_set ∈ ((Finset.univ.erase a_1).erase a_2 :
        Finset (Fin n_A)).powersetCard (k - 2),
      ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).filter
        (fun N => N.image Prod.fst = A_set)).card
        = (n_B - 2).descFactorial (k - 2) := by
    intro A_set h_A_set
    rw [Finset.mem_powersetCard] at h_A_set
    obtain ⟨h_A_sub, h_A_card⟩ := h_A_set
    rw [show (n_B - 2).descFactorial (k - 2)
          = Fintype.card (↥A_set ↪ ↥(((Finset.univ.erase b_1).erase b_2 :
                                       Finset (Fin n_B)))) by
      rw [Fintype.card_embedding_eq]
      have hA_card : Fintype.card ↥A_set = k - 2 := by rw [Fintype.card_coe, h_A_card]
      have hB_card : Fintype.card ↥(((Finset.univ.erase b_1).erase b_2 :
          Finset (Fin n_B))) = n_B - 2 := by
        rw [Fintype.card_coe]
        have h_b2_in : b_2 ∈ (Finset.univ.erase b_1 : Finset (Fin n_B)) := by
          rw [Finset.mem_erase]
          exact ⟨h_b_distinct.symm, Finset.mem_univ _⟩
        rw [Finset.card_erase_of_mem h_b2_in,
            Finset.card_erase_of_mem (Finset.mem_univ b_1),
            Finset.card_univ, Fintype.card_fin]
        omega
      rw [hA_card, hB_card]]
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- toFun: N ↦ embedding via candidatePairPairing.
      intro N
      have h_N_mem := N.property
      have h_N_cand : N.val ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2 :=
        (Finset.mem_filter.mp h_N_mem).1
      have h_N_image : N.val.image Prod.fst = A_set :=
        (Finset.mem_filter.mp h_N_mem).2
      refine
        { toFun := fun x => ⟨candidatePairPairing k a_1 a_2 b_1 b_2 N.val h_N_cand ⟨x.val, ?_⟩, ?_⟩,
          inj' := ?_ }
      · rw [h_N_image]; exact x.property
      · exact candidatePairPairing_mem_erase k a_1 a_2 b_1 b_2 N.val h_N_cand _
      · intro x y h_eq
        have h_inj := candidatePairPairing_injective k a_1 a_2 b_1 b_2 N.val h_N_cand
        have h_pair_eq : candidatePairPairing k a_1 a_2 b_1 b_2 N.val h_N_cand
            ⟨x.val, by rw [h_N_image]; exact x.property⟩
          = candidatePairPairing k a_1 a_2 b_1 b_2 N.val h_N_cand
            ⟨y.val, by rw [h_N_image]; exact y.property⟩ :=
          congrArg Subtype.val h_eq
        have h_sub_eq :
            ((⟨x.val, by rw [h_N_image]; exact x.property⟩ : ↥(N.val.image Prod.fst)))
              = ⟨y.val, by rw [h_N_image]; exact y.property⟩ := h_inj h_pair_eq
        have h_val_eq : x.val = y.val := by
          have := congrArg Subtype.val h_sub_eq
          exact this
        exact Subtype.ext h_val_eq
    · -- invFun: f ↦ embToPairFiber f.
      intro f
      refine ⟨embToPairFiber b_1 b_2 A_set f, ?_⟩
      refine Finset.mem_filter.mpr
        ⟨embToPairFiber_mem_candidatePairPartnerSet k h_k_ge_2 a_1 a_2 b_1 b_2 A_set
            h_A_sub h_A_card f,
         embToPairFiber_image_fst b_1 b_2 A_set f⟩
    · -- left_inv: for each N, invFun (toFun N) = N.
      intro N
      apply Subtype.ext
      have h_N_mem := N.property
      have h_N_cand : N.val ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2 :=
        (Finset.mem_filter.mp h_N_mem).1
      have h_N_image : N.val.image Prod.fst = A_set :=
        (Finset.mem_filter.mp h_N_mem).2
      have h_N_card_eq : N.val.card = k - 2 :=
        (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 _).mp h_N_cand |>.2.1
      let toF : ↥A_set ↪ ↥((Finset.univ.erase b_1).erase b_2 : Finset (Fin n_B)) :=
        { toFun := fun x => ⟨candidatePairPairing k a_1 a_2 b_1 b_2 N.val h_N_cand ⟨x.val, by
              rw [h_N_image]; exact x.property⟩,
            candidatePairPairing_mem_erase k a_1 a_2 b_1 b_2 N.val h_N_cand _⟩,
          inj' := by
            intro x y h_eq
            have h_inj := candidatePairPairing_injective k a_1 a_2 b_1 b_2 N.val h_N_cand
            have h_pair_eq : candidatePairPairing k a_1 a_2 b_1 b_2 N.val h_N_cand
                ⟨x.val, by rw [h_N_image]; exact x.property⟩
              = candidatePairPairing k a_1 a_2 b_1 b_2 N.val h_N_cand
                ⟨y.val, by rw [h_N_image]; exact y.property⟩ :=
              congrArg Subtype.val h_eq
            have h_sub_eq :
                ((⟨x.val, by rw [h_N_image]; exact x.property⟩ : ↥(N.val.image Prod.fst)))
                  = ⟨y.val, by rw [h_N_image]; exact y.property⟩ := h_inj h_pair_eq
            have h_val_eq : x.val = y.val := by
              have := congrArg Subtype.val h_sub_eq
              exact this
            exact Subtype.ext h_val_eq }
      change embToPairFiber b_1 b_2 A_set toF = N.val
      have h_sub : embToPairFiber b_1 b_2 A_set toF ⊆ N.val := by
        intro ab h_ab
        rw [mem_embToPairFiber] at h_ab
        obtain ⟨h_in_A, h_eq⟩ := h_ab
        have h_pair := candidatePairPairing_spec k a_1 a_2 b_1 b_2 N.val h_N_cand
          ⟨ab.1, by rw [h_N_image]; exact h_in_A⟩
        have h_b_eq : ab.2 = candidatePairPairing k a_1 a_2 b_1 b_2 N.val h_N_cand
            ⟨ab.1, by rw [h_N_image]; exact h_in_A⟩ := h_eq
        have h_ab_eq : ab = (ab.1, candidatePairPairing k a_1 a_2 b_1 b_2 N.val h_N_cand
            ⟨ab.1, by rw [h_N_image]; exact h_in_A⟩) :=
          Prod.ext rfl h_b_eq
        rw [h_ab_eq]; exact h_pair
      have h_card_eq :
          (embToPairFiber b_1 b_2 A_set toF).card = N.val.card := by
        unfold embToPairFiber
        rw [Finset.card_image_of_injective, Finset.card_attach, h_A_card, h_N_card_eq]
        intro x y h_eq
        exact Subtype.ext ((Prod.mk.injEq _ _ _ _).mp h_eq |>.1)
      exact Finset.eq_of_subset_of_card_le h_sub h_card_eq.ge
    · -- right_inv: for each f, fiberToEmb (embToPairFiber f) = f.
      intro f
      apply DFunLike.ext
      intro x
      apply Subtype.ext
      set N := embToPairFiber b_1 b_2 A_set f
      have h_N_in_filter : N ∈ (candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).filter
          (fun N' => N'.image Prod.fst = A_set) :=
        Finset.mem_filter.mpr
          ⟨embToPairFiber_mem_candidatePairPartnerSet k h_k_ge_2 a_1 a_2 b_1 b_2 A_set
              h_A_sub h_A_card f,
           embToPairFiber_image_fst b_1 b_2 A_set f⟩
      have h_N_cand : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2 :=
        (Finset.mem_filter.mp h_N_in_filter).1
      have h_N_image : N.image Prod.fst = A_set := (Finset.mem_filter.mp h_N_in_filter).2
      have h_pair := candidatePairPairing_spec k a_1 a_2 b_1 b_2 N h_N_cand
        ⟨x.val, by rw [h_N_image]; exact x.property⟩
      have h_target : (x.val, (f x).val) ∈ N := by
        rw [show N = embToPairFiber b_1 b_2 A_set f from rfl, mem_embToPairFiber]
        exact ⟨x.property, rfl⟩
      have h_cand_prop : CandidatePairPartner a_1 a_2 b_1 b_2 N :=
        (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp h_N_cand |>.2.2
      have h_uniq : (x.val, candidatePairPairing k a_1 a_2 b_1 b_2 N h_N_cand
          ⟨x.val, by rw [h_N_image]; exact x.property⟩) = (x.val, (f x).val) := by
        by_contra h_ne
        have h_A_clash : (x.val, candidatePairPairing k a_1 a_2 b_1 b_2 N h_N_cand
            ⟨x.val, by rw [h_N_image]; exact x.property⟩).1 ≠ (x.val, (f x).val).1 :=
          h_cand_prop.2.2.2.2.1 _ h_pair _ h_target h_ne
        exact h_A_clash rfl
      exact ((Prod.mk.injEq _ _ _ _).mp h_uniq).2
  rw [Finset.sum_congr rfl h_each_fiber]
  rw [Finset.sum_const]
  rw [Finset.card_powersetCard]
  -- (univ.erase a_1).erase a_2 has card n_A - 2.
  have h_outer_card :
      ((Finset.univ.erase a_1).erase a_2 : Finset (Fin n_A)).card = n_A - 2 := by
    have h_a2_in : a_2 ∈ (Finset.univ.erase a_1 : Finset (Fin n_A)) := by
      rw [Finset.mem_erase]
      exact ⟨h_a_distinct.symm, Finset.mem_univ _⟩
    rw [Finset.card_erase_of_mem h_a2_in,
        Finset.card_erase_of_mem (Finset.mem_univ a_1),
        Finset.card_univ, Fintype.card_fin]
    omega
  rw [h_outer_card]
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  ring

/-! ## PS.4.c.7: headline integral identity for codegree (Step E) -/

open DaveyThesis2024.BipartiteRandomGraph in
open MeasureTheory in
/-- **Headline integral identity (codegree, Step E).**

For a random bipartite graph `G ~ G(n_A, n_B, p)` and two fixed edge slots
`e_1 = (a_1, b_1)`, `e_2 = (a_2, b_2)` with distinct A-coords, distinct B-coords,
and "no bridges" indicator `(g (a_1, b_2)) = false ∧ g (a_2, b_1) = false`:

  `E[|{ M ∈ F_k(G) : e_1, e_2 ∈ M }| · 1[e_1 ∈ E(G)] · 1[e_2 ∈ E(G)]
        · 1[(a_1, b_2) ∉ E(G)] · 1[(a_2, b_1) ∉ E(G)]]
    = |candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2| · p^k · (1 - p)^(k(k - 1))
    = C(n_A - 2, k - 2) · C(n_B - 2, k - 2) · (k - 2)! · p^k · (1 - p)^(k(k - 1))`.

Strategy: composition of Steps B (`count_pair_mul_indicator_eq_sum_matchingPairIndicator`),
C-final (`integral_matchingPairIndicator_eq`), and D (`candidatePairPartnerSet_card`). -/
theorem expectation_inducedKMatchings_with_edge_pair
    {n_A n_B : ℕ}
    (k : ℕ) (h_k_ge_2 : 2 ≤ k) (h_k_le_A : k ≤ n_A) (h_k_le_B : k ≤ n_B)
    (p : ENNReal) (hp_le : p ≤ 1)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_a_distinct : a_1 ≠ a_2) (h_b_distinct : b_1 ≠ b_2) :
    ∫ g, (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
        (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
        Finset.univ Finset.univ k).filter
          (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card : ℝ) *
        (if g (a_1, b_1) = true then (1 : ℝ) else 0) *
        (if g (a_2, b_2) = true then (1 : ℝ) else 0) *
        (if g (a_1, b_2) = true then (0 : ℝ) else 1) *
        (if g (a_2, b_1) = true then (0 : ℝ) else 1)
      ∂((bipartiteEdgeChoice n_A n_B p hp_le).toMeasure)
    = p.toReal ^ k * (1 - p.toReal) ^ (k * (k - 1))
        * ((Nat.choose (n_A - 2) (k - 2) : ℝ)
            * (Nat.choose (n_B - 2) (k - 2) : ℝ)
            * (Nat.factorial (k - 2) : ℝ)) := by
  classical
  set μ := (bipartiteEdgeChoice n_A n_B p hp_le).toMeasure with hμ_def
  -- Step B: pointwise rewriting.
  have h_pointwise : ∀ g,
      (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
          (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
          Finset.univ Finset.univ k).filter
            (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card : ℝ) *
          (if g (a_1, b_1) = true then (1 : ℝ) else 0) *
          (if g (a_2, b_2) = true then (1 : ℝ) else 0) *
          (if g (a_1, b_2) = true then (0 : ℝ) else 1) *
          (if g (a_2, b_1) = true then (0 : ℝ) else 1)
        = ∑ N ∈ (((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a_1, b_1)).erase
                  (a_2, b_2)).powersetCard (k - 2),
            matchingPairIndicator a_1 a_2 b_1 b_2 N g := by
    intro g
    exact count_pair_mul_indicator_eq_sum_matchingPairIndicator k h_k_ge_2 a_1 a_2 b_1 b_2
      h_a_distinct h_b_distinct g
  have h_int_pointwise :
      ∫ g, (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
          (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
          Finset.univ Finset.univ k).filter
            (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card : ℝ) *
          (if g (a_1, b_1) = true then (1 : ℝ) else 0) *
          (if g (a_2, b_2) = true then (1 : ℝ) else 0) *
          (if g (a_1, b_2) = true then (0 : ℝ) else 1) *
          (if g (a_2, b_1) = true then (0 : ℝ) else 1)
        ∂μ
      = ∫ g, (∑ N ∈ (((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a_1, b_1)).erase
                  (a_2, b_2)).powersetCard (k - 2),
              matchingPairIndicator a_1 a_2 b_1 b_2 N g) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with g using h_pointwise g
  rw [h_int_pointwise]
  -- Pull integral inside finite sum.
  have h_integrable : ∀ N ∈ (((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a_1, b_1)).erase
                  (a_2, b_2)).powersetCard (k - 2),
      MeasureTheory.Integrable (fun g => matchingPairIndicator a_1 a_2 b_1 b_2 N g) μ := by
    intro N _
    refine (MeasureTheory.integrable_const (1 : ℝ)).mono'
      (by exact Measurable.of_discrete.aestronglyMeasurable) ?_
    filter_upwards with g
    rcases matchingPairIndicator_eq_zero_or_one a_1 a_2 b_1 b_2 N g with h | h
    · rw [h]; simp
    · rw [h]; simp
  rw [MeasureTheory.integral_finset_sum _ h_integrable]
  -- For N ∈ candidatePairPartnerSet: integral = p^k * (1-p)^(k(k-1)).
  -- For N ∉ candidatePairPartnerSet: integral = 0.
  have h_each_integral :
      ∀ N ∈ (((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a_1, b_1)).erase
                  (a_2, b_2)).powersetCard (k - 2),
        ∫ g, matchingPairIndicator a_1 a_2 b_1 b_2 N g ∂μ
          = if N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2 then
              p.toReal ^ k * (1 - p.toReal) ^ (k * (k - 1))
            else 0 := by
    intro N hN
    by_cases h_cand : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2
    · rw [if_pos h_cand]
      exact integral_matchingPairIndicator_eq k h_k_ge_2 a_1 a_2 b_1 b_2
        h_a_distinct h_b_distinct N h_cand p hp_le
    · rw [if_neg h_cand]
      have h_zero : (fun g => matchingPairIndicator a_1 a_2 b_1 b_2 N g) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
        filter_upwards with g
        exact matchingPairIndicator_eq_zero_of_not_candidate k h_k_ge_2 a_1 a_2 b_1 b_2 N hN h_cand g
      rw [MeasureTheory.integral_congr_ae h_zero, MeasureTheory.integral_zero]
  rw [Finset.sum_congr rfl h_each_integral]
  rw [← Finset.sum_filter]
  have h_filter_eq :
      ((((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a_1, b_1)).erase (a_2, b_2)).powersetCard
          (k - 2)).filter
        (fun N => N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2)
      = candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2 := by
    ext N
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, h_in⟩
      exact h_in
    · intro h_in
      refine ⟨?_, h_in⟩
      rw [mem_candidatePairPartnerSet_iff] at h_in
      rw [Finset.mem_powersetCard]
      exact ⟨h_in.1, h_in.2.1⟩
  rw [h_filter_eq]
  rw [Finset.sum_const]
  rw [candidatePairPartnerSet_card k h_k_ge_2 h_k_le_A h_k_le_B a_1 a_2 b_1 b_2
      h_a_distinct h_b_distinct]
  ring

/-! ## PS.5: D-concentration and codegree upper bound

Combining the PS.4.b expectation identity with the Kim-Vu polynomial concentration
axiom (PS.2) yields an a.a.s. concentration bound for `D(e) := |{M : F_k | e ∈ M}|·1[e ∈ E(G)]`
around its mean `μ = p · expectedDegreeFormula`. Combining the PS.4.c codegree
expectation with Markov yields a uniform a.a.s. upper bound on the codegree
`C(e_1, e_2)` over all pairs `e_1 ≠ e_2`. These two ingredients are exactly the
hypotheses of `pippenger_spencer_covering` (PS.1), to be verified in PS.6.

PS.5 is a *direct invocation* of the Kim-Vu axiom: we set `f g := (count) · 1[g(a,b)]`
(the LHS of `expectation_inducedKMatchings_with_edge`), `μ := p · expectedDegreeFormula`,
and pick `deg := k * (k - 1) + k` (the polynomial degree in the n_A · n_B edge
indicators, upper-bounded by `k²`). The `E_max` parameter is bounded by the per-pair
codegree expectation `expectedCodegreeFormula × (1-p)^{-4}` (from PS.4.c), which is the
"max partial-derivative norm" in Kim-Vu's notation. -/

/-! ### PS.5 Step 1: D-concentration via Kim-Vu -/

/-- The polynomial degree of `D(e) := (count of matchings through e) · 1[e ∈ E(G)]`
as a multilinear function of the `n_A · n_B` cross-edge indicators.

The factor `(count of matchings through e)` involves `k - 1` matching edges present
plus `k(k-1)` cross-edges absent (the induced-matching constraint), total degree
`k - 1 + k(k - 1) = k² - 1`. Multiplying by `1[e ∈ E(G)]` adds one more degree of
dependence. We pick the bound `k * (k - 1) + k = k²` for simplicity. -/
noncomputable def dPolyDegree (k : ℕ) : ℕ := k * (k - 1) + k

lemma dPolyDegree_pos (k : ℕ) (h_k_pos : 0 < k) : 0 < dPolyDegree k := by
  unfold dPolyDegree
  omega

section KimVuIntegration
open DaveyThesis2024.SecRandomBipartite.KimVu

/-- **Canonical verbatim Kim–Vu tail constant.** The `Classical.choose` of the verbatim Kim–Vu
axiom at uniformity `k`. Both `c'_allEdges_concentration_aas` and `c''_allPairs_concentration_aas`
return THIS constant (via `.choose`), so it is the single `n`-independent constant that bounds
both Kim–Vu tails — the Bonferroni budget of `secRandomBipartite_aas_BQ`. -/
noncomputable def kimVuVerbatimConst (k : ℕ) (h_k_pos : 0 < k) : ℝ :=
  (kim_vu_concentration_verbatim k h_k_pos).choose

lemma kimVuVerbatimConst_pos (k : ℕ) (h_k_pos : 0 < k) : 0 < kimVuVerbatimConst k h_k_pos :=
  (kim_vu_concentration_verbatim k h_k_pos).choose_spec.1

/-- The matching indicator equals the `monoH` monomial over its present/absent slots
(`presentSlots = insert (a,b) N`, `absentSlots` the bridge slots). Bridges the per-matching
monomial to the Kim–Vu discrete-derivative calculus in `KimVuEffects`. -/
lemma matchingIndicator_eq_monoH_prod {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) (h_ab : (a, b) ∉ N) :
    (fun g => matchingIndicator a b N g)
      = fun g => ∏ i, monoH (presentSlots a b N) (absentSlots a b N) i (g i) := by
  funext g
  rw [matchingIndicator_eq_product_form a b N h_cand h_ab,
      prod_monoH (presentSlots a b N) (absentSlots a b N)
        (presentSlots_disjoint_absentSlots a b N h_cand) g]
  have h1 : (∏ ab ∈ presentSlots a b N,
        DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g)
      = ∏ i ∈ presentSlots a b N, (if g i = true then (1 : ℝ) else 0) :=
    Finset.prod_congr rfl fun ab _ => (if_eq_edgeIndicator ab g).symm
  have h2 : (∏ ab ∈ absentSlots a b N,
        (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g))
      = ∏ i ∈ absentSlots a b N, (1 - if g i = true then (1 : ℝ) else 0) :=
    Finset.prod_congr rfl fun ab _ => by rw [← if_eq_edgeIndicator ab g]
  rw [h1, h2]

/-- **L4: integral of the discrete derivative of a single matching indicator.**
`∫ ∂_A matchingIndicator = (constant) · ∏_{i∉A} (per-slot expectation)`, where the constant
is `(−1)^{|A∩absentSlots|}` if `A ⊆ present∪absent`, else `0`. Combines the monomial
derivative (`discreteDeriv_monomial`) with the independence integral (`integral_prod_monoH`). -/
lemma integral_discreteDeriv_matchingIndicator {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) (h_ab : (a, b) ∉ N)
    (A : Finset (Fin n_A × Fin n_B)) (p : ENNReal) (hp : p ≤ 1) :
    ∫ g, discreteDeriv (matchingIndicator a b N) A g
        ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      = (if A ⊆ presentSlots a b N ∪ absentSlots a b N then
            (-1 : ℝ) ^ (A ∩ absentSlots a b N).card else 0)
          * ∏ i ∈ Aᶜ, (if i ∈ presentSlots a b N then p.toReal
              else if i ∈ absentSlots a b N then (1 - p.toReal) else 1) := by
  rw [show matchingIndicator a b N
        = (fun g => ∏ i, monoH (presentSlots a b N) (absentSlots a b N) i (g i)) from
      matchingIndicator_eq_monoH_prod a b N h_cand h_ab]
  simp_rw [discreteDeriv_monomial (presentSlots a b N) (absentSlots a b N)
      (presentSlots_disjoint_absentSlots a b N h_cand) A]
  rw [MeasureTheory.integral_const_mul,
      integral_prod_monoH (presentSlots a b N) (absentSlots a b N) Aᶜ p hp]

/-- **The H_k-degree polynomial of a present edge `e=(a,b)`**, treating `e` as present:
`c'(g) = ∑_N ∏_i monoH N (absentSlots) i (g i)` (present set `N`, NO `(a,b)` factor). It is a
polynomial in the slots other than `(a,b)` — structurally `g(a,b)`-independent — so it has no
dominant `μ/p` effect. For present `e`, the H_k-degree equals `c'`; `count = c'·1[g(a,b)]`. -/
noncomputable def matchingCountNoFactor {n_A n_B : ℕ} (a : Fin n_A) (b : Fin n_B) (k : ℕ)
    (g : Fin n_A × Fin n_B → Bool) : ℝ :=
  ∑ N ∈ candidatePartnerSet n_A n_B k a b, ∏ i, monoH N (absentSlots a b N) i (g i)

/-- Helper: the per-candidate product of slot expectations (with present set `N`,
absent set `absentSlots a b N`) evaluates to `p^{|N|} · (1-p)^{|absentSlots|}`.
The slots in `N` contribute `p`, those in `absentSlots` contribute `1-p`, all others
contribute `1`; `N` and `absentSlots` are disjoint. -/
private lemma prod_slot_expectation_eval {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePartner a b N) (q : ℝ) :
    (∏ i ∈ (Finset.univ : Finset (Fin n_A × Fin n_B)),
        (if i ∈ N then q else if i ∈ absentSlots a b N then (1 - q) else 1))
      = q ^ N.card * (1 - q) ^ (absentSlots a b N).card := by
  classical
  -- `N` and `absentSlots` are disjoint (from `presentSlots = insert (a,b) N ⊇ N`).
  have h_disj_pres : Disjoint (presentSlots a b N) (absentSlots a b N) :=
    presentSlots_disjoint_absentSlots a b N h_cand
  have h_N_sub_pres : N ⊆ presentSlots a b N := by
    unfold presentSlots; exact Finset.subset_insert _ _
  have h_disj : Disjoint N (absentSlots a b N) :=
    Finset.disjoint_of_subset_left h_N_sub_pres h_disj_pres
  -- Split `univ` into `N ∪ absentSlots ∪ rest`.
  set T := absentSlots a b N with hT
  -- Product over `N ∪ T` and over the complement.
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ N ∪ T)]
  -- The "not in N ∪ T" part is `1`.
  have h_rest : (∏ i ∈ Finset.univ.filter (fun i => ¬ i ∈ N ∪ T),
      (if i ∈ N then q else if i ∈ T then (1 - q) else 1)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [Finset.mem_filter, Finset.mem_union] at hi
    push_neg at hi
    rw [if_neg hi.2.1, if_neg hi.2.2]
  rw [h_rest, mul_one]
  -- The "in N ∪ T" part: split as union of disjoint `N` and `T`.
  have h_filter_eq : Finset.univ.filter (fun i => i ∈ N ∪ T) = N ∪ T := by
    ext i; simp
  rw [h_filter_eq, Finset.prod_union h_disj]
  -- Product over `N`: each factor is `q`.
  have h_prodN : (∏ i ∈ N, (if i ∈ N then q else if i ∈ T then (1 - q) else 1))
      = q ^ N.card := by
    rw [Finset.prod_congr rfl (fun i hi => by rw [if_pos hi]), Finset.prod_const]
  -- Product over `T`: each factor is `1-q` (using disjointness so `i ∉ N`).
  have h_prodT : (∏ i ∈ T, (if i ∈ N then q else if i ∈ T then (1 - q) else 1))
      = (1 - q) ^ T.card := by
    refine (Finset.prod_congr rfl (fun i hi => ?_)).trans (Finset.prod_const _)
    have h_notN : i ∉ N := fun h => (Finset.disjoint_left.mp h_disj h) hi
    rw [if_neg h_notN, if_pos hi]
  rw [h_prodN, h_prodT, hT]

/-- **P2 mean (L5): `E[c'] = expectedDegreeFormula = μ_c`.** -/
lemma matchingCountNoFactor_integral {n_A n_B : ℕ} (a : Fin n_A) (b : Fin n_B) (k : ℕ)
    (h_k_pos : 0 < k) (h_k_le_A : k ≤ n_A) (h_k_le_B : k ≤ n_B)
    (p : ENNReal) (hp : p ≤ 1) :
    ∫ g, matchingCountNoFactor a b k g
        ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      = expectedDegreeFormula n_A n_B k p.toReal := by
  classical
  set μ := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure
    with hμ_def
  -- Unfold and push the integral inside the finite sum over `candidatePartnerSet`.
  unfold matchingCountNoFactor
  have h_integrable : ∀ N ∈ candidatePartnerSet n_A n_B k a b,
      MeasureTheory.Integrable
        (fun g => ∏ i, monoH N (absentSlots a b N) i (g i)) μ := by
    intro N _
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ f : Fin n_A × Fin n_B → Bool,
        ‖∏ i, monoH N (absentSlots a b N) i (f i)‖ ≤ C := by
      rcases Finset.exists_le
        (Finset.univ.image
          (fun f : Fin n_A × Fin n_B → Bool => ‖∏ i, monoH N (absentSlots a b N) i (f i)‖))
        with ⟨C, hC⟩
      exact ⟨C, fun f => hC _ (Finset.mem_image.2 ⟨f, Finset.mem_univ f, rfl⟩)⟩
    haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
    exact (MeasureTheory.memLp_top_of_bound Measurable.of_discrete.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)).integrable le_top
  rw [MeasureTheory.integral_finset_sum _ h_integrable]
  -- Each summand: the product-integral, then product evaluation, then constant value.
  have h_each : ∀ N ∈ candidatePartnerSet n_A n_B k a b,
      ∫ g, (∏ i, monoH N (absentSlots a b N) i (g i)) ∂μ
        = p.toReal ^ (k - 1) * (1 - p.toReal) ^ (k * (k - 1)) := by
    intro N hN
    have h_cand : CandidatePartner a b N :=
      (mem_candidatePartnerSet_iff k a b N |>.mp hN).2.2
    have h_N_card : N.card = k - 1 := (mem_candidatePartnerSet_iff k a b N |>.mp hN).2.1
    have h_abs_card : (absentSlots a b N).card = k * (k - 1) :=
      absentSlots_card_of_candidate k h_k_pos a b N hN
    -- `∏ i, F i = ∏ i ∈ univ, F i`, so `integral_prod_monoH` applies directly.
    rw [hμ_def, integral_prod_monoH N (absentSlots a b N) Finset.univ p hp]
    rw [prod_slot_expectation_eval a b N h_cand p.toReal, h_N_card, h_abs_card]
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, nsmul_eq_mul]
  rw [candidatePartnerSet_card k h_k_pos h_k_le_A h_k_le_B a b]
  unfold expectedDegreeFormula
  push_cast
  ring

/-- **P2 effect (foundational): the absolute-effect upper bound.**
`E[|∂_A c'|] ≤ ∑_{N : A ⊆ N∪absentSlots} ∏_{i∉A} (per-slot expectation)` — by linearity of
`∂_A` over the `N`-sum, the triangle inequality `E[|∑|] ≤ ∑ E[|·|]`, and the per-monomial
integral (`|±1|=1`, the `{0,1}` residual monomial integrates to `∏ (per-slot)`). This is the
clean, unconditional engine; the `E := μ_c` and `E' := codegree` bounds follow by counting. -/
lemma matchingCountNoFactor_effect_le_sum {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (k : ℕ) (_h_k_pos : 0 < k)
    (A : Finset (Fin n_A × Fin n_B)) (p : ENNReal) (hp : p ≤ 1) :
    ∫ g, |discreteDeriv (matchingCountNoFactor a b k) A g|
        ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      ≤ ∑ N ∈ candidatePartnerSet n_A n_B k a b,
          (if A ⊆ N ∪ absentSlots a b N then
              ∏ i ∈ Aᶜ, (if i ∈ N then p.toReal
                  else if i ∈ absentSlots a b N then (1 - p.toReal) else 1)
            else 0) := by
  classical
  set μ := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure
    with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  -- Abbreviation for the per-`N` monomial.
  set F : Finset (Fin n_A × Fin n_B) → (Fin n_A × Fin n_B → Bool) → ℝ :=
    fun N g => ∏ i, monoH N (absentSlots a b N) i (g i) with hF_def
  set cand := candidatePartnerSet n_A n_B k a b with hcand_def
  -- Step 1: linearity of `discreteDeriv` over the `N`-sum.
  have h_deriv_sum : ∀ g, discreteDeriv (matchingCountNoFactor a b k) A g
      = ∑ N ∈ cand, discreteDeriv (F N) A g := by
    intro g
    have : matchingCountNoFactor a b k = (fun g => ∑ N ∈ cand, F N g) := by
      funext g; rfl
    rw [this, discreteDeriv_finset_sum cand F A g]
  -- Per-`N` value of the derivative.
  have h_disj : ∀ N ∈ cand, Disjoint N (absentSlots a b N) := by
    intro N hN
    have h_cand : CandidatePartner a b N :=
      (mem_candidatePartnerSet_iff k a b N |>.mp hN).2.2
    exact Finset.disjoint_of_subset_left
      (by unfold presentSlots; exact Finset.subset_insert _ _)
      (presentSlots_disjoint_absentSlots a b N h_cand)
  -- Each monomial factor is in `[0,1]`, so the residual product is `≥ 0`.
  have h_monoH_nonneg : ∀ (N : Finset (Fin n_A × Fin n_B)) (i : Fin n_A × Fin n_B) (b' : Bool),
      0 ≤ monoH N (absentSlots a b N) i b' := by
    intro N i b'
    unfold monoH
    by_cases hS : i ∈ N
    · simp only [if_pos hS]; cases b' <;> simp
    · simp only [if_neg hS]
      by_cases hT : i ∈ absentSlots a b N
      · simp only [if_pos hT]; cases b' <;> simp
      · simp only [if_neg hT]; norm_num
  have h_prod_nonneg : ∀ (N : Finset (Fin n_A × Fin n_B)) (g : Fin n_A × Fin n_B → Bool),
      0 ≤ ∏ i ∈ Aᶜ, monoH N (absentSlots a b N) i (g i) := by
    intro N g
    exact Finset.prod_nonneg (fun i _ => h_monoH_nonneg N i (g i))
  -- |∂_A (F N)| = (if A ⊆ N∪absent then 1 else 0) * (∏ over Aᶜ).
  have h_abs_deriv : ∀ N ∈ cand, ∀ g,
      |discreteDeriv (F N) A g|
        = (if A ⊆ N ∪ absentSlots a b N then (1 : ℝ) else 0)
            * ∏ i ∈ Aᶜ, monoH N (absentSlots a b N) i (g i) := by
    intro N hN g
    rw [hF_def, discreteDeriv_monomial N (absentSlots a b N) (h_disj N hN) A g, abs_mul,
      abs_of_nonneg (h_prod_nonneg N g)]
    congr 1
    by_cases h : A ⊆ N ∪ absentSlots a b N
    · simp only [if_pos h]
      rw [abs_pow, abs_neg, abs_one, one_pow]
    · simp only [if_neg h, abs_zero]
  -- Integrability helper for any function on this finite space.
  have h_int : ∀ (φ : (Fin n_A × Fin n_B → Bool) → ℝ), MeasureTheory.Integrable φ μ := by
    intro φ
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ f : Fin n_A × Fin n_B → Bool, ‖φ f‖ ≤ C := by
      rcases Finset.exists_le
        (Finset.univ.image (fun f : Fin n_A × Fin n_B → Bool => ‖φ f‖)) with ⟨C, hC⟩
      exact ⟨C, fun f => hC _ (Finset.mem_image.2 ⟨f, Finset.mem_univ f, rfl⟩)⟩
    exact (MeasureTheory.memLp_top_of_bound Measurable.of_discrete.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)).integrable le_top
  -- Step 3: ∫ |∂_A c'| ≤ ∫ (∑ |∂_A F N|) = ∑ ∫ |∂_A F N|.
  calc ∫ g, |discreteDeriv (matchingCountNoFactor a b k) A g| ∂μ
      ≤ ∫ g, ∑ N ∈ cand, |discreteDeriv (F N) A g| ∂μ := by
        refine MeasureTheory.integral_mono (h_int _) (h_int _) ?_
        intro g
        simp only
        rw [h_deriv_sum g]
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ N ∈ cand, ∫ g, |discreteDeriv (F N) A g| ∂μ := by
        rw [MeasureTheory.integral_finset_sum _ (fun N _ => h_int _)]
    _ = ∑ N ∈ cand, (if A ⊆ N ∪ absentSlots a b N then
            ∏ i ∈ Aᶜ, (if i ∈ N then p.toReal
                else if i ∈ absentSlots a b N then (1 - p.toReal) else 1)
          else 0) := by
        refine Finset.sum_congr rfl ?_
        intro N hN
        rw [MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (h_abs_deriv N hN))]
        by_cases h : A ⊆ N ∪ absentSlots a b N
        · simp only [if_pos h, one_mul]
          rw [hμ_def, integral_prod_monoH N (absentSlots a b N) Aᶜ p hp]
        · simp only [if_neg h, zero_mul, MeasureTheory.integral_zero]

/-- **P2 effect (count reduction):** `E[|∂_A c'|] ≤ #{N ∈ cand : A ⊆ N∪absentSlots_N}`.
Each per-slot factor lies in `[0,1]`, so every residual product is `≤ 1`; the effect bound
collapses to a pure count of qualifying matchings. -/
lemma matchingCountNoFactor_effect_le_card {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (k : ℕ) (h_k_pos : 0 < k)
    (A : Finset (Fin n_A × Fin n_B)) (p : ENNReal) (hp : p ≤ 1) :
    ∫ g, |discreteDeriv (matchingCountNoFactor a b k) A g|
        ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      ≤ (((candidatePartnerSet n_A n_B k a b).filter
            (fun N => A ⊆ N ∪ absentSlots a b N)).card : ℝ) := by
  classical
  refine le_trans (matchingCountNoFactor_effect_le_sum a b k h_k_pos A p hp) ?_
  rw [← Finset.sum_boole]
  have hp_nonneg : (0 : ℝ) ≤ p.toReal := ENNReal.toReal_nonneg
  have hp_le_one : p.toReal ≤ 1 :=
    le_trans (ENNReal.toReal_mono (by simp) hp) (by simp)
  refine Finset.sum_le_sum ?_
  intro N hN
  by_cases h : A ⊆ N ∪ absentSlots a b N
  · simp only [if_pos h]
    refine Finset.prod_le_one ?_ ?_
    · intro i _
      split_ifs
      · exact hp_nonneg
      · linarith
      · norm_num
    · intro i _
      split_ifs
      · exact hp_le_one
      · linarith
      · exact le_rfl
  · simp only [if_neg h]; exact le_rfl

/-- **P2 effect (E := #cand):** the unconditional `E` bound — every effect is `≤ #cand`
(at most that many matchings qualify). For constant `k`, `#cand = O(μ_c)`, so this is a valid
and regime-usable `E`. -/
lemma matchingCountNoFactor_effect_le_cardCand {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (k : ℕ) (h_k_pos : 0 < k)
    (A : Finset (Fin n_A × Fin n_B)) (p : ENNReal) (hp : p ≤ 1) :
    ∫ g, |discreteDeriv (matchingCountNoFactor a b k) A g|
        ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      ≤ ((candidatePartnerSet n_A n_B k a b).card : ℝ) := by
  refine le_trans (matchingCountNoFactor_effect_le_card a b k h_k_pos A p hp) ?_
  exact_mod_cast Finset.card_filter_le _ _

/-- Relabel the B-coordinate of every edge of `N` by swapping columns `c ↔ c'`. -/
private noncomputable def relabelCol {n_A n_B : ℕ} (c c' : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) : Finset (Fin n_A × Fin n_B) :=
  N.image (fun x => (x.1, Equiv.swap c c' x.2))

private lemma mem_relabelCol {n_A n_B : ℕ} (c c' : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) (p : Fin n_A × Fin n_B) :
    p ∈ relabelCol c c' N ↔ ∃ x ∈ N, (x.1, Equiv.swap c c' x.2) = p := by
  unfold relabelCol; rw [Finset.mem_image]

/-- `relabelCol` is an involution. -/
private lemma relabelCol_involutive {n_A n_B : ℕ} (c c' : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) :
    relabelCol c c' (relabelCol c c' N) = N := by
  classical
  unfold relabelCol
  rw [Finset.image_image]
  have : (fun x : Fin n_A × Fin n_B => (x.1, Equiv.swap c c' x.2)) ∘
      (fun x : Fin n_A × Fin n_B => (x.1, Equiv.swap c c' x.2)) = id := by
    funext x
    simp [Function.comp, Equiv.swap_apply_self]
  rw [this, Finset.image_id]

/-- If `c, c' ≠ b`, then `relabelCol c c'` maps `candidatePartnerSet` into itself. -/
private lemma relabelCol_mem_candidatePartnerSet {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (c c' : Fin n_B) (hc : c ≠ b) (hc' : c' ≠ b)
    (N : Finset (Fin n_A × Fin n_B)) (hN : N ∈ candidatePartnerSet n_A n_B k a b) :
    relabelCol c c' N ∈ candidatePartnerSet n_A n_B k a b := by
  classical
  rw [mem_candidatePartnerSet_iff] at hN ⊢
  obtain ⟨h_sub, h_card, h_cand⟩ := hN
  -- The swap on second coords, as a map on pairs, is injective.
  have h_inj : Set.InjOn (fun x : Fin n_A × Fin n_B => (x.1, Equiv.swap c c' x.2)) N := by
    intro x _ y _ h_eq
    have h1 : x.1 = y.1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
    have h2 : Equiv.swap c c' x.2 = Equiv.swap c c' y.2 :=
      (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
    have h2' : x.2 = y.2 := (Equiv.swap c c').injective h2
    exact Prod.ext h1 h2'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- subset univ.erase (a,b)
    intro p hp
    rw [mem_relabelCol] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [← h_eq]
    intro h_contra
    -- p = (x.1, swap x.2); if p = (a,b) then x.1 = a (forbidden) ... actually use B-coord.
    have hx_b : x.2 ≠ b := h_cand.2.1 x hx
    have h_p2 : Equiv.swap c c' x.2 = b := (Prod.mk.injEq _ _ _ _).mp h_contra |>.2
    -- swap c c' x.2 = b ⇒ x.2 = b (since c,c' ≠ b, swap fixes b's preimage = b).
    have hswb : Equiv.swap c c' b = b :=
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hc) (Ne.symm hc')
    have : x.2 = b := by rw [Equiv.swap_apply_eq_iff, hswb] at h_p2; exact h_p2
    exact hx_b this
  · -- card
    rw [relabelCol, Finset.card_image_of_injOn h_inj, h_card]
  · -- A-coords ≠ a
    intro p hp
    rw [mem_relabelCol] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [← h_eq]
    exact h_cand.1 x hx
  · -- B-coords ≠ b
    intro p hp
    rw [mem_relabelCol] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [← h_eq]
    have hx_b : x.2 ≠ b := h_cand.2.1 x hx
    intro h_contra
    -- swap c c' x.2 = b ⇒ x.2 = b
    have hswb : Equiv.swap c c' b = b :=
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hc) (Ne.symm hc')
    have : x.2 = b := by rw [Equiv.swap_apply_eq_iff, hswb] at h_contra; exact h_contra
    exact hx_b this
  · -- distinct A-coords
    intro p hp q hq h_ne
    rw [mem_relabelCol] at hp hq
    obtain ⟨x, hx, h_eqx⟩ := hp
    obtain ⟨y, hy, h_eqy⟩ := hq
    rw [← h_eqx, ← h_eqy]
    have hxy : x ≠ y := by
      intro h; apply h_ne; rw [← h_eqx, ← h_eqy, h]
    exact h_cand.2.2.1 x hx y hy hxy
  · -- distinct B-coords (under swap, still distinct since swap injective)
    intro p hp q hq h_ne
    rw [mem_relabelCol] at hp hq
    obtain ⟨x, hx, h_eqx⟩ := hp
    obtain ⟨y, hy, h_eqy⟩ := hq
    rw [← h_eqx, ← h_eqy]
    simp only
    have hxy : x ≠ y := by
      intro h; apply h_ne; rw [← h_eqx, ← h_eqy, h]
    intro h_swap
    have : x.2 = y.2 := (Equiv.swap c c').injective h_swap
    exact h_cand.2.2.2 x hx y hy hxy this

/-- `relabelCol c c'` carries column `c` to column `c'`:
`c ∈ N.image snd ↔ c' ∈ (relabelCol c c' N).image snd`. -/
private lemma relabelCol_image_snd_iff {n_A n_B : ℕ} (c c' : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) :
    c' ∈ (relabelCol c c' N).image Prod.snd ↔ c ∈ N.image Prod.snd := by
  classical
  constructor
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨p, hp, hp2⟩ := h
    rw [mem_relabelCol] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [Finset.mem_image]
    refine ⟨x, hx, ?_⟩
    -- p.2 = swap c c' x.2 = c'  ⇒ x.2 = c
    have hsc : Equiv.swap c c' x.2 = c' := by rw [← h_eq] at hp2; exact hp2
    have h2 : x.2 = Equiv.swap c c' c' := Equiv.swap_apply_eq_iff.mp hsc
    rw [Equiv.swap_apply_right] at h2
    exact h2
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨x, hx, hx2⟩ := h
    rw [Finset.mem_image]
    refine ⟨(x.1, Equiv.swap c c' x.2), ?_, ?_⟩
    · rw [mem_relabelCol]; exact ⟨x, hx, rfl⟩
    · change Equiv.swap c c' x.2 = c'
      rw [hx2, Equiv.swap_apply_left]

/-- For two non-`b` columns `c, c'`, the number of candidate matchings using column `c`
equals the number using column `c'` (column-relabelling symmetry). -/
private lemma candidate_col_count_eq {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (c c' : Fin n_B) (hc : c ≠ b) (hc' : c' ≠ b) :
    ((candidatePartnerSet n_A n_B k a b).filter (fun N => c ∈ N.image Prod.snd)).card
      = ((candidatePartnerSet n_A n_B k a b).filter (fun N => c' ∈ N.image Prod.snd)).card := by
  classical
  apply Finset.card_nbij' (relabelCol c c') (relabelCol c c')
  · -- MapsTo forward
    intro N hN
    rw [Finset.mem_coe, Finset.mem_filter] at hN ⊢
    refine ⟨relabelCol_mem_candidatePartnerSet k a b c c' hc hc' N hN.1, ?_⟩
    rw [relabelCol_image_snd_iff]; exact hN.2
  · -- MapsTo backward
    intro N hN
    rw [Finset.mem_coe, Finset.mem_filter] at hN ⊢
    refine ⟨relabelCol_mem_candidatePartnerSet k a b c c' hc hc' N hN.1, ?_⟩
    -- need c ∈ (relabel N).image snd given c' ∈ N.image snd
    have h_symm : relabelCol c c' N = relabelCol c' c N := by
      unfold relabelCol; rw [Equiv.swap_comm]
    rw [h_symm, relabelCol_image_snd_iff c' c N]; exact hN.2
  · intro N _; exact relabelCol_involutive c c' N
  · intro N _; exact relabelCol_involutive c c' N

/-- Relabel the A-coordinate of every edge of `N` by swapping rows `r ↔ r'`. -/
private noncomputable def relabelRow {n_A n_B : ℕ} (r r' : Fin n_A)
    (N : Finset (Fin n_A × Fin n_B)) : Finset (Fin n_A × Fin n_B) :=
  N.image (fun x => (Equiv.swap r r' x.1, x.2))

private lemma mem_relabelRow {n_A n_B : ℕ} (r r' : Fin n_A)
    (N : Finset (Fin n_A × Fin n_B)) (p : Fin n_A × Fin n_B) :
    p ∈ relabelRow r r' N ↔ ∃ x ∈ N, (Equiv.swap r r' x.1, x.2) = p := by
  unfold relabelRow; rw [Finset.mem_image]

private lemma relabelRow_involutive {n_A n_B : ℕ} (r r' : Fin n_A)
    (N : Finset (Fin n_A × Fin n_B)) :
    relabelRow r r' (relabelRow r r' N) = N := by
  classical
  unfold relabelRow
  rw [Finset.image_image]
  have : (fun x : Fin n_A × Fin n_B => (Equiv.swap r r' x.1, x.2)) ∘
      (fun x : Fin n_A × Fin n_B => (Equiv.swap r r' x.1, x.2)) = id := by
    funext x
    simp [Function.comp, Equiv.swap_apply_self]
  rw [this, Finset.image_id]

private lemma relabelRow_mem_candidatePartnerSet {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (r r' : Fin n_A) (hr : r ≠ a) (hr' : r' ≠ a)
    (N : Finset (Fin n_A × Fin n_B)) (hN : N ∈ candidatePartnerSet n_A n_B k a b) :
    relabelRow r r' N ∈ candidatePartnerSet n_A n_B k a b := by
  classical
  rw [mem_candidatePartnerSet_iff] at hN ⊢
  obtain ⟨h_sub, h_card, h_cand⟩ := hN
  have h_inj : Set.InjOn (fun x : Fin n_A × Fin n_B => (Equiv.swap r r' x.1, x.2)) N := by
    intro x _ y _ h_eq
    have h1 : Equiv.swap r r' x.1 = Equiv.swap r r' y.1 :=
      (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
    have h1' : x.1 = y.1 := (Equiv.swap r r').injective h1
    have h2 : x.2 = y.2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
    exact Prod.ext h1' h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [mem_relabelRow] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [← h_eq]
    intro h_contra
    have hx_a : x.1 ≠ a := h_cand.1 x hx
    have h_p1 : Equiv.swap r r' x.1 = a := (Prod.mk.injEq _ _ _ _).mp h_contra |>.1
    have hswa : Equiv.swap r r' a = a :=
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hr) (Ne.symm hr')
    have : x.1 = a := by rw [Equiv.swap_apply_eq_iff, hswa] at h_p1; exact h_p1
    exact hx_a this
  · rw [relabelRow, Finset.card_image_of_injOn h_inj, h_card]
  · intro p hp
    rw [mem_relabelRow] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [← h_eq]
    have hx_a : x.1 ≠ a := h_cand.1 x hx
    intro h_contra
    have hswa : Equiv.swap r r' a = a :=
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hr) (Ne.symm hr')
    have : x.1 = a := by rw [Equiv.swap_apply_eq_iff, hswa] at h_contra; exact h_contra
    exact hx_a this
  · intro p hp
    rw [mem_relabelRow] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [← h_eq]
    exact h_cand.2.1 x hx
  · intro p hp q hq h_ne
    rw [mem_relabelRow] at hp hq
    obtain ⟨x, hx, h_eqx⟩ := hp
    obtain ⟨y, hy, h_eqy⟩ := hq
    rw [← h_eqx, ← h_eqy]
    simp only
    have hxy : x ≠ y := by
      intro h; apply h_ne; rw [← h_eqx, ← h_eqy, h]
    intro h_swap
    have : x.1 = y.1 := (Equiv.swap r r').injective h_swap
    exact h_cand.2.2.1 x hx y hy hxy this
  · intro p hp q hq h_ne
    rw [mem_relabelRow] at hp hq
    obtain ⟨x, hx, h_eqx⟩ := hp
    obtain ⟨y, hy, h_eqy⟩ := hq
    rw [← h_eqx, ← h_eqy]
    have hxy : x ≠ y := by
      intro h; apply h_ne; rw [← h_eqx, ← h_eqy, h]
    exact h_cand.2.2.2 x hx y hy hxy

private lemma relabelRow_image_fst_iff {n_A n_B : ℕ} (r r' : Fin n_A)
    (N : Finset (Fin n_A × Fin n_B)) :
    r' ∈ (relabelRow r r' N).image Prod.fst ↔ r ∈ N.image Prod.fst := by
  classical
  constructor
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨p, hp, hp1⟩ := h
    rw [mem_relabelRow] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [Finset.mem_image]
    refine ⟨x, hx, ?_⟩
    have hsr : Equiv.swap r r' x.1 = r' := by rw [← h_eq] at hp1; exact hp1
    have h1 : x.1 = Equiv.swap r r' r' := Equiv.swap_apply_eq_iff.mp hsr
    rw [Equiv.swap_apply_right] at h1
    exact h1
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨x, hx, hx1⟩ := h
    rw [Finset.mem_image]
    refine ⟨(Equiv.swap r r' x.1, x.2), ?_, ?_⟩
    · rw [mem_relabelRow]; exact ⟨x, hx, rfl⟩
    · change Equiv.swap r r' x.1 = r'
      rw [hx1, Equiv.swap_apply_left]

private lemma candidate_row_count_eq {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (r r' : Fin n_A) (hr : r ≠ a) (hr' : r' ≠ a) :
    ((candidatePartnerSet n_A n_B k a b).filter (fun N => r ∈ N.image Prod.fst)).card
      = ((candidatePartnerSet n_A n_B k a b).filter (fun N => r' ∈ N.image Prod.fst)).card := by
  classical
  apply Finset.card_nbij' (relabelRow r r') (relabelRow r r')
  · intro N hN
    rw [Finset.mem_coe, Finset.mem_filter] at hN ⊢
    refine ⟨relabelRow_mem_candidatePartnerSet k a b r r' hr hr' N hN.1, ?_⟩
    rw [relabelRow_image_fst_iff]; exact hN.2
  · intro N hN
    rw [Finset.mem_coe, Finset.mem_filter] at hN ⊢
    refine ⟨relabelRow_mem_candidatePartnerSet k a b r r' hr hr' N hN.1, ?_⟩
    have h_symm : relabelRow r r' N = relabelRow r' r N := by
      unfold relabelRow; rw [Equiv.swap_comm]
    rw [h_symm, relabelRow_image_fst_iff r' r N]; exact hN.2
  · intro N _; exact relabelRow_involutive r r' N
  · intro N _; exact relabelRow_involutive r r' N

/-- **Column double-count equality.** For `β ≠ b`,
`(n_B − 1) · #{N ∈ cand : β ∈ cols(N)} = (k − 1) · #cand`. -/
private lemma candidate_col_double_count {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (β : Fin n_B) (hβ : β ≠ b) :
    (n_B - 1) * ((candidatePartnerSet n_A n_B k a b).filter
        (fun N => β ∈ N.image Prod.snd)).card
      = (k - 1) * (candidatePartnerSet n_A n_B k a b).card := by
  classical
  set cand := candidatePartnerSet n_A n_B k a b with hcand
  set partnerCols := (Finset.univ.erase b : Finset (Fin n_B)) with hpc
  -- The double-counted incidence sum T = ∑_{N} #{c ∈ partnerCols : c ∈ N.image snd}.
  -- Row sum: each term = k-1.
  have h_rowsum : ∑ N ∈ cand, (partnerCols.filter (fun c => c ∈ N.image Prod.snd)).card
      = (k - 1) * cand.card := by
    rw [Finset.sum_congr rfl (fun N hN => ?_)]
    · rw [Finset.sum_const, smul_eq_mul, mul_comm]
    · -- N.image snd ⊆ partnerCols, so filtering partnerCols by membership = N.image snd.
      have h_sub : N.image Prod.snd ⊆ partnerCols := candidate_image_snd_subset k a b N hN
      have : partnerCols.filter (fun c => c ∈ N.image Prod.snd) = N.image Prod.snd :=
        (Finset.filter_mem_eq_inter).trans (Finset.inter_eq_right.mpr h_sub)
      rw [this, candidate_image_snd_card k a b N hN]
  -- Column sum: each term = #{N : β ∈ cols(N)} by symmetry.
  have h_colsum : ∑ c ∈ partnerCols, (cand.filter (fun N => c ∈ N.image Prod.snd)).card
      = (n_B - 1) * (cand.filter (fun N => β ∈ N.image Prod.snd)).card := by
    rw [Finset.sum_congr rfl (fun c hc => ?_)]
    · rw [Finset.sum_const, smul_eq_mul]
      congr 1
      rw [hpc, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    · have hc' : c ≠ b := (Finset.mem_erase.mp hc).1
      exact candidate_col_count_eq k a b c β hc' hβ
  -- Equate the two via sum_comm over the product.
  have h_comm : ∑ N ∈ cand, (partnerCols.filter (fun c => c ∈ N.image Prod.snd)).card
      = ∑ c ∈ partnerCols, (cand.filter (fun N => c ∈ N.image Prod.snd)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [← h_colsum, ← h_comm, h_rowsum]

/-- **Row double-count equality.** For `α ≠ a`,
`(n_A − 1) · #{N ∈ cand : α ∈ rows(N)} = (k − 1) · #cand`. -/
private lemma candidate_row_double_count {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) (α : Fin n_A) (hα : α ≠ a) :
    (n_A - 1) * ((candidatePartnerSet n_A n_B k a b).filter
        (fun N => α ∈ N.image Prod.fst)).card
      = (k - 1) * (candidatePartnerSet n_A n_B k a b).card := by
  classical
  set cand := candidatePartnerSet n_A n_B k a b with hcand
  set partnerRows := (Finset.univ.erase a : Finset (Fin n_A)) with hpr
  have h_rowsum : ∑ N ∈ cand, (partnerRows.filter (fun r => r ∈ N.image Prod.fst)).card
      = (k - 1) * cand.card := by
    rw [Finset.sum_congr rfl (fun N hN => ?_)]
    · rw [Finset.sum_const, smul_eq_mul, mul_comm]
    · have h_sub : N.image Prod.fst ⊆ partnerRows := candidate_image_fst_subset k a b N hN
      have : partnerRows.filter (fun r => r ∈ N.image Prod.fst) = N.image Prod.fst :=
        (Finset.filter_mem_eq_inter).trans (Finset.inter_eq_right.mpr h_sub)
      rw [this, candidate_image_fst_card k a b N hN]
  have h_colsum : ∑ r ∈ partnerRows, (cand.filter (fun N => r ∈ N.image Prod.fst)).card
      = (n_A - 1) * (cand.filter (fun N => α ∈ N.image Prod.fst)).card := by
    rw [Finset.sum_congr rfl (fun r hr => ?_)]
    · rw [Finset.sum_const, smul_eq_mul]
      congr 1
      rw [hpr, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    · have hr' : r ≠ a := (Finset.mem_erase.mp hr).1
      exact candidate_row_count_eq k a b r α hr' hα
  have h_comm : ∑ N ∈ cand, (partnerRows.filter (fun r => r ∈ N.image Prod.fst)).card
      = ∑ r ∈ partnerRows, (cand.filter (fun N => r ∈ N.image Prod.fst)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [← h_colsum, ← h_comm, h_rowsum]

/-- **P2 E' — per-slot support count (the codegree crux).** For a slot `s = (α,β) ≠ (a,b)`,
the number of candidate matchings whose support contains `s` is codegree-scale:
`min(n_A−1, n_B−1) · #{N : s ∈ N∪absentSlots_N} ≤ (k−1) · #cand`.
Proof idea: `s ∈ supp_N ⇒ β ∈ cols(N)` (when `β ≠ b`) or `α ∈ rows(N)` (when `β = b`) — checked
across `N`, aBridge, bBridge, withinN; then `#{N : β∈cols(N)} = #cand·(k−1)/(n_B−1)` (complementary
count: matchings avoiding column β live in an `(n_A−1)×(n_B−2)` grid), and `min ≤ n_B−1`. -/
lemma slot_supp_count_le {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (k : ℕ) (_h_k_ge_2 : 2 ≤ k)
    (_h_k_le_A : k ≤ n_A) (_h_k_le_B : k ≤ n_B)
    (s : Fin n_A × Fin n_B) (hs : s ≠ (a, b)) :
    (min (n_A - 1) (n_B - 1)) *
        ((candidatePartnerSet n_A n_B k a b).filter
          (fun N => s ∈ N ∪ absentSlots a b N)).card
      ≤ (k - 1) * (candidatePartnerSet n_A n_B k a b).card := by
  classical
  obtain ⟨α, β⟩ := s
  set cand := candidatePartnerSet n_A n_B k a b with hcand
  -- STAGE 1: membership ⇒ column (β≠b) or row (β=b) condition.
  -- The slot predicate.
  by_cases hβ : β = b
  · -- β = b ⇒ α ≠ a (since s ≠ (a,b)), and s ∈ supp_N ⇒ α ∈ rows(N).
    subst β
    have hα : α ≠ a := by
      intro h; exact hs (by rw [h])
    -- Filter monotonicity into the row filter.
    have h_subset : (cand.filter (fun N => (α, b) ∈ N ∪ absentSlots a b N))
        ⊆ (cand.filter (fun N => α ∈ N.image Prod.fst)) := by
      intro N hN
      rw [Finset.mem_filter] at hN ⊢
      obtain ⟨hN_cand, hN_mem⟩ := hN
      refine ⟨hN_cand, ?_⟩
      -- Analyse the four parts.
      rw [Finset.mem_union] at hN_mem
      rcases hN_mem with hIn | hAbs
      · -- (α,b) ∈ N: but candidates have B-coord ≠ b, contradiction.
        exfalso
        have h_cand : CandidatePartner a b N :=
          (mem_candidatePartnerSet_iff k a b N).mp hN_cand |>.2.2
        exact h_cand.2.1 (α, b) hIn rfl
      · unfold absentSlots at hAbs
        rw [Finset.mem_union, Finset.mem_union] at hAbs
        rcases hAbs with (hA | hB) | hW
        · -- aBridge: (a, x.2), forces fst = a; but our fst = α ≠ a. Contradiction.
          exfalso
          unfold aBridgeSlots at hA
          rw [Finset.mem_image] at hA
          obtain ⟨x, _, h_eq⟩ := hA
          exact hα ((Prod.mk.injEq _ _ _ _).mp h_eq |>.1).symm
        · -- bBridge: (x.1, b), x ∈ N ⇒ α = x.1 ∈ rows(N).
          unfold bBridgeSlots at hB
          rw [Finset.mem_image] at hB
          obtain ⟨x, hx, h_eq⟩ := hB
          rw [Finset.mem_image]
          exact ⟨x, hx, ((Prod.mk.injEq _ _ _ _).mp h_eq |>.1)⟩
        · -- withinN: (x.1, y.2) ⇒ α = x.1 ∈ rows(N).
          unfold withinNSlots at hW
          rw [Finset.mem_image] at hW
          obtain ⟨p, hp, h_eq⟩ := hW
          rw [Finset.mem_filter, Finset.mem_product] at hp
          rw [Finset.mem_image]
          exact ⟨p.1, hp.1.1, ((Prod.mk.injEq _ _ _ _).mp h_eq |>.1)⟩
    -- STAGE 2 (row branch).
    have h_card_le : (cand.filter (fun N => (α, b) ∈ N ∪ absentSlots a b N)).card
        ≤ (cand.filter (fun N => α ∈ N.image Prod.fst)).card := Finset.card_le_card h_subset
    calc (min (n_A - 1) (n_B - 1)) *
            (cand.filter (fun N => (α, b) ∈ N ∪ absentSlots a b N)).card
        ≤ (n_A - 1) * (cand.filter (fun N => α ∈ N.image Prod.fst)).card := by
          apply Nat.mul_le_mul (Nat.min_le_left _ _) h_card_le
      _ = (k - 1) * cand.card :=
          candidate_row_double_count k a b α hα
  · -- β ≠ b ⇒ s ∈ supp_N ⇒ β ∈ cols(N).
    have h_subset : (cand.filter (fun N => (α, β) ∈ N ∪ absentSlots a b N))
        ⊆ (cand.filter (fun N => β ∈ N.image Prod.snd)) := by
      intro N hN
      rw [Finset.mem_filter] at hN ⊢
      obtain ⟨hN_cand, hN_mem⟩ := hN
      refine ⟨hN_cand, ?_⟩
      rw [Finset.mem_union] at hN_mem
      rcases hN_mem with hIn | hAbs
      · -- (α,β) ∈ N ⇒ β ∈ cols(N).
        rw [Finset.mem_image]
        exact ⟨(α, β), hIn, rfl⟩
      · unfold absentSlots at hAbs
        rw [Finset.mem_union, Finset.mem_union] at hAbs
        rcases hAbs with (hA | hB) | hW
        · -- aBridge: (a, x.2), x ∈ N ⇒ β = x.2 ∈ cols(N).
          unfold aBridgeSlots at hA
          rw [Finset.mem_image] at hA
          obtain ⟨x, hx, h_eq⟩ := hA
          rw [Finset.mem_image]
          exact ⟨x, hx, ((Prod.mk.injEq _ _ _ _).mp h_eq |>.2)⟩
        · -- bBridge: (x.1, b), forces snd = b; but β ≠ b. Contradiction.
          exfalso
          unfold bBridgeSlots at hB
          rw [Finset.mem_image] at hB
          obtain ⟨x, _, h_eq⟩ := hB
          exact hβ ((Prod.mk.injEq _ _ _ _).mp h_eq |>.2).symm
        · -- withinN: (x.1, y.2) ⇒ β = y.2 ∈ cols(N).
          unfold withinNSlots at hW
          rw [Finset.mem_image] at hW
          obtain ⟨p, hp, h_eq⟩ := hW
          rw [Finset.mem_filter, Finset.mem_product] at hp
          rw [Finset.mem_image]
          exact ⟨p.2, hp.1.2, ((Prod.mk.injEq _ _ _ _).mp h_eq |>.2)⟩
    have h_card_le : (cand.filter (fun N => (α, β) ∈ N ∪ absentSlots a b N)).card
        ≤ (cand.filter (fun N => β ∈ N.image Prod.snd)).card := Finset.card_le_card h_subset
    calc (min (n_A - 1) (n_B - 1)) *
            (cand.filter (fun N => (α, β) ∈ N ∪ absentSlots a b N)).card
        ≤ (n_B - 1) * (cand.filter (fun N => β ∈ N.image Prod.snd)).card := by
          apply Nat.mul_le_mul (Nat.min_le_right _ _) h_card_le
      _ = (k - 1) * cand.card :=
          candidate_col_double_count k a b β hβ

/-- **P2 E' bound.** For nonempty `A`, the effect is codegree-scale:
`E[|∂_A c'|] ≤ (k−1)·#cand / min(n_A−1, n_B−1)`. (If `(a,b) ∈ A` the count is `0`, since
`(a,b) ∉ supp_N`; otherwise reduce to a single slot `s ∈ A`, `s ≠ (a,b)`, via `slot_supp_count_le`.)
This is the off-diagonal `E'`; for constant `k` it is `o(μ_c)`, enabling the regime inequality. -/
lemma matchingCountNoFactor_effect_le_E' {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (h_k_le_A : k ≤ n_A) (h_k_le_B : k ≤ n_B)
    (A : Finset (Fin n_A × Fin n_B)) (hA : A.Nonempty) (p : ENNReal) (hp : p ≤ 1) :
    ∫ g, |discreteDeriv (matchingCountNoFactor a b k) A g|
        ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      ≤ ((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ)
          / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ) := by
  classical
  have h_k_pos : 0 < k := by omega
  refine le_trans (matchingCountNoFactor_effect_le_card a b k h_k_pos A p hp) ?_
  have hmin_pos : 0 < min (n_A - 1) (n_B - 1) := by omega
  set cnt := ((candidatePartnerSet n_A n_B k a b).filter
      (fun N => A ⊆ N ∪ absentSlots a b N)).card with hcnt
  by_cases hab : (a, b) ∈ A
  · -- (a,b) ∈ A ⇒ no candidate N can satisfy A ⊆ N ∪ absentSlots a b N, so cnt = 0.
    have hcnt0 : cnt = 0 := by
      rw [hcnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro N hN h_sub
      have hN_cand : N ⊆ Finset.univ.erase (a, b) ∧ N.card = k - 1 ∧ CandidatePartner a b N :=
        (mem_candidatePartnerSet_iff k a b N).mp hN
      have h_mem : (a, b) ∈ N ∪ absentSlots a b N := h_sub hab
      rw [Finset.mem_union] at h_mem
      rcases h_mem with hIn | hAbs
      · exact (Finset.mem_erase.mp (hN_cand.1 hIn)).1 rfl
      · unfold absentSlots at hAbs
        rw [Finset.mem_union, Finset.mem_union] at hAbs
        have h_cand := hN_cand.2.2
        rcases hAbs with (hA | hB) | hW
        · unfold aBridgeSlots at hA
          rw [Finset.mem_image] at hA
          obtain ⟨x, hx, h_eq⟩ := hA
          exact h_cand.2.1 x hx ((Prod.mk.injEq _ _ _ _).mp h_eq).2
        · unfold bBridgeSlots at hB
          rw [Finset.mem_image] at hB
          obtain ⟨x, hx, h_eq⟩ := hB
          exact h_cand.1 x hx ((Prod.mk.injEq _ _ _ _).mp h_eq).1
        · unfold withinNSlots at hW
          rw [Finset.mem_image] at hW
          obtain ⟨q, hq, h_eq⟩ := hW
          rw [Finset.mem_filter, Finset.mem_product] at hq
          exact h_cand.1 q.1 hq.1.1 ((Prod.mk.injEq _ _ _ _).mp h_eq).1
    rw [hcnt0]
    have : (0:ℝ) ≤ ((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ)
        / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ) := by positivity
    simpa using this
  · obtain ⟨s, hsA⟩ := hA
    have hs_ne : s ≠ (a, b) := fun h => hab (h ▸ hsA)
    -- The "A ⊆ ..." filter refines the "s ∈ ..." filter.
    have h_le : cnt ≤ ((candidatePartnerSet n_A n_B k a b).filter
        (fun N => s ∈ N ∪ absentSlots a b N)).card := by
      rw [hcnt]
      refine Finset.card_le_card ?_
      intro N hN
      rw [Finset.mem_filter] at hN ⊢
      exact ⟨hN.1, hN.2 hsA⟩
    have h_slot := slot_supp_count_le a b k h_k_ge_2 h_k_le_A h_k_le_B s hs_ne
    have h_nat : min (n_A - 1) (n_B - 1) * cnt
        ≤ (k - 1) * (candidatePartnerSet n_A n_B k a b).card :=
      le_trans (Nat.mul_le_mul_left _ h_le) h_slot
    have h_real : ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ) * (cnt : ℝ)
        ≤ ((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ) := by
      have := h_nat
      push_cast at this ⊢
      exact_mod_cast this
    rw [le_div_iff₀ (by exact_mod_cast hmin_pos : (0:ℝ) < ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ))]
    linarith [h_real]

/-- **P3: verbatim Kim–Vu instantiated for the H_k-degree polynomial `c'`.**
Plug the P2 bounds — `mean = μ_c = expectedDegreeFormula` (`matchingCountNoFactor_integral`),
`E := #cand` (`matchingCountNoFactor_effect_le_cardCand`, ∀A), `E' := (k−1)#cand/min(n_A−1,n_B−1)`
(`matchingCountNoFactor_effect_le_E'`, nonempty A) — into `kim_vu_concentration_verbatim`. -/
lemma c'_verbatim_concentration {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (h_k_le_A : k ≤ n_A) (h_k_le_B : k ≤ n_B) (p : ENNReal) (hp : p ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 1 < lam →
      ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
        {g | kimVuConst k *
              Real.sqrt (((candidatePartnerSet n_A n_B k a b).card : ℝ)
                * (((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ)
                    / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ)))
              * lam ^ k
            < |matchingCountNoFactor a b k g - expectedDegreeFormula n_A n_B k p.toReal|}
        ≤ C * Real.exp (-lam + (k - 1 : ℝ)
            * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) := by
  classical
  have h_k_pos : 0 < k := by omega
  obtain ⟨C, hC_pos, hbound⟩ := kim_vu_concentration_verbatim k h_k_pos
  refine ⟨C, hC_pos, fun lam hlam => ?_⟩
  haveI : IsProbabilityMeasure
      ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure) :=
    inferInstance
  -- mean = ∫ f
  have h_mean : expectedDegreeFormula n_A n_B k p.toReal
      = ∫ g, matchingCountNoFactor a b k g
          ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure) :=
    (matchingCountNoFactor_integral a b k h_k_pos h_k_le_A h_k_le_B p hp).symm
  -- E-bound (∀ A)
  have h_E : ∀ A : Finset (Fin n_A × Fin n_B),
      ∫ g, |discreteDeriv (matchingCountNoFactor a b k) A g|
          ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
        ≤ ((candidatePartnerSet n_A n_B k a b).card : ℝ) :=
    fun A => matchingCountNoFactor_effect_le_cardCand a b k h_k_pos A p hp
  -- E'-bound (nonempty A)
  have h_E' : ∀ A : Finset (Fin n_A × Fin n_B), A.Nonempty →
      ∫ g, |discreteDeriv (matchingCountNoFactor a b k) A g|
          ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
        ≤ ((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ)
            / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ) :=
    fun A hA => matchingCountNoFactor_effect_le_E' a b k h_k_ge_2 h_k_le_A h_k_le_B A hA p hp
  -- 0 < E
  have h_Epos : (0:ℝ) < ((candidatePartnerSet n_A n_B k a b).card : ℝ) := by
    rw [candidatePartnerSet_card k h_k_pos h_k_le_A h_k_le_B a b]
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (Nat.choose_pos (by omega))
      (Nat.choose_pos (by omega))) (Nat.factorial_pos _)
  -- 0 < E'
  have h_E'pos : (0:ℝ) < ((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ)
      / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ) := by
    apply div_pos
    · exact mul_pos (by exact_mod_cast (by omega : 0 < k - 1)) h_Epos
    · exact_mod_cast (by omega : 0 < min (n_A - 1) (n_B - 1))
  exact hbound _ (matchingCountNoFactor a b k) (expectedDegreeFormula n_A n_B k p.toReal)
    ((candidatePartnerSet n_A n_B k a b).card : ℝ)
    (((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ)
      / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ))
    h_mean h_E h_E' h_Epos h_E'pos lam hlam

/-- **P3 regime: per-edge concentration `≤ C/N²`.** At `λ = (k+1)·log N` (`N = #variables =
n_A·n_B`), the verbatim tail collapses to `C·exp(−2 log N) = C/N²`; under the threshold
hypothesis `h_thresh` (the deviation scale at this `λ` sits below `ε·μ_c` — satisfiable for
balanced graphs, carried by `asymptotic_regime_BQ`), the relative-deviation event is dominated
by the verbatim event, giving `P(|c'−μ_c| ≥ ε·μ_c) ≤ C·N⁻²`. This is the union-bound-ready
per-edge bound for the constant-`k` B–Q nibble. -/
lemma c'_concentration_le {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (h_k_le_A : k ≤ n_A) (h_k_le_B : k ≤ n_B) (p : ENNReal) (hp : p ≤ 1)
    (ε : ℝ)
    (hN1 : 1 < (k + 1 : ℝ)
        * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ))
    (h_thresh : kimVuConst k *
          Real.sqrt (((candidatePartnerSet n_A n_B k a b).card : ℝ)
            * (((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ)
                / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ)))
          * ((k + 1 : ℝ) * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) ^ k
        < ε * expectedDegreeFormula n_A n_B k p.toReal) :
    ∃ C : ℝ, 0 < C ∧
      ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
        {g | ε * expectedDegreeFormula n_A n_B k p.toReal
              ≤ |matchingCountNoFactor a b k g - expectedDegreeFormula n_A n_B k p.toReal|}
        ≤ C * ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) ^ (-2 : ℤ) := by
  classical
  set N : ℝ := ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) with hN_def
  set lam : ℝ := (k + 1 : ℝ) * Real.log N with hlam_def
  set μm := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure
    with hμm_def
  haveI : IsProbabilityMeasure μm := inferInstance
  -- N > 0
  have hN_pos : 0 < N := by
    rw [hN_def]
    have : 0 < Fintype.card (Fin n_A × Fin n_B) := by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      have hA : 0 < n_A := by omega
      have hB : 0 < n_B := by omega
      exact Nat.mul_pos hA hB
    exact_mod_cast this
  -- The verbatim concentration bound.
  obtain ⟨C, hC_pos, hbound⟩ :=
    c'_verbatim_concentration a b k h_k_ge_2 h_k_le_A h_k_le_B p hp
  refine ⟨C, hC_pos, ?_⟩
  have hb := hbound lam hN1
  -- Event inclusion.
  have h_subset :
      {g | ε * expectedDegreeFormula n_A n_B k p.toReal
            ≤ |matchingCountNoFactor a b k g - expectedDegreeFormula n_A n_B k p.toReal|}
      ⊆ {g | kimVuConst k *
              Real.sqrt (((candidatePartnerSet n_A n_B k a b).card : ℝ)
                * (((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ)
                    / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ)))
              * lam ^ k
            < |matchingCountNoFactor a b k g - expectedDegreeFormula n_A n_B k p.toReal|} := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    exact lt_of_lt_of_le h_thresh hg
  -- Monotonicity of measure + the verbatim bound.
  have h_le := MeasureTheory.measureReal_mono (μ := μm) h_subset
  refine le_trans (le_trans h_le hb) ?_
  -- Tail simplification: exponent collapses to -2 log N.
  have h_exp : (-lam + (k - 1 : ℝ) * Real.log N) = (-2 : ℝ) * Real.log N := by
    rw [hlam_def]; ring
  rw [h_exp]
  -- exp(-2 log N) = N^(-2)
  have h_eq : Real.exp ((-2 : ℝ) * Real.log N) = N ^ (-2 : ℤ) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hN_pos, ← Real.rpow_intCast N (-2)]
    norm_num
  rw [h_eq]

/-- **P4 (regularity a.a.s.): union bound over all `N = n_A·n_B` edges.** Since `#cand`, `μ_c`,
`E'` are edge-independent, the per-edge bound `P(|c'(e)−μ_c| ≥ εμ_c) ≤ C/N²` is uniform (one
`C` from the axiom, chosen per `k`); union over the `N` edges gives `≤ N·C/N² = C/N → 0`. This
is the a.a.s. `(1±ε)`-regularity of `H_k` (each present edge's degree `c'` concentrates). -/
lemma c'_allEdges_concentration_aas {n_A n_B : ℕ} (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (h_k_le_A : k ≤ n_A) (h_k_le_B : k ≤ n_B) (p : ENNReal) (hp : p ≤ 1) (ε : ℝ)
    (hN1 : 1 < (k + 1 : ℝ) * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ))
    (h_thresh : ∀ (a : Fin n_A) (b : Fin n_B),
        kimVuConst k * Real.sqrt (((candidatePartnerSet n_A n_B k a b).card : ℝ)
            * (((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ)
                / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ)))
          * ((k + 1 : ℝ) * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) ^ k
        < ε * expectedDegreeFormula n_A n_B k p.toReal) :
      ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
        {g | ∃ (a : Fin n_A) (b : Fin n_B),
              ε * expectedDegreeFormula n_A n_B k p.toReal
                ≤ |matchingCountNoFactor a b k g - expectedDegreeFormula n_A n_B k p.toReal|}
        ≤ kimVuVerbatimConst k (by omega)
            / ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) := by
  classical
  set N : ℝ := ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) with hN_def
  set μc : ℝ := expectedDegreeFormula n_A n_B k p.toReal with hμc_def
  set lam : ℝ := (k + 1 : ℝ) * Real.log N with hlam_def
  set μm := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure
    with hμm_def
  haveI : IsProbabilityMeasure μm := inferInstance
  have h_k_pos : 0 < k := by omega
  -- N > 0
  have hN_pos : 0 < N := by
    rw [hN_def]
    have : 0 < Fintype.card (Fin n_A × Fin n_B) := by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      exact Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  -- Obtain the SHARED constant C once from the verbatim Kim–Vu axiom, using `.choose`
  -- so that the returned `C` is the canonical `kimVuVerbatimConst k` (n-independent, shared
  -- across all `c'`/`c''` applications — needed by the B–Q headline's Bonferroni budget).
  set C : ℝ := kimVuVerbatimConst k (by omega) with hC_def
  have hCeq : (kim_vu_concentration_verbatim k h_k_pos).choose = C := rfl
  obtain ⟨hC_pos, hbound⟩ := (kim_vu_concentration_verbatim k h_k_pos).choose_spec
  rw [hCeq] at hC_pos hbound
  -- Per-edge bound with the SHARED `C`, mirroring `c'_verbatim_concentration` +
  -- `c'_concentration_le` but reusing the already-obtained `hbound`.
  have hpe : ∀ (a : Fin n_A) (b : Fin n_B),
      μm.real {g | ε * μc ≤ |matchingCountNoFactor a b k g - μc|}
        ≤ C * N ^ (-2 : ℤ) := by
    intro a b
    -- The verbatim bound for this edge (mirror of `c'_verbatim_concentration`).
    have h_mean : μc = ∫ g, matchingCountNoFactor a b k g ∂μm :=
      (matchingCountNoFactor_integral a b k h_k_pos h_k_le_A h_k_le_B p hp).symm
    have h_E : ∀ A : Finset (Fin n_A × Fin n_B),
        ∫ g, |discreteDeriv (matchingCountNoFactor a b k) A g| ∂μm
          ≤ ((candidatePartnerSet n_A n_B k a b).card : ℝ) :=
      fun A => matchingCountNoFactor_effect_le_cardCand a b k h_k_pos A p hp
    have h_E' : ∀ A : Finset (Fin n_A × Fin n_B), A.Nonempty →
        ∫ g, |discreteDeriv (matchingCountNoFactor a b k) A g| ∂μm
          ≤ ((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ)
              / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ) :=
      fun A hA => matchingCountNoFactor_effect_le_E' a b k h_k_ge_2 h_k_le_A h_k_le_B A hA p hp
    have h_Epos : (0:ℝ) < ((candidatePartnerSet n_A n_B k a b).card : ℝ) := by
      rw [candidatePartnerSet_card k h_k_pos h_k_le_A h_k_le_B a b]
      exact_mod_cast Nat.mul_pos (Nat.mul_pos (Nat.choose_pos (by omega))
        (Nat.choose_pos (by omega))) (Nat.factorial_pos _)
    have h_E'pos : (0:ℝ) < ((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ)
        / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ) := by
      apply div_pos
      · exact mul_pos (by exact_mod_cast (by omega : 0 < k - 1)) h_Epos
      · exact_mod_cast (by omega : 0 < min (n_A - 1) (n_B - 1))
    have hb := hbound (ι := Fin n_A × Fin n_B) μm (matchingCountNoFactor a b k) μc
      ((candidatePartnerSet n_A n_B k a b).card : ℝ)
      (((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ)
        / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ))
      h_mean h_E h_E' h_Epos h_E'pos lam hN1
    -- Event inclusion via `h_thresh a b` (mirror of `c'_concentration_le`).
    have h_subset :
        {g | ε * μc ≤ |matchingCountNoFactor a b k g - μc|}
        ⊆ {g | kimVuConst k *
                Real.sqrt (((candidatePartnerSet n_A n_B k a b).card : ℝ)
                  * (((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ)
                      / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ)))
                * lam ^ k
              < |matchingCountNoFactor a b k g - μc|} := by
      intro g hg
      simp only [Set.mem_setOf_eq] at hg ⊢
      exact lt_of_lt_of_le (h_thresh a b) hg
    have h_le := MeasureTheory.measureReal_mono (μ := μm) h_subset
    refine le_trans (le_trans h_le hb) ?_
    -- Tail simplification.
    have h_exp : (-lam + (k - 1 : ℝ) * Real.log N) = (-2 : ℝ) * Real.log N := by
      rw [hlam_def]; ring
    rw [h_exp]
    have h_eq : Real.exp ((-2 : ℝ) * Real.log N) = N ^ (-2 : ℤ) := by
      rw [mul_comm, Real.exp_mul, Real.exp_log hN_pos, ← Real.rpow_intCast N (-2)]
      norm_num
    rw [h_eq]
  -- Rewrite the bad set as a `Fintype` indexed union over edges.
  have h_set_eq :
      {g | ∃ (a : Fin n_A) (b : Fin n_B), ε * μc ≤ |matchingCountNoFactor a b k g - μc|}
      = ⋃ (e : Fin n_A × Fin n_B),
          {g | ε * μc ≤ |matchingCountNoFactor e.1 e.2 k g - μc|} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Prod.exists]
  rw [h_set_eq]
  -- Union bound.
  refine le_trans (MeasureTheory.measureReal_iUnion_fintype_le (μ := μm) _) ?_
  refine le_trans (Finset.sum_le_sum (fun e _ => hpe e.1 e.2)) ?_
  -- Sum of the constant.
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, nsmul_eq_mul]
  -- `(n_A * n_B : ℝ) = N`, so `N * (C * N^(-2)) = C / N`.
  have hcast : ((n_A * n_B : ℕ) : ℝ) = N := by
    rw [hN_def, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  rw [hcast]
  have hNne : N ≠ 0 := ne_of_gt hN_pos
  apply le_of_eq
  rw [zpow_neg, zpow_two]
  field_simp

/-- **P4b step 1: `c'` is the realized H_k vertex-degree (for a present edge).** When the slot
`(a,b)` is present, `matchingCountNoFactor a b k g` equals the number of induced `k`-matchings of
the realized graph through `(a,b)` — i.e. the `SCIHypergraph_k` degree of the edge `(a,b)`. -/
lemma matchingCountNoFactor_eq_degree_of_present {n_A n_B : ℕ}
    (a : Fin n_A) (b : Fin n_B) (k : ℕ) (h_k_pos : 0 < k)
    (g : Fin n_A × Fin n_B → Bool) (hg : g (a, b) = true) :
    matchingCountNoFactor a b k g
      = (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
            (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
            Finset.univ Finset.univ k).filter (fun M => (a, b) ∈ M)).card : ℝ) := by
  classical
  -- Step 1: from the count identity, with `g (a,b) = true` the indicator is `1`.
  have h_count :
      (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
          (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
          Finset.univ Finset.univ k).filter (fun M => (a, b) ∈ M)).card : ℝ)
        = ∑ N ∈ ((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a, b)).powersetCard (k - 1),
            matchingIndicator a b N g := by
    simpa only [if_pos hg, mul_one] using
      count_mul_indicator_eq_sum_matchingIndicator k h_k_pos a b g
  -- Step 2: restrict the powersetCard sum to `candidatePartnerSet` (other terms vanish).
  have h_restrict :
      (∑ N ∈ ((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a, b)).powersetCard (k - 1),
          matchingIndicator a b N g)
        = ∑ N ∈ candidatePartnerSet n_A n_B k a b, matchingIndicator a b N g := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro N hN
      rw [mem_candidatePartnerSet_iff] at hN
      rw [Finset.mem_powersetCard]
      exact ⟨hN.1, hN.2.1⟩
    · intro N hN h_not
      exact matchingIndicator_eq_zero_of_not_candidate k h_k_pos a b N hN h_not g
  -- Step 3: each candidate summand equals the `matchingCountNoFactor` summand.
  have h_each :
      ∀ N ∈ candidatePartnerSet n_A n_B k a b,
        matchingIndicator a b N g = ∏ i, monoH N (absentSlots a b N) i (g i) := by
    intro N hN
    have h_cand : CandidatePartner a b N :=
      (mem_candidatePartnerSet_iff k a b N |>.mp hN).2.2
    have h_ab : (a, b) ∉ N := ab_not_mem_of_candidate k a b N hN
    -- (a,b) is in `presentSlots` and `presentSlots` is disjoint from `absentSlots`,
    -- so (a,b) ∉ absentSlots.
    have h_ab_pres : (a, b) ∈ presentSlots a b N := by
      unfold presentSlots; exact Finset.mem_insert_self _ _
    have h_ab_abs : (a, b) ∉ absentSlots a b N := fun h =>
      (Finset.disjoint_left.mp (presentSlots_disjoint_absentSlots a b N h_cand))
        h_ab_pres h
    -- rewrite via the monoH-product form
    have h_mono := congrFun (matchingIndicator_eq_monoH_prod a b N h_cand h_ab) g
    rw [h_mono]
    -- the two products differ only at `i = (a,b)`, where both factors equal `1`.
    refine Finset.prod_congr rfl ?_
    intro i _
    unfold presentSlots monoH
    by_cases h_eq : i = (a, b)
    · subst h_eq
      -- present side: i ∈ insert (a,b) N, b = g(a,b) = true ⇒ 1
      rw [if_pos (Finset.mem_insert_self _ _)]
      -- absent side: i ∉ N and i ∉ absentSlots ⇒ 1
      rw [if_neg h_ab, if_neg h_ab_abs]
      simp [hg]
    · -- i ≠ (a,b): i ∈ insert (a,b) N ↔ i ∈ N
      simp only [Finset.mem_insert, h_eq, false_or]
  -- Combine.
  rw [matchingCountNoFactor, ← Finset.sum_congr rfl h_each, ← h_restrict, ← h_count]

/-- **Codegree polynomial `c''`** (treating both `e₁=(a₁,b₁)`, `e₂=(a₂,b₂)` present): the number
of induced `k`-matchings containing both, as a polynomial in the OTHER slots (present set `N` =
the `k−2` completion edges, absent set = `absentSlotsPair`). The pair analogue of
`matchingCountNoFactor`. -/
noncomputable def matchingCodegreeNoFactor {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (k : ℕ)
    (g : Fin n_A × Fin n_B → Bool) : ℝ :=
  ∑ N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2,
    ∏ i, monoH N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) i (g i)

/-- STEP 0(a): `N` is disjoint from the core absent slots (drops the two anchor-anchor
bridges from `absentSlotsPair`). Derived from `presentSlotsPair_disjoint_absentSlotsPair`
via `N ⊆ presentSlotsPair` and `absentSlotsPairCore ⊆ absentSlotsPair`. -/
private lemma disjoint_N_absentSlotsPairCore {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (h_a : a_1 ≠ a_2) (h_b : b_1 ≠ b_2)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) :
    Disjoint N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) := by
  have h_N_sub_pres : N ⊆ presentSlotsPair a_1 a_2 b_1 b_2 N := by
    unfold presentSlotsPair
    exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  have h_core_sub : absentSlotsPairCore a_1 a_2 b_1 b_2 N
      ⊆ absentSlotsPair a_1 a_2 b_1 b_2 N := by
    rw [absentSlotsPair_eq_insert_core]
    exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  exact Finset.disjoint_of_subset_right h_core_sub
    (Finset.disjoint_of_subset_left h_N_sub_pres
      (presentSlotsPair_disjoint_absentSlotsPair a_1 a_2 b_1 b_2 h_a h_b N h_cand))

/-- STEP 0(b): the core absent slots have cardinality `k(k-1) - 2` (two fewer than
`absentSlotsPair`, having dropped the two anchor-anchor bridges). -/
private lemma absentSlotsPairCore_card {n_A n_B : ℕ} (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_a : a_1 ≠ a_2) (h_b : b_1 ≠ b_2)
    (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2) :
    (absentSlotsPairCore a_1 a_2 b_1 b_2 N).card = k * (k - 1) - 2 := by
  classical
  have h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N :=
    (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp hN |>.2.2
  have h_full : (absentSlotsPair a_1 a_2 b_1 b_2 N).card = k * (k - 1) :=
    absentSlotsPair_card k h_k_ge_2 a_1 a_2 b_1 b_2 h_a h_b N hN
  have h_a2b1_not : (a_2, b_1) ∉ absentSlotsPairCore a_1 a_2 b_1 b_2 N :=
    a2b1_not_mem_N_absent a_1 a_2 b_1 b_2 h_a h_b N h_cand
  have h_a1b2_not_core : (a_1, b_2) ∉ absentSlotsPairCore a_1 a_2 b_1 b_2 N :=
    a1b2_not_mem_N_absent a_1 a_2 b_1 b_2 h_a h_b N h_cand
  have h_ne : (a_1, b_2) ≠ (a_2, b_1) := a1b2_ne_a2b1 a_1 a_2 b_1 b_2 h_a
  have h_a1b2_not : (a_1, b_2) ∉ insert (a_2, b_1) (absentSlotsPairCore a_1 a_2 b_1 b_2 N) := by
    rw [Finset.mem_insert]; push_neg; exact ⟨h_ne, h_a1b2_not_core⟩
  have h_insert_card : (absentSlotsPair a_1 a_2 b_1 b_2 N).card
      = (absentSlotsPairCore a_1 a_2 b_1 b_2 N).card + 2 := by
    rw [absentSlotsPair_eq_insert_core, Finset.card_insert_of_notMem h_a1b2_not,
      Finset.card_insert_of_notMem h_a2b1_not]
  omega

/-- STEP 0(c): core analogue of `prod_slot_expectation_eval_pair` — the per-slot expectation
product over the whole grid splits as `q^|N| · (1-q)^|absentSlotsPairCore|`. -/
private lemma prod_slot_expectation_eval_core {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (h_a : a_1 ≠ a_2) (h_b : b_1 ≠ b_2)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) (q : ℝ) :
    (∏ i ∈ (Finset.univ : Finset (Fin n_A × Fin n_B)),
        (if i ∈ N then q
          else if i ∈ absentSlotsPairCore a_1 a_2 b_1 b_2 N then (1 - q) else 1))
      = q ^ N.card * (1 - q) ^ (absentSlotsPairCore a_1 a_2 b_1 b_2 N).card := by
  classical
  have h_disj : Disjoint N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) :=
    disjoint_N_absentSlotsPairCore a_1 a_2 b_1 b_2 h_a h_b N h_cand
  set T := absentSlotsPairCore a_1 a_2 b_1 b_2 N with hT
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ N ∪ T)]
  have h_rest : (∏ i ∈ Finset.univ.filter (fun i => ¬ i ∈ N ∪ T),
      (if i ∈ N then q else if i ∈ T then (1 - q) else 1)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [Finset.mem_filter, Finset.mem_union] at hi
    push_neg at hi
    rw [if_neg hi.2.1, if_neg hi.2.2]
  rw [h_rest, mul_one]
  have h_filter_eq : Finset.univ.filter (fun i => i ∈ N ∪ T) = N ∪ T := by
    ext i; simp
  rw [h_filter_eq, Finset.prod_union h_disj]
  have h_prodN : (∏ i ∈ N, (if i ∈ N then q else if i ∈ T then (1 - q) else 1))
      = q ^ N.card := by
    rw [Finset.prod_congr rfl (fun i hi => by rw [if_pos hi]), Finset.prod_const]
  have h_prodT : (∏ i ∈ T, (if i ∈ N then q else if i ∈ T then (1 - q) else 1))
      = (1 - q) ^ T.card := by
    refine (Finset.prod_congr rfl (fun i hi => ?_)).trans (Finset.prod_const _)
    have h_notN : i ∉ N := fun h => (Finset.disjoint_left.mp h_disj h) hi
    rw [if_neg h_notN, if_pos hi]
  rw [h_prodN, h_prodT, hT]

/-- Pair analogue of `prod_slot_expectation_eval`: the per-slot expectation product over the
whole grid splits as `q^|N| · (1-q)^|absentSlotsPair|`, using disjointness of `N` from
`absentSlotsPair` (via `presentSlotsPair ⊇ N`). -/
private lemma prod_slot_expectation_eval_pair {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (h_a : a_1 ≠ a_2) (h_b : b_1 ≠ b_2)
    (N : Finset (Fin n_A × Fin n_B))
    (h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N) (q : ℝ) :
    (∏ i ∈ (Finset.univ : Finset (Fin n_A × Fin n_B)),
        (if i ∈ N then q
          else if i ∈ absentSlotsPair a_1 a_2 b_1 b_2 N then (1 - q) else 1))
      = q ^ N.card * (1 - q) ^ (absentSlotsPair a_1 a_2 b_1 b_2 N).card := by
  classical
  -- `N` and `absentSlotsPair` are disjoint (from `presentSlotsPair = insert _ (insert _ N) ⊇ N`).
  have h_disj_pres : Disjoint (presentSlotsPair a_1 a_2 b_1 b_2 N)
      (absentSlotsPair a_1 a_2 b_1 b_2 N) :=
    presentSlotsPair_disjoint_absentSlotsPair a_1 a_2 b_1 b_2 h_a h_b N h_cand
  have h_N_sub_pres : N ⊆ presentSlotsPair a_1 a_2 b_1 b_2 N := by
    unfold presentSlotsPair
    exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
  have h_disj : Disjoint N (absentSlotsPair a_1 a_2 b_1 b_2 N) :=
    Finset.disjoint_of_subset_left h_N_sub_pres h_disj_pres
  set T := absentSlotsPair a_1 a_2 b_1 b_2 N with hT
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ N ∪ T)]
  -- The "not in N ∪ T" part is `1`.
  have h_rest : (∏ i ∈ Finset.univ.filter (fun i => ¬ i ∈ N ∪ T),
      (if i ∈ N then q else if i ∈ T then (1 - q) else 1)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [Finset.mem_filter, Finset.mem_union] at hi
    push_neg at hi
    rw [if_neg hi.2.1, if_neg hi.2.2]
  rw [h_rest, mul_one]
  -- The "in N ∪ T" part: split as union of disjoint `N` and `T`.
  have h_filter_eq : Finset.univ.filter (fun i => i ∈ N ∪ T) = N ∪ T := by
    ext i; simp
  rw [h_filter_eq, Finset.prod_union h_disj]
  -- Product over `N`: each factor is `q`.
  have h_prodN : (∏ i ∈ N, (if i ∈ N then q else if i ∈ T then (1 - q) else 1))
      = q ^ N.card := by
    rw [Finset.prod_congr rfl (fun i hi => by rw [if_pos hi]), Finset.prod_const]
  -- Product over `T`: each factor is `1-q` (using disjointness so `i ∉ N`).
  have h_prodT : (∏ i ∈ T, (if i ∈ N then q else if i ∈ T then (1 - q) else 1))
      = (1 - q) ^ T.card := by
    refine (Finset.prod_congr rfl (fun i hi => ?_)).trans (Finset.prod_const _)
    have h_notN : i ∉ N := fun h => (Finset.disjoint_left.mp h_disj h) hi
    rw [if_neg h_notN, if_pos hi]
  rw [h_prodN, h_prodT, hT]

/-- **Codegree mean: `E[c''] = |pairCand|·p^{k−2}(1−p)^{k(k−1)}`** (the expected codegree of a
distinct-row-col pair; `≪ μ_c`). Pair analogue of `matchingCountNoFactor_integral`. -/
lemma matchingCodegreeNoFactor_integral {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (h_a : a_1 ≠ a_2) (h_b : b_1 ≠ b_2) (p : ENNReal) (hp : p ≤ 1) :
    ∫ g, matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g
        ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      = ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
          * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2) := by
  classical
  set μ := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure
    with hμ_def
  -- Unfold and push the integral inside the finite sum over `candidatePairPartnerSet`.
  unfold matchingCodegreeNoFactor
  have h_integrable : ∀ N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2,
      MeasureTheory.Integrable
        (fun g => ∏ i, monoH N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) i (g i)) μ := by
    intro N _
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ f : Fin n_A × Fin n_B → Bool,
        ‖∏ i, monoH N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) i (f i)‖ ≤ C := by
      rcases Finset.exists_le
        (Finset.univ.image
          (fun f : Fin n_A × Fin n_B → Bool =>
            ‖∏ i, monoH N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) i (f i)‖))
        with ⟨C, hC⟩
      exact ⟨C, fun f => hC _ (Finset.mem_image.2 ⟨f, Finset.mem_univ f, rfl⟩)⟩
    haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
    exact (MeasureTheory.memLp_top_of_bound Measurable.of_discrete.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)).integrable le_top
  rw [MeasureTheory.integral_finset_sum _ h_integrable]
  -- Each summand: the product-integral, then product evaluation, then constant value.
  have h_each : ∀ N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2,
      ∫ g, (∏ i, monoH N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) i (g i)) ∂μ
        = p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2) := by
    intro N hN
    have h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N :=
      (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp hN |>.2.2
    have h_N_card : N.card = k - 2 :=
      (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp hN |>.2.1
    have h_abs_card : (absentSlotsPairCore a_1 a_2 b_1 b_2 N).card = k * (k - 1) - 2 :=
      absentSlotsPairCore_card k h_k_ge_2 a_1 a_2 b_1 b_2 h_a h_b N hN
    -- `∏ i, F i = ∏ i ∈ univ, F i`, so `integral_prod_monoH` applies directly.
    rw [hμ_def,
      integral_prod_monoH N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) Finset.univ p hp]
    rw [prod_slot_expectation_eval_core a_1 a_2 b_1 b_2 h_a h_b N h_cand p.toReal,
      h_N_card, h_abs_card]
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Codegree effect engine** (pair analogue of `matchingCountNoFactor_effect_le_sum`):
`E[|∂_A c''|] ≤ ∑_{N : A ⊆ N∪absentSlotsPair} ∏_{i∉A}(per-slot)`. -/
lemma matchingCodegreeNoFactor_effect_le_sum {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (k : ℕ) (_h_k_ge_2 : 2 ≤ k)
    (h_a : a_1 ≠ a_2) (h_b : b_1 ≠ b_2)
    (A : Finset (Fin n_A × Fin n_B)) (p : ENNReal) (hp : p ≤ 1) :
    ∫ g, |discreteDeriv (matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k) A g|
        ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      ≤ ∑ N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2,
          (if A ⊆ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N then
              ∏ i ∈ Aᶜ, (if i ∈ N then p.toReal
                  else if i ∈ absentSlotsPairCore a_1 a_2 b_1 b_2 N then (1 - p.toReal) else 1)
            else 0) := by
  classical
  set μ := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure
    with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  -- Abbreviation for the per-`N` monomial.
  set F : Finset (Fin n_A × Fin n_B) → (Fin n_A × Fin n_B → Bool) → ℝ :=
    fun N g => ∏ i, monoH N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) i (g i) with hF_def
  set cand := candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2 with hcand_def
  -- Step 1: linearity of `discreteDeriv` over the `N`-sum.
  have h_deriv_sum : ∀ g, discreteDeriv (matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k) A g
      = ∑ N ∈ cand, discreteDeriv (F N) A g := by
    intro g
    have : matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k = (fun g => ∑ N ∈ cand, F N g) := by
      funext g; rfl
    rw [this, discreteDeriv_finset_sum cand F A g]
  -- Per-`N` value of the derivative.
  have h_disj : ∀ N ∈ cand, Disjoint N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) := by
    intro N hN
    have h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N :=
      (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp hN |>.2.2
    exact disjoint_N_absentSlotsPairCore a_1 a_2 b_1 b_2 h_a h_b N h_cand
  -- Each monomial factor is in `[0,1]`, so the residual product is `≥ 0`.
  have h_monoH_nonneg : ∀ (N : Finset (Fin n_A × Fin n_B)) (i : Fin n_A × Fin n_B) (b' : Bool),
      0 ≤ monoH N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) i b' := by
    intro N i b'
    unfold monoH
    by_cases hS : i ∈ N
    · simp only [if_pos hS]; cases b' <;> simp
    · simp only [if_neg hS]
      by_cases hT : i ∈ absentSlotsPairCore a_1 a_2 b_1 b_2 N
      · simp only [if_pos hT]; cases b' <;> simp
      · simp only [if_neg hT]; norm_num
  have h_prod_nonneg : ∀ (N : Finset (Fin n_A × Fin n_B)) (g : Fin n_A × Fin n_B → Bool),
      0 ≤ ∏ i ∈ Aᶜ, monoH N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) i (g i) := by
    intro N g
    exact Finset.prod_nonneg (fun i _ => h_monoH_nonneg N i (g i))
  -- |∂_A (F N)| = (if A ⊆ N∪absent then 1 else 0) * (∏ over Aᶜ).
  have h_abs_deriv : ∀ N ∈ cand, ∀ g,
      |discreteDeriv (F N) A g|
        = (if A ⊆ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N then (1 : ℝ) else 0)
            * ∏ i ∈ Aᶜ, monoH N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) i (g i) := by
    intro N hN g
    rw [hF_def,
      discreteDeriv_monomial N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) (h_disj N hN) A g, abs_mul,
      abs_of_nonneg (h_prod_nonneg N g)]
    congr 1
    by_cases h : A ⊆ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N
    · simp only [if_pos h]
      rw [abs_pow, abs_neg, abs_one, one_pow]
    · simp only [if_neg h, abs_zero]
  -- Integrability helper for any function on this finite space.
  have h_int : ∀ (φ : (Fin n_A × Fin n_B → Bool) → ℝ), MeasureTheory.Integrable φ μ := by
    intro φ
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ f : Fin n_A × Fin n_B → Bool, ‖φ f‖ ≤ C := by
      rcases Finset.exists_le
        (Finset.univ.image (fun f : Fin n_A × Fin n_B → Bool => ‖φ f‖)) with ⟨C, hC⟩
      exact ⟨C, fun f => hC _ (Finset.mem_image.2 ⟨f, Finset.mem_univ f, rfl⟩)⟩
    exact (MeasureTheory.memLp_top_of_bound Measurable.of_discrete.aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)).integrable le_top
  -- Step 3: ∫ |∂_A c''| ≤ ∫ (∑ |∂_A F N|) = ∑ ∫ |∂_A F N|.
  calc ∫ g, |discreteDeriv (matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k) A g| ∂μ
      ≤ ∫ g, ∑ N ∈ cand, |discreteDeriv (F N) A g| ∂μ := by
        refine MeasureTheory.integral_mono (h_int _) (h_int _) ?_
        intro g
        simp only
        rw [h_deriv_sum g]
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ N ∈ cand, ∫ g, |discreteDeriv (F N) A g| ∂μ := by
        rw [MeasureTheory.integral_finset_sum _ (fun N _ => h_int _)]
    _ = ∑ N ∈ cand, (if A ⊆ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N then
            ∏ i ∈ Aᶜ, (if i ∈ N then p.toReal
                else if i ∈ absentSlotsPairCore a_1 a_2 b_1 b_2 N then (1 - p.toReal) else 1)
          else 0) := by
        refine Finset.sum_congr rfl ?_
        intro N hN
        rw [MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (h_abs_deriv N hN))]
        by_cases h : A ⊆ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N
        · simp only [if_pos h, one_mul]
          rw [hμ_def, integral_prod_monoH N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) Aᶜ p hp]
        · simp only [if_neg h, zero_mul, MeasureTheory.integral_zero]

/-- **Codegree count reduction** (pair analogue of `matchingCountNoFactor_effect_le_card`):
`E[|∂_A c''|] ≤ #{N ∈ pairCand : A ⊆ N∪absentSlotsPair_N}`. -/
lemma matchingCodegreeNoFactor_effect_le_card {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (h_a : a_1 ≠ a_2) (h_b : b_1 ≠ b_2)
    (A : Finset (Fin n_A × Fin n_B)) (p : ENNReal) (hp : p ≤ 1) :
    ∫ g, |discreteDeriv (matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k) A g|
        ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      ≤ (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).filter
            (fun N => A ⊆ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N)).card : ℝ) := by
  classical
  refine le_trans
    (matchingCodegreeNoFactor_effect_le_sum a_1 a_2 b_1 b_2 k h_k_ge_2 h_a h_b A p hp) ?_
  rw [← Finset.sum_boole]
  have hp_nonneg : (0 : ℝ) ≤ p.toReal := ENNReal.toReal_nonneg
  have hp_le_one : p.toReal ≤ 1 :=
    le_trans (ENNReal.toReal_mono (by simp) hp) (by simp)
  refine Finset.sum_le_sum ?_
  intro N hN
  by_cases h : A ⊆ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N
  · simp only [if_pos h]
    refine Finset.prod_le_one ?_ ?_
    · intro i _
      split_ifs
      · exact hp_nonneg
      · linarith
      · norm_num
    · intro i _
      split_ifs
      · exact hp_le_one
      · linarith
      · exact le_rfl
  · simp only [if_neg h]; exact le_rfl

/-- **Codegree `E := #pairCand`** (pair analogue of `matchingCountNoFactor_effect_le_cardCand`):
unconditional `E` bound for the codegree polynomial. -/
lemma matchingCodegreeNoFactor_effect_le_cardCand {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (h_a : a_1 ≠ a_2) (h_b : b_1 ≠ b_2)
    (A : Finset (Fin n_A × Fin n_B)) (p : ENNReal) (hp : p ≤ 1) :
    ∫ g, |discreteDeriv (matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k) A g|
        ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      ≤ ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ) := by
  refine le_trans (matchingCodegreeNoFactor_effect_le_card a_1 a_2 b_1 b_2 k h_k_ge_2 h_a h_b A p hp) ?_
  exact_mod_cast Finset.card_filter_le _ _

/-- For a candidate pair N: `N.image snd ⊆ (univ.erase b_1).erase b_2`. -/
private lemma candidatePair_image_snd_subset {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2) :
    N.image Prod.snd ⊆ (Finset.univ.erase b_1).erase b_2 := by
  classical
  rw [mem_candidatePairPartnerSet_iff] at hN
  obtain ⟨_, _, _, _, h_b1, h_b2, _, _⟩ := hN
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨y, hy, h_eq⟩ := hx
  rw [Finset.mem_erase, Finset.mem_erase]
  refine ⟨?_, ?_, Finset.mem_univ _⟩
  · rw [← h_eq]; exact h_b2 y hy
  · rw [← h_eq]; exact h_b1 y hy

/-- For a candidate pair N: `(N.image snd).card = k - 2`. -/
private lemma candidatePair_image_snd_card {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2) :
    (N.image Prod.snd).card = k - 2 := by
  classical
  rw [mem_candidatePairPartnerSet_iff] at hN
  obtain ⟨_, h_N_card, _, _, _, _, _, h_B_inj⟩ := hN
  rw [Finset.card_image_of_injOn, h_N_card]
  intro x hx y hy h_eq
  by_contra h_ne
  exact (h_B_inj x hx y hy h_ne) h_eq

/-- Relabel the B-coordinate of every edge of `N` by swapping columns `c ↔ c'`
(pair version). -/
private noncomputable def relabelColPair {n_A n_B : ℕ} (c c' : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) : Finset (Fin n_A × Fin n_B) :=
  N.image (fun x => (x.1, Equiv.swap c c' x.2))

private lemma mem_relabelColPair {n_A n_B : ℕ} (c c' : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) (p : Fin n_A × Fin n_B) :
    p ∈ relabelColPair c c' N ↔ ∃ x ∈ N, (x.1, Equiv.swap c c' x.2) = p := by
  unfold relabelColPair; rw [Finset.mem_image]

private lemma relabelColPair_involutive {n_A n_B : ℕ} (c c' : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) :
    relabelColPair c c' (relabelColPair c c' N) = N := by
  classical
  unfold relabelColPair
  rw [Finset.image_image]
  have : (fun x : Fin n_A × Fin n_B => (x.1, Equiv.swap c c' x.2)) ∘
      (fun x : Fin n_A × Fin n_B => (x.1, Equiv.swap c c' x.2)) = id := by
    funext x
    simp [Function.comp, Equiv.swap_apply_self]
  rw [this, Finset.image_id]

/-- If `c, c' ∉ {b_1, b_2}`, then `relabelColPair c c'` maps `candidatePairPartnerSet`
into itself. -/
private lemma relabelColPair_mem_candidatePairPartnerSet {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (c c' : Fin n_B)
    (hc1 : c ≠ b_1) (hc2 : c ≠ b_2) (hc'1 : c' ≠ b_1) (hc'2 : c' ≠ b_2)
    (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2) :
    relabelColPair c c' N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2 := by
  classical
  rw [mem_candidatePairPartnerSet_iff] at hN ⊢
  obtain ⟨h_sub, h_card, h_cand⟩ := hN
  obtain ⟨h_a1, h_a2, h_b1, h_b2, h_A_inj, h_B_inj⟩ := h_cand
  have h_inj : Set.InjOn (fun x : Fin n_A × Fin n_B => (x.1, Equiv.swap c c' x.2)) N := by
    intro x _ y _ h_eq
    have h1 : x.1 = y.1 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
    have h2 : Equiv.swap c c' x.2 = Equiv.swap c c' y.2 :=
      (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
    have h2' : x.2 = y.2 := (Equiv.swap c c').injective h2
    exact Prod.ext h1 h2'
  -- swap fixes b_1, b_2
  have hswb1 : Equiv.swap c c' b_1 = b_1 :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hc1) (Ne.symm hc'1)
  have hswb2 : Equiv.swap c c' b_2 = b_2 :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hc2) (Ne.symm hc'2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- subset
    intro p hp
    rw [mem_relabelColPair] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [Finset.mem_erase, Finset.mem_erase]
    refine ⟨?_, ?_, Finset.mem_univ _⟩
    · -- p ≠ (a_2, b_2): if so, swap x.2 = b_2 ⇒ x.2 = b_2, contradiction.
      rw [← h_eq]; intro h_contra
      have h_p2 : Equiv.swap c c' x.2 = b_2 := (Prod.mk.injEq _ _ _ _).mp h_contra |>.2
      have : x.2 = b_2 := by rw [Equiv.swap_apply_eq_iff, hswb2] at h_p2; exact h_p2
      exact (h_b2 x hx) this
    · rw [← h_eq]; intro h_contra
      have h_p2 : Equiv.swap c c' x.2 = b_1 := (Prod.mk.injEq _ _ _ _).mp h_contra |>.2
      have : x.2 = b_1 := by rw [Equiv.swap_apply_eq_iff, hswb1] at h_p2; exact h_p2
      exact (h_b1 x hx) this
  · rw [relabelColPair, Finset.card_image_of_injOn h_inj, h_card]
  · intro p hp
    rw [mem_relabelColPair] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [← h_eq]; exact h_a1 x hx
  · intro p hp
    rw [mem_relabelColPair] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [← h_eq]; exact h_a2 x hx
  · intro p hp
    rw [mem_relabelColPair] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [← h_eq]; intro h_contra
    have : x.2 = b_1 := by rw [Equiv.swap_apply_eq_iff, hswb1] at h_contra; exact h_contra
    exact (h_b1 x hx) this
  · intro p hp
    rw [mem_relabelColPair] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [← h_eq]; intro h_contra
    have : x.2 = b_2 := by rw [Equiv.swap_apply_eq_iff, hswb2] at h_contra; exact h_contra
    exact (h_b2 x hx) this
  · intro p hp q hq h_ne
    rw [mem_relabelColPair] at hp hq
    obtain ⟨x, hx, h_eqx⟩ := hp
    obtain ⟨y, hy, h_eqy⟩ := hq
    rw [← h_eqx, ← h_eqy]
    have hxy : x ≠ y := by intro h; apply h_ne; rw [← h_eqx, ← h_eqy, h]
    exact h_A_inj x hx y hy hxy
  · intro p hp q hq h_ne
    rw [mem_relabelColPair] at hp hq
    obtain ⟨x, hx, h_eqx⟩ := hp
    obtain ⟨y, hy, h_eqy⟩ := hq
    rw [← h_eqx, ← h_eqy]; simp only
    have hxy : x ≠ y := by intro h; apply h_ne; rw [← h_eqx, ← h_eqy, h]
    intro h_swap
    have : x.2 = y.2 := (Equiv.swap c c').injective h_swap
    exact h_B_inj x hx y hy hxy this

private lemma relabelColPair_image_snd_iff {n_A n_B : ℕ} (c c' : Fin n_B)
    (N : Finset (Fin n_A × Fin n_B)) :
    c' ∈ (relabelColPair c c' N).image Prod.snd ↔ c ∈ N.image Prod.snd := by
  classical
  constructor
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨p, hp, hp2⟩ := h
    rw [mem_relabelColPair] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [Finset.mem_image]
    refine ⟨x, hx, ?_⟩
    have hsc : Equiv.swap c c' x.2 = c' := by rw [← h_eq] at hp2; exact hp2
    have h2 : x.2 = Equiv.swap c c' c' := Equiv.swap_apply_eq_iff.mp hsc
    rw [Equiv.swap_apply_right] at h2; exact h2
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨x, hx, hx2⟩ := h
    rw [Finset.mem_image]
    refine ⟨(x.1, Equiv.swap c c' x.2), ?_, ?_⟩
    · rw [mem_relabelColPair]; exact ⟨x, hx, rfl⟩
    · change Equiv.swap c c' x.2 = c'
      rw [hx2, Equiv.swap_apply_left]

/-- For two columns `c, c' ∉ {b_1, b_2}`, the number of pair-candidate matchings using
column `c` equals the number using column `c'`. -/
private lemma candidate_col_count_eq_pair {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (c c' : Fin n_B)
    (hc1 : c ≠ b_1) (hc2 : c ≠ b_2) (hc'1 : c' ≠ b_1) (hc'2 : c' ≠ b_2) :
    ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).filter
        (fun N => c ∈ N.image Prod.snd)).card
      = ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).filter
        (fun N => c' ∈ N.image Prod.snd)).card := by
  classical
  apply Finset.card_nbij' (relabelColPair c c') (relabelColPair c c')
  · intro N hN
    rw [Finset.mem_coe, Finset.mem_filter] at hN ⊢
    refine ⟨relabelColPair_mem_candidatePairPartnerSet k a_1 a_2 b_1 b_2 c c'
      hc1 hc2 hc'1 hc'2 N hN.1, ?_⟩
    rw [relabelColPair_image_snd_iff]; exact hN.2
  · intro N hN
    rw [Finset.mem_coe, Finset.mem_filter] at hN ⊢
    refine ⟨relabelColPair_mem_candidatePairPartnerSet k a_1 a_2 b_1 b_2 c c'
      hc1 hc2 hc'1 hc'2 N hN.1, ?_⟩
    have h_symm : relabelColPair c c' N = relabelColPair c' c N := by
      unfold relabelColPair; rw [Equiv.swap_comm]
    rw [h_symm, relabelColPair_image_snd_iff c' c N]; exact hN.2
  · intro N _; exact relabelColPair_involutive c c' N
  · intro N _; exact relabelColPair_involutive c c' N

/-- Relabel the A-coordinate of every edge of `N` by swapping rows `r ↔ r'`
(pair version). -/
private noncomputable def relabelRowPair {n_A n_B : ℕ} (r r' : Fin n_A)
    (N : Finset (Fin n_A × Fin n_B)) : Finset (Fin n_A × Fin n_B) :=
  N.image (fun x => (Equiv.swap r r' x.1, x.2))

private lemma mem_relabelRowPair {n_A n_B : ℕ} (r r' : Fin n_A)
    (N : Finset (Fin n_A × Fin n_B)) (p : Fin n_A × Fin n_B) :
    p ∈ relabelRowPair r r' N ↔ ∃ x ∈ N, (Equiv.swap r r' x.1, x.2) = p := by
  unfold relabelRowPair; rw [Finset.mem_image]

private lemma relabelRowPair_involutive {n_A n_B : ℕ} (r r' : Fin n_A)
    (N : Finset (Fin n_A × Fin n_B)) :
    relabelRowPair r r' (relabelRowPair r r' N) = N := by
  classical
  unfold relabelRowPair
  rw [Finset.image_image]
  have : (fun x : Fin n_A × Fin n_B => (Equiv.swap r r' x.1, x.2)) ∘
      (fun x : Fin n_A × Fin n_B => (Equiv.swap r r' x.1, x.2)) = id := by
    funext x
    simp [Function.comp, Equiv.swap_apply_self]
  rw [this, Finset.image_id]

private lemma relabelRowPair_mem_candidatePairPartnerSet {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (r r' : Fin n_A)
    (hr1 : r ≠ a_1) (hr2 : r ≠ a_2) (hr'1 : r' ≠ a_1) (hr'2 : r' ≠ a_2)
    (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2) :
    relabelRowPair r r' N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2 := by
  classical
  rw [mem_candidatePairPartnerSet_iff] at hN ⊢
  obtain ⟨h_sub, h_card, h_cand⟩ := hN
  obtain ⟨h_a1, h_a2, h_b1, h_b2, h_A_inj, h_B_inj⟩ := h_cand
  have h_inj : Set.InjOn (fun x : Fin n_A × Fin n_B => (Equiv.swap r r' x.1, x.2)) N := by
    intro x _ y _ h_eq
    have h1 : Equiv.swap r r' x.1 = Equiv.swap r r' y.1 :=
      (Prod.mk.injEq _ _ _ _).mp h_eq |>.1
    have h1' : x.1 = y.1 := (Equiv.swap r r').injective h1
    have h2 : x.2 = y.2 := (Prod.mk.injEq _ _ _ _).mp h_eq |>.2
    exact Prod.ext h1' h2
  have hswa1 : Equiv.swap r r' a_1 = a_1 :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hr1) (Ne.symm hr'1)
  have hswa2 : Equiv.swap r r' a_2 = a_2 :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hr2) (Ne.symm hr'2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [mem_relabelRowPair] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [Finset.mem_erase, Finset.mem_erase]
    refine ⟨?_, ?_, Finset.mem_univ _⟩
    · rw [← h_eq]; intro h_contra
      have h_p1 : Equiv.swap r r' x.1 = a_2 := (Prod.mk.injEq _ _ _ _).mp h_contra |>.1
      have : x.1 = a_2 := by rw [Equiv.swap_apply_eq_iff, hswa2] at h_p1; exact h_p1
      exact (h_a2 x hx) this
    · rw [← h_eq]; intro h_contra
      have h_p1 : Equiv.swap r r' x.1 = a_1 := (Prod.mk.injEq _ _ _ _).mp h_contra |>.1
      have : x.1 = a_1 := by rw [Equiv.swap_apply_eq_iff, hswa1] at h_p1; exact h_p1
      exact (h_a1 x hx) this
  · rw [relabelRowPair, Finset.card_image_of_injOn h_inj, h_card]
  · intro p hp
    rw [mem_relabelRowPair] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [← h_eq]; intro h_contra
    have : x.1 = a_1 := by rw [Equiv.swap_apply_eq_iff, hswa1] at h_contra; exact h_contra
    exact (h_a1 x hx) this
  · intro p hp
    rw [mem_relabelRowPair] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [← h_eq]; intro h_contra
    have : x.1 = a_2 := by rw [Equiv.swap_apply_eq_iff, hswa2] at h_contra; exact h_contra
    exact (h_a2 x hx) this
  · intro p hp
    rw [mem_relabelRowPair] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [← h_eq]; exact h_b1 x hx
  · intro p hp
    rw [mem_relabelRowPair] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [← h_eq]; exact h_b2 x hx
  · intro p hp q hq h_ne
    rw [mem_relabelRowPair] at hp hq
    obtain ⟨x, hx, h_eqx⟩ := hp
    obtain ⟨y, hy, h_eqy⟩ := hq
    rw [← h_eqx, ← h_eqy]; simp only
    have hxy : x ≠ y := by intro h; apply h_ne; rw [← h_eqx, ← h_eqy, h]
    intro h_swap
    have : x.1 = y.1 := (Equiv.swap r r').injective h_swap
    exact h_A_inj x hx y hy hxy this
  · intro p hp q hq h_ne
    rw [mem_relabelRowPair] at hp hq
    obtain ⟨x, hx, h_eqx⟩ := hp
    obtain ⟨y, hy, h_eqy⟩ := hq
    rw [← h_eqx, ← h_eqy]
    have hxy : x ≠ y := by intro h; apply h_ne; rw [← h_eqx, ← h_eqy, h]
    exact h_B_inj x hx y hy hxy

private lemma relabelRowPair_image_fst_iff {n_A n_B : ℕ} (r r' : Fin n_A)
    (N : Finset (Fin n_A × Fin n_B)) :
    r' ∈ (relabelRowPair r r' N).image Prod.fst ↔ r ∈ N.image Prod.fst := by
  classical
  constructor
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨p, hp, hp1⟩ := h
    rw [mem_relabelRowPair] at hp
    obtain ⟨x, hx, h_eq⟩ := hp
    rw [Finset.mem_image]
    refine ⟨x, hx, ?_⟩
    have hsr : Equiv.swap r r' x.1 = r' := by rw [← h_eq] at hp1; exact hp1
    have h1 : x.1 = Equiv.swap r r' r' := Equiv.swap_apply_eq_iff.mp hsr
    rw [Equiv.swap_apply_right] at h1; exact h1
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨x, hx, hx1⟩ := h
    rw [Finset.mem_image]
    refine ⟨(Equiv.swap r r' x.1, x.2), ?_, ?_⟩
    · rw [mem_relabelRowPair]; exact ⟨x, hx, rfl⟩
    · change Equiv.swap r r' x.1 = r'
      rw [hx1, Equiv.swap_apply_left]

private lemma candidate_row_count_eq_pair {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (r r' : Fin n_A)
    (hr1 : r ≠ a_1) (hr2 : r ≠ a_2) (hr'1 : r' ≠ a_1) (hr'2 : r' ≠ a_2) :
    ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).filter
        (fun N => r ∈ N.image Prod.fst)).card
      = ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).filter
        (fun N => r' ∈ N.image Prod.fst)).card := by
  classical
  apply Finset.card_nbij' (relabelRowPair r r') (relabelRowPair r r')
  · intro N hN
    rw [Finset.mem_coe, Finset.mem_filter] at hN ⊢
    refine ⟨relabelRowPair_mem_candidatePairPartnerSet k a_1 a_2 b_1 b_2 r r'
      hr1 hr2 hr'1 hr'2 N hN.1, ?_⟩
    rw [relabelRowPair_image_fst_iff]; exact hN.2
  · intro N hN
    rw [Finset.mem_coe, Finset.mem_filter] at hN ⊢
    refine ⟨relabelRowPair_mem_candidatePairPartnerSet k a_1 a_2 b_1 b_2 r r'
      hr1 hr2 hr'1 hr'2 N hN.1, ?_⟩
    have h_symm : relabelRowPair r r' N = relabelRowPair r' r N := by
      unfold relabelRowPair; rw [Equiv.swap_comm]
    rw [h_symm, relabelRowPair_image_fst_iff r' r N]; exact hN.2
  · intro N _; exact relabelRowPair_involutive r r' N
  · intro N _; exact relabelRowPair_involutive r r' N

/-- **Pair column double-count equality.** For `β ∉ {b_1, b_2}`,
`(n_B − 2) · #{N ∈ pairCand : β ∈ cols(N)} = (k − 2) · #pairCand`. -/
private lemma candidate_col_double_count_pair {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (h_b : b_1 ≠ b_2) (β : Fin n_B)
    (hβ1 : β ≠ b_1) (hβ2 : β ≠ b_2) :
    (n_B - 2) * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).filter
        (fun N => β ∈ N.image Prod.snd)).card
      = (k - 2) * (candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card := by
  classical
  set cand := candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2 with hcand
  set partnerCols := ((Finset.univ.erase b_1).erase b_2 : Finset (Fin n_B)) with hpc
  have h_rowsum : ∑ N ∈ cand, (partnerCols.filter (fun c => c ∈ N.image Prod.snd)).card
      = (k - 2) * cand.card := by
    rw [Finset.sum_congr rfl (fun N hN => ?_)]
    · rw [Finset.sum_const, smul_eq_mul, mul_comm]
    · have h_sub : N.image Prod.snd ⊆ partnerCols :=
        candidatePair_image_snd_subset k a_1 a_2 b_1 b_2 N hN
      have : partnerCols.filter (fun c => c ∈ N.image Prod.snd) = N.image Prod.snd :=
        (Finset.filter_mem_eq_inter).trans (Finset.inter_eq_right.mpr h_sub)
      rw [this, candidatePair_image_snd_card k a_1 a_2 b_1 b_2 N hN]
  have h_colsum : ∑ c ∈ partnerCols, (cand.filter (fun N => c ∈ N.image Prod.snd)).card
      = (n_B - 2) * (cand.filter (fun N => β ∈ N.image Prod.snd)).card := by
    rw [Finset.sum_congr rfl (fun c hc => ?_)]
    · rw [Finset.sum_const, smul_eq_mul]
      congr 1
      rw [hpc]
      have hb1 : b_1 ∈ (Finset.univ : Finset (Fin n_B)) := Finset.mem_univ _
      have hb2 : b_2 ∈ (Finset.univ.erase b_1 : Finset (Fin n_B)) :=
        Finset.mem_erase.mpr ⟨Ne.symm h_b, Finset.mem_univ _⟩
      rw [Finset.card_erase_of_mem hb2, Finset.card_erase_of_mem hb1,
        Finset.card_univ, Fintype.card_fin]
      omega
    · have hc2 : c ≠ b_2 := (Finset.mem_erase.mp hc).1
      have hc1 : c ≠ b_1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
      exact candidate_col_count_eq_pair k a_1 a_2 b_1 b_2 c β hc1 hc2 hβ1 hβ2
  have h_comm : ∑ N ∈ cand, (partnerCols.filter (fun c => c ∈ N.image Prod.snd)).card
      = ∑ c ∈ partnerCols, (cand.filter (fun N => c ∈ N.image Prod.snd)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [← h_colsum, ← h_comm, h_rowsum]

/-- **Pair row double-count equality.** For `α ∉ {a_1, a_2}`,
`(n_A − 2) · #{N ∈ pairCand : α ∈ rows(N)} = (k − 2) · #pairCand`. -/
private lemma candidate_row_double_count_pair {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (h_a : a_1 ≠ a_2) (b_1 b_2 : Fin n_B) (α : Fin n_A)
    (hα1 : α ≠ a_1) (hα2 : α ≠ a_2) :
    (n_A - 2) * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).filter
        (fun N => α ∈ N.image Prod.fst)).card
      = (k - 2) * (candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card := by
  classical
  set cand := candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2 with hcand
  set partnerRows := ((Finset.univ.erase a_1).erase a_2 : Finset (Fin n_A)) with hpr
  have h_rowsum : ∑ N ∈ cand, (partnerRows.filter (fun r => r ∈ N.image Prod.fst)).card
      = (k - 2) * cand.card := by
    rw [Finset.sum_congr rfl (fun N hN => ?_)]
    · rw [Finset.sum_const, smul_eq_mul, mul_comm]
    · have h_sub : N.image Prod.fst ⊆ partnerRows :=
        candidatePair_image_fst_subset k a_1 a_2 b_1 b_2 N hN
      have : partnerRows.filter (fun r => r ∈ N.image Prod.fst) = N.image Prod.fst :=
        (Finset.filter_mem_eq_inter).trans (Finset.inter_eq_right.mpr h_sub)
      rw [this, candidatePair_image_fst_card k a_1 a_2 b_1 b_2 N hN]
  have h_colsum : ∑ r ∈ partnerRows, (cand.filter (fun N => r ∈ N.image Prod.fst)).card
      = (n_A - 2) * (cand.filter (fun N => α ∈ N.image Prod.fst)).card := by
    rw [Finset.sum_congr rfl (fun r hr => ?_)]
    · rw [Finset.sum_const, smul_eq_mul]
      congr 1
      rw [hpr]
      have ha1 : a_1 ∈ (Finset.univ : Finset (Fin n_A)) := Finset.mem_univ _
      have ha2 : a_2 ∈ (Finset.univ.erase a_1 : Finset (Fin n_A)) :=
        Finset.mem_erase.mpr ⟨Ne.symm h_a, Finset.mem_univ _⟩
      rw [Finset.card_erase_of_mem ha2, Finset.card_erase_of_mem ha1,
        Finset.card_univ, Fintype.card_fin]
      omega
    · have hr2 : r ≠ a_2 := (Finset.mem_erase.mp hr).1
      have hr1 : r ≠ a_1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
      exact candidate_row_count_eq_pair k a_1 a_2 b_1 b_2 r α hr1 hr2 hα1 hα2
  have h_comm : ∑ N ∈ cand, (partnerRows.filter (fun r => r ∈ N.image Prod.fst)).card
      = ∑ r ∈ partnerRows, (cand.filter (fun N => r ∈ N.image Prod.fst)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [← h_colsum, ← h_comm, h_rowsum]

/-- **Codegree `E'` per-slot count** (pair analogue of `slot_supp_count_le`). For a slot
`s ∉ {(a₁,b₁),(a₂,b₂),(a₁,b₂),(a₂,b₁)}` (the 4 anchor slots), the number of pair-candidate
matchings whose core support contains `s` is codegree-of-codegree scale:
`min(n_A−2,n_B−2) · #{N : s ∈ N ∪ absentSlotsPairCore_N} ≤ (k−2) · #pairCand`. -/
lemma slot_supp_count_le_pair {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (k : ℕ) (_h_k_ge_2 : 2 ≤ k)
    (h_a : a_1 ≠ a_2) (h_b : b_1 ≠ b_2) (_h_k_le_A : k ≤ n_A) (_h_k_le_B : k ≤ n_B)
    (s : Fin n_A × Fin n_B)
    (hs1 : s ≠ (a_1, b_1)) (hs2 : s ≠ (a_2, b_2))
    (hs3 : s ≠ (a_1, b_2)) (hs4 : s ≠ (a_2, b_1)) :
    (min (n_A - 2) (n_B - 2)) *
        ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).filter
          (fun N => s ∈ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N)).card
      ≤ (k - 2) * (candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card := by
  classical
  obtain ⟨α, β⟩ := s
  set cand := candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2 with hcand
  by_cases hβ : β = b_1 ∨ β = b_2
  · -- β ∈ {b_1, b_2}: then α ∉ {a_1, a_2} (else s is an anchor). Reduce to row condition.
    have hα1 : α ≠ a_1 := by
      intro h
      rcases hβ with hb | hb
      · exact hs1 (by rw [h, hb])
      · exact hs3 (by rw [h, hb])
    have hα2 : α ≠ a_2 := by
      intro h
      rcases hβ with hb | hb
      · exact hs4 (by rw [h, hb])
      · exact hs2 (by rw [h, hb])
    have h_subset : (cand.filter (fun N => (α, β) ∈ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N))
        ⊆ (cand.filter (fun N => α ∈ N.image Prod.fst)) := by
      intro N hN
      rw [Finset.mem_filter] at hN ⊢
      obtain ⟨hN_cand, hN_mem⟩ := hN
      refine ⟨hN_cand, ?_⟩
      have h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N :=
        (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp hN_cand |>.2.2
      rw [Finset.mem_union] at hN_mem
      rcases hN_mem with hIn | hAbs
      · -- (α,β) ∈ N: β = b_1 or b_2 forbidden for candidates. Contradiction.
        exfalso
        rcases hβ with hb | hb
        · exact h_cand.2.2.1 (α, β) hIn (by rw [hb])
        · exact h_cand.2.2.2.1 (α, β) hIn (by rw [hb])
      · unfold absentSlotsPairCore at hAbs
        rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union] at hAbs
        rcases hAbs with ((((hA1 | hA2) | hB1) | hB2) | hW)
        · -- aBridge a_1: (a_1, x.2) ⇒ α = a_1, forbidden.
          exfalso
          unfold aBridgeSlots at hA1
          rw [Finset.mem_image] at hA1
          obtain ⟨x, _, h_eq⟩ := hA1
          exact hα1 ((Prod.mk.injEq _ _ _ _).mp h_eq |>.1).symm
        · exfalso
          unfold aBridgeSlots at hA2
          rw [Finset.mem_image] at hA2
          obtain ⟨x, _, h_eq⟩ := hA2
          exact hα2 ((Prod.mk.injEq _ _ _ _).mp h_eq |>.1).symm
        · -- bBridge b_1: (x.1, b_1) ⇒ α = x.1 ∈ rows(N).
          unfold bBridgeSlots at hB1
          rw [Finset.mem_image] at hB1
          obtain ⟨x, hx, h_eq⟩ := hB1
          rw [Finset.mem_image]
          exact ⟨x, hx, ((Prod.mk.injEq _ _ _ _).mp h_eq |>.1)⟩
        · unfold bBridgeSlots at hB2
          rw [Finset.mem_image] at hB2
          obtain ⟨x, hx, h_eq⟩ := hB2
          rw [Finset.mem_image]
          exact ⟨x, hx, ((Prod.mk.injEq _ _ _ _).mp h_eq |>.1)⟩
        · -- withinN: (x.1, y.2) ⇒ α = x.1 ∈ rows(N).
          unfold withinNSlots at hW
          rw [Finset.mem_image] at hW
          obtain ⟨p, hp, h_eq⟩ := hW
          rw [Finset.mem_filter, Finset.mem_product] at hp
          rw [Finset.mem_image]
          exact ⟨p.1, hp.1.1, ((Prod.mk.injEq _ _ _ _).mp h_eq |>.1)⟩
    have h_card_le : (cand.filter (fun N => (α, β) ∈ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N)).card
        ≤ (cand.filter (fun N => α ∈ N.image Prod.fst)).card := Finset.card_le_card h_subset
    calc (min (n_A - 2) (n_B - 2)) *
            (cand.filter (fun N => (α, β) ∈ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N)).card
        ≤ (n_A - 2) * (cand.filter (fun N => α ∈ N.image Prod.fst)).card := by
          apply Nat.mul_le_mul (Nat.min_le_left _ _) h_card_le
      _ = (k - 2) * cand.card :=
          candidate_row_double_count_pair k a_1 a_2 h_a b_1 b_2 α hα1 hα2
  · -- β ∉ {b_1, b_2}: reduce to column condition.
    push_neg at hβ
    obtain ⟨hβ1, hβ2⟩ := hβ
    have h_subset : (cand.filter (fun N => (α, β) ∈ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N))
        ⊆ (cand.filter (fun N => β ∈ N.image Prod.snd)) := by
      intro N hN
      rw [Finset.mem_filter] at hN ⊢
      obtain ⟨hN_cand, hN_mem⟩ := hN
      refine ⟨hN_cand, ?_⟩
      rw [Finset.mem_union] at hN_mem
      rcases hN_mem with hIn | hAbs
      · rw [Finset.mem_image]
        exact ⟨(α, β), hIn, rfl⟩
      · unfold absentSlotsPairCore at hAbs
        rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union] at hAbs
        rcases hAbs with ((((hA1 | hA2) | hB1) | hB2) | hW)
        · -- aBridge a_1: (a_1, x.2) ⇒ β = x.2 ∈ cols(N).
          unfold aBridgeSlots at hA1
          rw [Finset.mem_image] at hA1
          obtain ⟨x, hx, h_eq⟩ := hA1
          rw [Finset.mem_image]
          exact ⟨x, hx, ((Prod.mk.injEq _ _ _ _).mp h_eq |>.2)⟩
        · unfold aBridgeSlots at hA2
          rw [Finset.mem_image] at hA2
          obtain ⟨x, hx, h_eq⟩ := hA2
          rw [Finset.mem_image]
          exact ⟨x, hx, ((Prod.mk.injEq _ _ _ _).mp h_eq |>.2)⟩
        · -- bBridge b_1: (x.1, b_1) ⇒ β = b_1, forbidden.
          exfalso
          unfold bBridgeSlots at hB1
          rw [Finset.mem_image] at hB1
          obtain ⟨x, _, h_eq⟩ := hB1
          exact hβ1 ((Prod.mk.injEq _ _ _ _).mp h_eq |>.2).symm
        · exfalso
          unfold bBridgeSlots at hB2
          rw [Finset.mem_image] at hB2
          obtain ⟨x, _, h_eq⟩ := hB2
          exact hβ2 ((Prod.mk.injEq _ _ _ _).mp h_eq |>.2).symm
        · unfold withinNSlots at hW
          rw [Finset.mem_image] at hW
          obtain ⟨p, hp, h_eq⟩ := hW
          rw [Finset.mem_filter, Finset.mem_product] at hp
          rw [Finset.mem_image]
          exact ⟨p.2, hp.1.2, ((Prod.mk.injEq _ _ _ _).mp h_eq |>.2)⟩
    have h_card_le : (cand.filter (fun N => (α, β) ∈ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N)).card
        ≤ (cand.filter (fun N => β ∈ N.image Prod.snd)).card := Finset.card_le_card h_subset
    calc (min (n_A - 2) (n_B - 2)) *
            (cand.filter (fun N => (α, β) ∈ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N)).card
        ≤ (n_B - 2) * (cand.filter (fun N => β ∈ N.image Prod.snd)).card := by
          apply Nat.mul_le_mul (Nat.min_le_right _ _) h_card_le
      _ = (k - 2) * cand.card :=
          candidate_col_double_count_pair k a_1 a_2 b_1 b_2 h_b β hβ1 hβ2

/-- **Codegree `E'` bound.** For nonempty `A`, the codegree effect is codegree-of-codegree scale:
`E[|∂_A c''|] ≤ (k−2)·#pairCand / min(n_A−2,n_B−2)`. (If `A` meets the 4 anchor slots the count is
`0`, since none lie in `N ∪ absentSlotsPairCore`; otherwise reduce to a single slot via
`slot_supp_count_le_pair`.) -/
lemma matchingCodegreeNoFactor_effect_le_E' {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (h_a : a_1 ≠ a_2) (h_b : b_1 ≠ b_2) (h_k_le_A : k ≤ n_A) (h_k_le_B : k ≤ n_B)
    (A : Finset (Fin n_A × Fin n_B)) (hA : A.Nonempty) (p : ENNReal) (hp : p ≤ 1) :
    ∫ g, |discreteDeriv (matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k) A g|
        ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
      ≤ ((k - 2 : ℕ) : ℝ) * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
          / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ) := by
  classical
  refine le_trans
    (matchingCodegreeNoFactor_effect_le_card a_1 a_2 b_1 b_2 k h_k_ge_2 h_a h_b A p hp) ?_
  set cnt := ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).filter
      (fun N => A ⊆ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N)).card with hcnt
  -- Helper: when k = 2, every candidate is ∅ and its core is ∅, so cnt = 0.
  by_cases hmin0 : min (n_A - 2) (n_B - 2) = 0
  · -- min = 0 ⟹ n_A = 2 or n_B = 2 ⟹ k = 2 (since 2 ≤ k ≤ n_A, n_B).
    have hk2 : k = 2 := by
      have h1 : min (n_A - 2) (n_B - 2) ≤ n_A - 2 := Nat.min_le_left _ _
      have h2 : min (n_A - 2) (n_B - 2) ≤ n_B - 2 := Nat.min_le_right _ _
      omega
    -- Then cnt = 0: any candidate N has N.card = 0 so N = ∅, core ∅ = ∅, A nonempty ⊄ ∅.
    have hcnt0 : cnt = 0 := by
      rw [hcnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro N hN h_sub
      have hN_card : N.card = k - 2 :=
        (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp hN |>.2.1
      have hN_empty : N = ∅ := by
        have : N.card = 0 := by rw [hN_card, hk2]
        exact Finset.card_eq_zero.mp this
      obtain ⟨s, hsA⟩ := hA
      have h_mem : s ∈ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N := h_sub hsA
      rw [hN_empty] at h_mem
      simp only [absentSlotsPairCore, aBridgeSlots, bBridgeSlots, withinNSlots,
        Finset.image_empty, Finset.empty_product, Finset.filter_empty,
        Finset.union_empty, Finset.notMem_empty] at h_mem
    rw [hcnt0]
    rw [hmin0]
    simp only [Nat.cast_zero, div_zero]
    exact le_rfl
  · -- min > 0: reduce to a single non-anchor slot.
    have hmin_pos : 0 < min (n_A - 2) (n_B - 2) := Nat.pos_of_ne_zero hmin0
    by_cases hanchor : (a_1, b_1) ∈ A ∨ (a_2, b_2) ∈ A ∨ (a_1, b_2) ∈ A ∨ (a_2, b_1) ∈ A
    · -- A meets an anchor ⇒ no candidate satisfies A ⊆ N ∪ core ⇒ cnt = 0.
      have hcnt0 : cnt = 0 := by
        rw [hcnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro N hN h_sub
        have h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N :=
          (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp hN |>.2.2
        have hN_sub : N ⊆ (Finset.univ.erase (a_1, b_1)).erase (a_2, b_2) :=
          (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp hN |>.1
        rcases hanchor with hA1 | hA2 | hA3 | hA4
        · -- (a_1,b_1): not in N (subset of erase) and not in core (a_1 forbidden).
          have h_mem := h_sub hA1
          rw [Finset.mem_union] at h_mem
          rcases h_mem with hIn | hAbs
          · exact (Finset.mem_erase.mp (Finset.mem_erase.mp (hN_sub hIn)).2).1 rfl
          · unfold absentSlotsPairCore at hAbs
            rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union] at hAbs
            rcases hAbs with ((((hx | hx) | hx) | hx) | hx)
            · unfold aBridgeSlots at hx; rw [Finset.mem_image] at hx
              obtain ⟨x, hx', he⟩ := hx
              exact h_cand.2.2.1 x hx' ((Prod.mk.injEq _ _ _ _).mp he).2
            · unfold aBridgeSlots at hx; rw [Finset.mem_image] at hx
              obtain ⟨_, _, he⟩ := hx
              exact h_a (((Prod.mk.injEq _ _ _ _).mp he).1).symm
            · unfold bBridgeSlots at hx; rw [Finset.mem_image] at hx
              obtain ⟨x, hx', he⟩ := hx
              exact h_cand.1 x hx' ((Prod.mk.injEq _ _ _ _).mp he).1
            · unfold bBridgeSlots at hx; rw [Finset.mem_image] at hx
              obtain ⟨_, _, he⟩ := hx
              exact h_b (((Prod.mk.injEq _ _ _ _).mp he).2).symm
            · unfold withinNSlots at hx; rw [Finset.mem_image] at hx
              obtain ⟨q, hq, he⟩ := hx
              rw [Finset.mem_filter, Finset.mem_product] at hq
              exact h_cand.1 q.1 hq.1.1 ((Prod.mk.injEq _ _ _ _).mp he).1
        · -- (a_2,b_2)
          have h_mem := h_sub hA2
          rw [Finset.mem_union] at h_mem
          rcases h_mem with hIn | hAbs
          · exact (Finset.mem_erase.mp (hN_sub hIn)).1 rfl
          · unfold absentSlotsPairCore at hAbs
            rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union] at hAbs
            rcases hAbs with ((((hx | hx) | hx) | hx) | hx)
            · unfold aBridgeSlots at hx; rw [Finset.mem_image] at hx
              obtain ⟨_, _, he⟩ := hx
              exact h_a ((Prod.mk.injEq _ _ _ _).mp he).1
            · unfold aBridgeSlots at hx; rw [Finset.mem_image] at hx
              obtain ⟨x, hx', he⟩ := hx
              exact h_cand.2.2.2.1 x hx' ((Prod.mk.injEq _ _ _ _).mp he).2
            · unfold bBridgeSlots at hx; rw [Finset.mem_image] at hx
              obtain ⟨_, _, he⟩ := hx
              exact h_b ((Prod.mk.injEq _ _ _ _).mp he).2
            · unfold bBridgeSlots at hx; rw [Finset.mem_image] at hx
              obtain ⟨x, hx', he⟩ := hx
              exact h_cand.2.1 x hx' ((Prod.mk.injEq _ _ _ _).mp he).1
            · unfold withinNSlots at hx; rw [Finset.mem_image] at hx
              obtain ⟨q, hq, he⟩ := hx
              rw [Finset.mem_filter, Finset.mem_product] at hq
              exact h_cand.2.2.2.1 q.2 hq.1.2 ((Prod.mk.injEq _ _ _ _).mp he).2
        · -- (a_1,b_2): not in N (a_1 forbidden) and not in core (a1b2_not_mem_N_absent).
          have h_mem := h_sub hA3
          rw [Finset.mem_union] at h_mem
          rcases h_mem with hIn | hAbs
          · exact h_cand.1 (a_1, b_2) hIn rfl
          · exact a1b2_not_mem_N_absent a_1 a_2 b_1 b_2 h_a h_b N h_cand hAbs
        · -- (a_2,b_1)
          have h_mem := h_sub hA4
          rw [Finset.mem_union] at h_mem
          rcases h_mem with hIn | hAbs
          · exact h_cand.2.1 (a_2, b_1) hIn rfl
          · exact a2b1_not_mem_N_absent a_1 a_2 b_1 b_2 h_a h_b N h_cand hAbs
      rw [hcnt0]
      have : (0:ℝ) ≤ ((k - 2 : ℕ) : ℝ) * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
          / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ) := by positivity
      simpa using this
    · -- A avoids all 4 anchors: pick s ∈ A, apply slot_supp_count_le_pair.
      push_neg at hanchor
      obtain ⟨hna1, hna2, hna3, hna4⟩ := hanchor
      obtain ⟨s, hsA⟩ := hA
      have hs1 : s ≠ (a_1, b_1) := fun h => hna1 (h ▸ hsA)
      have hs2 : s ≠ (a_2, b_2) := fun h => hna2 (h ▸ hsA)
      have hs3 : s ≠ (a_1, b_2) := fun h => hna3 (h ▸ hsA)
      have hs4 : s ≠ (a_2, b_1) := fun h => hna4 (h ▸ hsA)
      have h_le : cnt ≤ ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).filter
          (fun N => s ∈ N ∪ absentSlotsPairCore a_1 a_2 b_1 b_2 N)).card := by
        rw [hcnt]
        refine Finset.card_le_card ?_
        intro N hN
        rw [Finset.mem_filter] at hN ⊢
        exact ⟨hN.1, hN.2 hsA⟩
      have h_slot := slot_supp_count_le_pair a_1 a_2 b_1 b_2 k h_k_ge_2 h_a h_b
        h_k_le_A h_k_le_B s hs1 hs2 hs3 hs4
      have h_nat : min (n_A - 2) (n_B - 2) * cnt
          ≤ (k - 2) * (candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card :=
        le_trans (Nat.mul_le_mul_left _ h_le) h_slot
      have h_real : ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ) * (cnt : ℝ)
          ≤ ((k - 2 : ℕ) : ℝ) * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ) := by
        have := h_nat
        push_cast at this ⊢
        exact_mod_cast this
      rw [le_div_iff₀ (by exact_mod_cast hmin_pos :
        (0:ℝ) < ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ))]
      linarith [h_real]

/-- **Codegree P3 instantiation** (pair analogue of `c'_verbatim_concentration`): plug the
codegree mean/`E`/`E'` (P2 bounds) into the verbatim Kim–Vu axiom. Requires `3 ≤ k` so that
`E' = (k−2)#pairCand/min > 0`. -/
lemma c''_verbatim_concentration {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (k : ℕ) (h_k_ge_3 : 3 ≤ k)
    (h_a : a_1 ≠ a_2) (h_b : b_1 ≠ b_2) (h_k_le_A : k ≤ n_A) (h_k_le_B : k ≤ n_B)
    (p : ENNReal) (hp : p ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 1 < lam →
      ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
        {g | kimVuConst k *
              Real.sqrt (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                * (((k - 2 : ℕ) : ℝ) * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                    / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ)))
              * lam ^ k
            < |matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g
                - ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                    * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2)|}
        ≤ C * Real.exp (-lam + (k - 1 : ℝ)
            * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) := by
  classical
  have h_k_pos : 0 < k := by omega
  obtain ⟨C, hC_pos, hbound⟩ := kim_vu_concentration_verbatim k h_k_pos
  refine ⟨C, hC_pos, fun lam hlam => ?_⟩
  haveI : IsProbabilityMeasure
      ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure) :=
    inferInstance
  -- mean = ∫ f
  have h_mean : ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
          * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2)
      = ∫ g, matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g
          ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure) :=
    (matchingCodegreeNoFactor_integral a_1 a_2 b_1 b_2 k (by omega : 2 ≤ k) h_a h_b p hp).symm
  -- E-bound (∀ A)
  have h_E : ∀ A : Finset (Fin n_A × Fin n_B),
      ∫ g, |discreteDeriv (matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k) A g|
          ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
        ≤ ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ) :=
    fun A => matchingCodegreeNoFactor_effect_le_cardCand a_1 a_2 b_1 b_2 k (by omega) h_a h_b A p hp
  -- E'-bound (nonempty A)
  have h_E' : ∀ A : Finset (Fin n_A × Fin n_B), A.Nonempty →
      ∫ g, |discreteDeriv (matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k) A g|
          ∂((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure)
        ≤ ((k - 2 : ℕ) : ℝ) * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
            / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ) :=
    fun A hA => matchingCodegreeNoFactor_effect_le_E' a_1 a_2 b_1 b_2 k (by omega) h_a h_b
      h_k_le_A h_k_le_B A hA p hp
  -- 0 < E
  have h_Epos : (0:ℝ) < ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ) := by
    rw [candidatePairPartnerSet_card k (by omega : 2 ≤ k) h_k_le_A h_k_le_B a_1 a_2 b_1 b_2 h_a h_b]
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (Nat.choose_pos (by omega))
      (Nat.choose_pos (by omega))) (Nat.factorial_pos _)
  -- 0 < E'
  have h_E'pos : (0:ℝ) < ((k - 2 : ℕ) : ℝ)
      * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
      / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ) := by
    apply div_pos
    · exact mul_pos (by exact_mod_cast (by omega : 0 < k - 2)) h_Epos
    · exact_mod_cast (by omega : 0 < min (n_A - 2) (n_B - 2))
  exact hbound _ (matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k)
    (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
      * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2))
    ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
    (((k - 2 : ℕ) : ℝ) * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
      / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ))
    h_mean h_E h_E' h_Epos h_E'pos lam hlam

/-- **Codegree P3 regime: per-pair `≤ C/N³`.** At `λ=(k+2)·log N` the verbatim tail collapses to
`C·exp(−3 log N) = C/N³` (so the union over `N²` pairs gives `≤ C/N`); under the codegree
threshold hypothesis `h_thresh`, `P(|c''−μ''| ≥ ε·μ'') ≤ C·N⁻³`. Pair analogue of
`c'_concentration_le` (which used `λ=(k+1)log N` → `N⁻²`). -/
lemma c''_concentration_le {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (k : ℕ) (h_k_ge_3 : 3 ≤ k)
    (h_a : a_1 ≠ a_2) (h_b : b_1 ≠ b_2) (h_k_le_A : k ≤ n_A) (h_k_le_B : k ≤ n_B)
    (p : ENNReal) (hp : p ≤ 1) (ε : ℝ)
    (hN1 : 1 < (k + 2 : ℝ)
        * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ))
    (h_thresh : kimVuConst k *
          Real.sqrt (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
            * (((k - 2 : ℕ) : ℝ) * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ)))
          * ((k + 2 : ℝ) * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) ^ k
        < ε * (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
            * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2))) :
    ∃ C : ℝ, 0 < C ∧
      ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
        {g | ε * (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2))
              ≤ |matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g
                  - ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                      * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2)|}
        ≤ C * ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) ^ (-3 : ℤ) := by
  classical
  set N : ℝ := ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) with hN_def
  set lam : ℝ := (k + 2 : ℝ) * Real.log N with hlam_def
  set μm := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure
    with hμm_def
  haveI : IsProbabilityMeasure μm := inferInstance
  -- N > 0
  have hN_pos : 0 < N := by
    rw [hN_def]
    have : 0 < Fintype.card (Fin n_A × Fin n_B) := by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      have hA : 0 < n_A := by omega
      have hB : 0 < n_B := by omega
      exact Nat.mul_pos hA hB
    exact_mod_cast this
  -- The verbatim concentration bound.
  obtain ⟨C, hC_pos, hbound⟩ :=
    c''_verbatim_concentration a_1 a_2 b_1 b_2 k h_k_ge_3 h_a h_b h_k_le_A h_k_le_B p hp
  refine ⟨C, hC_pos, ?_⟩
  have hb := hbound lam hN1
  -- Event inclusion.
  have h_subset :
      {g | ε * (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2))
            ≤ |matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g
                - ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                    * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2)|}
      ⊆ {g | kimVuConst k *
              Real.sqrt (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                * (((k - 2 : ℕ) : ℝ) * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                    / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ)))
              * lam ^ k
            < |matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g
                - ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                    * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2)|} := by
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    exact lt_of_lt_of_le h_thresh hg
  -- Monotonicity of measure + the verbatim bound.
  have h_le := MeasureTheory.measureReal_mono (μ := μm) h_subset
  refine le_trans (le_trans h_le hb) ?_
  -- Tail simplification: exponent collapses to -3 log N.
  have h_exp : (-lam + (k - 1 : ℝ) * Real.log N) = (-3 : ℝ) * Real.log N := by
    rw [hlam_def]; ring
  rw [h_exp]
  -- exp(-3 log N) = N^(-3)
  have h_eq : Real.exp ((-3 : ℝ) * Real.log N) = N ^ (-3 : ℤ) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hN_pos, ← Real.rpow_intCast N (-3)]
    norm_num
  rw [h_eq]

/-- **Codegree union bound** (pair analogue of `c'_allEdges_concentration_aas`): a.a.s. EVERY
distinct-row-col pair has its codegree within `(1±ε)` of the mean. Per-pair `C·N⁻³` × `N²`
distinct-pair tuples (`= n_A²·n_B²`) gives `≤ C·N⁻¹ = C/N → 0`. (Shared-row/col pairs have
codegree `0`, excluded from the event.) This is the a.a.s. codegree side of P–S applicability. -/
lemma c''_allPairs_concentration_aas {n_A n_B : ℕ} (k : ℕ) (h_k_ge_3 : 3 ≤ k)
    (h_k_le_A : k ≤ n_A) (h_k_le_B : k ≤ n_B) (p : ENNReal) (hp : p ≤ 1) (ε : ℝ)
    (hN1 : 1 < (k + 2 : ℝ) * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ))
    (h_thresh : ∀ (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B), a_1 ≠ a_2 → b_1 ≠ b_2 →
        kimVuConst k *
          Real.sqrt (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
            * (((k - 2 : ℕ) : ℝ) * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ)))
          * ((k + 2 : ℝ) * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) ^ k
        < ε * (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
            * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2))) :
      ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure).real
        {g | ∃ (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B), a_1 ≠ a_2 ∧ b_1 ≠ b_2 ∧
              ε * (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                  * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2))
                ≤ |matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g
                    - ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                        * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2)|}
        ≤ kimVuVerbatimConst k (by omega)
            / ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) := by
  classical
  set N : ℝ := ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) with hN_def
  set μm := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B p hp).toMeasure
    with hμm_def
  haveI : IsProbabilityMeasure μm := inferInstance
  have h_k_pos : 0 < k := by omega
  set lam : ℝ := (k + 2 : ℝ) * Real.log N with hlam_def
  -- abbreviation for the per-pair mean `μ''`
  set μ'' : Fin n_A → Fin n_A → Fin n_B → Fin n_B → ℝ :=
    fun a_1 a_2 b_1 b_2 =>
      ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
        * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2) with hμ''_def
  -- N > 0
  have hN_pos : 0 < N := by
    rw [hN_def]
    have : 0 < Fintype.card (Fin n_A × Fin n_B) := by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      exact Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  -- Obtain the SHARED constant C once from the verbatim Kim–Vu axiom, using `.choose`
  -- so that the returned `C` is the canonical `kimVuVerbatimConst k` (shared with `c'`).
  set C : ℝ := kimVuVerbatimConst k (by omega) with hC_def
  have hCeq : (kim_vu_concentration_verbatim k h_k_pos).choose = C := rfl
  obtain ⟨hC_pos, hbound⟩ := (kim_vu_concentration_verbatim k h_k_pos).choose_spec
  rw [hCeq] at hC_pos hbound
  -- Per-pair bound with the SHARED `C`, mirroring `c''_verbatim_concentration` +
  -- `c''_concentration_le` but reusing the already-obtained `hbound`.
  have hpe : ∀ (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B), a_1 ≠ a_2 → b_1 ≠ b_2 →
      μm.real {g | ε * μ'' a_1 a_2 b_1 b_2
            ≤ |matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g - μ'' a_1 a_2 b_1 b_2|}
        ≤ C * N ^ (-3 : ℤ) := by
    intro a_1 a_2 b_1 b_2 h_a h_b
    -- mean = ∫ f  (mirror of `c''_verbatim_concentration`'s `h_mean`).
    have h_mean : μ'' a_1 a_2 b_1 b_2
        = ∫ g, matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g ∂μm :=
      (matchingCodegreeNoFactor_integral a_1 a_2 b_1 b_2 k (by omega : 2 ≤ k) h_a h_b p hp).symm
    -- E-bound (∀ A)
    have h_E : ∀ A : Finset (Fin n_A × Fin n_B),
        ∫ g, |discreteDeriv (matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k) A g| ∂μm
          ≤ ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ) :=
      fun A => matchingCodegreeNoFactor_effect_le_cardCand a_1 a_2 b_1 b_2 k (by omega) h_a h_b A p hp
    -- E'-bound (nonempty A)
    have h_E' : ∀ A : Finset (Fin n_A × Fin n_B), A.Nonempty →
        ∫ g, |discreteDeriv (matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k) A g| ∂μm
          ≤ ((k - 2 : ℕ) : ℝ) * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
              / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ) :=
      fun A hA => matchingCodegreeNoFactor_effect_le_E' a_1 a_2 b_1 b_2 k (by omega) h_a h_b
        h_k_le_A h_k_le_B A hA p hp
    -- 0 < E
    have h_Epos : (0:ℝ) < ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ) := by
      rw [candidatePairPartnerSet_card k (by omega : 2 ≤ k) h_k_le_A h_k_le_B a_1 a_2 b_1 b_2 h_a h_b]
      exact_mod_cast Nat.mul_pos (Nat.mul_pos (Nat.choose_pos (by omega))
        (Nat.choose_pos (by omega))) (Nat.factorial_pos _)
    -- 0 < E'
    have h_E'pos : (0:ℝ) < ((k - 2 : ℕ) : ℝ)
        * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
        / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ) := by
      apply div_pos
      · exact mul_pos (by exact_mod_cast (by omega : 0 < k - 2)) h_Epos
      · exact_mod_cast (by omega : 0 < min (n_A - 2) (n_B - 2))
    have hb := hbound (ι := Fin n_A × Fin n_B) μm
      (matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k) (μ'' a_1 a_2 b_1 b_2)
      ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
      (((k - 2 : ℕ) : ℝ) * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
        / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ))
      h_mean h_E h_E' h_Epos h_E'pos lam hN1
    -- Event inclusion via `h_thresh` (mirror of `c''_concentration_le`).
    have h_subset :
        {g | ε * μ'' a_1 a_2 b_1 b_2
              ≤ |matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g - μ'' a_1 a_2 b_1 b_2|}
        ⊆ {g | kimVuConst k *
                Real.sqrt (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                  * (((k - 2 : ℕ) : ℝ) * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                      / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ)))
                * lam ^ k
              < |matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g - μ'' a_1 a_2 b_1 b_2|} := by
      intro g hg
      simp only [Set.mem_setOf_eq] at hg ⊢
      exact lt_of_lt_of_le (h_thresh a_1 a_2 b_1 b_2 h_a h_b) hg
    have h_le := MeasureTheory.measureReal_mono (μ := μm) h_subset
    refine le_trans (le_trans h_le hb) ?_
    -- Tail simplification: exponent collapses to -3 log N.
    have h_exp : (-lam + (k - 1 : ℝ) * Real.log N) = (-3 : ℝ) * Real.log N := by
      rw [hlam_def]; ring
    rw [h_exp]
    have h_eq : Real.exp ((-3 : ℝ) * Real.log N) = N ^ (-3 : ℤ) := by
      rw [mul_comm, Real.exp_mul, Real.exp_log hN_pos, ← Real.rpow_intCast N (-3)]
      norm_num
    rw [h_eq]
  -- Rewrite the bad set as a `Fintype` indexed union over distinct-row-col 4-tuples.
  have h_set_eq :
      {g | ∃ (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B), a_1 ≠ a_2 ∧ b_1 ≠ b_2 ∧
            ε * μ'' a_1 a_2 b_1 b_2
              ≤ |matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g - μ'' a_1 a_2 b_1 b_2|}
      = ⋃ (t : Fin n_A × Fin n_A × Fin n_B × Fin n_B),
          {g | t.1 ≠ t.2.1 ∧ t.2.2.1 ≠ t.2.2.2 ∧
            ε * μ'' t.1 t.2.1 t.2.2.1 t.2.2.2
              ≤ |matchingCodegreeNoFactor t.1 t.2.1 t.2.2.1 t.2.2.2 k g
                  - μ'' t.1 t.2.1 t.2.2.1 t.2.2.2|} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨a_1, a_2, b_1, b_2, h⟩
      exact ⟨(a_1, a_2, b_1, b_2), h⟩
    · rintro ⟨t, h⟩
      exact ⟨t.1, t.2.1, t.2.2.1, t.2.2.2, h⟩
  rw [h_set_eq]
  -- Union bound.
  refine le_trans (MeasureTheory.measureReal_iUnion_fintype_le (μ := μm) _) ?_
  -- Per-tuple bound `≤ C * N^(-3)` for ALL tuples (distinct: `hpe`; non-distinct: empty set).
  have h_per_tuple : ∀ t : Fin n_A × Fin n_A × Fin n_B × Fin n_B,
      μm.real {g | t.1 ≠ t.2.1 ∧ t.2.2.1 ≠ t.2.2.2 ∧
            ε * μ'' t.1 t.2.1 t.2.2.1 t.2.2.2
              ≤ |matchingCodegreeNoFactor t.1 t.2.1 t.2.2.1 t.2.2.2 k g
                  - μ'' t.1 t.2.1 t.2.2.1 t.2.2.2|}
        ≤ C * N ^ (-3 : ℤ) := by
    intro t
    by_cases h_dist : t.1 ≠ t.2.1 ∧ t.2.2.1 ≠ t.2.2.2
    · -- distinct: the set is exactly the per-pair event, so apply `hpe`.
      have h_eq_set :
          {g | t.1 ≠ t.2.1 ∧ t.2.2.1 ≠ t.2.2.2 ∧
                ε * μ'' t.1 t.2.1 t.2.2.1 t.2.2.2
                  ≤ |matchingCodegreeNoFactor t.1 t.2.1 t.2.2.1 t.2.2.2 k g
                      - μ'' t.1 t.2.1 t.2.2.1 t.2.2.2|}
          = {g | ε * μ'' t.1 t.2.1 t.2.2.1 t.2.2.2
                  ≤ |matchingCodegreeNoFactor t.1 t.2.1 t.2.2.1 t.2.2.2 k g
                      - μ'' t.1 t.2.1 t.2.2.1 t.2.2.2|} := by
        ext g
        simp only [Set.mem_setOf_eq]
        exact ⟨fun h => h.2.2, fun h => ⟨h_dist.1, h_dist.2, h⟩⟩
      rw [h_eq_set]
      exact hpe t.1 t.2.1 t.2.2.1 t.2.2.2 h_dist.1 h_dist.2
    · -- non-distinct: the membership conjunction is false, so the set is empty.
      have h_empty :
          {g | t.1 ≠ t.2.1 ∧ t.2.2.1 ≠ t.2.2.2 ∧
                ε * μ'' t.1 t.2.1 t.2.2.1 t.2.2.2
                  ≤ |matchingCodegreeNoFactor t.1 t.2.1 t.2.2.1 t.2.2.2 k g
                      - μ'' t.1 t.2.1 t.2.2.1 t.2.2.2|}
          = (∅ : Set (Fin n_A × Fin n_B → Bool)) := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => h_dist ⟨h.1, h.2.1⟩
      rw [h_empty, MeasureTheory.measureReal_empty]
      positivity
  refine le_trans (Finset.sum_le_sum (fun t _ => h_per_tuple t)) ?_
  -- Sum of the constant over `N²` tuples.
  rw [Finset.sum_const, nsmul_eq_mul]
  -- `card (Fin n_A × Fin n_A × Fin n_B × Fin n_B) = n_A*n_A*n_B*n_B`.
  have h_card : (Finset.univ : Finset (Fin n_A × Fin n_A × Fin n_B × Fin n_B)).card
      = n_A * n_A * (n_B * n_B) := by
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    ring
  rw [h_card]
  -- `(n_A * n_A * (n_B * n_B) : ℝ) = N^2`, so `N^2 * (C * N^(-3)) = C / N`.
  have hcast : ((n_A * n_A * (n_B * n_B) : ℕ) : ℝ) = N ^ 2 := by
    rw [hN_def, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  rw [hcast]
  have hNne : N ≠ 0 := ne_of_gt hN_pos
  apply le_of_eq
  rw [zpow_neg]
  field_simp

/-- **Per-candidate bound:** for a candidate erase-partner `N`, the realized pair indicator
`matchingPairIndicator` is bounded above by the core codegree monomial `∏ i, monoH N (core) i (g i)`.
The pair indicator factors (via `matchingPairIndicator_eq_product_form`) as the product over
`presentSlotsPair`/`absentSlotsPair`; peeling the two anchor edges (each present-factor `≤ 1`) and
the two anchor-anchor bridges (each absent-factor `≤ 1`) leaves exactly the core monomial, whose
factors are all in `{0,1}` (hence `≥ 0`). -/
private lemma matchingPairIndicator_le_core_monoH {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B)
    (h_a : a_1 ≠ a_2) (h_b : b_1 ≠ b_2)
    (N : Finset (Fin n_A × Fin n_B))
    (hN : N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2)
    (g : Fin n_A × Fin n_B → Bool) :
    matchingPairIndicator a_1 a_2 b_1 b_2 N g
      ≤ ∏ i, monoH N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) i (g i) := by
  classical
  have h_cand : CandidatePairPartner a_1 a_2 b_1 b_2 N :=
    (mem_candidatePairPartnerSet_iff k a_1 a_2 b_1 b_2 N).mp hN |>.2.2
  obtain ⟨h_e1_notMem, h_e2_notMem⟩ :=
    e1_e2_notMem_of_candidatePair k a_1 a_2 b_1 b_2 N hN
  -- The core monomial equals the product of edge-indicators over `N` times
  -- `(1 - edgeIndicator)` over `absentSlotsPairCore` (via `prod_monoH`).
  have h_disj : Disjoint N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) :=
    disjoint_N_absentSlotsPairCore a_1 a_2 b_1 b_2 h_a h_b N h_cand
  have h_core_eq :
      (∏ i, monoH N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) i (g i))
        = (∏ ab ∈ N, DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g) *
          (∏ ab ∈ absentSlotsPairCore a_1 a_2 b_1 b_2 N,
              (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g)) := by
    rw [prod_monoH N (absentSlotsPairCore a_1 a_2 b_1 b_2 N) h_disj g]
    have hN_re : (∏ i ∈ N, (if g i = true then (1 : ℝ) else 0))
        = ∏ ab ∈ N, DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g :=
      Finset.prod_congr rfl (fun ab _ => if_eq_edgeIndicator ab g)
    have hT_re : (∏ i ∈ absentSlotsPairCore a_1 a_2 b_1 b_2 N,
            (1 - if g i = true then (1 : ℝ) else 0))
        = ∏ ab ∈ absentSlotsPairCore a_1 a_2 b_1 b_2 N,
            (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g) :=
      Finset.prod_congr rfl (fun ab _ => by rw [if_eq_edgeIndicator ab g])
    rw [hN_re, hT_re]
  -- The pair indicator equals the product over presentSlotsPair/absentSlotsPair.
  rw [matchingPairIndicator_eq_product_form a_1 a_2 b_1 b_2 h_a h_b N h_cand
    h_e1_notMem h_e2_notMem g]
  -- Peel the two anchor edges off presentSlotsPair and the two anchor-anchor bridges
  -- off absentSlotsPair, exposing the core monomial.
  have h_e_distinct : (a_1, b_1) ≠ (a_2, b_2) := fun h =>
    h_a (by simpa using congrArg Prod.fst h)
  have h_e1_notMem_step : (a_1, b_1) ∉ insert (a_2, b_2) N := by
    rw [Finset.mem_insert]; push_neg; exact ⟨h_e_distinct, h_e1_notMem⟩
  have h_pres_split :
      (∏ ab ∈ presentSlotsPair a_1 a_2 b_1 b_2 N,
          DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g)
        = DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a_1 b_1 g *
          (DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a_2 b_2 g *
            (∏ ab ∈ N, DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g)) := by
    unfold presentSlotsPair
    rw [Finset.prod_insert h_e1_notMem_step, Finset.prod_insert h_e2_notMem]
  have h_a1b2_not_core : (a_1, b_2) ∉ absentSlotsPairCore a_1 a_2 b_1 b_2 N :=
    a1b2_not_mem_N_absent a_1 a_2 b_1 b_2 h_a h_b N h_cand
  have h_a2b1_not_core : (a_2, b_1) ∉ absentSlotsPairCore a_1 a_2 b_1 b_2 N :=
    a2b1_not_mem_N_absent a_1 a_2 b_1 b_2 h_a h_b N h_cand
  have h_a1b2_ne_a2b1 : (a_1, b_2) ≠ (a_2, b_1) := a1b2_ne_a2b1 a_1 a_2 b_1 b_2 h_a
  have h_a1b2_not_step : (a_1, b_2) ∉
      insert (a_2, b_1) (absentSlotsPairCore a_1 a_2 b_1 b_2 N) := by
    rw [Finset.mem_insert]; push_neg; exact ⟨h_a1b2_ne_a2b1, h_a1b2_not_core⟩
  have h_abs_split :
      (∏ ab ∈ absentSlotsPair a_1 a_2 b_1 b_2 N,
          (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g))
        = (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a_1 b_2 g) *
          ((1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator a_2 b_1 g) *
            (∏ ab ∈ absentSlotsPairCore a_1 a_2 b_1 b_2 N,
                (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g))) := by
    rw [absentSlotsPair_eq_insert_core, Finset.prod_insert h_a1b2_not_step,
      Finset.prod_insert h_a2b1_not_core]
  rw [h_pres_split, h_abs_split, h_core_eq]
  -- Set the four anchor factors and the two core products as abbreviations.
  set Pcore : ℝ := ∏ ab ∈ N, DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g
    with hPcore
  set Acore : ℝ := ∏ ab ∈ absentSlotsPairCore a_1 a_2 b_1 b_2 N,
      (1 - DaveyThesis2024.BipartiteRandomGraph.edgeIndicator ab.1 ab.2 g) with hAcore
  -- Each anchor factor is in `{0,1}` and the core products are nonnegative.
  have h_e1_bounds := DaveyThesis2024.BipartiteRandomGraph.edgeIndicator_indicator a_1 b_1 g
  have h_e2_bounds := DaveyThesis2024.BipartiteRandomGraph.edgeIndicator_indicator a_2 b_2 g
  have h_b1_bounds := DaveyThesis2024.BipartiteRandomGraph.edgeIndicator_indicator a_1 b_2 g
  have h_b2_bounds := DaveyThesis2024.BipartiteRandomGraph.edgeIndicator_indicator a_2 b_1 g
  have hPcore_nonneg : 0 ≤ Pcore := by
    rw [hPcore]; exact Finset.prod_nonneg (fun ab _ => by
      rcases DaveyThesis2024.BipartiteRandomGraph.edgeIndicator_indicator ab.1 ab.2 g with h | h
        <;> rw [h] <;> norm_num)
  have hAcore_nonneg : 0 ≤ Acore := by
    rw [hAcore]; exact Finset.prod_nonneg (fun ab _ => by
      rcases DaveyThesis2024.BipartiteRandomGraph.edgeIndicator_indicator ab.1 ab.2 g with h | h
        <;> rw [h] <;> norm_num)
  -- Now bound: the four anchor factors are each `≤ 1` (and `≥ 0`), core product `≥ 0`.
  have hPA_nonneg : 0 ≤ Pcore * Acore := mul_nonneg hPcore_nonneg hAcore_nonneg
  rcases h_e1_bounds with he1 | he1 <;> rcases h_e2_bounds with he2 | he2 <;>
    rcases h_b1_bounds with hb1 | hb1 <;> rcases h_b2_bounds with hb2 | hb2 <;>
    rw [he1, he2, hb1, hb2] <;> nlinarith [hPcore_nonneg, hAcore_nonneg, hPA_nonneg]

/-- **Realized-codegree bridge:** the `H_k` codegree of a distinct-row-col pair is `≤ c''_core`.
`C(e₁,e₂,g) = #{induced k-matchings ⊇ {e₁,e₂}} ≤ matchingCodegreeNoFactor a₁ a₂ b₁ b₂ k g`.
(A realized induced matching `{e₁,e₂}∪N` forces `N` present + N-bridges absent + `e₁,e₂` present
+ anchor-anchor absent — strictly more than `c''_core` counts — so `≤`.) Combined with the
codegree concentration, this gives the P–S codegree hypothesis a.a.s. -/
lemma codegree_count_le_matchingCodegreeNoFactor {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (h_a : a_1 ≠ a_2) (h_b : b_1 ≠ b_2) (g : Fin n_A × Fin n_B → Bool) :
    (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
          (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
          Finset.univ Finset.univ k).filter
        (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card : ℝ)
      ≤ matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g := by
  classical
  set cnt : ℝ := (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
        (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
        Finset.univ Finset.univ k).filter
      (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card : ℝ) with hcnt
  -- The four anchor indicator factors.
  set P4 : ℝ := (if g (a_1, b_1) = true then (1 : ℝ) else 0) *
      (if g (a_2, b_2) = true then (1 : ℝ) else 0) *
      (if g (a_1, b_2) = true then (0 : ℝ) else 1) *
      (if g (a_2, b_1) = true then (0 : ℝ) else 1) with hP4
  -- The count identity: `cnt * P4 = ∑ matchingPairIndicator`.
  have h_count :
      cnt * P4
        = ∑ N ∈ (((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a_1, b_1)).erase
                (a_2, b_2)).powersetCard (k - 2),
            matchingPairIndicator a_1 a_2 b_1 b_2 N g := by
    have h := count_pair_mul_indicator_eq_sum_matchingPairIndicator k h_k_ge_2
      a_1 a_2 b_1 b_2 h_a h_b g
    rw [hcnt, hP4, ← h]; ring
  -- Step A: ∑ over powersetCard matchingPairIndicator ≤ matchingCodegreeNoFactor.
  have h_stepA :
      (∑ N ∈ (((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a_1, b_1)).erase
                (a_2, b_2)).powersetCard (k - 2),
            matchingPairIndicator a_1 a_2 b_1 b_2 N g)
        ≤ matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g := by
    -- Restrict the sum to candidates (non-candidate terms vanish).
    have h_restrict :
        (∑ N ∈ (((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a_1, b_1)).erase
                  (a_2, b_2)).powersetCard (k - 2),
              matchingPairIndicator a_1 a_2 b_1 b_2 N g)
          = ∑ N ∈ candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2,
              matchingPairIndicator a_1 a_2 b_1 b_2 N g := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro N hN
        rw [mem_candidatePairPartnerSet_iff] at hN
        rw [Finset.mem_powersetCard]
        exact ⟨hN.1, hN.2.1⟩
      · intro N hN h_not
        exact matchingPairIndicator_eq_zero_of_not_candidate k h_k_ge_2 a_1 a_2 b_1 b_2 N hN
          h_not g
    rw [h_restrict, matchingCodegreeNoFactor]
    exact Finset.sum_le_sum (fun N hN =>
      matchingPairIndicator_le_core_monoH k a_1 a_2 b_1 b_2 h_a h_b N hN g)
  -- Step B: cnt ≤ ∑ matchingPairIndicator (= cnt * P4).
  -- P4 is a product of four `{0,1}` factors, so P4 ∈ {0,1}.
  have hP4_cases : P4 = 0 ∨ P4 = 1 := by
    rw [hP4]
    rcases (by by_cases h : g (a_1, b_1) = true <;> simp [h] :
        (if g (a_1, b_1) = true then (1 : ℝ) else 0) = 0 ∨
        (if g (a_1, b_1) = true then (1 : ℝ) else 0) = 1) with h1 | h1 <;>
      rcases (by by_cases h : g (a_2, b_2) = true <;> simp [h] :
        (if g (a_2, b_2) = true then (1 : ℝ) else 0) = 0 ∨
        (if g (a_2, b_2) = true then (1 : ℝ) else 0) = 1) with h2 | h2 <;>
      rcases (by by_cases h : g (a_1, b_2) = true <;> simp [h] :
        (if g (a_1, b_2) = true then (0 : ℝ) else 1) = 0 ∨
        (if g (a_1, b_2) = true then (0 : ℝ) else 1) = 1) with h3 | h3 <;>
      rcases (by by_cases h : g (a_2, b_1) = true <;> simp [h] :
        (if g (a_2, b_1) = true then (0 : ℝ) else 1) = 0 ∨
        (if g (a_2, b_1) = true then (0 : ℝ) else 1) = 1) with h4 | h4 <;>
      rw [h1, h2, h3, h4] <;> norm_num
  rcases hP4_cases with hP4_zero | hP4_one
  · -- P4 = 0: some anchor condition fails, so the filter is empty and cnt = 0.
    have h_cnt_zero : cnt = 0 := by
      rw [hcnt, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro M hM ⟨h_e1_in, h_e2_in⟩
      -- Extract structure of M.
      have h_iff := (mem_inducedKMatchings_iff
        (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
        Finset.univ Finset.univ k M).mp hM
      obtain ⟨h_sub, _, h_indMatch⟩ := h_iff
      -- (a_1,b_1) and (a_2,b_2) are edges ⟹ g(a_1,b_1)=g(a_2,b_2)=true.
      have h_g_e1 : g (a_1, b_1) = true := by
        have h_cross := h_sub h_e1_in
        have := ((DaveyThesis2024.SecRandomBipartite.mem_crossBlockPairs _ _ _
          (a_1, b_1)).mp h_cross).2.2
        exact (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr
          g a_1 b_1).mp this
      have h_g_e2 : g (a_2, b_2) = true := by
        have h_cross := h_sub h_e2_in
        have := ((DaveyThesis2024.SecRandomBipartite.mem_crossBlockPairs _ _ _
          (a_2, b_2)).mp h_cross).2.2
        exact (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr
          g a_2 b_2).mp this
      -- (a_1,b_1) ≠ (a_2,b_2) since a_1 ≠ a_2.
      have h_e_ne : ((a_1, b_1) : Fin n_A × Fin n_B) ≠ (a_2, b_2) := fun h =>
        h_a (by simpa using congrArg Prod.fst h)
      -- The induced-matching property forbids the two bridge edges.
      have h_bridges := h_indMatch (a_1, b_1) h_e1_in (a_2, b_2) h_e2_in h_e_ne
      have h_not_adj_a1b2 : ¬ (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g).Adj
          (Sum.inl a_1) (Sum.inr b_2) := h_bridges.2.2.1
      have h_not_adj_a2b1 : ¬ (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g).Adj
          (Sum.inl a_2) (Sum.inr b_1) := h_bridges.2.2.2
      have h_g_a1b2 : g (a_1, b_2) ≠ true := fun h => h_not_adj_a1b2
        ((DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr g a_1 b_2).mpr h)
      have h_g_a2b1 : g (a_2, b_1) ≠ true := fun h => h_not_adj_a2b1
        ((DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph_adj_inl_inr g a_2 b_1).mpr h)
      -- All four anchor conditions hold ⟹ P4 = 1, contradicting P4 = 0.
      rw [hP4, if_pos h_g_e1, if_pos h_g_e2, if_neg h_g_a1b2, if_neg h_g_a2b1] at hP4_zero
      norm_num at hP4_zero
    rw [h_cnt_zero]
    -- 0 ≤ matchingCodegreeNoFactor (sum of nonneg core monomials).
    rw [matchingCodegreeNoFactor]
    refine Finset.sum_nonneg (fun N _ => ?_)
    exact Finset.prod_nonneg (fun i _ => by
      unfold monoH
      by_cases hS : i ∈ N
      · rw [if_pos hS]; by_cases hgi : g i = true <;> simp [hgi]
      · rw [if_neg hS]
        by_cases hT : i ∈ absentSlotsPairCore a_1 a_2 b_1 b_2 N
        · rw [if_pos hT]; by_cases hgi : g i = true <;> simp [hgi]
        · rw [if_neg hT]; norm_num)
  · -- P4 = 1: cnt = cnt * P4 = ∑ matchingPairIndicator ≤ matchingCodegreeNoFactor.
    calc cnt = cnt * P4 := by rw [hP4_one, mul_one]
      _ = ∑ N ∈ (((Finset.univ : Finset (Fin n_A × Fin n_B)).erase (a_1, b_1)).erase
                (a_2, b_2)).powersetCard (k - 2),
            matchingPairIndicator a_1 a_2 b_1 b_2 N g := h_count
      _ ≤ matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g := h_stepA

/-- **I1-reg: the regularity P–S hypothesis from the degree good-event.** If every slot's `c'`
is within `δ·mu` of `mu` (the good event of `c'_allEdges_concentration_aas`), then every PRESENT
edge's `H_k`-degree is within `δ·mu` of `mu` — i.e. `H_k` is `(1±δ)`-regular over the present
edges. Immediate from the degree bridge `matchingCountNoFactor_eq_degree_of_present`. -/
lemma Hk_degree_regular_of_good {n_A n_B : ℕ} (k : ℕ) (h_k_pos : 0 < k)
    (g : Fin n_A × Fin n_B → Bool) (δ mu : ℝ)
    (h_good : ∀ (a : Fin n_A) (b : Fin n_B),
      |matchingCountNoFactor a b k g - mu| ≤ δ * mu) :
    ∀ (a : Fin n_A) (b : Fin n_B), g (a, b) = true →
      |(((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
            (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
            Finset.univ Finset.univ k).filter (fun M => (a, b) ∈ M)).card : ℝ) - mu|
        ≤ δ * mu := by
  intro a b hab
  rw [← matchingCountNoFactor_eq_degree_of_present a b k h_k_pos g hab]
  exact h_good a b

/-- **I1-codeg: the codegree P–S hypothesis from the codegree good-event.** If `c''_core` is
within `δ'·mu''` of its mean `mu''` (the good event of `c''_allPairs_concentration_aas`) and
`(1+δ')·mu'' ≤ bound` (the regime arithmetic `(1+δ')μ'' ≤ δD`, valid for large `n` since
`μ''/μ → 0`), then the realised `H_k` codegree of the distinct pair is `≤ bound`. Via the codegree
bridge `C ≤ c''_core ≤ (1+δ')μ'' ≤ bound`. -/
lemma Hk_codegree_bounded_of_good {n_A n_B : ℕ}
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (h_a : a_1 ≠ a_2) (h_b : b_1 ≠ b_2) (g : Fin n_A × Fin n_B → Bool)
    (δ' mu'' bound : ℝ)
    (h_good : |matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g - mu''| ≤ δ' * mu'')
    (h_arith : (1 + δ') * mu'' ≤ bound) :
    (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
          (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
          Finset.univ Finset.univ k).filter
        (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card : ℝ)
      ≤ bound := by
  have h_abs := abs_le.mp h_good
  calc (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
            (DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph g)
            Finset.univ Finset.univ k).filter
          (fun M => (a_1, b_1) ∈ M ∧ (a_2, b_2) ∈ M)).card : ℝ)
      ≤ matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k g :=
        codegree_count_le_matchingCodegreeNoFactor a_1 a_2 b_1 b_2 k h_k_ge_2 h_a h_b g
    _ ≤ (1 + δ') * mu'' := by nlinarith [h_abs.2]
    _ ≤ bound := h_arith

end KimVuIntegration

/-! ## I3c: regime discharge — sub-lemmas A (cardinality upper bounds)

These bound the candidate-partner sets purely combinatorially (no asymptotics):
`|candidatePartnerSet| ≤ (n_A·n_B)^(k-1)` and `|candidatePairPartnerSet| ≤ (n_A·n_B)^(k-2)`,
via `card (filter …) ≤ card (powersetCard …) = C(card, k-1) ≤ card^(k-1) = (n_A·n_B)^(k-1)`. -/

/-- **A (c′).** The candidate-partner set has at most `(n_A·n_B)^(k-1)` members. -/
lemma candidatePartnerSet_card_le {n_A n_B : ℕ} (k : ℕ)
    (a : Fin n_A) (b : Fin n_B) :
    (candidatePartnerSet n_A n_B k a b).card ≤ (n_A * n_B) ^ (k - 1) := by
  classical
  unfold candidatePartnerSet
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_powersetCard]
  refine le_trans (Nat.choose_le_pow _ _) ?_
  refine Nat.pow_le_pow_left ?_ _
  refine le_trans (Finset.card_erase_le) ?_
  rw [Finset.card_univ]
  simp [Fintype.card_prod, Fintype.card_fin]

/-- **A (c″).** The candidate-pair-partner set has at most `(n_A·n_B)^(k-2)` members. -/
lemma candidatePairPartnerSet_card_le {n_A n_B : ℕ} (k : ℕ)
    (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B) :
    (candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card ≤ (n_A * n_B) ^ (k - 2) := by
  classical
  unfold candidatePairPartnerSet
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_powersetCard]
  refine le_trans (Nat.choose_le_pow _ _) ?_
  refine Nat.pow_le_pow_left ?_ _
  refine le_trans (Finset.card_erase_le) ?_
  refine le_trans (Finset.card_erase_le) ?_
  rw [Finset.card_univ]
  simp [Fintype.card_prod, Fintype.card_fin]

/-! ## I3c: regime discharge — sub-lemma B (mean lower bound)

`μc = expectedDegreeFormula = C(n_A-1,k-1)·C(n_B-1,k-1)·(k-1)!·p^(k-1)·(1-p)^(k(k-1))`.
Using `Nat.pow_le_choose : ((n+1-r)^r)/r! ≤ n.choose r` on each binomial gives the positive-constant
lower bound `c_k·B_A·B_B ≤ μc` with
`c_k := p^(k-1)·(1-p)^(k(k-1))/(k-1)!` and `B_A := ((n_A-1)+1-(k-1))^(k-1)`, `B_B` analogously. -/

/-- The positive constant in the mean lower bound (sub-lemma B). -/
noncomputable def meanLowerConst (k : ℕ) (p : ℝ) : ℝ :=
  p ^ (k - 1) * (1 - p) ^ (k * (k - 1)) / (Nat.factorial (k - 1) : ℝ)

lemma meanLowerConst_pos {k : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 < meanLowerConst k p := by
  unfold meanLowerConst
  have h1 : 0 < p ^ (k - 1) := pow_pos hp _
  have h2 : 0 < (1 - p) ^ (k * (k - 1)) := pow_pos (by linarith) _
  have h3 : 0 < (Nat.factorial (k - 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  positivity

/-- **B.** Positive-constant lower bound on the expected degree (mean). -/
lemma expectedDegreeFormula_ge {n_A n_B k : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    meanLowerConst k p
        * (((((n_A - 1) + 1 - (k - 1) : ℕ) : ℝ) ^ (k - 1))
            * ((((n_B - 1) + 1 - (k - 1) : ℕ) : ℝ) ^ (k - 1)))
      ≤ expectedDegreeFormula n_A n_B k p := by
  unfold expectedDegreeFormula meanLowerConst
  set r := k - 1 with hr
  have hfac : 0 < (Nat.factorial r : ℝ) := by exact_mod_cast Nat.factorial_pos _
  -- lower bounds on each choose
  have hA : ((((n_A - 1) + 1 - r : ℕ) : ℝ) ^ r) / (Nat.factorial r : ℝ)
      ≤ ((Nat.choose (n_A - 1) r : ℝ)) := by
    have := Nat.pow_le_choose (α := ℝ) r (n_A - 1)
    simpa using this
  have hB : ((((n_B - 1) + 1 - r : ℕ) : ℝ) ^ r) / (Nat.factorial r : ℝ)
      ≤ ((Nat.choose (n_B - 1) r : ℝ)) := by
    have := Nat.pow_le_choose (α := ℝ) r (n_B - 1)
    simpa using this
  have hbaseA : (0 : ℝ) ≤ ((((n_A - 1) + 1 - r : ℕ) : ℝ) ^ r) := by positivity
  have hbaseB : (0 : ℝ) ≤ ((((n_B - 1) + 1 - r : ℕ) : ℝ) ^ r) := by positivity
  have hpk : (0 : ℝ) ≤ p ^ r := pow_nonneg hp _
  have h1mp : (0 : ℝ) ≤ (1 - p) ^ (k * r) := pow_nonneg (by linarith) _
  have hcA : (0 : ℝ) ≤ (Nat.choose (n_A - 1) r : ℝ) := Nat.cast_nonneg _
  -- combine: lower-bound each choose, multiply by the nonneg remaining factors
  have key :
      (((((n_A - 1) + 1 - r : ℕ) : ℝ) ^ r) / (Nat.factorial r : ℝ))
        * (((((n_B - 1) + 1 - r : ℕ) : ℝ) ^ r) / (Nat.factorial r : ℝ))
        * (Nat.factorial r : ℝ) * p ^ r * (1 - p) ^ (k * r)
      ≤ (Nat.choose (n_A - 1) r : ℝ) * (Nat.choose (n_B - 1) r : ℝ)
          * (Nat.factorial r : ℝ) * p ^ r * (1 - p) ^ (k * r) := by
    have hmul : (((((n_A - 1) + 1 - r : ℕ) : ℝ) ^ r) / (Nat.factorial r : ℝ))
          * (((((n_B - 1) + 1 - r : ℕ) : ℝ) ^ r) / (Nat.factorial r : ℝ))
        ≤ (Nat.choose (n_A - 1) r : ℝ) * (Nat.choose (n_B - 1) r : ℝ) := by
      apply mul_le_mul hA hB (by positivity) hcA
    have hrest : (0 : ℝ) ≤ (Nat.factorial r : ℝ) * p ^ r * (1 - p) ^ (k * r) := by positivity
    nlinarith [hmul, hrest, mul_le_mul_of_nonneg_right hmul hrest]
  -- rewrite the LHS constant form to match `key`'s LHS
  have hlhs :
      p ^ r * (1 - p) ^ (k * r) / (Nat.factorial r : ℝ)
        * (((((n_A - 1) + 1 - r : ℕ) : ℝ) ^ r) * ((((n_B - 1) + 1 - r : ℕ) : ℝ) ^ r))
      = (((((n_A - 1) + 1 - r : ℕ) : ℝ) ^ r) / (Nat.factorial r : ℝ))
          * (((((n_B - 1) + 1 - r : ℕ) : ℝ) ^ r) / (Nat.factorial r : ℝ))
          * (Nat.factorial r : ℝ) * p ^ r * (1 - p) ^ (k * r) := by
    field_simp
  rw [hlhs]
  exact key

/-! ## I3c: regime discharge — sub-lemma C-core (the analytic `(log m)^k = o(√m)` fact)

The single piece of real analysis behind the bounded-aspect discharge. For any `ε' > 0`
and `k`, eventually in `m : ℕ` we have `(log m)^k ≤ ε' · √m`. Proved from
`isLittleO_log_rpow_atTop (r := 1/(2k))` raised to the `k`-th power
(`(log x)^k = o((x^{1/(2k)})^k) = o(√x)`). -/

/-- **C-core.** `(log m)^k = o(√m)`: for every `ε' > 0` there is an `M` past which
`(Real.log m)^k ≤ ε' · Real.sqrt m` for all natural `m ≥ M`. -/
lemma log_pow_le_eps_sqrt_eventually (k : ℕ) (hk : 0 < k) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → (Real.log m) ^ k ≤ ε' * Real.sqrt m := by
  -- `log =o[atTop] (· ^ (1/(2k)))`, raise both sides to the `k`-th power.
  have hr : (0 : ℝ) < 1 / (2 * (k : ℝ)) := by positivity
  have hlog : (Real.log) =o[Filter.atTop] (fun x : ℝ => x ^ (1 / (2 * (k : ℝ)))) :=
    isLittleO_log_rpow_atTop hr
  -- raise to the k-th power: |log|^k =o |x^{1/(2k)}|^k = x^{1/2} (eventually, for x ≥ 0).
  have hpow := hlog.pow (n := k) hk
  -- Turn the `IsLittleO` into the explicit ε'-bound on `|log x|^k ≤ ε' |x^{1/(2k)}|^k`.
  have hbound := hpow.def hε'
  -- `hbound : ∀ᶠ x in atTop, ‖(log x)^k‖ ≤ ε' * ‖(x^{1/(2k)})^k‖`.
  rw [Filter.eventually_atTop] at hbound
  obtain ⟨X, hX⟩ := hbound
  -- choose a natural threshold ≥ max (X, 2) so that log m ≥ 0 and the rpow simplifies.
  refine ⟨max (Nat.ceil X) 2, fun m hm => ?_⟩
  have hm2 : (2 : ℕ) ≤ m := le_trans (le_max_right _ _) hm
  have hmX : X ≤ (m : ℝ) := by
    have : (Nat.ceil X : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_trans (le_max_left _ _) hm
    exact le_trans (Nat.le_ceil X) this
  have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
  have hlog_nn : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm2.trans' (by norm_num))
  have h := hX (m : ℝ) hmX
  -- simplify the norms and the nested rpow.
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hlhs : |(Real.log m) ^ k| = (Real.log m) ^ k := abs_of_nonneg (pow_nonneg hlog_nn _)
  have hrhs : |((m : ℝ) ^ (1 / (2 * (k : ℝ)))) ^ k| = Real.sqrt m := by
    rw [abs_of_nonneg (by positivity)]
    rw [← Real.rpow_natCast ((m : ℝ) ^ (1 / (2 * (k : ℝ)))) k, ← Real.rpow_mul hmpos.le]
    rw [Real.sqrt_eq_rpow]
    congr 1
    field_simp
  rw [hlhs, hrhs] at h
  exact h

/-- **C-core'.** The shifted/scaled residual `K·(log m + L)^k / √(m - d) → 0`: for every
`ε' > 0` there is `M` past which `K·(Real.log m + L)^k ≤ ε'·√(m - d)` for `m ≥ M`.
Reduces to `log_pow_le_eps_sqrt_eventually` after `(log m + L)^k ≤ (2 log m)^k` (for `log m ≥ L`,
`m` large) and `√(m-d) ≥ √(m)/√2` (for `m ≥ 2d`). -/
lemma scaled_log_pow_le_eps_sqrt_shift_eventually (k : ℕ) (hk : 0 < k)
    {K L : ℝ} (hK : 0 ≤ K) (d : ℕ) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      K * (Real.log m + L) ^ k ≤ ε' * Real.sqrt ((m : ℝ) - d) := by
  -- Work with the cleaner target `(2 K 2^k) (log m)^k ≤ (ε'/√2) √m`, then translate.
  -- Step 1: choose M₁ so that for m ≥ M₁: log m ≥ |L|  ⟹  log m + L ≤ 2 log m and ≥ 0.
  obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp
    (Filter.Tendsto.eventually_ge_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      (|L| + 1))
  -- Step 2: the base C-core at the scaled epsilon ε'' := ε' / (√2 * 2^k * (K+1)).
  have hden : (0 : ℝ) < Real.sqrt 2 * (2:ℝ)^k * (K + 1) := by positivity
  obtain ⟨M₂, hM₂⟩ := log_pow_le_eps_sqrt_eventually k hk
    (ε' := ε' / (Real.sqrt 2 * (2:ℝ)^k * (K + 1))) (by positivity)
  refine ⟨max (max M₁ M₂) (2 * d + 1), fun m hm => ?_⟩
  have hmM₁ : M₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hmM₂ : M₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm2d : 2 * d + 1 ≤ m := le_trans (le_max_right _ _) hm
  have hlogL : |L| + 1 ≤ Real.log m := by simpa using hM₁ m hmM₁
  have hlog_nn : 0 ≤ Real.log m := le_trans (by positivity) hlogL
  have hL_le : Real.log m + L ≤ 2 * Real.log m := by
    have : L ≤ Real.log m := le_trans (le_trans (le_abs_self L) (by linarith)) (le_refl _)
    linarith
  have hsum_nn : 0 ≤ Real.log m + L := by
    have : -L ≤ Real.log m := le_trans (le_trans (neg_le_abs L) (by linarith)) (le_refl _)
    linarith
  -- (log m + L)^k ≤ (2 log m)^k = 2^k (log m)^k.
  have hpow_le : (Real.log m + L) ^ k ≤ (2:ℝ)^k * (Real.log m) ^ k := by
    calc (Real.log m + L) ^ k ≤ (2 * Real.log m) ^ k := by
            apply pow_le_pow_left₀ hsum_nn hL_le
      _ = (2:ℝ)^k * (Real.log m) ^ k := by rw [mul_pow]
  -- √m ≤ √2 · √(m - d) for m ≥ 2d  (since m ≤ 2(m-d)).
  have hmd_nn : (0 : ℝ) ≤ (m : ℝ) - d := by
    have : (d : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : d ≤ m)
    linarith
  have hsqrt_shift : Real.sqrt m ≤ Real.sqrt 2 * Real.sqrt ((m : ℝ) - d) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply Real.sqrt_le_sqrt
    have : (m : ℝ) ≤ 2 * ((m : ℝ) - d) := by
      have hd2 : 2 * (d : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm2d
      linarith
    linarith
  -- base bound on (log m)^k.
  have hbase := hM₂ m hmM₂
  -- assemble.
  calc K * (Real.log m + L) ^ k
      ≤ K * ((2:ℝ)^k * (Real.log m) ^ k) := by
        apply mul_le_mul_of_nonneg_left hpow_le hK
    _ = ((2:ℝ)^k * K) * (Real.log m) ^ k := by ring
    _ ≤ ((2:ℝ)^k * (K + 1)) * (ε' / (Real.sqrt 2 * (2:ℝ)^k * (K + 1)) * Real.sqrt m) := by
        apply mul_le_mul _ hbase (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = ε' / Real.sqrt 2 * Real.sqrt m := by
        field_simp
    _ ≤ ε' / Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt ((m : ℝ) - d)) := by
        apply mul_le_mul_of_nonneg_left hsqrt_shift (by positivity)
    _ = ε' * Real.sqrt ((m : ℝ) - d) := by
        rw [← mul_assoc]
        congr 1
        field_simp

/-! ## I3c: regime discharge — sub-lemma C (the two Kim–Vu threshold clauses)

These discharge the `c'` and `c''` threshold clauses of `asymptotic_regime_BQ` in the
bounded-aspect regime. Both reduce, after cancelling the matched `(n_A n_B)^{2t}` powers, to
`scaled_log_pow_le_eps_sqrt_shift_eventually`. -/

/-- The aspect bound `max ≤ C·min` gives the product bound `n_A·n_B ≤ C·(min n_A n_B)²`. -/
lemma aspect_prod_bound {n_A n_B : ℕ} {C : ℝ} (_hC : 1 ≤ C)
    (h_aspect : (max n_A n_B : ℝ) ≤ C * (min n_A n_B : ℝ)) :
    ((n_A * n_B : ℕ) : ℝ) ≤ C * ((min n_A n_B : ℕ) : ℝ) ^ 2 := by
  -- normalize the casts: ↑(min n_A n_B) = min ↑n_A ↑n_B etc.
  rw [Nat.cast_min] at *
  have hmin_nn : (0 : ℝ) ≤ min (n_A : ℝ) (n_B : ℝ) := le_min (by positivity) (by positivity)
  have hprod : ((n_A * n_B : ℕ) : ℝ) = min (n_A : ℝ) (n_B : ℝ) * max (n_A : ℝ) (n_B : ℝ) := by
    rw [min_mul_max]; push_cast; ring
  rw [hprod]
  calc min (n_A : ℝ) (n_B : ℝ) * max (n_A : ℝ) (n_B : ℝ)
      ≤ min (n_A : ℝ) (n_B : ℝ) * (C * min (n_A : ℝ) (n_B : ℝ)) :=
        mul_le_mul_of_nonneg_left h_aspect hmin_nn
    _ = C * min (n_A : ℝ) (n_B : ℝ) ^ 2 := by ring

/-- **C (c′).** The `c'` Kim–Vu threshold holds eventually under the aspect bound. -/
lemma c'_threshold_eventually {p : ℝ} (hp_lb : 0 < p) (hp_ub : p < 1)
    (k : ℕ) (hk : 3 ≤ k) (C : ℝ) (hC : 1 ≤ C) {δ_PS : ℝ} (hδ_PS : 0 < δ_PS) :
    ∃ N₀ : ℕ, ∀ (n_A n_B : ℕ), N₀ ≤ min n_A n_B →
      (max n_A n_B : ℝ) ≤ C * (min n_A n_B : ℝ) →
      ∀ (a : Fin n_A) (b : Fin n_B),
        DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k
          * Real.sqrt (((candidatePartnerSet n_A n_B k a b).card : ℝ)
          * (((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ)
              / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ)))
        * ((k + 1 : ℝ) * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) ^ k
      < δ_PS * expectedDegreeFormula n_A n_B k p := by
  have hk1 : 1 ≤ k := by omega
  set t := k - 1 with ht
  -- The post-cancellation constant K' and target slope ε' for C-core'.
  have hck_pos : 0 < meanLowerConst k p := meanLowerConst_pos hp_lb hp_ub
  set Kbase : ℝ := DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k
      * Real.sqrt ((t : ℝ)) * C ^ (2 * t) * ((2 * (k + 1 : ℝ)) ^ k)
    with hKbase
  have hkv_pos : 0 < DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k :=
    DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst_pos k
  have hKbase_nn : 0 ≤ Kbase := by
    rw [hKbase]; positivity
  set ε' : ℝ := δ_PS * meanLowerConst k p / (2 * (4 : ℝ) ^ t) with hε'
  have hε'_pos : 0 < ε' := by rw [hε']; positivity
  -- C-core' provides M for K·(log m + log C)^k ≤ (ε'/2)·√(m-1).  We use ε'/2 to get strict.
  obtain ⟨M, hM⟩ := scaled_log_pow_le_eps_sqrt_shift_eventually k (by omega)
    (K := Kbase) (L := Real.log C) hKbase_nn 1 (ε' := ε' / 2) (by positivity)
  refine ⟨max M (2 * k + 2), fun n_A n_B hN h_aspect a b => ?_⟩
  set m := min n_A n_B with hm
  have hmM : M ≤ m := le_trans (le_max_left _ _) hN
  have hm2k : 2 * k + 2 ≤ m := le_trans (le_max_right _ _) hN
  -- basic positivity / casts
  have hm_pos : 0 < m := by omega
  have hk_le_m : k ≤ m := by omega
  have hmA : m ≤ n_A := Nat.min_le_left _ _
  have hmB : m ≤ n_B := Nat.min_le_right _ _
  have hnA_pos : 0 < n_A := lt_of_lt_of_le hm_pos hmA
  have hnB_pos : 0 < n_B := lt_of_lt_of_le hm_pos hmB
  -- abbreviations
  set s : ℝ := ((candidatePartnerSet n_A n_B k a b).card : ℝ) with hs
  have hs_nn : 0 ≤ s := by rw [hs]; positivity
  -- A: s ≤ (n_A n_B)^t
  have hsA : s ≤ ((n_A * n_B : ℕ) : ℝ) ^ t := by
    rw [hs]
    have := candidatePartnerSet_card_le (n_A := n_A) (n_B := n_B) k a b
    calc ((candidatePartnerSet n_A n_B k a b).card : ℝ)
        ≤ (((n_A * n_B) ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast this
      _ = ((n_A * n_B : ℕ) : ℝ) ^ t := by push_cast [ht]; ring
  -- aspect: n_A · n_B ≤ C · m²
  have h_aspect' : ((n_A * n_B : ℕ) : ℝ) ≤ C * (m : ℝ) ^ 2 := aspect_prod_bound hC h_aspect
  -- so (n_A n_B)^t ≤ (C m²)^t ≤ C^{2t} m^{2t}
  have hbase_nn : (0 : ℝ) ≤ ((n_A * n_B : ℕ) : ℝ) := by positivity
  have hCm_nn : (0 : ℝ) ≤ C * (m : ℝ) ^ 2 := by positivity
  have hsP : s ≤ C ^ (2 * t) * (m : ℝ) ^ (2 * t) := by
    calc s ≤ ((n_A * n_B : ℕ) : ℝ) ^ t := hsA
      _ ≤ (C * (m : ℝ) ^ 2) ^ t := by
            apply pow_le_pow_left₀ hbase_nn h_aspect'
      _ = C ^ t * (m : ℝ) ^ (2 * t) := by
            rw [mul_pow, ← pow_mul, mul_comm 2 t]
      _ ≤ C ^ (2 * t) * (m : ℝ) ^ (2 * t) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply pow_le_pow_right₀ hC (by omega)
  -- the sqrt-argument bound: arg ≤ (k-1) · (C^{2t} m^{2t})² / (m-1)
  -- (min(n_A-1,n_B-1) = m - 1 ≥ 1)
  have hmin_eq : ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have : min (n_A - 1) (n_B - 1) = m - 1 := by
      rw [hm]; omega
    rw [this]
    have : 1 ≤ m := by omega
    push_cast [Nat.cast_sub this]; ring
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 ≤ m)
    linarith
  -- bound on the LHS sqrt argument.  `(k - 1 : ℕ) = t`.
  have htcast : ((k - 1 : ℕ) : ℝ) = (t : ℝ) := by rw [ht]
  set P : ℝ := C ^ (2 * t) * (m : ℝ) ^ (2 * t) with hP
  have hP_nn : 0 ≤ P := by rw [hP]; positivity
  have harg_eq : s * (((k - 1 : ℕ) : ℝ) * s / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ))
      = (t : ℝ) * s ^ 2 / ((m : ℝ) - 1) := by
    rw [htcast, hmin_eq]; ring
  have hs2P2 : s ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ hs_nn hsP 2
  have harg_le : s * (((k - 1 : ℕ) : ℝ) * s / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ))
      ≤ (t : ℝ) * P ^ 2 / ((m : ℝ) - 1) := by
    rw [harg_eq]
    gcongr
  -- √arg ≤ √((t : ℝ) · P² / (m-1)) = √t · P / √(m-1)
  have harg_nn : 0 ≤ s * (((k - 1 : ℕ) : ℝ) * s / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ)) := by
    rw [harg_eq]; positivity
  have hsqrt_le : Real.sqrt (s * (((k - 1 : ℕ) : ℝ) * s
        / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ)))
      ≤ Real.sqrt ((t : ℝ)) * P / Real.sqrt ((m : ℝ) - 1) := by
    refine le_trans (Real.sqrt_le_sqrt harg_le) ?_
    rw [Real.sqrt_div ((by positivity : (0:ℝ) ≤ (t:ℝ) * P^2)), Real.sqrt_mul (by positivity),
        Real.sqrt_sq hP_nn]
  -- the log factor:  log N = log (n_A·n_B) ≤ 2 log m + 2 log C.
  have hcard : ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) = ((n_A * n_B : ℕ) : ℝ) := by
    simp [Fintype.card_prod, Fintype.card_fin]
  set L := Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) with hL
  have hL_nn : 0 ≤ L := by
    rw [hL, hcard]; apply Real.log_nonneg
    have : (1 : ℝ) ≤ ((n_A * n_B : ℕ) : ℝ) := by
      have : 1 ≤ n_A * n_B := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast this
    exact this
  have hlogC_nn : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlogm_nn : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hL_le : L ≤ 2 * Real.log m + 2 * Real.log C := by
    rw [hL, hcard]
    calc Real.log ((n_A * n_B : ℕ) : ℝ) ≤ Real.log (C * (m : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) h_aspect'
      _ = Real.log C + 2 * Real.log m := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ 2 * Real.log m + 2 * Real.log C := by linarith
  -- the log-power factor bound
  have hlog_factor : ((k + 1 : ℝ) * L) ^ k ≤ (2 * (k + 1 : ℝ)) ^ k * (Real.log m + Real.log C) ^ k := by
    have hkp_nn : (0 : ℝ) ≤ (k + 1 : ℝ) := by positivity
    calc ((k + 1 : ℝ) * L) ^ k
        ≤ ((k + 1 : ℝ) * (2 * Real.log m + 2 * Real.log C)) ^ k := by
          apply pow_le_pow_left₀ (by positivity)
          apply mul_le_mul_of_nonneg_left hL_le hkp_nn
      _ = (2 * (k + 1 : ℝ)) ^ k * (Real.log m + Real.log C) ^ k := by
          rw [← mul_pow]; congr 1; ring
  -- RHS lower bound:  δ_PS·μc ≥ δ_PS · c_k · (m-k)^{2t} ≥ δ_PS · c_k · m^{2t}/4^t = ε'·2·√? ...
  -- We use sub-lemma B with both factors ≥ (m-k)^t and (m-k) ≥ m/2.
  have hmk_nn : (0 : ℝ) ≤ (m : ℝ) - (k : ℝ) := by
    have : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk_le_m
    linarith
  -- B gives:  meanLowerConst · ((n_A-(k-1))^t · (n_B-(k-1))^t) ≤ μc.
  have hB := expectedDegreeFormula_ge (n_A := n_A) (n_B := n_B) (k := k) (p := p)
    hp_lb.le hp_ub.le
  -- (n_X - 1) + 1 - (k - 1) = n_X - (k-1) ≥ m - (k-1) ≥ m - k  (as ℕ casts).
  have hbaseA_ge : (m : ℝ) - (k : ℝ) ≤ ((((n_A - 1) + 1 - (k - 1) : ℕ) : ℝ)) := by
    have hnat : m - k ≤ (n_A - 1) + 1 - (k - 1) := by omega
    calc (m : ℝ) - (k : ℝ) ≤ ((m - k : ℕ) : ℝ) := by
            rw [Nat.cast_sub hk_le_m]
      _ ≤ ((((n_A - 1) + 1 - (k - 1)) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hbaseB_ge : (m : ℝ) - (k : ℝ) ≤ ((((n_B - 1) + 1 - (k - 1) : ℕ) : ℝ)) := by
    have hnat : m - k ≤ (n_B - 1) + 1 - (k - 1) := by omega
    calc (m : ℝ) - (k : ℝ) ≤ ((m - k : ℕ) : ℝ) := by
            rw [Nat.cast_sub hk_le_m]
      _ ≤ ((((n_B - 1) + 1 - (k - 1)) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hμc_ge : meanLowerConst k p * (((m : ℝ) - (k : ℝ)) ^ t * ((m : ℝ) - (k : ℝ)) ^ t)
      ≤ expectedDegreeFormula n_A n_B k p := by
    refine le_trans ?_ hB
    apply mul_le_mul_of_nonneg_left _ hck_pos.le
    apply mul_le_mul (pow_le_pow_left₀ hmk_nn hbaseA_ge t) (pow_le_pow_left₀ hmk_nn hbaseB_ge t)
      (by positivity) (by positivity)
  -- (m - k)^t · (m-k)^t = (m-k)^{2t} ≥ (m/2)^{2t} = m^{2t}/4^t.
  have hmk_half : (m : ℝ) / 2 ≤ (m : ℝ) - (k : ℝ) := by
    have : (k : ℝ) ≤ (m : ℝ) / 2 := by
      have : (2 : ℝ) * (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 * k ≤ m)
      linarith
    linarith
  have h4t : (4 : ℝ) ^ t = (2 : ℝ) ^ (2 * t) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
  have hpow2t : (m : ℝ) ^ (2 * t) / (4 : ℝ) ^ t
      ≤ ((m : ℝ) - (k : ℝ)) ^ t * ((m : ℝ) - (k : ℝ)) ^ t := by
    rw [← pow_add, show t + t = 2 * t by ring]
    calc (m : ℝ) ^ (2 * t) / (4 : ℝ) ^ t = ((m : ℝ) / 2) ^ (2 * t) := by
            rw [div_pow, h4t]
      _ ≤ ((m : ℝ) - (k : ℝ)) ^ (2 * t) := by
            apply pow_le_pow_left₀ (by positivity) hmk_half
  -- Assemble the RHS lower bound:  δ_PS·μc ≥ (δ_PS·c_k/4^t)·m^{2t} = ε'·2·m^{2t}.
  have hRHS_ge : ε' * 2 * (m : ℝ) ^ (2 * t) ≤ δ_PS * expectedDegreeFormula n_A n_B k p := by
    have : ε' * 2 * (m : ℝ) ^ (2 * t)
        = δ_PS * (meanLowerConst k p * ((m : ℝ) ^ (2 * t) / (4 : ℝ) ^ t)) := by
      rw [hε']; field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_left _ hδ_PS.le
    apply le_trans _ hμc_ge
    apply mul_le_mul_of_nonneg_left hpow2t hck_pos.le
  -- C-core' bound at m:  Kbase·(log m + log C)^k ≤ (ε'/2)·√(m-1).
  have hcore := hM m hmM
  -- Now chain everything.  LHS ≤ kimVuConst·(√t·P/√(m-1))·(2(k+1))^k·(log m+log C)^k
  --   = [kimVuConst·√t·C^{2t}·(2(k+1))^k]·m^{2t}·(log m+log C)^k/√(m-1)
  --   = Kbase·(log m+log C)^k·m^{2t}/√(m-1) ≤ (ε'/2)·√(m-1)·m^{2t}/√(m-1) = (ε'/2)·m^{2t}
  --   < ε'·2·m^{2t} ≤ RHS.
  have hkv_nn : 0 ≤ DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k := hkv_pos.le
  have hsqrt_arg_nn : 0 ≤ Real.sqrt (s * (((k - 1 : ℕ) : ℝ) * s
      / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ))) := Real.sqrt_nonneg _
  have hlogfac_nn : 0 ≤ (Real.log m + Real.log C) ^ k := by positivity
  have hsqrtm1_pos : 0 < Real.sqrt ((m : ℝ) - 1) := Real.sqrt_pos.mpr hm1_pos
  have hPpow_eq : P = C ^ (2 * t) * (m : ℝ) ^ (2 * t) := hP
  -- LHS step 1: replace the log-power and sqrt factors by their bounds.
  have hLHS_le1 :
      DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k
        * Real.sqrt (s * (((k - 1 : ℕ) : ℝ) * s / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ)))
        * ((k + 1 : ℝ) * L) ^ k
      ≤ DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k
          * (Real.sqrt ((t : ℝ)) * P / Real.sqrt ((m : ℝ) - 1))
          * ((2 * (k + 1 : ℝ)) ^ k * (Real.log m + Real.log C) ^ k) := by
    apply mul_le_mul (by apply mul_le_mul_of_nonneg_left hsqrt_le hkv_nn) hlog_factor
      (by positivity) (by positivity)
  -- LHS step 2: this equals (Kbase·(log m+log C)^k / √(m-1)) · m^{2t}.
  have hLHS_eq :
      DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k
          * (Real.sqrt ((t : ℝ)) * P / Real.sqrt ((m : ℝ) - 1))
          * ((2 * (k + 1 : ℝ)) ^ k * (Real.log m + Real.log C) ^ k)
      = (Kbase * (Real.log m + Real.log C) ^ k / Real.sqrt ((m : ℝ) - 1)) * (m : ℝ) ^ (2 * t) := by
    rw [hKbase, hPpow_eq]; field_simp
  -- LHS step 3: Kbase·(log m+log C)^k ≤ (ε'/2)·√(m-1), so divide and multiply.
  have hcore' : Kbase * (Real.log m + Real.log C) ^ k ≤ ε' / 2 * Real.sqrt ((m : ℝ) - 1) := by
    have := hcore; rw [Nat.cast_one] at this; exact this
  have hLHS_le3 :
      (Kbase * (Real.log m + Real.log C) ^ k / Real.sqrt ((m : ℝ) - 1)) * (m : ℝ) ^ (2 * t)
      ≤ (ε' / 2) * (m : ℝ) ^ (2 * t) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ hsqrtm1_pos]
    exact hcore'
  -- Final: (ε'/2)·m^{2t} < ε'·2·m^{2t} ≤ RHS.
  have hstrict : (ε' / 2) * (m : ℝ) ^ (2 * t) < ε' * 2 * (m : ℝ) ^ (2 * t) := by
    apply mul_lt_mul_of_pos_right _ (by positivity)
    linarith
  calc DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k
        * Real.sqrt (s * (((k - 1 : ℕ) : ℝ) * s / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ)))
        * ((k + 1 : ℝ) * L) ^ k
      ≤ _ := hLHS_le1
    _ = _ := hLHS_eq
    _ ≤ (ε' / 2) * (m : ℝ) ^ (2 * t) := hLHS_le3
    _ < ε' * 2 * (m : ℝ) ^ (2 * t) := hstrict
    _ ≤ δ_PS * expectedDegreeFormula n_A n_B k p := hRHS_ge

/-- **C (c″).** The `c''` Kim–Vu threshold (at `ε_codeg = 1`) holds eventually under the aspect
bound. Here the `|cpps|` powers cancel directly (LHS has `|cpps|`, RHS has `|cpps|`), so the
residual is the pure-constant inequality `kimVuConst·√(k-2)·((k+2)log N)^k < |cpps|·c''const`
with `c''const = p^{k-2}(1-p)^{k(k-1)-2}`. -/
lemma c''_threshold_eventually {p : ℝ} (hp_lb : 0 < p) (hp_ub : p < 1)
    (k : ℕ) (hk : 3 ≤ k) (C : ℝ) (hC : 1 ≤ C) :
    ∃ N₀ : ℕ, ∀ (n_A n_B : ℕ), N₀ ≤ min n_A n_B →
      (max n_A n_B : ℝ) ≤ C * (min n_A n_B : ℝ) →
      ∀ (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B), a_1 ≠ a_2 → b_1 ≠ b_2 →
        DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k *
          Real.sqrt (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
            * (((k - 2 : ℕ) : ℝ) * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ)))
          * ((k + 2 : ℝ) * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) ^ k
        < (1 : ℝ) * (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
            * p ^ (k - 2) * (1 - p) ^ (k * (k - 1) - 2)) := by
  set t := k - 2 with ht
  have h1mp : (0 : ℝ) < 1 - p := by linarith
  have hkv_pos : 0 < DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k :=
    DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst_pos k
  -- the pure constant on the RHS (after cancelling |cpps|):  c''const = p^{k-2}(1-p)^{...}.
  set cconst : ℝ := p ^ (k - 2) * (1 - p) ^ (k * (k - 1) - 2) with hcconst
  have hcconst_pos : 0 < cconst := by rw [hcconst]; positivity
  set Kbase : ℝ := DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k
      * Real.sqrt ((t : ℝ)) * ((2 * (k + 2 : ℝ)) ^ k) with hKbase
  have hKbase_nn : 0 ≤ Kbase := by rw [hKbase]; positivity
  set ε' : ℝ := cconst / 2 with hε'
  obtain ⟨M, hM⟩ := scaled_log_pow_le_eps_sqrt_shift_eventually k (by omega)
    (K := Kbase) (L := Real.log C) hKbase_nn 2 (ε' := ε' / 2) (by positivity)
  refine ⟨max M (2 * k + 3), fun n_A n_B hN h_aspect a_1 a_2 b_1 b_2 h_a h_b => ?_⟩
  set m := min n_A n_B with hm
  have hmM : M ≤ m := le_trans (le_max_left _ _) hN
  have hm2k : 2 * k + 3 ≤ m := le_trans (le_max_right _ _) hN
  have hm_pos : 0 < m := by omega
  have hmA : m ≤ n_A := Nat.min_le_left _ _
  have hmB : m ≤ n_B := Nat.min_le_right _ _
  have hkA : k ≤ n_A := le_trans (by omega) hmA
  have hkB : k ≤ n_B := le_trans (by omega) hmB
  -- |cpps| > 0 via the exact card formula.
  set s : ℝ := ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ) with hs
  have hs_pos : 0 < s := by
    rw [hs, candidatePairPartnerSet_card k (by omega) hkA hkB a_1 a_2 b_1 b_2 h_a h_b]
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (Nat.choose_pos (by omega))
      (Nat.choose_pos (by omega))) (Nat.factorial_pos _)
  have hs_nn : 0 ≤ s := hs_pos.le
  -- min(n_A-2,n_B-2) = m - 2.
  have hmin_eq : ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ) = (m : ℝ) - 2 := by
    have : min (n_A - 2) (n_B - 2) = m - 2 := by rw [hm]; omega
    rw [this, Nat.cast_sub (by omega)]; push_cast; ring
  have hm2_pos : (0 : ℝ) < (m : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 3 ≤ m)
    linarith
  have htcast : ((k - 2 : ℕ) : ℝ) = (t : ℝ) := by rw [ht]
  -- sqrt-argument = s · (t·s/(m-2)) = t·s²/(m-2);  √ = √t·s/√(m-2)  (s ≥ 0).
  have harg_eq : s * (((k - 2 : ℕ) : ℝ) * s / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ))
      = (t : ℝ) * s ^ 2 / ((m : ℝ) - 2) := by
    rw [htcast, hmin_eq]; ring
  have hsqrt_eq : Real.sqrt (s * (((k - 2 : ℕ) : ℝ) * s / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ)))
      = Real.sqrt ((t : ℝ)) * s / Real.sqrt ((m : ℝ) - 2) := by
    rw [harg_eq, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_sq hs_nn]
  -- log factor:  N = n_A·n_B, log N ≤ 2 log m + 2 log C.
  have hcard : ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) = ((n_A * n_B : ℕ) : ℝ) := by
    simp [Fintype.card_prod, Fintype.card_fin]
  set L := Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) with hL
  have hlogm_nn : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hlogC_nn : 0 ≤ Real.log C := Real.log_nonneg hC
  have h_aspect' : ((n_A * n_B : ℕ) : ℝ) ≤ C * (m : ℝ) ^ 2 := aspect_prod_bound hC h_aspect
  have hnAnB_pos : (0 : ℝ) < ((n_A * n_B : ℕ) : ℝ) := by
    have : 0 < n_A * n_B := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hL_le : L ≤ 2 * Real.log m + 2 * Real.log C := by
    rw [hL, hcard]
    calc Real.log ((n_A * n_B : ℕ) : ℝ) ≤ Real.log (C * (m : ℝ) ^ 2) :=
          Real.log_le_log hnAnB_pos h_aspect'
      _ = Real.log C + 2 * Real.log m := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ 2 * Real.log m + 2 * Real.log C := by linarith
  have hlog_factor : ((k + 2 : ℝ) * L) ^ k
      ≤ (2 * (k + 2 : ℝ)) ^ k * (Real.log m + Real.log C) ^ k := by
    calc ((k + 2 : ℝ) * L) ^ k
        ≤ ((k + 2 : ℝ) * (2 * Real.log m + 2 * Real.log C)) ^ k := by
          apply pow_le_pow_left₀ (by positivity)
          apply mul_le_mul_of_nonneg_left hL_le (by positivity)
      _ = (2 * (k + 2 : ℝ)) ^ k * (Real.log m + Real.log C) ^ k := by
          rw [← mul_pow]; congr 1; ring
  -- C-core' at d = 2:  Kbase·(log m + log C)^k ≤ (ε'/2)·√(m-2).
  have hcore := hM m hmM
  -- Assemble.  LHS = kimVuConst·(√t·s/√(m-2))·((k+2)L)^k
  --   ≤ kimVuConst·(√t·s/√(m-2))·(2(k+2))^k·(log m+log C)^k
  --   = s·[Kbase·(log m+log C)^k/√(m-2)] ≤ s·(ε'/2) < s·cconst = RHS.
  have hsqrtm2_pos : 0 < Real.sqrt ((m : ℝ) - 2) := Real.sqrt_pos.mpr hm2_pos
  have hkv_nn : 0 ≤ DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k := hkv_pos.le
  -- the bracket bound:  Kbase·(log m+log C)^k/√(m-2) ≤ ε'/2.
  have hbracket : Kbase * (Real.log m + Real.log C) ^ k / Real.sqrt ((m : ℝ) - 2) ≤ ε' / 2 := by
    rw [div_le_iff₀ hsqrtm2_pos]; exact hcore
  -- rewrite LHS to s·bracket.
  have hLHS_le1 :
      DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k
        * Real.sqrt (s * (((k - 2 : ℕ) : ℝ) * s / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ)))
        * ((k + 2 : ℝ) * L) ^ k
      ≤ DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k
          * (Real.sqrt ((t : ℝ)) * s / Real.sqrt ((m : ℝ) - 2))
          * ((2 * (k + 2 : ℝ)) ^ k * (Real.log m + Real.log C) ^ k) := by
    rw [hsqrt_eq]
    apply mul_le_mul_of_nonneg_left hlog_factor (by positivity)
  have hLHS_eq :
      DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k
          * (Real.sqrt ((t : ℝ)) * s / Real.sqrt ((m : ℝ) - 2))
          * ((2 * (k + 2 : ℝ)) ^ k * (Real.log m + Real.log C) ^ k)
      = s * (Kbase * (Real.log m + Real.log C) ^ k / Real.sqrt ((m : ℝ) - 2)) := by
    rw [hKbase]; field_simp
  calc DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k
        * Real.sqrt (s * (((k - 2 : ℕ) : ℝ) * s / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ)))
        * ((k + 2 : ℝ) * L) ^ k
      ≤ _ := hLHS_le1
    _ = s * (Kbase * (Real.log m + Real.log C) ^ k / Real.sqrt ((m : ℝ) - 2)) := hLHS_eq
    _ ≤ s * (ε' / 2) := by apply mul_le_mul_of_nonneg_left hbracket hs_nn
    _ < s * cconst := by
        apply mul_lt_mul_of_pos_left _ hs_pos
        rw [hε']; linarith
    _ = (1 : ℝ) * (s * p ^ (k - 2) * (1 - p) ^ (k * (k - 1) - 2)) := by
        rw [hcconst]; ring

/-- **C (c″-arith).** The codegree arithmetic clause `(1+1)·μ'' ≤ δ_PS·μc` holds eventually
under the aspect bound. `μ'' = |cpps|·p^{k-2}(1-p)^{k(k-1)-2} = Θ((n)^{k-2})` while
`μc = Θ((n)^{2(k-1)})`, so `μ''/μc → 0`. -/
lemma codeg_arith_eventually {p : ℝ} (hp_lb : 0 < p) (hp_ub : p < 1)
    (k : ℕ) (hk : 3 ≤ k) (C : ℝ) (hC : 1 ≤ C) {δ_PS : ℝ} (hδ_PS : 0 < δ_PS) :
    ∃ N₀ : ℕ, ∀ (n_A n_B : ℕ), N₀ ≤ min n_A n_B →
      (max n_A n_B : ℝ) ≤ C * (min n_A n_B : ℝ) →
      ∀ (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B), a_1 ≠ a_2 → b_1 ≠ b_2 →
        (1 + (1 : ℝ)) * (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
            * p ^ (k - 2) * (1 - p) ^ (k * (k - 1) - 2))
          ≤ δ_PS * expectedDegreeFormula n_A n_B k p := by
  set t := k - 2 with ht
  set u := k - 1 with hu
  have h1mp : (0 : ℝ) < 1 - p := by linarith
  have hck_pos : 0 < meanLowerConst k p := meanLowerConst_pos hp_lb hp_ub
  -- positive constants:  upper-const for μ'' (mult m^{2t}) and lower-const for μc (mult m^{2u}).
  set Aconst : ℝ := 2 * (C ^ t * (p ^ t * (1 - p) ^ (k * (k - 1) - 2))) with hAconst
  have hAconst_nn : 0 ≤ Aconst := by rw [hAconst]; positivity
  set Bconst : ℝ := δ_PS * (meanLowerConst k p / (4 : ℝ) ^ u) with hBconst
  have hBconst_pos : 0 < Bconst := by rw [hBconst]; positivity
  -- threshold:  m ≥ N₀ ensures Aconst·m^{2t} ≤ Bconst·m^{2u}  (since 2u = 2t+2).
  -- equivalently Aconst ≤ Bconst·m²; pick N₀ = ⌈Aconst/Bconst⌉ + (2k+3).
  obtain ⟨Mr, hMr⟩ := exists_nat_ge (Aconst / Bconst)
  refine ⟨max Mr (2 * k + 3), fun n_A n_B hN h_aspect a_1 a_2 b_1 b_2 h_a h_b => ?_⟩
  set m := min n_A n_B with hm
  have hmMr : Mr ≤ m := le_trans (le_max_left _ _) hN
  have hm2k : 2 * k + 3 ≤ m := le_trans (le_max_right _ _) hN
  have hm_pos : 0 < m := by omega
  have hmA : m ≤ n_A := Nat.min_le_left _ _
  have hmB : m ≤ n_B := Nat.min_le_right _ _
  have hkA : k ≤ n_A := le_trans (by omega) hmA
  have hkB : k ≤ n_B := le_trans (by omega) hmB
  have hk_le_m : k ≤ m := by omega
  set s : ℝ := ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ) with hs
  have hs_nn : 0 ≤ s := by rw [hs]; positivity
  -- upper bound s ≤ (n_A n_B)^t ≤ C^t m^{2t}.
  have h_aspect' : ((n_A * n_B : ℕ) : ℝ) ≤ C * (m : ℝ) ^ 2 := aspect_prod_bound hC h_aspect
  have hsP : s ≤ C ^ t * (m : ℝ) ^ (2 * t) := by
    have hsA : s ≤ ((n_A * n_B : ℕ) : ℝ) ^ t := by
      rw [hs]
      have := candidatePairPartnerSet_card_le (n_A := n_A) (n_B := n_B) k a_1 a_2 b_1 b_2
      calc ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
          ≤ (((n_A * n_B) ^ (k - 2) : ℕ) : ℝ) := by exact_mod_cast this
        _ = ((n_A * n_B : ℕ) : ℝ) ^ t := by push_cast [ht]; ring
    calc s ≤ ((n_A * n_B : ℕ) : ℝ) ^ t := hsA
      _ ≤ (C * (m : ℝ) ^ 2) ^ t := pow_le_pow_left₀ (by positivity) h_aspect' t
      _ = C ^ t * (m : ℝ) ^ (2 * t) := by rw [mul_pow, ← pow_mul, mul_comm 2 t]
  -- μ'' ≤ Aconst/2 · m^{2t}.
  have hμ''_le : s * p ^ (k - 2) * (1 - p) ^ (k * (k - 1) - 2)
      ≤ (C ^ t * (p ^ t * (1 - p) ^ (k * (k - 1) - 2))) * (m : ℝ) ^ (2 * t) := by
    have hfac_nn : 0 ≤ p ^ (k - 2) * (1 - p) ^ (k * (k - 1) - 2) := by positivity
    calc s * p ^ (k - 2) * (1 - p) ^ (k * (k - 1) - 2)
        = s * (p ^ (k - 2) * (1 - p) ^ (k * (k - 1) - 2)) := by ring
      _ ≤ (C ^ t * (m : ℝ) ^ (2 * t)) * (p ^ (k - 2) * (1 - p) ^ (k * (k - 1) - 2)) := by
          apply mul_le_mul_of_nonneg_right hsP hfac_nn
      _ = (C ^ t * (p ^ t * (1 - p) ^ (k * (k - 1) - 2))) * (m : ℝ) ^ (2 * t) := by
          rw [ht]; ring
  -- μc ≥ Bconst/δ_PS · m^{2u}.
  have hmk_nn : (0 : ℝ) ≤ (m : ℝ) - (k : ℝ) := by
    have : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk_le_m
    linarith
  have hmk_half : (m : ℝ) / 2 ≤ (m : ℝ) - (k : ℝ) := by
    have : (2 : ℝ) * (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 * k ≤ m)
    linarith
  have hB := expectedDegreeFormula_ge (n_A := n_A) (n_B := n_B) (k := k) (p := p)
    hp_lb.le hp_ub.le
  have hbaseA_ge : (m : ℝ) - (k : ℝ) ≤ ((((n_A - 1) + 1 - (k - 1) : ℕ) : ℝ)) := by
    have hnat : m - k ≤ (n_A - 1) + 1 - (k - 1) := by omega
    calc (m : ℝ) - (k : ℝ) ≤ ((m - k : ℕ) : ℝ) := by rw [Nat.cast_sub hk_le_m]
      _ ≤ _ := by exact_mod_cast hnat
  have hbaseB_ge : (m : ℝ) - (k : ℝ) ≤ ((((n_B - 1) + 1 - (k - 1) : ℕ) : ℝ)) := by
    have hnat : m - k ≤ (n_B - 1) + 1 - (k - 1) := by omega
    calc (m : ℝ) - (k : ℝ) ≤ ((m - k : ℕ) : ℝ) := by rw [Nat.cast_sub hk_le_m]
      _ ≤ _ := by exact_mod_cast hnat
  have hμc_ge : meanLowerConst k p * (((m : ℝ) - (k : ℝ)) ^ (k-1) * ((m : ℝ) - (k : ℝ)) ^ (k-1))
      ≤ expectedDegreeFormula n_A n_B k p := by
    refine le_trans ?_ hB
    apply mul_le_mul_of_nonneg_left _ hck_pos.le
    apply mul_le_mul (pow_le_pow_left₀ hmk_nn hbaseA_ge (k-1))
      (pow_le_pow_left₀ hmk_nn hbaseB_ge (k-1)) (by positivity) (by positivity)
  have h4u : (4 : ℝ) ^ u = (2 : ℝ) ^ (2 * u) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]
  have hpow2u : (m : ℝ) ^ (2 * u) / (4 : ℝ) ^ u
      ≤ ((m : ℝ) - (k : ℝ)) ^ (k-1) * ((m : ℝ) - (k : ℝ)) ^ (k-1) := by
    rw [← pow_add, show (k-1) + (k-1) = 2 * u by rw [hu]; ring]
    calc (m : ℝ) ^ (2 * u) / (4 : ℝ) ^ u = ((m : ℝ) / 2) ^ (2 * u) := by
            rw [div_pow, h4u]
      _ ≤ ((m : ℝ) - (k : ℝ)) ^ (2 * u) := pow_le_pow_left₀ (by positivity) hmk_half (2 * u)
  have hμc_ge2 : Bconst / δ_PS * (m : ℝ) ^ (2 * u) ≤ expectedDegreeFormula n_A n_B k p := by
    refine le_trans ?_ hμc_ge
    have : Bconst / δ_PS * (m : ℝ) ^ (2 * u)
        = meanLowerConst k p * ((m : ℝ) ^ (2 * u) / (4 : ℝ) ^ u) := by
      rw [hBconst]; field_simp
    rw [this]
    apply mul_le_mul_of_nonneg_left hpow2u hck_pos.le
  -- now combine: 2·μ'' ≤ Aconst·m^{2t} ≤ Bconst·m^{2u} ≤ δ_PS·μc.
  have h2t2 : 2 * u = 2 * t + 2 := by rw [hu, ht]; omega
  have hm2_pos : (0 : ℝ) < (m : ℝ) ^ (2 * t) := by positivity
  have h_Am_le_Bm : Aconst * (m : ℝ) ^ (2 * t) ≤ Bconst * (m : ℝ) ^ (2 * u) := by
    rw [h2t2, pow_add]
    rw [show Bconst * ((m : ℝ) ^ (2 * t) * (m : ℝ) ^ 2)
        = (Bconst * (m : ℝ) ^ 2) * (m : ℝ) ^ (2 * t) by ring]
    apply mul_le_mul_of_nonneg_right _ hm2_pos.le
    -- Aconst ≤ Bconst·m²  (from m ≥ Mr ≥ Aconst/Bconst, m ≥ 1).
    have hm_ge : Aconst / Bconst ≤ (m : ℝ) := le_trans hMr (by exact_mod_cast hmMr)
    have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
    have : Aconst ≤ Bconst * (m : ℝ) := by
      rw [div_le_iff₀ hBconst_pos] at hm_ge; linarith
    calc Aconst ≤ Bconst * (m : ℝ) := this
      _ ≤ Bconst * (m : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hBconst_pos.le
          nlinarith [hm_ge1]
  calc (1 + (1 : ℝ)) * (s * p ^ (k - 2) * (1 - p) ^ (k * (k - 1) - 2))
      = 2 * (s * p ^ (k - 2) * (1 - p) ^ (k * (k - 1) - 2)) := by ring
    _ ≤ 2 * ((C ^ t * (p ^ t * (1 - p) ^ (k * (k - 1) - 2))) * (m : ℝ) ^ (2 * t)) := by
        apply mul_le_mul_of_nonneg_left hμ''_le (by norm_num)
    _ = Aconst * (m : ℝ) ^ (2 * t) := by rw [hAconst]; ring
    _ ≤ Bconst * (m : ℝ) ^ (2 * u) := h_Am_le_Bm
    _ = δ_PS * (Bconst / δ_PS * (m : ℝ) ^ (2 * u)) := by
        field_simp
    _ ≤ δ_PS * expectedDegreeFormula n_A n_B k p := by
        apply mul_le_mul_of_nonneg_left hμc_ge2 hδ_PS.le

/-! ## I3b core: `asymptotic_regime_BQ` predicate (verbatim Kim–Vu route)

`asymptotic_regime_BQ p hp` is the **honest balanced-asymptotic hypothesis** consumed by
`secRandomBipartite_aas_BQ` (the Brualdi–Quinn `χ'_s ≤ Δ_A·Δ_B` a.a.s. bound routed through
the SOUND verbatim Kim–Vu axiom via `c'`/`c''`). It mirrors `asymptotic_regime` in spirit
(an explicit Prop recording the residual real-analysis content) but bundles exactly the
large-`n` data the B–Q headline proof consumes:

* a fixed nibble degree `k ≥ 3` and a leftover slack `η > 0` with `1/k + η ≤ (1−p/2)·p`
  (the `k`-choice link feeding `nibble_real_le_of_deltas`);
* for every P–S deviation `δ_PS > 0`, P–S floor `D₀`, Kim–Vu tail constant `C_kv > 0`,
  and `ε > 0`, a threshold `N₀` beyond which (for `min n_A n_B ≥ N₀`):
  - `k ≤ n_A`, `k ≤ n_B`;
  - the `hN1` log conditions for `c'` (`λ = (k+1)·log N`) and `c''` (`λ = (k+2)·log N`);
  - the `c'` deviation threshold `h_thresh` at fraction `δ_PS` (around `μc`);
  - a codegree deviation `ε_codeg > 0` with the `c''` `h_thresh` at `ε_codeg` AND the
    `Hk_codegree_bounded_of_good` arithmetic `(1+ε_codeg)·μ'' ≤ δ_PS·μc`;
  - the P–S largeness `D₀ ≤ μc`;
  - the Kim–Vu tail decay `C_kv / N ≤ ε/4` (Bonferroni budget for `EReg`/`ECodeg`);
  - the `deltaB`-link `(1−p/2)·n_A·p ≥ n_A·(1/k+η)+1` (`h_gap` for `nibble_real_le_of_deltas`);
  - the `deltaA`-positivity link `1 ≤ (1−p/2)·n_B·p` (gives `1 ≤ deltaA` on the `EA` event).

Like `asymptotic_regime`, this is an explicit *hypothesis* (not proven): it records the
balanced-asymptotic regime in which the Kim–Vu tails and the `Δ_A`/`Δ_B` concentration combine.
`N := Fintype.card (Fin n_A × Fin n_B)`, `μc := expectedDegreeFormula n_A n_B k p.toReal`, and
`μ'' a₁ a₂ b₁ b₂ := |candidatePairPartnerSet| · p^{k-2} · (1-p)^{k(k-1)-2}`. -/
def asymptotic_regime_BQ (p : ENNReal) (_hp : p ≤ 1) (C : ℝ) (_hC : 1 ≤ C) : Prop :=
  ∃ (k : ℕ) (η : ℝ), 3 ≤ k ∧ 0 < η ∧
    (1 / (k : ℝ) + η ≤ (1 - p.toReal / 2) * p.toReal) ∧
    ∀ (δ_PS : ℝ), 0 < δ_PS → ∀ (D₀ : ℝ) (C_kv : ℝ), 0 < C_kv →
      ∀ (ε : ℝ), 0 < ε → ∃ N₀ : ℕ, ∀ (n_A n_B : ℕ), N₀ ≤ min n_A n_B →
        (max n_A n_B : ℝ) ≤ C * (min n_A n_B : ℝ) →
        (k ≤ n_A ∧ k ≤ n_B) ∧
        -- hN1 for c'
        (1 < (k + 1 : ℝ) * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) ∧
        -- hN1 for c''
        (1 < (k + 2 : ℝ) * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) ∧
        -- c' h_thresh at deviation δ_PS
        (∀ (a : Fin n_A) (b : Fin n_B),
            DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k * Real.sqrt (((candidatePartnerSet n_A n_B k a b).card : ℝ)
              * (((k - 1 : ℕ) : ℝ) * ((candidatePartnerSet n_A n_B k a b).card : ℝ)
                  / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ)))
            * ((k + 1 : ℝ) * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) ^ k
          < δ_PS * expectedDegreeFormula n_A n_B k p.toReal) ∧
        -- c'' h_thresh + codeg arithmetic, at some ε_codeg
        (∃ ε_codeg : ℝ, 0 < ε_codeg ∧
          (∀ (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B), a_1 ≠ a_2 → b_1 ≠ b_2 →
              DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k *
                Real.sqrt (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                  * (((k - 2 : ℕ) : ℝ)
                      * ((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                      / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ)))
                * ((k + 2 : ℝ) * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) ^ k
              < ε_codeg * (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                  * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2))) ∧
          (∀ (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B), a_1 ≠ a_2 → b_1 ≠ b_2 →
              (1 + ε_codeg) * (((candidatePairPartnerSet n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                  * p.toReal ^ (k - 2) * (1 - p.toReal) ^ (k * (k - 1) - 2))
                ≤ δ_PS * expectedDegreeFormula n_A n_B k p.toReal)) ∧
        -- P–S largeness D₀ ≤ μc
        (D₀ ≤ expectedDegreeFormula n_A n_B k p.toReal) ∧
        -- Kim–Vu tail decay (Bonferroni budget)
        (C_kv / ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) ≤ ε / 4) ∧
        -- deltaB-link (h_gap)
        ((n_A : ℝ) * (1 / (k : ℝ) + η) + 1 ≤ (1 - p.toReal / 2) * (n_A : ℝ) * p.toReal) ∧
        -- deltaA-positivity link
        ((1 : ℝ) ≤ (1 - p.toReal / 2) * (n_B : ℝ) * p.toReal)

/-! ### I3c: regime-discharge RESOLVED (2026-06-18) — `asymptotic_regime_BQ_holds`

The predicate was originally FALSE for *unbalanced* sizes (`n_A ≫ n_B`): the two Kim–Vu
threshold clauses have ratio `LHS/RHS = Θ((log(n_A n_B))^k / √(min n_A n_B))`, which → ∞ when
`n_B` is held fixed and `n_A → ∞`. The fix (accepted decision) restricts to the **bounded
aspect-ratio** regime `max n_A n_B ≤ C · min n_A n_B`. Under that guard both sides are
`Θ(min)`-balanced and `LHS/RHS = Θ((log m)^k/√m) → 0` (`m = min n_A n_B`), so the predicate is
now satisfiable and is discharged below as a theorem. The reusable combinatorial substrate —
`candidatePartnerSet_card_le`, `candidatePairPartnerSet_card_le` (A), `expectedDegreeFormula_ge`
/ `meanLowerConst` (B) — plus the analytic cores `log_pow_le_eps_sqrt_eventually` and
`scaled_log_pow_le_eps_sqrt_shift_eventually` (C-core / C-core') and the per-clause lemmas
`c'_threshold_eventually`, `c''_threshold_eventually`, `codeg_arith_eventually` (C) assemble
into `asymptotic_regime_BQ_holds` (E). All standard-axiom clean. -/

/-! ### Sub-lemma D: routine eventual clauses. -/

/-- D-log: both `hN1` log conditions hold for large `min n_A n_B`. -/
lemma log_cond_eventually (k : ℕ) :
    ∃ N₀ : ℕ, ∀ (n_A n_B : ℕ), N₀ ≤ min n_A n_B →
      (1 < (k + 1 : ℝ) * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) ∧
      (1 < (k + 2 : ℝ) * Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) := by
  refine ⟨3, fun n_A n_B hN => ?_⟩
  have hmA : 3 ≤ n_A := le_trans hN (Nat.min_le_left _ _)
  have hmB : 3 ≤ n_B := le_trans hN (Nat.min_le_right _ _)
  have hcard : ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) = ((n_A * n_B : ℕ) : ℝ) := by
    simp [Fintype.card_prod, Fintype.card_fin]
  have hnAnB_pos : (0 : ℝ) < ((n_A * n_B : ℕ) : ℝ) := by
    have : 0 < n_A * n_B := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have h9 : (9 : ℝ) ≤ ((n_A * n_B : ℕ) : ℝ) := by
    have : 9 ≤ n_A * n_B := by nlinarith [hmA, hmB]
    exact_mod_cast this
  have hlog_ge : 2 ≤ Real.log ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) := by
    rw [hcard]
    have hexp2 : Real.exp 2 ≤ ((n_A * n_B : ℕ) : ℝ) := by
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have hlt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      have hpos : 0 < Real.exp 1 := Real.exp_pos 1
      have : Real.exp 2 ≤ (9 : ℝ) := by rw [he2]; nlinarith [hlt, hpos]
      linarith
    exact (Real.le_log_iff_exp_le hnAnB_pos).mpr hexp2
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0:ℝ) ≤ (k:ℝ) := by positivity
    linarith
  constructor
  · nlinarith [hlog_ge, hk1]
  · nlinarith [hlog_ge, hk1]

/-- D-tail: `C_kv / N ≤ ε/4` for large `min n_A n_B` (`N = n_A·n_B → ∞`). -/
lemma tail_decay_eventually {C_kv ε4 : ℝ} (hε4 : 0 < ε4) :
    ∃ N₀ : ℕ, ∀ (n_A n_B : ℕ), N₀ ≤ min n_A n_B →
      C_kv / ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) ≤ ε4 := by
  obtain ⟨Mr, hMr⟩ := exists_nat_ge (C_kv / ε4)
  refine ⟨max Mr 1, fun n_A n_B hN => ?_⟩
  have hmA : max Mr 1 ≤ n_A := le_trans hN (Nat.min_le_left _ _)
  have hmB : max Mr 1 ≤ n_B := le_trans hN (Nat.min_le_right _ _)
  have hMrA : Mr ≤ n_A := le_trans (le_max_left _ _) hmA
  have h1A : 1 ≤ n_A := le_trans (le_max_right _ _) hmA
  have h1B : 1 ≤ n_B := le_trans (le_max_right _ _) hmB
  have hcard : ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) = ((n_A * n_B : ℕ) : ℝ) := by
    simp [Fintype.card_prod, Fintype.card_fin]
  rw [hcard]
  have hN_ge : (C_kv / ε4) ≤ ((n_A * n_B : ℕ) : ℝ) := by
    calc C_kv / ε4 ≤ (Mr : ℝ) := hMr
      _ ≤ (n_A : ℝ) := by exact_mod_cast hMrA
      _ ≤ ((n_A * n_B : ℕ) : ℝ) := by
          push_cast
          nlinarith [(by exact_mod_cast h1B : (1:ℝ) ≤ (n_B:ℝ)),
            (by exact_mod_cast h1A : (1:ℝ) ≤ (n_A:ℝ))]
  have hNpos : (0 : ℝ) < ((n_A * n_B : ℕ) : ℝ) := by
    have : 0 < n_A * n_B := by positivity
    exact_mod_cast this
  rw [div_le_iff₀ hNpos]
  rw [div_le_iff₀ hε4] at hN_ge
  nlinarith [hN_ge, hε4]

/-- D-μc: `D₀ ≤ μc = expectedDegreeFormula …` for large `min n_A n_B` (μc → ∞). -/
lemma mu_c_ge_eventually {p : ℝ} (hp_lb : 0 < p) (hp_ub : p < 1)
    (k : ℕ) (hk : 3 ≤ k) (C : ℝ) (_hC : 1 ≤ C) (D₀ : ℝ) :
    ∃ N₀ : ℕ, ∀ (n_A n_B : ℕ), N₀ ≤ min n_A n_B →
      D₀ ≤ expectedDegreeFormula n_A n_B k p := by
  set u := k - 1 with hu
  have hck_pos : 0 < meanLowerConst k p := meanLowerConst_pos hp_lb hp_ub
  -- μc ≥ c_k·(m-k)^{2u} ≥ c_k·(m/2)^{2u} ≥ c_k·(m/2)^2  (since 2u ≥ 2, m/2 ≥ 1).
  -- it suffices m ≥ 2·max(k, √(D₀/c_k)+1).
  obtain ⟨Mr, hMr⟩ := exists_nat_ge (Real.sqrt (|D₀| / meanLowerConst k p) * 2 + 2 * k + 4)
  refine ⟨max Mr (2 * k + 3), fun n_A n_B hN => ?_⟩
  set m := min n_A n_B with hm
  have hmMr : Mr ≤ m := le_trans (le_max_left _ _) hN
  have hm2k : 2 * k + 3 ≤ m := le_trans (le_max_right _ _) hN
  have hmA : m ≤ n_A := Nat.min_le_left _ _
  have hmB : m ≤ n_B := Nat.min_le_right _ _
  have hkA : k ≤ n_A := le_trans (by omega) hmA
  have hkB : k ≤ n_B := le_trans (by omega) hmB
  have hk_le_m : k ≤ m := by omega
  have hmk_nn : (0 : ℝ) ≤ (m : ℝ) - (k : ℝ) := by
    have : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk_le_m
    linarith
  have hmk_half : (m : ℝ) / 2 ≤ (m : ℝ) - (k : ℝ) := by
    have : (2 : ℝ) * (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 2 * k ≤ m)
    linarith
  have hB := expectedDegreeFormula_ge (n_A := n_A) (n_B := n_B) (k := k) (p := p) hp_lb.le hp_ub.le
  have hbaseA_ge : (m : ℝ) - (k : ℝ) ≤ ((((n_A - 1) + 1 - (k - 1) : ℕ) : ℝ)) := by
    have hnat : m - k ≤ (n_A - 1) + 1 - (k - 1) := by omega
    calc (m : ℝ) - (k : ℝ) ≤ ((m - k : ℕ) : ℝ) := by rw [Nat.cast_sub hk_le_m]
      _ ≤ _ := by exact_mod_cast hnat
  have hbaseB_ge : (m : ℝ) - (k : ℝ) ≤ ((((n_B - 1) + 1 - (k - 1) : ℕ) : ℝ)) := by
    have hnat : m - k ≤ (n_B - 1) + 1 - (k - 1) := by omega
    calc (m : ℝ) - (k : ℝ) ≤ ((m - k : ℕ) : ℝ) := by rw [Nat.cast_sub hk_le_m]
      _ ≤ _ := by exact_mod_cast hnat
  have hμc_ge : meanLowerConst k p * (((m : ℝ) - (k : ℝ)) ^ u * ((m : ℝ) - (k : ℝ)) ^ u)
      ≤ expectedDegreeFormula n_A n_B k p := by
    refine le_trans ?_ hB
    apply mul_le_mul_of_nonneg_left _ hck_pos.le
    apply mul_le_mul (pow_le_pow_left₀ hmk_nn hbaseA_ge u) (pow_le_pow_left₀ hmk_nn hbaseB_ge u)
      (by positivity) (by positivity)
  -- lower bound (m-k)^u·(m-k)^u ≥ (m-k)²  (since u ≥ 1 and m-k ≥ 1).
  have hmk_ge1 : (1 : ℝ) ≤ (m : ℝ) - (k : ℝ) := by
    have : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ m)
    linarith
  have hu1 : 1 ≤ u := by omega
  have hpow_ge : ((m : ℝ) - (k : ℝ)) ^ 2 ≤ ((m : ℝ) - (k : ℝ)) ^ u * ((m : ℝ) - (k : ℝ)) ^ u := by
    rw [← pow_add]
    apply pow_le_pow_right₀ hmk_ge1 (by omega)
  -- D₀ ≤ c_k·(m-k)²  (m-k ≥ m/2 ≥ Mr/2-k ... and Mr ≥ √(|D₀|/c_k)·2 + ...).
  have hD₀_le : D₀ ≤ meanLowerConst k p * ((m : ℝ) - (k : ℝ)) ^ 2 := by
    have hsqrt_le : Real.sqrt (|D₀| / meanLowerConst k p) ≤ (m : ℝ) - (k : ℝ) := by
      have hm_ge : Real.sqrt (|D₀| / meanLowerConst k p) * 2 + 2 * k + 4 ≤ (m : ℝ) :=
        le_trans hMr (by exact_mod_cast hmMr)
      have : (2:ℝ) * (k:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 2 * k ≤ m)
      have hsqrt_nn : 0 ≤ Real.sqrt (|D₀| / meanLowerConst k p) := Real.sqrt_nonneg _
      nlinarith [hm_ge, hmk_half, hsqrt_nn]
    have hsq : |D₀| / meanLowerConst k p ≤ ((m : ℝ) - (k : ℝ)) ^ 2 := by
      have := Real.sq_sqrt (by positivity : (0:ℝ) ≤ |D₀| / meanLowerConst k p)
      nlinarith [hsqrt_le, Real.sqrt_nonneg (|D₀| / meanLowerConst k p), this, hmk_nn]
    rw [div_le_iff₀ hck_pos] at hsq
    calc D₀ ≤ |D₀| := le_abs_self _
      _ ≤ ((m : ℝ) - (k : ℝ)) ^ 2 * meanLowerConst k p := hsq
      _ = meanLowerConst k p * ((m : ℝ) - (k : ℝ)) ^ 2 := by ring
  calc D₀ ≤ meanLowerConst k p * ((m : ℝ) - (k : ℝ)) ^ 2 := hD₀_le
    _ ≤ meanLowerConst k p * (((m : ℝ) - (k : ℝ)) ^ u * ((m : ℝ) - (k : ℝ)) ^ u) := by
        apply mul_le_mul_of_nonneg_left hpow_ge hck_pos.le
    _ ≤ expectedDegreeFormula n_A n_B k p := hμc_ge

/-- D-gap: the `h_gap` link, using the strict margin `1/k + η < b` (here `η = (b-1/k)/2`,
so `b - (1/k+η) = (b-1/k)/2 = η > 0`). -/
lemma gap_link_eventually {p : ℝ} (_hp_lb : 0 < p) (_hp_ub : p < 1)
    (k : ℕ) (_hk : 3 ≤ k) (η : ℝ) (hη_pos : 0 < η)
    (h_margin : 1 / (k : ℝ) + η + η ≤ (1 - p / 2) * p) :
    ∃ N₀ : ℕ, ∀ (n_A n_B : ℕ), N₀ ≤ min n_A n_B →
      (n_A : ℝ) * (1 / (k : ℝ) + η) + 1 ≤ (1 - p / 2) * (n_A : ℝ) * p := by
  obtain ⟨Mr, hMr⟩ := exists_nat_ge (1 / η)
  refine ⟨max Mr 1, fun n_A n_B hN => ?_⟩
  have hmA : max Mr 1 ≤ n_A := le_trans hN (Nat.min_le_left _ _)
  have hMrA : Mr ≤ n_A := le_trans (le_max_left _ _) hmA
  have h1A : 1 ≤ n_A := le_trans (le_max_right _ _) hmA
  have hnA_ge : 1 / η ≤ (n_A : ℝ) := le_trans hMr (by exact_mod_cast hMrA)
  have hnA_pos : (0 : ℝ) < (n_A : ℝ) := by exact_mod_cast (by omega : 0 < n_A)
  -- n_A·η ≥ 1.
  have hkey : 1 ≤ (n_A : ℝ) * η := by
    rw [div_le_iff₀ hη_pos] at hnA_ge; linarith
  -- (1-p/2)·n_A·p - n_A·(1/k+η) = n_A·(b - 1/k - η) ≥ n_A·η ≥ 1.
  have : (1 - p / 2) * (n_A : ℝ) * p - ((n_A : ℝ) * (1 / (k : ℝ) + η))
      = (n_A : ℝ) * ((1 - p / 2) * p - (1 / (k : ℝ) + η)) := by ring
  nlinarith [hkey, h_margin, hnA_pos, mul_le_mul_of_nonneg_left h_margin hnA_pos.le]

/-- D-dA: the `deltaA`-positivity link `1 ≤ (1-p/2)·n_B·p` for large `min n_A n_B`. -/
lemma dA_pos_eventually {p : ℝ} (hp_lb : 0 < p) (hp_ub : p < 1) :
    ∃ N₀ : ℕ, ∀ (n_A n_B : ℕ), N₀ ≤ min n_A n_B →
      (1 : ℝ) ≤ (1 - p / 2) * (n_B : ℝ) * p := by
  set q : ℝ := (1 - p / 2) * p with hq
  have hq_pos : 0 < q := by
    rw [hq]; have h12 : (0:ℝ) < 1 - p / 2 := by linarith
    positivity
  obtain ⟨Mr, hMr⟩ := exists_nat_ge (1 / q)
  refine ⟨max Mr 1, fun n_A n_B hN => ?_⟩
  have hmB : max Mr 1 ≤ n_B := le_trans hN (Nat.min_le_right _ _)
  have hMrB : Mr ≤ n_B := le_trans (le_max_left _ _) hmB
  have hnB_ge : 1 / q ≤ (n_B : ℝ) := le_trans hMr (by exact_mod_cast hMrB)
  rw [div_le_iff₀ hq_pos] at hnB_ge
  calc (1 : ℝ) ≤ (n_B : ℝ) * q := by linarith
    _ = (1 - p / 2) * (n_B : ℝ) * p := by rw [hq]; ring

/-- **E: discharge of `asymptotic_regime_BQ` under the bounded aspect-ratio guard.**
For any fixed `p ∈ (0,1)` and aspect constant `C ≥ 1`, the balanced-asymptotic predicate
`asymptotic_regime_BQ (ENNReal.ofReal p) hp_le C hC` is *true* — proved, not assumed.
Standard Lean axioms only. -/
theorem asymptotic_regime_BQ_holds (p : ℝ) (hp_lb : 0 < p) (hp_ub : p < 1)
    (C : ℝ) (hC : 1 ≤ C) :
    ∀ (hp_le : ENNReal.ofReal p ≤ 1),
      asymptotic_regime_BQ (ENNReal.ofReal p) hp_le C hC := by
  intro hp_le
  have hpR : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp_lb.le
  -- the positive "k-budget"  b := (1 - p/2)·p > 0.
  set b : ℝ := (1 - p / 2) * p with hb
  have hb_pos : 0 < b := by
    rw [hb]; have h12 : (0:ℝ) < 1 - p / 2 := by linarith
    positivity
  -- choose k ≥ 3 with 1/k < b  (strict), via k > 1/b.
  obtain ⟨kr, hkr⟩ := exists_nat_gt (1 / b)
  set k : ℕ := max 3 (kr + 1) with hk_def
  have hk3 : 3 ≤ k := le_max_left _ _
  have hk_pos : 0 < (k : ℝ) := by positivity
  have hk_gt : 1 / b < (k : ℝ) := by
    have hlt : (kr : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : kr < k)
    linarith
  have hinvk_lt_b : 1 / (k : ℝ) < b := by
    have hbk : 1 < b * (k : ℝ) := by rw [div_lt_iff₀ hb_pos] at hk_gt; linarith
    rw [div_lt_iff₀ hk_pos]; linarith
  set η : ℝ := (b - 1 / (k : ℝ)) / 2 with hη_def
  have hη_pos : 0 < η := by rw [hη_def]; linarith
  have h_margin : 1 / (k : ℝ) + η + η ≤ b := by rw [hη_def]; linarith
  have h_k_link : 1 / (k : ℝ) + η
      ≤ (1 - (ENNReal.ofReal p).toReal / 2) * (ENNReal.ofReal p).toReal := by
    rw [hpR, ← hb, hη_def]; linarith
  refine ⟨k, η, hk3, hη_pos, h_k_link, ?_⟩
  intro δ_PS hδ_PS D₀ C_kv _hC_kv ε hε
  obtain ⟨Nc', hNc'⟩ := c'_threshold_eventually hp_lb hp_ub k hk3 C hC hδ_PS
  obtain ⟨Nc'', hNc''⟩ := c''_threshold_eventually hp_lb hp_ub k hk3 C hC
  obtain ⟨Narith, hNarith⟩ := codeg_arith_eventually hp_lb hp_ub k hk3 C hC hδ_PS
  obtain ⟨ND₀, hND₀⟩ := mu_c_ge_eventually hp_lb hp_ub k hk3 C hC D₀
  obtain ⟨Ntail, hNtail⟩ := tail_decay_eventually (C_kv := C_kv) (by linarith : 0 < ε / 4)
  obtain ⟨Nlog, hNlog⟩ := log_cond_eventually k
  obtain ⟨Ngap, hNgap⟩ := gap_link_eventually hp_lb hp_ub k hk3 η hη_pos
    (by rw [← hb]; exact h_margin)
  obtain ⟨NdA, hNdA⟩ := dA_pos_eventually hp_lb hp_ub
  refine ⟨max (max (max Nc' Nc'') (max Narith ND₀))
            (max (max Ntail Nlog) (max (max Ngap NdA) k)),
    fun n_A n_B hN h_aspect => ?_⟩
  -- distribute the big threshold.
  have hNc'_le : Nc' ≤ min n_A n_B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hN)
  have hNc''_le : Nc'' ≤ min n_A n_B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) hN)
  have hNarith_le : Narith ≤ min n_A n_B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hN)
  have hND₀_le : ND₀ ≤ min n_A n_B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_trans (le_max_left _ _) hN)
  have hNtail_le : Ntail ≤ min n_A n_B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) hN)
  have hNlog_le : Nlog ≤ min n_A n_B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) hN)
  have hNgap_le : Ngap ≤ min n_A n_B := le_trans
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _))
    (le_trans (le_max_right _ _) hN)
  have hNdA_le : NdA ≤ min n_A n_B := le_trans
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _))
    (le_trans (le_max_right _ _) hN)
  have hk_le : k ≤ min n_A n_B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_trans (le_max_right _ _) hN)
  have hkA : k ≤ n_A := le_trans hk_le (Nat.min_le_left _ _)
  have hkB : k ≤ n_B := le_trans hk_le (Nat.min_le_right _ _)
  obtain ⟨hlog1, hlog2⟩ := hNlog n_A n_B hNlog_le
  refine ⟨⟨hkA, hkB⟩, hlog1, hlog2, ?_, ⟨1, by norm_num, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- c'
    rw [hpR]; exact hNc' n_A n_B hNc'_le h_aspect
  · -- c'' threshold
    rw [hpR]; exact hNc'' n_A n_B hNc''_le h_aspect
  · -- codeg arithmetic
    rw [hpR]; exact hNarith n_A n_B hNarith_le h_aspect
  · -- D₀ ≤ μc
    rw [hpR]; exact hND₀ n_A n_B hND₀_le
  · -- tail decay
    exact hNtail n_A n_B hNtail_le
  · -- gap link
    rw [hpR]; exact hNgap n_A n_B hNgap_le
  · -- deltaA positivity
    rw [hpR]; exact hNdA n_A n_B hNdA_le

end DaveyThesis2024.SecRandomBipartite.PippengerSpencer

/-! ## Axiom hygiene check -/

section AxiomCheck
open DaveyThesis2024.SecRandomBipartite.PippengerSpencer
#print axioms candidatePartnerSet_card_le
#print axioms candidatePairPartnerSet_card_le
#print axioms expectedDegreeFormula_ge
#print axioms meanLowerConst_pos
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.asymptotic_regime_BQ_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms asymptotic_regime_BQ_holds
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.mem_inducedKMatchings_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms mem_inducedKMatchings_iff
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.SCIHypergraph_k_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SCIHypergraph_k_uniform
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.SCIHypergraph_k_subset_cross' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SCIHypergraph_k_subset_cross
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.SCIHypergraph_k_isInducedMatching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SCIHypergraph_k_isInducedMatching
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.expectedDegreeFormula_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms expectedDegreeFormula_nonneg
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.expectedCodegreeFormula_nonneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms expectedCodegreeFormula_nonneg
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.codegree_zero_shared_A' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms codegree_zero_shared_A
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.codegree_zero_shared_B' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms codegree_zero_shared_B
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.codegree_zero_bridge_a1b2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms codegree_zero_bridge_a1b2
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.codegree_zero_bridge_a2b1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms codegree_zero_bridge_a2b1
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.choose_pascal_pred' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms choose_pascal_pred
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.choose_pascal_pred_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms choose_pascal_pred_real
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.factorial_pred_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms factorial_pred_eq
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.pow_p_kmin1_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pow_p_kmin1_split
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.pow_one_sub_p_kmin1_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pow_one_sub_p_kmin1_split
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.ratio_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ratio_identity
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatching_erase_insert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms inducedKMatching_erase_insert
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatching_erase_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms inducedKMatching_erase_card
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings_filter_mem_image_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms inducedKMatchings_filter_mem_image_erase
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.validErasePartner_A_coord_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms validErasePartner_A_coord_ne
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.validErasePartner_B_coord_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms validErasePartner_B_coord_ne
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.validErasePartner_A_coords_inj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms validErasePartner_A_coords_inj
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.validErasePartner_B_coords_inj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms validErasePartner_B_coords_inj
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.mem_candidatePartnerSet_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms mem_candidatePartnerSet_iff
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.slot_supp_count_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms slot_supp_count_le
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.matchingIndicator_eq_zero_or_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms matchingIndicator_eq_zero_or_one
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.count_mul_indicator_eq_sum_matchingIndicator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms count_mul_indicator_eq_sum_matchingIndicator
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.matchingIndicator_eq_zero_of_not_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms matchingIndicator_eq_zero_of_not_candidate
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.integral_matchingIndicator_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms integral_matchingIndicator_eq
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.candidatePartnerSet_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms candidatePartnerSet_card
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.expectation_inducedKMatchings_with_edge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms expectation_inducedKMatchings_with_edge
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatching_erase_pair_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms inducedKMatching_erase_pair_card
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings_filter_mem_pair_image_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms inducedKMatchings_filter_mem_pair_image_erase
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.mem_candidatePairPartnerSet_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms mem_candidatePairPartnerSet_iff
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.e1_e2_notMem_of_candidatePair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms e1_e2_notMem_of_candidatePair
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.matchingPairIndicator_eq_zero_or_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms matchingPairIndicator_eq_zero_or_one
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.count_pair_mul_indicator_eq_sum_matchingPairIndicator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms count_pair_mul_indicator_eq_sum_matchingPairIndicator
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.matchingPairIndicator_eq_zero_of_not_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms matchingPairIndicator_eq_zero_of_not_candidate
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.presentSlotsPair_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms presentSlotsPair_card
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.absentSlotsPair_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms absentSlotsPair_card
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.presentSlotsPair_disjoint_absentSlotsPair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms presentSlotsPair_disjoint_absentSlotsPair
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.matchingPairIndicator_eq_product_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms matchingPairIndicator_eq_product_form
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.integral_matchingPairIndicator_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms integral_matchingPairIndicator_eq
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.candidatePairPartnerSet_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms candidatePairPartnerSet_card
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.expectation_inducedKMatchings_with_edge_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms expectation_inducedKMatchings_with_edge_pair
/--
info: 'DaveyThesis2024.SecRandomBipartite.PippengerSpencer.dPolyDegree_pos' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms dPolyDegree_pos
end AxiomCheck
