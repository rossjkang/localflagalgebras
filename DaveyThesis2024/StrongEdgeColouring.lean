import DaveyThesis2024.Basic
import DaveyThesis2024.LocalFlagAlgebra
import DaveyThesis2024.PentagonConjecture
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Davey 2024: Application — Strong Edge Colouring (Chapter 4)

Formalisation of Chapter 4 of Eoin Davey's MSc thesis
"Local Flags: Bounding the Strong Chromatic Index" (UvA, 2024).

The main results are improved bounds on the strong chromatic index:

* `strong_chromatic_index_bound` — Theorem 4.1: χ'_s(G) ≤ 1.73·Δ(G)² for large Δ(G)
* `strong_chromatic_index_bipartite` — Theorem 4.9: χ'_s(G) ≤ 1.6254·Δ(G)² for bipartite G

The proof uses a 2-step strategy (Molloy-Reed 1997):
1. Bound the strong neighbourhood density using local flags + SDP
2. Apply a probabilistic colouring lemma (Hurley-de Joannis de Verclos-Kang 2022)

## Historical context

| Year | Authors | Bound |
|------|---------|-------|
| 1997 | Molloy, Reed | 1.998Δ² |
| 2015 | Bruhn, Joos | 1.93Δ² |
| 2018 | Bonamy, Perrett, Postle | 1.835Δ² |
| 2022 | Hurley, de Joannis de Verclos, Kang | 1.772Δ² |
| 2024 | Davey | 1.73Δ² |

## References

* E. Davey, "Local Flags: Bounding the Strong Chromatic Index", MSc thesis, UvA, 2024.
* M. Molloy, B. Reed, "A Bound on the Strong Chromatic Index", J. Combin. Theory B, 1997.
* S. Bruhn, F. Joos, "A Stronger Bound for the Strong Chromatic Index", CPC, 2018.
* C. Bonamy, N. Perrett, L. Postle, "Colouring Graphs with Sparse Neighbourhoods", JCTB, 2018.
* T. Hurley, R. de Joannis de Verclos, R. Kang, "An Improved Procedure for Colouring...", 2022.
-/

open Finset BigOperators Nat Classical in
noncomputable section

set_option linter.unusedSectionVars false

namespace Davey2024

/-! ## §4.0: Degree Bound Helpers -/

/-- Each vertex's degree is at most `maxDegree G`. -/
lemma degree_le_maxDegree (G : Flag emptyType) (v : Fin G.size) :
    (Finset.univ.filter (fun u => G.graph.Adj v u)).card ≤ maxDegree G :=
  @Finset.le_sup ℕ (Fin G.size) _ _ Finset.univ
    (fun w => (Finset.univ.filter (fun w' => G.graph.Adj w w')).card)
    v (Finset.mem_univ _)

/-- The number of directed edges incident to a vertex v is at most 2·Δ(G).
    Each incident edge (a,b) with Adj a b satisfies a = v or b = v,
    giving at most deg(v) + deg(v) ≤ 2Δ directed edges. -/
lemma incident_edges_le (G : Flag emptyType) (v : Fin G.size) :
    ((Finset.univ : Finset (Fin G.size × Fin G.size)).filter fun e =>
      G.graph.Adj e.1 e.2 ∧ (e.1 = v ∨ e.2 = v)).card ≤ 2 * maxDegree G := by
  have hsub : (Finset.univ.filter fun e : Fin G.size × Fin G.size =>
      G.graph.Adj e.1 e.2 ∧ (e.1 = v ∨ e.2 = v)) ⊆
    (Finset.univ.filter fun e : Fin G.size × Fin G.size =>
      G.graph.Adj e.1 e.2 ∧ e.1 = v) ∪
    (Finset.univ.filter fun e : Fin G.size × Fin G.size =>
      G.graph.Adj e.1 e.2 ∧ e.2 = v) := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at he ⊢
    exact he.2.elim (fun h => .inl ⟨he.1, h⟩) (fun h => .inr ⟨he.1, h⟩)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ + _ := Finset.card_union_le _ _
    _ ≤ maxDegree G + maxDegree G := by
        apply Nat.add_le_add
        · exact le_trans (Finset.card_le_card_of_injOn Prod.snd
            (fun ⟨a, b⟩ he => by
              obtain ⟨_, hadj, heq⟩ := Finset.mem_filter.mp he
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq ▸ hadj⟩)
            (fun ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq => Prod.ext
              ((Finset.mem_filter.mp h₁).2.2.trans (Finset.mem_filter.mp h₂).2.2.symm) heq))
            (degree_le_maxDegree G v)
        · exact le_trans (Finset.card_le_card_of_injOn Prod.fst
            (fun ⟨a, b⟩ he => by
              obtain ⟨_, hadj, heq⟩ := Finset.mem_filter.mp he
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq ▸ G.graph.symm hadj⟩)
            (fun ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq => Prod.ext heq
              ((Finset.mem_filter.mp h₁).2.2.trans (Finset.mem_filter.mp h₂).2.2.symm)))
            (degree_le_maxDegree G v)
    _ = 2 * maxDegree G := by ring

/-- Directed edges sharing an endpoint with edge (u,v) total at most 4Δ. -/
lemma incident_to_edge_le (G : Flag emptyType) (u v : Fin G.size) :
    ((Finset.univ : Finset (Fin G.size × Fin G.size)).filter fun e' =>
      G.graph.Adj e'.1 e'.2 ∧
      (e'.1 = u ∨ e'.1 = v ∨ e'.2 = u ∨ e'.2 = v)).card
    ≤ 4 * maxDegree G := by
  have hsub : (Finset.univ.filter fun e' : Fin G.size × Fin G.size =>
      G.graph.Adj e'.1 e'.2 ∧ (e'.1 = u ∨ e'.1 = v ∨ e'.2 = u ∨ e'.2 = v)) ⊆
    (Finset.univ.filter fun e' : Fin G.size × Fin G.size =>
      G.graph.Adj e'.1 e'.2 ∧ (e'.1 = u ∨ e'.2 = u)) ∪
    (Finset.univ.filter fun e' : Fin G.size × Fin G.size =>
      G.graph.Adj e'.1 e'.2 ∧ (e'.1 = v ∨ e'.2 = v)) := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at he ⊢
    obtain ⟨hadj, h⟩ := he
    rcases h with h | h | h | h
    · left; exact ⟨hadj, Or.inl h⟩
    · right; exact ⟨hadj, Or.inl h⟩
    · left; exact ⟨hadj, Or.inr h⟩
    · right; exact ⟨hadj, Or.inr h⟩
  calc ((Finset.univ.filter fun e' : Fin G.size × Fin G.size =>
        G.graph.Adj e'.1 e'.2 ∧ (e'.1 = u ∨ e'.1 = v ∨ e'.2 = u ∨ e'.2 = v)).card)
      ≤ ((Finset.univ.filter fun e' : Fin G.size × Fin G.size =>
          G.graph.Adj e'.1 e'.2 ∧ (e'.1 = u ∨ e'.2 = u)) ∪
        (Finset.univ.filter fun e' : Fin G.size × Fin G.size =>
          G.graph.Adj e'.1 e'.2 ∧ (e'.1 = v ∨ e'.2 = v))).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter fun e' : Fin G.size × Fin G.size =>
          G.graph.Adj e'.1 e'.2 ∧ (e'.1 = u ∨ e'.2 = u)).card +
        (Finset.univ.filter fun e' : Fin G.size × Fin G.size =>
          G.graph.Adj e'.1 e'.2 ∧ (e'.1 = v ∨ e'.2 = v)).card := Finset.card_union_le _ _
    _ ≤ 2 * maxDegree G + 2 * maxDegree G := by
        apply Nat.add_le_add <;> exact incident_edges_le G _
    _ = 4 * maxDegree G := by ring

/-- For Δ ≥ 1, 4Δ ≤ 4Δ³. -/
private lemma four_delta_le_four_delta_cubed {Δ : ℕ} (h : 1 ≤ Δ) :
    4 * Δ ≤ 4 * Δ ^ 3 := by
  have : Δ ≤ Δ ^ 3 := le_self_pow₀ (by omega) (by omega)
  omega

/-- A graph with an edge has maxDegree ≥ 1. -/
lemma maxDegree_pos_of_adj (G : Flag emptyType) (u v : Fin G.size)
    (hadj : G.graph.Adj u v) : 1 ≤ maxDegree G :=
  le_trans (Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩⟩)
    (degree_le_maxDegree G u)

/-! ## §4.1: Strong Edge Colouring — Definitions -/

/-- A **strong edge colouring** of a graph G is an edge colouring where any two edges
    that share a common incident edge receive different colours. Equivalently, it is
    a proper vertex colouring of L(G)², the square of the line graph. -/
def IsStrongEdgeColouring {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (c : (Fin n × Fin n) → ℕ) -- colouring of ordered pairs (representing edges)
    : Prop :=
  -- Symmetric: c(u,v) = c(v,u) for edges
  (∀ u v : Fin n, G.Adj u v → c (u,v) = c (v,u)) ∧
  -- Strong property: if e₁, e₂ share a common incident edge, they get different colours.
  -- Two edges are at distance ≤ 2 in L(G) iff there exists an edge sharing an
  -- endpoint with both (which includes the edges themselves when they share an endpoint).
  (∀ u₁ v₁ u₂ v₂ : Fin n,
    G.Adj u₁ v₁ → G.Adj u₂ v₂ → (u₁, v₁) ≠ (u₂, v₂) → (u₁, v₁) ≠ (v₂, u₂) →
    (∃ a b : Fin n, G.Adj a b ∧
      (a = u₁ ∨ a = v₁ ∨ b = u₁ ∨ b = v₁) ∧
      (a = u₂ ∨ a = v₂ ∨ b = u₂ ∨ b = v₂)) →
    c (u₁, v₁) ≠ c (u₂, v₂))

/-- The **strong chromatic index** χ'_s(G): the minimum number of colours needed
    for a strong edge colouring of G. Defined as the infimum of the set of k such
    that there exists a strong edge colouring using colours in {0, ..., k-1}. -/
noncomputable def strongChromaticIndex (G : Flag emptyType) : ℕ :=
  sInf {k : ℕ | ∃ c : Fin G.size × Fin G.size → ℕ,
    IsStrongEdgeColouring G.graph c ∧
    ∀ u v : Fin G.size, G.graph.Adj u v → c (u, v) < k}

/-- The **strong neighbourhood** of an edge e in G: the set of edges e' such that
    e and e' are at distance ≤ 2 in the line graph L(G). Equivalently, e' shares
    a common incident edge with e. Counts directed edge pairs (u',v') with u' < v'
    that are distinct from e and share a common incident vertex with e. -/
noncomputable def strongNeighbourhoodSize (G : Flag emptyType)
    (e : Fin G.size × Fin G.size) : ℕ :=
  ((Finset.univ : Finset (Fin G.size × Fin G.size)).filter fun e' =>
    G.graph.Adj e'.1 e'.2 ∧ (e'.1, e'.2) ≠ (e.1, e.2) ∧
    ∃ w : Fin G.size,
      (G.graph.Adj e.1 w ∨ G.graph.Adj e.2 w) ∧
      (G.graph.Adj e'.1 w ∨ G.graph.Adj e'.2 w)).card

/-! ## §4.1a: Basic Graph Definitions -/

/-- The **chromatic number** χ(G): the minimum number of colours for a proper
    vertex colouring of G. Defined as the infimum of k such that there exists
    a proper k-colouring (each vertex gets a colour in {0,...,k-1}, adjacent
    vertices get different colours). -/
noncomputable def chromaticNumber (G : Flag emptyType) : ℕ :=
  sInf {k : ℕ | ∃ c : Fin G.size → ℕ,
    (∀ u v : Fin G.size, G.graph.Adj u v → c u ≠ c v) ∧
    ∀ v : Fin G.size, c v < k}

/-- The count of **edges in the neighbourhood** of a vertex v in G:
    |E(G[N(v)])| = number of edges between neighbours of v.
    This is the key quantity in the colouring lemma. -/
noncomputable def edgesInNeighbourhood (G : Flag emptyType) (v : Fin G.size) : ℕ :=
  let nbrs := (Finset.univ : Finset (Fin G.size)).filter (fun u => G.graph.Adj v u)
  ((nbrs ×ˢ nbrs).filter (fun p => p.1 < p.2 ∧ G.graph.Adj p.1 p.2)).card

/-! ## §4.1b: Line Graph and Square -/

/-- The **edge set** of a graph G as a finset of ordered pairs (u,v) with u < v. -/
noncomputable def edgeFinset (G : Flag emptyType) : Finset (Fin G.size × Fin G.size) :=
  (Finset.univ : Finset (Fin G.size × Fin G.size)).filter fun e => G.graph.Adj e.1 e.2 ∧ e.1 < e.2

/-- The **line graph** L(G) has the edges of G as vertices, with two edges
    adjacent in L(G) iff they share a common endpoint.
    We represent L(G) as a `SimpleGraph` on the canonical edge set (u < v). -/
noncomputable def lineGraphAdj (G : Flag emptyType)
    (e₁ e₂ : Fin G.size × Fin G.size) : Prop :=
  G.graph.Adj e₁.1 e₁.2 ∧ G.graph.Adj e₂.1 e₂.2 ∧
  e₁ ≠ e₂ ∧
  (e₁.1 = e₂.1 ∨ e₁.1 = e₂.2 ∨ e₁.2 = e₂.1 ∨ e₁.2 = e₂.2)

/-- L(G) adjacency is symmetric. -/
lemma lineGraphAdj_symm (G : Flag emptyType) (e₁ e₂ : Fin G.size × Fin G.size) :
    lineGraphAdj G e₁ e₂ → lineGraphAdj G e₂ e₁ := by
  intro ⟨h1, h2, hne, hshare⟩
  refine ⟨h2, h1, Ne.symm hne, ?_⟩
  rcases hshare with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inr h.symm))

/-- L(G) adjacency is irreflexive.

    **Status**: Intentional standalone — foundational fact about L(G);
    no consumer expected. -/
lemma lineGraphAdj_irrefl (G : Flag emptyType) (e : Fin G.size × Fin G.size) :
    ¬lineGraphAdj G e e := by
  intro ⟨_, _, hne, _⟩; exact hne rfl

/-- The **squared line graph** L(G)² has edges of G as vertices, with two edges
    adjacent in L(G)² iff they are at distance ≤ 2 in L(G). Equivalently,
    e₁ and e₂ are adjacent in L(G)² iff there exists an edge e₃ sharing an
    endpoint with both e₁ and e₂ (or e₁, e₂ share an endpoint directly).

    This is the graph whose chromatic number equals the strong chromatic index. -/
noncomputable def lineGraphSqAdj (G : Flag emptyType)
    (e₁ e₂ : Fin G.size × Fin G.size) : Prop :=
  G.graph.Adj e₁.1 e₁.2 ∧ G.graph.Adj e₂.1 e₂.2 ∧
  e₁ ≠ e₂ ∧ e₁ ≠ (e₂.2, e₂.1) ∧
  -- Distance ≤ 2 in L(G): share an endpoint OR share a common incident edge
  (lineGraphAdj G e₁ e₂ ∨
   ∃ e₃ : Fin G.size × Fin G.size,
     G.graph.Adj e₃.1 e₃.2 ∧ lineGraphAdj G e₁ e₃ ∧ lineGraphAdj G e₃ e₂)

/-- L(G)² adjacency is symmetric. -/
lemma lineGraphSqAdj_symm (G : Flag emptyType) (e₁ e₂ : Fin G.size × Fin G.size) :
    lineGraphSqAdj G e₁ e₂ → lineGraphSqAdj G e₂ e₁ := by
  intro ⟨h1, h2, hne, hne_rev, hconn⟩
  refine ⟨h2, h1, Ne.symm hne, fun h => hne_rev (by
    rw [Prod.ext_iff] at h ⊢; exact ⟨h.2.symm, h.1.symm⟩), ?_⟩
  rcases hconn with h | ⟨e₃, he₃, h13, h32⟩
  · exact Or.inl (lineGraphAdj_symm G _ _ h)
  · exact Or.inr ⟨e₃, he₃, lineGraphAdj_symm G _ _ h32, lineGraphAdj_symm G _ _ h13⟩

-- **Line Graph Equivalence** (Thesis §4.1):
-- A strong edge colouring of G is exactly a proper vertex colouring of L(G)².
-- Hence χ'_s(G) = χ(L(G)²).

/-- **Forward direction**: A strong edge colouring induces a proper colouring of L(G)².

    **Status**: Intentional standalone — Thesis §5.1 line-graph
    equivalence (forward direction); no consumer expected (the chain
    uses `strongChromaticIndex_le_lineGraphSq` directly). -/
theorem strong_to_line_graph_sq_colouring (G : Flag emptyType)
    (c : Fin G.size × Fin G.size → ℕ) [DecidableRel G.graph.Adj]
    (hstrong : IsStrongEdgeColouring G.graph c) :
    ∀ e₁ e₂ : Fin G.size × Fin G.size,
      lineGraphSqAdj G e₁ e₂ → c e₁ ≠ c e₂ := by
  intro e₁ e₂ ⟨hadj₁, hadj₂, hne, hne_rev, hconn⟩
  apply hstrong.2 e₁.1 e₁.2 e₂.1 e₂.2 hadj₁ hadj₂ hne hne_rev
  rcases hconn with ⟨_, _, _, hshare⟩ | ⟨e₃, he₃, ⟨_, _, _, hshare₁⟩, ⟨_, _, _, hshare₂⟩⟩
  · exact ⟨e₁.1, e₁.2, hadj₁, Or.inl rfl, by tauto⟩
  · exact ⟨e₃.1, e₃.2, he₃, by tauto, by tauto⟩

/-- A graph is **bipartite** if its vertex set can be partitioned into two
    independent sets. -/
def IsBipartite (G : Flag emptyType) : Prop :=
  ∃ (S : Finset (Fin G.size)),
    ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S)

/-- **Conjecture (Erdos-Nesetril, 1985)**: χ'_s(G) ≤ 1.25·Δ(G)² for all graphs G.
    This remains open. The best known bound is 2Δ² for small Δ. -/
def ErdosNesetrilConjecture : Prop :=
  ∀ G : Flag emptyType,
    (strongChromaticIndex G : ℝ) ≤ 1.25 * (maxDegree G : ℝ) ^ 2

/-- **Faudree et al. Conjecture (1989)**: χ'_s(G) ≤ Δ(G)² for bipartite G. -/
def BipartiteStrongColouringConjecture : Prop :=
  ∀ G : Flag emptyType, IsBipartite G →
    (strongChromaticIndex G : ℝ) ≤ (maxDegree G : ℝ) ^ 2

/-! ## §4.3: The 2-Step Strategy (Molloy-Reed 1997)

The proof follows the 2-step strategy introduced by Molloy and Reed:
1. Bound the strong neighbourhood density
2. Apply a probabilistic colouring lemma -/

/-! ## §4.3a: The Colouring Function ε(σ) -/

/-- The **sparsity improvement function** ε(σ) = σ/2 - σ·√σ/6 from the
    Hurley-de Joannis de Verclos-Kang colouring lemma (Theorem 1.2, 2022).
    If a graph has max degree X and every vertex neighbourhood has at most
    (1-σ)·C(X,2) edges, then χ(G) ≤ (1 - ε(σ) + ι)·X for any ι > 0
    and X large enough. -/
noncomputable def colouringEps (sigma : ℝ) : ℝ :=
  sigma / 2 - sigma * Real.sqrt sigma / 6

/-- ε(σ) ≥ 0 for σ ∈ [0, 1]: since √σ ≤ 1, we have σ·√σ/6 ≤ σ/6 ≤ σ/2.

    **Status**: Intentional standalone — foundational arithmetic fact
    about `colouringEps`; no consumer expected. -/
lemma colouringEps_nonneg {sigma : ℝ} (h0 : 0 ≤ sigma) (h1 : sigma ≤ 1) :
    0 ≤ colouringEps sigma := by
  unfold colouringEps
  have hsqrt : Real.sqrt sigma ≤ 1 := Real.sqrt_le_one.mpr h1
  have hsqrt_nn : 0 ≤ Real.sqrt sigma := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hsqrt h0]

/-- ε(σ) ≤ σ/3: a useful lower bound for the colouring improvement.
    Since √σ ≤ 1 for σ ∈ [0,1], we have σ·√σ/6 ≤ σ/6, so ε ≥ σ/2 - σ/6 = σ/3.

    **Status**: Intentional standalone — foundational lower bound for
    `colouringEps`; no consumer expected. -/
lemma colouringEps_ge_third {sigma : ℝ} (h0 : 0 ≤ sigma) (h1 : sigma ≤ 1) :
    sigma / 3 ≤ colouringEps sigma := by
  unfold colouringEps
  have hsqrt : Real.sqrt sigma ≤ 1 := Real.sqrt_le_one.mpr h1
  nlinarith [mul_le_mul_of_nonneg_left hsqrt h0]

/-! ## §4.3b: The Colouring Lemma (Hurley, de Joannis de Verclos, Kang 2022) -/

/-- **σ-sparse local-density colouring lemma** (Hurley–de Joannis de Verclos–Kang 2022,
    arXiv:2007.07874 / SODA 2021; theorem `col_result`, the headline σ-sparse colouring bound).
    Verbatim transcription: `G` is *σ-sparse* if for every vertex `v` the subgraph `G[N(v)]` spans at most
    `(1-σ)·C(Δ(G),2)` edges (HJK §1 definition); then for every `0 < σ ≤ 1` and `ι > 0` there is `Δ₀` such
    that every σ-sparse `G` with `Δ(G) ≥ Δ₀` satisfies `χ(G) ≤ (1 - ε(σ) + ι)·Δ(G)`, where
    `ε(σ) = σ/2 - σ^{3/2}/6 = colouringEps σ`. Here `edgesInNeighbourhood G v = |E(G[N(v)])|`. The SEC
    application follows HJK's own route: verify `L(G)²` is σ-sparse (via the SDP bound) and apply this lemma. -/
axiom hurley_colouring_lemma (sigma iota : ℝ)
    (hsigma : 0 < sigma) (hsigma1 : sigma ≤ 1) (hiota : 0 < iota) :
    ∃ X₀ : ℕ, ∀ G : Flag emptyType,
      X₀ ≤ maxDegree G →
      (∀ v : Fin G.size, (edgesInNeighbourhood G v : ℝ) ≤
        (1 - sigma) * (Nat.choose (maxDegree G) 2 : ℝ)) →
      (chromaticNumber G : ℝ) ≤ (1 - colouringEps sigma + iota) * (maxDegree G : ℝ)

/-- **Step 1: Strong Neighbourhood Density Bound.**
    For any graph G with maximum degree Δ, the strong neighbourhood density of any
    edge is bounded. The SDP yields φ(O) ≤ 10.644, and the objective interpretation
    gives |E_O(G')|/Δ⁴ ≤ 10.644/8 = 1.3305 asymptotically. -/
noncomputable def strongNeighbourhoodDensityBound : ℝ := 10.644 / 8

-- **Step 2: Application of the Colouring Lemma.**
-- The colouring lemma (`hurley_colouring_lemma`) is applied with:
-- - H = L(G)² (the squared line graph), X = Δ(H) ≈ 2Δ(G)²
-- - σ = secSparsity = 1 - secDensityBound/16 ≈ 0.33475, ε(σ) ≈ 0.13510
-- This gives χ(H) ≤ (1 - ε(σ) + ι)·2Δ² ≈ (1.72981 + ι)Δ² for any ι > 0.
-- The all-vertex sparsity hypothesis is supplied by `sec_vertex_sparsity`.
-- See `hurley_colouring_lemma`.

/-! ## §4.3: Reduction to Coloured Graphs

The strong neighbourhood density problem reduces to bounding edge pair counts
in a (2,2)-coloured graph (red/black vertices + red/black edges). -/

/-- A **(2,2)-coloured graph**: a graph with both vertex colours (red/black) and
    edge colours (red/black). Used to model the strong edge colouring reduction. -/
structure ColouredGraph22 where
  graph : Flag emptyType
  vertexColour : Fin graph.size → Fin 2  -- 0=red, 1=black
  edgeColour : Fin graph.size → Fin graph.size → Fin 2  -- 0=red, 1=black
  edgeSymm : ∀ u v, edgeColour u v = edgeColour v u

/-- **Lemma (Non-incident pairs dominate, §4.3 Lemma 1)**:
    The number of edges in H[N_{H[F]}(f)] that correspond to non-incident
    edge pairs dominates the total. Incident pairs contribute O(Δ³) = o(Δ⁴).

    More precisely: |N_s(f)| ∈ O(Δ²) and each edge has O(Δ) incident edges,
    giving O(Δ³) incident pairs vs Θ(Δ⁴) non-incident pairs.

    **Status**: Intentional standalone — Thesis Ch 5 Lemma 4.2
    (`count_non_incident_pairs`); no consumer expected (the SDP chain
    uses the encoded form directly). -/
theorem non_incident_pairs_dominate :
    ∀ eps : ℝ, 0 < eps → ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      D₀ ≤ maxDegree G →
      ∀ e : Fin G.size × Fin G.size, G.graph.Adj e.1 e.2 →
      -- Incident pairs: edges sharing an endpoint with e that are in N_s(e)
      -- These are bounded by 2Δ·|N_s(e)| ≤ 4Δ³
      (((Finset.univ : Finset (Fin G.size × Fin G.size)).filter fun e' =>
        G.graph.Adj e'.1 e'.2 ∧ (e'.1 = e.1 ∨ e'.1 = e.2 ∨ e'.2 = e.1 ∨ e'.2 = e.2) ∧
        (e'.1, e'.2) ≠ (e.1, e.2)).card : ℝ) ≤ eps * (maxDegree G : ℝ) ^ 4 := by
  intro eps heps
  refine ⟨Nat.ceil (4 / eps) + 1, fun G hG e hadj => ?_⟩
  have hle : ((Finset.univ.filter fun e' : Fin G.size × Fin G.size =>
    G.graph.Adj e'.1 e'.2 ∧ (e'.1 = e.1 ∨ e'.1 = e.2 ∨ e'.2 = e.1 ∨ e'.2 = e.2) ∧
    (e'.1, e'.2) ≠ (e.1, e.2)).card : ℝ) ≤ 4 * (maxDegree G : ℝ) := by
    exact_mod_cast le_trans (Finset.card_le_card (fun e' he' => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he' ⊢
      exact ⟨he'.1, he'.2.1⟩)) (incident_to_edge_le G e.1 e.2)
  have hDelta_pos : (1 : ℝ) ≤ (maxDegree G : ℝ) := by
    exact_mod_cast maxDegree_pos_of_adj G e.1 e.2 hadj
  have hfour_le : 4 ≤ eps * (maxDegree G : ℝ) := by
    have h2 : 4 / eps ≤ (maxDegree G : ℝ) := by
      linarith [Nat.le_ceil (4 / eps),
        (show (Nat.ceil (4 / eps) + 1 : ℝ) ≤ (maxDegree G : ℝ) from by exact_mod_cast hG)]
    rw [div_le_iff₀ heps] at h2; linarith
  have hDelta_sq : (1 : ℝ) ≤ (maxDegree G : ℝ) ^ 2 :=
    le_trans (by norm_num : (1:ℝ) ≤ 1 ^ 2) (sq_le_sq' (by linarith) hDelta_pos)
  calc ((Finset.univ.filter fun e' : Fin G.size × Fin G.size =>
      G.graph.Adj e'.1 e'.2 ∧ (e'.1 = e.1 ∨ e'.1 = e.2 ∨ e'.2 = e.1 ∨ e'.2 = e.2) ∧
      (e'.1, e'.2) ≠ (e.1, e.2)).card : ℝ)
      ≤ 4 * (maxDegree G : ℝ) := hle
    _ ≤ eps * (maxDegree G : ℝ) ^ 2 := by nlinarith
    _ ≤ eps * (maxDegree G : ℝ) ^ 4 := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt heps)
        nlinarith [sq_nonneg ((maxDegree G : ℝ) ^ 2 - 1)]

/-- **Lemma (Degree condition, §4.3 Lemma 2)**:
    The minimum degree condition deg_{H[F]}(f) ≥ (2-η)Δ² is asymptotically
    determined by non-incident edges. The incident edges contribute O(Δ) = o(Δ²).

    **Status**: Intentional standalone — Thesis Ch 5 Lemma 4.3
    (`sec_degree_non_incident`); no consumer expected. -/
theorem degree_condition_non_incident :
    ∀ eps : ℝ, 0 < eps → ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      D₀ ≤ maxDegree G →
      ∀ e : Fin G.size × Fin G.size, G.graph.Adj e.1 e.2 →
      -- Incident edges to e: at most 2Δ (each endpoint has degree ≤ Δ)
      (((Finset.univ : Finset (Fin G.size × Fin G.size)).filter fun e' =>
        G.graph.Adj e'.1 e'.2 ∧
        (e'.1 = e.1 ∨ e'.1 = e.2 ∨ e'.2 = e.1 ∨ e'.2 = e.2)).card : ℝ) ≤
        eps * (maxDegree G : ℝ) ^ 2 := by
  intro eps heps
  refine ⟨Nat.ceil (4 / eps) + 1, fun G hG e hadj => ?_⟩
  have hle : ((Finset.univ.filter fun e' : Fin G.size × Fin G.size =>
      G.graph.Adj e'.1 e'.2 ∧
      (e'.1 = e.1 ∨ e'.1 = e.2 ∨ e'.2 = e.1 ∨ e'.2 = e.2)).card : ℝ) ≤
      4 * (maxDegree G : ℝ) := by exact_mod_cast incident_to_edge_le G e.1 e.2
  have hDelta_pos : (1 : ℝ) ≤ (maxDegree G : ℝ) := by
    exact_mod_cast maxDegree_pos_of_adj G e.1 e.2 hadj
  have hfour_le_eps_delta : 4 ≤ eps * (maxDegree G : ℝ) := by
    have h1 : (4 : ℝ) / eps ≤ ↑(Nat.ceil (4 / eps)) := Nat.le_ceil _
    have h2 : (↑(Nat.ceil (4 / eps)) : ℝ) + 1 ≤ (maxDegree G : ℝ) := by exact_mod_cast hG
    have h3 : 4 / eps ≤ (maxDegree G : ℝ) := by linarith
    rw [div_le_iff₀ heps] at h3; linarith
  calc ((Finset.univ.filter fun e' : Fin G.size × Fin G.size =>
      G.graph.Adj e'.1 e'.2 ∧
      (e'.1 = e.1 ∨ e'.1 = e.2 ∨ e'.2 = e.1 ∨ e'.2 = e.2)).card : ℝ)
      ≤ 4 * (maxDegree G : ℝ) := hle
    _ ≤ eps * (maxDegree G : ℝ) * (maxDegree G : ℝ) := by nlinarith
    _ = eps * (maxDegree G : ℝ) ^ 2 := by ring

/-! ## §4.4: SDP Parameters

The SDP certificates (verified by `certificates/verify_sdp.py`) give:
- General: φ(O) ≤ 10.644 (`certificates/strong_edge_colouring.{sdpa,cert}`, m=17950)
- Bipartite: φ(O_bip) ≤ 4.093 (`certificates/bipartite_strong_edge_colouring.{sdpa,cert}`, m=3808)

The per-vertex sparsity bounds (`sec_vertex_sparsity`, `sec_vertex_sparsity_bipartite`)
encapsulate the full SDP-to-counting bridge. The SDP value λ determines the
sparsity parameter σ = 1 - λ/16 (general) or σ_bip = 1 - λ/8 (bipartite). -/

/-- The **SDP density bound** λ = 10.644 for the general strong edge colouring problem. -/
noncomputable def secDensityBound : ℝ := 10.644

lemma secDensityBound_val : secDensityBound = 10.644 := rfl

/-! ## §4.4b: Sparsity Parameter and Numeric Verification -/

/-- The **sparsity parameter** σ used in the Hurley colouring lemma.

**Definition** (2026-05-14, after α phase 2's RED verdict and the
1.73→1.74 constant-relaxation refactor): `σ := 1 - λ/16 - 1/200`, where
`λ = secDensityBound = 10.644` is the SDP density bound and `1/200`
is the **absorbed strict-bound buffer**.

Original definition (before this refactor): `σ := 1 - λ/16 = 0.33475`,
matching the thesis's exact statement that the buffer `1/10000` was
needed downstream (encoded by the now-deleted axiom
`phi_evalAlg_O_sec_alg_le_bound_strict`). Absorbing the buffer into σ
allows the chain to be proved from the **loose** bound axiom
`phi_evalAlg_O_sec_alg_le_bound : ≤ 10.644` alone — eliminating the
strict-bound axiom at the cost of raising the headline constant from
1.73 to 1.74.

Numerical value: σ ≈ 0.32975.

The Hurley colouring lemma uses this σ: the strong neighbourhood density
bound implies that for large Δ, every high-degree vertex f in L(G)² has
at most `(1-σ)·C(Δ(H), 2)` edges in its neighbourhood. -/
noncomputable def secSparsity : ℝ := 1 - secDensityBound / 16 - 1/200

/-- σ = 1 - 10.644/16 - 1/200 = 0.32975. -/
lemma secSparsity_val : secSparsity = 1 - 10.644 / 16 - 1/200 := by
  unfold secSparsity; rw [secDensityBound_val]

/-- σ > 0 (the neighbourhoods are genuinely sparse). -/
lemma secSparsity_pos : 0 < secSparsity := by
  rw [secSparsity_val]; norm_num

/-- σ ≤ 1. -/
lemma secSparsity_le_one : secSparsity ≤ 1 := by
  rw [secSparsity_val]; norm_num

/-- √σ ≤ 0.575. Since 0.575² = 0.330625 ≥ 0.32975 = σ. -/
lemma sqrt_secSparsity_le : Real.sqrt secSparsity ≤ 0.575 :=
  (Real.sqrt_le_sqrt (by rw [secSparsity_val]; norm_num)).trans_eq (Real.sqrt_sq (by norm_num))

/-- σ · √σ ≤ 0.19. (0.33 × 0.575 = 0.18975 ≤ 0.19.) -/
lemma secSparsity_mul_sqrt_le : secSparsity * Real.sqrt secSparsity ≤ 0.19 := by
  have hsigma : secSparsity ≤ 0.33 := by rw [secSparsity_val]; norm_num
  have hsqrt := sqrt_secSparsity_le
  calc secSparsity * Real.sqrt secSparsity
      ≤ 0.33 * 0.575 := by
        apply mul_le_mul hsigma hsqrt (Real.sqrt_nonneg _) (by norm_num)
    _ ≤ 0.19 := by norm_num

/-- ε(σ) > 0.133: the colouring improvement is large enough.
    Since σ/2 ≥ 0.32975/2 = 0.164875 and σ·√σ/6 ≤ 0.19/6 ≈ 0.031667,
    we get ε(σ) ≥ 0.164875 - 0.031667 ≈ 0.133208 > 0.133. -/
lemma colouringEps_secSparsity_gt : 0.133 < colouringEps secSparsity := by
  unfold colouringEps
  have hbound := secSparsity_mul_sqrt_le
  have hsigma_val := secSparsity_val
  have h1 : secSparsity / 2 - secSparsity * Real.sqrt secSparsity / 6 ≥
      secSparsity / 2 - 0.19 / 6 := by
    linarith [div_le_div_of_nonneg_right hbound (show (0:ℝ) ≤ 6 by norm_num)]
  linarith [show secSparsity / 2 - 0.19 / 6 > 0.133 by rw [hsigma_val]; norm_num]

/-- **(1 - ε(σ)) · 2 < 1.734**: the colouring part of the bound is below 1.734.
    Key numeric verification for the proof of Theorem 4.1 at constant 1.74. -/
lemma sec_colouring_factor_lt : (1 - colouringEps secSparsity) * 2 < 1.734 := by
  have heps := colouringEps_secSparsity_gt
  linarith

/-- √σ ≤ 0.5743 (tighter: 0.5743² ≈ 0.32982 ≥ 0.32975 = σ). -/
lemma sqrt_secSparsity_le' : Real.sqrt secSparsity ≤ 0.5743 :=
  (Real.sqrt_le_sqrt (by rw [secSparsity_val]; norm_num)).trans_eq (Real.sqrt_sq (by norm_num))

/-- σ · √σ ≤ 0.1895 (tighter: 0.32975 × 0.5743 ≈ 0.18938 ≤ 0.1895). -/
lemma secSparsity_mul_sqrt_le' : secSparsity * Real.sqrt secSparsity ≤ 0.1895 := by
  have hsigma : secSparsity ≤ 0.32975 := by rw [secSparsity_val]; norm_num
  have hsqrt := sqrt_secSparsity_le'
  calc secSparsity * Real.sqrt secSparsity
      ≤ 0.32975 * 0.5743 := by
        apply mul_le_mul hsigma hsqrt (Real.sqrt_nonneg _) (by norm_num)
    _ ≤ 0.1895 := by norm_num

/-- ε(σ) > 0.1331 (tighter than colouringEps_secSparsity_gt). -/
lemma colouringEps_secSparsity_gt' : 0.1331 < colouringEps secSparsity := by
  unfold colouringEps
  have hbound := secSparsity_mul_sqrt_le'
  have hsigma_val := secSparsity_val
  have h1 : secSparsity / 2 - secSparsity * Real.sqrt secSparsity / 6 ≥
      secSparsity / 2 - 0.1895 / 6 := by
    linarith [div_le_div_of_nonneg_right hbound (show (0:ℝ) ≤ 6 by norm_num)]
  linarith [show secSparsity / 2 - 0.1895 / 6 > 0.1331 by rw [hsigma_val]; norm_num]

/-- (1 - ε(σ)) · 2 < 1.7338 (tighter than sec_colouring_factor_lt). -/
lemma sec_colouring_factor_lt' : (1 - colouringEps secSparsity) * 2 < 1.7338 := by
  linarith [colouringEps_secSparsity_gt']

/-! ## §4.4b': Thesis-tight raw sparsity (for the 1.73 parallel chain)

This block parallels the headline `secSparsity` (which absorbs a `1/200`
buffer for axiom hygiene) with the **raw** sparsity value
`secSparsityRaw = 1 - 10.644/16 = 0.33475` matching the thesis's exact
constant. Used only by the optional thesis-tight headline
`strong_chromatic_index_bound_thesis_tight`, which re-introduces the
strict-bound axiom to recover the thesis-published `1.73·Δ²`. -/

/-- Raw sparsity parameter (thesis-original): `σ = 1 - λ/16 = 0.33475`. -/
noncomputable def secSparsityRaw : ℝ := 1 - secDensityBound / 16

lemma secSparsityRaw_val : secSparsityRaw = 1 - 10.644 / 16 := by
  unfold secSparsityRaw; rw [secDensityBound_val]

lemma secSparsityRaw_pos : 0 < secSparsityRaw := by
  rw [secSparsityRaw_val]; norm_num

lemma secSparsityRaw_le_one : secSparsityRaw ≤ 1 := by
  rw [secSparsityRaw_val]; norm_num

/-- √σ_raw ≤ 0.5787 (since 0.5787² = 0.33489 ≥ 0.33475 = σ_raw). -/
lemma sqrt_secSparsityRaw_le : Real.sqrt secSparsityRaw ≤ 0.5787 :=
  (Real.sqrt_le_sqrt (by rw [secSparsityRaw_val]; norm_num)).trans_eq (Real.sqrt_sq (by norm_num))

/-- σ_raw · √σ_raw ≤ 0.1939. -/
lemma secSparsityRaw_mul_sqrt_le : secSparsityRaw * Real.sqrt secSparsityRaw ≤ 0.1939 := by
  have hsigma : secSparsityRaw ≤ 0.335 := by rw [secSparsityRaw_val]; norm_num
  have hsqrt := sqrt_secSparsityRaw_le
  calc secSparsityRaw * Real.sqrt secSparsityRaw
      ≤ 0.335 * 0.5787 := by
        apply mul_le_mul hsigma hsqrt (Real.sqrt_nonneg _) (by norm_num)
    _ ≤ 0.1939 := by norm_num

/-- ε(σ_raw) > 0.13505. -/
lemma colouringEps_secSparsityRaw_gt : 0.13505 < colouringEps secSparsityRaw := by
  unfold colouringEps
  have hbound := secSparsityRaw_mul_sqrt_le
  have hsigma_val := secSparsityRaw_val
  have h1 : secSparsityRaw / 2 - secSparsityRaw * Real.sqrt secSparsityRaw / 6 ≥
      secSparsityRaw / 2 - 0.1939 / 6 := by
    linarith [div_le_div_of_nonneg_right hbound (show (0:ℝ) ≤ 6 by norm_num)]
  linarith [show secSparsityRaw / 2 - 0.1939 / 6 > 0.13505 by rw [hsigma_val]; norm_num]

/-- (1 - ε(σ_raw)) · 2 < 1.7299 (thesis-original tight version). -/
lemma sec_colouring_factor_lt_raw : (1 - colouringEps secSparsityRaw) * 2 < 1.7299 := by
  linarith [colouringEps_secSparsityRaw_gt]

/-! ## §4.4c: L(G)² Construction and Sparsity -/

/-- The squared line graph L(G)² as a `Flag emptyType`.
    Vertices are the canonical edges of G (ordered pairs (u,v) with Adj u v ∧ u < v),
    with adjacency inherited from `lineGraphSqAdj`. -/
noncomputable def lineGraphSqFlag (G : Flag emptyType) : Flag emptyType where
  size := (edgeFinset G).card
  graph := {
    Adj := fun i j => lineGraphSqAdj G
      ((edgeFinset G).equivFin.symm i).val
      ((edgeFinset G).equivFin.symm j).val
    symm := fun {_ _} h => lineGraphSqAdj_symm G _ _ h
    loopless := ⟨fun _ h => absurd rfl h.2.2.1⟩
  }
  embedding := ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
  hsize := Nat.zero_le _

/-- Canonical edges in `edgeFinset G` are actual edges. -/
lemma edgeFinset_adj (G : Flag emptyType)
    (e : ↥(edgeFinset G)) : G.graph.Adj e.val.1 e.val.2 :=
  ((Finset.mem_filter.mp e.property).2).1

/-- Canonical edges in `edgeFinset G` have u < v. -/
private lemma edgeFinset_lt (G : Flag emptyType)
    (e : ↥(edgeFinset G)) : e.val.1 < e.val.2 :=
  ((Finset.mem_filter.mp e.property).2).2

/-- Canonical edges are never equal to their reverse. -/
private lemma edgeFinset_ne_swap (G : Flag emptyType)
    (e₁ e₂ : ↥(edgeFinset G)) : e₁.val ≠ (e₂.val.2, e₂.val.1) := by
  intro h
  have h1 : (e₁.val.1 : ℕ) < e₁.val.2 := edgeFinset_lt G e₁
  have h2 : (e₂.val.1 : ℕ) < e₂.val.2 := edgeFinset_lt G e₂
  simp [Prod.ext_iff] at h
  omega

/-- **Part (a)**: χ'_s(G) ≤ χ(L(G)²).
    A proper colouring of L(G)² yields a strong edge colouring of G. -/
theorem strongChromaticIndex_le_lineGraphSq (G : Flag emptyType) :
    strongChromaticIndex G ≤ chromaticNumber (lineGraphSqFlag G) := by
  apply csInf_le_csInf (OrderBot.bddBelow _)
  · exact ⟨(lineGraphSqFlag G).size, fun v => v.val,
      ⟨fun u v hadj => Fin.val_ne_of_ne ((lineGraphSqFlag G).graph.ne_of_adj hadj),
       fun v => v.isLt⟩⟩
  · intro k ⟨c', hproper, hbound⟩
    let canonEdge : Fin G.size → Fin G.size → Fin G.size × Fin G.size :=
      fun u v => if u < v then (u, v) else (v, u)
    have canon_mem : ∀ u v, G.graph.Adj u v → canonEdge u v ∈ edgeFinset G := by
      intro u v hadj
      change (if u < v then (u, v) else (v, u)) ∈ edgeFinset G
      by_cases h : u < v
      · simp only [if_pos h]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj, h⟩
      · simp only [if_neg h]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, G.graph.symm hadj,
          lt_of_le_of_ne (not_lt.mp h) (Ne.symm (G.graph.ne_of_adj hadj))⟩
    have canon_symm : ∀ u v, canonEdge u v = canonEdge v u := by
      intro u v
      change (if u < v then (u, v) else (v, u)) = (if v < u then (v, u) else (u, v))
      by_cases h1 : u < v <;> by_cases h2 : v < u
      · exact absurd (lt_trans h1 h2) (lt_irrefl _)
      · simp only [if_pos h1, if_neg h2]
      · simp only [if_neg h1, if_pos h2]
      · have heq := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
        subst heq; simp only [if_neg h1]
    let canonIdx : (u : Fin G.size) → (v : Fin G.size) → G.graph.Adj u v →
        Fin (edgeFinset G).card :=
      fun u v hadj => (edgeFinset G).equivFin ⟨canonEdge u v, canon_mem u v hadj⟩
    let c : Fin G.size × Fin G.size → ℕ := fun e =>
      if hadj : G.graph.Adj e.1 e.2 then c' (canonIdx e.1 e.2 hadj) else 0
    refine ⟨c, ⟨?_, ?_⟩, ?_⟩
    · intro u v hadj
      simp only [c, hadj, G.graph.symm hadj, dif_pos]
      show c' (canonIdx u v hadj) = c' (canonIdx v u (G.graph.symm hadj))
      exact congrArg c' (congrArg _ (Subtype.ext (canon_symm u v)))
    · intro u₁ v₁ u₂ v₂ hadj₁ hadj₂ hne hne_rev hbridge
      simp only [c, hadj₁, hadj₂, dif_pos]
      show c' (canonIdx u₁ v₁ hadj₁) ≠ c' (canonIdx u₂ v₂ hadj₂)
      apply hproper
      change lineGraphSqAdj G
        ((edgeFinset G).equivFin.symm (canonIdx u₁ v₁ hadj₁)).val
        ((edgeFinset G).equivFin.symm (canonIdx u₂ v₂ hadj₂)).val
      simp only [canonIdx, Equiv.symm_apply_apply]
      have canon_adj : ∀ u v, G.graph.Adj u v →
          G.graph.Adj (canonEdge u v).1 (canonEdge u v).2 := by
        intro u v hadj'
        change G.graph.Adj (if u < v then (u, v) else (v, u)).1
                           (if u < v then (u, v) else (v, u)).2
        by_cases h : u < v
        · simp only [if_pos h]; exact hadj'
        · simp only [if_neg h]; exact G.graph.symm hadj'
      have canon_lt : ∀ u v, G.graph.Adj u v →
          (canonEdge u v).1 < (canonEdge u v).2 := by
        intro u v hadj'
        change (if u < v then (u, v) else (v, u)).1 < (if u < v then (u, v) else (v, u)).2
        by_cases h : u < v
        · simp only [if_pos h]; exact h
        · simp only [if_neg h]
          exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm (G.graph.ne_of_adj hadj'))
      have canon_ne_swap : ∀ u₁ v₁ u₂ v₂, G.graph.Adj u₁ v₁ → G.graph.Adj u₂ v₂ →
          canonEdge u₁ v₁ ≠ canonEdge u₂ v₂ →
          canonEdge u₁ v₁ ≠ ((canonEdge u₂ v₂).2, (canonEdge u₂ v₂).1) := by
        intro a₁ b₁ a₂ b₂ h1 h2 hne' h
        have := canon_lt a₁ b₁ h1; have := canon_lt a₂ b₂ h2
        simp only [Prod.ext_iff] at h; omega
      have canon_ne : canonEdge u₁ v₁ ≠ canonEdge u₂ v₂ := by
        change (if u₁ < v₁ then (u₁, v₁) else (v₁, u₁)) ≠
               (if u₂ < v₂ then (u₂, v₂) else (v₂, u₂))
        by_cases h1 : u₁ < v₁ <;> by_cases h2 : u₂ < v₂
        · simp only [if_pos h1, if_pos h2]; exact hne
        · simp only [if_pos h1, if_neg h2]
          intro h; exact hne_rev (Prod.ext (Prod.ext_iff.mp h).1 (Prod.ext_iff.mp h).2)
        · simp only [if_neg h1, if_pos h2]
          intro h; exact hne_rev (Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp h).1)
        · simp only [if_neg h1, if_neg h2]
          intro h; exact hne (Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp h).1)
      have canon_shares_endpoint : ∀ a b u v,
          (a = u ∨ a = v ∨ b = u ∨ b = v) →
          ((canonEdge a b).1 = (canonEdge u v).1 ∨
           (canonEdge a b).1 = (canonEdge u v).2 ∨
           (canonEdge a b).2 = (canonEdge u v).1 ∨
           (canonEdge a b).2 = (canonEdge u v).2) := by
        intro a b u v hshare
        change ((if a < b then (a, b) else (b, a)).1 = (if u < v then (u, v) else (v, u)).1 ∨
             (if a < b then (a, b) else (b, a)).1 = (if u < v then (u, v) else (v, u)).2 ∨
             (if a < b then (a, b) else (b, a)).2 = (if u < v then (u, v) else (v, u)).1 ∨
             (if a < b then (a, b) else (b, a)).2 = (if u < v then (u, v) else (v, u)).2)
        by_cases hab : a < b <;> by_cases huv : u < v <;>
          simp only [if_pos, *] <;>
          rcases hshare with rfl | rfl | rfl | rfl <;>
          simp [*, or_comm, or_left_comm]
      have canon_shares_symm : ∀ a b u v,
          (a = u ∨ a = v ∨ b = u ∨ b = v) →
          ((canonEdge u v).1 = (canonEdge a b).1 ∨
           (canonEdge u v).1 = (canonEdge a b).2 ∨
           (canonEdge u v).2 = (canonEdge a b).1 ∨
           (canonEdge u v).2 = (canonEdge a b).2) := by
        intro a b u v hshare
        rcases canon_shares_endpoint a b u v hshare with h | h | h | h
        · exact Or.inl h.symm
        · exact Or.inr (Or.inr (Or.inl h.symm))
        · exact Or.inr (Or.inl h.symm)
        · exact Or.inr (Or.inr (Or.inr h.symm))
      obtain ⟨a, b, hadj_ab, hshare₁, hshare₂⟩ := hbridge
      by_cases hab₁ : canonEdge a b = canonEdge u₁ v₁
      · exact ⟨canon_adj u₁ v₁ hadj₁, canon_adj u₂ v₂ hadj₂,
                canon_ne, canon_ne_swap u₁ v₁ u₂ v₂ hadj₁ hadj₂ canon_ne,
                Or.inl ⟨canon_adj u₁ v₁ hadj₁, canon_adj u₂ v₂ hadj₂,
                        canon_ne, hab₁ ▸ canon_shares_endpoint a b u₂ v₂ hshare₂⟩⟩
      · by_cases hab₂ : canonEdge a b = canonEdge u₂ v₂
        · exact ⟨canon_adj u₁ v₁ hadj₁, canon_adj u₂ v₂ hadj₂,
                  canon_ne, canon_ne_swap u₁ v₁ u₂ v₂ hadj₁ hadj₂ canon_ne,
                  Or.inl ⟨canon_adj u₁ v₁ hadj₁, canon_adj u₂ v₂ hadj₂,
                          canon_ne, hab₂ ▸ canon_shares_symm a b u₁ v₁ hshare₁⟩⟩
        · refine ⟨canon_adj u₁ v₁ hadj₁, canon_adj u₂ v₂ hadj₂,
                  canon_ne, canon_ne_swap u₁ v₁ u₂ v₂ hadj₁ hadj₂ canon_ne,
                  Or.inr ⟨canonEdge a b, canon_adj a b hadj_ab,
                          ⟨canon_adj u₁ v₁ hadj₁, canon_adj a b hadj_ab,
                           Ne.symm hab₁, canon_shares_symm a b u₁ v₁ hshare₁⟩,
                          ⟨canon_adj a b hadj_ab, canon_adj u₂ v₂ hadj₂,
                           hab₂, canon_shares_endpoint a b u₂ v₂ hshare₂⟩⟩⟩
    · intro u v hadj
      simp only [c, hadj, dif_pos]
      exact hbound _

/-- The number of canonical edges incident to vertex `w` is at most `maxDegree G`. -/
private lemma canonical_edges_incident_le (G : Flag emptyType) (w : Fin G.size) :
    ((edgeFinset G).filter (fun e => e.1 = w ∨ e.2 = w)).card ≤ maxDegree G := by
  -- Each canonical edge (a,b) with a = w or b = w maps injectively to the other endpoint,
  -- which is a neighbor of w.
  apply le_trans _ (degree_le_maxDegree G w)
  apply Finset.card_le_card_of_injOn
    (fun e : Fin G.size × Fin G.size => if e.1 = w then e.2 else e.1)
  · -- Maps into N(w)
    intro e he
    obtain ⟨hmem, hor⟩ := Finset.mem_filter.mp he
    have hadj := ((Finset.mem_filter.mp hmem).2).1
    have hlt := ((Finset.mem_filter.mp hmem).2).2
    by_cases hw : e.1 = w
    · simp only [hw, ite_true]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw ▸ hadj⟩
    · simp only [hw, ite_false]
      have h2 : e.2 = w := by rcases hor with h | h <;> [exact absurd h hw; exact h]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2 ▸ G.graph.symm hadj⟩
  · -- Injective
    intro e1 hf1 e2 hf2 heq
    obtain ⟨hmem1, hor1⟩ := Finset.mem_filter.mp hf1
    obtain ⟨hmem2, hor2⟩ := Finset.mem_filter.mp hf2
    have hlt1 := ((Finset.mem_filter.mp hmem1).2).2
    have hlt2 := ((Finset.mem_filter.mp hmem2).2).2
    by_cases h1 : e1.1 = w <;> by_cases h2 : e2.1 = w
    · simp only [h1, h2, ite_true] at heq; exact Prod.ext (h1.trans h2.symm) heq
    · simp only [h1, h2, ite_true, ite_false] at heq
      have h2' : e2.2 = w := by rcases hor2 with h | h <;> [exact absurd h h2; exact h]
      -- heq : e1.2 = e2.1, h1 : e1.1 = w, h2' : e2.2 = w
      -- hlt1 : e1.1 < e1.2, so w < e1.2 = e2.1 < e2.2 = w, contradiction
      rw [h1] at hlt1; rw [h2'] at hlt2; omega
    · simp only [h1, h2, ite_true, ite_false] at heq
      have h1' : e1.2 = w := by rcases hor1 with h | h <;> [exact absurd h h1; exact h]
      rw [h1'] at hlt1; rw [h2] at hlt2; omega
    · simp only [h1, h2, ite_false] at heq
      have h1' : e1.2 = w := by rcases hor1 with h | h <;> [exact absurd h h1; exact h]
      have h2' : e2.2 = w := by rcases hor2 with h | h <;> [exact absurd h h2; exact h]
      exact Prod.ext heq (h1'.trans h2'.symm)

/-- If `lineGraphSqAdj G (u,v) (a,b)` and `u < v` and `a < b`, then one of `a,b` is adjacent
    to `u` or `v` in G (i.e., is in N_G(u) ∪ N_G(v)). -/
private lemma lineGraphSq_neighbor_in_neighborhood (G : Flag emptyType)
    (u v a b : Fin G.size)
    (_hadj_uv : G.graph.Adj u v) (hadj_ab : G.graph.Adj a b)
    (hne : (u, v) ≠ (a, b)) (hne_swap : (u, v) ≠ (b, a))
    (hconn : lineGraphAdj G (u, v) (a, b) ∨
      ∃ e₃ : Fin G.size × Fin G.size,
        G.graph.Adj e₃.1 e₃.2 ∧ lineGraphAdj G (u, v) e₃ ∧ lineGraphAdj G e₃ (a, b)) :
    (G.graph.Adj u a ∨ u = a) ∨ (G.graph.Adj u b ∨ u = b) ∨
    (G.graph.Adj v a ∨ v = a) ∨ (G.graph.Adj v b ∨ v = b) := by
  rcases hconn with ⟨_, _, _, hshare⟩ | ⟨⟨c, d⟩, hadj_cd, ⟨_, _, _, hshare1⟩, ⟨_, _, _, hshare2⟩⟩
  · -- Direct: (u,v) and (a,b) share an endpoint
    rcases hshare with h | h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · -- Bridge (c,d): shares endpoint with (u,v) and (a,b)
    -- One of {c,d} ∈ {u,v} and one of {c,d} ∈ {a,b} (possibly the same)
    -- hshare1 from lineGraphAdj G (u,v) (c,d): u = c ∨ u = d ∨ v = c ∨ v = d
    -- hshare2 from lineGraphAdj G (c,d) (a,b): c = a ∨ c = b ∨ d = a ∨ d = b
    rcases hshare1 with h1 | h1 | h1 | h1 <;> rcases hshare2 with h2 | h2 | h2 | h2
    · exact Or.inl (Or.inr (h1.trans h2))
    · exact Or.inr (Or.inl (Or.inr (h1.trans h2)))
    · subst h1; subst h2; exact Or.inl (Or.inl hadj_cd)
    · subst h1; subst h2; exact Or.inr (Or.inl (Or.inl hadj_cd))
    · subst h1; subst h2; exact Or.inl (Or.inl (G.graph.symm hadj_cd))
    · subst h1; subst h2; exact Or.inr (Or.inl (Or.inl (G.graph.symm hadj_cd)))
    · exact Or.inl (Or.inr (h1.trans h2))
    · exact Or.inr (Or.inl (Or.inr (h1.trans h2)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (h1.trans h2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (h1.trans h2))))
    · subst h1; subst h2; exact Or.inr (Or.inr (Or.inl (Or.inl hadj_cd)))
    · subst h1; subst h2; exact Or.inr (Or.inr (Or.inr (Or.inl hadj_cd)))
    · subst h1; subst h2; exact Or.inr (Or.inr (Or.inl (Or.inl (G.graph.symm hadj_cd))))
    · subst h1; subst h2; exact Or.inr (Or.inr (Or.inr (Or.inl (G.graph.symm hadj_cd))))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (h1.trans h2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (h1.trans h2))))

/-- Each neighbor of edge `e` in L(G)^2 has an endpoint that is a neighbor of `e.1` or `e.2`.
    More precisely: the canonical edge `e' = (a,b)` satisfies a ∈ N(u)∪N(v) or b ∈ N(u)∪N(v),
    where `e = (u,v)`. This means the edge is incident to some vertex in N(u) ∪ N(v). -/
lemma lineGraphSq_nbr_incident_to_neighborhood (G : Flag emptyType)
    (e e' : ↥(edgeFinset G))
    (hadj_sq : lineGraphSqAdj G e.val e'.val) :
    e'.val.1 ∈ (Finset.univ.filter (fun w => G.graph.Adj e.val.1 w)) ∪
               (Finset.univ.filter (fun w => G.graph.Adj e.val.2 w)) ∨
    e'.val.2 ∈ (Finset.univ.filter (fun w => G.graph.Adj e.val.1 w)) ∪
               (Finset.univ.filter (fun w => G.graph.Adj e.val.2 w)) := by
  obtain ⟨hadj1, hadj2, hne, hne_swap, hconn⟩ := hadj_sq
  have h := lineGraphSq_neighbor_in_neighborhood G e.val.1 e.val.2 e'.val.1 e'.val.2
    hadj1 hadj2 hne hne_swap hconn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  -- The 8 cases: (Adj u a | u=a) | (Adj u b | u=b) | (Adj v a | v=a) | (Adj v b | v=b)
  -- When we get an equality like u=a, we use Adj u v to place a in N(v) instead.
  rcases h with ⟨h | h⟩ | ⟨h | h⟩ | ⟨h | h⟩ | ⟨h | h⟩
  · -- Adj u a: a ∈ N(u), so e'.val.1 ∈ Nu
    exact Or.inl (Or.inl h)
  · -- u = a: since Adj u v, Adj v a (via u=a, Adj u v → Adj a v → G.symm), so a ∈ N(v)
    left; right; rw [← h]; exact G.graph.symm hadj1
  · -- Adj u b: b ∈ N(u), so e'.val.2 ∈ Nu
    exact Or.inr (Or.inl h)
  · -- u = b: Adj v b (via u=b, Adj u v → Adj b v → symm), so b ∈ N(v)
    right; right; rw [← h]; exact G.graph.symm hadj1
  · -- Adj v a: a ∈ N(v)
    exact Or.inl (Or.inr h)
  · -- v = a: Adj u a (via v=a, Adj u v), so a ∈ N(u)
    left; left; rw [← h]; exact hadj1
  · -- Adj v b: b ∈ N(v)
    exact Or.inr (Or.inr h)
  · -- v = b: Adj u b (via v=b, Adj u v), so b ∈ N(u)
    right; left; rw [← h]; exact hadj1

/-- **Part (b)**: Δ(L(G)²) ≤ 2·Δ(G)².
    Each edge in G is incident to at most 2Δ(G) edges, and squaring at most doubles this. -/
theorem lineGraphSq_maxDegree_le (G : Flag emptyType) :
    maxDegree (lineGraphSqFlag G) ≤ 2 * (maxDegree G) ^ 2 := by
  unfold maxDegree
  apply Finset.sup_le
  intro i _
  set e := (edgeFinset G).equivFin.symm i with he_def
  set u := e.val.1 with hu_def
  set v := e.val.2 with hv_def
  set Nu := (Finset.univ : Finset (Fin G.size)).filter (fun w => G.graph.Adj u w) with hNu_def
  set Nv := (Finset.univ : Finset (Fin G.size)).filter (fun w => G.graph.Adj v w) with hNv_def
  have hle : (Finset.univ.filter (fun j => (lineGraphSqFlag G).graph.Adj i j)).card ≤
      ((edgeFinset G).filter (fun e' =>
        e'.1 ∈ Nu ∪ Nv ∨ e'.2 ∈ Nu ∪ Nv)).card := by
    apply Finset.card_le_card_of_injOn
      (fun j => ((edgeFinset G).equivFin.symm j).val)
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_filter] at hj
      exact Finset.mem_filter.mpr
        ⟨((edgeFinset G).equivFin.symm j).property,
          lineGraphSq_nbr_incident_to_neighborhood G e _ hj.2⟩
    · intro j1 _ j2 _ heq
      exact (edgeFinset G).equivFin.symm.injective (Subtype.val_injective heq)
  have hle2 : ((edgeFinset G).filter (fun e' =>
      e'.1 ∈ Nu ∪ Nv ∨ e'.2 ∈ Nu ∪ Nv)).card ≤
      ((Nu ∪ Nv).biUnion (fun w => (edgeFinset G).filter (fun e' =>
        e'.1 = w ∨ e'.2 = w))).card := by
    apply Finset.card_le_card
    intro e' he'
    simp only [Finset.mem_filter] at he'
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    exact he'.2.elim (fun h => ⟨e'.1, h, he'.1, Or.inl rfl⟩)
      (fun h => ⟨e'.2, h, he'.1, Or.inr rfl⟩)
  have hle3 : ((Nu ∪ Nv).biUnion (fun w => (edgeFinset G).filter (fun e' =>
      e'.1 = w ∨ e'.2 = w))).card ≤
      (Nu ∪ Nv).card * maxDegree G :=
    calc ((Nu ∪ Nv).biUnion (fun w => (edgeFinset G).filter (fun e' =>
          e'.1 = w ∨ e'.2 = w))).card
        ≤ ∑ w ∈ Nu ∪ Nv, ((edgeFinset G).filter (fun e' =>
            e'.1 = w ∨ e'.2 = w)).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ Nu ∪ Nv, maxDegree G :=
          Finset.sum_le_sum (fun w _ => canonical_edges_incident_le G w)
      _ = (Nu ∪ Nv).card * maxDegree G := by rw [Finset.sum_const, smul_eq_mul]
  have hNuv : (Nu ∪ Nv).card ≤ 2 * maxDegree G :=
    calc (Nu ∪ Nv).card ≤ Nu.card + Nv.card := Finset.card_union_le Nu Nv
      _ ≤ maxDegree G + maxDegree G :=
          Nat.add_le_add (degree_le_maxDegree G u) (degree_le_maxDegree G v)
      _ = 2 * maxDegree G := by ring
  calc (Finset.univ.filter (fun j => (lineGraphSqFlag G).graph.Adj i j)).card
      ≤ ((edgeFinset G).filter (fun e' =>
          e'.1 ∈ Nu ∪ Nv ∨ e'.2 ∈ Nu ∪ Nv)).card := hle
    _ ≤ ((Nu ∪ Nv).biUnion (fun w => (edgeFinset G).filter (fun e' =>
          e'.1 = w ∨ e'.2 = w))).card := hle2
    _ ≤ (Nu ∪ Nv).card * maxDegree G := hle3
    _ ≤ 2 * maxDegree G * maxDegree G := Nat.mul_le_mul_right _ hNuv
    _ = 2 * (maxDegree G) ^ 2 := by ring

/-- **Part (c)**: Δ(G) ≤ Δ(L(G)²) + 1.
    At a vertex of max degree, the Δ incident edges form a near-clique in L(G). -/
theorem lineGraphSq_maxDegree_ge (G : Flag emptyType) :
    maxDegree G ≤ maxDegree (lineGraphSqFlag G) + 1 := by
  by_cases hΔ : maxDegree G = 0
  · simp [hΔ]
  have hΔ_pos : 1 ≤ maxDegree G := Nat.one_le_iff_ne_zero.mpr hΔ
  have hG_nonempty : (Finset.univ : Finset (Fin G.size)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at h
    simp [maxDegree] at hΔ_pos
  obtain ⟨v, _, hv_max⟩ := Finset.exists_mem_eq_sup (Finset.univ) hG_nonempty
    (fun v : Fin G.size => (Finset.univ.filter (fun u => G.graph.Adj v u)).card)
  have hv_deg : (Finset.univ.filter (fun u => G.graph.Adj v u)).card = maxDegree G :=
    hv_max.symm
  obtain ⟨w, hw⟩ : (Finset.univ.filter (fun u => G.graph.Adj v u)).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hadj_vw : G.graph.Adj v w := (Finset.mem_filter.mp hw).2
  let e_vw : Fin G.size × Fin G.size := if v < w then (v, w) else (w, v)
  have he_vw_adj : G.graph.Adj e_vw.1 e_vw.2 := by
    simp only [e_vw]; split <;> [exact hadj_vw; exact G.graph.symm hadj_vw]
  have he_vw_lt : e_vw.1 < e_vw.2 := by
    simp only [e_vw]; split
    · assumption
    · rename_i h; exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm (G.graph.ne_of_adj hadj_vw))
  have he_vw_mem : e_vw ∈ edgeFinset G := by
    simp only [edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨he_vw_adj, he_vw_lt⟩
  have hv_endpoint : e_vw.1 = v ∨ e_vw.2 = v := by simp only [e_vw]; split <;> simp
  set Nv := Finset.univ.filter (fun u => G.graph.Adj v u) with hNv_def
  let canonOf : Fin G.size → Fin G.size × Fin G.size :=
    fun u => if v < u then (v, u) else (u, v)
  have hcanon_mem : ∀ u, G.graph.Adj v u → canonOf u ∈ edgeFinset G := by
    intro u hadj_vu
    simp only [edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and, canonOf]
    split
    · exact ⟨hadj_vu, by assumption⟩
    · rename_i h
      exact ⟨G.graph.symm hadj_vu,
        lt_of_le_of_ne (not_lt.mp h) (Ne.symm (G.graph.ne_of_adj hadj_vu))⟩
  have hshares_v : ∀ u, G.graph.Adj v u →
      (canonOf u).1 = v ∨ (canonOf u).2 = v := by
    intro u _; simp only [canonOf]; split <;> simp
  have hcanon_inj : ∀ u₁ u₂, G.graph.Adj v u₁ → G.graph.Adj v u₂ →
      canonOf u₁ = canonOf u₂ → u₁ = u₂ := by
    intro u₁ u₂ _ _ heq
    simp only [canonOf] at heq
    split at heq <;> split at heq <;> simp [Prod.ext_iff] at heq <;> omega
  have hcanon_w : canonOf w = e_vw := by simp only [canonOf, e_vw]
  have hcanon_ne : ∀ u, G.graph.Adj v u → u ≠ w → canonOf u ≠ e_vw := by
    intro u hadj_vu huw heq
    exact huw (hcanon_inj u w hadj_vu hadj_vw (heq.trans hcanon_w.symm))
  have hcanon_ne_swap : ∀ u, G.graph.Adj v u → u ≠ w →
      canonOf u ≠ (e_vw.2, e_vw.1) := by
    intro u hadj_vu _ heq
    have h1 : (canonOf u).1 < (canonOf u).2 := by
      simp only [canonOf]; split
      · assumption
      · rename_i h; exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm (G.graph.ne_of_adj hadj_vu))
    have h2 : e_vw.2 < e_vw.1 := by
      have hprod := Prod.ext_iff.mp heq
      calc e_vw.2 = (canonOf u).1 := hprod.1.symm
        _ < (canonOf u).2 := h1
        _ = e_vw.1 := hprod.2
    exact absurd (lt_trans h2 he_vw_lt) (lt_irrefl _)
  have hlgsq : ∀ u, G.graph.Adj v u → u ≠ w →
      lineGraphSqAdj G (canonOf u) e_vw := by
    intro u hadj_vu huw
    have hadj_cu : G.graph.Adj (canonOf u).1 (canonOf u).2 := by
      simp only [canonOf]; split <;> [exact hadj_vu; exact G.graph.symm hadj_vu]
    exact ⟨hadj_cu, he_vw_adj, hcanon_ne u hadj_vu huw, hcanon_ne_swap u hadj_vu huw,
      Or.inl ⟨hadj_cu, he_vw_adj, hcanon_ne u hadj_vu huw, by
        rcases hshares_v u hadj_vu with h | h <;> rcases hv_endpoint with h' | h'
        · exact Or.inl (h.trans h'.symm)
        · exact Or.inr (Or.inl (h.trans h'.symm))
        · exact Or.inr (Or.inr (Or.inl (h.trans h'.symm)))
        · exact Or.inr (Or.inr (Or.inr (h.trans h'.symm)))⟩⟩
  let idx_vw : Fin (edgeFinset G).card := (edgeFinset G).equivFin ⟨e_vw, he_vw_mem⟩
  set L2nbrs := (Finset.univ : Finset (Fin (lineGraphSqFlag G).size)).filter
    (fun j => (lineGraphSqFlag G).graph.Adj idx_vw j) with hL2_def
  have hcard_ineq : (Nv.erase w).card ≤ L2nbrs.card := by
    apply Finset.card_le_card_of_injOn
      (fun u => if h : u ∈ Nv
        then (edgeFinset G).equivFin ⟨canonOf u, hcanon_mem u ((Finset.mem_filter.mp h).2)⟩
        else idx_vw)
    · intro u (hu : u ∈ Nv.erase w)
      have hu_Nv : u ∈ Nv := Finset.erase_subset w Nv hu
      simp only [hu_Nv, dif_pos]
      rw [hL2_def, Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      change lineGraphSqAdj G
        ((edgeFinset G).equivFin.symm idx_vw).val
        ((edgeFinset G).equivFin.symm
          ((edgeFinset G).equivFin ⟨canonOf u,
            hcanon_mem u ((Finset.mem_filter.mp hu_Nv).2)⟩)).val
      simp only [Equiv.symm_apply_apply, idx_vw]
      exact lineGraphSqAdj_symm G _ _ (hlgsq u ((Finset.mem_filter.mp hu_Nv).2)
        (Finset.ne_of_mem_erase hu))
    · intro u₁ (h₁ : u₁ ∈ Nv.erase w) u₂ (h₂ : u₂ ∈ Nv.erase w) heq
      have h₁_Nv := Finset.erase_subset w Nv h₁
      have h₂_Nv := Finset.erase_subset w Nv h₂
      simp only [h₁_Nv, h₂_Nv, dif_pos] at heq
      exact hcanon_inj u₁ u₂ ((Finset.mem_filter.mp h₁_Nv).2) ((Finset.mem_filter.mp h₂_Nv).2)
        (Subtype.mk.inj ((edgeFinset G).equivFin.injective heq))
  have herase_card : (Nv.erase w).card = Nv.card - 1 := Finset.card_erase_of_mem hw
  have hdeg_le : L2nbrs.card ≤ maxDegree (lineGraphSqFlag G) :=
    degree_le_maxDegree (lineGraphSqFlag G) idx_vw
  omega

/-! ## §4.4c': Bolzano-Weierstrass for SEC Densities

We establish the compactness/subsequence extraction machinery needed for proving
`sec_vertex_sparsity` from the SDP limit axiom `sec_sdp_limit_bound`.

The sequence type is `ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size`:
a graph G together with a vertex v of L(G)².
The density `edgesInNeighbourhood(H,v) / C(Δ(H), 2)` is bounded because
`edgesInNeighbourhood(H,v) ≤ Δ(H)^2` (at most Δ^2 pairs from a neighbourhood of size ≤ Δ).
-/

/-- `edgesInNeighbourhood G v ≤ (maxDegree G)^2`: every counted pair `(u,w)` comes from
    `N(v) × N(v)` which has at most `|N(v)|^2 ≤ Δ(G)^2` elements. -/
theorem edgesInNeighbourhood_le_maxDegree_sq (G : Flag emptyType) (v : Fin G.size) :
    edgesInNeighbourhood G v ≤ (maxDegree G) ^ 2 := by
  unfold edgesInNeighbourhood
  set nbrs := Finset.univ.filter (fun u : Fin G.size => G.graph.Adj v u) with hnbrs_def
  calc ((nbrs ×ˢ nbrs).filter (fun p : Fin G.size × Fin G.size =>
          p.1 < p.2 ∧ G.graph.Adj p.1 p.2)).card
      ≤ (nbrs ×ˢ nbrs).card := Finset.card_filter_le _ _
    _ = nbrs.card * nbrs.card := Finset.card_product _ _
    _ = nbrs.card ^ 2 := (sq nbrs.card).symm
    _ ≤ (maxDegree G) ^ 2 := Nat.pow_le_pow_left (degree_le_maxDegree G v) 2

/-- The SEC density `edgesInNeighbourhood(H,v) / C(Δ(H), 2)` lies in `[0, 4]` for `Δ(H) ≥ 2`.
    Uses `edgesInNbhd ≤ Δ² ≤ 4 · C(Δ,2)` (from `Δ²/C(Δ,2) = 2Δ/(Δ-1) ≤ 4`). -/
private theorem sec_density_in_Icc (G : Flag emptyType) (v : Fin G.size) (hΔ : 2 ≤ maxDegree G) :
    (edgesInNeighbourhood G v : ℝ) / (Nat.choose (maxDegree G) 2 : ℝ) ∈ Set.Icc 0 4 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hchoose_pos : (0 : ℝ) < (Nat.choose (maxDegree G) 2 : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos hΔ)
    rw [div_le_iff₀ hchoose_pos]
    have h1 := edgesInNeighbourhood_le_maxDegree_sq G v
    -- Need: Δ² ≤ 4 · C(Δ,2), i.e., Δ² ≤ 4 · Δ(Δ-1)/2 = 2Δ(Δ-1)
    -- Equivalently: Δ ≤ 2(Δ-1), i.e., 2 ≤ Δ, which holds.
    have h2 : (maxDegree G) ^ 2 ≤ 4 * Nat.choose (maxDegree G) 2 := by
      rw [Nat.choose_two_right, sq]
      have hΔ_pos : 0 < maxDegree G := by omega
      -- Δ * Δ ≤ 4 * (Δ * (Δ-1) / 2) = 2 * Δ * (Δ-1)
      -- Since Δ ≥ 2: Δ ≤ 2 * (Δ-1) ⟺ Δ ≤ 2Δ - 2 ⟺ 2 ≤ Δ. ✓
      calc maxDegree G * maxDegree G
          ≤ maxDegree G * (2 * (maxDegree G - 1)) := by
            apply Nat.mul_le_mul_left; omega
        _ = 2 * (maxDegree G * (maxDegree G - 1)) := by ring
        _ = 2 * (2 * (maxDegree G * (maxDegree G - 1) / 2)) := by
            rw [Nat.mul_div_cancel']; exact (Nat.even_mul_pred_self _).two_dvd
        _ = 4 * (maxDegree G * (maxDegree G - 1) / 2) := by ring
    calc (edgesInNeighbourhood G v : ℝ)
        ≤ ((maxDegree G : ℝ) ^ 2 : ℝ) := by exact_mod_cast h1
      _ ≤ (4 * Nat.choose (maxDegree G) 2 : ℝ) := by exact_mod_cast h2

/-- **Bolzano-Weierstrass for SEC densities**: given a sequence of `(G, v)` pairs
    where G : Flag emptyType and v : Fin (lineGraphSqFlag G).size, with strictly
    increasing max degree of G, there exists a subsequence along which
    `edgesInNeighbourhood / C(Δ(H), 2)` converges to some `L ≥ 0`. -/
theorem sec_density_convergent_subseq
    (seq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size)
    (hΔ : StrictMono (fun k => maxDegree (seq k).1)) :
    ∃ (sub : ℕ → ℕ) (L : ℝ), StrictMono sub ∧ 0 ≤ L ∧
      Filter.Tendsto
        (fun k => (edgesInNeighbourhood (lineGraphSqFlag (seq (sub k)).1) (seq (sub k)).2 : ℝ) /
          (Nat.choose (maxDegree (lineGraphSqFlag (seq (sub k)).1)) 2 : ℝ))
        Filter.atTop (nhds L) := by
  -- Shift by 3: for k ≥ 3, Δ(G_k) ≥ 3, so Δ(H_k) ≥ 2 and C(Δ(H),2) > 0.
  let seq' := fun k => seq (k + 3)
  have hΔ' : StrictMono (fun k => maxDegree (seq' k).1) :=
    fun a b hab => hΔ (by omega : a + 3 < b + 3)
  have hΔ_ge : ∀ k, 2 ≤ maxDegree (lineGraphSqFlag (seq' k).1) := by
    intro k
    have h3 : 3 ≤ maxDegree (seq' k).1 :=
      le_trans (by omega : 3 ≤ k + 3) (StrictMono.id_le hΔ (k + 3))
    have hge := lineGraphSq_maxDegree_ge (seq' k).1
    omega
  have hmem : ∀ k, (edgesInNeighbourhood (lineGraphSqFlag (seq' k).1) (seq' k).2 : ℝ) /
      (Nat.choose (maxDegree (lineGraphSqFlag (seq' k).1)) 2 : ℝ) ∈ Set.Icc 0 4 :=
    fun k => sec_density_in_Icc (lineGraphSqFlag (seq' k).1) (seq' k).2 (hΔ_ge k)
  obtain ⟨L, hL_mem, ψ, hψ_mono, hψ_tend⟩ := isCompact_Icc.tendsto_subseq hmem
  refine ⟨fun k => ψ k + 3, L, ?_, hL_mem.1, hψ_tend⟩
  intro a b hab
  exact Nat.add_lt_add_right (hψ_mono hab) 3

/-- **Contradiction framework**: if every limit of
    `edgesInNeighbourhood(H,v)/C(Δ(H),2)` along convergent subsequences is at most `c`,
    then `edgesInNeighbourhood ≤ (c+ε)·C(Δ(H),2)` for large Δ(G).

    This reduces `sec_vertex_sparsity` to showing that the SDP certificate forces
    every limit to be at most a constant strictly less than `1 - secSparsity`. -/
theorem sec_bound_from_limit
    (c : ℝ) (_hc : 0 ≤ c)
    (hlim : ∀ (seq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size)
      (_hΔ : StrictMono (fun k => maxDegree (seq k).1)),
      ∀ (sub : ℕ → ℕ) (L : ℝ),
        StrictMono sub →
        Filter.Tendsto (fun k =>
          (edgesInNeighbourhood (lineGraphSqFlag (seq (sub k)).1) (seq (sub k)).2 : ℝ) /
          (Nat.choose (maxDegree (lineGraphSqFlag (seq (sub k)).1)) 2 : ℝ))
          Filter.atTop (nhds L) →
        L ≤ c) :
    ∀ eps : ℝ, 0 < eps → ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      D₀ ≤ maxDegree G →
      ∀ v : Fin (lineGraphSqFlag G).size,
        (edgesInNeighbourhood (lineGraphSqFlag G) v : ℝ) ≤
          (c + eps) * (Nat.choose (maxDegree (lineGraphSqFlag G)) 2 : ℝ) := by
  intro eps heps
  by_contra h_not
  push_neg at h_not
  have h_exists : ∀ D : ℕ, ∃ (p : Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size),
      D < maxDegree p.1 ∧
      (c + eps) * (Nat.choose (maxDegree (lineGraphSqFlag p.1)) 2 : ℝ) <
        (edgesInNeighbourhood (lineGraphSqFlag p.1) p.2 : ℝ) := by
    intro D
    obtain ⟨G, hG_deg, v, hv⟩ := h_not (D + 1)
    exact ⟨⟨G, v⟩, show D < maxDegree G by omega, hv⟩
  let buildSeq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size :=
    Nat.rec (h_exists 2).choose
      (fun _ p => (h_exists (maxDegree p.1)).choose)
  have hΔ_strict : StrictMono (fun k => maxDegree (buildSeq k).1) :=
    strictMono_nat_of_lt_succ fun k => (h_exists (maxDegree (buildSeq k).1)).choose_spec.1
  have hΔ_ge2 : ∀ k, 2 ≤ maxDegree (lineGraphSqFlag (buildSeq k).1) := by
    intro k
    have : 3 ≤ maxDegree (buildSeq 0).1 :=
      Nat.succ_le_of_lt (h_exists 2).choose_spec.1
    have h3 : 3 ≤ maxDegree (buildSeq k).1 := le_trans this (by
      rcases k with _ | k
      · exact le_refl _
      · exact le_of_lt (hΔ_strict (Nat.zero_lt_succ k)))
    have := lineGraphSq_maxDegree_ge (buildSeq k).1
    omega
  obtain ⟨sub, L, hsub_mono, _, hL_tend⟩ :=
    sec_density_convergent_subseq buildSeq hΔ_strict
  have h_density_gt : ∀ n, 1 ≤ n →
      c + eps < (edgesInNeighbourhood (lineGraphSqFlag (buildSeq n).1) (buildSeq n).2 : ℝ) /
        (Nat.choose (maxDegree (lineGraphSqFlag (buildSeq n).1)) 2 : ℝ) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [lt_div_iff₀ (Nat.cast_pos.mpr (Nat.choose_pos (hΔ_ge2 (m + 1))))]
    exact (h_exists (maxDegree (buildSeq m).1)).choose_spec.2
  have hL_ge : c + eps ≤ L := by
    apply ge_of_tendsto hL_tend
    rw [Filter.eventually_atTop]
    exact ⟨1, fun k hk => le_of_lt (h_density_gt (sub k)
      (le_trans hk (StrictMono.id_le hsub_mono k)))⟩
  linarith [hlim buildSeq hΔ_strict sub L hsub_mono hL_tend]

/-! ## §4.4d: Main theorems

The SDP+averaging bridge axiom `sec_sdp_limit_bound` and its downstream consumers
(`sec_vertex_sparsity`, `sec_line_graph_sq_sparsity`,
`sec_combined_bound`, `strong_chromatic_index_bound`,
`strong_neighbourhood_density_improved`) have been moved to
`DaveyThesis2024/StrongChromaticIndex.lean` (Phase S3.H, 2026-05-14). That file
sits *above* both `StrongEdgeColouring` and the cert-driven bridges
(`SecBridge`, `SecBipartiteBridge`) in the import graph, allowing the literal
axiom to be replaced by a theorem aliased to
`Davey2024.SecBridge.sec_sdp_limit_bound_via_bridge`. -/

/-! ## §4.5: Bipartite Case -/

/-! ## §4.5a: Bipartite SDP Parameters -/

/-- The **bipartite SDP density bound** λ_bip = 4.093, tighter than secDensityBound
    thanks to the bipartite constraints.
    Certificate: `certificates/bipartite_strong_edge_colouring.{sdpa,cert}` (m=3808). -/
noncomputable def secBipartiteDensityBound : ℝ := 4.093

lemma secBipartiteDensityBound_val : secBipartiteDensityBound = 4.093 := rfl

/-- The **bipartite sparsity parameter**: σ_bip = 1 - λ/8 - 1/200 where λ = 4.093.

**Definition** (2026-05-14, after the 1.73→1.74 constant-relaxation refactor):
absorbs a `1/200` buffer to allow the chain to be proved from the **loose**
bound axiom alone — eliminating `phi_evalAlg_O_sec_bip_alg_le_bound_strict`
at the cost of raising the bipartite headline constant accordingly.

Numerical value: σ_bip ≈ 0.483375 (was 0.488375).

The denominator is 8 (not 16 as in the general case) because the bipartite
(4,2)-coloured graph construction eliminates the factor-of-2 double-counting
present in the general (2,2)-coloured case. -/
noncomputable def secBipartiteSparsity : ℝ := 1 - secBipartiteDensityBound / 8 - 1/200

lemma secBipartiteSparsity_val : secBipartiteSparsity = 1 - 4.093 / 8 - 1/200 := by
  unfold secBipartiteSparsity; rw [secBipartiteDensityBound_val]

lemma secBipartiteSparsity_pos : 0 < secBipartiteSparsity := by
  rw [secBipartiteSparsity_val]; norm_num

lemma secBipartiteSparsity_le_one : secBipartiteSparsity ≤ 1 := by
  rw [secBipartiteSparsity_val]; norm_num

/-- √σ_bip ≤ 0.6953 (since 0.6953² ≈ 0.483442 ≥ 0.483375 = σ_bip). -/
lemma sqrt_secBipartiteSparsity_le : Real.sqrt secBipartiteSparsity ≤ 0.6953 :=
  (Real.sqrt_le_sqrt (by rw [secBipartiteSparsity_val]; norm_num)).trans_eq
    (Real.sqrt_sq (by norm_num))

/-- σ_bip · √σ_bip ≤ 0.3361 (0.483375 × 0.6953 ≈ 0.336051 ≤ 0.3361). -/
lemma secBipartiteSparsity_mul_sqrt_le :
    secBipartiteSparsity * Real.sqrt secBipartiteSparsity ≤ 0.3361 := by
  have hsigma : secBipartiteSparsity ≤ 0.483375 := by rw [secBipartiteSparsity_val]; norm_num
  have hsqrt := sqrt_secBipartiteSparsity_le
  calc secBipartiteSparsity * Real.sqrt secBipartiteSparsity
      ≤ 0.483375 * 0.6953 := by
        apply mul_le_mul hsigma hsqrt (Real.sqrt_nonneg _) (by norm_num)
    _ ≤ 0.3361 := by norm_num

/-- The bipartite ε value: ε(σ_bip) > 0.1855.
    σ/2 ≥ 0.483375/2 = 0.241688; σ·√σ/6 ≤ 0.3361/6 ≈ 0.056017;
    ε ≥ 0.241688 - 0.056017 ≈ 0.185671 > 0.1855. -/
lemma colouringEps_bipartiteSparsity_gt : 0.1855 < colouringEps secBipartiteSparsity := by
  unfold colouringEps
  have hbound := secBipartiteSparsity_mul_sqrt_le
  have hsigma_val := secBipartiteSparsity_val
  have h1 : secBipartiteSparsity / 2 - secBipartiteSparsity * Real.sqrt secBipartiteSparsity / 6 ≥
      secBipartiteSparsity / 2 - 0.3361 / 6 := by
    linarith [div_le_div_of_nonneg_right hbound (show (0:ℝ) ≤ 6 by norm_num)]
  linarith [show secBipartiteSparsity / 2 - 0.3361 / 6 > 0.1855 by rw [hsigma_val]; norm_num]

/-- The bipartite colouring factor: (1-ε(σ_bip))·2 < 1.629. -/
lemma sec_bipartite_colouring_factor_lt :
    (1 - colouringEps secBipartiteSparsity) * 2 < 1.629 := by
  linarith [colouringEps_bipartiteSparsity_gt]

/-! ## §4.5a': Thesis-tight raw bipartite sparsity (for 1.6255 parallel chain)

Parallel to `secSparsityRaw` for general SEC. -/

/-- Raw bipartite sparsity (thesis-original): σ_bip = 1 - λ/8 = 0.488375. -/
noncomputable def secBipartiteSparsityRaw : ℝ := 1 - secBipartiteDensityBound / 8

lemma secBipartiteSparsityRaw_val : secBipartiteSparsityRaw = 1 - 4.093 / 8 := by
  unfold secBipartiteSparsityRaw; rw [secBipartiteDensityBound_val]

lemma secBipartiteSparsityRaw_pos : 0 < secBipartiteSparsityRaw := by
  rw [secBipartiteSparsityRaw_val]; norm_num

lemma secBipartiteSparsityRaw_le_one : secBipartiteSparsityRaw ≤ 1 := by
  rw [secBipartiteSparsityRaw_val]; norm_num

/-- √σ_bip_raw ≤ 0.69884 (0.69884² = 0.488377 ≥ 0.488375 = σ_bip_raw). -/
lemma sqrt_secBipartiteSparsityRaw_le : Real.sqrt secBipartiteSparsityRaw ≤ 0.69884 :=
  (Real.sqrt_le_sqrt (by rw [secBipartiteSparsityRaw_val]; norm_num)).trans_eq
    (Real.sqrt_sq (by norm_num))

/-- σ_bip_raw · √σ_bip_raw ≤ 0.3413. -/
lemma secBipartiteSparsityRaw_mul_sqrt_le :
    secBipartiteSparsityRaw * Real.sqrt secBipartiteSparsityRaw ≤ 0.3413 := by
  have hsigma : secBipartiteSparsityRaw ≤ 0.48838 := by
    rw [secBipartiteSparsityRaw_val]; norm_num
  have hsqrt := sqrt_secBipartiteSparsityRaw_le
  calc secBipartiteSparsityRaw * Real.sqrt secBipartiteSparsityRaw
      ≤ 0.48838 * 0.69884 := by
        apply mul_le_mul hsigma hsqrt (Real.sqrt_nonneg _) (by norm_num)
    _ ≤ 0.3413 := by norm_num

/-- ε(σ_bip_raw) > 0.1873. -/
lemma colouringEps_bipartiteSparsityRaw_gt :
    0.1873 < colouringEps secBipartiteSparsityRaw := by
  unfold colouringEps
  have hbound := secBipartiteSparsityRaw_mul_sqrt_le
  have hsigma_val := secBipartiteSparsityRaw_val
  have h1 : secBipartiteSparsityRaw / 2 -
      secBipartiteSparsityRaw * Real.sqrt secBipartiteSparsityRaw / 6 ≥
      secBipartiteSparsityRaw / 2 - 0.3413 / 6 := by
    linarith [div_le_div_of_nonneg_right hbound (show (0:ℝ) ≤ 6 by norm_num)]
  linarith [show secBipartiteSparsityRaw / 2 - 0.3413 / 6 > 0.1873 by
    rw [hsigma_val]; norm_num]

/-- (1 - ε(σ_bip_raw)) · 2 < 1.6254 (thesis-original tight version). -/
lemma sec_bipartite_colouring_factor_lt_raw :
    (1 - colouringEps secBipartiteSparsityRaw) * 2 < 1.6254 := by
  linarith [colouringEps_bipartiteSparsityRaw_gt]

/-! ## §4.5a: Bolzano-Weierstrass for Bipartite SEC Densities

Analogous to §4.4c' but for bipartite graphs. The sequence carries an `IsBipartite`
proof alongside each graph. The BW extraction and contradiction framework are
structurally identical, reusing `sec_density_in_Icc`. -/

/-- **Bolzano-Weierstrass for bipartite SEC densities**: given a sequence of
    bipartite `(G, v)` pairs with strictly increasing Δ(G), there exists a
    subsequence along which `edgesInNeighbourhood / C(Δ(H), 2)` converges. -/
theorem sec_bipartite_density_convergent_subseq
    (seq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size)
    (hΔ : StrictMono (fun k => maxDegree (seq k).1))
    (_hBip : ∀ k, IsBipartite (seq k).1) :
    ∃ (sub : ℕ → ℕ) (L : ℝ), StrictMono sub ∧ 0 ≤ L ∧
      Filter.Tendsto
        (fun k => (edgesInNeighbourhood (lineGraphSqFlag (seq (sub k)).1) (seq (sub k)).2 : ℝ) /
          (Nat.choose (maxDegree (lineGraphSqFlag (seq (sub k)).1)) 2 : ℝ))
        Filter.atTop (nhds L) :=
  sec_density_convergent_subseq seq hΔ

/-- **Bipartite contradiction framework**: if every limit of
    `edgesInNeighbourhood(H,v)/C(Δ(H),2)` along bipartite convergent subsequences
    is at most `c`, then `edgesInNeighbourhood ≤ (c+ε)·C(Δ(H),2)` for large Δ(G). -/
theorem sec_bipartite_bound_from_limit
    (c : ℝ) (_hc : 0 ≤ c)
    (hlim : ∀ (seq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size)
      (_hΔ : StrictMono (fun k => maxDegree (seq k).1))
      (_hBip : ∀ k, IsBipartite (seq k).1),
      ∀ (sub : ℕ → ℕ) (L : ℝ),
        StrictMono sub →
        Filter.Tendsto (fun k =>
          (edgesInNeighbourhood (lineGraphSqFlag (seq (sub k)).1) (seq (sub k)).2 : ℝ) /
          (Nat.choose (maxDegree (lineGraphSqFlag (seq (sub k)).1)) 2 : ℝ))
          Filter.atTop (nhds L) →
        L ≤ c) :
    ∀ eps : ℝ, 0 < eps → ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      IsBipartite G → D₀ ≤ maxDegree G →
      ∀ v : Fin (lineGraphSqFlag G).size,
        (edgesInNeighbourhood (lineGraphSqFlag G) v : ℝ) ≤
          (c + eps) * (Nat.choose (maxDegree (lineGraphSqFlag G)) 2 : ℝ) := by
  intro eps heps
  by_contra h_not
  push_neg at h_not
  have h_exists : ∀ D : ℕ, ∃ (p : Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size),
      IsBipartite p.1 ∧ D < maxDegree p.1 ∧
      (c + eps) * (Nat.choose (maxDegree (lineGraphSqFlag p.1)) 2 : ℝ) <
        (edgesInNeighbourhood (lineGraphSqFlag p.1) p.2 : ℝ) := by
    intro D
    obtain ⟨G, hBip, hG_deg, v, hv⟩ := h_not (D + 1)
    exact ⟨⟨G, v⟩, hBip, show D < maxDegree G by omega, hv⟩
  let buildSeq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size :=
    Nat.rec (h_exists 2).choose
      (fun _ p => (h_exists (maxDegree p.1)).choose)
  have hΔ_strict : StrictMono (fun k => maxDegree (buildSeq k).1) :=
    strictMono_nat_of_lt_succ fun k => (h_exists (maxDegree (buildSeq k).1)).choose_spec.2.1
  have hΔ_ge2 : ∀ k, 2 ≤ maxDegree (lineGraphSqFlag (buildSeq k).1) := by
    intro k
    have h3 : 3 ≤ maxDegree (buildSeq k).1 :=
      le_trans (Nat.succ_le_of_lt (h_exists 2).choose_spec.2.1) (by
        rcases k with _ | k
        · exact le_refl _
        · exact le_of_lt (hΔ_strict (Nat.zero_lt_succ k)))
    have := lineGraphSq_maxDegree_ge (buildSeq k).1; omega
  let shiftSeq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size :=
    fun k => buildSeq (k + 1)
  have hΔ_shift : StrictMono (fun k => maxDegree (shiftSeq k).1) :=
    fun a b hab => hΔ_strict (by omega : a + 1 < b + 1)
  have hBip_shift : ∀ k, IsBipartite (shiftSeq k).1 :=
    fun k => (h_exists (maxDegree (buildSeq k).1)).choose_spec.1
  obtain ⟨sub, L, hsub_mono, _, hL_tend⟩ :=
    sec_bipartite_density_convergent_subseq shiftSeq hΔ_shift hBip_shift
  have hL_ge : c + eps ≤ L := by
    apply ge_of_tendsto hL_tend
    rw [Filter.eventually_atTop]
    exact ⟨0, fun k _ => le_of_lt (by
      rw [lt_div_iff₀ (Nat.cast_pos.mpr (Nat.choose_pos (hΔ_ge2 (sub k + 1))))]
      exact (h_exists (maxDegree (buildSeq (sub k)).1)).choose_spec.2.2)⟩
  linarith [hlim shiftSeq hΔ_shift hBip_shift sub L hsub_mono hL_tend]

/-! ## §4.5d: Bipartite main theorems

The SDP+averaging bridge axiom `sec_sdp_limit_bound_bipartite` and its
downstream consumers (`sec_vertex_sparsity_bipartite`,
`sec_line_graph_sq_sparsity_bipartite`,
`sec_combined_bound_bipartite`, `strong_chromatic_index_bipartite`) have
been moved to `DaveyThesis2024/StrongChromaticIndex.lean` (Phase S3.H,
2026-05-14). The literal axiom is replaced there by a theorem aliased to
`Davey2024.SecBipartiteBridge.sec_sdp_limit_bound_bipartite_via_bridge`. -/

end Davey2024

end
