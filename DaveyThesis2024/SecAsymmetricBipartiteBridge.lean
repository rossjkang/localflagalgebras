import DaveyThesis2024.SecBipartiteCertificate
import DaveyThesis2024.SecBipartiteBasis
import DaveyThesis2024.SecBipartiteBridge
import DaveyThesis2024.LocalFlagAlgebra
import DaveyThesis2024.CG22
import DaveyThesis2024.CGraph22Bridge
import DaveyThesis2024.StrongEdgeColouring

/-!
# SecAsymmetricBipartiteBridge — asymmetric SEC hypothesis + density/sparsity constants

**Status (2026-07-12, post B1 R1b repair):** this file provides the
*host-independent* pieces of the §8 asymmetric-bipartite strong-edge-colouring
chain: the hypothesis predicate `IsAsymmetricBipartite`, the asymmetric
inflated max-degree bound `Δ(L(G)²) ≤ 2p·Δ²`, and the two numerical constants
consumed downstream (`secAsymDensityBound`, `secAsymBipartiteSparsity`).

The old CG22 objective / host / SDP-limit machinery — an algebra-level
objective over a *borrowed symmetric* cert target, together with a per-`G`
combinatorial-identity axiom (which was FALSE for general `p`), a vacuous
eval-bound axiom, a strict variant, and a CG22 regularity axiom — was
**retired** in the B1 R1b repair. The sound bound now lives on the F-free
CG4 `p = 1` arm in `SecAsymBridgeF` and is carried to general `p` per-graph
by the proven blow-up transfer (`SecAsymBlowup`), with the chromatic step in
`StrongChromaticIndex` §8.

## What this file provides

* `IsAsymmetricBipartite : ℝ → Flag emptyType → Prop` — bipartite opposition
  + exact high-side degree `= Δ` + low-side degree `≤ p·Δ` (paper L2003-2020).
* `asymmetric_lineGraphSq_maxDegree_le : Δ(L(G)²) ≤ 2p·Δ²` — the per-`p`
  inflated max-degree bound (paper L2096-2097).
* `secAsymDensityBound : ℝ := 0.5687` — the `p = 1` per-vertex density target
  (= C/2, the eval-level CG4 cert upper bound in `SecAsymBridgeF`).
* `secAsymBipartiteSparsity`, `sec_asym_bipartite_colouring_factor_lt` — the
  derived Hurley sparsity `σ_p ≈ 0.4312` and the chromatic factor
  `(1 − ε(σ_p))·2 < 1.6632`.
-/

namespace Davey2024.SecAsymmetricBipartiteBridge

open Davey2024 SecBipartiteCertificate SecBipartiteBasis

open Finset Classical in
noncomputable section

/-! ## §1. Asymmetric bipartite SEC graph class + Δ parameter at `CG22` -/

/-- **Asymmetric bipartite hypothesis at ratio `p`.**

A `G : Flag emptyType` satisfies `IsAsymmetricBipartite p G` iff it is
bipartite with bipartition `A ⊔ B` where `A` is $\Delta(G)$-regular
and `B` is $p\Delta(G)$-regular, for the asymmetry ratio `p ∈ (0, 1]`.

Concretely, we package this as: there exists a bipartition `S : Finset
(Fin G.size)` (the "high-degree" component, analogous to `A`) such
that every vertex in `S` has degree exactly `maxDegree G` and every
vertex outside `S` has degree at most `p · maxDegree G`.

The §8 prose (paper L2003-2020) sets up the asymmetric class as
4-coloured bipartite graphs $G'$ with $\Delta(G)$ red vertices and
$p \Delta(G)$ black vertices, with the components of black/blue and
red/green vertices each regular at degrees $\Delta(G)$ and
$p \Delta(G)$. This Lean definition captures the underlying simple
graph's asymmetric bipartite structure; the four-colour packaging is
absorbed into the (4,2)-coloured SDP basis via `secBipartiteBasis`. -/
def IsAsymmetricBipartite (p : ℝ) (G : Flag emptyType) : Prop :=
  ∃ (S : Finset (Fin G.size)),
    (∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S)) ∧
    (∀ u ∈ S, (Finset.univ.filter (fun v => G.graph.Adj u v)).card = maxDegree G) ∧
    (∀ u, u ∉ S →
      ((Finset.univ.filter (fun v => G.graph.Adj u v)).card : ℝ) ≤
        p * (maxDegree G : ℝ))

/-- An asymmetric bipartite graph is in particular bipartite. -/
theorem IsAsymmetricBipartite.isBipartite {p : ℝ} {G : Flag emptyType}
    (h : IsAsymmetricBipartite p G) : IsBipartite G :=
  ⟨h.choose, h.choose_spec.1⟩

/-! ### §1.5 Asymmetric inflated max-degree bound (paper L2096-2097)

Paper Theorem 2.17 (L2110-2115) publishes the per-$p$ form
$\chi'_s(G) \le 1.6632 \cdot \Delta(A) \cdot \Delta(B) = 1.6632 \cdot p
\cdot \Delta(G)^2$. The $\cdot p$ factor enters via the refined
asymmetric inflated max-degree bound: for $G = A \sqcup B$ with $A$
$\Delta$-regular and $B$ $p\Delta$-regular,
$$\Delta(L(G)^2) \le 2 p \, \Delta(G)^2$$
(rather than the loose $\le 2 \, \Delta(G)^2$ for general $G$).

The proof (mirroring `Davey2024.lineGraphSq_maxDegree_le` but using
the asymmetric structure) decomposes the $L(G)^2$-neighbours of an
edge $e = (u, v)$ via the disjoint union $N_G(u) \uplus N_G(v)$
(disjoint because in the bipartition $A \sqcup B$, $N_G(u) \subset
\overline{S}$ when $u \in S$ and $N_G(v) \subset S$ when $v \notin S$),
then sums per-side degree bounds: vertices in $S$ have degree exactly
$\Delta$, vertices outside have degree at most $p \cdot \Delta$.

The total is $|N_u| \cdot (p\Delta) + |N_v| \cdot \Delta \le \Delta
\cdot p\Delta + p\Delta \cdot \Delta = 2p\Delta^2$. -/

/-- **Asymmetric degree bound, per-side** (real-valued): if `w ∉ S`,
then `deg(w) ≤ p · Δ`. Direct unpacking of the third clause of
`IsAsymmetricBipartite`. -/
private lemma degree_le_p_maxDegree_of_not_mem
    {p : ℝ} {G : Flag emptyType} (hAsym : IsAsymmetricBipartite p G)
    (w : Fin G.size) (hw : w ∉ hAsym.choose) :
    ((Finset.univ.filter (fun v => G.graph.Adj w v)).card : ℝ) ≤
      p * (maxDegree G : ℝ) :=
  hAsym.choose_spec.2.2 w hw

/-- **Asymmetric degree equality, per-side** (Nat): if `w ∈ S`, then
`deg(w) = Δ`. Direct unpacking of the second clause of
`IsAsymmetricBipartite`. -/
private lemma degree_eq_maxDegree_of_mem
    {p : ℝ} {G : Flag emptyType} (hAsym : IsAsymmetricBipartite p G)
    (w : Fin G.size) (hw : w ∈ hAsym.choose) :
    (Finset.univ.filter (fun v => G.graph.Adj w v)).card = maxDegree G :=
  hAsym.choose_spec.2.1 w hw

/-- **Bipartite-component opposition** (Nat-friendly): adjacent vertices
lie on opposite sides of the bipartition `S`. Unpacks the first
clause of `IsAsymmetricBipartite`. -/
private lemma bipartite_opposition
    {p : ℝ} {G : Flag emptyType} (hAsym : IsAsymmetricBipartite p G)
    {u v : Fin G.size} (huv : G.graph.Adj u v) :
    u ∈ hAsym.choose ↔ v ∉ hAsym.choose :=
  hAsym.choose_spec.1 u v huv

/-- **Per-vertex bound: canonical edges through `w` ≤ deg(`w`)** (Nat).
A vertex `w`'s canonical edges (incident edges with `w` as a labelled
endpoint) inject into `N(w)`. -/
private lemma canonical_edges_through_le_degree (G : Flag emptyType) (w : Fin G.size) :
    ((edgeFinset G).filter (fun e => e.1 = w ∨ e.2 = w)).card ≤
      (Finset.univ.filter (fun v => G.graph.Adj w v)).card := by
  apply Finset.card_le_card_of_injOn
    (fun e : Fin G.size × Fin G.size => if e.1 = w then e.2 else e.1)
  · intro e he
    obtain ⟨hmem, hor⟩ := Finset.mem_filter.mp he
    have hadj := ((Finset.mem_filter.mp hmem).2).1
    by_cases hw : e.1 = w
    · simp only [hw, ite_true]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw ▸ hadj⟩
    · simp only [hw, ite_false]
      have h2 : e.2 = w := by rcases hor with h | h <;> [exact absurd h hw; exact h]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2 ▸ G.graph.symm hadj⟩
  · intro e1 hf1 e2 hf2 heq
    obtain ⟨hmem1, hor1⟩ := Finset.mem_filter.mp hf1
    obtain ⟨hmem2, hor2⟩ := Finset.mem_filter.mp hf2
    have hlt1 := ((Finset.mem_filter.mp hmem1).2).2
    have hlt2 := ((Finset.mem_filter.mp hmem2).2).2
    by_cases h1 : e1.1 = w <;> by_cases h2 : e2.1 = w
    · simp only [h1, h2, ite_true] at heq
      exact Prod.ext (h1.trans h2.symm) heq
    · simp only [h1, h2, ite_true, ite_false] at heq
      have h2' : e2.2 = w := by rcases hor2 with h | h <;> [exact absurd h h2; exact h]
      rw [h1] at hlt1; rw [h2'] at hlt2; omega
    · simp only [h1, h2, ite_true, ite_false] at heq
      have h1' : e1.2 = w := by rcases hor1 with h | h <;> [exact absurd h h1; exact h]
      rw [h1'] at hlt1; rw [h2] at hlt2; omega
    · simp only [h1, h2, ite_false] at heq
      have h1' : e1.2 = w := by rcases hor1 with h | h <;> [exact absurd h h1; exact h]
      have h2' : e2.2 = w := by rcases hor2 with h | h <;> [exact absurd h h2; exact h]
      exact Prod.ext heq (h1'.trans h2'.symm)

/-- **Asymmetric inflated max-degree bound (paper L2096-2097)**:
for a $p$-asymmetric-bipartite graph `G` with `0 < p ≤ 1`,
`Δ(L(G)²) ≤ 2 · p · Δ(G)²` (real-valued).

Sharpens `Davey2024.lineGraphSq_maxDegree_le : maxDegree (L(G)²) ≤
2 · Δ(G)²` by the $\cdot p$ factor capturing the asymmetric
bipartite structure $G = A \sqcup B$ with $|A|$-side $\Delta$-
regular and $|B|$-side $p\Delta$-regular.

Proof sketch:
* For an edge `e = (u, v)` (canonical) in `L(G)²`, its
  `L(G)²`-neighbours are bounded by the edges of `G` having at
  least one endpoint in `N_G(u) ∪ N_G(v)` (lemma
  `lineGraphSq_nbr_incident_to_neighborhood`).
* By the bipartite structure, `u ∈ S ↔ v ∉ S`; WLOG (or by
  symmetry of the bound) `u ∈ S, v ∉ S`. Then `N_G(u) ⊂ S^c` and
  `N_G(v) ⊂ S`, so `N_G(u) ∩ N_G(v) = ∅`.
* For `w ∈ N_G(u) ⊂ S^c`: canonical edges through `w` are at most
  `deg(w) ≤ p·Δ`. Total contribution: `|N_u| · p·Δ ≤ Δ · p·Δ =
  p·Δ²`.
* For `w ∈ N_G(v) ⊂ S`: canonical edges through `w` are at most
  `deg(w) = Δ`. Total contribution: `|N_v| · Δ ≤ p·Δ · Δ = p·Δ²`.
* Total: `2p·Δ²`. -/
theorem asymmetric_lineGraphSq_maxDegree_le
    {p : ℝ} (hp1 : 0 < p) (_hp2 : p ≤ 1)
    {G : Flag emptyType} (hAsym : IsAsymmetricBipartite p G) :
    (maxDegree (lineGraphSqFlag G) : ℝ) ≤ 2 * p * (maxDegree G : ℝ) ^ 2 := by
  set S := hAsym.choose with hS_def
  set Δ := maxDegree G with hΔ_def
  -- Strategy: bound Finset.sup by showing each per-i term is ≤ 2p·Δ².
  -- Use Finset.sup_le on naturals, then cast at the end.
  have hΔ_nn : (0 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast Nat.zero_le _
  have hp_nn : (0 : ℝ) ≤ p := le_of_lt hp1
  have h2p_nn : (0 : ℝ) ≤ 2 * p := by linarith
  have hsq_nn : (0 : ℝ) ≤ (Δ : ℝ) ^ 2 := sq_nonneg _
  have hRHS_nn : (0 : ℝ) ≤ 2 * p * (Δ : ℝ) ^ 2 := mul_nonneg h2p_nn hsq_nn
  -- Per-i bound
  have hsup_le : ∀ i : Fin (lineGraphSqFlag G).size,
      (((Finset.univ.filter
          ((lineGraphSqFlag G).graph.Adj i)).card : ℕ) : ℝ) ≤ 2 * p * (Δ : ℝ) ^ 2 := by
    intro i
    set e := (edgeFinset G).equivFin.symm i with he_def
    set u := e.val.1 with hu_def
    set v := e.val.2 with hv_def
    have hadj_uv : G.graph.Adj u v := Davey2024.edgeFinset_adj G e
    set Nu := (Finset.univ : Finset (Fin G.size)).filter (fun w => G.graph.Adj u w)
      with hNu_def
    set Nv := (Finset.univ : Finset (Fin G.size)).filter (fun w => G.graph.Adj v w)
      with hNv_def
    have hle : (Finset.univ.filter
        (fun j => (lineGraphSqFlag G).graph.Adj i j)).card ≤
        ((edgeFinset G).filter (fun e' =>
          e'.1 ∈ Nu ∪ Nv ∨ e'.2 ∈ Nu ∪ Nv)).card := by
      apply Finset.card_le_card_of_injOn
        (fun j => ((edgeFinset G).equivFin.symm j).val)
      · intro j hj
        rw [Finset.mem_coe, Finset.mem_filter] at hj
        exact Finset.mem_filter.mpr
          ⟨((edgeFinset G).equivFin.symm j).property,
            Davey2024.lineGraphSq_nbr_incident_to_neighborhood G e _ hj.2⟩
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
        ∑ w ∈ Nu ∪ Nv, ((edgeFinset G).filter (fun e' =>
          e'.1 = w ∨ e'.2 = w)).card := Finset.card_biUnion_le
    have hcombined : (Finset.univ.filter
        (fun j => (lineGraphSqFlag G).graph.Adj i j)).card ≤
        ∑ w ∈ Nu ∪ Nv, ((edgeFinset G).filter (fun e' =>
          e'.1 = w ∨ e'.2 = w)).card := (hle.trans hle2).trans hle3
    -- Lift to ℝ
    have hle_real : (((Finset.univ.filter
        (fun j => (lineGraphSqFlag G).graph.Adj i j)).card : ℕ) : ℝ) ≤
        ∑ w ∈ Nu ∪ Nv,
          (((edgeFinset G).filter (fun e' =>
            e'.1 = w ∨ e'.2 = w)).card : ℝ) := by
      have hcast : ((∑ w ∈ Nu ∪ Nv, ((edgeFinset G).filter (fun e' =>
          e'.1 = w ∨ e'.2 = w)).card : ℕ) : ℝ) =
          ∑ w ∈ Nu ∪ Nv,
            (((edgeFinset G).filter (fun e' =>
              e'.1 = w ∨ e'.2 = w)).card : ℝ) := by
        push_cast; rfl
      rw [← hcast]
      exact_mod_cast hcombined
    -- bipartite_opposition and subsetdisj setup
    have hopp : u ∈ S ↔ v ∉ S := hAsym.choose_spec.1 u v hadj_uv
    have hNu_subset : ∀ w ∈ Nu, w ∉ S ↔ u ∈ S := by
      intro w hw
      rw [hNu_def, Finset.mem_filter] at hw
      exact (hAsym.choose_spec.1 u w hw.2).symm
    have hNv_subset : ∀ w ∈ Nv, w ∉ S ↔ v ∈ S := by
      intro w hw
      rw [hNv_def, Finset.mem_filter] at hw
      exact (hAsym.choose_spec.1 v w hw.2).symm
    -- Nu and Nv are disjoint by bipartite opposition
    have hdisj : Disjoint Nu Nv := by
      rw [Finset.disjoint_left]
      intro w hwu hwv
      have h1 : w ∉ S ↔ u ∈ S := hNu_subset w hwu
      have h2 : w ∉ S ↔ v ∈ S := hNv_subset w hwv
      by_cases hu : u ∈ S
      · have hvS : v ∉ S := hopp.mp hu
        have hwS : w ∉ S := h1.mpr hu
        exact hvS (h2.mp hwS)
      · have hwS_mem : w ∈ S := by
          by_contra hwS'
          exact hu (h1.mp hwS')
        have hvS_mem : v ∈ S := by
          by_contra hvS'
          exact hu (hopp.mpr hvS')
        exact (h2.mpr hvS_mem) hwS_mem
    have hsum_split :
        (∑ w ∈ Nu ∪ Nv,
            (((edgeFinset G).filter (fun e' =>
              e'.1 = w ∨ e'.2 = w)).card : ℝ)) =
        (∑ w ∈ Nu,
            (((edgeFinset G).filter (fun e' =>
              e'.1 = w ∨ e'.2 = w)).card : ℝ)) +
        (∑ w ∈ Nv,
            (((edgeFinset G).filter (fun e' =>
              e'.1 = w ∨ e'.2 = w)).card : ℝ)) :=
      Finset.sum_union hdisj
    -- per-w bound (real)
    have hper_w : ∀ w : Fin G.size,
        (((edgeFinset G).filter (fun e' => e'.1 = w ∨ e'.2 = w)).card : ℝ) ≤
        ((Finset.univ.filter (fun u' => G.graph.Adj w u')).card : ℝ) := by
      intro w
      exact_mod_cast canonical_edges_through_le_degree G w
    -- per-side degree bounds
    have hdeg_S : ∀ w ∈ S,
        ((Finset.univ.filter (fun u' => G.graph.Adj w u')).card : ℝ) ≤ (Δ : ℝ) := by
      intro w hw
      rw [degree_eq_maxDegree_of_mem hAsym w hw]
    have hdeg_compl : ∀ w, w ∉ S →
        ((Finset.univ.filter (fun u' => G.graph.Adj w u')).card : ℝ) ≤ p * (Δ : ℝ) := by
      intro w hw
      exact degree_le_p_maxDegree_of_not_mem hAsym w hw
    -- Cardinality bounds on Nu and Nv (real)
    have hNu_card : (Nu.card : ℝ) ≤ (Δ : ℝ) := by
      exact_mod_cast degree_le_maxDegree G u
    have hNv_card : (Nv.card : ℝ) ≤ (Δ : ℝ) := by
      exact_mod_cast degree_le_maxDegree G v
    -- Case-split: u ∈ S or u ∉ S
    have hbound :
        (∑ w ∈ Nu,
            (((edgeFinset G).filter (fun e' =>
              e'.1 = w ∨ e'.2 = w)).card : ℝ)) +
        (∑ w ∈ Nv,
            (((edgeFinset G).filter (fun e' =>
              e'.1 = w ∨ e'.2 = w)).card : ℝ)) ≤
        2 * p * (Δ : ℝ) ^ 2 := by
      by_cases huS : u ∈ S
      · -- u ∈ S, v ∉ S; Nu ⊂ Sᶜ, Nv ⊂ S
        have hvS : v ∉ S := hopp.mp huS
        have hNu_compl : ∀ w ∈ Nu, w ∉ S := by
          intro w hw; exact (hNu_subset w hw).mpr huS
        have hNv_in_S : ∀ w ∈ Nv, w ∈ S := by
          intro w hw
          by_contra hwS
          exact hvS ((hNv_subset w hw).mp hwS)
        have hsum_u : (∑ w ∈ Nu,
            (((edgeFinset G).filter (fun e' =>
              e'.1 = w ∨ e'.2 = w)).card : ℝ)) ≤ (Nu.card : ℝ) * (p * (Δ : ℝ)) := by
          calc (∑ w ∈ Nu,
              (((edgeFinset G).filter (fun e' =>
                e'.1 = w ∨ e'.2 = w)).card : ℝ))
              ≤ ∑ w ∈ Nu, p * (Δ : ℝ) := by
                apply Finset.sum_le_sum
                intro w hw
                exact (hper_w w).trans (hdeg_compl w (hNu_compl w hw))
            _ = (Nu.card : ℝ) * (p * (Δ : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        have hsum_v : (∑ w ∈ Nv,
            (((edgeFinset G).filter (fun e' =>
              e'.1 = w ∨ e'.2 = w)).card : ℝ)) ≤ (Nv.card : ℝ) * (Δ : ℝ) := by
          calc (∑ w ∈ Nv,
              (((edgeFinset G).filter (fun e' =>
                e'.1 = w ∨ e'.2 = w)).card : ℝ))
              ≤ ∑ w ∈ Nv, (Δ : ℝ) := by
                apply Finset.sum_le_sum
                intro w hw
                exact (hper_w w).trans (hdeg_S w (hNv_in_S w hw))
            _ = (Nv.card : ℝ) * (Δ : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        have hNv_p : (Nv.card : ℝ) ≤ p * (Δ : ℝ) := hdeg_compl v hvS
        have hpdelta_nn : (0 : ℝ) ≤ p * (Δ : ℝ) := mul_nonneg hp_nn hΔ_nn
        calc (∑ w ∈ Nu,
              (((edgeFinset G).filter (fun e' =>
                e'.1 = w ∨ e'.2 = w)).card : ℝ)) +
            (∑ w ∈ Nv,
              (((edgeFinset G).filter (fun e' =>
                e'.1 = w ∨ e'.2 = w)).card : ℝ))
            ≤ (Nu.card : ℝ) * (p * (Δ : ℝ)) + (Nv.card : ℝ) * (Δ : ℝ) :=
              add_le_add hsum_u hsum_v
          _ ≤ (Δ : ℝ) * (p * (Δ : ℝ)) + (p * (Δ : ℝ)) * (Δ : ℝ) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right hNu_card hpdelta_nn
              · exact mul_le_mul_of_nonneg_right hNv_p hΔ_nn
          _ = 2 * p * (Δ : ℝ) ^ 2 := by ring
      · -- u ∉ S, v ∈ S; Nu ⊂ S, Nv ⊂ Sᶜ
        have hvS : v ∈ S := by
          by_contra hvS'
          exact huS (hopp.mpr hvS')
        have hNu_in_S : ∀ w ∈ Nu, w ∈ S := by
          intro w hw
          by_contra hwS
          exact huS ((hNu_subset w hw).mp hwS)
        have hNv_compl : ∀ w ∈ Nv, w ∉ S := by
          intro w hw; exact (hNv_subset w hw).mpr hvS
        have hNu_p : (Nu.card : ℝ) ≤ p * (Δ : ℝ) := hdeg_compl u huS
        have hpdelta_nn : (0 : ℝ) ≤ p * (Δ : ℝ) := mul_nonneg hp_nn hΔ_nn
        have hsum_u : (∑ w ∈ Nu,
            (((edgeFinset G).filter (fun e' =>
              e'.1 = w ∨ e'.2 = w)).card : ℝ)) ≤ (Nu.card : ℝ) * (Δ : ℝ) := by
          calc (∑ w ∈ Nu,
              (((edgeFinset G).filter (fun e' =>
                e'.1 = w ∨ e'.2 = w)).card : ℝ))
              ≤ ∑ w ∈ Nu, (Δ : ℝ) := by
                apply Finset.sum_le_sum
                intro w hw
                exact (hper_w w).trans (hdeg_S w (hNu_in_S w hw))
            _ = (Nu.card : ℝ) * (Δ : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        have hsum_v : (∑ w ∈ Nv,
            (((edgeFinset G).filter (fun e' =>
              e'.1 = w ∨ e'.2 = w)).card : ℝ)) ≤ (Nv.card : ℝ) * (p * (Δ : ℝ)) := by
          calc (∑ w ∈ Nv,
              (((edgeFinset G).filter (fun e' =>
                e'.1 = w ∨ e'.2 = w)).card : ℝ))
              ≤ ∑ w ∈ Nv, p * (Δ : ℝ) := by
                apply Finset.sum_le_sum
                intro w hw
                exact (hper_w w).trans (hdeg_compl w (hNv_compl w hw))
            _ = (Nv.card : ℝ) * (p * (Δ : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        calc (∑ w ∈ Nu,
              (((edgeFinset G).filter (fun e' =>
                e'.1 = w ∨ e'.2 = w)).card : ℝ)) +
            (∑ w ∈ Nv,
              (((edgeFinset G).filter (fun e' =>
                e'.1 = w ∨ e'.2 = w)).card : ℝ))
            ≤ (Nu.card : ℝ) * (Δ : ℝ) + (Nv.card : ℝ) * (p * (Δ : ℝ)) :=
              add_le_add hsum_u hsum_v
          _ ≤ (p * (Δ : ℝ)) * (Δ : ℝ) + (Δ : ℝ) * (p * (Δ : ℝ)) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right hNu_p hΔ_nn
              · exact mul_le_mul_of_nonneg_right hNv_card hpdelta_nn
          _ = 2 * p * (Δ : ℝ) ^ 2 := by ring
    calc (((Finset.univ.filter
        ((lineGraphSqFlag G).graph.Adj i)).card : ℕ) : ℝ)
        ≤ ∑ w ∈ Nu ∪ Nv,
          (((edgeFinset G).filter (fun e' =>
            e'.1 = w ∨ e'.2 = w)).card : ℝ) := hle_real
      _ = (∑ w ∈ Nu,
            (((edgeFinset G).filter (fun e' =>
              e'.1 = w ∨ e'.2 = w)).card : ℝ)) +
          (∑ w ∈ Nv,
            (((edgeFinset G).filter (fun e' =>
              e'.1 = w ∨ e'.2 = w)).card : ℝ)) := hsum_split
      _ ≤ 2 * p * (Δ : ℝ) ^ 2 := hbound
  -- Lift to the Finset.sup: ∀ i, term_i ≤ RHS, hence sup ≤ RHS.
  unfold maxDegree
  by_cases hempty : (Finset.univ : Finset (Fin (lineGraphSqFlag G).size)).Nonempty
  · obtain ⟨i₀, _, hi₀_eq⟩ :=
      Finset.exists_mem_eq_sup
        (Finset.univ : Finset (Fin (lineGraphSqFlag G).size)) hempty
        (fun v : Fin (lineGraphSqFlag G).size =>
          (Finset.univ.filter ((lineGraphSqFlag G).graph.Adj v)).card)
    -- The goal is: ((Finset.univ.sup ... : ℕ) : ℝ) ≤ 2 * p * Δ²
    -- Use hi₀_eq : (Finset.univ.sup ...) = filter_card i₀, then apply hsup_le i₀
    rw [hi₀_eq]
    exact hsup_le i₀
  · rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.sup_empty]
    simpa using hRHS_nn

/-! ## §2. Asymmetric SEC density-bound + sparsity constants

The Route-1 asymmetric chain (`SecAsymBridgeF`, `StrongChromaticIndex` §8)
consumes only two constants from this file: the `p = 1` per-vertex density
target `secAsymDensityBound` and the derived Hurley sparsity
`secAsymBipartiteSparsity`. The old CG22 objective / host / SDP-limit
machinery (with the false identity + vacuous eval-bound axioms) was retired
in the B1 R1b repair; the sound bound now lives on the F-free CG4 arm
(`SecAsymBridgeF.secAsymF_p1_vertex_bound`). -/

/-- The **§8 asymmetric per-vertex density target**: $C/2 \approx 0.5687$
(= 1.13723/2).

Bounds `eIN(L(G')²,·)/C(2Δ'²,2)` for the regular blow-up `G'` at `p = 1`
(the F-free CG4 cert, `SecAsymBridgeF.phi_evalAlg_O_asym_CG4_le_bound`); the
blow-up transfer carries it to general `p`. The downstream Hurley colouring
lemma consumes the sparsity $\sigma_p = 1 - C/2 \approx 0.4313$ to yield the
headline chromatic constant $2 \cdot (1 - \varepsilon(\sigma_p)) \approx
1.6632$ (paper Theorem 2.17, L2076-2116).

Numerical value: `0.5687` (slightly looser than the published
`1.13723 / 2 ≈ 0.56862`, giving a `1e-4` numerical buffer that
absorbs round-off in the downstream `(1 - ε(σ))·2 < 1.6632` chain). -/
noncomputable def secAsymDensityBound : ℝ := 0.5687

lemma secAsymDensityBound_val : secAsymDensityBound = 0.5687 := rfl

lemma secAsymDensityBound_pos : 0 < secAsymDensityBound := by
  unfold secAsymDensityBound; norm_num

lemma secAsymDensityBound_le_one : secAsymDensityBound ≤ 1 := by
  unfold secAsymDensityBound; norm_num

/-! ### Derived sparsity + colouring constants for the §8 chromatic chain

These mirror the bipartite `secBipartiteSparsity`/
`colouringEps_bipartiteSparsity_gt`/`sec_bipartite_colouring_factor_lt`
infrastructure, with constants chosen so that the downstream Hurley-
colouring-lemma assembly closes at the headline `1.6632·Δ²`. -/

/-- The **asymmetric SDP sparsity parameter** $\sigma_p = 1 - C/2 -
1/10000 = 1 - \mathtt{secAsymDensityBound} - 1/10000$. Numerically
$\approx 0.4312$ (the `1/10000` buffer mirrors `secBipartiteSparsity`'s
`1/200` buffer; it absorbs the contradiction-framework `eps` cushion
so the SDP limit bound `L \le \mathtt{secAsymDensityBound}` flows
into `edges \le (1 - \sigma_p) \cdot \binom{\Delta_H}{2}`). -/
noncomputable def secAsymBipartiteSparsity : ℝ := 1 - secAsymDensityBound - 1/10000

lemma secAsymBipartiteSparsity_val :
    secAsymBipartiteSparsity = 1 - 0.5687 - 1/10000 := by
  unfold secAsymBipartiteSparsity; rw [secAsymDensityBound_val]

lemma secAsymBipartiteSparsity_pos : 0 < secAsymBipartiteSparsity := by
  rw [secAsymBipartiteSparsity_val]; norm_num

lemma secAsymBipartiteSparsity_le_one :
    secAsymBipartiteSparsity ≤ 1 := by
  rw [secAsymBipartiteSparsity_val]; norm_num

/-- $\sqrt{\sigma_p} \le 0.65666$ (since $0.65666^2 \approx 0.43120236
\ge 0.4312 = \sigma_p$). -/
lemma sqrt_secAsymBipartiteSparsity_le :
    Real.sqrt secAsymBipartiteSparsity ≤ 0.65666 := by
  have h1 : secAsymBipartiteSparsity ≤ 0.65666 ^ 2 := by
    rw [secAsymBipartiteSparsity_val]; norm_num
  have h2 : Real.sqrt secAsymBipartiteSparsity ≤ Real.sqrt (0.65666 ^ 2) :=
    Real.sqrt_le_sqrt h1
  have h3 : Real.sqrt (0.65666 ^ 2) = 0.65666 := Real.sqrt_sq (by norm_num)
  linarith

/-- $\sigma_p \cdot \sqrt{\sigma_p} \le 0.28316$ (since $0.4312 \times
0.65666 \approx 0.283152$, leaving a `~1e-5` cushion). -/
lemma secAsymBipartiteSparsity_mul_sqrt_le :
    secAsymBipartiteSparsity * Real.sqrt secAsymBipartiteSparsity ≤ 0.28316 := by
  have hsigma : secAsymBipartiteSparsity ≤ 0.4312 := by
    rw [secAsymBipartiteSparsity_val]; norm_num
  have hsqrt := sqrt_secAsymBipartiteSparsity_le
  calc secAsymBipartiteSparsity * Real.sqrt secAsymBipartiteSparsity
      ≤ 0.4312 * 0.65666 := by
        apply mul_le_mul hsigma hsqrt (Real.sqrt_nonneg _) (by norm_num)
    _ ≤ 0.28316 := by norm_num

/-- $\varepsilon(\sigma_p) > 0.1684$.
    $\sigma_p/2 \ge 0.4312/2 = 0.2156$;
    $\sigma_p \cdot \sqrt{\sigma_p}/6 \le 0.28316/6 \approx 0.047194$;
    $\varepsilon \ge 0.2156 - 0.04720 = 0.16840 > 0.1684$. -/
lemma colouringEps_secAsymBipartiteSparsity_gt :
    0.1684 < colouringEps secAsymBipartiteSparsity := by
  unfold colouringEps
  have hbound := secAsymBipartiteSparsity_mul_sqrt_le
  have hsigma_val := secAsymBipartiteSparsity_val
  have h1 :
      secAsymBipartiteSparsity / 2 -
        secAsymBipartiteSparsity * Real.sqrt secAsymBipartiteSparsity / 6 ≥
      secAsymBipartiteSparsity / 2 - 0.28316 / 6 := by
    linarith [div_le_div_of_nonneg_right hbound (show (0:ℝ) ≤ 6 by norm_num)]
  linarith [show secAsymBipartiteSparsity / 2 - 0.28316 / 6 > 0.1684 by
    rw [hsigma_val]; norm_num]

/-- The **asymmetric chromatic factor** $(1 - \varepsilon(\sigma_p)) \cdot
2 < 1.6632$ (numerically $\approx 2 \cdot 0.83160 = 1.66320$). The
slack between `1.6632` and the final headline `1.6633` is `0.0001`,
absorbed by the `iota = 0.0001` chain. -/
lemma sec_asym_bipartite_colouring_factor_lt :
    (1 - colouringEps secAsymBipartiteSparsity) * 2 < 1.6632 := by
  linarith [colouringEps_secAsymBipartiteSparsity_gt]

end  -- noncomputable section

end Davey2024.SecAsymmetricBipartiteBridge
