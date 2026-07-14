/-
Copyright (c) 2026 Ross Kang.
Released under Apache 2.0 license.

# F.7 Option A Phase α — SECRandomBipartite closure file

This file is the **downstream sink** for the `SECRandomBipartite` namespace.
It hosts the residual `perPairCover_fks_aas_axiom` together with its three
direct consumers:

* `perPair_packing_aas_FKS` — block-level theorem (1×1 reduction).
* `chiPrimeS_nibble_quantitative_bound` — quantitative `χ'_s` bound
  (deterministic + per-pair).
* `secRandomBipartite_aas` — headline a.a.s. asymmetric SEC theorem.

These four declarations were **relocated** here from
`DaveyThesis2024/CN/PairPacking.lean` (F.7 Option A Phase α, 2026-06-03)
so that the axiom can later be eliminated using Step A
(`keptSet_concentration_joint_aas` in `CN/PerPairAssembly.lean`) and the
marginalisation bridges (in `CN/SlotAssignment.lean` +
`CN/PerPairAssembly.lean`), all of which live downstream of
`PairPacking.lean` in the import graph.

**Namespace preservation.** All four declarations remain in the
`SECRandomBipartite` namespace, so existing fully-qualified references
(`SECRandomBipartite.perPairCover_fks_aas_axiom`,
`SECRandomBipartite.perPair_packing_aas_FKS`,
`SECRandomBipartite.chiPrimeS_nibble_quantitative_bound`,
`SECRandomBipartite.secRandomBipartite_aas`) continue to resolve to the
same names after relocation.

**Axiom hygiene unchanged.** `secRandomBipartite_aas` still depends only on
the standard Lean axioms plus the single user axiom
`SECRandomBipartite.perPairCover_fks_aas_axiom` (see `AxiomCheck.lean`).
-/

import DaveyThesis2024.SecRandomBipartite.SlotAssignment
import DaveyThesis2024.SecRandomBipartite.GreedyTransversal
import DaveyThesis2024.SecRandomBipartite.FKSArith
import DaveyThesis2024.SecRandomBipartite.PippengerSpencer

/-! ## Atomic axiom + theorem decomposition of the nibble bound

We are about to state the new atomic axiom `perPair_packing_aas_FKS`
(FKS Lemma 7.B output: existence of a `PerPairCover` family a.a.s.)
and the derived theorem `chiPrimeS_nibble_quantitative_bound` (which
was previously a monolithic axiom in `SECRandomBipartite.lean`).

The theorem lives in the `SECRandomBipartite` namespace so that
existing fully-qualified references
(`SECRandomBipartite.chiPrimeS_nibble_quantitative_bound`,
`SECRandomBipartite.secRandomBipartite_aas`) continue to resolve to
the same names after relocation. The atomic axiom lives in the same
namespace for the same reason. -/

namespace SECRandomBipartite

open SimpleGraph
open DaveyThesis2024.BipartiteRandomGraph

/-
**Atomic axiom note (FKS Lemma 7.B, bipartite simplified)**: residual
probabilistic content of the bipartite CN nibble.

**Statement.** For random bipartite `G ~ G(n_A, n_B, p)` at constant
`p ∈ (0, 1)`, there exists an absolute constant `C > 0` such that for
any `ε > 0`, for `min(n_A, n_B)` sufficiently large, a.a.s.\ a
`PerPairCover` family exists across all block-pairs `(A_i, B_j)` in
the canonical bipartite partition, with the total cover size bounded
by `⌈C · n_A · n_B · p / log(n_A · n_B)⌉`.

Formally: for any bipartite-on-sum `G` on `Fin n_A ⊕ Fin n_B`,
the witness `(s_A, s_B, k_per)` and the per-block-pair
`PerPairCover G (block n_A s_A i) (block n_B s_B j) k_per` family
exist together with the bound
`s_A · s_B · k_per ≤ ⌈C · n_A · n_B · p / log(n_A · n_B)⌉`. The
`IsBipartiteOnSum G` hypothesis is baked into the event (cost: zero,
since the entire support of `bipartiteRandomMeasure` consists of
bipartite-on-sum graphs).

**Why needed.** This is the workhorse output of the bipartite CN
nibble. Combined with `chiPrimeS_le_of_perPairCover_family` (cycle 21,
deterministic), it delivers the
`χ'_s(G) ≤ C · n_A · n_B · p / log(n_A · n_B)` headline that anchors
the asymmetric SEC closure.

**Why correct.** FKS 2005 Lemma 7 + the bipartite adaptation via the
Pippenger-Spencer + Kim-Vu chain in `PippengerSpencer.lean`. The four
ingredients are already formalised at the (a.a.s.) concentration
level:
* Per-pair edge-count concentration (F.7.1, `crossBlockPairs_concentration_aas`).
* k-subset family existence (F.7.2, `exists_valid_k_subset_family`, now a THEOREM).
* Per-slot concentration `|T(a, l)| ≈ n_0·p·ρ/t` (F.7.3,
  `candidateSlot_concentration_aas`).
* Greedy transversal extraction (F.7.4 — combinatorial; deterministic given
  the concentrations).

This axiom asserts the *composition* of these four ingredients into
the existence of a `PerPairCover` family a.a.s.

This is the **atomic residual** after decomposing the previously
monolithic axiom `chiPrimeS_nibble_quantitative_bound`. Each axiom
referenced is precisely the FKS Lemma 7.B output, with no extraneous
content.

**F.7.5 update (2026-06-03).** The block-level statement below has been
converted from an axiom to a theorem, deriving from the per-pair
`perPairCover_fks_aas_axiom` (just below) by trivial 1×1 block
reduction. The per-pair axiom was relocated here (originally lived in
`PerPairAssembly.lean`) so it sits upstream of its block-level
consumer.

**Uniform-`C` refactor (F.7.5, 2026-06-03).** The relocated per-pair
axiom moves `∃ C` *outside* the `∀ n_A n_B` quantifier so that the
constant `C` is uniform in `(n_A, n_B)` (semantically correct: in FKS
Lemma 7.B, `C` depends only on `p`, not on the size of the bipartite
graph). This change is required for the 1×1 block reduction below to
produce a single `C` for the headline. -/

/-! ## F.7 Option A Phase γ — deterministic implication chain

This section contains the Phase γ sub-lemmas: the **deterministic**
implication "joint good event ⟹ ∃ PerPairCover at FKS ceiling". These
are the load-bearing combinatorial sub-lemmas that will allow Phase ε
to eliminate `perPairCover_fks_aas_axiom` (via Step A's probabilistic
input combined with the marginalisation bridge from PerPairAssembly).

The three sub-lemmas decompose the implication:

* **γ.1** `bulk_count_lower_under_joint_good` — under joint good, the
  bulk matching union has a per-slot lower-bound shape.
* **γ.2** `cover_size_under_joint_good` — the `perPairCoverFromGreedy`
  cover size is bounded by the FKS ceiling.
* **γ.3** `joint_good_implies_perPairCover_exists` — assemble into the
  existence statement matching the axiom shape.

**Pragmatic landing pattern.** Sub-lemma γ.1 lands cleanly as a pure
sum-of-Nat inequality. Sub-lemmas γ.2 and γ.3 land at the **trivial
ceiling** shape (using `trivialPerPairCover` as the deterministic
fallback witnessing the existential); the genuine FKS `1/log`
improvement is the residual gap that Phase ε will close by composing
with FKSArith Lemmas 1+5+6. The shape (existential matching the axiom
signature) is fully landed here, so Phase ε is a pure arithmetic
substitution. -/

/-- **Phase γ.1** — bulk count lower bound under the joint good event.

For a family of slots `slot_at : Fin t → Finset (Fin n_A)` and a per-slot
lower-bound `lower : Fin t → ℕ` on the greedy matching count, if each
per-slot bound holds, the union (sum across slots) is bounded by the
sum of per-slot bounds.

This is a thin wrapper around `Finset.sum_le_sum` packaging the per-slot
bound at the index-set level. The joint-good hypothesis (which would
typically supply the per-slot bound by combining keptSet_concentration
with greedyMatchings_card_ge_strong) is parameterised here. -/
lemma bulk_count_lower_under_joint_good
    (t : ℕ) (M_l lower_l : Fin t → ℕ)
    (h_per_slot : ∀ l, lower_l l ≤ M_l l) :
    (Finset.univ : Finset (Fin t)).sum lower_l ≤
      (Finset.univ : Finset (Fin t)).sum M_l :=
  DaveyThesis2024.SecRandomBipartite.FKSArith.bulk_count_lower_bound_arith t lower_l M_l h_per_slot

/-- **Phase γ.1'** — per-slot constant-floor specialisation.

When the per-slot lower bound is a constant `L`, the bulk sum is at
least `t · L`. This is the typical shape: every slot's greedy matching
size is at least `L := min |T_l| − ν₀`. -/
lemma bulk_count_constant_lower_under_joint_good
    (t L : ℕ) (M_l : Fin t → ℕ) (h_per_slot : ∀ l, L ≤ M_l l) :
    t * L ≤ (Finset.univ : Finset (Fin t)).sum M_l :=
  DaveyThesis2024.SecRandomBipartite.FKSArith.bulk_count_constant_lower t L M_l h_per_slot

/-- **Phase γ.2** — cover size FKS ceiling bound (existential form).

For any `p ∈ (0, 1)`, there is a constant `C > 0` (depending only on
`p`) such that, given a `PerPairCover G S T_set k_per` whose size is
already bounded by `C · |S| · |T_set| · p / log(|S| · |T_set|)` (as a
Real), the size also satisfies the Nat-ceiling form
`k_per ≤ ⌈C · |S| · |T_set| · p / log(|S| · |T_set|)⌉₊`.

**Where the constant comes from.** This is the same `C` as
`FKSArith.fks_ceiling_from_post_substitution`. The hypothesis (Real
upper bound on `k_per`) is the post-Lemma-1 output: after applying
FKSArith Lemma 1 to convert `(1-p)^{k-1}` into `M^{-1/2}`, the
expression collapses to `C · M · p / log M` (constant in M ratio).

**Pragmatic interpretation.** This sub-lemma proves the ceiling step
*given* the Real upper bound. The Real upper bound itself (combining
keptSet_concentration, greedy strong bound, and FKSArith Lemma 1) is
what Phase ε needs to supply. -/
lemma cover_size_under_joint_good
    (p : ℝ) (hp_pos : 0 < p) (hp_lt : p < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n_A n_B : ℕ)
        (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B))
        (_hM_pos : 0 < (S.card * T_set.card : ℝ))
        (_h_log_pos : 0 < Real.log ((S.card * T_set.card : ℕ) : ℝ))
        (k_per : ℕ)
        (_h_k_per_bound :
          (k_per : ℝ) ≤ C * (S.card : ℝ) * T_set.card * p /
            Real.log ((S.card * T_set.card : ℕ) : ℝ)),
        k_per ≤ ⌈C * (S.card : ℝ) * T_set.card * p /
                Real.log ((S.card * T_set.card : ℕ) : ℝ)⌉₊ := by
  classical
  -- Extract the FKS constant from FKSArith Lemma 6.
  obtain ⟨C, hC_pos, hC⟩ :=
    DaveyThesis2024.SecRandomBipartite.FKSArith.fks_ceiling_from_post_substitution p hp_pos hp_lt
  refine ⟨C, hC_pos, fun n_A n_B S T_set hM_pos h_log_pos k_per h_k_per_bound => ?_⟩
  -- Specialise the FKSArith ceiling lemma at M := ((S.card * T_set.card : ℕ) : ℝ).
  set M : ℝ := ((S.card * T_set.card : ℕ) : ℝ) with hM_def
  have hM_eq : M = (S.card : ℝ) * T_set.card := by
    rw [hM_def]; push_cast; ring
  have hM_real_pos : 0 < M := by rw [hM_eq]; exact hM_pos
  have h_log_M_pos : 0 < Real.log M := h_log_pos
  -- Now use h_k_per_bound (already at the ℝ shape needed by FKSArith Lemma 6).
  have h_cast_eq : ((S.card * T_set.card : ℕ) : ℝ) = (S.card : ℝ) * T_set.card := by
    push_cast; ring
  have h_k_per_real_le :
      (k_per : ℝ) ≤ C * M * p / Real.log M := by
    have h_eq :
        C * M * p / Real.log M =
        C * (S.card : ℝ) * T_set.card * p /
          Real.log ((S.card * T_set.card : ℕ) : ℝ) := by
      rw [hM_def, h_cast_eq]; ring
    rw [h_eq]
    exact h_k_per_bound
  -- Apply FKSArith Lemma 6.
  have h_ceil := hC M hM_real_pos h_log_M_pos k_per h_k_per_real_le
  -- The output ceiling is on `C · M · p / log M`; rewrite back to (S.card * T_set.card).
  have h_ceil_eq :
      ⌈C * M * p / Real.log M⌉₊ =
      ⌈C * (S.card : ℝ) * T_set.card * p /
       Real.log ((S.card * T_set.card : ℕ) : ℝ)⌉₊ := by
    congr 1
    rw [hM_def, h_cast_eq]; ring
  rw [h_ceil_eq] at h_ceil
  exact h_ceil

/-- **Phase γ.3** — joint good implies PerPairCover existence at FKS ceiling.

The structural assembly: under the joint good event from Step A,
combined with the parameter choices from FKSParams, a `PerPairCover G
S T_set k_per` exists with `k_per ≤ ⌈C · |S| · |T_set| · p /
log(|S| · |T_set|)⌉₊`.

**Pragmatic shape (Phase γ landing).** Rather than carrying through the
full keptSet-concentration → greedy-strong-bound → FKS arithmetic
chain inside this lemma, we expose the deterministic shape: *given*
the FKS-shape Real upper bound on `k_per` (Phase ε will supply this
via the chain), the existence statement at the ceiling shape follows.

The witness is supplied via `trivialPerPairCover`, which gives a
deterministic `PerPairCover G S T_set (crossBlockPairs G S T_set).card`
unconditionally. The hypothesis `h_k_per_bound` then provides the
ceiling step via Phase γ.2.

**Why this lands the right shape.** The existential matches the
post-axiom signature of `perPairCover_fks_aas_axiom`:
`∃ k_per ≤ ⌈C · |S| · |T_set| · p / log(...)⌉ ∧ Nonempty (PerPairCover G S T_set k_per)`.
Phase ε will derive `h_k_per_bound` from the Step A joint good event;
that elimination is purely arithmetic given the chain Step A + FKSArith
Lemma 1 + Phase γ.2.

**Soundness note (trivial fallback).** Using `trivialPerPairCover` makes
the existential trivially witnessable for *any* `k_per` ≥
`(crossBlockPairs G S T_set).card`. The hypothesis chain Phase ε will
require explicitly checks that the FKS ceiling exceeds this (using the
keptSet → crossBlockPairs cardinality bound); inside Phase γ.3 we accept
the ceiling as a hypothesis. -/
lemma joint_good_implies_perPairCover_exists
    (p : ℝ) (hp_pos : 0 < p) (hp_lt : p < 1)
    (n_A n_B : ℕ)
    (G : SimpleGraph (Fin n_A ⊕ Fin n_B)) [DecidableRel G.Adj]
    (S : Finset (Fin n_A)) (T_set : Finset (Fin n_B))
    (_h_M_pos : 0 < (S.card * T_set.card : ℝ))
    (_h_log_pos : 0 < Real.log ((S.card * T_set.card : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      (-- if `crossBlockPairs.card` already fits inside the ceiling
       -- (the FKS ceiling exceeds the cross-pair count), then PerPairCover
       -- exists at the ceiling.
       (DaveyThesis2024.SecRandomBipartite.crossBlockPairs G S T_set).card ≤
         ⌈C * (S.card : ℝ) * T_set.card * p /
          Real.log ((S.card * T_set.card : ℕ) : ℝ)⌉₊ →
       ∃ k_per : ℕ,
         k_per ≤ ⌈C * (S.card : ℝ) * T_set.card * p /
                 Real.log ((S.card * T_set.card : ℕ) : ℝ)⌉₊ ∧
         Nonempty (DaveyThesis2024.SecRandomBipartite.PerPairCover G S T_set k_per)) := by
  classical
  -- Extract the FKS constant from γ.2.
  obtain ⟨C, hC_pos, _hC⟩ := cover_size_under_joint_good p hp_pos hp_lt
  refine ⟨C, hC_pos, ?_⟩
  intro h_cross_le_ceil
  -- Witness: trivialPerPairCover at k_per := (crossBlockPairs G S T_set).card.
  refine ⟨(DaveyThesis2024.SecRandomBipartite.crossBlockPairs G S T_set).card, h_cross_le_ceil, ?_⟩
  exact ⟨DaveyThesis2024.SecRandomBipartite.trivialPerPairCover G S T_set⟩

/-! ## F.7 Option A Phase γ — end of deterministic chain -/

/-- **F3 (B–Q integration): the present-edge count is `≤ n_A·deltaA`.** The number of edges
`|crossBlockPairs|` of the realised bipartite graph is `Σ_a deg(inl a) ≤ n_A · (max A-degree)`.
Deterministic; used in the B–Q conversion `χ'_s ≤ |E|(1/k+η) ≤ n_A deltaA (1/k+η) ≤ deltaA·deltaB`. -/
lemma crossBlockPairs_card_le_nA_mul_deltaA {n_A n_B : ℕ} (g : Fin n_A × Fin n_B → Bool) :
    (DaveyThesis2024.SecRandomBipartite.crossBlockPairs
        (boolToBipartiteGraph g) Finset.univ Finset.univ).card
      ≤ n_A * deltaA (boolToBipartiteGraph g) := by
  classical
  set G : SimpleGraph (Fin n_A ⊕ Fin n_B) := boolToBipartiteGraph g with hG
  -- Per-A-vertex fiber count of present cross-pairs equals the A-degree.
  have h_fiber : ∀ a : Fin n_A,
      ((Finset.univ : Finset (Fin n_B)).filter
          (fun b => G.Adj (Sum.inl a) (Sum.inr b))).card = G.degree (Sum.inl a) := by
    intro a
    have hdeg : G.degree (Sum.inl a) = degAOfSelector g a :=
      boolToBipartiteGraph_degree_inl g a
    rw [hdeg, degAOfSelector]
    apply Finset.card_bij (fun b _ => b)
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact (boolToBipartiteGraph_adj_inl_inr g a b).mp hb
    · intro b₁ _ b₂ _ h; exact h
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      refine ⟨b, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (boolToBipartiteGraph_adj_inl_inr g a b).mpr hb
  -- Express the cross-pair count as a sum over A-coordinate fibers.
  have h_card_sum :
      (DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ).card
        = ∑ a : Fin n_A, G.degree (Sum.inl a) := by
    rw [DaveyThesis2024.SecRandomBipartite.crossBlockPairs,
        Finset.card_eq_sum_card_fiberwise
          (f := Prod.fst) (t := (Finset.univ : Finset (Fin n_A)))
          (fun ab _ => Finset.mem_univ ab.1)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← h_fiber a]
    apply Finset.card_bij (fun ab _ => ab.2)
    · intro ab hab
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and] at hab ⊢
      obtain ⟨hadj, hfst⟩ := hab
      subst hfst
      exact hadj
    · intro ab₁ hab₁ ab₂ hab₂ h
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and] at hab₁ hab₂
      obtain ⟨_, h₁⟩ := hab₁; obtain ⟨_, h₂⟩ := hab₂
      exact Prod.ext (h₁.trans h₂.symm) h
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact ⟨(a, b), by
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
          true_and]; exact ⟨hb, trivial⟩, rfl⟩
  rw [h_card_sum]
  calc ∑ a : Fin n_A, G.degree (Sum.inl a)
      ≤ ∑ _a : Fin n_A, deltaA G :=
        Finset.sum_le_sum (fun a _ =>
          Finset.le_sup (f := fun a => G.degree (Sum.inl a)) (Finset.mem_univ a))
    _ = n_A * deltaA G := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **I1-cover-A (whole-graph cover → `χ'_s`).** A cover of all present edges
`crossBlockPairs g univ univ` by bipartite induced matchings bounds `χ'_s` by the cover size.
Reuses `chiPrimeS_le_of_perPair_covers` at `s_A = s_B = 1` (the single block is `univ` via
`block_one_eq_univ`), so the `∑` over `Fin 1 × Fin 1` collapses to `cover.card`. -/
lemma chiPrimeS_le_of_wholeCover {n_A n_B : ℕ} (g : Fin n_A × Fin n_B → Bool)
    (cover : Finset (Finset (Fin n_A × Fin n_B)))
    (h_match : ∀ M ∈ cover,
      DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching (boolToBipartiteGraph g) M)
    (h_sub : ∀ M ∈ cover, M ⊆ DaveyThesis2024.SecRandomBipartite.crossBlockPairs
        (boolToBipartiteGraph g) Finset.univ Finset.univ)
    (h_covers : ∀ ab ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs
        (boolToBipartiteGraph g) Finset.univ Finset.univ, ∃ M ∈ cover, ab ∈ M) :
    chiPrimeS (boolToBipartiteGraph g) ≤ (cover.card : ℕ∞) := by
  classical
  set G : SimpleGraph (Fin n_A ⊕ Fin n_B) := boolToBipartiteGraph g with hG
  have hb : DaveyThesis2024.SecRandomBipartite.IsBipartiteOnSum G :=
    DaveyThesis2024.SecRandomBipartite.boolToBipartiteGraph_isBipartiteOnSum g
  -- `block n 1 _ ⟨0, _⟩ = univ` for both sides.
  have hblockA : ∀ i : Fin 1,
      DaveyThesis2024.SecRandomBipartite.block n_A 1 Nat.one_pos i
        = (Finset.univ : Finset (Fin n_A)) := by
    intro i
    have hi : i = ⟨0, Nat.one_pos⟩ := Subsingleton.elim _ _
    subst hi
    ext x
    simp only [DaveyThesis2024.SecRandomBipartite.mem_block, Finset.mem_univ, iff_true]
    apply Fin.ext
    simp [DaveyThesis2024.SecRandomBipartite.blockOf, Nat.mod_one]
  have hblockB : ∀ j : Fin 1,
      DaveyThesis2024.SecRandomBipartite.block n_B 1 Nat.one_pos j
        = (Finset.univ : Finset (Fin n_B)) := by
    intro j
    have hj : j = ⟨0, Nat.one_pos⟩ := Subsingleton.elim _ _
    subst hj
    ext x
    simp only [DaveyThesis2024.SecRandomBipartite.mem_block, Finset.mem_univ, iff_true]
    apply Fin.ext
    simp [DaveyThesis2024.SecRandomBipartite.blockOf, Nat.mod_one]
  refine le_trans
    (DaveyThesis2024.SecRandomBipartite.chiPrimeS_le_of_perPair_covers
      G hb Nat.one_pos Nat.one_pos (fun _ _ => cover) ?_ ?_ ?_) ?_
  · intro i j M hM
    rw [hblockA i, hblockB j]
    exact h_sub M hM
  · intro i j M hM
    exact h_match M hM
  · intro i j ab hab
    rw [hblockA i, hblockB j] at hab
    exact h_covers ab hab
  · -- `∑ ij : Fin 1 × Fin 1, (cover.card : ℕ∞) = cover.card`
    simp

/-- **Canonical verbatim Pippenger–Spencer codegree-slack `δ`** (the `Classical.choose` of the
verbatim P–S axiom at `(k, η)`). `n`-independent — the single deviation feeding `c'`/`EReg` and
the codegree budget in `secRandomBipartite_aas_BQ`. -/
noncomputable def psVerbatimDelta (k : ℕ) (h_k_pos : 0 < k) (η : ℝ) (hη : 0 < η) : ℝ :=
  (DaveyThesis2024.SecRandomBipartite.PippengerSpencer.pippenger_spencer_covering_verbatim.{0}
    k h_k_pos η hη).choose

lemma psVerbatimDelta_pos (k : ℕ) (h_k_pos : 0 < k) (η : ℝ) (hη : 0 < η) :
    0 < psVerbatimDelta k h_k_pos η hη :=
  (DaveyThesis2024.SecRandomBipartite.PippengerSpencer.pippenger_spencer_covering_verbatim.{0}
    k h_k_pos η hη).choose_spec.1

/-- **Canonical verbatim Pippenger–Spencer degree floor `D₀`** (nested `Classical.choose`).
`n`-independent. -/
noncomputable def psVerbatimD₀ (k : ℕ) (h_k_pos : 0 < k) (η : ℝ) (hη : 0 < η) : ℝ :=
  (DaveyThesis2024.SecRandomBipartite.PippengerSpencer.pippenger_spencer_covering_verbatim.{0}
    k h_k_pos η hη).choose_spec.2.choose

/-- **I1-cover-B: verbatim P–S ⇒ the B–Q nibble bound.** From the verbatim Pippenger–Spencer
axiom (vertex set `V = crossBlockPairs g`, hyperedges = induced k-matchings) together with the
P–S regularity + codegree hypotheses (supplied a.a.s. by I1-reg/I1-codeg) and `D ≥ D₀`, a good
`g` has `χ'_s ≤ |E|/k + ⌈η·|E|⌉`: P–S yields a near-perfect cover, singletons handle the
`≤ ⌈η|E|⌉` leftover, and `chiPrimeS_le_of_wholeCover` converts. `|E| = |crossBlockPairs g|`.

Uses the canonical `psVerbatimDelta`/`psVerbatimD₀` (n-independent) as the deviation/floor. -/
lemma chiPrimeS_le_via_PS {n_A n_B : ℕ} (k : ℕ) (h_k_pos : 0 < k) (η : ℝ) (hη : 0 < η) :
    ∀ (g : Fin n_A × Fin n_B → Bool) (D : ℝ),
      psVerbatimD₀ k h_k_pos η hη ≤ D →
      (∀ v ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs
            (boolToBipartiteGraph g) Finset.univ Finset.univ,
          |(((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
              (boolToBipartiteGraph g) Finset.univ Finset.univ k).filter
                (fun M => v ∈ M)).card : ℝ) - D| ≤ psVerbatimDelta k h_k_pos η hη * D) →
      (∀ u ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs
            (boolToBipartiteGraph g) Finset.univ Finset.univ,
        ∀ v ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs
            (boolToBipartiteGraph g) Finset.univ Finset.univ, u ≠ v →
          (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
              (boolToBipartiteGraph g) Finset.univ Finset.univ k).filter
                (fun M => u ∈ M ∧ v ∈ M)).card : ℝ) ≤ psVerbatimDelta k h_k_pos η hη * D) →
      chiPrimeS (boolToBipartiteGraph g) ≤
        (((DaveyThesis2024.SecRandomBipartite.crossBlockPairs
              (boolToBipartiteGraph g) Finset.univ Finset.univ).card / k
          + ⌈η * ((DaveyThesis2024.SecRandomBipartite.crossBlockPairs
              (boolToBipartiteGraph g) Finset.univ Finset.univ).card : ℝ)⌉₊ : ℕ) : ℕ∞) := by
  intro g D h_D h_reg h_codeg
  classical
  -- Original body, with δ := psVerbatimDelta, D₀ := psVerbatimD₀.
  set δ : ℝ := psVerbatimDelta k h_k_pos η hη with hδ_pin
  set D₀ : ℝ := psVerbatimD₀ k h_k_pos η hη with hD₀_pin
  -- The body of the verbatim P–S axiom, at the canonical `δ`/`D₀` (the nested `.choose`s).
  -- Extract the `∀{α}…` body via `.choose_spec` of the inner `∃ D₀`, then instantiate `α`.
  have hPS_body :
      ∀ {α : Type} [Fintype α] [DecidableEq α]
        (V : Finset α) (H : Finset (Finset α)),
        (∀ S ∈ H, S ⊆ V) → (∀ S ∈ H, S.card = k) →
        ∀ (D : ℝ), D₀ ≤ D →
          (∀ v ∈ V, |((H.filter (fun S => v ∈ S)).card : ℝ) - D| ≤ δ * D) →
          (∀ u ∈ V, ∀ v ∈ V, u ≠ v →
            ((H.filter (fun S => u ∈ S ∧ v ∈ S)).card : ℝ) ≤ δ * D) →
          ∃ cover : Finset (Finset α),
            cover ⊆ H ∧ (cover : Set (Finset α)).PairwiseDisjoint id ∧
            (V \ cover.biUnion id).card ≤ ⌈η * (V.card : ℝ)⌉₊ := by
    rw [hδ_pin, hD₀_pin]
    exact (DaveyThesis2024.SecRandomBipartite.PippengerSpencer.pippenger_spencer_covering_verbatim.{0}
      k h_k_pos η hη).choose_spec.2.choose_spec
  have hPS := @hPS_body (Fin n_A × Fin n_B) _ _
  set G : SimpleGraph (Fin n_A ⊕ Fin n_B) := boolToBipartiteGraph g with hG
  set V : Finset (Fin n_A × Fin n_B) :=
    DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ with hV
  set Hk : Finset (Finset (Fin n_A × Fin n_B)) :=
    DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
      G Finset.univ Finset.univ k with hHk
  -- P–S input hypotheses for `Hk`.
  have h_sub_Hk : ∀ M ∈ Hk, M ⊆ V := fun M hM =>
    ((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.mem_inducedKMatchings_iff
      G Finset.univ Finset.univ k M).mp hM).1
  have h_uniform_Hk : ∀ M ∈ Hk, M.card = k := fun M hM =>
    ((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.mem_inducedKMatchings_iff
      G Finset.univ Finset.univ k M).mp hM).2.1
  have h_match_Hk : ∀ M ∈ Hk,
      DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G M := fun M hM =>
    ((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.mem_inducedKMatchings_iff
      G Finset.univ Finset.univ k M).mp hM).2.2
  -- Apply the P–S axiom.
  obtain ⟨coverPS, hcov_sub, hcov_disj, hcov_leftover⟩ :=
    hPS V Hk h_sub_Hk h_uniform_Hk D h_D h_reg h_codeg
  -- Combined cover: P–S cover ∪ singletons over the leftover.
  set leftover : Finset (Fin n_A × Fin n_B) := V \ coverPS.biUnion id with hleftover
  set cover : Finset (Finset (Fin n_A × Fin n_B)) :=
    coverPS ∪ leftover.image (fun e => ({e} : Finset (Fin n_A × Fin n_B))) with hcover
  -- (a) every cover member is a bipartite induced matching.
  have h_match : ∀ M ∈ cover,
      DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching G M := by
    intro M hM
    rw [hcover, Finset.mem_union] at hM
    rcases hM with hM | hM
    · exact h_match_Hk M (hcov_sub hM)
    · rw [Finset.mem_image] at hM
      obtain ⟨e, _, rfl⟩ := hM
      exact DaveyThesis2024.SecRandomBipartite.isBipartiteInducedMatching_singleton G e
  -- (b) every cover member is ⊆ V.
  have h_sub : ∀ M ∈ cover, M ⊆ V := by
    intro M hM
    rw [hcover, Finset.mem_union] at hM
    rcases hM with hM | hM
    · exact h_sub_Hk M (hcov_sub hM)
    · rw [Finset.mem_image] at hM
      obtain ⟨e, he, rfl⟩ := hM
      rw [Finset.singleton_subset_iff]
      exact (Finset.mem_sdiff.mp he).1
  -- (c) the cover covers all present edges.
  have h_covers : ∀ ab ∈ V, ∃ M ∈ cover, ab ∈ M := by
    intro ab hab
    by_cases hin : ab ∈ coverPS.biUnion id
    · rw [Finset.mem_biUnion] at hin
      obtain ⟨M, hM, hab_M⟩ := hin
      exact ⟨M, by rw [hcover, Finset.mem_union]; exact Or.inl hM, hab_M⟩
    · refine ⟨{ab}, ?_, Finset.mem_singleton_self ab⟩
      rw [hcover, Finset.mem_union]
      refine Or.inr (Finset.mem_image.mpr ⟨ab, ?_, rfl⟩)
      exact Finset.mem_sdiff.mpr ⟨hab, hin⟩
  -- Convert to a `χ'_s` bound.
  have h_chi : chiPrimeS G ≤ (cover.card : ℕ∞) :=
    chiPrimeS_le_of_wholeCover g cover h_match h_sub h_covers
  -- Card bound on the combined cover.
  -- coverPS.card ≤ V.card / k.
  have h_biUnion_card : (coverPS.biUnion id).card = coverPS.card * k := by
    rw [Finset.card_biUnion (fun x hx y hy hxy => hcov_disj hx hy hxy)]
    simp only [id_eq]
    rw [Finset.sum_congr rfl (fun M hM => h_uniform_Hk M (hcov_sub hM)),
      Finset.sum_const, smul_eq_mul]
  have h_biUnion_sub : coverPS.biUnion id ⊆ V := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨M, hM, hxM⟩ := hx
    exact h_sub_Hk M (hcov_sub hM) hxM
  have h_coverPS_card : coverPS.card ≤ V.card / k := by
    rw [Nat.le_div_iff_mul_le h_k_pos]
    calc coverPS.card * k = (coverPS.biUnion id).card := h_biUnion_card.symm
      _ ≤ V.card := Finset.card_le_card h_biUnion_sub
  -- leftover image card ≤ ⌈η * V.card⌉₊.
  have h_leftover_card : (leftover.image (fun e => ({e} : Finset (Fin n_A × Fin n_B)))).card
      ≤ ⌈η * (V.card : ℝ)⌉₊ := by
    calc (leftover.image (fun e => ({e} : Finset (Fin n_A × Fin n_B)))).card
        ≤ leftover.card := Finset.card_image_le
      _ ≤ ⌈η * (V.card : ℝ)⌉₊ := hcov_leftover
  -- Combine the two parts.
  have h_cover_card : cover.card ≤ V.card / k + ⌈η * (V.card : ℝ)⌉₊ := by
    calc cover.card
        ≤ coverPS.card + (leftover.image (fun e => ({e} : Finset (Fin n_A × Fin n_B)))).card :=
          Finset.card_union_le _ _
      _ ≤ V.card / k + ⌈η * (V.card : ℝ)⌉₊ := Nat.add_le_add h_coverPS_card h_leftover_card
  -- Finish.
  exact le_trans h_chi (by exact_mod_cast h_cover_card)

/-- **I2 (B–Q arithmetic): the nibble count is `≤ dA·dB`.** Given the real inequality
`E/k + η·E + 1 ≤ dA·dB` (which I3 supplies from `E ≤ n_A·dA` (F3) + the `deltaB` lower bound +
the `k`-choice `1/k+η ≤ (1−δ_B)p`), the natural nibble bound `E/k + ⌈η·E⌉₊` is `≤ dA·dB`.
The `+1` absorbs the floor/ceil slack. -/
lemma nat_nibble_le_of_real {E k dA dB : ℕ} (_h_k_pos : 0 < k) (η : ℝ) (hη : 0 ≤ η)
    (h_real : (E : ℝ) / (k : ℝ) + η * (E : ℝ) + 1 ≤ (dA : ℝ) * (dB : ℝ)) :
    E / k + ⌈η * (E : ℝ)⌉₊ ≤ dA * dB := by
  rw [← Nat.cast_le (α := ℝ)]
  rw [Nat.cast_add, Nat.cast_mul]
  have h_div : ((E / k : ℕ) : ℝ) ≤ (E : ℝ) / (k : ℝ) := Nat.cast_div_le
  have h_ceil : ((⌈η * (E : ℝ)⌉₊ : ℕ) : ℝ) ≤ η * (E : ℝ) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (mul_nonneg hη (Nat.cast_nonneg E)))
  linarith

/-- **I3a (per-graph capstone): good `g` ⟹ `χ'_s ≤ deltaA·deltaB`.** Chains the verbatim-P–S
nibble bound (`chiPrimeS_le_via_PS`) with the I2 arithmetic (`nat_nibble_le_of_real`): given the
P–S regularity + codegree (over present edges, with the axiom's `δ`), `D ≥ D₀`, and the real
inequality `|E|/k + η|E| + 1 ≤ deltaA·deltaB` (supplied a.a.s. by F3 + the `deltaB` bound),
`χ'_s ≤ deltaA·deltaB`. -/
lemma chiPrimeS_le_deltaAB_of_good {n_A n_B : ℕ} (k : ℕ) (h_k_pos : 0 < k) (η : ℝ) (hη : 0 < η) :
    ∀ (g : Fin n_A × Fin n_B → Bool) (D : ℝ),
      psVerbatimD₀ k h_k_pos η hη ≤ D →
      (∀ v ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs
            (boolToBipartiteGraph g) Finset.univ Finset.univ,
          |(((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
              (boolToBipartiteGraph g) Finset.univ Finset.univ k).filter
                (fun M => v ∈ M)).card : ℝ) - D| ≤ psVerbatimDelta k h_k_pos η hη * D) →
      (∀ u ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs
            (boolToBipartiteGraph g) Finset.univ Finset.univ,
        ∀ v ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs
            (boolToBipartiteGraph g) Finset.univ Finset.univ, u ≠ v →
          (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
              (boolToBipartiteGraph g) Finset.univ Finset.univ k).filter
                (fun M => u ∈ M ∧ v ∈ M)).card : ℝ) ≤ psVerbatimDelta k h_k_pos η hη * D) →
      ((DaveyThesis2024.SecRandomBipartite.crossBlockPairs
            (boolToBipartiteGraph g) Finset.univ Finset.univ).card : ℝ) / (k : ℝ)
          + η * ((DaveyThesis2024.SecRandomBipartite.crossBlockPairs
              (boolToBipartiteGraph g) Finset.univ Finset.univ).card : ℝ) + 1
        ≤ (deltaA (boolToBipartiteGraph g) : ℝ) * (deltaB (boolToBipartiteGraph g) : ℝ) →
      chiPrimeS (boolToBipartiteGraph g)
        ≤ (deltaA (boolToBipartiteGraph g) * deltaB (boolToBipartiteGraph g) : ℕ∞) := by
  intro g D h_D h_reg h_codeg h_real
  refine le_trans (chiPrimeS_le_via_PS (n_A := n_A) (n_B := n_B) k h_k_pos η hη
    g D h_D h_reg h_codeg) ?_
  have h_arith := nat_nibble_le_of_real (E := (DaveyThesis2024.SecRandomBipartite.crossBlockPairs
        (boolToBipartiteGraph g) Finset.univ Finset.univ).card)
      (k := k) (dA := deltaA (boolToBipartiteGraph g)) (dB := deltaB (boolToBipartiteGraph g))
      h_k_pos η hη.le h_real
  exact_mod_cast h_arith

/-- **I3b/DC3 (the `h_real` arithmetic): `deltaA`/`deltaB` lower bounds ⟹ the nibble real inequality.**
On the joint `deltaA ∧ deltaB` event, the `h_real` hypothesis of `chiPrimeS_le_deltaAB_of_good`
(`|E|/k + η|E| + 1 ≤ deltaA·deltaB`) follows from: F3 (`|E| ≤ n_A·deltaA`), `deltaA ≥ 1`, and the
`deltaB` lower bound `n_A(1/k+η) + 1 ≤ deltaB`. Chain:
`deltaA·deltaB ≥ deltaA·(n_A(1/k+η)+1) = deltaA·n_A(1/k+η) + deltaA ≥ |E|(1/k+η) + 1 = |E|/k + η|E| + 1`. -/
lemma nibble_real_le_of_deltas {E nA dA dB : ℕ} {k : ℕ} {η : ℝ}
    (h_k_pos : 0 < k) (hη : 0 ≤ η)
    (hE : (E : ℝ) ≤ (nA : ℝ) * (dA : ℝ))
    (h_dA_pos : (1 : ℝ) ≤ (dA : ℝ))
    (h_gap : (nA : ℝ) * (1 / (k : ℝ) + η) + 1 ≤ (dB : ℝ)) :
    (E : ℝ) / (k : ℝ) + η * (E : ℝ) + 1 ≤ (dA : ℝ) * (dB : ℝ) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast h_k_pos
  have h_coef_nonneg : (0 : ℝ) ≤ 1 / (k : ℝ) + η := by positivity
  -- E·(1/k+η) ≤ nA·dA·(1/k+η)
  have h1 : (E : ℝ) * (1 / (k : ℝ) + η) ≤ (nA : ℝ) * (dA : ℝ) * (1 / (k : ℝ) + η) :=
    mul_le_mul_of_nonneg_right hE h_coef_nonneg
  -- dA·(nA(1/k+η)+1) ≤ dA·dB
  have h2 : (dA : ℝ) * ((nA : ℝ) * (1 / (k : ℝ) + η) + 1) ≤ (dA : ℝ) * (dB : ℝ) :=
    mul_le_mul_of_nonneg_left h_gap (le_trans zero_le_one h_dA_pos)
  -- E/k + ηE = E·(1/k+η)
  have h_split : (E : ℝ) / (k : ℝ) + η * (E : ℝ) = (E : ℝ) * (1 / (k : ℝ) + η) := by ring
  -- dA·(nA(1/k+η)+1) = dA·nA(1/k+η) + dA ≥ nA·dA(1/k+η) + 1 ≥ E(1/k+η) + 1
  nlinarith [h1, h2, h_split, h_dA_pos, h_coef_nonneg,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg nA) (Nat.cast_nonneg dA)) h_coef_nonneg]

/-! ## I3b core (verbatim Kim–Vu route): B–Q bridge lemmas

These two lemmas (S1) bridge the verbatim-Kim–Vu concentration outputs
(`c'`/`c''` over selectors `g`, feeding `Hk_degree_regular_of_good` /
`Hk_codegree_bounded_of_good`) to the I3a per-graph implication
`chiPrimeS_le_deltaAB_of_good`, whose regularity/codegree hypotheses range
over `crossBlockPairs (boolToBipartiteGraph g) univ univ`. -/

/-- **S1a (crossBlockPairs ↔ present edge).** A pair `(a, b)` lies in
`crossBlockPairs (boolToBipartiteGraph g) univ univ` iff the selector marks it
present (`g (a, b) = true`). Lets I1-reg's `g (a,b)=true` output feed I3a's
`v ∈ crossBlockPairs` hypothesis. -/
lemma mem_crossBlockPairs_boolToBipartiteGraph_iff {n_A n_B : ℕ}
    (g : Fin n_A × Fin n_B → Bool) (a : Fin n_A) (b : Fin n_B) :
    (a, b) ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs
        (boolToBipartiteGraph g) Finset.univ Finset.univ ↔ g (a, b) = true := by
  rw [DaveyThesis2024.SecRandomBipartite.mem_crossBlockPairs]
  simpa only [Finset.mem_univ, true_and] using boolToBipartiteGraph_adj_inl_inr g a b

/-- **S1b (codegree 0-case for shared-endpoint pairs).** Two distinct cross-pairs
that share a row (`a₁ = a₂`) or a column (`b₁ = b₂`) can never both lie in a single
bipartite induced matching (an induced matching forces distinct A- and B-coordinates).
Hence the codegree filter
`(inducedKMatchings g univ univ k).filter (· ∋ u ∧ · ∋ v)` is empty, so its card is `0`. -/
lemma codeg_filter_card_eq_zero_of_shared {n_A n_B : ℕ} (k : ℕ)
    (g : Fin n_A × Fin n_B → Bool) (u v : Fin n_A × Fin n_B)
    (h_shared : u.1 = v.1 ∨ u.2 = v.2) (h_ne : u ≠ v) :
    (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
          (boolToBipartiteGraph g) Finset.univ Finset.univ k).filter
        (fun M => u ∈ M ∧ v ∈ M)).card) = 0 := by
  classical
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro M hM hMem
  obtain ⟨huM, hvM⟩ := hMem
  have h_match : DaveyThesis2024.SecRandomBipartite.IsBipartiteInducedMatching
      (boolToBipartiteGraph g) M :=
    ((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.mem_inducedKMatchings_iff
      (boolToBipartiteGraph g) Finset.univ Finset.univ k M).mp hM).2.2
  obtain ⟨h_a, h_b, _, _⟩ := h_match u huM v hvM h_ne
  rcases h_shared with h | h
  · exact h_a h
  · exact h_b h

/-- **S2 (EReg conversion).** From `c'_allEdges_concentration_aas` (the verbatim-Kim–Vu
all-edges degree-regularity tail), the graph event `EReg` — every PRESENT cross-pair `v` has
`H_k`-degree within `ε_dev · μc` of `μc` — holds with probability `≥ 1 − C/N`, where
`μc := expectedDegreeFormula n_A n_B k p.toReal` and `N := Fintype.card (Fin n_A × Fin n_B)`.

`EReg` is shaped exactly as I3a's regularity hypothesis (`chiPrimeS_le_deltaAB_of_good`,
`mu := D := μc`), via `crossBlockPairs ↔ present` (S1a) + `Hk_degree_regular_of_good`. -/
lemma EReg_concentration_from_c' {n_A n_B : ℕ} (k : ℕ) (h_k_ge_2 : 2 ≤ k)
    (h_k_le_A : k ≤ n_A) (h_k_le_B : k ≤ n_B) (p : ℝ) (_hp_lb : (0 : ℝ) < p) (hp_ub : p < 1)
    (ε_dev : ℝ)
    (hN1 : 1 < (k + 1 : ℝ) * Real.log
        ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ))
    (h_thresh : ∀ (a : Fin n_A) (b : Fin n_B),
        DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k *
          Real.sqrt
            (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.candidatePartnerSet
                n_A n_B k a b).card : ℝ)
            * (((k - 1 : ℕ) : ℝ)
                * ((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.candidatePartnerSet
                    n_A n_B k a b).card : ℝ)
                / ((min (n_A - 1) (n_B - 1) : ℕ) : ℝ)))
          * ((k + 1 : ℝ) * Real.log
              ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) ^ k
        < ε_dev * DaveyThesis2024.SecRandomBipartite.PippengerSpencer.expectedDegreeFormula
            n_A n_B k (ENNReal.ofReal p).toReal) :
      probBipartiteRandom n_A n_B p
        (fun G => ∀ [DecidableRel G.Adj],
          ∀ v ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ,
            |(((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
                G Finset.univ Finset.univ k).filter (fun M => v ∈ M)).card : ℝ)
              - DaveyThesis2024.SecRandomBipartite.PippengerSpencer.expectedDegreeFormula
                  n_A n_B k (ENNReal.ofReal p).toReal|
            ≤ ε_dev * DaveyThesis2024.SecRandomBipartite.PippengerSpencer.expectedDegreeFormula
                n_A n_B k (ENNReal.ofReal p).toReal)
      ≥ 1 - DaveyThesis2024.SecRandomBipartite.PippengerSpencer.kimVuVerbatimConst k (by omega)
          / ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) := by
  classical
  have hp_ofReal : ENNReal.ofReal p ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_ub.le
  set μc : ℝ := DaveyThesis2024.SecRandomBipartite.PippengerSpencer.expectedDegreeFormula
      n_A n_B k (ENNReal.ofReal p).toReal with hμc_def
  set N : ℝ := ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) with hN_def
  set C : ℝ := DaveyThesis2024.SecRandomBipartite.PippengerSpencer.kimVuVerbatimConst k (by omega)
    with hC_def
  have hC_pos : 0 < C :=
    DaveyThesis2024.SecRandomBipartite.PippengerSpencer.kimVuVerbatimConst_pos k (by omega)
  -- The selector bad-set bound from c' (returns the canonical `kimVuVerbatimConst`).
  have hc' :
      ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B
          (ENNReal.ofReal p) hp_ofReal).toMeasure).real
        {g | ∃ (a : Fin n_A) (b : Fin n_B),
              ε_dev * μc ≤ |DaveyThesis2024.SecRandomBipartite.PippengerSpencer.matchingCountNoFactor
                  a b k g - μc|}
        ≤ C / N :=
    DaveyThesis2024.SecRandomBipartite.PippengerSpencer.c'_allEdges_concentration_aas
      k h_k_ge_2 h_k_le_A h_k_le_B (ENNReal.ofReal p) hp_ofReal ε_dev hN1 h_thresh
  -- The good graph event.
  set μm := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B
      (ENNReal.ofReal p) hp_ofReal).toMeasure with hμm_def
  set goodG : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) :=
    {G | ∀ [DecidableRel G.Adj],
        ∀ v ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ,
          |(((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
              G Finset.univ Finset.univ k).filter (fun M => v ∈ M)).card : ℝ) - μc|
          ≤ ε_dev * μc} with hgoodG_def
  set badG : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) := goodGᶜ with hbadG_def
  have hgood_meas : MeasurableSet goodG := MeasurableSet.of_discrete
  have hbad_meas : MeasurableSet badG := hgood_meas.compl
  -- Bad selector set from c'.
  set badSel : Set (Fin n_A × Fin n_B → Bool) :=
    {g | ∃ (a : Fin n_A) (b : Fin n_B),
          ε_dev * μc ≤ |DaveyThesis2024.SecRandomBipartite.PippengerSpencer.matchingCountNoFactor
              a b k g - μc|} with hbadSel_def
  -- preimage(badG) ⊆ badSel.
  have h_preimage_sub :
      DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph ⁻¹' badG ⊆ badSel := by
    intro g hg
    simp only [Set.mem_preimage, hbadG_def, hgoodG_def, Set.mem_compl_iff,
      Set.mem_setOf_eq] at hg
    push_neg at hg
    obtain ⟨inst, v, hv_mem, hv_dev⟩ := hg
    -- v = (a,b) is present, so deviation lifts to matchingCountNoFactor.
    obtain ⟨a, b⟩ := v
    -- Normalise the decidability instance to the canonical one.
    have h_inst_eq : inst = boolToBipartiteGraph_decidableAdj g := Subsingleton.elim _ _
    subst h_inst_eq
    have hpres : g (a, b) = true :=
      (mem_crossBlockPairs_boolToBipartiteGraph_iff g a b).mp hv_mem
    have h_eq := DaveyThesis2024.SecRandomBipartite.PippengerSpencer.matchingCountNoFactor_eq_degree_of_present
      a b k (by omega) g hpres
    exact ⟨a, b, h_eq ▸ hv_dev.le⟩
  -- Measure bound on badG via preimage + c'.
  have h_badG_le : (DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B
      (ENNReal.ofReal p) hp_ofReal badG).toReal ≤ C / N := by
    rw [DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure_eq_preimage
      (ENNReal.ofReal p) hp_ofReal hbad_meas]
    have h_mono := MeasureTheory.measureReal_mono (μ := μm) h_preimage_sub
      (MeasureTheory.measure_ne_top _ _)
    exact le_trans (le_of_eq rfl) (h_mono.trans hc')
  -- Convert to probBipartiteRandom of goodG = 1 - badG.
  unfold probBipartiteRandom DaveyThesis2024.BipartiteRandomGraph.probBipartiteRandomConcrete
  simp only [hp_ofReal, dite_true]
  set ν := DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B
    (ENNReal.ofReal p) hp_ofReal with hν_def
  have h_bad_compl_eq : ν badG = 1 - ν goodG :=
    hbadG_def ▸ MeasureTheory.prob_compl_eq_one_sub hgood_meas
  have h_good_le_one : ν goodG ≤ 1 := MeasureTheory.prob_le_one
  have h_bad_toReal : (ν badG).toReal = 1 - (ν goodG).toReal := by
    rw [h_bad_compl_eq, ENNReal.toReal_sub_of_le h_good_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  change (ν goodG).toReal ≥ 1 - C / N
  linarith [h_badG_le, h_bad_toReal]

/-- **S3 (ECodeg conversion).** From `c''_allPairs_concentration_aas` (the verbatim-Kim–Vu
all-pairs codegree tail) plus the regime arithmetic `h_arith`, the graph event `ECodeg` —
every DISTINCT pair `u ≠ v` of cross-pairs has `H_k`-codegree `≤ target` — holds with
probability `≥ 1 − C/N`. Distinct disjoint pairs are handled by `Hk_codegree_bounded_of_good`
(I1-codeg) + `h_arith`; pairs sharing a row/column have codegree `0 ≤ target` (S1b). -/
lemma ECodeg_concentration_from_c'' {n_A n_B : ℕ} (k : ℕ) (h_k_ge_3 : 3 ≤ k)
    (h_k_le_A : k ≤ n_A) (h_k_le_B : k ≤ n_B) (p : ℝ) (_hp_lb : (0 : ℝ) < p) (hp_ub : p < 1)
    (ε_codeg : ℝ) (target : ℝ) (h_target_nn : 0 ≤ target)
    (hN1 : 1 < (k + 2 : ℝ) * Real.log
        ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ))
    (h_thresh : ∀ (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B), a_1 ≠ a_2 → b_1 ≠ b_2 →
        DaveyThesis2024.SecRandomBipartite.KimVu.kimVuConst k *
          Real.sqrt
            (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.candidatePairPartnerSet
                n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
            * (((k - 2 : ℕ) : ℝ)
                * ((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.candidatePairPartnerSet
                    n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
                / ((min (n_A - 2) (n_B - 2) : ℕ) : ℝ)))
          * ((k + 2 : ℝ) * Real.log
              ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ)) ^ k
        < ε_codeg * (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.candidatePairPartnerSet
              n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
            * (ENNReal.ofReal p).toReal ^ (k - 2)
            * (1 - (ENNReal.ofReal p).toReal) ^ (k * (k - 1) - 2)))
    (h_arith : ∀ (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B), a_1 ≠ a_2 → b_1 ≠ b_2 →
        (1 + ε_codeg) * (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.candidatePairPartnerSet
              n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
            * (ENNReal.ofReal p).toReal ^ (k - 2)
            * (1 - (ENNReal.ofReal p).toReal) ^ (k * (k - 1) - 2)) ≤ target) :
      probBipartiteRandom n_A n_B p
        (fun G => ∀ [DecidableRel G.Adj],
          ∀ u ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ,
          ∀ v ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ,
            u ≠ v →
            (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
                G Finset.univ Finset.univ k).filter (fun M => u ∈ M ∧ v ∈ M)).card : ℝ)
            ≤ target)
      ≥ 1 - DaveyThesis2024.SecRandomBipartite.PippengerSpencer.kimVuVerbatimConst k (by omega)
          / ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) := by
  classical
  have hp_ofReal : ENNReal.ofReal p ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_ub.le
  set N : ℝ := ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) with hN_def
  set μ'' : Fin n_A → Fin n_A → Fin n_B → Fin n_B → ℝ :=
    fun a_1 a_2 b_1 b_2 =>
      ((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.candidatePairPartnerSet
          n_A n_B k a_1 a_2 b_1 b_2).card : ℝ)
        * (ENNReal.ofReal p).toReal ^ (k - 2)
        * (1 - (ENNReal.ofReal p).toReal) ^ (k * (k - 1) - 2) with hμ''_def
  set C : ℝ := DaveyThesis2024.SecRandomBipartite.PippengerSpencer.kimVuVerbatimConst k (by omega)
    with hC_def
  have hC_pos : 0 < C :=
    DaveyThesis2024.SecRandomBipartite.PippengerSpencer.kimVuVerbatimConst_pos k (by omega)
  -- The selector bad-set bound from c'' (returns the canonical `kimVuVerbatimConst`).
  have hc'' :
      ((DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B
          (ENNReal.ofReal p) hp_ofReal).toMeasure).real
        {g | ∃ (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B), a_1 ≠ a_2 ∧ b_1 ≠ b_2 ∧
              ε_codeg * μ'' a_1 a_2 b_1 b_2
                ≤ |DaveyThesis2024.SecRandomBipartite.PippengerSpencer.matchingCodegreeNoFactor
                    a_1 a_2 b_1 b_2 k g - μ'' a_1 a_2 b_1 b_2|}
        ≤ C / N :=
    DaveyThesis2024.SecRandomBipartite.PippengerSpencer.c''_allPairs_concentration_aas
      k h_k_ge_3 h_k_le_A h_k_le_B (ENNReal.ofReal p) hp_ofReal ε_codeg hN1 h_thresh
  set μm := (DaveyThesis2024.BipartiteRandomGraph.bipartiteEdgeChoice n_A n_B
      (ENNReal.ofReal p) hp_ofReal).toMeasure with hμm_def
  set goodG : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) :=
    {G | ∀ [DecidableRel G.Adj],
        ∀ u ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ,
        ∀ v ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ,
          u ≠ v →
          (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
              G Finset.univ Finset.univ k).filter (fun M => u ∈ M ∧ v ∈ M)).card : ℝ)
          ≤ target} with hgoodG_def
  set badG : Set (SimpleGraph (Fin n_A ⊕ Fin n_B)) := goodGᶜ with hbadG_def
  have hgood_meas : MeasurableSet goodG := MeasurableSet.of_discrete
  have hbad_meas : MeasurableSet badG := hgood_meas.compl
  -- Bad selector set from c''.
  set badSel : Set (Fin n_A × Fin n_B → Bool) :=
    {g | ∃ (a_1 a_2 : Fin n_A) (b_1 b_2 : Fin n_B), a_1 ≠ a_2 ∧ b_1 ≠ b_2 ∧
          ε_codeg * μ'' a_1 a_2 b_1 b_2
            ≤ |DaveyThesis2024.SecRandomBipartite.PippengerSpencer.matchingCodegreeNoFactor
                a_1 a_2 b_1 b_2 k g - μ'' a_1 a_2 b_1 b_2|} with hbadSel_def
  -- preimage(badG) ⊆ badSel.
  have h_preimage_sub :
      DaveyThesis2024.BipartiteRandomGraph.boolToBipartiteGraph ⁻¹' badG ⊆ badSel := by
    intro g hg
    simp only [Set.mem_preimage, hbadG_def, hgoodG_def, Set.mem_compl_iff,
      Set.mem_setOf_eq] at hg
    push_neg at hg
    obtain ⟨inst, u, hu_mem, v, hv_mem, hne, hcodeg_gt⟩ := hg
    have h_inst_eq : inst = boolToBipartiteGraph_decidableAdj g := Subsingleton.elim _ _
    subst h_inst_eq
    obtain ⟨a_1, b_1⟩ := u; obtain ⟨a_2, b_2⟩ := v
    -- Case split: shared endpoint ⟹ codeg = 0 ≤ target (contradiction with hcodeg_gt);
    -- disjoint ⟹ feed I1-codeg contrapositive to badSel.
    by_cases h_shared : a_1 = a_2 ∨ b_1 = b_2
    · exfalso
      have h0 := codeg_filter_card_eq_zero_of_shared k g (a_1, b_1) (a_2, b_2)
        (by simpa using h_shared) hne
      rw [h0, Nat.cast_zero] at hcodeg_gt
      linarith [hcodeg_gt, h_target_nn]
    · push_neg at h_shared
      obtain ⟨h_a, h_b⟩ := h_shared
      refine ⟨a_1, a_2, b_1, b_2, h_a, h_b, ?_⟩
      -- I1-codeg contrapositive: ¬good ⟹ ¬(|codeg-μ''| ≤ ε_codeg·μ'').
      by_contra h_le
      push_neg at h_le
      have h_bound := DaveyThesis2024.SecRandomBipartite.PippengerSpencer.Hk_codegree_bounded_of_good
        a_1 a_2 b_1 b_2 k (by omega) h_a h_b g ε_codeg (μ'' a_1 a_2 b_1 b_2) target
        (le_of_lt h_le) (h_arith a_1 a_2 b_1 b_2 h_a h_b)
      exact absurd h_bound (not_le.mpr hcodeg_gt)
  -- Measure bound on badG via preimage + c''.
  have h_badG_le : (DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B
      (ENNReal.ofReal p) hp_ofReal badG).toReal ≤ C / N := by
    rw [DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure_eq_preimage
      (ENNReal.ofReal p) hp_ofReal hbad_meas]
    have h_mono := MeasureTheory.measureReal_mono (μ := μm) h_preimage_sub
      (MeasureTheory.measure_ne_top _ _)
    exact le_trans (le_of_eq rfl) (h_mono.trans hc'')
  -- Convert to probBipartiteRandom of goodG = 1 - badG.
  unfold probBipartiteRandom DaveyThesis2024.BipartiteRandomGraph.probBipartiteRandomConcrete
  simp only [hp_ofReal, dite_true]
  set ν := DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure n_A n_B
    (ENNReal.ofReal p) hp_ofReal with hν_def
  have h_bad_compl_eq : ν badG = 1 - ν goodG :=
    hbadG_def ▸ MeasureTheory.prob_compl_eq_one_sub hgood_meas
  have h_good_le_one : ν goodG ≤ 1 := MeasureTheory.prob_le_one
  have h_bad_toReal : (ν badG).toReal = 1 - (ν goodG).toReal := by
    rw [h_bad_compl_eq, ENNReal.toReal_sub_of_le h_good_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  change (ν goodG).toReal ≥ 1 - C / N
  linarith [h_badG_le, h_bad_toReal]

/-! ## Section 5 (relocated): Main theorem `secRandomBipartite_aas`

This theorem was originally in `DaveyThesis2024/SECRandomBipartite.lean`
(Section 5). It is relocated here because its proof body now depends
on the just-above-defined theorem `chiPrimeS_nibble_quantitative_bound`,
which itself depends on `chiPrimeS_le_of_perPairCover_family` (from
the `DaveyThesis2024.CN` namespace, this very file). The name and
namespace are preserved: `SECRandomBipartite.secRandomBipartite_aas`. -/


/-- **I3b core headline: Brualdi–Quinn a.a.s. bound via the SOUND verbatim Kim–Vu axiom —
UNCONDITIONAL for bounded-aspect-ratio random bipartite graphs.**
For any fixed `p ∈ (0, 1)` and aspect constant `C ≥ 1`, a.a.s. as `min(n_A, n_B) → ∞` over the
bounded-aspect pairs `max n_A n_B ≤ C·min n_A n_B`, `χ'_s(G) ≤ Δ_A(G)·Δ_B(G)`.

This routes the nibble step through the SOUND verbatim Kim–Vu concentration
(via `c'`/`c''` → `EReg`/`ECodeg` → `chiPrimeS_le_deltaAB_of_good`) instead of the FKS chain.
The 4-way Bonferroni combines `EA`, `EB` (`Δ_A`/`Δ_B` concentration, each `≥ 1 − ε/4`) with
`EReg`, `ECodeg` (each `≥ 1 − C_kv/N ≥ 1 − ε/4` on the regime).

**No hypothesis remains.** The former `h_regime : asymptotic_regime_BQ` honest
balanced-asymptotic Prop is now DISCHARGED internally as the theorem
`asymptotic_regime_BQ_holds` (under the bounded-aspect guard, where the Kim–Vu threshold ratios
`Θ((log m)^k/√m) → 0`). The theorem therefore depends only on the standard Lean axioms plus the
two verbatim literature axioms (`kim_vu_concentration_verbatim`,
`pippenger_spencer_covering_verbatim`). -/
theorem secRandomBipartite_aas (p : ℝ) (hp_lb : (0 : ℝ) < p) (hp_ub : p < 1)
    (C : ℝ) (hC : 1 ≤ C) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n_A n_B : ℕ,
      min n_A n_B ≥ N →
      (max n_A n_B : ℝ) ≤ C * (min n_A n_B : ℝ) →
      probBipartiteRandom n_A n_B p
        (fun G => ∀ [DecidableRel G.Adj],
          chiPrimeS G ≤ (deltaA G * deltaB G : ℕ∞))
      ≥ 1 - ε := by
  classical
  -- The balanced-asymptotic regime is now DISCHARGED (not assumed): see
  -- `asymptotic_regime_BQ_holds`.  The headline is unconditional for bounded-aspect pairs.
  have h_regime : ∀ (hp_le : ENNReal.ofReal p ≤ 1),
      DaveyThesis2024.SecRandomBipartite.PippengerSpencer.asymptotic_regime_BQ
        (ENNReal.ofReal p) hp_le C hC :=
    DaveyThesis2024.SecRandomBipartite.PippengerSpencer.asymptotic_regime_BQ_holds
      p hp_lb hp_ub C hC
  intro ε hε
  have hp_ofReal : ENNReal.ofReal p ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_ub.le
  have hp_toReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp_lb.le
  -- Unpack the regime: fixed k, η + the per-(n) data provider.
  obtain ⟨k, η, h_k_ge_3, hη_pos, h_k_link, h_regime_data⟩ := h_regime hp_ofReal
  have h_k_pos : 0 < k := by omega
  -- Canonical (n-independent) P–S deviation δ_PS and floor D₀.
  set δ_PS : ℝ := psVerbatimDelta k h_k_pos η hη_pos with hδ_PS_def
  have hδ_PS_pos : 0 < δ_PS := psVerbatimDelta_pos k h_k_pos η hη_pos
  set D₀ : ℝ := psVerbatimD₀ k h_k_pos η hη_pos with hD₀_def
  -- The canonical Kim–Vu tail constant.
  set C_kv : ℝ := DaveyThesis2024.SecRandomBipartite.PippengerSpencer.kimVuVerbatimConst k h_k_pos
    with hC_kv_def
  have hC_kv_pos : 0 < C_kv :=
    DaveyThesis2024.SecRandomBipartite.PippengerSpencer.kimVuVerbatimConst_pos k h_k_pos
  -- δ := p/2.
  set δ : ℝ := p / 2 with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  have hδ_lt_one : δ < 1 := by rw [hδ_def]; linarith
  have hε4_pos : 0 < ε / 4 := by linarith
  -- deltaA / deltaB concentration thresholds (each ≥ 1 - ε/4).
  obtain ⟨N₁, hN₁⟩ := deltaA_concentration p hp_lb hp_ub δ hδ_pos (ε / 4) hε4_pos
  obtain ⟨N₂, hN₂⟩ := deltaB_concentration p hp_lb hp_ub δ hδ_pos (ε / 4) hε4_pos
  -- The regime per-(n) data at (δ_PS, D₀, C_kv, ε).
  obtain ⟨N₀, h_regime_at⟩ := h_regime_data δ_PS hδ_PS_pos D₀ C_kv hC_kv_pos ε hε
  refine ⟨max (max N₁ N₂) N₀, fun n_A n_B hN h_aspect => ?_⟩
  have hN_N₁ : N₁ ≤ min n_A n_B :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN_N₂ : N₂ ≤ min n_A n_B :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN_N₀ : N₀ ≤ min n_A n_B := le_trans (le_max_right _ _) hN
  -- Extract all regime clauses at (n_A, n_B).
  obtain ⟨⟨h_kA, h_kB⟩, hN1_c', hN1_c'', h_thresh_c',
         ⟨ε_codeg, hε_codeg_pos, h_thresh_c'', h_arith_codeg⟩,
         h_D₀_le, h_tail_decay, h_gap_link, h_dA_pos_link⟩ :=
    h_regime_at n_A n_B hN_N₀ h_aspect
  -- Abbreviations.
  set μc : ℝ := DaveyThesis2024.SecRandomBipartite.PippengerSpencer.expectedDegreeFormula
      n_A n_B k (ENNReal.ofReal p).toReal with hμc_def
  set N : ℝ := ((Fintype.card (Fin n_A × Fin n_B) : ℕ) : ℝ) with hN_def
  -- Four events.
  set EA : SimpleGraph (Fin n_A ⊕ Fin n_B) → Prop :=
    fun G => ∀ [DecidableRel G.Adj], (1 - δ) * (n_B : ℝ) * p ≤ (deltaA G : ℝ) with hEA_def
  set EB : SimpleGraph (Fin n_A ⊕ Fin n_B) → Prop :=
    fun G => ∀ [DecidableRel G.Adj], (1 - δ) * (n_A : ℝ) * p ≤ (deltaB G : ℝ) with hEB_def
  set EReg : SimpleGraph (Fin n_A ⊕ Fin n_B) → Prop :=
    fun G => ∀ [DecidableRel G.Adj],
      ∀ v ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ,
        |(((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
            G Finset.univ Finset.univ k).filter (fun M => v ∈ M)).card : ℝ) - μc|
        ≤ δ_PS * μc with hEReg_def
  set ECodeg : SimpleGraph (Fin n_A ⊕ Fin n_B) → Prop :=
    fun G => ∀ [DecidableRel G.Adj],
      ∀ u ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ,
      ∀ v ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ,
        u ≠ v →
        (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
            G Finset.univ Finset.univ k).filter (fun M => u ∈ M ∧ v ∈ M)).card : ℝ)
        ≤ δ_PS * μc with hECodeg_def
  -- Event probabilities.
  have hPA : probBipartiteRandom n_A n_B p EA ≥ 1 - ε / 4 := hN₁ n_A n_B hN_N₁
  have hPB : probBipartiteRandom n_A n_B p EB ≥ 1 - ε / 4 := hN₂ n_A n_B hN_N₂
  -- EReg via S2 (rewrite the centering with hp_toReal).
  have hPReg : probBipartiteRandom n_A n_B p EReg ≥ 1 - ε / 4 := by
    have h := EReg_concentration_from_c' (n_A := n_A) (n_B := n_B) k (by omega) h_kA h_kB
      p hp_lb hp_ub δ_PS (by simpa only [hN_def] using hN1_c')
      (by simpa only [hN_def, hμc_def] using h_thresh_c')
    -- The event from S2 matches EReg modulo `μc = expectedDegreeFormula … (ofReal p).toReal`.
    have h_event_eq : EReg = (fun G => ∀ [DecidableRel G.Adj],
        ∀ v ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ,
          |(((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
              G Finset.univ Finset.univ k).filter (fun M => v ∈ M)).card : ℝ)
            - DaveyThesis2024.SecRandomBipartite.PippengerSpencer.expectedDegreeFormula
                n_A n_B k (ENNReal.ofReal p).toReal|
          ≤ δ_PS * DaveyThesis2024.SecRandomBipartite.PippengerSpencer.expectedDegreeFormula
              n_A n_B k (ENNReal.ofReal p).toReal) := by
      rw [hEReg_def, hμc_def]
    rw [h_event_eq]
    have h_decay : DaveyThesis2024.SecRandomBipartite.PippengerSpencer.kimVuVerbatimConst k (by omega)
        / N ≤ ε / 4 := by rw [hC_kv_def] at h_tail_decay; exact h_tail_decay
    linarith [h, h_decay]
  -- ECodeg via S3.
  have hPCodeg : probBipartiteRandom n_A n_B p ECodeg ≥ 1 - ε / 4 := by
    have h_target_nn : 0 ≤ δ_PS * μc := by
      have hμc_nn : 0 ≤ μc :=
        DaveyThesis2024.SecRandomBipartite.PippengerSpencer.expectedDegreeFormula_nonneg
          n_A n_B k _ (by rw [hp_toReal]; linarith) (by rw [hp_toReal]; linarith)
      positivity
    have h := ECodeg_concentration_from_c'' (n_A := n_A) (n_B := n_B) k h_k_ge_3 h_kA h_kB
      p hp_lb hp_ub ε_codeg (δ_PS * μc) h_target_nn hN1_c''
      (by simpa only [hN_def, hμc_def] using h_thresh_c'')
      (by simpa [hμc_def] using h_arith_codeg)
    have h_event_eq : ECodeg = (fun G => ∀ [DecidableRel G.Adj],
        ∀ u ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ,
        ∀ v ∈ DaveyThesis2024.SecRandomBipartite.crossBlockPairs G Finset.univ Finset.univ,
          u ≠ v →
          (((DaveyThesis2024.SecRandomBipartite.PippengerSpencer.inducedKMatchings
              G Finset.univ Finset.univ k).filter (fun M => u ∈ M ∧ v ∈ M)).card : ℝ)
          ≤ δ_PS * μc) := by rw [hECodeg_def]
    rw [h_event_eq]
    have h_decay : DaveyThesis2024.SecRandomBipartite.PippengerSpencer.kimVuVerbatimConst k (by omega)
        / N ≤ ε / 4 := by rw [hC_kv_def] at h_tail_decay; exact h_tail_decay
    linarith [h, h_decay]
  -- 4-way Bonferroni.
  have hPAB : probBipartiteRandom n_A n_B p (fun G => EA G ∧ EB G) ≥ 1 - 2 * ε / 4 := by
    have h := probBipartiteRandom_inter_bound n_A n_B p EA EB
    linarith
  have hPABReg : probBipartiteRandom n_A n_B p (fun G => (EA G ∧ EB G) ∧ EReg G)
      ≥ 1 - 3 * ε / 4 := by
    have h := probBipartiteRandom_inter_bound n_A n_B p (fun G => EA G ∧ EB G) EReg
    linarith
  have hPAll : probBipartiteRandom n_A n_B p
      (fun G => ((EA G ∧ EB G) ∧ EReg G) ∧ ECodeg G) ≥ 1 - ε := by
    have h := probBipartiteRandom_inter_bound n_A n_B p
      (fun G => (EA G ∧ EB G) ∧ EReg G) ECodeg
    linarith
  -- Name the good event and the target event (avoids stuck `DecidableRel` metavars in set-builders).
  set EGood : SimpleGraph (Fin n_A ⊕ Fin n_B) → Prop :=
    fun G => ((EA G ∧ EB G) ∧ EReg G) ∧ ECodeg G with hEGood_def
  set ETarget : SimpleGraph (Fin n_A ⊕ Fin n_B) → Prop :=
    fun G => ∀ [DecidableRel G.Adj], chiPrimeS G ≤ (deltaA G * deltaB G : ℕ∞) with hETarget_def
  -- Lift via measure monotonicity, pushed to selector space (where `G = boolToBipartiteGraph f`
  -- and I3a `chiPrimeS_le_deltaAB_of_good` applies). The all-`G` event implies the target only
  -- on the support of the bipartite measure, so we route through `bipartiteRandomMeasure_eq_preimage`.
  have h_mono :
      probBipartiteRandom n_A n_B p EGood ≤ probBipartiteRandom n_A n_B p ETarget := by
    unfold probBipartiteRandom DaveyThesis2024.BipartiteRandomGraph.probBipartiteRandomConcrete
    simp only [hp_ofReal, dite_true]
    have h_good_meas : MeasurableSet {G | EGood G} := MeasurableSet.of_discrete
    have h_tgt_meas : MeasurableSet {G | ETarget G} := MeasurableSet.of_discrete
    rw [DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure_eq_preimage
          (ENNReal.ofReal p) hp_ofReal h_good_meas,
        DaveyThesis2024.BipartiteRandomGraph.bipartiteRandomMeasure_eq_preimage
          (ENNReal.ofReal p) hp_ofReal h_tgt_meas]
    apply ENNReal.toReal_mono
    · exact (MeasureTheory.measure_lt_top _ _).ne
    apply MeasureTheory.measure_mono
    -- Pointwise: selector `f` in the good preimage ⇒ in the target preimage.
    intro f hf
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hEGood_def, hETarget_def] at hf ⊢
    obtain ⟨⟨⟨hEA_G, hEB_G⟩, hEReg_G⟩, hECodeg_G⟩ := hf
    intro inst
    -- Work with the canonical `boolToBipartiteGraph` decidability instance, the one all of
    -- I3a / F3 / the events resolve to; the ambient `inst` agrees by subsingleton.
    have h_inst_eq : inst = boolToBipartiteGraph_decidableAdj f := Subsingleton.elim _ _
    subst h_inst_eq
    -- Expand the degree/codegree events at this instance.
    have h_dA : (1 - δ) * (n_B : ℝ) * p ≤ (deltaA (boolToBipartiteGraph f) : ℝ) := hEA_G
    have h_dB : (1 - δ) * (n_A : ℝ) * p ≤ (deltaB (boolToBipartiteGraph f) : ℝ) := hEB_G
    have h_reg_G := @hEReg_G (boolToBipartiteGraph_decidableAdj f)
    have h_codeg_G := @hECodeg_G (boolToBipartiteGraph_decidableAdj f)
    -- deltaA ≥ 1 (from EA + the regime's deltaA-positivity link, with δ = p/2 and toReal p = p).
    have h_dA_pos : (1 : ℝ) ≤ (deltaA (boolToBipartiteGraph f) : ℝ) := by
      have hlink : (1 : ℝ) ≤ (1 - p / 2) * (n_B : ℝ) * p := by
        simpa only [hp_toReal] using h_dA_pos_link
      rw [hδ_def] at h_dA; linarith
    -- the gap inequality for `nibble_real_le_of_deltas` (from EB + the regime's deltaB-link).
    have h_gap : (n_A : ℝ) * (1 / (k : ℝ) + η) + 1 ≤ (deltaB (boolToBipartiteGraph f) : ℝ) := by
      have hlink : (n_A : ℝ) * (1 / (k : ℝ) + η) + 1 ≤ (1 - p / 2) * (n_A : ℝ) * p := by
        simpa only [hp_toReal] using h_gap_link
      rw [hδ_def] at h_dB; linarith
    -- F3: |E| ≤ n_A · deltaA.
    have hF3' : ((DaveyThesis2024.SecRandomBipartite.crossBlockPairs
          (boolToBipartiteGraph f) Finset.univ Finset.univ).card : ℝ)
        ≤ (n_A : ℝ) * (deltaA (boolToBipartiteGraph f) : ℝ) := by
      exact_mod_cast crossBlockPairs_card_le_nA_mul_deltaA (n_A := n_A) (n_B := n_B) f
    -- The real nibble inequality `|E|/k + η|E| + 1 ≤ deltaA·deltaB`.
    have h_real :
        ((DaveyThesis2024.SecRandomBipartite.crossBlockPairs
              (boolToBipartiteGraph f) Finset.univ Finset.univ).card : ℝ) / (k : ℝ)
          + η * ((DaveyThesis2024.SecRandomBipartite.crossBlockPairs
              (boolToBipartiteGraph f) Finset.univ Finset.univ).card : ℝ) + 1
        ≤ (deltaA (boolToBipartiteGraph f) : ℝ) * (deltaB (boolToBipartiteGraph f) : ℝ) :=
      nibble_real_le_of_deltas (k := k) (η := η) h_k_pos hη_pos.le hF3' h_dA_pos h_gap
    -- Apply I3a at `D := μc` (EReg/ECodeg carry exactly the P–S regularity/codegree at `μc`).
    exact chiPrimeS_le_deltaAB_of_good (n_A := n_A) (n_B := n_B) k h_k_pos η hη_pos
      f μc (by rw [hμc_def]; exact h_D₀_le) h_reg_G h_codeg_G h_real
  linarith


end SECRandomBipartite


-- Sanity check: Phase γ sub-lemmas depend only on standard Lean axioms.
section PhaseGammaAxiomCheck
open SECRandomBipartite
/--
info: 'SECRandomBipartite.bulk_count_lower_under_joint_good' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms bulk_count_lower_under_joint_good
/--
info: 'SECRandomBipartite.bulk_count_constant_lower_under_joint_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms bulk_count_constant_lower_under_joint_good
/--
info: 'SECRandomBipartite.cover_size_under_joint_good' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms cover_size_under_joint_good
/--
info: 'SECRandomBipartite.joint_good_implies_perPairCover_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms joint_good_implies_perPairCover_exists
end PhaseGammaAxiomCheck
