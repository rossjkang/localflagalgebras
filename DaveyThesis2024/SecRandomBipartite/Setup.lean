/-
Copyright (c) 2026 Ross Kang.
Released under Apache 2.0 license.

# Setup for the bipartite SCI random-graph proof chain

Foundations for the bipartite strong chromatic index a.a.s. theorem,
following FKS 2005 §3 with bipartite adaptations. The probabilistic
core is in `PippengerSpencer.lean` (Pippenger-Spencer + Kim-Vu).

## Status
Phase C-CN.1 cycle 1 (2026-06-02):
- `IsInducedMatching` definition.
- Connection to independent sets in `lineGraphSq`.
-/

import DaveyThesis2024.SECRandomBipartite

namespace DaveyThesis2024.SecRandomBipartite

open SimpleGraph SECRandomBipartite

variable {V : Type*}

/-! ## Induced matchings -/

/-- A set `M` of edges of `G` is an **induced matching** iff edges in `M` are
pairwise non-`L²`-adjacent (i.e., vertex-disjoint AND no bridge edge
between them). Equivalently, `M` is an independent set in `lineGraphSq G`. -/
def IsInducedMatching (G : SimpleGraph V) (M : Set G.edgeSet) : Prop :=
  ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ¬ LineGraphSqAdj G e₁ e₂

/-- An induced matching is the same as an independent set in `lineGraphSq G`. -/
lemma isInducedMatching_iff_isIndepSet (G : SimpleGraph V) (M : Set G.edgeSet) :
    IsInducedMatching G M ↔ (lineGraphSq G).IsIndepSet M := by
  -- IsIndepSet := s.Pairwise (fun v w => ¬ Adj v w)
  constructor
  · intro h e₁ he₁ e₂ he₂ hne hadj
    exact h e₁ he₁ e₂ he₂ hne ((lineGraphSq_adj G e₁ e₂).mp hadj)
  · intro h e₁ he₁ e₂ he₂ hne hadj
    exact h he₁ he₂ hne ((lineGraphSq_adj G e₁ e₂).mpr hadj)

/-- The empty set is an induced matching. -/
lemma isInducedMatching_empty (G : SimpleGraph V) :
    IsInducedMatching G ∅ := by
  intro e₁ he₁; exact False.elim he₁

/-- A singleton is always an induced matching. -/
lemma isInducedMatching_singleton (G : SimpleGraph V) (e : G.edgeSet) :
    IsInducedMatching G {e} := by
  intro e₁ he₁ e₂ he₂ hne
  rw [Set.mem_singleton_iff] at he₁ he₂
  subst he₁; subst he₂
  exact absurd rfl hne

/-! ## Block partition (FKS 2005 §3 setup, bipartite adaptation)

Partition `Fin n` into `s` blocks, each of size approximately `n/s`. We
use the assignment `i ↦ i % s`, which yields blocks of size `⌈n/s⌉` or
`⌊n/s⌋` (differing by at most 1).

For the bipartite CN nibble: partition `Fin n_A` into `s_A` blocks and
`Fin n_B` into `s_B` blocks; then for each pair `(A_i, B_j)`, run the
per-pair edge-packing routine. -/

variable (n s : ℕ)

/-- Block assignment: vertex `i ∈ Fin n` goes to block `i % s`. Requires
`0 < s` (positivity of modulus). -/
def blockOf (hs : 0 < s) (i : Fin n) : Fin s :=
  ⟨(i : ℕ) % s, Nat.mod_lt _ hs⟩

/-- The `j`-th block: vertices `i ∈ Fin n` with `blockOf n s hs i = j`. -/
def block (hs : 0 < s) (j : Fin s) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => blockOf n s hs i = j)

@[simp] lemma mem_block (hs : 0 < s) (j : Fin s) (i : Fin n) :
    i ∈ block n s hs j ↔ blockOf n s hs i = j := by
  unfold block; simp

/-- The blocks are pairwise disjoint. -/
lemma block_disjoint (hs : 0 < s) (j₁ j₂ : Fin s) (hne : j₁ ≠ j₂) :
    Disjoint (block n s hs j₁) (block n s hs j₂) := by
  rw [Finset.disjoint_left]
  intro i hi₁ hi₂
  rw [mem_block] at hi₁ hi₂
  exact hne (hi₁.symm.trans hi₂)

/-- The blocks cover `Fin n`. -/
lemma block_cover (hs : 0 < s) (i : Fin n) :
    i ∈ block n s hs (blockOf n s hs i) := by
  rw [mem_block]

/-- The union of all blocks is `Finset.univ`. -/
lemma block_iUnion (hs : 0 < s) :
    (Finset.univ : Finset (Fin s)).biUnion (block n s hs) = Finset.univ := by
  ext i
  refine ⟨fun _ => Finset.mem_univ _, fun _ => ?_⟩
  exact Finset.mem_biUnion.mpr ⟨blockOf n s hs i, Finset.mem_univ _, block_cover n s hs i⟩

/-- Each block has at most `n / s + 1` elements (upper bound via `i ↦ i / s`
into `Fin (n / s + 1)`). The exact size is `⌈(n - j) / s⌉` when `j < n` and
`0` otherwise, but this loose bound is what the FKS arithmetic uses. -/
lemma block_card_le_div_succ (hs : 0 < s) (j : Fin s) :
    (block n s hs j).card ≤ n / s + 1 := by
  have key : (block n s hs j).card ≤ (Finset.range (n / s + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun i => (i : ℕ) / s) ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, mem_block] at hi
      simp only [Finset.coe_range, Set.mem_Iio]
      have hi_lt : (i : ℕ) < n := i.isLt
      have : (i : ℕ) / s ≤ n / s := Nat.div_le_div_right (Nat.le_of_lt hi_lt)
      omega
    · intro i₁ hi₁ i₂ hi₂ h_eq
      simp only [Finset.mem_coe, mem_block] at hi₁ hi₂
      have hj₁ : (i₁ : ℕ) % s = (j : ℕ) := by
        have := congr_arg Fin.val hi₁
        simpa [blockOf] using this
      have hj₂ : (i₂ : ℕ) % s = (j : ℕ) := by
        have := congr_arg Fin.val hi₂
        simpa [blockOf] using this
      have heq : (i₁ : ℕ) / s = (i₂ : ℕ) / s := h_eq
      have e₁ : s * ((i₁ : ℕ) / s) + (i₁ : ℕ) % s = (i₁ : ℕ) := Nat.div_add_mod _ _
      have e₂ : s * ((i₂ : ℕ) / s) + (i₂ : ℕ) % s = (i₂ : ℕ) := Nat.div_add_mod _ _
      apply Fin.ext
      calc (i₁ : ℕ)
          = s * ((i₁ : ℕ) / s) + (i₁ : ℕ) % s := e₁.symm
        _ = s * ((i₂ : ℕ) / s) + (j : ℕ) := by rw [heq, hj₁]
        _ = s * ((i₂ : ℕ) / s) + (i₂ : ℕ) % s := by rw [← hj₂]
        _ = (i₂ : ℕ) := e₂
  simpa [Finset.card_range] using key

/-- The block sizes sum to `n` (since the blocks partition `Fin n`). -/
lemma sum_block_card (hs : 0 < s) :
    ∑ j : Fin s, (block n s hs j).card = n := by
  have hbi := Finset.card_biUnion (s := (Finset.univ : Finset (Fin s)))
    (t := block n s hs) (fun j₁ _ j₂ _ hne => block_disjoint n s hs j₁ j₂ hne)
  rw [block_iUnion] at hbi
  simpa [Finset.card_univ, Fintype.card_fin] using hbi.symm

/-! ## k-Subset family with controlled pairwise intersection (Issue 1)

Following FKS 2005 Lemma 7 part 2: given a vertex set `W : Finset α` of
size `|W| = n₀` and integers `k, target_size`, construct a family
`I_i ⊂ powersetCard k W` of `target_size` k-subsets with:

* each `I_l ∈ I_i` has `|I_l| = k`,
* pairwise intersection `|I_{l₁} ∩ I_{l₂}| ≤ 1`,
* each `v ∈ W` belongs to ~`target_size · k / n₀` sets.

The FKS construction is **probabilistic**: sample each k-subset
independently with probability `target_size / Nat.choose n₀ k`, then
delete overlap-violating pairs via Chernoff. We package this as a
spec for now; the constructive existence proof is deferred to a
future C-CN cycle (substantial work, ~1-2 weeks per the audit). -/

/-- A "valid k-subset family" of `W` with target size `target_size`. -/
structure ValidKSubsetFamily (α : Type*) [DecidableEq α]
    (W : Finset α) (k target_size : ℕ) where
  /-- The family itself. -/
  family : Finset (Finset α)
  /-- Each set is a k-subset of W. -/
  subsets_of_W : ∀ I ∈ family, I ⊆ W ∧ I.card = k
  /-- Family size matches the target (up to a 1+o(1) factor; here we
  encode the lower bound; an `≤` upper bound would be a separate field). -/
  family_card_ge : (3 * target_size / 4 : ℕ) ≤ family.card
  /-- Pairwise intersection at most 1. -/
  pairwise_overlap : ∀ I₁ ∈ family, ∀ I₂ ∈ family,
    I₁ ≠ I₂ → (I₁ ∩ I₂).card ≤ 1

/-- **Combinatorial helper**: the number of `k`-subsets of `W` containing
a fixed subset `p ⊆ W` with `|p| ≤ k` equals `C(|W| - |p|, k - |p|)`.
Bijection `I ↦ I \ p` to `(W \ p).powersetCard (k - |p|)`. -/
lemma card_powersetCard_filter_subset {α : Type*} [DecidableEq α]
    (W : Finset α) (k : ℕ) (p : Finset α)
    (hp_subset : p ⊆ W) (hpk : p.card ≤ k) :
    ((W.powersetCard k).filter (fun I => p ⊆ I)).card
      = Nat.choose (W.card - p.card) (k - p.card) := by
  have h_target_card :
      ((W \ p).powersetCard (k - p.card)).card
        = Nat.choose (W.card - p.card) (k - p.card) := by
    rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hp_subset]
  rw [← h_target_card]
  refine Finset.card_bij (fun I _ => I \ p) ?_ ?_ ?_
  · intro I hI
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hI
    obtain ⟨⟨hI_sub_W, hI_card⟩, hp_sub_I⟩ := hI
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Finset.mem_sdiff] at hx ⊢
      exact ⟨hI_sub_W hx.1, hx.2⟩
    · rw [Finset.card_sdiff_of_subset hp_sub_I, hI_card]
  · intro I₁ h₁ I₂ h₂ h_eq
    rw [Finset.mem_filter] at h₁ h₂
    have hp1 : p ⊆ I₁ := h₁.2
    have hp2 : p ⊆ I₂ := h₂.2
    have hI1 : I₁ = (I₁ \ p) ∪ p := (Finset.sdiff_union_of_subset hp1).symm
    have hI2 : I₂ = (I₂ \ p) ∪ p := (Finset.sdiff_union_of_subset hp2).symm
    have h_eq' : I₁ \ p = I₂ \ p := h_eq
    rw [hI1, hI2, h_eq']
  · intro J hJ
    rw [Finset.mem_powersetCard] at hJ
    obtain ⟨hJ_sub, hJ_card⟩ := hJ
    have h_disj : Disjoint J p :=
      disjoint_sdiff_self_left.mono_left hJ_sub
    refine ⟨J ∪ p, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨?_, ?_⟩, Finset.subset_union_right⟩
      · rw [Finset.union_subset_iff]
        exact ⟨hJ_sub.trans Finset.sdiff_subset, hp_subset⟩
      · rw [Finset.card_union_of_disjoint h_disj, hJ_card]
        omega
    · -- (J ∪ p) \ p = J
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hor, hnp⟩
        rcases hor with hJ_x | hp_x
        · exact hJ_x
        · exact absurd hp_x hnp
      · intro hJ_x
        refine ⟨Or.inl hJ_x, ?_⟩
        intro hp_x
        exact Finset.disjoint_left.mp h_disj hJ_x hp_x

/-- **Double-counting identity**: `C(n, k) · C(k, m) = C(n, m) · C(n-m, k-m)`
for `m ≤ k ≤ n`. Not in Mathlib directly (as of v4.28); proved here from
`Nat.choose_mul_factorial_mul_factorial`. -/
lemma choose_mul_choose_eq_choose_mul_choose {n k m : ℕ} (hmk : m ≤ k) (hkn : k ≤ n) :
    n.choose k * k.choose m = n.choose m * (n - m).choose (k - m) := by
  have hmn : m ≤ n := hmk.trans hkn
  have h1 : n.choose k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n :=
    Nat.choose_mul_factorial_mul_factorial hkn
  have h2 : k.choose m * Nat.factorial m * Nat.factorial (k - m) = Nat.factorial k :=
    Nat.choose_mul_factorial_mul_factorial hmk
  have h3 : n.choose m * Nat.factorial m * Nat.factorial (n - m) = Nat.factorial n :=
    Nat.choose_mul_factorial_mul_factorial hmn
  have hk_sub_m_le : k - m ≤ n - m := by omega
  have h4_raw := Nat.choose_mul_factorial_mul_factorial hk_sub_m_le
  have hk_sub : (n - m) - (k - m) = n - k := by omega
  rw [hk_sub] at h4_raw
  -- h4_raw : (n - m).choose (k - m) * (k - m)! * (n - k)! = (n - m)!  (with Nat.factorial)
  have hpos : 0 < Nat.factorial m * Nat.factorial (k - m) * Nat.factorial (n - k) := by
    positivity
  have h1' : n.choose k * Nat.factorial k * Nat.factorial (n - k) = Nat.factorial n := h1
  have main_eq :
      n.choose k * k.choose m * (Nat.factorial m * Nat.factorial (k - m) * Nat.factorial (n - k))
        = n.choose m * (n - m).choose (k - m) *
            (Nat.factorial m * Nat.factorial (k - m) * Nat.factorial (n - k)) := by
    calc n.choose k * k.choose m *
            (Nat.factorial m * Nat.factorial (k - m) * Nat.factorial (n - k))
        = n.choose k *
            (k.choose m * Nat.factorial m * Nat.factorial (k - m)) * Nat.factorial (n - k) := by ring
      _ = n.choose k * Nat.factorial k * Nat.factorial (n - k) := by rw [h2]
      _ = Nat.factorial n := h1'
      _ = n.choose m * Nat.factorial m * Nat.factorial (n - m) := h3.symm
      _ = n.choose m * Nat.factorial m *
            ((n - m).choose (k - m) * Nat.factorial (k - m) * Nat.factorial (n - k)) := by
          rw [h4_raw]
      _ = n.choose m * (n - m).choose (k - m) *
            (Nat.factorial m * Nat.factorial (k - m) * Nat.factorial (n - k)) := by ring
  exact Nat.eq_of_mul_eq_mul_right hpos main_eq

/-- **Existence axiom (temporary scaffold, to be eliminated)**: under a
strengthened Fisher-style pair-packing bound, a `ValidKSubsetFamily`
exists.

**Hypothesis** (greedy-feasibility, `2 · target_size · C(k,2)² ≤ C(|W|, 2)`):
strictly stronger than the pure Fisher bound `target_size · C(k,2) ≤
C(|W|, 2)` by a factor of `2 · C(k, 2)`. The Fisher bound alone is
necessary but **not sufficient** for either greedy OR a standard
probabilistic deletion argument — both incur an extra factor of
`C(k, 2)` from the per-violation union-bound.

Strengthened hypothesis derivation:
* Greedy: each chosen `J ∈ family` blocks at most `C(k, 2) · C(|W|-2, k-2)`
  further k-subsets (a 2-subset of `J` extended to any k-set). Process all
  `C(|W|, k)` k-subsets; rejected ≤ `|family| · C(k, 2) · C(|W|-2, k-2)`.
  Hence `|family| ≥ C(|W|, k) / (1 + C(k, 2) · C(|W|-2, k-2))`.
  Via the identity `C(|W|, k) · C(k, 2) = C(|W|, 2) · C(|W|-2, k-2)`:
  `|family| ≥ C(|W|, 2) / (2 · C(k, 2)²)` (assuming `C(k, 2) · C(|W|-2, k-2) ≥ 1`).
* So `2 · target_size · C(k, 2)² ≤ C(|W|, 2) ⟹ target_size ≤ |family|`,
  which gives `(3/4) · target_size ≤ target_size ≤ |family|`.

**FKS regime check**: with `target_size ≈ |W| · k / n*`, `k ≈ log n*`,
`|W| ≈ n* / log² n*` (block size), the hypothesis becomes
`2 · (n*·k/n*) · k⁴ ≤ |W|² / 2`, i.e., `4 · k⁵ ≤ |W|² = (n*/log² n*)²`.
With `k = log n*`: `4 · log⁵ n* ≤ n*² / log⁴ n*`, holds for large `n*`.

**Construction (planned)**: greedy enumeration of `W.powersetCard k`.
Each candidate `I` is added iff `∀ J ∈ acc, |I ∩ J| ≤ 1`. Termination
guaranteed; the size bound follows from the counting above.

**Bugfix history**:
* Cycle 4 (2026-06-02): fixed prior `target_size ≤ Nat.choose W.card k`
  hypothesis (counterexample: `k=3, |W|=10, target_size=120`).
* Cycle 31 (2026-06-02): strengthened from `target_size · C(k,2) ≤
  C(|W|, 2)` (Fisher) to `2 · target_size · C(k,2)² ≤ C(|W|, 2)` after
  recount showed Fisher insufficient for both Route 1 (probabilistic
  deletion's `E[Y] = O(target² · C(k,2)² / C(|W|, 2))`) and Route 2
  (greedy union bound). Currently 0 downstream consumers; safe to
  strengthen. -/
theorem exists_valid_k_subset_family {α : Type*} [DecidableEq α]
    (W : Finset α) (k target_size : ℕ)
    (h_k : 2 ≤ k) (h_k_le : k ≤ W.card)
    (h_strengthened : 2 * target_size * (Nat.choose k 2) ^ 2 ≤ Nat.choose W.card 2) :
    Nonempty (ValidKSubsetFamily α W k target_size) := by
  classical
  -- Step 1: Pick a max-cardinality valid family.
  let candidates : Finset (Finset (Finset α)) :=
    (W.powersetCard k).powerset.filter (fun fam =>
      ∀ J₁ ∈ fam, ∀ J₂ ∈ fam, J₁ ≠ J₂ → (J₁ ∩ J₂).card ≤ 1)
  have h_empty_mem : ∅ ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset,
               Finset.empty_subset, true_and]
    intro J₁ hJ₁; simp at hJ₁
  obtain ⟨maximal, h_max_mem, h_max⟩ :=
    candidates.exists_max_image Finset.card ⟨∅, h_empty_mem⟩
  have h_max_in : maximal ∈ candidates := h_max_mem
  have h_max_subset : maximal ⊆ W.powersetCard k := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset] at h_max_in
    exact h_max_in.1
  have h_max_pairwise : ∀ J₁ ∈ maximal, ∀ J₂ ∈ maximal, J₁ ≠ J₂ → (J₁ ∩ J₂).card ≤ 1 := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset] at h_max_in
    exact h_max_in.2
  -- Step 2: Maximality property.
  have h_maximality : ∀ I ∈ W.powersetCard k, I ∉ maximal →
      ∃ J ∈ maximal, 2 ≤ (I ∩ J).card := by
    intro I hI hI_not_in
    by_contra h_not_exists
    push_neg at h_not_exists
    have h_overlap : ∀ J ∈ maximal, (I ∩ J).card ≤ 1 := fun J hJ => by
      have := h_not_exists J hJ; omega
    have h_new_mem : insert I maximal ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · rw [Finset.insert_subset_iff]; exact ⟨hI, h_max_subset⟩
      · intro J₁ hJ₁ J₂ hJ₂ hne
        rw [Finset.mem_insert] at hJ₁ hJ₂
        rcases hJ₁ with rfl | hJ₁ <;> rcases hJ₂ with rfl | hJ₂
        · contradiction
        · exact h_overlap J₂ hJ₂
        · have := h_overlap J₁ hJ₁; rwa [Finset.inter_comm] at this
        · exact h_max_pairwise J₁ hJ₁ J₂ hJ₂ hne
    have h_card_new : (insert I maximal).card = maximal.card + 1 :=
      Finset.card_insert_of_notMem hI_not_in
    have h_max_ge_new : (insert I maximal).card ≤ maximal.card :=
      h_max (insert I maximal) h_new_mem
    omega
  -- Step 3: Counting bound on non-maximal subsets.
  have h_J_card : ∀ J ∈ maximal, J ⊆ W ∧ J.card = k := fun J hJ => by
    have := h_max_subset hJ
    rw [Finset.mem_powersetCard] at this; exact this
  have h_diff_subset :
      W.powersetCard k \ maximal ⊆
        maximal.biUnion (fun J =>
          (J.powersetCard 2).biUnion (fun p =>
            (W.powersetCard k).filter (fun I => p ⊆ I))) := by
    intro I hI
    rw [Finset.mem_sdiff] at hI
    obtain ⟨hI_mem, hI_not_in⟩ := hI
    obtain ⟨J, hJ_mem, hcard⟩ := h_maximality I hI_mem hI_not_in
    obtain ⟨p, hp_sub, hp_card⟩ : ∃ p ⊆ I ∩ J, p.card = 2 :=
      Finset.exists_subset_card_eq hcard
    refine Finset.mem_biUnion.mpr ⟨J, hJ_mem, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨hp_sub.trans Finset.inter_subset_right, hp_card⟩
    · rw [Finset.mem_filter]
      exact ⟨hI_mem, hp_sub.trans Finset.inter_subset_left⟩
  have h_count :
      (W.powersetCard k \ maximal).card
        ≤ maximal.card * (Nat.choose k 2 * Nat.choose (W.card - 2) (k - 2)) := by
    calc (W.powersetCard k \ maximal).card
        ≤ _ := Finset.card_le_card h_diff_subset
      _ ≤ ∑ J ∈ maximal, ((J.powersetCard 2).biUnion (fun p =>
            (W.powersetCard k).filter (fun I => p ⊆ I))).card := Finset.card_biUnion_le
      _ ≤ ∑ J ∈ maximal, ∑ p ∈ J.powersetCard 2,
            ((W.powersetCard k).filter (fun I => p ⊆ I)).card := by
          apply Finset.sum_le_sum; intros J _; exact Finset.card_biUnion_le
      _ ≤ ∑ J ∈ maximal, ∑ _ ∈ J.powersetCard 2,
            Nat.choose (W.card - 2) (k - 2) := by
          apply Finset.sum_le_sum; intros J hJ
          apply Finset.sum_le_sum; intros p hp
          rw [Finset.mem_powersetCard] at hp
          have hp_sub_W : p ⊆ W := hp.1.trans (h_J_card J hJ).1
          have hpk : p.card ≤ k := by rw [hp.2]; omega
          rw [card_powersetCard_filter_subset W k p hp_sub_W hpk, hp.2]
      _ = ∑ J ∈ maximal, (J.powersetCard 2).card * Nat.choose (W.card - 2) (k - 2) := by
          apply Finset.sum_congr rfl; intros J _
          rw [Finset.sum_const, smul_eq_mul]
      _ = ∑ J ∈ maximal, Nat.choose k 2 * Nat.choose (W.card - 2) (k - 2) := by
          apply Finset.sum_congr rfl; intros J hJ
          rw [Finset.card_powersetCard, (h_J_card J hJ).2]
      _ = maximal.card * (Nat.choose k 2 * Nat.choose (W.card - 2) (k - 2)) := by
          rw [Finset.sum_const, smul_eq_mul]
  -- Step 4: Combine partition + counting + identity + hypothesis.
  have h_partition' : (W.powersetCard k).card = maximal.card + (W.powersetCard k \ maximal).card := by
    have := Finset.card_sdiff_add_card_eq_card h_max_subset; omega
  rw [Finset.card_powersetCard] at h_partition'
  have h_main_ineq :
      W.card.choose k ≤ maximal.card * (1 + Nat.choose k 2 * Nat.choose (W.card - 2) (k - 2)) := by
    calc W.card.choose k
        = maximal.card + (W.powersetCard k \ maximal).card := h_partition'
      _ ≤ maximal.card + maximal.card * (Nat.choose k 2 * Nat.choose (W.card - 2) (k - 2)) := by
          linarith
      _ = maximal.card * (1 + Nat.choose k 2 * Nat.choose (W.card - 2) (k - 2)) := by ring
  have h_identity :
      W.card.choose k * Nat.choose k 2 = W.card.choose 2 * (W.card - 2).choose (k - 2) :=
    choose_mul_choose_eq_choose_mul_choose (show 2 ≤ k from h_k) h_k_le
  -- 2 · target_size · C(k,2)² ≤ C(W,2). Want target_size ≤ |maximal|.
  -- Strategy:
  --   C(W, 2) · C(W-2, k-2) = C(W, k) · C(k, 2)   (identity)
  --                      ≤ maximal.card * (1 + C(k,2) · C(W-2, k-2)) * C(k, 2)
  --                      ≤ 2 · maximal.card · C(k,2)² · C(W-2, k-2)   (when C(k,2)·C(W-2,k-2) ≥ 1)
  -- Cancel C(W-2, k-2): C(W, 2) ≤ 2 · maximal.card · C(k,2)².
  -- Hypothesis: 2 · target_size · C(k,2)² ≤ C(W, 2) ≤ 2 · maximal.card · C(k,2)².
  -- Cancel 2 · C(k,2)²: target_size ≤ maximal.card.
  have h_Ck2_pos : 0 < Nat.choose k 2 := Nat.choose_pos h_k
  -- Need C(W-2, k-2) > 0 or k = 2.
  have h_target_le : target_size ≤ maximal.card := by
    by_cases h_sub_zero : (W.card - 2).choose (k - 2) = 0
    · -- W.card - 2 < k - 2 means W.card < k, contradicting h_k_le.
      have := Nat.choose_eq_zero_iff.mp h_sub_zero
      omega
    have h_sub_pos : 0 < (W.card - 2).choose (k - 2) := Nat.pos_of_ne_zero h_sub_zero
    have h_prod_pos : 0 < Nat.choose k 2 * (W.card - 2).choose (k - 2) :=
      Nat.mul_pos h_Ck2_pos h_sub_pos
    -- 1 + C(k,2) · C(W-2,k-2) ≤ 2 · C(k,2) · C(W-2,k-2)
    have h_bound :
        1 + Nat.choose k 2 * (W.card - 2).choose (k - 2)
          ≤ 2 * (Nat.choose k 2 * (W.card - 2).choose (k - 2)) := by linarith
    have h_step1 :
        W.card.choose k * Nat.choose k 2
          ≤ maximal.card * (1 + Nat.choose k 2 * (W.card - 2).choose (k - 2)) * Nat.choose k 2 :=
      Nat.mul_le_mul_right _ h_main_ineq
    have h_step2 :
        W.card.choose k * Nat.choose k 2
          ≤ maximal.card * (2 * (Nat.choose k 2 * (W.card - 2).choose (k - 2))) * Nat.choose k 2 := by
      apply le_trans h_step1
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_left
      exact h_bound
    rw [h_identity] at h_step2
    -- h_step2 : C(W,2) · C(W-2,k-2) ≤ maximal.card · (2 · C(k,2) · C(W-2,k-2)) · C(k,2)
    have h_factored :
        W.card.choose 2 * (W.card - 2).choose (k - 2)
          ≤ 2 * maximal.card * Nat.choose k 2 * Nat.choose k 2 * (W.card - 2).choose (k - 2) := by
      calc W.card.choose 2 * (W.card - 2).choose (k - 2)
          ≤ maximal.card * (2 * (Nat.choose k 2 * (W.card - 2).choose (k - 2))) * Nat.choose k 2 :=
            h_step2
        _ = 2 * maximal.card * Nat.choose k 2 * Nat.choose k 2 * (W.card - 2).choose (k - 2) := by
            ring
    have h_dropped :
        W.card.choose 2 ≤ 2 * maximal.card * Nat.choose k 2 * Nat.choose k 2 :=
      Nat.le_of_mul_le_mul_right h_factored h_sub_pos
    -- Combine with hypothesis: 2 · target_size · C(k,2)² ≤ C(W, 2) ≤ 2 · maximal.card · C(k,2)²
    have h_hyp : 2 * target_size * Nat.choose k 2 * Nat.choose k 2 ≤ W.card.choose 2 := by
      have h_sq : (Nat.choose k 2) ^ 2 = Nat.choose k 2 * Nat.choose k 2 := by ring
      rw [h_sq] at h_strengthened
      linarith
    have h_chain :
        2 * target_size * Nat.choose k 2 * Nat.choose k 2
          ≤ 2 * maximal.card * Nat.choose k 2 * Nat.choose k 2 := le_trans h_hyp h_dropped
    -- Cancel 2 · C(k,2) · C(k,2):
    have h_pos_factor : 0 < 2 * Nat.choose k 2 * Nat.choose k 2 := by positivity
    have h_re1 : 2 * target_size * Nat.choose k 2 * Nat.choose k 2
                = target_size * (2 * Nat.choose k 2 * Nat.choose k 2) := by ring
    have h_re2 : 2 * maximal.card * Nat.choose k 2 * Nat.choose k 2
                = maximal.card * (2 * Nat.choose k 2 * Nat.choose k 2) := by ring
    rw [h_re1, h_re2] at h_chain
    exact Nat.le_of_mul_le_mul_right h_chain h_pos_factor
  -- Step 5: Build the structure.
  refine ⟨{ family := maximal
          , subsets_of_W := ?_
          , family_card_ge := ?_
          , pairwise_overlap := h_max_pairwise }⟩
  · intro I hI
    have := h_max_subset hI
    rw [Finset.mem_powersetCard] at this; exact this
  · -- (3 · target_size / 4) ≤ target_size ≤ maximal.card
    omega

/-! ## Induced-matching cover → strong edge colouring

The fundamental bridge: a covering of `E(G)` by induced matchings yields a
strong edge colouring with that many colours. Standard fact (Berge 1973),
but worth packaging for the nibble proof — once the nibble
constructs a cover of size `≤ C·n_A·n_B·p / log(n_A·n_B)`, this lemma
delivers the corresponding bound on `chiPrimeS G`. -/

/-- A covering of `E(G)` by induced matchings yields a strong edge
colouring (assign each edge the index of a matching containing it).
Hence `chiPrimeS G ≤ cover.card`. -/
lemma chiPrimeS_le_of_indMatchingCover
    (G : SimpleGraph V)
    (cover : Finset (Finset G.edgeSet))
    (h_match : ∀ M ∈ cover, IsInducedMatching G (M : Set G.edgeSet))
    (h_cover : ∀ e : G.edgeSet, ∃ M ∈ cover, e ∈ M) :
    chiPrimeS G ≤ (cover.card : ℕ∞) := by
  classical
  -- For each edge e, choose a matching `chosen e ∈ cover` containing e.
  let chosen : G.edgeSet → {M : Finset G.edgeSet // M ∈ cover} := fun e =>
    ⟨Classical.choose (h_cover e), (Classical.choose_spec (h_cover e)).1⟩
  have chosen_contains : ∀ e : G.edgeSet, e ∈ (chosen e).val :=
    fun e => (Classical.choose_spec (h_cover e)).2
  -- Index the cover by `Fin cover.card`.
  let f : {M : Finset G.edgeSet // M ∈ cover} ≃ Fin cover.card := cover.equivFin
  -- The colouring: each edge gets the index of its chosen matching.
  let c : G.edgeSet → Fin cover.card := fun e => f (chosen e)
  -- Show c is a strong edge colouring.
  have hc : IsStrongEdgeColouring G c := by
    intro e₁ e₂ hadj h_eq
    -- f is injective, so chosen e₁ = chosen e₂; both edges lie in the same matching M.
    have h_chosen_eq : chosen e₁ = chosen e₂ := f.injective h_eq
    have h₁ : e₁ ∈ (chosen e₁).val := chosen_contains e₁
    have h₂ : e₂ ∈ (chosen e₁).val := by
      rw [h_chosen_eq]; exact chosen_contains e₂
    -- The matching is induced, so distinct edges in it are non-L²-adjacent.
    have h_M_match : IsInducedMatching G ((chosen e₁).val : Set G.edgeSet) :=
      h_match (chosen e₁).val (chosen e₁).property
    have hne : e₁ ≠ e₂ := hadj.1
    exact h_M_match e₁ h₁ e₂ h₂ hne hadj
  -- Conclude `chiPrimeS G ≤ cover.card`.
  unfold chiPrimeS
  refine sInf_le ?_
  exact ⟨cover.card, ⟨c, hc⟩, rfl⟩

end DaveyThesis2024.SecRandomBipartite
