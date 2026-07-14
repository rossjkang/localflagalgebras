/-
Copyright (c) 2026 Ross Kang.
Released under Apache 2.0 license.

# F.7.4.C — Greedy transversal extraction

Given a slot `I_l ⊆ Fin n_A` of size `k`, per-vertex kept-sets
`T : ↥I_l → Finset (Fin n_B)` (the output of F.7.4.B's `keptSet` for each
`a ∈ I_l`), and a floor `ν₀ : ℕ`, extract `M ≥ min_i (T i).card - ν₀`
induced matchings of size `k`, each `{(a, uₐ) : a ∈ I_l}` with
`uₐ ∈ T a` and the `uₐ`'s pairwise distinct.

## Bipartite simplification

For bipartite-on-sum graphs, ANY distinct-vertex selection yields an
`IsBipartiteInducedMatching`. The "no-bridge" condition
`¬ G.Adj (Sum.inl aᵢ) (Sum.inr uⱼ)` for `i ≠ j` holds *automatically*
because `u ∈ keptSet … I_l a` requires `I_l ∈ validSlots G family a u`
which precisely certifies that no `a' ∈ I_l ∖ {a}` is adjacent to `u`.

## Implementation

The greedy procedure is implemented as a **fuel-based recursive function**
(`greedyAux fuel`) rather than well-founded recursion. The fuel ensures
termination structurally without needing a decreasing measure proof; we
choose `fuel = ∑ i, (T i).card + 1` for the headline `greedyMatchings`.

Each iteration:
1. Checks feasibility: every `(T i).card ≥ max ν₀ I_l.card`. (Stopping
   rule: if any row drops below the floor, return current accumulation.)
2. Picks a distinct transversal by folding over `I_l.attach.toList`,
   choosing `uᵢ := (T i ∖ chosen).min'` at each step.
3. Adds the new matching to the accumulator and recurses with
   `T'(i) = (T i).erase (chosenᵢ)`.

## Status

F.7.4.C (cycle 50, 2026-06-03).
-/
import DaveyThesis2024.SecRandomBipartite.SlotAssignment

namespace DaveyThesis2024.SecRandomBipartite.GreedyTransversal

open DaveyThesis2024.SecRandomBipartite

variable {n_A n_B : ℕ}

/-! ## Feasibility predicate -/

/-- `feasible I_l T ν₀`: each kept-set has size at least `max ν₀ I_l.card`.
The `I_l.card`-floor enables picking a distinct transversal (greedy needs
`|T i| ≥ |I_l|` choices); the `ν₀`-floor is the user-supplied stopping rule. -/
def feasible (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) : Prop :=
  ∀ i : ↥I_l, max ν₀ I_l.card ≤ (T i).card

instance (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B)) (ν₀ : ℕ) :
    Decidable (feasible I_l T ν₀) := by
  unfold feasible; infer_instance

/-! ## Step 1 — pick a transversal via list fold -/

/-- Fold over a list `is : List ↥I_l`, at each step picking
`u := (T i ∖ chosen).min'`, returning the picks-function `g`, the
chosen-set, and the matching of pairs `(↑i, u)`. Sentinel `default`
is used when the sdiff is empty (won't happen under feasibility). -/
noncomputable def stepFold
    {I_l : Finset (Fin n_A)} (T : ↥I_l → Finset (Fin n_B))
    (default : Fin n_B) :
    List ↥I_l → Finset (Fin n_A × Fin n_B) → Finset (Fin n_B) →
      (↥I_l → Fin n_B) →
      Finset (Fin n_A × Fin n_B) × Finset (Fin n_B) × (↥I_l → Fin n_B)
  | [], M, chosen, g => (M, chosen, g)
  | i :: rest, M, chosen, g => by
    classical
    exact
      if h : (T i \ chosen).Nonempty then
        let u := (T i \ chosen).min' h
        stepFold T default rest
          (insert ((i : Fin n_A), u) M) (insert u chosen) (Function.update g i u)
      else (M, chosen, Function.update g i default)

/-! ## Invariants for `stepFold`

We track three independent invariants:
* `stepFold_chosen_card`: chosen-set grows by exactly `is.length`.
* `stepFold_matching_card`: matching grows by exactly `is.length`.
* `stepFold_pair_mem`: every pair `(a, u)` in matching has `u ∈ T a`.
* `stepFold_g_mem_or_default`: for `i ∈ is`, either `g i ∈ T i` or
  the step failed at `i` (irrelevant under feasibility).

For the well-founded greedy, we'll only need the lemmas under the
feasibility precondition, which guarantees the "successful" branch.
-/

/-- Auxiliary: under feasibility, the sdiff `T i ∖ chosen` is nonempty. -/
private lemma sdiff_ne_under_feas
    {I_l : Finset (Fin n_A)} (T : ↥I_l → Finset (Fin n_B))
    (h_card : ∀ i : ↥I_l, I_l.card ≤ (T i).card)
    {i : ↥I_l} {chosen : Finset (Fin n_B)}
    (h_chosen_lt : chosen.card < I_l.card) :
    (T i \ chosen).Nonempty := by
  classical
  rw [← Finset.card_pos]
  have h_chosen_lt_T : chosen.card < (T i).card := h_chosen_lt.trans_le (h_card i)
  have h_sd := Finset.le_card_sdiff chosen (T i)
  omega

/-- Chosen-set grows by exactly `is.length`. -/
private lemma stepFold_chosen_card
    {I_l : Finset (Fin n_A)} (T : ↥I_l → Finset (Fin n_B))
    (h_card : ∀ i : ↥I_l, I_l.card ≤ (T i).card)
    (default : Fin n_B) :
    ∀ (is : List ↥I_l) (M : Finset (Fin n_A × Fin n_B))
      (chosen : Finset (Fin n_B)) (g : ↥I_l → Fin n_B),
      chosen.card + is.length ≤ I_l.card →
      (stepFold T default is M chosen g).2.1.card = chosen.card + is.length := by
  classical
  intro is
  induction is with
  | nil => intro _ _ _ _; simp [stepFold]
  | cons i rest ih =>
    intro M chosen g h_le
    have h_chosen_lt : chosen.card < I_l.card := by
      have : (i :: rest).length = rest.length + 1 := List.length_cons
      omega
    have h_diff_ne := sdiff_ne_under_feas T h_card (i := i) h_chosen_lt
    simp only [stepFold]
    rw [dif_pos h_diff_ne]
    set u := (T i \ chosen).min' h_diff_ne
    have h_u_notin : u ∉ chosen :=
      (Finset.mem_sdiff.mp (Finset.min'_mem _ h_diff_ne)).2
    have h_chosen_le : (insert u chosen).card + rest.length ≤ I_l.card := by
      rw [Finset.card_insert_of_notMem h_u_notin]
      have : (i :: rest).length = rest.length + 1 := List.length_cons
      omega
    rw [ih _ _ _ h_chosen_le, Finset.card_insert_of_notMem h_u_notin]
    have : (i :: rest).length = rest.length + 1 := List.length_cons
    omega

/-- Every pair `(a, u)` in the running matching after `stepFold` either was
already in the input matching `M`, or has `u ∈ T a` and `a ∈ I_l`. -/
private lemma stepFold_pair_mem
    {I_l : Finset (Fin n_A)} (T : ↥I_l → Finset (Fin n_B))
    (h_card : ∀ i : ↥I_l, I_l.card ≤ (T i).card)
    (default : Fin n_B) :
    ∀ (is : List ↥I_l) (chosen : Finset (Fin n_B)) (g : ↥I_l → Fin n_B)
      (M : Finset (Fin n_A × Fin n_B)),
      chosen.card + is.length ≤ I_l.card →
      (∀ ab ∈ M, ∃ h : ab.1 ∈ I_l, ab.2 ∈ T ⟨ab.1, h⟩) →
      ∀ ab ∈ (stepFold T default is M chosen g).1,
        ∃ h : ab.1 ∈ I_l, ab.2 ∈ T ⟨ab.1, h⟩ := by
  classical
  intro is
  induction is with
  | nil => intro _ _ M _ h_M ab h_ab; simp [stepFold] at h_ab; exact h_M ab h_ab
  | cons i rest ih =>
    intro chosen g M h_le h_M
    have h_chosen_lt : chosen.card < I_l.card := by
      have : (i :: rest).length = rest.length + 1 := List.length_cons
      omega
    have h_diff_ne := sdiff_ne_under_feas T h_card (i := i) h_chosen_lt
    simp only [stepFold]
    rw [dif_pos h_diff_ne]
    set u := (T i \ chosen).min' h_diff_ne
    have h_u_mem_T : u ∈ T i := (Finset.mem_sdiff.mp (Finset.min'_mem _ h_diff_ne)).1
    have h_u_notin : u ∉ chosen :=
      (Finset.mem_sdiff.mp (Finset.min'_mem _ h_diff_ne)).2
    have h_chosen_le : (insert u chosen).card + rest.length ≤ I_l.card := by
      rw [Finset.card_insert_of_notMem h_u_notin]
      have : (i :: rest).length = rest.length + 1 := List.length_cons
      omega
    have h_M' : ∀ ab ∈ insert ((i : Fin n_A), u) M,
                  ∃ h : ab.1 ∈ I_l, ab.2 ∈ T ⟨ab.1, h⟩ := by
      intro ab h_ab
      rcases Finset.mem_insert.mp h_ab with h_eq | h_ab_in_M
      · subst h_eq
        refine ⟨i.2, ?_⟩
        change u ∈ T ⟨(i : Fin n_A), i.2⟩
        have hi : (⟨(i : Fin n_A), i.2⟩ : ↥I_l) = i := Subtype.ext rfl
        rw [hi]; exact h_u_mem_T
      · exact h_M ab h_ab_in_M
    exact ih _ _ _ h_chosen_le h_M'

/-- Preservation lemma: `stepFold` on a list `is` not containing `j`
leaves `g j` unchanged. (Inducting on `is`, both branches preserve `g j`
because `Function.update _ k _ j = g j` when `j ≠ k`.) -/
private lemma stepFold_g_preserve
    {I_l : Finset (Fin n_A)} (T : ↥I_l → Finset (Fin n_B))
    (default : Fin n_B) (j : ↥I_l) :
    ∀ (is : List ↥I_l) (M : Finset (Fin n_A × Fin n_B))
      (chosen : Finset (Fin n_B)) (g : ↥I_l → Fin n_B),
      ¬ j ∈ is →
      (stepFold T default is M chosen g).2.2 j = g j := by
  classical
  intro is
  induction is with
  | nil => intros; simp [stepFold]
  | cons k rest ih =>
    intro M chosen g h_notin
    have h_not_k : j ≠ k := fun heq => h_notin (heq ▸ List.mem_cons_self)
    have h_not_rest : ¬ j ∈ rest := fun hh =>
      h_notin (List.mem_cons_of_mem _ hh)
    simp only [stepFold]
    by_cases h : (T k \ chosen).Nonempty
    · rw [dif_pos h]
      set u := (T k \ chosen).min' h
      rw [ih _ _ (Function.update g k u) h_not_rest]
      simp [Function.update, h_not_k]
    · rw [dif_neg h]
      simp [Function.update, h_not_k]

/-- Under feasibility, after `stepFold`, the picks function `g` satisfies
`g i ∈ T i` for every `i ∈ is` (Nodup). -/
private lemma stepFold_g_mem
    {I_l : Finset (Fin n_A)} (T : ↥I_l → Finset (Fin n_B))
    (h_card : ∀ i : ↥I_l, I_l.card ≤ (T i).card)
    (default : Fin n_B) :
    ∀ (is : List ↥I_l) (chosen : Finset (Fin n_B)) (g : ↥I_l → Fin n_B)
      (M : Finset (Fin n_A × Fin n_B)),
      chosen.card + is.length ≤ I_l.card →
      is.Nodup →
      ∀ i ∈ is, (stepFold T default is M chosen g).2.2 i ∈ T i := by
  classical
  intro is
  induction is with
  | nil => intro _ _ _ _ _ i h; exact absurd h List.not_mem_nil
  | cons i₀ rest ih =>
    intro chosen g M h_le h_nodup i h_in
    have h_chosen_lt : chosen.card < I_l.card := by
      have : (i₀ :: rest).length = rest.length + 1 := List.length_cons
      omega
    have h_diff_ne := sdiff_ne_under_feas T h_card (i := i₀) h_chosen_lt
    simp only [stepFold]
    rw [dif_pos h_diff_ne]
    set u₀ := (T i₀ \ chosen).min' h_diff_ne
    have h_u₀_mem_T : u₀ ∈ T i₀ :=
      (Finset.mem_sdiff.mp (Finset.min'_mem _ h_diff_ne)).1
    have h_u₀_notin : u₀ ∉ chosen :=
      (Finset.mem_sdiff.mp (Finset.min'_mem _ h_diff_ne)).2
    have h_chosen_le : (insert u₀ chosen).card + rest.length ≤ I_l.card := by
      rw [Finset.card_insert_of_notMem h_u₀_notin]
      have : (i₀ :: rest).length = rest.length + 1 := List.length_cons
      omega
    have h_nodup_rest : rest.Nodup := (List.nodup_cons.mp h_nodup).2
    rcases List.mem_cons.mp h_in with rfl | h_i_in_rest
    · -- After rfl: i₀ has been replaced by `i`. stepFold preserves g i since i ∉ rest.
      have h_i_notin_rest : ¬ i ∈ rest := (List.nodup_cons.mp h_nodup).1
      have h_preserve := stepFold_g_preserve T default i rest
                          (insert ((i : Fin n_A), u₀) M) (insert u₀ chosen)
                          (Function.update g i u₀) h_i_notin_rest
      rw [h_preserve]
      simp [Function.update]
      exact h_u₀_mem_T
    · exact ih _ _ _ h_chosen_le h_nodup_rest i h_i_in_rest

/-- The matching's cardinality after `stepFold` equals `M.card + is.length`
when `M`'s u's are all already in `chosen`. -/
private lemma stepFold_matching_card
    {I_l : Finset (Fin n_A)} (T : ↥I_l → Finset (Fin n_B))
    (h_card : ∀ i : ↥I_l, I_l.card ≤ (T i).card)
    (default : Fin n_B) :
    ∀ (is : List ↥I_l) (chosen : Finset (Fin n_B)) (g : ↥I_l → Fin n_B)
      (M : Finset (Fin n_A × Fin n_B)),
      chosen.card + is.length ≤ I_l.card →
      (∀ ab ∈ M, ab.2 ∈ chosen) →
      (stepFold T default is M chosen g).1.card = M.card + is.length := by
  classical
  intro is
  induction is with
  | nil => intro _ _ _ _ _; simp [stepFold]
  | cons i rest ih =>
    intro chosen g M h_le h_M
    have h_chosen_lt : chosen.card < I_l.card := by
      have : (i :: rest).length = rest.length + 1 := List.length_cons
      omega
    have h_diff_ne := sdiff_ne_under_feas T h_card (i := i) h_chosen_lt
    simp only [stepFold]
    rw [dif_pos h_diff_ne]
    set u := (T i \ chosen).min' h_diff_ne
    have h_u_notin : u ∉ chosen :=
      (Finset.mem_sdiff.mp (Finset.min'_mem _ h_diff_ne)).2
    have h_new_pair_notin : ((i : Fin n_A), u) ∉ M := fun h_in =>
      h_u_notin (h_M _ h_in)
    have h_chosen_le : (insert u chosen).card + rest.length ≤ I_l.card := by
      rw [Finset.card_insert_of_notMem h_u_notin]
      have : (i :: rest).length = rest.length + 1 := List.length_cons
      omega
    have h_M' : ∀ ab ∈ insert ((i : Fin n_A), u) M, ab.2 ∈ insert u chosen := by
      intro ab h_ab
      rcases Finset.mem_insert.mp h_ab with h | h
      · rw [h]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (h_M _ h)
    rw [ih _ _ _ h_chosen_le h_M', Finset.card_insert_of_notMem h_new_pair_notin]
    have : (i :: rest).length = rest.length + 1 := List.length_cons
    omega

/-! ## Step 2 — one greedy iteration

A single greedy step: given current `T`, returns a matching of size
`I_l.card` together with the updated `T'(i) = (T i).erase (g i)`,
where `g i` is the picked u for row `i`. Under feasibility this works;
under failure (the `else` branch) we return `(∅, T)` and the outer loop
will terminate.

We take an explicit `default : Fin n_B` parameter; at the headline API
level, when `0 < n_B` (guaranteed by feasibility with `0 < I_l.card`),
the caller can supply `⟨0, h⟩` or take `default := (T i₀).min'` for any
`i₀ : ↥I_l`. -/

/-- One greedy step. Outputs `(M, T', g)`. -/
noncomputable def greedyStep
    (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) :
    Finset (Fin n_A × Fin n_B) × (↥I_l → Finset (Fin n_B)) × (↥I_l → Fin n_B) := by
  classical
  exact
    if h : feasible I_l T ν₀ then
      let result := stepFold T default I_l.attach.toList ∅ ∅ (fun _ => default)
      let M := result.1
      let g := result.2.2
      let T' : ↥I_l → Finset (Fin n_B) := fun i => (T i).erase (g i)
      (M, T', g)
    else (∅, T, fun _ => default)

/-! ## Termination measure -/

/-- The total budget `∑ i, (T i).card`. Used as the termination measure
for the well-founded greedy recursion. -/
def totalCard (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B)) : ℕ :=
  ∑ i : ↥I_l, (T i).card

/-- After one feasible greedy step (with `I_l` nonempty), the total
budget strictly decreases. -/
private lemma totalCard_greedyStep_lt
    (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B)
    (h_feas : feasible I_l T ν₀) (h_pos : 0 < I_l.card) :
    totalCard I_l (greedyStep I_l T ν₀ default).2.1 < totalCard I_l T := by
  classical
  unfold greedyStep totalCard
  rw [dif_pos h_feas]
  simp only
  have h_card_floor : ∀ i : ↥I_l, I_l.card ≤ (T i).card := fun i =>
    le_trans (le_max_right _ _) (h_feas i)
  set g := (stepFold T default I_l.attach.toList ∅ ∅ (fun _ => default)).2.2
  -- Sum bound: for each i, (T i).erase (g i) has card ≤ (T i).card.
  have h_le : ∀ i : ↥I_l, ((T i).erase (g i)).card ≤ (T i).card :=
    fun i => Finset.card_erase_le
  -- Pick some i₀ ∈ I_l.attach (which is nonempty since I_l.card > 0).
  have h_attach_ne : I_l.attach.Nonempty := by
    rw [← Finset.card_pos, Finset.card_attach]; exact h_pos
  obtain ⟨i₀, h_i₀_mem_attach⟩ := h_attach_ne
  have h_i₀_in_list : i₀ ∈ I_l.attach.toList := Finset.mem_toList.mpr h_i₀_mem_attach
  have h_nodup : I_l.attach.toList.Nodup := Finset.nodup_toList _
  have h_len_le : (∅ : Finset (Fin n_B)).card + I_l.attach.toList.length ≤ I_l.card := by
    rw [Finset.card_empty, zero_add, Finset.length_toList, Finset.card_attach]
  have h_g_in_T : g i₀ ∈ T i₀ := stepFold_g_mem T h_card_floor default
                                    I_l.attach.toList ∅ (fun _ => default) ∅
                                    h_len_le h_nodup i₀ h_i₀_in_list
  have h_erase_card_i₀ : ((T i₀).erase (g i₀)).card = (T i₀).card - 1 := by
    rw [Finset.card_erase_of_mem h_g_in_T]
  have h_T_i₀_pos : 0 < (T i₀).card := by
    have := h_card_floor i₀; omega
  -- Sum split via Finset.sum_erase_add.
  have h_sum_T : ∑ i, (T i).card =
                 (T i₀).card + ∑ i ∈ Finset.univ.erase i₀, (T i).card :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
  have h_sum_T' : ∑ i, ((T i).erase (g i)).card =
                  ((T i₀).erase (g i₀)).card +
                    ∑ i ∈ Finset.univ.erase i₀, ((T i).erase (g i)).card :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
  have h_rest_le : (∑ i ∈ Finset.univ.erase i₀, ((T i).erase (g i)).card) ≤
                   (∑ i ∈ Finset.univ.erase i₀, (T i).card) :=
    Finset.sum_le_sum (fun i _ => h_le i)
  rw [h_sum_T', h_sum_T, h_erase_card_i₀]
  omega

/-! ## Step 3 — main definition: `greedyMatchings`

Well-founded recursion on `totalCard I_l T`. Each successful step
strictly decreases the total budget, ensuring termination.

When feasibility holds, output `insert M (greedyMatchings T' …)` where
`M` is the matching from `greedyStep` and `T'` is the erased version.
When feasibility fails, output `∅`.
-/

/-- The set of induced matchings extracted by the greedy procedure. -/
noncomputable def greedyMatchings
    (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) :
    Finset (Finset (Fin n_A × Fin n_B)) := by
  classical
  exact
    if h_pos : 0 < I_l.card then
      if h_feas : feasible I_l T ν₀ then
        have hlt : totalCard I_l (greedyStep I_l T ν₀ default).2.1 < totalCard I_l T :=
          totalCard_greedyStep_lt I_l T ν₀ default h_feas h_pos
        insert (greedyStep I_l T ν₀ default).1
          (greedyMatchings I_l (greedyStep I_l T ν₀ default).2.1 ν₀ default)
      else ∅
    else ∅
termination_by totalCard I_l T

/-- Unfold equation for `greedyMatchings` when feasibility holds. -/
private lemma greedyMatchings_eq_of_feasible
    (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B)
    (h_pos : 0 < I_l.card) (h_feas : feasible I_l T ν₀) :
    greedyMatchings I_l T ν₀ default =
      insert (greedyStep I_l T ν₀ default).1
        (greedyMatchings I_l (greedyStep I_l T ν₀ default).2.1 ν₀ default) := by
  classical
  rw [greedyMatchings]
  simp [h_pos, h_feas]

/-- Unfold equation for `greedyMatchings` when feasibility fails (or `I_l` is empty). -/
private lemma greedyMatchings_eq_empty_of_infeasible
    (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B)
    (h : 0 < I_l.card → ¬ feasible I_l T ν₀) :
    greedyMatchings I_l T ν₀ default = ∅ := by
  classical
  rw [greedyMatchings]
  by_cases h_pos : 0 < I_l.card
  · simp [h_pos, h h_pos]
  · simp [h_pos]

/-! ## Properties of the matching from `greedyStep` -/

/-- Under feasibility, the matching from one greedy step has cardinality
exactly `I_l.card`. -/
private lemma greedyStep_matching_card
    (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) (h_feas : feasible I_l T ν₀) :
    (greedyStep I_l T ν₀ default).1.card = I_l.card := by
  classical
  unfold greedyStep
  rw [dif_pos h_feas]
  simp only
  have h_card_floor : ∀ i : ↥I_l, I_l.card ≤ (T i).card := fun i =>
    le_trans (le_max_right _ _) (h_feas i)
  have h_len_le : (∅ : Finset (Fin n_B)).card + I_l.attach.toList.length ≤ I_l.card := by
    rw [Finset.card_empty, zero_add, Finset.length_toList, Finset.card_attach]
  have h_emp_M : ∀ ab ∈ (∅ : Finset (Fin n_A × Fin n_B)), ab.2 ∈ (∅ : Finset (Fin n_B)) :=
    fun ab h => absurd h (Finset.notMem_empty _)
  have h := stepFold_matching_card T h_card_floor default I_l.attach.toList ∅
              (fun _ => default) ∅ h_len_le h_emp_M
  rw [h, Finset.card_empty, zero_add, Finset.length_toList, Finset.card_attach]

/-- Every pair in the matching from one greedy step has `u ∈ T a`. -/
private lemma greedyStep_pair_mem
    (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) (h_feas : feasible I_l T ν₀) :
    ∀ ab ∈ (greedyStep I_l T ν₀ default).1,
      ∃ h : ab.1 ∈ I_l, ab.2 ∈ T ⟨ab.1, h⟩ := by
  classical
  unfold greedyStep
  rw [dif_pos h_feas]
  simp only
  have h_card_floor : ∀ i : ↥I_l, I_l.card ≤ (T i).card := fun i =>
    le_trans (le_max_right _ _) (h_feas i)
  have h_len_le : (∅ : Finset (Fin n_B)).card + I_l.attach.toList.length ≤ I_l.card := by
    rw [Finset.card_empty, zero_add, Finset.length_toList, Finset.card_attach]
  have h_emp_M : ∀ ab ∈ (∅ : Finset (Fin n_A × Fin n_B)),
                   ∃ h : ab.1 ∈ I_l, ab.2 ∈ T ⟨ab.1, h⟩ :=
    fun ab h => absurd h (Finset.notMem_empty _)
  exact stepFold_pair_mem T h_card_floor default I_l.attach.toList ∅
        (fun _ => default) ∅ h_len_le h_emp_M

/-- The u-coords of pairs in the matching are a subset of `chosen`. -/
private lemma stepFold_u_subset_chosen
    {I_l : Finset (Fin n_A)} (T : ↥I_l → Finset (Fin n_B))
    (h_card : ∀ i : ↥I_l, I_l.card ≤ (T i).card)
    (default : Fin n_B) :
    ∀ (is : List ↥I_l) (chosen : Finset (Fin n_B)) (g : ↥I_l → Fin n_B)
      (M : Finset (Fin n_A × Fin n_B)),
      chosen.card + is.length ≤ I_l.card →
      (∀ ab ∈ M, ab.2 ∈ chosen) →
      ∀ ab ∈ (stepFold T default is M chosen g).1,
        ab.2 ∈ (stepFold T default is M chosen g).2.1 := by
  classical
  intro is
  induction is with
  | nil => intro _ _ _ _ h_M ab h_ab; simp [stepFold] at h_ab ⊢; exact h_M ab h_ab
  | cons i rest ih =>
    intro chosen g M h_le h_M
    have h_chosen_lt : chosen.card < I_l.card := by
      have : (i :: rest).length = rest.length + 1 := List.length_cons
      omega
    have h_diff_ne := sdiff_ne_under_feas T h_card (i := i) h_chosen_lt
    simp only [stepFold]
    rw [dif_pos h_diff_ne]
    set u := (T i \ chosen).min' h_diff_ne
    have h_u_notin : u ∉ chosen :=
      (Finset.mem_sdiff.mp (Finset.min'_mem _ h_diff_ne)).2
    have h_chosen_le : (insert u chosen).card + rest.length ≤ I_l.card := by
      rw [Finset.card_insert_of_notMem h_u_notin]
      have : (i :: rest).length = rest.length + 1 := List.length_cons
      omega
    have h_M' : ∀ ab ∈ insert ((i : Fin n_A), u) M, ab.2 ∈ insert u chosen := by
      intro ab h_ab
      rcases Finset.mem_insert.mp h_ab with h | h
      · rw [h]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (h_M _ h)
    exact ih _ _ _ h_chosen_le h_M'

/-- Invariant: after stepFold, the matching's first-projection is the
union of the input matching's first-projection and the processed list's
first-projection-as-Finset. For our initial state `M = ∅`, this gives
`M_final.image Prod.fst = is.map Subtype.val |>.toFinset`. -/
private lemma stepFold_fst_image
    {I_l : Finset (Fin n_A)} (T : ↥I_l → Finset (Fin n_B))
    (h_card : ∀ i : ↥I_l, I_l.card ≤ (T i).card)
    (default : Fin n_B) :
    ∀ (is : List ↥I_l) (M : Finset (Fin n_A × Fin n_B))
      (chosen : Finset (Fin n_B)) (g : ↥I_l → Fin n_B),
      chosen.card + is.length ≤ I_l.card →
      (stepFold T default is M chosen g).1.image Prod.fst =
        M.image Prod.fst ∪ (is.map Subtype.val).toFinset := by
  classical
  intro is
  induction is with
  | nil => intro M chosen g _; simp [stepFold]
  | cons i rest ih =>
    intro M chosen g h_le
    have h_chosen_lt : chosen.card < I_l.card := by
      have : (i :: rest).length = rest.length + 1 := List.length_cons
      omega
    have h_diff_ne := sdiff_ne_under_feas T h_card (i := i) h_chosen_lt
    simp only [stepFold]
    rw [dif_pos h_diff_ne]
    set u := (T i \ chosen).min' h_diff_ne
    have h_u_notin : u ∉ chosen :=
      (Finset.mem_sdiff.mp (Finset.min'_mem _ h_diff_ne)).2
    have h_chosen_le : (insert u chosen).card + rest.length ≤ I_l.card := by
      rw [Finset.card_insert_of_notMem h_u_notin]
      have : (i :: rest).length = rest.length + 1 := List.length_cons
      omega
    rw [ih _ _ _ h_chosen_le, Finset.image_insert]
    ext x
    simp [Finset.mem_union, Finset.mem_insert]

/-- Invariant: stepFold maintains `chosen = M.image Prod.snd ∪ initial_extras`.
For our initial state `M = ∅, chosen = ∅`, this gives `chosen = M.image Prod.snd`. -/
private lemma stepFold_chosen_eq_M_image
    {I_l : Finset (Fin n_A)} (T : ↥I_l → Finset (Fin n_B))
    (default : Fin n_B) :
    ∀ (is : List ↥I_l) (M : Finset (Fin n_A × Fin n_B))
      (chosen : Finset (Fin n_B)) (g : ↥I_l → Fin n_B),
      chosen = M.image Prod.snd →
      (stepFold T default is M chosen g).2.1 =
        (stepFold T default is M chosen g).1.image Prod.snd := by
  classical
  intro is
  induction is with
  | nil => intro M chosen g h_inv; simp [stepFold]; exact h_inv
  | cons i rest ih =>
    intro M chosen g h_inv
    simp only [stepFold]
    by_cases h : (T i \ chosen).Nonempty
    · rw [dif_pos h]
      set u := (T i \ chosen).min' h
      apply ih
      rw [Finset.image_insert, ← h_inv]
    · rw [dif_neg h]
      exact h_inv

/-- The matching from one greedy step has distinct u-coordinates. The key
trick: `final_chosen = M.image Prod.snd` (set equality, started from
empty), so `|M.image Prod.snd| = |final_chosen| = I_l.card = |M|`, hence
`Prod.snd` is injective on `M`. -/
private lemma greedyStep_distinct_u
    (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) (h_feas : feasible I_l T ν₀)
    (ab₁ ab₂ : Fin n_A × Fin n_B)
    (h₁ : ab₁ ∈ (greedyStep I_l T ν₀ default).1)
    (h₂ : ab₂ ∈ (greedyStep I_l T ν₀ default).1)
    (h_ne : ab₁ ≠ ab₂) : ab₁.2 ≠ ab₂.2 := by
  classical
  set M := (greedyStep I_l T ν₀ default).1 with hM_def
  have h_card_M : M.card = I_l.card := greedyStep_matching_card I_l T ν₀ default h_feas
  have h_step_unfold : (greedyStep I_l T ν₀ default).1 =
      (stepFold T default I_l.attach.toList ∅ ∅ (fun _ => default)).1 := by
    unfold greedyStep; rw [dif_pos h_feas]
  set final_chosen := (stepFold T default I_l.attach.toList ∅ ∅
                        (fun _ => default)).2.1 with hfc_def
  have h_card_floor : ∀ i : ↥I_l, I_l.card ≤ (T i).card := fun i =>
    le_trans (le_max_right _ _) (h_feas i)
  have h_len_le : (∅ : Finset (Fin n_B)).card + I_l.attach.toList.length ≤ I_l.card := by
    rw [Finset.card_empty, zero_add, Finset.length_toList, Finset.card_attach]
  have h_chosen_card : final_chosen.card = I_l.card := by
    rw [hfc_def, stepFold_chosen_card T h_card_floor default I_l.attach.toList ∅ ∅
          (fun _ => default) h_len_le]
    rw [Finset.card_empty, zero_add, Finset.length_toList, Finset.card_attach]
  -- final_chosen = M.image Prod.snd (started from empty).
  have h_chosen_eq_img : final_chosen = M.image Prod.snd := by
    rw [hfc_def, hM_def, h_step_unfold]
    apply stepFold_chosen_eq_M_image T default I_l.attach.toList ∅ ∅ (fun _ => default)
    simp
  have h_img_card : (M.image Prod.snd).card = M.card := by
    rw [← h_chosen_eq_img, h_chosen_card, h_card_M]
  -- Therefore Prod.snd is injOn M.
  have h_inj : Set.InjOn Prod.snd (M : Set (Fin n_A × Fin n_B)) :=
    Finset.injOn_of_card_image_eq h_img_card
  exact fun h_eq => h_ne (h_inj h₁ h₂ h_eq)

/-! ## Main lemmas: bipartite induced matching, cardinality, member size

We finally state and prove the three deliverables.
-/

/-- **Main Lemma 3** (size): every matching in `greedyMatchings` has
cardinality exactly `I_l.card`. -/
lemma greedyMatchings_member_card_eq
    (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) :
    ∀ M ∈ greedyMatchings I_l T ν₀ default, M.card = I_l.card := by
  classical
  intro M h_mem
  induction h_total : totalCard I_l T using Nat.strong_induction_on
    generalizing T M with
  | _ n ih =>
    by_cases h_pos : 0 < I_l.card
    · by_cases h_feas : feasible I_l T ν₀
      · rw [greedyMatchings_eq_of_feasible I_l T ν₀ default h_pos h_feas] at h_mem
        rcases Finset.mem_insert.mp h_mem with h_eq | h_in_rest
        · rw [h_eq]; exact greedyStep_matching_card I_l T ν₀ default h_feas
        · have hlt : totalCard I_l (greedyStep I_l T ν₀ default).2.1 < n := by
            rw [← h_total]
            exact totalCard_greedyStep_lt I_l T ν₀ default h_feas h_pos
          exact ih _ hlt _ _ h_in_rest rfl
      · rw [greedyMatchings_eq_empty_of_infeasible I_l T ν₀ default
              (fun _ => h_feas)] at h_mem
        exact absurd h_mem (Finset.notMem_empty _)
    · rw [greedyMatchings_eq_empty_of_infeasible I_l T ν₀ default
            (fun h => absurd h h_pos)] at h_mem
      exact absurd h_mem (Finset.notMem_empty _)


/-- The matching from one greedy step has distinct row-coordinates: each
row `i ∈ I_l` contributes EXACTLY ONE pair, so distinct pairs have
distinct first components. -/
private lemma greedyStep_distinct_a
    (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) (h_feas : feasible I_l T ν₀)
    (ab₁ ab₂ : Fin n_A × Fin n_B)
    (h₁ : ab₁ ∈ (greedyStep I_l T ν₀ default).1)
    (h₂ : ab₂ ∈ (greedyStep I_l T ν₀ default).1)
    (h_ne : ab₁ ≠ ab₂) : ab₁.1 ≠ ab₂.1 := by
  classical
  set M := (greedyStep I_l T ν₀ default).1 with hM_def
  have h_card_M : M.card = I_l.card := greedyStep_matching_card I_l T ν₀ default h_feas
  have h_step_unfold : (greedyStep I_l T ν₀ default).1 =
      (stepFold T default I_l.attach.toList ∅ ∅ (fun _ => default)).1 := by
    unfold greedyStep; rw [dif_pos h_feas]
  have h_card_floor : ∀ i : ↥I_l, I_l.card ≤ (T i).card := fun i =>
    le_trans (le_max_right _ _) (h_feas i)
  have h_len_le : (∅ : Finset (Fin n_B)).card + I_l.attach.toList.length ≤ I_l.card := by
    rw [Finset.card_empty, zero_add, Finset.length_toList, Finset.card_attach]
  -- M.image Prod.fst = (I_l.attach.toList.map Subtype.val).toFinset.
  have h_M_fst_eq : M.image Prod.fst =
      (I_l.attach.toList.map Subtype.val).toFinset := by
    rw [hM_def, h_step_unfold]
    have := stepFold_fst_image T h_card_floor default I_l.attach.toList ∅ ∅
              (fun _ => default) h_len_le
    rw [this]
    simp
  -- This Finset has cardinality I_l.card.
  have h_M_fst_card : (M.image Prod.fst).card = I_l.card := by
    rw [h_M_fst_eq]
    have h_nodup : (I_l.attach.toList.map Subtype.val).Nodup := by
      rw [List.nodup_map_iff_inj_on (Finset.nodup_toList _)]
      intro a _ b _ h_eq
      exact Subtype.ext h_eq
    rw [List.toFinset_card_of_nodup h_nodup, List.length_map, Finset.length_toList,
        Finset.card_attach]
  -- Hence Prod.fst is injOn M.
  have h_card_eq : (M.image Prod.fst).card = M.card := by rw [h_M_fst_card, h_card_M]
  have h_inj : Set.InjOn Prod.fst (M : Set (Fin n_A × Fin n_B)) :=
    Finset.injOn_of_card_image_eq h_card_eq
  exact fun h_a_eq => h_ne (h_inj h₁ h₂ h_a_eq)

/-! ## Main headline lemmas -/

/-- **Helper Lemma 1**: every matching in `greedyMatchings I_l T ν₀ default`
satisfies the "pair-mem" property: for every `(a, u) ∈ M`, `a ∈ I_l`
and `u ∈ T ⟨a, h⟩`. This is the invariant that propagates through the
greedy recursion. -/
lemma greedyMatchings_member_pair_mem
    (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) :
    ∀ M ∈ greedyMatchings I_l T ν₀ default,
      ∀ ab ∈ M, ∃ h : ab.1 ∈ I_l, ab.2 ∈ T ⟨ab.1, h⟩ := by
  classical
  intro M h_mem
  induction h_total : totalCard I_l T using Nat.strong_induction_on
    generalizing T M with
  | _ n ih =>
    by_cases h_pos : 0 < I_l.card
    · by_cases h_feas : feasible I_l T ν₀
      · rw [greedyMatchings_eq_of_feasible I_l T ν₀ default h_pos h_feas] at h_mem
        rcases Finset.mem_insert.mp h_mem with h_eq | h_in_rest
        · rw [h_eq]; exact greedyStep_pair_mem I_l T ν₀ default h_feas
        · have hlt : totalCard I_l (greedyStep I_l T ν₀ default).2.1 < n := by
            rw [← h_total]
            exact totalCard_greedyStep_lt I_l T ν₀ default h_feas h_pos
          intro ab h_ab
          -- Apply ih to the recursive call.
          have h_rec := ih _ hlt (greedyStep I_l T ν₀ default).2.1 M h_in_rest rfl ab h_ab
          obtain ⟨h_a, h_u⟩ := h_rec
          -- h_u : ab.2 ∈ T' ⟨ab.1, h_a⟩ where T' i = (T i).erase (g i)
          refine ⟨h_a, ?_⟩
          -- Unfold T' = (T i).erase (g i) and use erase ⊆ T.
          have h_unfold : (greedyStep I_l T ν₀ default).2.1 ⟨ab.1, h_a⟩ =
              (T ⟨ab.1, h_a⟩).erase
                ((stepFold T default I_l.attach.toList ∅ ∅ (fun _ => default)).2.2
                  ⟨ab.1, h_a⟩) := by
            unfold greedyStep; rw [dif_pos h_feas]
          rw [h_unfold] at h_u
          exact Finset.mem_of_mem_erase h_u
      · rw [greedyMatchings_eq_empty_of_infeasible I_l T ν₀ default
              (fun _ => h_feas)] at h_mem
        exact absurd h_mem (Finset.notMem_empty _)
    · rw [greedyMatchings_eq_empty_of_infeasible I_l T ν₀ default
            (fun h => absurd h h_pos)] at h_mem
      exact absurd h_mem (Finset.notMem_empty _)

/-- **Helper Lemma 2**: every matching in `greedyMatchings` has distinct
first-coordinates (different `a`'s) and distinct second-coordinates
(different `u`'s) between distinct pairs. -/
lemma greedyMatchings_member_distinct
    (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) :
    ∀ M ∈ greedyMatchings I_l T ν₀ default,
      ∀ ab₁ ∈ M, ∀ ab₂ ∈ M, ab₁ ≠ ab₂ → ab₁.1 ≠ ab₂.1 ∧ ab₁.2 ≠ ab₂.2 := by
  classical
  intro M h_mem
  induction h_total : totalCard I_l T using Nat.strong_induction_on
    generalizing T M with
  | _ n ih =>
    by_cases h_pos : 0 < I_l.card
    · by_cases h_feas : feasible I_l T ν₀
      · rw [greedyMatchings_eq_of_feasible I_l T ν₀ default h_pos h_feas] at h_mem
        rcases Finset.mem_insert.mp h_mem with h_eq | h_in_rest
        · rw [h_eq]
          intro ab₁ h₁ ab₂ h₂ h_ne
          exact ⟨greedyStep_distinct_a I_l T ν₀ default h_feas ab₁ ab₂ h₁ h₂ h_ne,
                 greedyStep_distinct_u I_l T ν₀ default h_feas ab₁ ab₂ h₁ h₂ h_ne⟩
        · have hlt : totalCard I_l (greedyStep I_l T ν₀ default).2.1 < n := by
            rw [← h_total]
            exact totalCard_greedyStep_lt I_l T ν₀ default h_feas h_pos
          exact ih _ hlt (greedyStep I_l T ν₀ default).2.1 M h_in_rest rfl
      · rw [greedyMatchings_eq_empty_of_infeasible I_l T ν₀ default
              (fun _ => h_feas)] at h_mem
        exact absurd h_mem (Finset.notMem_empty _)
    · rw [greedyMatchings_eq_empty_of_infeasible I_l T ν₀ default
            (fun h => absurd h h_pos)] at h_mem
      exact absurd h_mem (Finset.notMem_empty _)

/-- **Main Lemma 1** (bipartite induced matching): every matching in
`greedyMatchings I_l T ν₀ default` is a bipartite induced matching, when
`T = fun ⟨a, _⟩ => keptSet G family t slot_at I_l a σ`.

The proof uses the validSlots-structure of `keptSet`: for every
`u ∈ keptSet G family t slot_at I_l a σ`, we have
`I_l ∈ validSlots G family a u`, which means no `a' ∈ I_l ∖ {a}` is
adjacent to `u`. This automatically gives the "no bridge" condition. -/
lemma greedyMatchings_member_isBipartiteInducedMatching
    {G : SimpleGraph (Fin n_A ⊕ Fin n_B)} [DecidableRel G.Adj]
    (family : Finset (Finset (Fin n_A))) (t : ℕ)
    (slot_at : Fin t → Finset (Fin n_A))
    (I_l : Finset (Fin n_A)) (_h_mem_I : I_l ∈ family)
    (σ : Fin n_A × Fin n_B → Fin t)
    (ν₀ : ℕ) (default : Fin n_B) :
    let T : ↥I_l → Finset (Fin n_B) :=
      fun ⟨a, _⟩ => DaveyThesis2024.SecRandomBipartite.SlotAssignment.keptSet
                      G family t slot_at I_l a σ
    ∀ M ∈ greedyMatchings I_l T ν₀ default, IsBipartiteInducedMatching G M := by
  classical
  intro T M h_mem
  intro ab₁ h₁ ab₂ h₂ h_ne
  -- Use the two helper lemmas.
  have h_pair₁ := greedyMatchings_member_pair_mem I_l T ν₀ default M h_mem ab₁ h₁
  have h_pair₂ := greedyMatchings_member_pair_mem I_l T ν₀ default M h_mem ab₂ h₂
  obtain ⟨h_a₁, h_u₁_in_T⟩ := h_pair₁
  obtain ⟨h_a₂, h_u₂_in_T⟩ := h_pair₂
  obtain ⟨h_a_ne, h_u_ne⟩ :=
    greedyMatchings_member_distinct I_l T ν₀ default M h_mem ab₁ h₁ ab₂ h₂ h_ne
  -- Extract validSlots conditions from keptSet membership.
  have h_kept₁ : ab₁.2 ∈ DaveyThesis2024.SecRandomBipartite.SlotAssignment.keptSet
                  G family t slot_at I_l ab₁.1 σ := h_u₁_in_T
  have h_kept₂ : ab₂.2 ∈ DaveyThesis2024.SecRandomBipartite.SlotAssignment.keptSet
                  G family t slot_at I_l ab₂.1 σ := h_u₂_in_T
  rw [DaveyThesis2024.SecRandomBipartite.SlotAssignment.mem_keptSet] at h_kept₁ h_kept₂
  obtain ⟨_, h_valid₁, _⟩ := h_kept₁
  obtain ⟨_, h_valid₂, _⟩ := h_kept₂
  rw [DaveyThesis2024.SecRandomBipartite.mem_validSlots] at h_valid₁ h_valid₂
  obtain ⟨_, _, h_not_adj₂⟩ := h_valid₂
  obtain ⟨_, _, h_not_adj₁⟩ := h_valid₁
  exact ⟨h_a_ne, h_u_ne,
         h_not_adj₂ ab₁.1 h_a₁ h_a_ne,
         h_not_adj₁ ab₂.1 h_a₂ h_a_ne.symm⟩

/-- **Main Lemma 2** (cardinality bound — minimal form):
`greedyMatchings` is nonempty whenever `feasible I_l T ν₀` holds.

This gives the weakest useful bound. The stronger bound
`(ν - max ν₀ I_l.card)` matchings would require a per-iteration
"freshness" lemma showing each `greedyStep` output differs from all
previous, which is provable but tedious; we defer it as it isn't needed
for the F.7.4.D union-of-slots construction (Bonferroni absorbs the
factor). The qualitative `≥ 1` bound suffices to certify that
greedyMatchings is nonempty under feasibility. -/
lemma greedyMatchings_card_pos_of_feasible
    (I_l : Finset (Fin n_A)) (h_pos : 0 < I_l.card)
    (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B)
    (h_feas : feasible I_l T ν₀) :
    0 < (greedyMatchings I_l T ν₀ default).card := by
  classical
  rw [greedyMatchings_eq_of_feasible I_l T ν₀ default h_pos h_feas]
  rw [Finset.card_pos]
  exact ⟨(greedyStep I_l T ν₀ default).1, Finset.mem_insert_self _ _⟩

/-- Same statement framed via a common floor `ν ≥ max ν₀ I_l.card`: when
all rows have at least `max ν₀ I_l.card` elements, the greedy yields at
least one matching. -/
lemma greedyMatchings_card_pos
    (I_l : Finset (Fin n_A)) (h_pos : 0 < I_l.card)
    (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B)
    (ν : ℕ) (h_floor : ∀ i, ν ≤ (T i).card) (h_ν_ge : max ν₀ I_l.card ≤ ν) :
    0 < (greedyMatchings I_l T ν₀ default).card := by
  classical
  refine greedyMatchings_card_pos_of_feasible I_l h_pos T ν₀ default ?_
  intro i; exact h_ν_ge.trans (h_floor i)

/-! ## Strengthened cardinality bound — `greedyMatchings.card ≥ min - max ν₀ k`

We now strengthen the qualitative `≥ 1` bound to the quantitative
`≥ min_i (T i).card - max ν₀ I_l.card` form. The key observation is
that **each feasible greedy step decreases every `(T i).card` by exactly
one** (since `g i ∈ T i` by `stepFold_g_mem`, so erasing `g i` drops the
card by 1). The recursion therefore produces one matching per iteration
until feasibility fails, which happens after exactly
`min_i (T i).card - max ν₀ I_l.card` iterations.
-/

/-- Each row's card drops by exactly one after one feasible greedy step:
`((T' i).card + 1 = (T i).card)`. Stated additively to avoid issues
when `(T i).card = 0` (the feasibility hypothesis rules that out
whenever `0 < I_l.card`, but the additive form is robust regardless). -/
private lemma greedyStep_T_card_succ
    (I_l : Finset (Fin n_A)) (_h_pos : 0 < I_l.card)
    (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) (h_feas : feasible I_l T ν₀) (i : ↥I_l) :
    ((greedyStep I_l T ν₀ default).2.1 i).card + 1 = (T i).card := by
  classical
  unfold greedyStep
  rw [dif_pos h_feas]
  simp only
  have h_card_floor : ∀ j : ↥I_l, I_l.card ≤ (T j).card := fun j =>
    le_trans (le_max_right _ _) (h_feas j)
  have h_len_le : (∅ : Finset (Fin n_B)).card + I_l.attach.toList.length ≤ I_l.card := by
    rw [Finset.card_empty, zero_add, Finset.length_toList, Finset.card_attach]
  have h_nodup : I_l.attach.toList.Nodup := Finset.nodup_toList _
  have h_i_in_list : i ∈ I_l.attach.toList :=
    Finset.mem_toList.mpr (Finset.mem_attach _ _)
  have h_g_mem : (stepFold T default I_l.attach.toList ∅ ∅
                    (fun _ => default)).2.2 i ∈ T i :=
    stepFold_g_mem T h_card_floor default I_l.attach.toList ∅ (fun _ => default) ∅
      h_len_le h_nodup i h_i_in_list
  exact Finset.card_erase_add_one h_g_mem

/-- After one feasible greedy step, the min row-card decreases by exactly one. -/
private lemma greedyStep_min_card_succ
    (I_l : Finset (Fin n_A)) (h_pos : 0 < I_l.card)
    (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) (h_feas : feasible I_l T ν₀) :
    haveI : Nonempty ↥I_l := Finset.card_pos.mp h_pos |>.to_subtype
    ((Finset.univ : Finset ↥I_l).inf'
        (Finset.univ_nonempty (α := ↥I_l)) (fun i => (T i).card)) =
      ((Finset.univ : Finset ↥I_l).inf'
        (Finset.univ_nonempty (α := ↥I_l))
        (fun i => ((greedyStep I_l T ν₀ default).2.1 i).card)) + 1 := by
  classical
  haveI : Nonempty ↥I_l := Finset.card_pos.mp h_pos |>.to_subtype
  -- Both inf's are nat-min over the same nonempty Finset; the row-cards differ by +1.
  apply le_antisymm
  · -- LHS ≤ RHS: pick i achieving min on the right, then (T i).card = (T' i).card + 1.
    obtain ⟨i₀, _, h_i₀_min⟩ := Finset.exists_mem_eq_inf'
      (Finset.univ_nonempty (α := ↥I_l))
      (fun i => ((greedyStep I_l T ν₀ default).2.1 i).card)
    rw [h_i₀_min]
    have h_succ := greedyStep_T_card_succ I_l h_pos T ν₀ default h_feas i₀
    -- inf' (T·.card) ≤ (T i₀).card = (T' i₀).card + 1.
    calc (Finset.univ : Finset ↥I_l).inf'
            (Finset.univ_nonempty (α := ↥I_l)) (fun i => (T i).card)
        ≤ (T i₀).card := Finset.inf'_le _ (Finset.mem_univ i₀)
      _ = ((greedyStep I_l T ν₀ default).2.1 i₀).card + 1 := h_succ.symm
  · -- RHS ≤ LHS: pick i achieving min on the left, get (T' i).card + 1 = (T i).card.
    obtain ⟨i₀, _, h_i₀_min⟩ := Finset.exists_mem_eq_inf'
      (Finset.univ_nonempty (α := ↥I_l)) (fun i => (T i).card)
    rw [h_i₀_min]
    have h_succ := greedyStep_T_card_succ I_l h_pos T ν₀ default h_feas i₀
    -- inf' (T'·.card) + 1 ≤ (T' i₀).card + 1 = (T i₀).card.
    have h_inf_le : (Finset.univ : Finset ↥I_l).inf'
            (Finset.univ_nonempty (α := ↥I_l))
            (fun i => ((greedyStep I_l T ν₀ default).2.1 i).card)
          ≤ ((greedyStep I_l T ν₀ default).2.1 i₀).card :=
      Finset.inf'_le _ (Finset.mem_univ i₀)
    omega

/-! ### Disjointness of consecutive greedy matchings

The key technical lemma: `greedyStep.1 ∉ greedyMatchings I_l (greedyStep T)'2.1 ν₀ default`.

**Key idea**: For each pair `(a, u) ∈ greedyStep T·.1`, we have
`u = g ⟨a, _⟩` where `g` is the picks-function from the underlying
`stepFold`. This is because stepFold processes each row exactly once
(I_l.attach.toList is nodup), recording the pick into both the matching
and the g-function. By Prod.fst-injectivity on M, the row-i pair is
uniquely `(i.val, g i)`.

Meanwhile, any `(a', u') ∈ M'` with `M' ∈ greedyMatchings I_l T' ν₀ default`
satisfies `u' ∈ T' ⟨a', _⟩ = (T ⟨a', _⟩).erase (g ⟨a', _⟩)`, so
`u' ≠ g ⟨a', _⟩`.

If `M = M'`, pick any pair `(a, u) ∈ M`: `u = g ⟨a, _⟩` (from M) and
`u ≠ g ⟨a, _⟩` (from M'), contradiction.

Implementation: we prove the stepFold-level invariant
`(a, u) ∈ stepFold.1 → (a, u) ∈ M_init ∨ ∃ i ∈ is, a = i.val ∧ u = (stepFold).2.2 i`
by induction on the list `is`. -/

/-- Pair-shape invariant of `stepFold`: every pair in the output matching
either came from the input `M`, or has the form `(i.val, g_final i)` for
some `i ∈ is`, where `g_final` is the final g function. -/
private lemma stepFold_pair_is_row_pick
    {I_l : Finset (Fin n_A)} (T : ↥I_l → Finset (Fin n_B))
    (h_card : ∀ i : ↥I_l, I_l.card ≤ (T i).card)
    (default : Fin n_B) :
    ∀ (is : List ↥I_l) (M : Finset (Fin n_A × Fin n_B))
      (chosen : Finset (Fin n_B)) (g : ↥I_l → Fin n_B),
      chosen.card + is.length ≤ I_l.card →
      is.Nodup →
      ∀ ab ∈ (stepFold T default is M chosen g).1,
        ab ∈ M ∨ ∃ i ∈ is,
          ab.1 = (i : Fin n_A) ∧ ab.2 = (stepFold T default is M chosen g).2.2 i := by
  classical
  intro is
  induction is with
  | nil =>
    intro M chosen g _ _ ab h_ab
    left; simpa [stepFold] using h_ab
  | cons i₀ rest ih =>
    intro M chosen g h_le h_nodup ab h_ab
    have h_chosen_lt : chosen.card < I_l.card := by
      have : (i₀ :: rest).length = rest.length + 1 := List.length_cons
      omega
    have h_diff_ne := sdiff_ne_under_feas T h_card (i := i₀) h_chosen_lt
    have h_nodup_rest : rest.Nodup := (List.nodup_cons.mp h_nodup).2
    have h_i₀_notin_rest : ¬ i₀ ∈ rest := (List.nodup_cons.mp h_nodup).1
    set u₀ := (T i₀ \ chosen).min' h_diff_ne with hu₀_def
    have h_u₀_notin : u₀ ∉ chosen :=
      (Finset.mem_sdiff.mp (Finset.min'_mem _ h_diff_ne)).2
    have h_chosen_le : (insert u₀ chosen).card + rest.length ≤ I_l.card := by
      rw [Finset.card_insert_of_notMem h_u₀_notin]
      have : (i₀ :: rest).length = rest.length + 1 := List.length_cons
      omega
    -- Unfold stepFold (i₀ :: rest).
    have h_step_unfold : stepFold T default (i₀ :: rest) M chosen g =
        stepFold T default rest (insert ((i₀ : Fin n_A), u₀) M)
          (insert u₀ chosen) (Function.update g i₀ u₀) := by
      simp only [stepFold]
      rw [dif_pos h_diff_ne]
    rw [h_step_unfold] at h_ab
    -- Apply ih to the recursive call.
    have h_ih := ih (insert ((i₀ : Fin n_A), u₀) M) (insert u₀ chosen)
                  (Function.update g i₀ u₀) h_chosen_le h_nodup_rest ab h_ab
    -- h_ih: ab ∈ insert (i₀.val, u₀) M ∨ ∃ i ∈ rest, fitting "row-i pick" form.
    -- The g-final of the outer = g-final of the inner. Need to push through.
    rw [h_step_unfold]
    rcases h_ih with h_orig | ⟨i, h_i_in_rest, h_a, h_u⟩
    · rcases Finset.mem_insert.mp h_orig with h_eq | h_in_M
      · right
        refine ⟨i₀, List.mem_cons_self, ?_⟩
        constructor
        · rw [h_eq]
        · rw [h_eq]
          -- ab.2 = u₀. Need: u₀ = (stepFold rest ... (Function.update g i₀ u₀)).2.2 i₀.
          -- Since i₀ ∉ rest, stepFold preserves g i₀ = u₀ (from the update).
          have h_preserve := stepFold_g_preserve T default i₀ rest
                              (insert ((i₀ : Fin n_A), u₀) M) (insert u₀ chosen)
                              (Function.update g i₀ u₀) h_i₀_notin_rest
          rw [h_preserve]
          simp [Function.update]
      · left; exact h_in_M
    · right
      refine ⟨i, List.mem_cons_of_mem _ h_i_in_rest, h_a, h_u⟩

/-- Specialization: for `M := (greedyStep I_l T ν₀ default).1`, every pair
`(a, u) ∈ M` has `u = g ⟨a, _⟩` where `g` is the stepFold's g-function. -/
private lemma greedyStep_pair_is_g
    (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) (h_feas : feasible I_l T ν₀)
    (ab : Fin n_A × Fin n_B) (h_ab : ab ∈ (greedyStep I_l T ν₀ default).1) :
    ∃ (h_a : ab.1 ∈ I_l),
      ab.2 = (stepFold T default I_l.attach.toList ∅ ∅
              (fun _ => default)).2.2 ⟨ab.1, h_a⟩ := by
  classical
  have h_card_floor : ∀ j : ↥I_l, I_l.card ≤ (T j).card := fun j =>
    le_trans (le_max_right _ _) (h_feas j)
  have h_step_unfold : (greedyStep I_l T ν₀ default).1 =
      (stepFold T default I_l.attach.toList ∅ ∅ (fun _ => default)).1 := by
    unfold greedyStep; rw [dif_pos h_feas]
  rw [h_step_unfold] at h_ab
  have h_len_le : (∅ : Finset (Fin n_B)).card + I_l.attach.toList.length ≤ I_l.card := by
    rw [Finset.card_empty, zero_add, Finset.length_toList, Finset.card_attach]
  have h_nodup : I_l.attach.toList.Nodup := Finset.nodup_toList _
  have h := stepFold_pair_is_row_pick T h_card_floor default I_l.attach.toList ∅ ∅
              (fun _ => default) h_len_le h_nodup ab h_ab
  rcases h with h_empty | ⟨i, _, h_a, h_u⟩
  · exact absurd h_empty (Finset.notMem_empty _)
  · refine ⟨h_a ▸ i.2, ?_⟩
    -- ab.2 = (stepFold ...).2.2 i, and ⟨ab.1, ...⟩ = i (since ab.1 = i.val).
    have h_eq : (⟨ab.1, h_a ▸ i.2⟩ : ↥I_l) = i := Subtype.ext h_a
    rw [h_eq]
    exact h_u

/-- The greedy-step matching `M = greedyStep.1` is **not** in the
recursive greedy output `greedyMatchings I_l T' ν₀ default`.

**Proof**: pick any pair `(a, u) ∈ M` (exists since `|M| = I_l.card > 0`).
By `greedyStep_pair_is_g`: `u = g ⟨a, _⟩`. If `M ∈ recursion`, then
applying `greedyMatchings_member_pair_mem` to `T'` gives
`u ∈ T' ⟨a, _⟩ = (T ⟨a, _⟩).erase (g ⟨a, _⟩)`, so `u ≠ g ⟨a, _⟩`,
contradicting `u = g ⟨a, _⟩`. -/
private lemma greedyStep_M_notMem_recursion
    (I_l : Finset (Fin n_A)) (h_pos : 0 < I_l.card)
    (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) (h_feas : feasible I_l T ν₀) :
    (greedyStep I_l T ν₀ default).1 ∉
      greedyMatchings I_l (greedyStep I_l T ν₀ default).2.1 ν₀ default := by
  classical
  intro h_M_in_rec
  -- M is nonempty (size = I_l.card > 0).
  have h_card_M : (greedyStep I_l T ν₀ default).1.card = I_l.card :=
    greedyStep_matching_card I_l T ν₀ default h_feas
  have h_M_nonempty : (greedyStep I_l T ν₀ default).1.Nonempty := by
    rw [← Finset.card_pos, h_card_M]; exact h_pos
  obtain ⟨ab, h_ab⟩ := h_M_nonempty
  -- Get u = g ⟨a, _⟩.
  obtain ⟨h_a, h_u_eq_g⟩ := greedyStep_pair_is_g I_l T ν₀ default h_feas ab h_ab
  -- M ∈ recursion → ab ∈ M' (= M, by h_M_in_rec) → ab.2 ∈ T' ⟨ab.1, h_a⟩.
  have h_pair_in_rec := greedyMatchings_member_pair_mem I_l
                          (greedyStep I_l T ν₀ default).2.1 ν₀ default
                          (greedyStep I_l T ν₀ default).1 h_M_in_rec ab h_ab
  obtain ⟨h_a', h_u_in_T'⟩ := h_pair_in_rec
  -- T' ⟨ab.1, h_a'⟩ = (T ⟨ab.1, h_a'⟩).erase (g ⟨ab.1, h_a'⟩).
  have hT' : (greedyStep I_l T ν₀ default).2.1 ⟨ab.1, h_a'⟩ =
      (T ⟨ab.1, h_a'⟩).erase
        ((stepFold T default I_l.attach.toList ∅ ∅ (fun _ => default)).2.2
          ⟨ab.1, h_a'⟩) := by
    unfold greedyStep; rw [dif_pos h_feas]
  rw [hT'] at h_u_in_T'
  -- ab.2 ∈ erase, so ab.2 ≠ g ⟨ab.1, h_a'⟩. But h_u_eq_g says ab.2 = g ⟨ab.1, h_a⟩.
  -- Use Subtype.ext to identify ⟨ab.1, h_a⟩ = ⟨ab.1, h_a'⟩.
  have h_subtype_eq : (⟨ab.1, h_a⟩ : ↥I_l) = ⟨ab.1, h_a'⟩ := Subtype.ext rfl
  rw [h_subtype_eq] at h_u_eq_g
  exact (Finset.mem_erase.mp h_u_in_T').1 h_u_eq_g

/-- **R1 (γ.E sub-lemma): edge-disjointness across iterations**.
The greedy-step matching `M = greedyStep.1` is edge-disjoint from every
matching `M'` produced by the recursive call
`greedyMatchings I_l T' ν₀ default` (where `T' i = (T i).erase (g i)`).

**Proof**: pick any pair `(a, u) ∈ M`. By `greedyStep_pair_is_g`,
`u = g ⟨a, _⟩`. If `(a, u) ∈ M'` for some `M'` in the recursion, then
by `greedyMatchings_member_pair_mem` applied to `T'`,
`u ∈ T' ⟨a, _⟩ = (T ⟨a, _⟩).erase (g ⟨a, _⟩)`, hence `u ≠ g ⟨a, _⟩`,
contradicting `u = g ⟨a, _⟩`.

This strengthens `greedyStep_M_notMem_recursion` (which only proves
set-distinctness `M ≠ M'`) to genuine edge-disjointness
`Disjoint M M'`. -/
private lemma greedyStep_M_disjoint_recursion
    (I_l : Finset (Fin n_A))
    (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) (h_feas : feasible I_l T ν₀) :
    ∀ M' ∈ greedyMatchings I_l (greedyStep I_l T ν₀ default).2.1 ν₀ default,
      Disjoint (greedyStep I_l T ν₀ default).1 M' := by
  classical
  intro M' h_M'_in_rec
  rw [Finset.disjoint_left]
  intro ab h_ab_in_step h_ab_in_M'
  -- By greedyStep_pair_is_g: ab.2 = g ⟨ab.1, h_a⟩.
  obtain ⟨h_a, h_u_eq_g⟩ :=
    greedyStep_pair_is_g I_l T ν₀ default h_feas ab h_ab_in_step
  -- By greedyMatchings_member_pair_mem on T': ab.2 ∈ T' ⟨ab.1, h_a'⟩.
  have h_pair_in_rec :=
    greedyMatchings_member_pair_mem I_l (greedyStep I_l T ν₀ default).2.1 ν₀ default
      M' h_M'_in_rec ab h_ab_in_M'
  obtain ⟨h_a', h_u_in_T'⟩ := h_pair_in_rec
  -- T' ⟨ab.1, h_a'⟩ = (T ⟨ab.1, h_a'⟩).erase (g ⟨ab.1, h_a'⟩).
  have hT' : (greedyStep I_l T ν₀ default).2.1 ⟨ab.1, h_a'⟩ =
      (T ⟨ab.1, h_a'⟩).erase
        ((stepFold T default I_l.attach.toList ∅ ∅ (fun _ => default)).2.2
          ⟨ab.1, h_a'⟩) := by
    unfold greedyStep; rw [dif_pos h_feas]
  rw [hT'] at h_u_in_T'
  -- Identify ⟨ab.1, h_a⟩ = ⟨ab.1, h_a'⟩ via Subtype.ext.
  have h_subtype_eq : (⟨ab.1, h_a⟩ : ↥I_l) = ⟨ab.1, h_a'⟩ := Subtype.ext rfl
  rw [h_subtype_eq] at h_u_eq_g
  exact (Finset.mem_erase.mp h_u_in_T').1 h_u_eq_g

/-- **Strong cardinality bound (raw form)**: when every row has at least
`max ν₀ I_l.card` elements (i.e., feasibility holds at the floor
`max ν₀ I_l.card`), the greedy produces at least
`min_i (T i).card - max ν₀ I_l.card` matchings.

The proof inducts on `totalCard`. Each feasible step decreases the min
by 1 (via `greedyStep_min_card_succ`) and adds 1 matching that is
**not** in the recursion (via `greedyStep_M_notMem_recursion`), so the
total grows by exactly 1. -/
lemma greedyMatchings_card_ge_min_sub_max
    (I_l : Finset (Fin n_A)) (h_pos : 0 < I_l.card)
    (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) :
    haveI : Nonempty ↥I_l := Finset.card_pos.mp h_pos |>.to_subtype
    ((Finset.univ : Finset ↥I_l).inf'
        (Finset.univ_nonempty (α := ↥I_l)) (fun i => (T i).card))
      - max ν₀ I_l.card ≤ (greedyMatchings I_l T ν₀ default).card := by
  classical
  haveI : Nonempty ↥I_l := Finset.card_pos.mp h_pos |>.to_subtype
  -- Strong induction on totalCard.
  induction h_total : totalCard I_l T using Nat.strong_induction_on
    generalizing T with
  | _ n ih =>
    by_cases h_feas : feasible I_l T ν₀
    · -- Feasible: unfold greedyMatchings, get one matching + recursive.
      rw [greedyMatchings_eq_of_feasible I_l T ν₀ default h_pos h_feas]
      have h_M_notin :
          (greedyStep I_l T ν₀ default).1 ∉
            greedyMatchings I_l (greedyStep I_l T ν₀ default).2.1 ν₀ default :=
        greedyStep_M_notMem_recursion I_l h_pos T ν₀ default h_feas
      rw [Finset.card_insert_of_notMem h_M_notin]
      -- IH on smaller totalCard.
      have h_totalCard_lt :
          totalCard I_l (greedyStep I_l T ν₀ default).2.1 < n := by
        rw [← h_total]
        exact totalCard_greedyStep_lt I_l T ν₀ default h_feas h_pos
      have h_ih := ih (totalCard I_l (greedyStep I_l T ν₀ default).2.1)
                      h_totalCard_lt (greedyStep I_l T ν₀ default).2.1 rfl
      -- Min decreases by exactly 1.
      have h_min_succ := greedyStep_min_card_succ I_l h_pos T ν₀ default h_feas
      -- h_min_succ : inf' T·.card = inf' T'·.card + 1.
      -- h_ih       : inf' T'·.card - max ν₀ I_l.card ≤ recursion.card.
      -- Goal: inf' T·.card - max ν₀ I_l.card ≤ recursion.card + 1.
      omega
    · -- Infeasible: greedyMatchings = ∅. Need to show LHS ≤ 0, i.e., min ≤ max ν₀ I_l.card.
      rw [greedyMatchings_eq_empty_of_infeasible I_l T ν₀ default (fun _ => h_feas)]
      simp only [Finset.card_empty]
      -- Infeasibility: ∃ i, (T i).card < max ν₀ I_l.card.
      have h_not_all : ¬ ∀ i : ↥I_l, max ν₀ I_l.card ≤ (T i).card := h_feas
      push_neg at h_not_all
      obtain ⟨i, h_i_lt⟩ := h_not_all
      have h_inf_le : (Finset.univ : Finset ↥I_l).inf'
              (Finset.univ_nonempty (α := ↥I_l)) (fun i => (T i).card) ≤ (T i).card :=
        Finset.inf'_le _ (Finset.mem_univ i)
      omega

/-- **Strong cardinality bound (user-friendly form)**: matches the
F.7.4.D specification. When `ν₀ + I_l.card ≤ (T i).card` for all `i`
(so `I_l.card ≤ (T i).card - ν₀`, in particular `I_l.card ≤ ν₀` is NOT
required: the LHS `min - ν₀` is bounded by `greedy.card` because
`min ≥ ν₀ + I_l.card ≥ max ν₀ I_l.card`, with the slack going into the
`I_l.card` term).

Wait — actually the raw bound gives `greedy.card ≥ min - max(ν₀, I_l.card)`.
When `I_l.card ≤ ν₀`, max = ν₀, so we get `min - ν₀` directly. When
`I_l.card > ν₀`, we only get `min - I_l.card`, which is `≤ min - ν₀`.
So an additional hypothesis `I_l.card ≤ ν₀` is required for the
`min - ν₀` form. We include this hypothesis explicitly. -/
theorem greedyMatchings_card_ge_strong
    (I_l : Finset (Fin n_A)) (h_I_l_nonempty : I_l.Nonempty)
    (T : ↥I_l → Finset (Fin n_B)) (ν₀ : ℕ)
    (h_k_le_ν₀ : I_l.card ≤ ν₀)
    (default : Fin n_B) :
    haveI : Nonempty ↥I_l := ⟨⟨h_I_l_nonempty.choose, h_I_l_nonempty.choose_spec⟩⟩
    ((Finset.univ : Finset ↥I_l).inf'
        (Finset.univ_nonempty (α := ↥I_l)) (fun i => (T i).card)) - ν₀
      ≤ (greedyMatchings I_l T ν₀ default).card := by
  classical
  haveI : Nonempty ↥I_l := ⟨⟨h_I_l_nonempty.choose, h_I_l_nonempty.choose_spec⟩⟩
  have h_pos : 0 < I_l.card := Finset.card_pos.mpr h_I_l_nonempty
  have h_max : max ν₀ I_l.card = ν₀ := max_eq_left h_k_le_ν₀
  have h_raw := greedyMatchings_card_ge_min_sub_max I_l h_pos T ν₀ default
  rw [h_max] at h_raw
  exact h_raw

/-- **γ.E — pairwise edge-disjointness of greedy matchings** (Wake 2).
The matchings produced by `greedyMatchings I_l T ν₀ default` are
pairwise edge-disjoint: for distinct `M, M'` in the output, `M ∩ M' = ∅`.

**Proof**: strong induction on `totalCard I_l T`. At the feasible unfold step
`greedyMatchings = insert greedyStep.1 (recursion on T')`:
* both elements equal `greedyStep.1` ⟹ ruled out by `h_ne`;
* both in recursion ⟹ IH on smaller totalCard;
* one is `greedyStep.1`, other in recursion ⟹ apply R1
  `greedyStep_M_disjoint_recursion`.

In the infeasible case `greedyMatchings = ∅` and the pairwise property is
vacuous. -/
lemma greedyMatchings_pairwise_disjoint
    (I_l : Finset (Fin n_A)) (T : ↥I_l → Finset (Fin n_B))
    (ν₀ : ℕ) (default : Fin n_B) :
    ((greedyMatchings I_l T ν₀ default :
        Finset (Finset (Fin n_A × Fin n_B))) :
      Set (Finset (Fin n_A × Fin n_B))).PairwiseDisjoint id := by
  classical
  induction h_total : totalCard I_l T using Nat.strong_induction_on
    generalizing T with
  | _ n ih =>
    by_cases h_pos : 0 < I_l.card
    · by_cases h_feas : feasible I_l T ν₀
      · rw [greedyMatchings_eq_of_feasible I_l T ν₀ default h_pos h_feas]
        -- IH on recursion.
        have hlt : totalCard I_l (greedyStep I_l T ν₀ default).2.1 < n := by
          rw [← h_total]
          exact totalCard_greedyStep_lt I_l T ν₀ default h_feas h_pos
        have h_ih :=
          ih (totalCard I_l (greedyStep I_l T ν₀ default).2.1) hlt
             (greedyStep I_l T ν₀ default).2.1 rfl
        -- M_step is edge-disjoint from every M' in recursion.
        have h_M_disj :
            ∀ M' ∈ greedyMatchings I_l (greedyStep I_l T ν₀ default).2.1 ν₀ default,
              Disjoint (greedyStep I_l T ν₀ default).1 M' :=
          greedyStep_M_disjoint_recursion I_l T ν₀ default h_feas
        -- Apply PairwiseDisjoint on `insert`.
        intro M₁ h₁ M₂ h₂ h_ne
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at h₁ h₂
        rcases h₁ with h₁_eq | h₁_in
        · rcases h₂ with h₂_eq | h₂_in
          · -- both equal: contradicts h_ne.
            exact absurd (h₁_eq.trans h₂_eq.symm) h_ne
          · -- M₁ = greedyStep.1, M₂ ∈ recursion. Apply h_M_disj.
            subst h₁_eq
            exact h_M_disj M₂ h₂_in
        · rcases h₂ with h₂_eq | h₂_in
          · subst h₂_eq
            exact (h_M_disj M₁ h₁_in).symm
          · -- both in recursion: apply IH.
            exact h_ih h₁_in h₂_in h_ne
      · rw [greedyMatchings_eq_empty_of_infeasible I_l T ν₀ default
              (fun _ => h_feas)]
        simp
    · rw [greedyMatchings_eq_empty_of_infeasible I_l T ν₀ default
            (fun h => absurd h h_pos)]
      simp

end DaveyThesis2024.SecRandomBipartite.GreedyTransversal

-- Sanity check: axioms used by the headline lemmas.
section AxiomCheck
open DaveyThesis2024.SecRandomBipartite.GreedyTransversal
/--
info: 'DaveyThesis2024.SecRandomBipartite.GreedyTransversal.greedyMatchings_member_isBipartiteInducedMatching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms greedyMatchings_member_isBipartiteInducedMatching
/--
info: 'DaveyThesis2024.SecRandomBipartite.GreedyTransversal.greedyMatchings_member_card_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms greedyMatchings_member_card_eq
/--
info: 'DaveyThesis2024.SecRandomBipartite.GreedyTransversal.greedyMatchings_card_pos_of_feasible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms greedyMatchings_card_pos_of_feasible
/--
info: 'DaveyThesis2024.SecRandomBipartite.GreedyTransversal.greedyMatchings_card_ge_strong' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms greedyMatchings_card_ge_strong
/--
info: 'DaveyThesis2024.SecRandomBipartite.GreedyTransversal.greedyMatchings_pairwise_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms greedyMatchings_pairwise_disjoint
end AxiomCheck
