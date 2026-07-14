import DaveyThesis2024.StrongEdgeColouring
import DaveyThesis2024.PentagonConjecture

/-!
# WLOG-regular reduction for the strong chromatic index

This file closes the `strong_chromatic_index_Reg_suffices` axiom
(formerly at `StrongChromaticIndex.lean:417`) as a **theorem**, using
the Molloy–Reed sparse-cover (iterated doubling) construction. The
construction reuses the `doubledFlag` substrate from
`PentagonConjecture.lean` (already proved to preserve `maxDegree` and
strictly increase `minDegree` until regular).

The "new" combinatorial content is `strongChromaticIndex_le_doubledFlag`:
the strong chromatic index does not decrease under doubling, because any
strong edge colouring of `doubledFlag G` restricts (along the copy-0
embedding) to a strong edge colouring of `G` using the same colour set.

Mirrors `pentagon_regular_suffices` (`PentagonConjecture.lean:1368`)
structurally.

Phase 3 of the development notes. After this file lands,
project axiom count drops 10 → 9.
-/

namespace Davey2024.Reductions.WLOGRegular

open Davey2024 Finset BigOperators Classical

set_option linter.unusedSectionVars false

noncomputable section

/-! ## §1. Strong-colouring restriction along the copy-0 embedding -/

/-- The copy-0 embedding `G ↪ doubledFlag G` at the `Fin`-index layer.

    Sends `a : Fin G.size` to `⟨a.val, _⟩ : Fin (G.size + G.size)`. -/
def emb0 (G : Flag emptyType) : Fin G.size → Fin (doubledFlag G).size :=
  fun a => ⟨a.val, by
    change a.val < G.size + G.size
    have := a.isLt; omega⟩

lemma emb0_injective (G : Flag emptyType) : Function.Injective (emb0 G) := by
  intro a b h
  exact Fin.ext (by simpa [emb0] using congr_arg Fin.val h)

/-- Adjacency along the copy-0 embedding is iff `G`-adjacency. -/
lemma emb0_adj_iff (G : Flag emptyType) (a b : Fin G.size) (hab : a ≠ b) :
    (doubledFlag G).graph.Adj (emb0 G a) (emb0 G b) ↔ G.graph.Adj a b := by
  change (doubledGraph G).Adj ⟨a.val, _⟩ ⟨b.val, _⟩ ↔ G.graph.Adj a b
  exact doubledGraph_adj_copy0 G a b hab

/-- **Key lemma**: pulling back a strong edge colouring of `doubledFlag G`
    along `emb0` yields a strong edge colouring of `G`. -/
lemma isStrongEdgeColouring_pullback (G : Flag emptyType)
    (c' : Fin (doubledFlag G).size × Fin (doubledFlag G).size → ℕ)
    (hc' : IsStrongEdgeColouring (doubledFlag G).graph c') :
    IsStrongEdgeColouring G.graph
      (fun e : Fin G.size × Fin G.size => c' (emb0 G e.1, emb0 G e.2)) := by
  obtain ⟨hsymm, hstrong⟩ := hc'
  refine ⟨?_, ?_⟩
  · -- Symmetry
    intro u v hadj
    have hne : u ≠ v := G.graph.ne_of_adj hadj
    have hadj' : (doubledFlag G).graph.Adj (emb0 G u) (emb0 G v) :=
      (emb0_adj_iff G u v hne).mpr hadj
    exact hsymm _ _ hadj'
  · -- Strong property
    intro u₁ v₁ u₂ v₂ h₁ h₂ hne hne_rev hbridge
    have hne₁ : u₁ ≠ v₁ := G.graph.ne_of_adj h₁
    have hne₂ : u₂ ≠ v₂ := G.graph.ne_of_adj h₂
    have h₁' : (doubledFlag G).graph.Adj (emb0 G u₁) (emb0 G v₁) :=
      (emb0_adj_iff G u₁ v₁ hne₁).mpr h₁
    have h₂' : (doubledFlag G).graph.Adj (emb0 G u₂) (emb0 G v₂) :=
      (emb0_adj_iff G u₂ v₂ hne₂).mpr h₂
    have hne' : (emb0 G u₁, emb0 G v₁) ≠ (emb0 G u₂, emb0 G v₂) := by
      intro heq
      apply hne
      have h1 := (Prod.mk.injEq _ _ _ _).mp heq
      exact Prod.ext (emb0_injective G h1.1) (emb0_injective G h1.2)
    have hne_rev' : (emb0 G u₁, emb0 G v₁) ≠ (emb0 G v₂, emb0 G u₂) := by
      intro heq
      apply hne_rev
      have h1 := (Prod.mk.injEq _ _ _ _).mp heq
      exact Prod.ext (emb0_injective G h1.1) (emb0_injective G h1.2)
    -- Pull a bridge across; existential over `Fin G.size` lifts to `Fin (doubledFlag G).size`.
    apply hstrong _ _ _ _ h₁' h₂' hne' hne_rev'
    obtain ⟨a, b, hab_adj, ha_share, hb_share⟩ := hbridge
    have hne_ab : a ≠ b := G.graph.ne_of_adj hab_adj
    refine ⟨emb0 G a, emb0 G b, (emb0_adj_iff G a b hne_ab).mpr hab_adj, ?_, ?_⟩
    · rcases ha_share with rfl | rfl | rfl | rfl <;> tauto
    · rcases hb_share with rfl | rfl | rfl | rfl <;> tauto

/-- **Strong chromatic index monotonicity under doubling**:
    `χ'_s(G) ≤ χ'_s(doubledFlag G)`. -/
theorem strongChromaticIndex_le_doubledFlag (G : Flag emptyType) :
    strongChromaticIndex G ≤ strongChromaticIndex (doubledFlag G) := by
  apply csInf_le_csInf (OrderBot.bddBelow _)
  · -- The colouring set is nonempty: use the all-distinct (identity-indexed) colouring.
    -- We exhibit a colouring of doubledFlag G with `(doubledFlag G).size * (doubledFlag G).size`
    -- colours: give each ordered pair its own colour (forced symmetric by indexing via {min,max}).
    refine ⟨(doubledFlag G).size * (doubledFlag G).size + 1,
      fun e => (Fin.val (min e.1 e.2)) * (doubledFlag G).size + Fin.val (max e.1 e.2),
      ⟨?_, ?_⟩, ?_⟩
    · intro u v _
      simp [min_comm, max_comm]
    · intro u₁ v₁ u₂ v₂ _ _ hne hne_rev _ heq
      -- Distinct unordered pairs give distinct values.
      have h_eq_min : (min u₁ v₁).val * (doubledFlag G).size + (max u₁ v₁).val =
                     (min u₂ v₂).val * (doubledFlag G).size + (max u₂ v₂).val := heq
      have hmax_lt : (max u₁ v₁).val < (doubledFlag G).size := (max u₁ v₁).isLt
      have hmax_lt' : (max u₂ v₂).val < (doubledFlag G).size := (max u₂ v₂).isLt
      have hN_pos : 0 < (doubledFlag G).size := lt_of_le_of_lt (Nat.zero_le _) hmax_lt
      -- Use Euclidean-division uniqueness: a₁ * N + r₁ = a₂ * N + r₂ with r₁, r₂ < N ⟹ a₁ = a₂.
      have hmax_eq : (max u₁ v₁).val = (max u₂ v₂).val := by
        have heq_mod : ((min u₁ v₁).val * (doubledFlag G).size + (max u₁ v₁).val) %
            (doubledFlag G).size =
            ((min u₂ v₂).val * (doubledFlag G).size + (max u₂ v₂).val) %
            (doubledFlag G).size := by rw [h_eq_min]
        rw [show (min u₁ v₁).val * (doubledFlag G).size + (max u₁ v₁).val =
              (max u₁ v₁).val + (min u₁ v₁).val * (doubledFlag G).size from by ring,
            show (min u₂ v₂).val * (doubledFlag G).size + (max u₂ v₂).val =
              (max u₂ v₂).val + (min u₂ v₂).val * (doubledFlag G).size from by ring] at heq_mod
        rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at heq_mod
        rw [Nat.mod_eq_of_lt hmax_lt, Nat.mod_eq_of_lt hmax_lt'] at heq_mod
        exact heq_mod
      have hmin_eq : (min u₁ v₁).val = (min u₂ v₂).val := by
        have h_eq' : (min u₁ v₁).val * (doubledFlag G).size =
            (min u₂ v₂).val * (doubledFlag G).size := by omega
        exact Nat.eq_of_mul_eq_mul_right hN_pos h_eq'
      -- Reduce to a Fin-level pair equality via the `min`/`max` representation.
      have hmin_fin : min u₁ v₁ = min u₂ v₂ := Fin.ext hmin_eq
      have hmax_fin : max u₁ v₁ = max u₂ v₂ := Fin.ext hmax_eq
      -- Set-theoretic fact: if {u₁, v₁} = {u₂, v₂} as multisets (via min+max), then
      -- (u₁, v₁) = (u₂, v₂) or (u₁, v₁) = (v₂, u₂).
      have hset : (u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ = v₂ ∧ v₁ = u₂) := by
        by_cases h12 : u₁ ≤ v₁
        · rw [min_eq_left h12] at hmin_fin
          rw [max_eq_right h12] at hmax_fin
          by_cases h12' : u₂ ≤ v₂
          · rw [min_eq_left h12'] at hmin_fin
            rw [max_eq_right h12'] at hmax_fin
            exact Or.inl ⟨hmin_fin, hmax_fin⟩
          · push_neg at h12'
            have h12'' : v₂ ≤ u₂ := le_of_lt h12'
            rw [min_eq_right h12''] at hmin_fin
            rw [max_eq_left h12''] at hmax_fin
            -- hmin_fin : u₁ = v₂, hmax_fin : v₁ = u₂; want (u₁ = v₂ ∧ v₁ = u₂).
            exact Or.inr ⟨hmin_fin, hmax_fin⟩
        · push_neg at h12
          have h12'' : v₁ ≤ u₁ := le_of_lt h12
          rw [min_eq_right h12''] at hmin_fin
          rw [max_eq_left h12''] at hmax_fin
          by_cases h12' : u₂ ≤ v₂
          · rw [min_eq_left h12'] at hmin_fin
            rw [max_eq_right h12'] at hmax_fin
            -- hmin_fin : v₁ = u₂, hmax_fin : u₁ = v₂; want (u₁ = v₂ ∧ v₁ = u₂).
            exact Or.inr ⟨hmax_fin, hmin_fin⟩
          · push_neg at h12'
            have h12''' : v₂ ≤ u₂ := le_of_lt h12'
            rw [min_eq_right h12'''] at hmin_fin
            rw [max_eq_left h12'''] at hmax_fin
            exact Or.inl ⟨hmax_fin, hmin_fin⟩
      rcases hset with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · exact hne (Prod.ext hu hv)
      · exact hne_rev (Prod.ext hu hv)
    · intro u v _
      have h1 : (min u v).val ≤ (doubledFlag G).size - 1 := by
        have := (min u v).isLt; omega
      have h2 : (max u v).val ≤ (doubledFlag G).size - 1 := by
        have := (max u v).isLt; omega
      have hN : 1 ≤ (doubledFlag G).size := by
        have hu := u.isLt; omega
      have hmul : (min u v).val * (doubledFlag G).size ≤
          ((doubledFlag G).size - 1) * (doubledFlag G).size :=
        Nat.mul_le_mul_right _ h1
      have key : (min u v).val * (doubledFlag G).size + (max u v).val
          ≤ ((doubledFlag G).size - 1) * (doubledFlag G).size + ((doubledFlag G).size - 1) :=
        Nat.add_le_add hmul h2
      -- ((N-1)*N + (N-1) < N*N + 1) for N ≥ 1: rewrite via Nat.sub_mul.
      have hmul_eq : ((doubledFlag G).size - 1) * (doubledFlag G).size =
          (doubledFlag G).size * (doubledFlag G).size - (doubledFlag G).size := by
        rw [Nat.sub_mul, one_mul]
      have hN_sub : ((doubledFlag G).size - 1) * (doubledFlag G).size + ((doubledFlag G).size - 1)
          < (doubledFlag G).size * (doubledFlag G).size + 1 := by
        rw [hmul_eq]
        have hsq : (doubledFlag G).size ≤ (doubledFlag G).size * (doubledFlag G).size := by
          exact Nat.le_mul_of_pos_left _ hN
        omega
      exact lt_of_le_of_lt key hN_sub
  · -- Pull back a colouring of doubledFlag G to G.
    intro k ⟨c', hc'_strong, hc'_lt⟩
    refine ⟨fun e => c' (emb0 G e.1, emb0 G e.2),
      isStrongEdgeColouring_pullback G c' hc'_strong, ?_⟩
    intro u v hadj
    have hne : u ≠ v := G.graph.ne_of_adj hadj
    have hadj' : (doubledFlag G).graph.Adj (emb0 G u) (emb0 G v) :=
      (emb0_adj_iff G u v hne).mpr hadj
    exact hc'_lt _ _ hadj'

/-! ## §1b. Bipartiteness is preserved by doubling -/

/-- **Cross-edge adjacency** in the doubled graph: for the same original
    vertex `a`, the copy-0 vertex `a₀` and copy-1 vertex `a₁` are adjacent
    iff `vertexDegree G a < maxDegree G`. -/
lemma doubledGraph_adj_cross (G : Flag emptyType) (a : Fin G.size) :
    (doubledGraph G).Adj ⟨a.val, by omega⟩ ⟨a.val + G.size, by omega⟩ ↔
      vertexDegree G a < maxDegree G := by
  unfold doubledGraph
  rw [SimpleGraph.fromRel_adj]
  have hne : G.size ≠ 0 := by
    intro h; exact absurd a.isLt (by omega)
  have hpos : 0 < G.size := Nat.pos_of_ne_zero hne
  constructor
  · rintro ⟨_, (⟨a', b', (⟨hva, hwb⟩ | ⟨hva, hwb⟩), hadj⟩ | ⟨a', ha1, ha2, hdeg⟩) |
             (⟨a', b', (⟨hva, hwb⟩ | ⟨hva, hwb⟩), hadj⟩ | ⟨a', ha1, ha2, hdeg⟩)⟩
    -- r v w, same-copy 0: w.val = a.val + size = b'.val < size, impossible
    · exfalso; dsimp only at hwb; omega
    -- r v w, same-copy 1: v.val = a.val = a'.val + size, impossible
    · exfalso; dsimp only at hva; omega
    -- r v w, cross-edge:
    · exact (Fin.ext (by dsimp only at ha1; omega) : a' = a) ▸ hdeg
    -- r w v, same-copy 0: hva : w.val = a.val + size = a'.val < size, impossible
    · exfalso; dsimp only at hva; have := a'.isLt; omega
    -- r w v, same-copy 1: hwb : v.val = a.val = b'.val + size, impossible
    · exfalso; dsimp only at hwb; omega
    -- r w v, cross-edge: ha2 : v.val = a.val = a'.val + size, impossible
    · exfalso; dsimp only at ha2; omega
  · intro hdeg
    exact ⟨by intro h; simp only [Fin.mk.injEq] at h; omega, Or.inl (Or.inr ⟨a, rfl, rfl, hdeg⟩)⟩

/-- **Doubling preserves bipartiteness.** If `G` is bipartite with side
    `S`, then `doubledFlag G` is bipartite with side `S'` in which copy-0
    keeps `G`'s sides and copy-1 swaps them:
    `S' = {v | v.val < size ∧ ⟨v.val⟩ ∈ S} ∪ {v | v.val ≥ size ∧ ⟨v.val-size⟩ ∉ S}`. -/
lemma doubledFlag_isBipartite (G : Flag emptyType) (h : IsBipartite G) :
    IsBipartite (doubledFlag G) := by
  -- For a copy-0 vertex `v` (v.val < size), the original is ⟨v.val⟩.
  -- For a copy-1 vertex `v` (v.val ≥ size), the original is ⟨v.val - size⟩.
  set n := G.size with hn_def
  obtain ⟨S, hS⟩ := h
  by_cases hn : n = 0
  · -- empty graph: trivially bipartite
    refine ⟨∅, ?_⟩
    intro u v _
    exact absurd u.isLt (by simp only [doubledFlag]; omega)
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  -- membership predicate
  let mem' : Fin (doubledFlag G).size → Prop := fun v =>
    (v.val < n ∧ (⟨v.val % n, Nat.mod_lt _ hpos⟩ : Fin n) ∈ S) ∨
    (n ≤ v.val ∧ (⟨v.val % n, Nat.mod_lt _ hpos⟩ : Fin n) ∉ S)
  classical
  refine ⟨Finset.univ.filter mem', ?_⟩
  intro u v hadj
  -- decode val arithmetic
  have hmod_lt : ∀ (x : Fin n), x.val % n = x.val := fun x => Nat.mod_eq_of_lt x.isLt
  have hmod_add : ∀ (x : Fin n), (x.val + n) % n = x.val := by
    intro x; rw [Nat.add_mod_right, hmod_lt]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem']
  -- Unfold the doubled adjacency.
  change (doubledGraph G).Adj u v at hadj
  rw [doubledGraph, SimpleGraph.fromRel_adj] at hadj
  obtain ⟨hne, hrel⟩ := hadj
  -- Classify the edge into copy-0 / copy-1 / cross.
  rcases hrel with (⟨a, b, hab_pos, hab_adj⟩ | ⟨a, ha_u, ha_v, _⟩) |
                    (⟨a, b, hab_pos, hab_adj⟩ | ⟨a, ha_v, ha_u, _⟩)
  -- r u v, same-copy: both copy-0 or both copy-1, G.Adj a b
  · rcases hab_pos with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · -- copy-0: u.val = a.val, v.val = b.val
      have hua : (⟨u.val % n, Nat.mod_lt _ hpos⟩ : Fin n) = a :=
        Fin.ext (show u.val % n = a.val by rw [hu]; exact Nat.mod_eq_of_lt a.isLt)
      have hvb : (⟨v.val % n, Nat.mod_lt _ hpos⟩ : Fin n) = b :=
        Fin.ext (show v.val % n = b.val by rw [hv]; exact Nat.mod_eq_of_lt b.isLt)
      have hu_lt : u.val < n := by rw [hu]; exact a.isLt
      have hv_lt : v.val < n := by rw [hv]; exact b.isLt
      have hbip := hS a b hab_adj
      rw [hua, hvb]
      constructor
      · rintro (⟨_, haS⟩ | ⟨h, _⟩)
        · rintro (⟨_, hbS⟩ | ⟨hge, _⟩)
          · exact (hbip.mp haS) hbS
          · omega
        · omega
      · intro hv_not
        left; refine ⟨hu_lt, ?_⟩
        by_contra haS
        have hbS : b ∈ S := by by_contra hb; exact haS (hbip.mpr hb)
        exact hv_not (Or.inl ⟨hv_lt, hbS⟩)
    · -- copy-1: u.val = a.val + n, v.val = b.val + n
      have hu_ge : n ≤ u.val := by rw [hu]; omega
      have hv_ge : n ≤ v.val := by rw [hv]; omega
      have hua : (⟨u.val % n, Nat.mod_lt _ hpos⟩ : Fin n) = a :=
        Fin.ext (show u.val % n = a.val by rw [hu]; exact hmod_add a)
      have hvb : (⟨v.val % n, Nat.mod_lt _ hpos⟩ : Fin n) = b :=
        Fin.ext (show v.val % n = b.val by rw [hv]; exact hmod_add b)
      have hbip := hS a b hab_adj
      rw [hua, hvb]
      constructor
      · rintro (⟨h, _⟩ | ⟨_, haS⟩)
        · omega
        · -- a ∉ S; want ¬(copy-1 v ∧ b ∉ S), i.e. show b ∈ S
          have hbS : b ∈ S := by by_contra hb; exact haS (hbip.mpr hb)
          rintro (⟨h, _⟩ | ⟨_, hbS'⟩)
          · omega
          · exact hbS' hbS
      · intro hv_not
        right
        refine ⟨hu_ge, ?_⟩
        intro haS
        -- a ∈ S ⟹ b ∉ S ⟹ copy-1 v holds, contradiction
        exact hv_not (Or.inr ⟨hv_ge, hbip.mp haS⟩)
  -- r u v, cross-edge: u.val = a.val, v.val = a.val + n
  · have hu_lt : u.val < n := by rw [ha_u]; exact a.isLt
    have hv_ge : n ≤ v.val := by rw [ha_v]; omega
    have hua : (⟨u.val % n, Nat.mod_lt _ hpos⟩ : Fin n) = a :=
      Fin.ext (show u.val % n = a.val by rw [ha_u]; exact Nat.mod_eq_of_lt a.isLt)
    have hva : (⟨v.val % n, Nat.mod_lt _ hpos⟩ : Fin n) = a :=
      Fin.ext (show v.val % n = a.val by rw [ha_v]; exact hmod_add a)
    rw [hua, hva]
    constructor
    · rintro (⟨_, haS⟩ | ⟨h, _⟩)
      · rintro (⟨h, _⟩ | ⟨_, haS'⟩)
        · omega
        · exact haS' haS
      · omega
    · intro hv_not
      left
      refine ⟨hu_lt, ?_⟩
      by_contra haS
      exact hv_not (Or.inr ⟨hv_ge, haS⟩)
  -- r v u, same-copy: G.Adj a b with v on a-side, u on b-side
  · rcases hab_pos with ⟨hv, hu⟩ | ⟨hv, hu⟩
    · -- copy-0: v.val = a.val, u.val = b.val
      have hua : (⟨u.val % n, Nat.mod_lt _ hpos⟩ : Fin n) = b :=
        Fin.ext (show u.val % n = b.val by rw [hu]; exact Nat.mod_eq_of_lt b.isLt)
      have hvb : (⟨v.val % n, Nat.mod_lt _ hpos⟩ : Fin n) = a :=
        Fin.ext (show v.val % n = a.val by rw [hv]; exact Nat.mod_eq_of_lt a.isLt)
      have hu_lt : u.val < n := by rw [hu]; exact b.isLt
      have hv_lt : v.val < n := by rw [hv]; exact a.isLt
      have hbip := hS a b hab_adj
      rw [hua, hvb]
      -- u ↦ b, v ↦ a; hbip : a ∈ S ↔ b ∉ S
      constructor
      · rintro (⟨_, hbS⟩ | ⟨h, _⟩)
        · rintro (⟨_, haS⟩ | ⟨hge, _⟩)
          · exact (hbip.mp haS) hbS
          · omega
        · omega
      · intro hv_not
        left; refine ⟨hu_lt, ?_⟩
        -- want b ∈ S; if not, then a ∈ S (since hbip : a∈S ↔ b∉S), contradiction
        by_contra hbS
        exact hv_not (Or.inl ⟨hv_lt, hbip.mpr hbS⟩)
    · -- copy-1: v.val = a.val + n, u.val = b.val + n
      have hu_ge : n ≤ u.val := by rw [hu]; omega
      have hv_ge : n ≤ v.val := by rw [hv]; omega
      have hua : (⟨u.val % n, Nat.mod_lt _ hpos⟩ : Fin n) = b :=
        Fin.ext (show u.val % n = b.val by rw [hu]; exact hmod_add b)
      have hvb : (⟨v.val % n, Nat.mod_lt _ hpos⟩ : Fin n) = a :=
        Fin.ext (show v.val % n = a.val by rw [hv]; exact hmod_add a)
      have hbip := hS a b hab_adj
      rw [hua, hvb]
      -- u ↦ b (copy-1), v ↦ a (copy-1); hbip : a ∈ S ↔ b ∉ S
      constructor
      · rintro (⟨h, _⟩ | ⟨_, hbS⟩)
        · omega
        · -- b ∉ S ⟹ a ∈ S
          rintro (⟨h, _⟩ | ⟨_, haS⟩)
          · omega
          · exact hbS (by by_contra hb; exact haS (hbip.mpr hb))
      · intro hv_not
        right; refine ⟨hu_ge, ?_⟩
        -- want b ∉ S; if b ∈ S then a ∉ S, so v-side (a ∉ S) holds, contradiction
        intro hbS
        exact hv_not (Or.inr ⟨hv_ge, fun haS => (hbip.mp haS) hbS⟩)
  -- r v u, cross-edge: v.val = a.val, u.val = a.val + n
  · have hu_ge : n ≤ u.val := by rw [ha_u]; omega
    have hv_lt : v.val < n := by rw [ha_v]; exact a.isLt
    have hua : (⟨u.val % n, Nat.mod_lt _ hpos⟩ : Fin n) = a :=
      Fin.ext (show u.val % n = a.val by rw [ha_u]; exact hmod_add a)
    have hva : (⟨v.val % n, Nat.mod_lt _ hpos⟩ : Fin n) = a :=
      Fin.ext (show v.val % n = a.val by rw [Nat.mod_eq_of_lt hv_lt, ha_v])
    rw [hua, hva]
    constructor
    · rintro (⟨h, _⟩ | ⟨_, haS⟩)
      · omega
      · rintro (⟨_, haS'⟩ | ⟨h, _⟩)
        · exact haS haS'
        · omega
    · intro hv_not
      right
      refine ⟨hu_ge, ?_⟩
      intro haS
      exact hv_not (Or.inl ⟨hv_lt, haS⟩)

/-! ## §2. Iterated cover: regular suffices for χ'_s -/

/-- **WLOG regular (χ'_s version)**: For any `G : Flag emptyType`, there
    exists a regular `G'` with `Δ(G') = Δ(G)` and
    `strongChromaticIndex G ≤ strongChromaticIndex G'`.

    Mirrors `pentagon_regular_suffices`. Proof is iterated doubling
    (Molloy–Reed): each iteration preserves `Δ`, strictly increases the
    minimum degree (until regular), and does not decrease `χ'_s`. -/
theorem sec_regular_suffices (G : Flag emptyType) :
    ∃ G' : Flag emptyType,
      IsRegular G' ∧
      maxDegree G' = maxDegree G ∧
      strongChromaticIndex G ≤ strongChromaticIndex G' := by
  suffices h : ∀ k : ℕ, ∀ H : Flag emptyType,
      maxDegree H - minDegree H ≤ k →
      ∃ H' : Flag emptyType,
        IsRegular H' ∧
        maxDegree H' = maxDegree H ∧
        strongChromaticIndex H ≤ strongChromaticIndex H' by
    exact h _ G le_rfl
  intro k
  induction k with
  | zero =>
    intro H hk
    refine ⟨H, ?_, rfl, le_rfl⟩
    intro v
    have hle := minDegree_le_vertexDegree H v
    have hge := vertexDegree_le_maxDegree H v
    unfold vertexDegree at hle hge
    have hminmax := minDegree_le_maxDegree H
    omega
  | succ k ih =>
    intro H hk
    by_cases hReg : IsRegular H
    · exact ⟨H, hReg, rfl, le_rfl⟩
    · have hne : 0 < H.size := by
        by_contra h
        push_neg at h
        exact hReg (fun v => absurd v.isLt (by omega))
      have hNotReg : minDegree H < maxDegree H := by
        by_contra hle
        push_neg at hle
        exact hReg fun v => by
          have := minDegree_le_vertexDegree H v
          have := vertexDegree_le_maxDegree H v
          unfold vertexDegree at *
          omega
      have hDelta := doubledFlag_maxDegree H
      have hMono := strongChromaticIndex_le_doubledFlag H
      have hMinInc := doubledFlag_minDegree_inc H hne hNotReg
      have hGap : maxDegree (doubledFlag H) - minDegree (doubledFlag H) ≤ k := by
        rw [hDelta]; omega
      obtain ⟨H', hReg'', hDelta'', hChi''⟩ := ih (doubledFlag H) hGap
      refine ⟨H', hReg'', by omega, le_trans hMono hChi''⟩

/-- **WLOG regular, bipartite version (χ'_s)**: For any bipartite
    `G : Flag emptyType`, there exists a **regular and bipartite** `G'`
    with `Δ(G') = Δ(G)` and `strongChromaticIndex G ≤ strongChromaticIndex G'`.

    Same iterated-doubling proof as `sec_regular_suffices`, threading the
    `IsBipartite` invariant through every step. The doubling construction
    preserves bipartiteness (`doubledFlag_isBipartite`), so the regular
    graph produced is still bipartite — this is what makes the bipartite
    SEC certificate (generated with `Degree::regularity` on bipartite
    graphs) applicable to all bipartite graphs. -/
theorem sec_bipartite_regular_suffices (G : Flag emptyType) (hBip : IsBipartite G) :
    ∃ G' : Flag emptyType,
      IsRegular G' ∧
      IsBipartite G' ∧
      maxDegree G' = maxDegree G ∧
      strongChromaticIndex G ≤ strongChromaticIndex G' := by
  suffices h : ∀ k : ℕ, ∀ H : Flag emptyType, IsBipartite H →
      maxDegree H - minDegree H ≤ k →
      ∃ H' : Flag emptyType,
        IsRegular H' ∧
        IsBipartite H' ∧
        maxDegree H' = maxDegree H ∧
        strongChromaticIndex H ≤ strongChromaticIndex H' by
    exact h _ G hBip le_rfl
  intro k
  induction k with
  | zero =>
    intro H hHBip hk
    refine ⟨H, ?_, hHBip, rfl, le_rfl⟩
    intro v
    have hle := minDegree_le_vertexDegree H v
    have hge := vertexDegree_le_maxDegree H v
    unfold vertexDegree at hle hge
    have hminmax := minDegree_le_maxDegree H
    omega
  | succ k ih =>
    intro H hHBip hk
    by_cases hReg : IsRegular H
    · exact ⟨H, hReg, hHBip, rfl, le_rfl⟩
    · have hne : 0 < H.size := by
        by_contra h
        push_neg at h
        exact hReg (fun v => absurd v.isLt (by omega))
      have hNotReg : minDegree H < maxDegree H := by
        by_contra hle
        push_neg at hle
        exact hReg fun v => by
          have := minDegree_le_vertexDegree H v
          have := vertexDegree_le_maxDegree H v
          unfold vertexDegree at *
          omega
      have hDelta := doubledFlag_maxDegree H
      have hMono := strongChromaticIndex_le_doubledFlag H
      have hMinInc := doubledFlag_minDegree_inc H hne hNotReg
      have hBipDbl := doubledFlag_isBipartite H hHBip
      have hGap : maxDegree (doubledFlag H) - minDegree (doubledFlag H) ≤ k := by
        rw [hDelta]; omega
      obtain ⟨H', hReg'', hBip'', hDelta'', hChi''⟩ := ih (doubledFlag H) hBipDbl hGap
      refine ⟨H', hReg'', hBip'', by omega, le_trans hMono hChi''⟩

end

end Davey2024.Reductions.WLOGRegular
