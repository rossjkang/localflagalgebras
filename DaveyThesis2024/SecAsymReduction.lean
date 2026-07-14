import DaveyThesis2024.SecAsymBiregularCompletion
import DaveyThesis2024.SecAsymBridgeF

/-!
# WLOG-biregular reduction for the asymmetric strong chromatic index (Phases M+W)

This file supplies the general induced-embedding χ'ₛ monotonicity lemma and the
per-graph "reduction to exactly-biregular" step that widens the asymmetric
thesis-tight headline from its `IsBiregularFloor`-narrowed (Phase R) form back to
all `IsAsymmetricBipartite p G`.

* `strongChromaticIndex_le_of_inducedEmbedding` — generalises the two
  `Reductions.WLOGRegular` template lemmas (`isStrongEdgeColouring_pullback`,
  `strongChromaticIndex_le_doubledFlag`) from the copy-0 doubling embedding to an
  arbitrary induced embedding `f : Fin G.size → Fin H.size`.
* `asym_biregular_reduction` — given `IsAsymmetricBipartite p G` (and `⌊pΔ⌋ ≥ 1`),
  produces the exact `(Δ, ⌊pΔ⌋)`-biregular completion `H = biregularCompletion G S a`
  (`SecAsymBiregularCompletion`) with `IsBiregularFloor p H`, `Δ(H) = Δ(G)`, and
  `χ'ₛ(G) ≤ χ'ₛ(H)`. The completion embeds `G` induced on `V(G)` (copy-0), so the
  monotonicity lemma applies.
-/

namespace Davey2024.SecAsymReduction

open Davey2024 Davey2024.SecAsymBiregularCompletion Davey2024.SecAsymmetricBipartiteBridge
open Finset BigOperators Classical

set_option linter.unusedSectionVars false

noncomputable section

/-! ## §1. Pullback of a strong colouring along a general induced embedding -/

/-- Pulling back a strong edge colouring of `H` along an induced embedding
`f : Fin G.size → Fin H.size` yields a strong edge colouring of `G`.
Generalises `Reductions.WLOGRegular.isStrongEdgeColouring_pullback`. -/
lemma isStrongEdgeColouring_pullback_gen (G H : Flag emptyType)
    (f : Fin G.size → Fin H.size)
    (hinj : Function.Injective f)
    (hadj : ∀ u v, u ≠ v → (H.graph.Adj (f u) (f v) ↔ G.graph.Adj u v))
    (c' : Fin H.size × Fin H.size → ℕ)
    (hc' : IsStrongEdgeColouring H.graph c') :
    IsStrongEdgeColouring G.graph
      (fun e : Fin G.size × Fin G.size => c' (f e.1, f e.2)) := by
  obtain ⟨hsymm, hstrong⟩ := hc'
  refine ⟨?_, ?_⟩
  · -- Symmetry
    intro u v hadjuv
    have hne : u ≠ v := G.graph.ne_of_adj hadjuv
    have hadj' : H.graph.Adj (f u) (f v) := (hadj u v hne).mpr hadjuv
    exact hsymm _ _ hadj'
  · -- Strong property
    intro u₁ v₁ u₂ v₂ h₁ h₂ hne hne_rev hbridge
    have hne₁ : u₁ ≠ v₁ := G.graph.ne_of_adj h₁
    have hne₂ : u₂ ≠ v₂ := G.graph.ne_of_adj h₂
    have h₁' : H.graph.Adj (f u₁) (f v₁) := (hadj u₁ v₁ hne₁).mpr h₁
    have h₂' : H.graph.Adj (f u₂) (f v₂) := (hadj u₂ v₂ hne₂).mpr h₂
    have hne' : (f u₁, f v₁) ≠ (f u₂, f v₂) := by
      intro heq
      apply hne
      have h1 := (Prod.mk.injEq _ _ _ _).mp heq
      exact Prod.ext (hinj h1.1) (hinj h1.2)
    have hne_rev' : (f u₁, f v₁) ≠ (f v₂, f u₂) := by
      intro heq
      apply hne_rev
      have h1 := (Prod.mk.injEq _ _ _ _).mp heq
      exact Prod.ext (hinj h1.1) (hinj h1.2)
    apply hstrong _ _ _ _ h₁' h₂' hne' hne_rev'
    obtain ⟨a, b, hab_adj, ha_share, hb_share⟩ := hbridge
    have hne_ab : a ≠ b := G.graph.ne_of_adj hab_adj
    refine ⟨f a, f b, (hadj a b hne_ab).mpr hab_adj, ?_, ?_⟩
    · rcases ha_share with rfl | rfl | rfl | rfl <;> tauto
    · rcases hb_share with rfl | rfl | rfl | rfl <;> tauto

/-- **General induced-embedding χ'ₛ monotonicity.** If `G` embeds induced into `H`
via an injective `f` whose adjacency is iff `G`-adjacency, then
`χ'ₛ(G) ≤ χ'ₛ(H)`. Generalises `Reductions.WLOGRegular.strongChromaticIndex_le_doubledFlag`. -/
theorem strongChromaticIndex_le_of_inducedEmbedding
    (G H : Flag emptyType) (f : Fin G.size → Fin H.size)
    (hinj : Function.Injective f)
    (hadj : ∀ u v, u ≠ v → (H.graph.Adj (f u) (f v) ↔ G.graph.Adj u v)) :
    strongChromaticIndex G ≤ strongChromaticIndex H := by
  apply csInf_le_csInf (OrderBot.bddBelow _)
  · -- The colouring set of `H` is nonempty: give each unordered pair its own colour.
    refine ⟨H.size * H.size + 1,
      fun e => (Fin.val (min e.1 e.2)) * H.size + Fin.val (max e.1 e.2),
      ⟨?_, ?_⟩, ?_⟩
    · intro u v _
      simp [min_comm, max_comm]
    · intro u₁ v₁ u₂ v₂ _ _ hne hne_rev _ heq
      have h_eq_min : (min u₁ v₁).val * H.size + (max u₁ v₁).val =
                     (min u₂ v₂).val * H.size + (max u₂ v₂).val := heq
      have hmax_lt : (max u₁ v₁).val < H.size := (max u₁ v₁).isLt
      have hmax_lt' : (max u₂ v₂).val < H.size := (max u₂ v₂).isLt
      have hN_pos : 0 < H.size := lt_of_le_of_lt (Nat.zero_le _) hmax_lt
      have hmax_eq : (max u₁ v₁).val = (max u₂ v₂).val := by
        have heq_mod : ((min u₁ v₁).val * H.size + (max u₁ v₁).val) % H.size =
            ((min u₂ v₂).val * H.size + (max u₂ v₂).val) % H.size := by rw [h_eq_min]
        rw [show (min u₁ v₁).val * H.size + (max u₁ v₁).val =
              (max u₁ v₁).val + (min u₁ v₁).val * H.size from by ring,
            show (min u₂ v₂).val * H.size + (max u₂ v₂).val =
              (max u₂ v₂).val + (min u₂ v₂).val * H.size from by ring] at heq_mod
        rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right] at heq_mod
        rw [Nat.mod_eq_of_lt hmax_lt, Nat.mod_eq_of_lt hmax_lt'] at heq_mod
        exact heq_mod
      have hmin_eq : (min u₁ v₁).val = (min u₂ v₂).val := by
        have h_eq' : (min u₁ v₁).val * H.size = (min u₂ v₂).val * H.size := by omega
        exact Nat.eq_of_mul_eq_mul_right hN_pos h_eq'
      have hmin_fin : min u₁ v₁ = min u₂ v₂ := Fin.ext hmin_eq
      have hmax_fin : max u₁ v₁ = max u₂ v₂ := Fin.ext hmax_eq
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
            exact Or.inr ⟨hmin_fin, hmax_fin⟩
        · push_neg at h12
          have h12'' : v₁ ≤ u₁ := le_of_lt h12
          rw [min_eq_right h12''] at hmin_fin
          rw [max_eq_left h12''] at hmax_fin
          by_cases h12' : u₂ ≤ v₂
          · rw [min_eq_left h12'] at hmin_fin
            rw [max_eq_right h12'] at hmax_fin
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
      have h1 : (min u v).val ≤ H.size - 1 := by
        have := (min u v).isLt; omega
      have h2 : (max u v).val ≤ H.size - 1 := by
        have := (max u v).isLt; omega
      have hN : 1 ≤ H.size := by
        have hu := u.isLt; omega
      have hmul : (min u v).val * H.size ≤ (H.size - 1) * H.size :=
        Nat.mul_le_mul_right _ h1
      have key : (min u v).val * H.size + (max u v).val
          ≤ (H.size - 1) * H.size + (H.size - 1) :=
        Nat.add_le_add hmul h2
      have hmul_eq : (H.size - 1) * H.size = H.size * H.size - H.size := by
        rw [Nat.sub_mul, one_mul]
      have hN_sub : (H.size - 1) * H.size + (H.size - 1) < H.size * H.size + 1 := by
        rw [hmul_eq]
        have hsq : H.size ≤ H.size * H.size := Nat.le_mul_of_pos_left _ hN
        omega
      exact lt_of_le_of_lt key hN_sub
  · -- Pull back a colouring of `H` to `G`.
    intro k ⟨c', hc'_strong, hc'_lt⟩
    refine ⟨fun e => c' (f e.1, f e.2),
      isStrongEdgeColouring_pullback_gen G H f hinj hadj c' hc'_strong, ?_⟩
    intro u v hadjuv
    have hne : u ≠ v := G.graph.ne_of_adj hadjuv
    have hadj' : H.graph.Adj (f u) (f v) := (hadj u v hne).mpr hadjuv
    exact hc'_lt _ _ hadj'

/-! ## §2. The per-graph reduction to exactly-biregular -/

/-- **WLOG-biregular reduction (asymmetric χ'ₛ).** Every `IsAsymmetricBipartite p G`
(with `⌊pΔ⌋ ≥ 1`) has an exactly-`(Δ, ⌊pΔ⌋)`-biregular completion `H` with the same
max degree and no smaller strong chromatic index. Widens the `IsBiregularFloor`-gated
asymmetric headline back to all asymmetric-bipartite hosts. -/
theorem asym_biregular_reduction (p : ℝ) (_hp1 : 0 < p) (hp2 : p ≤ 1) (G : Flag emptyType)
    (hAsym : IsAsymmetricBipartite p G) (ha1 : 1 ≤ Nat.floor (p * (maxDegree G : ℝ))) :
    ∃ H : Flag emptyType,
      IsBiregularFloor p H ∧ maxDegree H = maxDegree G ∧
      strongChromaticIndex G ≤ strongChromaticIndex H := by
  obtain ⟨S, hbip, hhi, hloR⟩ := hAsym
  set a : ℕ := Nat.floor (p * (maxDegree G : ℝ)) with hadef
  -- Low-side degree `≤ a` from `deg ≤ pΔ` (integer floor).
  have hlo : ∀ u, u ∉ S → (univ.filter (fun v => G.graph.Adj u v)).card ≤ a := by
    intro u hu
    exact Nat.le_floor (hloR u hu)
  -- `a = ⌊pΔ⌋ ≤ ⌊Δ⌋ = Δ`.
  have hle : p * (maxDegree G : ℝ) ≤ (maxDegree G : ℝ) :=
    mul_le_of_le_one_left (Nat.cast_nonneg _) hp2
  have haΔ : a ≤ maxDegree G := by
    rw [hadef]
    calc Nat.floor (p * (maxDegree G : ℝ)) ≤ Nat.floor ((maxDegree G : ℝ)) :=
          Nat.floor_mono hle
      _ = maxDegree G := Nat.floor_natCast _
  have hmax : maxDegree (biregularCompletion G S a) = maxDegree G :=
    biregularCompletion_maxDegree G S a ha1 haΔ
  refine ⟨biregularCompletion G S a, ?_, hmax, ?_⟩
  · -- `IsBiregularFloor p H`
    refine ⟨bcHighSet G S a, biregularCompletion_bipartite G S a hbip hhi haΔ, ?_, ?_⟩
    · -- high side exactly `= maxDegree H`
      intro u hu
      rw [hmax]
      exact biregularCompletion_high_deg G S a hhi haΔ u hu
    · -- low side exactly `= ⌊p·maxDegree H⌋`
      intro u hu
      rw [hmax, ← hadef]
      exact biregularCompletion_low_deg G S a hlo u hu
  · -- `χ'ₛ(G) ≤ χ'ₛ(H)` via the copy-0 induced embedding
    exact strongChromaticIndex_le_of_inducedEmbedding G (biregularCompletion G S a)
      (bcEmb0 G S a ha1 haΔ)
      (biregularCompletion_emb0_injective G S a ha1 haΔ)
      (biregularCompletion_emb0_adj_iff G S a ha1 haΔ)

end

end Davey2024.SecAsymReduction
