import DaveyThesis2024.PentagonQIsoInvariance
import DaveyThesis2024.PentagonQRooted

/-!
# `μ` on the abstract side

Item E's right-hand side is `Σ_S μ(G'[S])`, so `μ` has to exist as a function of
a **flag**, not of a `CGraph`.

**It is defined through `rootedCountG`, never through `rootedCount`.**  That is
not a stylistic choice.  `rootedCount` is the hand-rolled `embeds` enumerator,
and `rootedCount_eq_cRootedCount` — obligation (a0) — relates it to an honest
count *only at the 9295 basis flags*, which is all obligation (b) needed.  An
8-subset of an abstract host is not a basis flag, so routing `μ` through
`rootedCount` would silently reintroduce the scope gap that C2's hypothesis was
weakened to avoid.  `rootedCountG` carries no such restriction.
-/

namespace Davey2024
namespace PentagonQMuFlag

open Davey2024.PentagonQWeights Davey2024.PentagonQRooted
open Davey2024.PentagonQIsoInvariance

local notation "CG2'" => colouredGraphUniverse 2

/-- The three rooted patterns, as flags, each rooted at vertex `0`. -/
noncomputable def tauFlag (p : Pat) (n : Nat) : GenFlag CG2' (GenFlagType.empty CG2') :=
  (patC p n).toGenFlag

/-- **`μ` at the flag level**: `4n₁ + n₂ + 2n₃`, the certificate's weight. -/
noncomputable def muG (G : GenFlag CG2' (GenFlagType.empty CG2')) : ℕ :=
  4 * rootedCountG (tauFlag tau1 4) G ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩
    + rootedCountG (tauFlag tau2 5) G ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩
    + 2 * rootedCountG (tauFlag tau3 5) G ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩

/-- **E step 2.**  `μ` depends only on the isomorphism class of its argument —
which is what lets the sum over 8-subsets be grouped by flag type.  Three
applications of B2. -/
theorem muG_flagIso {G G' : GenFlag CG2' (GenFlagType.empty CG2')}
    (h : GenFlagIso (GenFlagType.empty CG2') G G') : muG G = muG G' := by
  unfold muG
  rw [rootedCountG_flagIso_target _ h, rootedCountG_flagIso_target _ h,
    rootedCountG_flagIso_target _ h]

/-! ## Extracting the embedding

Item E's regrouping needs, at each 8-subset with `μ ≠ 0`, one of the three
rooted τ-embeddings — the hypothesis `is_basis_flag_of_embedding` takes.  Two
steps: `μ ≠ 0` puts one of the three counts above zero, and a positive count is
an inhabited type. -/

/-- `μ = 4n₁ + n₂ + 2n₃` is non-zero exactly when some `nᵢ` is. -/
theorem muG_ne_zero_iff (G : GenFlag CG2' (GenFlagType.empty CG2')) :
    muG G ≠ 0 ↔
      0 < rootedCountG (tauFlag tau1 4) G ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩ ∨
      0 < rootedCountG (tauFlag tau2 5) G ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩ ∨
      0 < rootedCountG (tauFlag tau3 5) G ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩ := by
  unfold muG
  omega

/-- A positive rooted count is an inhabited type of rooted embeddings. -/
theorem nonempty_of_rootedCountG_pos {F G : GenFlag CG2' (GenFlagType.empty CG2')}
    (root : Fin F.size) (h : 0 < rootedCountG F G root) :
    Nonempty {e : GenInducedEmbedding CG2' (GenFlagType.empty CG2') F G //
      ∀ w : Fin G.size, (∀ i, e.toFun i ≠ w) → (G.str.1).Adj (e.toFun root) w} := by
  unfold rootedCountG at h
  exact (Nat.card_pos_iff.mp h).1

/-! ## The two rooted counts agree

`genRootedCount` (obligation (a0), `CGraph`-side) and `rootedCountG` (item B,
flag-side) count the same embeddings but phrase the root clause differently: the
first on the `CGraph`'s `Bool` adjacency, the second on the flag's `SimpleGraph`.
`toGenFlag` wraps the former in `fromRel`, which inserts a `≠` and a symmetrised
`∨`; symmetry and irreflexivity remove both.

This is the link that lets `μ` at a basis flag be read off obligation (b) — a
seam of exactly the kind the two audits were looking for. -/
theorem genRootedCount_eq_rootedCountG {m : Nat} (F : CGraph (m + 1)) (G : CGraph 8)
    (hGs : ∀ i j, G.adj i j = G.adj j i) (hGi : ∀ i, G.adj i i = false) :
    genRootedCount F G = rootedCountG F.toGenFlag G.toGenFlag ⟨0, Nat.succ_pos m⟩ := by
  unfold genRootedCount rootedCountG
  refine Nat.card_congr (Equiv.subtypeEquivRight fun e => ?_)
  constructor
  · intro h w hw
    have hne : e.toFun ⟨0, Nat.succ_pos m⟩ ≠ w := hw _
    refine ⟨hne, Or.inl ?_⟩
    simpa using h w hw
  · intro h w hw
    obtain ⟨-, hor⟩ := h w hw
    rcases hor with hx | hx
    · simpa using hx
    · have : G.adj (e.toFun ⟨0, Nat.succ_pos m⟩) w = G.adj w (e.toFun ⟨0, Nat.succ_pos m⟩) :=
        hGs _ _
      rw [this]; simpa using hx

/-! ## From a flag-level embedding to the `CGraph`-level data

`is_basis_flag_of_embedding` — item C's chain — takes its τ-embedding as
elementwise colour and adjacency equations on `CGraph`s, while `rootedCountG`
produces a `GenInducedEmbedding` whose content is a single `comap` equation.
This unpacks the one into the other: `comap_iff_of_injective` (lifted in
obligation (a0)) for the colour and adjacency halves, and the same `fromRel`
argument as above for the root clause. -/
theorem cgraph_data_of_rooted_embedding (p : Pat) (m : Nat)
    (hFs : ∀ i j, (patC p (m + 1)).adj i j = (patC p (m + 1)).adj j i)
    (hFi : ∀ i, (patC p (m + 1)).adj i i = false)
    (G : CGraph 8) (hGs : ∀ i j, G.adj i j = G.adj j i) (hGi : ∀ i, G.adj i i = false)
    (e : GenInducedEmbedding CG2' (GenFlagType.empty CG2')
      (patC p (m + 1)).toGenFlag G.toGenFlag)
    (hroot : ∀ w : Fin 8, (∀ i, e.toFun i ≠ w) →
      (G.toGenFlag.str.1).Adj (e.toFun ⟨0, Nat.succ_pos m⟩) w) :
    (∀ i, (patC p (m + 1)).col i = G.col (e.toFun i)) ∧
    (∀ i j, (patC p (m + 1)).adj i j = G.adj (e.toFun i) (e.toFun j)) ∧
    (∀ w : Fin 8, (∀ i, e.toFun i ≠ w) →
      G.adj (e.toFun ⟨0, Nat.succ_pos m⟩) w = true) := by
  obtain ⟨hcol, hadj⟩ :=
    (comap_iff_of_injective (patC p (m + 1)) G hFs hFi hGs hGi e.toFun e.injective).mpr
      e.isInduced
  refine ⟨hcol, hadj, ?_⟩
  intro w hw
  obtain ⟨-, hor⟩ := hroot w hw
  rcases hor with hx | hx
  · simpa using hx
  · have : G.adj (e.toFun ⟨0, Nat.succ_pos m⟩) w = G.adj w (e.toFun ⟨0, Nat.succ_pos m⟩) :=
      hGs _ _
    rw [this]; simpa using hx

#print axioms cgraph_data_of_rooted_embedding
#print axioms genRootedCount_eq_rootedCountG
#print axioms muG_ne_zero_iff
#print axioms nonempty_of_rootedCountG_pos
#print axioms muG
#print axioms muG_flagIso

end PentagonQMuFlag
end Davey2024
