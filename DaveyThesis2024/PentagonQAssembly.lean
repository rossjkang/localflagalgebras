import DaveyThesis2024.PentagonQRoundTrip
import DaveyThesis2024.PentagonQRelabel
import DaveyThesis2024.PentagonQSpikeC3
import DaveyThesis2024.PentagonQComplete
import DaveyThesis2024.PentagonQPatFacts

/-!
# The chain, part 1: a τ-embedding puts a graph into the family

`exists_perm_extending` moves the τ-image to `0 … k-1`.  This is the step that
turns that permutation into `FamShape` — the hypothesis `famGraph_maskOf`
consumes — by checking each of its six fields against the embedding's own
properties.

The first module to import `PentagonQRoundTrip` and `PentagonQRelabel` together,
so `FamShape` and `relabel` meet here for the first time.
-/

namespace Davey2024
namespace PentagonQAssembly

open Davey2024.PentagonQBasis Davey2024.PentagonQWeights
open Davey2024.PentagonQFamily Davey2024.PentagonQRoundTrip
open Davey2024.PentagonQRelabel Davey2024.PentagonQSpikeC3

/-- Relabelled adjacency, at `Nat` indices. -/
private theorem adjN_relabel (g : CGraph 8) (π : Equiv.Perm (Fin 8))
    {i j : Nat} (hi : i < 8) (hj : j < 8) :
    adjN (relabel g π) i j = g.adj (π ⟨i, hi⟩) (π ⟨j, hj⟩) := by
  simp [adjN, relabel, hi, hj]

private theorem colN_relabel (g : CGraph 8) (π : Equiv.Perm (Fin 8))
    {v : Nat} (hv : v < 8) : colN (relabel g π) v = g.col (π ⟨v, hv⟩) := by
  simp [colN, relabel, hv]

/-- **The chain's first link.**  A τ-embedding whose root dominates the outside,
composed with the permutation that moves its image to `0 … k-1`, lands in the
family's shape. -/
theorem famShape_of_embedding
    (g : CGraph 8) (p : Pat) (hn0 : 0 < p.n) (hn8 : p.n ≤ 8)
    (hsym : ∀ i j, g.adj i j = g.adj j i) (hirr : ∀ i, g.adj i i = false)
    (f : Fin p.n → Fin 8)
    (hcolf : ∀ i : Fin p.n, g.col (f i) = (if p.cols[i.val]! == 1 then 1 else 0))
    (hadjf : ∀ i j : Fin p.n, g.adj (f i) (f j) = (p.padj[i.val]!)[j.val]!)
    (hdom : ∀ w : Fin 8, (∀ i, f i ≠ w) → g.adj (f ⟨0, hn0⟩) w = true)
    (π : Equiv.Perm (Fin 8)) (hπ : ∀ i : Fin p.n, π (Fin.castLE hn8 i) = f i) :
    FamShape p (relabel g π) where
  size := ⟨hn0, hn8⟩
  irrefl := by
    intro i
    by_cases hi : i < 8
    · rw [adjN_relabel g π hi hi]; exact hirr _
    · simp [adjN, hi]
  symm := by
    intro i j
    by_cases hi : i < 8
    · by_cases hj : j < 8
      · rw [adjN_relabel g π hi hj, adjN_relabel g π hj hi]; exact hsym _ _
      · simp [adjN, hj]
    · simp [adjN, hi]
  inner := by
    intro i j hi hj
    have hi8 : i < 8 := by omega
    have hj8 : j < 8 := by omega
    rw [adjN_relabel g π hi8 hj8]
    have ei : π ⟨i, hi8⟩ = f ⟨i, hi⟩ := by rw [← hπ ⟨i, hi⟩]; rfl
    have ej : π ⟨j, hj8⟩ = f ⟨j, hj⟩ := by rw [← hπ ⟨j, hj⟩]; rfl
    rw [ei, ej]
    exact hadjf ⟨i, hi⟩ ⟨j, hj⟩
  root := by
    intro j hj hj8
    rw [adjN_relabel g π (by omega) hj8]
    have e0 : π ⟨0, by omega⟩ = f ⟨0, hn0⟩ := by rw [← hπ ⟨0, hn0⟩]; rfl
    rw [e0]
    refine hdom _ ?_
    intro i hi
    exact perm_outside hn8 f π hπ ⟨j, hj8⟩ hj ⟨i, by rw [← hi]⟩
  cols := by
    intro v hv
    have hv8 : v < 8 := by omega
    rw [colN_relabel g π hv8]
    have ev : π ⟨v, hv8⟩ = f ⟨v, hv⟩ := by rw [← hπ ⟨v, hv⟩]; rfl
    rw [ev]
    exact hcolf ⟨v, hv⟩

/-! ## The chain

Every link is in place; this composes them. -/

private theorem relabel_symm (g : CGraph 8) (π : Equiv.Perm (Fin 8))
    (hsym : ∀ i j, g.adj i j = g.adj j i) :
    ∀ i j, (relabel g π).adj i j = (relabel g π).adj j i := fun i j => hsym _ _

private theorem relabel_irrefl (g : CGraph 8) (π : Equiv.Perm (Fin 8))
    (hirr : ∀ i, g.adj i i = false) :
    ∀ i, (relabel g π).adj i i = false := fun i => hirr _

/-- **The chain.**  A triangle-free, black-independent 8-vertex coloured graph
carrying a τ-embedding whose root dominates the outside is isomorphic, as a flag,
to one of the 69 basis flags of non-zero weight. -/
theorem is_basis_flag_of_embedding
    (g : CGraph 8) (p : Pat) (hp : p ∈ [tau1, tau2, tau3])
    (hsym : ∀ i j, g.adj i j = g.adj j i) (hirr : ∀ i, g.adj i i = false)
    (htf : triangleFreeC g = true) (hbi : blackIndepC g = true)
    (f : Fin p.n → Fin 8) (hinj : Function.Injective f)
    (hcolf : ∀ i : Fin p.n, g.col (f i) = (if p.cols[i.val]! == 1 then 1 else 0))
    (hadjf : ∀ i j : Fin p.n, g.adj (f i) (f j) = (p.padj[i.val]!)[j.val]!)
    (hn0 : 0 < p.n)
    (hdom : ∀ w : Fin 8, (∀ i, f i ≠ w) → g.adj (f ⟨0, hn0⟩) w = true) :
    ∃ j ∈ PentagonQComplete.nzIdx,
      GenFlagClass.mk g.toGenFlag = GenFlagClass.mk (flagBasisCGraph j).toGenFlag := by
  obtain ⟨-, hn8⟩ := tau_sizes p hp
  obtain ⟨π, hπ⟩ := exists_perm_extending hn8 f hinj
  have hshape := famShape_of_embedding g p hn0 hn8 hsym hirr f hcolf hadjf hdom π hπ
  have hg' : famGraph p (maskOf p (relabel g π)) (cmOf p (relabel g π)) = relabel g π :=
    famGraph_maskOf p (relabel g π) hshape
  -- the recovered masks lie in the enumerated ranges
  have hmask : maskOf p (relabel g π) ∈ List.range (2 ^ (freePairs p.n).length) := by
    rw [List.mem_range]; exact MaskBits.maskUpTo_lt _ _
  have hcm : cmOf p (relabel g π) ∈ List.range (2 ^ (8 - p.n)) := by
    rw [List.mem_range]; exact MaskBits.maskUpTo_lt _ _
  -- C2, unpacked at this member
  have hall := PentagonQComplete.famAllMatch_true
  simp only [PentagonQComplete.famAllMatch, List.all_eq_true] at hall
  have hthis := hall p hp _ hmask _ hcm
  rw [hg'] at hthis
  -- the predicates transport
  have htf' : triangleFreeC (relabel g π) = true := triangleFreeC_relabel g π hsym htf
  have hbi' : blackIndepC (relabel g π) = true := blackIndepC_relabel g π hsym hbi
  simp only [htf', hbi', Bool.and_self, Bool.not_true, Bool.false_or,
    List.any_eq_true] at hthis
  obtain ⟨t, htmem, htcond⟩ := hthis
  obtain ⟨j, hjmem, rfl⟩ := List.mem_map.mp htmem
  refine ⟨j, hjmem, ?_⟩
  -- a non-zero permutation count identifies the classes
  have hperm : PentagonQDistinct.cPermCount (relabel g π) (flagBasisCGraph j) ≠ 0 := by
    simp only [Bool.and_eq_true, bne_iff_ne] at htcond
    exact htcond.2
  have hclass := PentagonQDistinct.genClass_eq_of_cPermCount_ne_zero
    (relabel g π) (flagBasisCGraph j)
    (relabel_symm g π hsym) (relabel_irrefl g π hirr)
    (PentagonQPatFacts.basis_adj_symm j) (PentagonQPatFacts.basis_adj_irrefl j) hperm
  -- and relabelling is itself an isomorphism
  have hrel : GenFlagClass.mk (relabel g π).toGenFlag = GenFlagClass.mk g.toGenFlag :=
    Quotient.sound (relabel_toGenFlag_iso g π)
  rw [← hrel]
  exact hclass

#print axioms famShape_of_embedding
#print axioms is_basis_flag_of_embedding

end PentagonQAssembly
end Davey2024
