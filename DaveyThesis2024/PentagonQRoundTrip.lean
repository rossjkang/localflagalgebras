import DaveyThesis2024.PentagonQFamily
import DaveyThesis2024.MaskBits

/-!
# C3.2: the family round trip

C2 checks every `μ ≠ 0` member of the enumerated family.  To consume it, C3 must
put an arbitrary graph *into* the family: given `g` whose τ-image sits at
`0 … k-1` and whose root dominates the outside — the shape
`PentagonQSpikeC3.exists_perm_extending` arranges — recover the `mask` and `cm`
that generate it.

This is the step the declarative `famAdj`/`famCol` were written for.  Every pair
of vertices falls in exactly one zone — equal, both inside the τ-image, one of
them the root, or a free pair — and the round trip is that case split, with
`MaskBits.testBit_maskUpTo` supplying the last zone.

In a file of its own: `PentagonQFamily` carries a `native_decide` of its own, and
iterating on a proof there would pay it every time.
-/

namespace Davey2024
namespace PentagonQRoundTrip

open Davey2024.PentagonQBasis Davey2024.PentagonQWeights
open Davey2024.PentagonQFamily Davey2024.MaskBits

/-- `Nat`-indexed adjacency, `false` out of range. -/
def adjN (g : CGraph 8) (i j : Nat) : Bool :=
  if h : i < 8 ∧ j < 8 then g.adj ⟨i, h.1⟩ ⟨j, h.2⟩ else false

/-- `Nat`-indexed colour, `0` out of range. -/
def colN (g : CGraph 8) (v : Nat) : Fin 2 :=
  if h : v < 8 then g.col ⟨v, h⟩ else 0

/-- The shape `exists_perm_extending` arranges: the τ-image at `0 … k-1`, the
root joined to everything outside it, and the graph symmetric and loopless. -/
structure FamShape (p : Pat) (g : CGraph 8) : Prop where
  size : 0 < p.n ∧ p.n ≤ 8
  irrefl : ∀ i, adjN g i i = false
  symm : ∀ i j, adjN g i j = adjN g j i
  inner : ∀ i j, i < p.n → j < p.n → adjN g i j = (p.padj[i]!)[j]!
  root : ∀ j, p.n ≤ j → j < 8 → adjN g 0 j = true
  cols : ∀ v, v < p.n → colN g v = (if p.cols[v]! == 1 then 1 else 0)

/-- The mask `g`'s free pairs determine. -/
def maskOf (p : Pat) (g : CGraph 8) : Nat :=
  maskUpTo (fun idx =>
    adjN g ((freePairs p.n)[idx]!).1 ((freePairs p.n)[idx]!).2)
    (freePairs p.n).length

/-- The colour mask `g`'s outside vertices determine. -/
def cmOf (p : Pat) (g : CGraph 8) : Nat :=
  maskUpTo (fun idx => colN g (p.n + idx) == 1) (8 - p.n)

/-- Every pair that reaches `famAdj`'s last branch really is a free pair. -/
theorem mem_freePairs {k a b : Nat} (hk : 0 < k) (ha1 : 1 ≤ a) (hab : a < b)
    (hb : b < 8) (hnot : ¬(a < k ∧ b < k)) : (a, b) ∈ freePairs k := by
  have hbk : k ≤ b := by by_contra h; exact hnot ⟨by omega, by omega⟩
  simp only [freePairs, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_filter, List.mem_range', decide_eq_true_eq]
  by_cases hak : k ≤ a
  · exact Or.inl ⟨a, ⟨a - k, by omega, by omega⟩, b, ⟨⟨b - k, by omega, by omega⟩, hab⟩, rfl⟩
  · exact Or.inr ⟨b, ⟨b - k, by omega, by omega⟩, a, ⟨a - 1, by omega, by omega⟩, rfl⟩

/-- **C3.2.**  A graph of the family shape is the family member its own free
pairs and outside colours name. -/
theorem famGraph_maskOf (p : Pat) (g : CGraph 8) (h : FamShape p g) :
    famGraph p (maskOf p g) (cmOf p g) = g := by
  obtain ⟨⟨hk0, hk8⟩, hirr, hsym, hin, hrt, hcl⟩ := h
  have hadj : ∀ i j : Fin 8, famAdj p (maskOf p g) i.val j.val = adjN g i.val j.val := by
    intro i j
    unfold famAdj
    split_ifs with h1 h2 h3
    · have : i.val = j.val := by simpa using h1
      rw [this, hirr]
    · have h2' : i.val < p.n ∧ j.val < p.n := by
        simpa [Bool.and_eq_true] using h2
      exact (hin _ _ h2'.1 h2'.2).symm
    · have h2' : ¬(i.val < p.n ∧ j.val < p.n) := by
        simpa [Bool.and_eq_true] using h2
      have h3' : i.val = 0 ∨ j.val = 0 := by simpa using h3
      rcases h3' with h' | h'
      · rw [h'] at h2' ⊢
        have : p.n ≤ j.val := by by_contra hc; exact h2' ⟨by omega, by omega⟩
        exact (hrt _ this j.isLt).symm
      · rw [h'] at h2' ⊢
        rw [hsym]
        have : p.n ≤ i.val := by by_contra hc; exact h2' ⟨by omega, by omega⟩
        exact (hrt _ this i.isLt).symm
    · have h2' : ¬(i.val < p.n ∧ j.val < p.n) := by
        simpa [Bool.and_eq_true] using h2
      have h3' : ¬(i.val = 0 ∨ j.val = 0) := by simpa using h3
      have h1' : i.val ≠ j.val := by simpa using h1
      push_neg at h3'
      have hmem : (min i.val j.val, max i.val j.val) ∈ freePairs p.n := by
        refine mem_freePairs hk0 ?_ ?_ ?_ ?_
        · omega
        · omega
        · have := i.isLt; have := j.isLt; omega
        · rintro ⟨u, v⟩; exact h2' ⟨by omega, by omega⟩
      have hlt : (freePairs p.n).idxOf (min i.val j.val, max i.val j.val)
          < (freePairs p.n).length := List.idxOf_lt_length_iff.mpr hmem
      unfold maskOf
      rw [testBit_maskUpTo _ _ _ hlt]
      have hget : (freePairs p.n)[(freePairs p.n).idxOf
          (min i.val j.val, max i.val j.val)]! = (min i.val j.val, max i.val j.val) := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        simp [List.getElem_idxOf hlt]
      rw [hget]
      rcases Nat.lt_or_ge i.val j.val with h' | h'
      · rw [Nat.min_eq_left h'.le, Nat.max_eq_right h'.le]
      · have hji : j.val < i.val := by omega
        rw [Nat.min_eq_right hji.le, Nat.max_eq_left hji.le, hsym]
  have hcol : ∀ v : Fin 8, famCol p (cmOf p g) v.val = colN g v.val := by
    intro v
    unfold famCol
    by_cases h1 : v.val < p.n
    · rw [if_pos h1]; exact (hcl _ h1).symm
    · rw [if_neg h1]
      have hpv : p.n + (v.val - p.n) = v.val := by omega
      have hbit : (cmOf p g).testBit (v.val - p.n) = (colN g v.val == 1) := by
        unfold cmOf
        rw [testBit_maskUpTo _ _ _ (by have := v.isLt; omega), hpv]
      rw [hbit]
      by_cases hc : colN g v.val = 1
      · simp [hc]
      · have hz : (colN g v.val).val = 0 := by
          have h2 := (colN g v.val).isLt
          have h3 : (colN g v.val).val ≠ 1 := fun hx => hc (Fin.ext hx)
          omega
        simp [hc, (Fin.ext hz : colN g v.val = 0)]
  have key : ∀ i j : Fin 8, (famGraph p (maskOf p g) (cmOf p g)).adj i j = g.adj i j := by
    intro i j
    have := hadj i j
    simpa [famGraph, adjN, i.isLt, j.isLt] using this
  have keyc : ∀ v : Fin 8, (famGraph p (maskOf p g) (cmOf p g)).col v = g.col v := by
    intro v
    have := hcol v
    simpa [famGraph, colN, v.isLt] using this
  cases g with
  | mk a c =>
    simp only [famGraph, CGraph.mk.injEq]
    exact ⟨funext fun i => funext fun j => key i j, funext fun v => keyc v⟩

#print axioms famGraph_maskOf

end PentagonQRoundTrip
end Davey2024
