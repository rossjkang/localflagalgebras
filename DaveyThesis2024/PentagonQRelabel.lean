import DaveyThesis2024.PentagonQRooted
import DaveyThesis2024.PentagonQFamily
import DaveyThesis2024.PentagonQPatFacts

/-!
# C3.3: relabelling, and what survives it

The τ-anchored WLOG moves the τ-image to `0 … k-1` by a permutation of the
vertices (`PentagonQSpikeC3.exists_perm_extending`).  Everything C2 tests of a
family member — triangle-freeness, black-independence, `μ ≠ 0` — therefore has to
survive relabelling.

Triangle-freeness and black-independence are immediate.  `μ` is the one that
needs an argument, and it is the one obligation (a0) makes possible: `μ` is a
weighted sum of `rootedCount`s, `rootedCount` is a `countP` over a hand-rolled
enumerator, and nothing relates *that* to relabelling — but (a0) proved it equals
`cRootedCount`, a `Finset.filter` over honest maps, and a filter transports by
composing with the permutation.
-/

namespace Davey2024
namespace PentagonQRelabel

open Finset
open Davey2024.PentagonQBasis Davey2024.PentagonQWeights
open Davey2024.PentagonQRooted Davey2024.PentagonQFamily

/-- Relabel a graph's vertices by `π`. -/
def relabel (g : CGraph 8) (π : Equiv.Perm (Fin 8)) : CGraph 8 where
  adj i j := g.adj (π i) (π j)
  col v := g.col (π v)

/-- **The rooted count is relabelling-invariant.**  Composing an embedding with
`π` is a bijection between the two filtered sets: it matches colours and
adjacencies by definition of `relabel`, and carries the root condition because
`π` is a bijection of the vertex set, so "outside the image" is preserved. -/
theorem cRootedCount_relabel {m : Nat} (F : CGraph (m + 1)) (g : CGraph 8)
    (π : Equiv.Perm (Fin 8)) :
    cRootedCount F (relabel g π) = cRootedCount F g := by
  classical
  unfold cRootedCount
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  refine Fintype.card_congr {
    toFun := fun x => ⟨fun i => π (x.1 i), ?_, ?_, ?_, ?_⟩
    invFun := fun y => ⟨fun i => π.symm (y.1 i), ?_, ?_, ?_, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · exact fun a b h => x.2.1 a b (π.injective h)
  · exact fun i => x.2.2.1 i
  · exact fun i j => x.2.2.2.1 i j
  · intro w hw
    have hw' : ∀ i, x.1 i ≠ π.symm w := by
      intro i hi
      exact hw i (by simp [hi])
    have := x.2.2.2.2 (π.symm w) hw'
    simpa [relabel, Equiv.apply_symm_apply] using this
  · exact fun a b h => y.2.1 a b (π.symm.injective h)
  · intro i
    have := y.2.2.1 i
    simpa [relabel] using this
  · intro i j
    have := y.2.2.2.1 i j
    simpa [relabel] using this
  · intro w hw
    have hw' : ∀ i, y.1 i ≠ π w := by
      intro i hi
      exact hw i (by simp [hi])
    have := y.2.2.2.2 (π w) hw'
    simpa [relabel] using this
  · intro x; ext i; simp
  · intro y; ext i; simp

/-! ## The predicate transports

Both `triangleFreeC` and `blackIndepC` guard on the *index* order, which a
permutation does not preserve: a triangle at `a < b < c` maps to one at three
distinct but unsorted images.  Each therefore goes through an unordered form
first, whose proof is the sort the guard hides. -/

/-- The ordered guard, unpacked. -/
private theorem tri_ordered {g : CGraph 8} (h : triangleFreeC g = true)
    (x y z : Fin 8) (hxy : x.val < y.val) (hyz : y.val < z.val) :
    ¬(g.adj x y = true ∧ g.adj y z = true ∧ g.adj x z = true) := by
  rintro ⟨e1, e2, e3⟩
  unfold triangleFreeC at h
  simp only [List.all_eq_true, List.mem_finRange, forall_const] at h
  have hxyz := h x y z
  simp [hxy, hyz, e1, e2, e3] at hxyz

/-- **Triangle-freeness, unordered.**  For a symmetric graph the index guard
costs nothing: any triangle can be sorted, and symmetry supplies the three edges
in whatever order the sort produces. -/
theorem no_triangle {g : CGraph 8} (hs : ∀ i j, g.adj i j = g.adj j i)
    (h : triangleFreeC g = true) (a b c : Fin 8) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) (e1 : g.adj a b = true) (e2 : g.adj b c = true)
    (e3 : g.adj a c = true) : False := by
  have hab' : a.val ≠ b.val := fun hx => hab (Fin.ext hx)
  have hbc' : b.val ≠ c.val := fun hx => hbc (Fin.ext hx)
  have hac' : a.val ≠ c.val := fun hx => hac (Fin.ext hx)
  rcases Nat.lt_or_ge a.val b.val with h1 | h1
  · rcases Nat.lt_or_ge b.val c.val with h2 | h2
    · exact tri_ordered h a b c h1 h2 ⟨e1, e2, e3⟩
    · have h2 : c.val < b.val := by omega
      rcases Nat.lt_or_ge a.val c.val with h3 | h3
      · exact tri_ordered h a c b h3 h2 ⟨e3, (hs c b).trans e2, e1⟩
      · have h3 : c.val < a.val := by omega
        exact tri_ordered h c a b h3 h1 ⟨(hs c a).trans e3, e1, (hs c b).trans e2⟩
  · have h1 : b.val < a.val := by omega
    rcases Nat.lt_or_ge a.val c.val with h2 | h2
    · exact tri_ordered h b a c h1 h2 ⟨(hs b a).trans e1, e3, e2⟩
    · have h2 : c.val < a.val := by omega
      rcases Nat.lt_or_ge b.val c.val with h3 | h3
      · exact tri_ordered h b c a h3 h2 ⟨e2, (hs c a).trans e3, (hs b a).trans e1⟩
      · have h3 : c.val < b.val := by omega
        exact tri_ordered h c b a h3 h1 ⟨(hs c b).trans e2, (hs b a).trans e1, (hs c a).trans e3⟩

/-- Triangle-freeness survives relabelling. -/
theorem triangleFreeC_relabel (g : CGraph 8) (π : Equiv.Perm (Fin 8))
    (hs : ∀ i j, g.adj i j = g.adj j i) (h : triangleFreeC g = true) :
    triangleFreeC (relabel g π) = true := by
  unfold triangleFreeC
  simp only [List.all_eq_true, List.mem_finRange, forall_const]
  intro a b c
  simp only [Bool.not_eq_true']
  by_contra hcon
  simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hcon
  obtain ⟨⟨⟨⟨hab, hbc⟩, e1⟩, e2⟩, e3⟩ := hcon
  have hne : ∀ x y : Fin 8, x.val < y.val → π x ≠ π y := by
    intro x y hxy hx
    exact absurd (congrArg Fin.val (π.injective hx)) (by omega)
  exact no_triangle hs h (π a) (π b) (π c) (hne a b hab) (hne b c hbc)
    (hne a c (by omega)) e1 e2 e3

/-- Black-independence survives relabelling: the same sort, with two cases. -/
theorem blackIndepC_relabel (g : CGraph 8) (π : Equiv.Perm (Fin 8))
    (hs : ∀ i j, g.adj i j = g.adj j i) (h : blackIndepC g = true) :
    blackIndepC (relabel g π) = true := by
  have hpair : ∀ x y : Fin 8, x ≠ y → g.adj x y = true → g.col x = 1 → g.col y = 1 → False := by
    intro x y hxy e c1 c2
    have hord : ∀ u v : Fin 8, u.val < v.val → g.adj u v = true → g.col u = 1 →
        g.col v = 1 → False := by
      intro u v huv e' d1 d2
      unfold blackIndepC at h
      simp only [List.all_eq_true, List.mem_finRange, forall_const] at h
      have := h u v
      simp [huv, e', d1, d2] at this
    have hxy' : x.val ≠ y.val := fun hx => hxy (Fin.ext hx)
    rcases Nat.lt_or_ge x.val y.val with h1 | h1
    · exact hord x y h1 e c1 c2
    · exact hord y x (by omega) ((hs y x).trans e) c2 c1
  unfold blackIndepC
  simp only [List.all_eq_true, List.mem_finRange, forall_const]
  intro a b
  by_contra hcon
  simp only [Bool.not_eq_true, Bool.not_eq_false] at hcon
  have hpos : (decide (a.val < b.val) && (relabel g π).adj a b &&
      ((relabel g π).col a == 1) && ((relabel g π).col b == 1)) = true := by
    simpa using hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpos
  obtain ⟨⟨⟨hab, e⟩, c1⟩, c2⟩ := hpos
  exact hpair (π a) (π b) (fun hx => absurd (congrArg Fin.val (π.injective hx)) (by omega))
    e c1 c2

/-! ## Relabelling is an isomorphism of flags

The assembly ends by carrying a match on the *relabelled* graph back to the
original, so the relabelling has to be a `GenFlagIso`.  It is, with `π` itself as
the vertex bijection: `comap` of `fromRel` is `fromRel` of the composite, the
inequality `fromRel` inserts transports because `π` is injective, and the colour
component is `rfl`. -/

theorem relabel_toGenFlag_iso (g : CGraph 8) (π : Equiv.Perm (Fin 8)) :
    GenFlagIso (GenFlagType.empty CG2) (relabel g π).toGenFlag g.toGenFlag := by
  refine ⟨π, ?_, fun i => i.elim0⟩
  refine Prod.ext_iff.mpr ⟨?_, rfl⟩
  ext u v
  simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj, CGraph.toGenFlag, relabel]
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨fun hx => hne (by rw [hx]), h⟩
  · rintro ⟨hne, h⟩
    exact ⟨fun hx => hne (π.injective hx), h⟩

/-! ## The τ patterns' basic facts

`FamShape.size` needs the pattern sizes.  The τ patterns' symmetry and
irreflexivity — which `comap_iff_of_injective` requires — are in
`PentagonQPatFacts`, kept separate because `patC` indexes an `Array` built by
`Array.map`, which the kernel will not reduce, so they need `native_decide` and
this module stays kernel-only without them. -/

/-- Finding I, the easy half: the family's members have no loops. -/
theorem famGraph_irrefl (p : Pat) (mask cm : Nat) (i : Fin 8) :
    (famGraph p mask cm).adj i i = false := by
  simp [famGraph, famAdj]

/-- **Finding I.**  The family's members are symmetric.  Four zones: the
diagonal, the τ-image (which needs the pattern's own symmetry — finding D), the
root's edges, and the free pairs, whose `(min, max)` lookup is symmetric by
construction. -/
theorem famGraph_symm (p : Pat) (hp : p ∈ [tau1, tau2, tau3]) (mask cm : Nat)
    (i j : Fin 8) :
    (famGraph p mask cm).adj i j = (famGraph p mask cm).adj j i := by
  have hpat : ∀ a b : Nat, a < p.n → b < p.n → (p.padj[a]!)[b]! = (p.padj[b]!)[a]! := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact fun a b ha hb => PentagonQPatFacts.patC_tau1_symm ⟨a, ha⟩ ⟨b, hb⟩
    · exact fun a b ha hb => PentagonQPatFacts.patC_tau2_symm ⟨a, ha⟩ ⟨b, hb⟩
    · exact fun a b ha hb => PentagonQPatFacts.patC_tau3_symm ⟨a, ha⟩ ⟨b, hb⟩
  show famAdj p mask i.val j.val = famAdj p mask j.val i.val
  unfold famAdj
  by_cases h : i.val = j.val
  · rw [h]
  · have h' : ¬(j.val = i.val) := fun hx => h hx.symm
    simp only [beq_iff_eq, h, h', if_false]
    by_cases hb : i.val < p.n ∧ j.val < p.n
    · have e1 : (decide (i.val < p.n) && decide (j.val < p.n)) = true := by simp [hb.1, hb.2]
      have e2 : (decide (j.val < p.n) && decide (i.val < p.n)) = true := by simp [hb.1, hb.2]
      simp only [e1, e2, if_true, Bool.true_eq]
      exact hpat _ _ hb.1 hb.2
    · have e1 : (decide (i.val < p.n) && decide (j.val < p.n)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        by_contra hc
        push_neg at hc
        exact hb ⟨by omega, by omega⟩
      have e2 : (decide (j.val < p.n) && decide (i.val < p.n)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        by_contra hc
        push_neg at hc
        exact hb ⟨by omega, by omega⟩
      by_cases hz : i.val = 0 ∨ j.val = 0
      · have z1 : (i.val == 0 || j.val == 0) = true := by
          rcases hz with hx | hx <;> simp [hx]
        have z2 : (j.val == 0 || i.val == 0) = true := by
          rcases hz with hx | hx <;> simp [hx]
        simp [e1, e2, z1, z2]
      · push_neg at hz
        have z1 : (i.val == 0 || j.val == 0) = false := by simp [hz.1, hz.2]
        have z2 : (j.val == 0 || i.val == 0) = false := by simp [hz.1, hz.2]
        simp [e1, e2, z1, z2, Nat.min_comm i.val j.val, Nat.max_comm i.val j.val]

/-- **F.**  The three pattern sizes lie in range. -/
theorem tau_sizes : ∀ p ∈ [tau1, tau2, tau3], 0 < p.n ∧ p.n ≤ 8 := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

/-! ## What is *not* here
Extracting the τ-embedding from `μ ≠ 0`, which needs
`PentagonQWeightsBridge.rootedCount_eq_cRootedCount` (proved, ~2 h), and the
assembly of C2 + C3.1 + C3.2 + C3.3 into the statement about an abstract host.
-/

#print axioms cRootedCount_relabel
#print axioms triangleFreeC_relabel
#print axioms blackIndepC_relabel
#print axioms relabel_toGenFlag_iso
#print axioms tau_sizes
#print axioms famGraph_symm
#print axioms famGraph_irrefl

end PentagonQRelabel
end Davey2024
