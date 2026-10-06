import DaveyThesis2024.StrongEdgeColouring
import DaveyThesis2024.SecBridge
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.PrimeCounting

/-!
# The affine-plane incidence family

A `p`-regular bipartite C₄-free family, for the non-vacuity of the general and
bipartite SEC bridge axioms (Group 3 of the audit's regression plan).

`K_{n,n}` cannot serve those two: every pair of its edges at distance one lies in
a 4-cycle, so an edge has only `≈ Δ²` strong neighbours, short of the `1.7297 Δ²`
the gates demand. The reachable maximum is `≈ 2Δ²`, and attaining it needs a
family with no 4-cycles.

**The construction.** Points and lines of the affine plane over `ZMod p`, minus
the vertical lines: both sides are `ZMod p × ZMod p`, and the point `(x, y)` is
incident to the line `(m, c)` when `y = m * x + c`. This is `p`-regular (a point
lies on one line of each slope; a line carries one point over each abscissa) and
C₄-free (two distinct points lie on at most one common line — where the field
inverse is used).

Vertices live in a sum type here and are transported to `Fin (2 * p * p)` only at
the end, since every count is far easier on the sum.

## Status

**Done here:** the graph, its adjacency characterisation, `p`-regularity
(`affFlag_isRegular`, `affFlag_maxDegree`), C₄-freeness in both forms
(`line_unique`, `point_unique`), and bipartiteness (`adj_cross`).  All on the
three standard kernel axioms.

**Not done here:** the strong-degree bound that the two gates actually ask for,

```
∀ e ∈ F, 17297 * Δ² ≤ 10000 * strongFDegree G F e
```

with `F` the whole edge set.  The combinatorics is settled — `lineGraphSqAdj` is
distance `≤ 2` in `L(G)`, so for an edge `e = {P, L}` the strong neighbours are

* the `p - 1` other lines through `P`, and the `p - 1` other points on `L`;
* for each of the `p - 1` lines `L' ∋ P` with `L' ≠ L`, the `p - 1` edges of `L'`
  other than `{P, L'}`;
* for each of the `p - 1` points `P' ∈ L` with `P' ≠ P`, the `p - 1` edges
  through `P'` other than `{P', L}`;

and the last two families are **disjoint**: an edge `{A, B}` in both would put
`A` and `P` on both `L` and `B`, two distinct lines through two distinct points,
which `line_unique` forbids.  That totals

```
2(p-1) + 2(p-1)² = 2p(p-1) = 2p² - 2p,
```

and `10000 · (2p² - 2p) ≥ 17297 · p²` reduces to `2703 p ≥ 20000`, i.e. `p ≥ 8`
— so primes `p ≥ 11`.  What remains is to carry that count through the
`edgeFinset`/`equivFin` encoding `lineGraphSqFlag` uses, which is where the work
is, and then to assemble the two sequences and the four non-vacuity theorems.
-/

namespace Davey2024
namespace AffinePlaneFamily

open Finset
open scoped Classical

variable (p : ℕ)

/-- Points on the left, lines on the right. -/
abbrev Pt := ZMod p × ZMod p
abbrev V := Pt p ⊕ Pt p

/-- Incidence: the point `(x, y)` lies on the line `(m, c)` iff `y = m * x + c`. -/
def onLine (P L : Pt p) : Prop := P.2 = L.1 * P.1 + L.2

/-- The incidence relation, oriented point-to-line. -/
def affRel : V p → V p → Prop
  | Sum.inl P, Sum.inr L => onLine p P L
  | _, _ => False

/-- The incidence graph. -/
def affGraph : SimpleGraph (V p) := SimpleGraph.fromRel (affRel p)

variable {p}

/-- Adjacency is incidence, in whichever orientation. -/
lemma affGraph_adj_iff (u v : V p) :
    (affGraph p).Adj u v ↔
      (∃ P L, u = Sum.inl P ∧ v = Sum.inr L ∧ onLine p P L) ∨
      (∃ P L, u = Sum.inr L ∧ v = Sum.inl P ∧ onLine p P L) := by
  unfold affGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · cases u with
      | inl P => cases v with
        | inl Q => exact absurd h (by unfold affRel; exact not_false)
        | inr L => exact Or.inl ⟨P, L, rfl, rfl, h⟩
      | inr L => cases v with
        | inl P => exact absurd h (by unfold affRel; exact not_false)
        | inr M => exact absurd h (by unfold affRel; exact not_false)
    · cases u with
      | inl P => cases v with
        | inl Q => exact absurd h (by unfold affRel; exact not_false)
        | inr L => exact absurd h (by unfold affRel; exact not_false)
      | inr L => cases v with
        | inl P => exact Or.inr ⟨P, L, rfl, rfl, h⟩
        | inr M => exact absurd h (by unfold affRel; exact not_false)
  · rintro (⟨P, L, rfl, rfl, h⟩ | ⟨P, L, rfl, rfl, h⟩)
    · exact ⟨by simp, Or.inl h⟩
    · exact ⟨by simp, Or.inr h⟩

/-- A point is adjacent exactly to the lines through it. -/
lemma adj_inl_iff (P : Pt p) (v : V p) :
    (affGraph p).Adj (Sum.inl P) v ↔ ∃ L, v = Sum.inr L ∧ onLine p P L := by
  rw [affGraph_adj_iff]
  constructor
  · rintro (⟨P', L, hu, rfl, h⟩ | ⟨P', L, hu, -, -⟩)
    · obtain rfl : P = P' := by simpa using hu
      exact ⟨L, rfl, h⟩
    · exact absurd hu (by simp)
  · rintro ⟨L, rfl, h⟩
    exact Or.inl ⟨P, L, rfl, rfl, h⟩

/-- A line is adjacent exactly to the points on it. -/
lemma adj_inr_iff (L : Pt p) (v : V p) :
    (affGraph p).Adj (Sum.inr L) v ↔ ∃ P, v = Sum.inl P ∧ onLine p P L := by
  rw [affGraph_adj_iff]
  constructor
  · rintro (⟨P, L', hu, -, -⟩ | ⟨P, L', hu, rfl, h⟩)
    · exact absurd hu (by simp)
    · obtain rfl : L = L' := by simpa using hu
      exact ⟨P, rfl, h⟩
  · rintro ⟨P, rfl, h⟩
    exact Or.inr ⟨P, L, rfl, rfl, h⟩

/-! ## Regularity

A point lies on exactly one line of each slope; a line carries exactly one point
over each abscissa. Both neighbourhoods are therefore images of `ZMod p` under an
injection, so both degrees are `p`. -/

variable (p)

/-- The lines through a point, indexed by slope. -/
lemma nbrs_inl [NeZero p] (P : Pt p) :
    (univ.filter fun v => (affGraph p).Adj (Sum.inl P) v)
      = univ.image (fun m : ZMod p => (Sum.inr (m, P.2 - m * P.1) : V p)) := by
  classical
  ext v
  simp only [mem_filter, mem_univ, true_and, mem_image, adj_inl_iff]
  constructor
  · rintro ⟨L, rfl, h⟩
    refine ⟨L.1, ?_⟩
    unfold onLine at h
    have h2 : L.2 = P.2 - L.1 * P.1 := by linear_combination -h
    simp [Prod.ext_iff, h2]
  · rintro ⟨m, rfl⟩
    exact ⟨(m, P.2 - m * P.1), rfl, by show P.2 = m * P.1 + (P.2 - m * P.1); ring⟩

/-- The points on a line, indexed by abscissa. -/
lemma nbrs_inr [NeZero p] (L : Pt p) :
    (univ.filter fun v => (affGraph p).Adj (Sum.inr L) v)
      = univ.image (fun x : ZMod p => (Sum.inl (x, L.1 * x + L.2) : V p)) := by
  classical
  ext v
  simp only [mem_filter, mem_univ, true_and, mem_image, adj_inr_iff]
  constructor
  · rintro ⟨P, rfl, h⟩
    refine ⟨P.1, ?_⟩
    unfold onLine at h
    simp [h.symm]
  · rintro ⟨x, rfl⟩
    exact ⟨(x, L.1 * x + L.2), rfl, rfl⟩

lemma degree_inl [NeZero p] (P : Pt p) :
    (univ.filter fun v => (affGraph p).Adj (Sum.inl P) v).card = p := by
  classical
  have hinj : Function.Injective (fun m : ZMod p => (Sum.inr (m, P.2 - m * P.1) : V p)) := by
    intro a b hab
    exact congrArg Prod.fst (Sum.inr.inj hab)
  rw [nbrs_inl, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]

lemma degree_inr [NeZero p] (L : Pt p) :
    (univ.filter fun v => (affGraph p).Adj (Sum.inr L) v).card = p := by
  classical
  have hinj : Function.Injective (fun x : ZMod p => (Sum.inl (x, L.1 * x + L.2) : V p)) := by
    intro a b hab
    exact congrArg Prod.fst (Sum.inl.inj hab)
  rw [nbrs_inr, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]

/-- Every vertex has degree `p`. -/
lemma degree_eq [NeZero p] (v : V p) :
    (univ.filter fun u => (affGraph p).Adj v u).card = p := by
  cases v with
  | inl P => exact degree_inl p P
  | inr L => exact degree_inr p L

/-! ## No four-cycles

Two distinct points lie on at most one common line. This is the one place the
field structure of `ZMod p` is used, and it is what separates this family from
`K_{n,n}`: it is why an edge has `≈ 2Δ²` strong neighbours rather than `≈ Δ²`. -/

variable {p}

/-- **Two distinct points determine at most one line.** -/
theorem line_unique [Fact p.Prime] {P P' L L' : Pt p} (hne : P ≠ P')
    (h1 : onLine p P L) (h2 : onLine p P' L)
    (h3 : onLine p P L') (h4 : onLine p P' L') : L = L' := by
  unfold onLine at h1 h2 h3 h4
  -- Subtracting the two pairs kills the intercepts and leaves a product of differences.
  have key : (L.1 - L'.1) * (P.1 - P'.1) = 0 := by linear_combination -h1 + h2 + h3 - h4
  rcases mul_eq_zero.mp key with hm | hx
  · -- equal slopes, hence equal intercepts
    have hslope : L.1 = L'.1 := by linear_combination hm
    have hint : L.2 = L'.2 := by linear_combination -h1 + h3 - P.1 * hslope
    exact Prod.ext hslope hint
  · -- equal abscissae would force the two points to coincide
    exfalso
    have hx' : P.1 = P'.1 := by linear_combination hx
    exact hne (Prod.ext hx' (by linear_combination h1 - h2 + L.1 * hx'))

/-- **Two distinct lines meet in at most one point** — the dual statement, proved
the same way and used in the same count. -/
theorem point_unique [Fact p.Prime] {P P' L L' : Pt p} (hne : L ≠ L')
    (h1 : onLine p P L) (h2 : onLine p P L')
    (h3 : onLine p P' L) (h4 : onLine p P' L') : P = P' := by
  by_contra hPP
  exact hne (line_unique hPP h1 h3 h2 h4)

/-! ## Bipartiteness -/

/-- Points are never adjacent to points, lines never to lines. -/
theorem adj_cross {u v : V p} (h : (affGraph p).Adj u v) :
    (∃ P L, u = Sum.inl P ∧ v = Sum.inr L) ∨ (∃ P L, u = Sum.inr L ∧ v = Sum.inl P) := by
  rcases (affGraph_adj_iff u v).mp h with ⟨P, L, hu, hv, -⟩ | ⟨P, L, hu, hv, -⟩
  · exact Or.inl ⟨P, L, hu, hv⟩
  · exact Or.inr ⟨P, L, hu, hv⟩

/-! ## Transport to a `Flag`

`Flag` carries its vertices in `Fin size`, so the sum type is transported along a
cardinality equivalence. Comap along an equivalence is a graph isomorphism, so
every degree is carried across unchanged. -/

variable (p)

lemma card_V [NeZero p] : Fintype.card (V p) = 2 * p * p := by
  simp [V, Pt, Fintype.card_sum, ZMod.card]
  ring

/-- A relabelling of the affine incidence graph onto `Fin (2 * p * p)`. -/
noncomputable def vEquiv [NeZero p] : Fin (2 * p * p) ≃ V p :=
  (Fintype.equivFinOfCardEq (card_V p)).symm

/-- The affine incidence graph on `Fin (2 * p * p)`. -/
noncomputable def affGraphFin [NeZero p] : SimpleGraph (Fin (2 * p * p)) :=
  (affGraph p).comap (vEquiv p)

/-- The affine incidence family as a `Flag emptyType`. -/
noncomputable def affFlag [NeZero p] : Flag emptyType where
  size := 2 * p * p
  graph := affGraphFin p
  embedding := ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
  hsize := Nat.zero_le _

@[simp] lemma affFlag_size [NeZero p] : (affFlag p).size = 2 * p * p := rfl

variable {p}

lemma affFlag_adj_iff [NeZero p] (u v : Fin (affFlag p).size) :
    (affFlag p).graph.Adj u v ↔ (affGraph p).Adj (vEquiv p u) (vEquiv p v) := Iff.rfl

/-- Degrees transfer along the relabelling. -/
lemma affFlag_degree [NeZero p] (v : Fin (affFlag p).size) :
    ((univ : Finset (Fin (affFlag p).size)).filter
      fun u => (affFlag p).graph.Adj v u).card = p := by
  classical
  have himg : ((univ : Finset (Fin (affFlag p).size)).filter
      fun u => (affFlag p).graph.Adj v u)
      = ((univ : Finset (V p)).filter
          fun w => (affGraph p).Adj (vEquiv p v) w).image (vEquiv p).symm := by
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_image, affFlag_adj_iff]
    constructor
    · intro h
      exact ⟨vEquiv p u, by simpa using h, by simp⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  rw [himg]
  rw [Finset.card_image_of_injective _ (vEquiv p).symm.injective]
  exact degree_eq p _

variable (p)

/-- The family is `p`-regular. -/
theorem affFlag_maxDegree [NeZero p] (hp : 0 < p) : maxDegree (affFlag p) = p := by
  classical
  have hpos : (0 : ℕ) < (affFlag p).size := by
    change 0 < 2 * p * p
    have := Nat.pos_of_ne_zero (NeZero.ne p)
    positivity
  unfold maxDegree
  refine le_antisymm (Finset.sup_le fun v _ => le_of_eq (affFlag_degree v)) ?_
  refine le_trans ?_ (Finset.le_sup (Finset.mem_univ (⟨0, hpos⟩ : Fin (affFlag p).size)))
  exact le_of_eq (affFlag_degree _).symm

theorem affFlag_isRegular [NeZero p] (hp : 0 < p) : IsRegular (affFlag p) := by
  intro v
  rw [affFlag_maxDegree p hp]
  exact affFlag_degree v

/-! ## A bridge to `strongFDegree`

`lineGraphSqFlag` indexes its vertices by `(edgeFinset G).equivFin`, so every
count has to be pushed through that equivalence.  This lemma does it once, in
graph-agnostic form: any injectively-indexed family of edges, each `L(G)²`-adjacent
to `e`, bounds `e`'s strong degree from below. -/

open Davey2024.SecBridge in
/-- **The counting bridge.**  An injection into the `L(G)²`-neighbourhood of `i`
bounds `strongFDegree G univ i` from below. -/
lemma card_le_strongFDegree {G : Flag emptyType} (i : Fin (lineGraphSqFlag G).size)
    {ι : Type*} (T : Finset ι) (f : ι → Fin G.size × Fin G.size)
    (hmem : ∀ t ∈ T, f t ∈ edgeFinset G)
    (hadj : ∀ t ∈ T, lineGraphSqAdj G ((edgeFinset G).equivFin.symm i).val (f t))
    (hinj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, f t₁ = f t₂ → t₁ = t₂) :
    T.card ≤ strongFDegree G Finset.univ i := by
  classical
  unfold strongFDegree
  set g : {x // x ∈ T} → Fin (lineGraphSqFlag G).size :=
    fun t => (edgeFinset G).equivFin ⟨f t.1, hmem t.1 t.2⟩ with hg
  have hginj : Function.Injective g := by
    intro a b hab
    have hval : f a.1 = f b.1 := by
      have h := congrArg (edgeFinset G).equivFin.symm hab
      simp only [hg, Equiv.symm_apply_apply] at h
      exact congrArg Subtype.val h
    exact Subtype.ext (hinj a.1 a.2 b.1 b.2 hval)
  have hsub : T.attach.image g ⊆
      (Finset.univ : Finset (Fin (lineGraphSqFlag G).size)).filter
        fun j => (lineGraphSqFlag G).graph.Adj i j := by
    intro j hj
    simp only [Finset.mem_image] at hj
    obtain ⟨t, -, rfl⟩ := hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show lineGraphSqAdj G _ _
    simpa [hg, Equiv.symm_apply_apply] using hadj t.1 t.2
  calc T.card = T.attach.card := (Finset.card_attach).symm
    _ = (T.attach.image g).card := (Finset.card_image_of_injective _ hginj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ## Edges of the affine family, canonically oriented

`edgeFinset` stores an edge as the ordered pair with the smaller index first, and
the relabelling `vEquiv` has nothing to do with that order, so incidences are
turned into edges through an explicit `canon`. -/

/-- The index of a point. -/
noncomputable def ptIdx [NeZero p] (P : Pt p) : Fin (affFlag p).size :=
  (vEquiv p).symm (Sum.inl P)

/-- The index of a line. -/
noncomputable def lnIdx [NeZero p] (L : Pt p) : Fin (affFlag p).size :=
  (vEquiv p).symm (Sum.inr L)

variable {p}

lemma ptIdx_ne_lnIdx [NeZero p] (P L : Pt p) : ptIdx p P ≠ lnIdx p L := by
  intro h
  exact absurd ((vEquiv p).symm.injective h) (by simp)

lemma ptIdx_inj [NeZero p] {P P' : Pt p} (h : ptIdx p P = ptIdx p P') : P = P' := by
  simpa using (vEquiv p).symm.injective h

lemma lnIdx_inj [NeZero p] {L L' : Pt p} (h : lnIdx p L = lnIdx p L') : L = L' := by
  simpa using (vEquiv p).symm.injective h

lemma adj_ptIdx_lnIdx [NeZero p] {P L : Pt p} (h : onLine p P L) :
    (affFlag p).graph.Adj (ptIdx p P) (lnIdx p L) := by
  rw [affFlag_adj_iff]
  show (affGraph p).Adj ((vEquiv p) ((vEquiv p).symm (Sum.inl P)))
    ((vEquiv p) ((vEquiv p).symm (Sum.inr L)))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, adj_inl_iff]
  exact ⟨L, rfl, h⟩

variable (p)

/-- An edge of `affFlag p`, oriented as `edgeFinset` stores it. -/
noncomputable def canonE [NeZero p] (a b : Fin (affFlag p).size) :
    Fin (affFlag p).size × Fin (affFlag p).size :=
  if a < b then (a, b) else (b, a)

/-- The edge carrying an incidence. -/
noncomputable def incEdge [NeZero p] (P L : Pt p) :
    Fin (affFlag p).size × Fin (affFlag p).size :=
  canonE p (ptIdx p P) (lnIdx p L)

variable {p}

lemma canonE_cases [NeZero p] (a b : Fin (affFlag p).size) :
    canonE p a b = (a, b) ∨ canonE p a b = (b, a) := by
  unfold canonE; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Both endpoints are recovered from the canonical pair. -/
lemma mem_canonE [NeZero p] (a b : Fin (affFlag p).size) :
    ((canonE p a b).1 = a ∧ (canonE p a b).2 = b) ∨
    ((canonE p a b).1 = b ∧ (canonE p a b).2 = a) := by
  rcases canonE_cases a b with h | h <;> rw [h]
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

lemma incEdge_mem [NeZero p] {P L : Pt p} (h : onLine p P L) :
    incEdge p P L ∈ edgeFinset (affFlag p) := by
  classical
  have hadj := adj_ptIdx_lnIdx h
  have hne : ptIdx p P ≠ lnIdx p L := ptIdx_ne_lnIdx P L
  simp only [edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and, incEdge, canonE]
  split
  · exact ⟨hadj, by assumption⟩
  · rename_i hlt
    exact ⟨(affFlag p).graph.symm hadj, lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)⟩

/-- An incidence is recoverable from its edge. -/
lemma incEdge_inj [NeZero p] {P L P' L' : Pt p}
    (h : incEdge p P L = incEdge p P' L') : P = P' ∧ L = L' := by
  have hPL : ptIdx p P ≠ lnIdx p L := ptIdx_ne_lnIdx P L
  have hPL' : ptIdx p P' ≠ lnIdx p L' := ptIdx_ne_lnIdx P' L'
  have key : ptIdx p P = ptIdx p P' ∧ lnIdx p L = lnIdx p L' := by
    unfold incEdge at h
    rcases canonE_cases (ptIdx p P) (lnIdx p L) with h1 | h1 <;>
      rcases canonE_cases (ptIdx p P') (lnIdx p L') with h2 | h2 <;>
      rw [h1, h2] at h <;> simp only [Prod.mk.injEq] at h
    · exact ⟨h.1, h.2⟩
    · exact absurd h.1 (ptIdx_ne_lnIdx P L')
    · exact absurd h.1.symm (ptIdx_ne_lnIdx P' L)
    · exact ⟨h.2, h.1⟩
  exact ⟨ptIdx_inj key.1, lnIdx_inj key.2⟩

/-! ## Adjacency in `L(G)²` between incidence edges -/

lemma incEdge_adj [NeZero p] {P L : Pt p} (h : onLine p P L) :
    (affFlag p).graph.Adj (incEdge p P L).1 (incEdge p P L).2 := by
  have := incEdge_mem h
  simp only [edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this.1

lemma incEdge_lt [NeZero p] {P L : Pt p} (h : onLine p P L) :
    (incEdge p P L).1 < (incEdge p P L).2 := by
  have := incEdge_mem h
  simp only [edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact this.2

lemma incEdge_pt_endpoint [NeZero p] (P L : Pt p) :
    (incEdge p P L).1 = ptIdx p P ∨ (incEdge p P L).2 = ptIdx p P := by
  rcases mem_canonE (ptIdx p P) (lnIdx p L) with ⟨h, -⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

lemma incEdge_ln_endpoint [NeZero p] (P L : Pt p) :
    (incEdge p P L).1 = lnIdx p L ∨ (incEdge p P L).2 = lnIdx p L := by
  rcases mem_canonE (ptIdx p P) (lnIdx p L) with ⟨-, h⟩ | ⟨h, -⟩
  · exact Or.inr h
  · exact Or.inl h

/-- A shared endpoint gives the four-way disjunct `lineGraphAdj` asks for. -/
lemma share_of_common {α : Type*} {a : α} {e f : α × α}
    (he : e.1 = a ∨ e.2 = a) (hf : f.1 = a ∨ f.2 = a) :
    e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2 := by
  rcases he with h | h <;> rcases hf with h' | h'
  · exact Or.inl (h.trans h'.symm)
  · exact Or.inr (Or.inl (h.trans h'.symm))
  · exact Or.inr (Or.inr (Or.inl (h.trans h'.symm)))
  · exact Or.inr (Or.inr (Or.inr (h.trans h'.symm)))

/-- Two incidence edges sharing their point are `L(G)`-adjacent. -/
lemma lineGraphAdj_of_share [NeZero p] {P L P' L' : Pt p}
    (h : onLine p P L) (h' : onLine p P' L')
    (hne : incEdge p P L ≠ incEdge p P' L')
    (hshare : (incEdge p P L).1 = (incEdge p P' L').1 ∨
              (incEdge p P L).1 = (incEdge p P' L').2 ∨
              (incEdge p P L).2 = (incEdge p P' L').1 ∨
              (incEdge p P L).2 = (incEdge p P' L').2) :
    lineGraphAdj (affFlag p) (incEdge p P L) (incEdge p P' L') :=
  ⟨incEdge_adj h, incEdge_adj h', hne, hshare⟩

/-- A canonical edge is never the reverse of a canonical edge. -/
lemma incEdge_ne_swap [NeZero p] {P L P' L' : Pt p}
    (h : onLine p P L) (h' : onLine p P' L') :
    incEdge p P L ≠ ((incEdge p P' L').2, (incEdge p P' L').1) := by
  intro hc
  have h1 := incEdge_lt h
  have h2 := incEdge_lt h'
  rw [hc] at h1
  exact absurd h1 (asymm h2)

/-- **Distance two in `L(G)`.**  If `e₃` shares an endpoint with each of `e₁`, `e₂`,
and the three are pairwise distinct, then `e₁` and `e₂` are `L(G)²`-adjacent. -/
lemma lineGraphSqAdj_of_witness [NeZero p] {P L P' L' A B : Pt p}
    (h : onLine p P L) (h' : onLine p P' L') (hw : onLine p A B)
    (hne : incEdge p P L ≠ incEdge p P' L')
    (h13 : incEdge p P L ≠ incEdge p A B)
    (h32 : incEdge p A B ≠ incEdge p P' L')
    (s13 : (incEdge p P L).1 = (incEdge p A B).1 ∨
           (incEdge p P L).1 = (incEdge p A B).2 ∨
           (incEdge p P L).2 = (incEdge p A B).1 ∨
           (incEdge p P L).2 = (incEdge p A B).2)
    (s32 : (incEdge p A B).1 = (incEdge p P' L').1 ∨
           (incEdge p A B).1 = (incEdge p P' L').2 ∨
           (incEdge p A B).2 = (incEdge p P' L').1 ∨
           (incEdge p A B).2 = (incEdge p P' L').2) :
    lineGraphSqAdj (affFlag p) (incEdge p P L) (incEdge p P' L') := by
  refine ⟨incEdge_adj h, incEdge_adj h', hne, incEdge_ne_swap h h', Or.inr ?_⟩
  exact ⟨incEdge p A B, incEdge_adj hw,
    lineGraphAdj_of_share h hw h13 s13, lineGraphAdj_of_share hw h' h32 s32⟩

/-! ## The two families of strong neighbours

Fix an edge `e₁ = {P, L}`.  Its `L(G)²`-neighbourhood contains

* **family 1**, indexed by a slope `m ≠ L.1` and an abscissa `x ≠ P.1`: the edge
  `{pointOn L' x, L'}` where `L' = lineThru P m` is the line through `P` of slope
  `m`, witnessed at distance two by `{P, L'}`;
* **family 2**, indexed by `x ≠ P.1` and `m ≠ L.1`: the edge `{P', lineThru P' m}`
  where `P' = pointOn L x` is the point of `L` over `x`, witnessed by `{P', L}`.

Each has `(p-1)²` members, and they are **disjoint**: a common edge would place
the two distinct points `P`, `P'` on the two distinct lines `L`, `L'`, which
`line_unique` forbids. -/

variable (p)

/-- The line through `P` of slope `m`. -/
def lineThru (P : Pt p) (m : ZMod p) : Pt p := (m, P.2 - m * P.1)

/-- The point of `L` over abscissa `x`. -/
def pointOn (L : Pt p) (x : ZMod p) : Pt p := (x, L.1 * x + L.2)

variable {p}

lemma onLine_lineThru (P : Pt p) (m : ZMod p) : onLine p P (lineThru p P m) := by
  show P.2 = m * P.1 + (P.2 - m * P.1); ring

lemma onLine_pointOn (L : Pt p) (x : ZMod p) : onLine p (pointOn p L x) L := rfl

@[simp] lemma lineThru_fst (P : Pt p) (m : ZMod p) : (lineThru p P m).1 = m := rfl
@[simp] lemma pointOn_fst (L : Pt p) (x : ZMod p) : (pointOn p L x).1 = x := rfl

lemma card_ne [NeZero p] (a : ZMod p) :
    ((univ : Finset (ZMod p)).filter (fun m => m ≠ a)).card = p - 1 := by
  classical
  rw [Finset.filter_ne', Finset.card_erase_of_mem (mem_univ a), Finset.card_univ, ZMod.card]

/-- The index set: two copies of (slope, abscissa). -/
noncomputable def idxSet [NeZero p] (P L : Pt p) :
    Finset ((ZMod p × ZMod p) ⊕ (ZMod p × ZMod p)) :=
  ((univ.filter (fun m : ZMod p => m ≠ L.1)) ×ˢ (univ.filter (fun x : ZMod p => x ≠ P.1))).disjSum
  ((univ.filter (fun x : ZMod p => x ≠ P.1)) ×ˢ (univ.filter (fun m : ZMod p => m ≠ L.1)))

lemma idxSet_card [NeZero p] (P L : Pt p) :
    (idxSet P L).card = 2 * ((p - 1) * (p - 1)) := by
  classical
  unfold idxSet
  rw [Finset.card_disjSum, Finset.card_product, Finset.card_product, card_ne, card_ne]
  ring

/-- The edge assigned to each index. -/
noncomputable def famEdge [NeZero p] (P L : Pt p) :
    (ZMod p × ZMod p) ⊕ (ZMod p × ZMod p) →
      Fin (affFlag p).size × Fin (affFlag p).size
  | Sum.inl (m, x) => incEdge p (pointOn p (lineThru p P m) x) (lineThru p P m)
  | Sum.inr (x, m) => incEdge p (pointOn p L x) (lineThru p (pointOn p L x) m)

/-! ## The three obligations -/

lemma idxSet_inl [NeZero p] {P L : Pt p} {m x : ZMod p}
    (h : Sum.inl (m, x) ∈ idxSet P L) : m ≠ L.1 ∧ x ≠ P.1 := by
  classical
  simp only [idxSet, Finset.mem_disjSum, Finset.mem_product, Finset.mem_filter,
    Finset.mem_univ, true_and] at h
  rcases h with ⟨a, ha, hEq⟩ | ⟨b, -, hEq⟩
  · obtain rfl : a = (m, x) := by simpa using hEq
    exact ha
  · exact absurd hEq (by simp)

lemma idxSet_inr [NeZero p] {P L : Pt p} {x m : ZMod p}
    (h : Sum.inr (x, m) ∈ idxSet P L) : x ≠ P.1 ∧ m ≠ L.1 := by
  classical
  simp only [idxSet, Finset.mem_disjSum, Finset.mem_product, Finset.mem_filter,
    Finset.mem_univ, true_and] at h
  rcases h with ⟨a, -, hEq⟩ | ⟨b, hb, hEq⟩
  · exact absurd hEq (by simp)
  · obtain rfl : b = (x, m) := by simpa using hEq
    exact hb

lemma famEdge_mem [NeZero p] {P L : Pt p} (t) (_ : t ∈ idxSet P L) :
    famEdge P L t ∈ edgeFinset (affFlag p) := by
  cases t with
  | inl mx => exact incEdge_mem (onLine_pointOn _ _)
  | inr xm => exact incEdge_mem (onLine_lineThru _ _)

/-- A point with a different abscissa is a different point. -/
lemma ne_pointOn [NeZero p] {L P : Pt p} {x : ZMod p} (hx : x ≠ P.1) :
    P ≠ pointOn p L x :=
  fun hc => hx (by simpa using (congrArg Prod.fst hc).symm)

/-- A line with a different slope is a different line. -/
lemma ne_lineThru [NeZero p] {P L : Pt p} {m : ZMod p} (hm : m ≠ L.1) :
    L ≠ lineThru p P m :=
  fun hc => hm (by simpa using (congrArg Prod.fst hc).symm)

lemma famEdge_adj [NeZero p] [Fact p.Prime] {P L : Pt p} (h : onLine p P L)
    (t) (ht : t ∈ idxSet P L) :
    lineGraphSqAdj (affFlag p) (incEdge p P L) (famEdge P L t) := by
  cases t with
  | inl mx =>
    obtain ⟨m, x⟩ := mx
    obtain ⟨hm, hx⟩ := idxSet_inl ht
    have hLL' : L ≠ lineThru p P m := ne_lineThru hm
    have hPP' : P ≠ pointOn p (lineThru p P m) x := ne_pointOn hx
    exact lineGraphSqAdj_of_witness h (onLine_pointOn _ x) (onLine_lineThru P m)
      (fun hc => hLL' (incEdge_inj hc).2) (fun hc => hLL' (incEdge_inj hc).2)
      (fun hc => hPP' (incEdge_inj hc).1)
      (share_of_common (incEdge_pt_endpoint P L) (incEdge_pt_endpoint P _))
      (share_of_common (incEdge_ln_endpoint P _) (incEdge_ln_endpoint _ _))
  | inr xm =>
    obtain ⟨x, m⟩ := xm
    obtain ⟨hx, hm⟩ := idxSet_inr ht
    have hPP' : P ≠ pointOn p L x := ne_pointOn hx
    have hLL'' : L ≠ lineThru p (pointOn p L x) m := ne_lineThru hm
    exact lineGraphSqAdj_of_witness h (onLine_lineThru _ m) (onLine_pointOn L x)
      (fun hc => hPP' (incEdge_inj hc).1) (fun hc => hPP' (incEdge_inj hc).1)
      (fun hc => hLL'' (incEdge_inj hc).2)
      (share_of_common (incEdge_ln_endpoint P L) (incEdge_ln_endpoint _ L))
      (share_of_common (incEdge_pt_endpoint _ L) (incEdge_pt_endpoint _ _))

lemma famEdge_inj [NeZero p] [Fact p.Prime] {P L : Pt p} (h : onLine p P L)
    (t₁) (h₁ : t₁ ∈ idxSet P L) (t₂) (h₂ : t₂ ∈ idxSet P L)
    (heq : famEdge P L t₁ = famEdge P L t₂) : t₁ = t₂ := by
  cases t₁ with
  | inl mx₁ =>
    obtain ⟨m₁, x₁⟩ := mx₁
    cases t₂ with
    | inl mx₂ =>
      obtain ⟨m₂, x₂⟩ := mx₂
      obtain ⟨hP, hL⟩ := incEdge_inj heq
      have hm : m₁ = m₂ := by simpa using congrArg Prod.fst hL
      have hxx : x₁ = x₂ := by simpa using congrArg Prod.fst hP
      rw [hm, hxx]
    | inr xm₂ =>
      exfalso
      obtain ⟨x₂, m₂⟩ := xm₂
      obtain ⟨hm₁, -⟩ := idxSet_inl h₁
      obtain ⟨hx₂, -⟩ := idxSet_inr h₂
      obtain ⟨hQ, -⟩ := incEdge_inj heq
      refine (ne_lineThru (P := P) hm₁) (line_unique (ne_pointOn (L := L) hx₂) h
        (onLine_pointOn L x₂) (onLine_lineThru P m₁) ?_)
      rw [← hQ]
      exact onLine_pointOn _ x₁
  | inr xm₁ =>
    obtain ⟨x₁, m₁⟩ := xm₁
    cases t₂ with
    | inl mx₂ =>
      exfalso
      obtain ⟨x₁', -⟩ := idxSet_inr h₁
      obtain ⟨m₂, x₂⟩ := mx₂
      obtain ⟨hm₂, -⟩ := idxSet_inl h₂
      obtain ⟨hQ, -⟩ := incEdge_inj heq
      refine (ne_lineThru (P := P) hm₂) (line_unique (ne_pointOn (L := L) x₁') h
        (onLine_pointOn L x₁) (onLine_lineThru P m₂) ?_)
      rw [hQ]
      exact onLine_pointOn _ x₂
    | inr xm₂ =>
      obtain ⟨x₂, m₂⟩ := xm₂
      obtain ⟨hP, hL⟩ := incEdge_inj heq
      have hxx : x₁ = x₂ := by simpa using congrArg Prod.fst hP
      have hm : m₁ = m₂ := by simpa using congrArg Prod.fst hL
      rw [hxx, hm]

/-! ## The strong-degree bound -/

/-- Every edge of the family carries an incidence. -/
lemma exists_incidence [NeZero p] {e : Fin (affFlag p).size × Fin (affFlag p).size}
    (he : e ∈ edgeFinset (affFlag p)) : ∃ P L, onLine p P L ∧ e = incEdge p P L := by
  classical
  simp only [edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and] at he
  obtain ⟨hadj, hlt⟩ := he
  rw [affFlag_adj_iff, affGraph_adj_iff] at hadj
  rcases hadj with ⟨P, L, h1, h2, hon⟩ | ⟨P, L, h1, h2, hon⟩
  · refine ⟨P, L, hon, ?_⟩
    have e1 : e.1 = ptIdx p P := by
      rw [ptIdx, ← h1, Equiv.symm_apply_apply]
    have e2 : e.2 = lnIdx p L := by
      rw [lnIdx, ← h2, Equiv.symm_apply_apply]
    unfold incEdge canonE
    rw [← e1, ← e2, if_pos hlt]
  · refine ⟨P, L, hon, ?_⟩
    have e1 : e.1 = lnIdx p L := by
      rw [lnIdx, ← h1, Equiv.symm_apply_apply]
    have e2 : e.2 = ptIdx p P := by
      rw [ptIdx, ← h2, Equiv.symm_apply_apply]
    unfold incEdge canonE
    rw [← e1, ← e2, if_neg (asymm hlt)]

open Davey2024.SecBridge in
/-- **The strong-degree bound.**  Every edge of the affine family has at least
`2(p-1)²` strong neighbours — the two families of the section above, disjoint by
`line_unique`. -/
theorem le_strongFDegree_affFlag [NeZero p] [Fact p.Prime]
    (i : Fin (lineGraphSqFlag (affFlag p)).size) :
    2 * ((p - 1) * (p - 1)) ≤ strongFDegree (affFlag p) Finset.univ i := by
  obtain ⟨P, L, hPL, hval⟩ :=
    exists_incidence ((edgeFinset (affFlag p)).equivFin.symm i).2
  have hb := card_le_strongFDegree i (idxSet P L) (famEdge P L)
    (fun t ht => famEdge_mem t ht) ?_ (famEdge_inj hPL)
  · rwa [idxSet_card] at hb
  · intro t ht
    rw [hval]
    exact famEdge_adj hPL t ht

/-- The arithmetic the gate asks for, from `p ≥ 15`. -/
lemma gate_arith {p : ℕ} (hp : 15 ≤ p) :
    17297 * p ^ 2 ≤ 10000 * (2 * ((p - 1) * (p - 1))) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 15 + k := ⟨p - 15, by omega⟩
  have h1 : 15 + k - 1 = 14 + k := by omega
  rw [h1]
  ring_nf
  nlinarith [sq_nonneg k, Nat.zero_le k]

/-! ## Bipartiteness, and the gate -/

theorem affFlag_isBipartite [NeZero p] : IsBipartite (affFlag p) := by
  classical
  refine ⟨Finset.univ.filter (fun i => (vEquiv p i).isLeft), ?_⟩
  intro u v huv
  rw [affFlag_adj_iff] at huv
  rcases adj_cross huv with ⟨P, L, h1, h2⟩ | ⟨P, L, h1, h2⟩ <;> simp [h1, h2]

open Davey2024.SecBridge in
/-- The general gate, `1.7297 Δ²`, holds for the affine family at every prime
`p ≥ 15`. -/
theorem affFlag_gate [NeZero p] [Fact p.Prime] (hp : 15 ≤ p)
    (i : Fin (lineGraphSqFlag (affFlag p)).size) :
    17297 * (maxDegree (affFlag p)) ^ 2 ≤
      10000 * strongFDegree (affFlag p) Finset.univ i := by
  rw [affFlag_maxDegree p (by omega)]
  exact le_trans (gate_arith hp)
    (Nat.mul_le_mul_left _ (le_strongFDegree_affFlag i))

open Davey2024.SecBridge in
/-- The bipartite gate is weaker (`1.6254 Δ²`), so the same bound serves. -/
theorem affFlag_gate_bip [NeZero p] [Fact p.Prime] (hp : 15 ≤ p)
    (i : Fin (lineGraphSqFlag (affFlag p)).size) :
    16254 * (maxDegree (affFlag p)) ^ 2 ≤
      10000 * strongFDegree (affFlag p) Finset.univ i := by
  refine le_trans (Nat.mul_le_mul_right _ (by omega)) (affFlag_gate hp i)

/-! ## A sequence of primes, and the family's distinguished edge -/

/-- The `(k+15)`-th prime; at least `15`, and strictly increasing. -/
noncomputable def primeSeq (k : ℕ) : ℕ := Nat.nth Nat.Prime (k + 15)

lemma primeSeq_prime (k : ℕ) : (primeSeq k).Prime := Nat.prime_nth_prime _

lemma primeSeq_strictMono : StrictMono primeSeq := by
  intro a b hab
  exact Nat.nth_strictMono Nat.infinite_setOf_prime (by omega)

lemma primeSeq_ge (k : ℕ) : 15 ≤ primeSeq k :=
  le_trans (by omega) (Nat.nth_strictMono Nat.infinite_setOf_prime).le_apply

instance primeSeq_fact (k : ℕ) : Fact (primeSeq k).Prime := ⟨primeSeq_prime k⟩

instance primeSeq_neZero (k : ℕ) : NeZero (primeSeq k) :=
  ⟨by have := primeSeq_ge k; omega⟩

/-- The origin lies on the line `y = 0`, so the family always has an edge. -/
lemma origin_onLine (q : ℕ) [NeZero q] : onLine q (0, 0) (0, 0) := by
  show (0 : ZMod q) = 0 * 0 + 0; ring

/-- A distinguished edge of `affFlag q`, as a vertex of `L(G)²`. -/
noncomputable def affEdgeIdx (q : ℕ) [NeZero q] :
    Fin (lineGraphSqFlag (affFlag q)).size :=
  (edgeFinset (affFlag q)).equivFin ⟨_, incEdge_mem (origin_onLine q)⟩

end AffinePlaneFamily
end Davey2024
