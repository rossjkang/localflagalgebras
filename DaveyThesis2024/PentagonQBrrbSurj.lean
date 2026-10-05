import DaveyThesis2024.PentagonConjecture
import DaveyThesis2024.PentagonQIsoInvariance
import DaveyThesis2024.PentagonQMuFlag

/-!
# (a2a): every BRRB tuple comes from a pentagon through `v`

`brrb_reduction` (`PentagonConjecture.lean:15339`) proves only
`2·pentagonCountAt G v ≤ brrbCount G'`, because `≤` is all it needs: the `calc`
at `:15630` ends with `Finset.card_le_card` on
`fwdImg ∪ revImg ⊆ brrbSet`.  Item `(a2a)` needs the **equality**, hence the
reverse inclusion — the surjection.

This file proves its mathematical content: a BRRB tuple at the `v`-colouring,
together with `v`, spans an **induced** pentagon.  Three of the four facts are
not bookkeeping —

* `v` is distinct from `r₁` and `r₂` *not* because they are red (the colouring
  makes `v` itself red, `¬Adj v v`), but because each `rᵢ` is adjacent to the
  other, which would drag `v` into `N(v)`'s complement the wrong way;
* the chords `b₁r₂`, `r₁b₂` and `b₁b₂` are excluded by **triangle-freeness**,
  one triangle each.  Without `IsTriangleFree` the statement is false: take
  `v–b₁–r₁–r₂–b₂–v` with the chord `b₁b₂` present.

`pentagonToTuple` and its helpers were `private` in `PentagonConjecture`; they
are now public, so the bridge lives here rather than in that 15k-line file —
which matters, because every edit to it re-elaborates `PentagonQBridge`'s 321
`native_decide` calls.
-/

namespace Davey2024
namespace PentagonQBrrbSurj

open Finset

variable {G : Flag emptyType}

/-- The five vertices of a BRRB tuple at the `v`-colouring, with `v`, are
pairwise distinct.  The six tuple-internal inequalities come from `brrbSet`'s
own filter; what is proved here is that `v` avoids all four.

For `b₁`, `b₂` that is irreflexivity.  For `r₁`, `r₂` the colouring is *not*
enough — `col v = 0` too, since `¬G.graph.Adj v v` — and the argument runs
through the other red vertex instead. -/
theorem v_ne_of_brrb {v b₁ r₁ r₂ b₂ : Fin G.size}
    (hvb₁ : G.graph.Adj v b₁) (hvb₂ : G.graph.Adj v b₂)
    (hnr₁ : ¬ G.graph.Adj v r₁) (hnr₂ : ¬ G.graph.Adj v r₂)
    (hr₁r₂ : G.graph.Adj r₁ r₂) :
    v ≠ b₁ ∧ v ≠ r₁ ∧ v ≠ r₂ ∧ v ≠ b₂ := by
  refine ⟨hvb₁.ne, ?_, ?_, hvb₂.ne⟩
  · rintro rfl; exact hnr₂ hr₁r₂
  · rintro rfl; exact hnr₁ hr₁r₂.symm

/-- **The surjection's content.**  A BRRB tuple at the `v`-colouring spans an
induced pentagon together with `v`.

The hypotheses are exactly what `brrbSet` supplies at
`PentagonConjecture.lean:15398` — the six distinctness clauses, the three
adjacencies, and the colour conditions read through
`col u = if G.graph.Adj v u then 1 else 0` — plus triangle-freeness. -/
theorem isPentagon_of_brrb (hTF : IsTriangleFree G) {v b₁ r₁ r₂ b₂ : Fin G.size}
    (hvb₁ : G.graph.Adj v b₁) (hvb₂ : G.graph.Adj v b₂)
    (hnr₁ : ¬ G.graph.Adj v r₁) (hnr₂ : ¬ G.graph.Adj v r₂)
    (hb₁r₁ : G.graph.Adj b₁ r₁) (hr₁r₂ : G.graph.Adj r₁ r₂)
    (hr₂b₂ : G.graph.Adj r₂ b₂)
    (h₁ : b₁ ≠ r₁) (h₂ : b₁ ≠ r₂) (h₃ : b₁ ≠ b₂)
    (h₄ : r₁ ≠ r₂) (h₅ : r₁ ≠ b₂) (h₆ : r₂ ≠ b₂) :
    IsPentagon G {v, b₁, r₁, r₂, b₂} ∧ v ∈ ({v, b₁, r₁, r₂, b₂} : Finset (Fin G.size)) := by
  obtain ⟨hv₁, hv₂, hv₃, hv₄⟩ := v_ne_of_brrb hvb₁ hvb₂ hnr₁ hnr₂ hr₁r₂
  -- the three chords, one triangle each
  have hnb₁r₂ : ¬ G.graph.Adj b₁ r₂ := fun h => hTF b₁ r₁ r₂ hb₁r₁ hr₁r₂ h
  have hnr₁b₂ : ¬ G.graph.Adj r₁ b₂ := fun h => hTF r₁ r₂ b₂ hr₁r₂ hr₂b₂ h
  have hnb₁b₂ : ¬ G.graph.Adj b₁ b₂ := fun h => hTF b₁ v b₂ hvb₁.symm hvb₂ h
  -- the same three, and the two colour conditions, read the other way round
  have hnb₁r₂' : ¬ G.graph.Adj r₂ b₁ := fun h => hnb₁r₂ h.symm
  have hnr₁b₂' : ¬ G.graph.Adj b₂ r₁ := fun h => hnr₁b₂ h.symm
  have hnb₁b₂' : ¬ G.graph.Adj b₂ b₁ := fun h => hnb₁b₂ h.symm
  have hnr₁' : ¬ G.graph.Adj r₁ v := fun h => hnr₁ h.symm
  have hnr₂' : ¬ G.graph.Adj r₂ v := fun h => hnr₂ h.symm
  refine ⟨⟨![v, b₁, r₁, r₂, b₂], ?_, ?_, ?_⟩, by simp⟩
  · -- injective
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  · -- image is the set
    ext x; simp [Fin.exists_fin_succ, Matrix.cons_val_zero, eq_comm]
  · -- adjacency, both ways
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [cycleGraph5, SimpleGraph.fromRel_adj, Matrix.cons_val_zero,
        Matrix.cons_val_one, G.graph.symm hvb₁, G.graph.symm hvb₂,
        G.graph.symm hb₁r₁, G.graph.symm hr₁r₂, G.graph.symm hr₂b₂]

/-- **The bridge.**  `pentagonToTuple` reads a tuple off an *arbitrary* C₅
labelling of the pentagon (`hpS.choose`), so it is pinned only up to the
stabiliser of `v` in the dihedral group — order two.  Hence the disjunction:
the tuple is the BRRB tuple or its reversal, which is exactly what
`brrb_reduction`'s `fwdImg ∪ revImg` covers.

The argument walks the cycle from `v`: the only neighbours of `v` inside the
pentagon are `b₁` and `b₂`, which forks the two cases, and each subsequent step
is forced because the chords are absent. -/
theorem pentagonToTuple_of_brrb (hTF : IsTriangleFree G) {v b₁ r₁ r₂ b₂ : Fin G.size}
    (hvb₁ : G.graph.Adj v b₁) (hvb₂ : G.graph.Adj v b₂)
    (hnr₁ : ¬ G.graph.Adj v r₁) (hnr₂ : ¬ G.graph.Adj v r₂)
    (hb₁r₁ : G.graph.Adj b₁ r₁) (hr₁r₂ : G.graph.Adj r₁ r₂)
    (hr₂b₂ : G.graph.Adj r₂ b₂)
    (h₁ : b₁ ≠ r₁) (h₂ : b₁ ≠ r₂) (h₃ : b₁ ≠ b₂)
    (h₄ : r₁ ≠ r₂) (h₅ : r₁ ≠ b₂) (h₆ : r₂ ≠ b₂) :
    pentagonToTuple G v {v, b₁, r₁, r₂, b₂} = (b₁, r₁, r₂, b₂) ∨
    pentagonToTuple G v {v, b₁, r₁, r₂, b₂} = (b₂, r₂, r₁, b₁) := by
  obtain ⟨hpS, hvS⟩ :=
    isPentagon_of_brrb hTF hvb₁ hvb₂ hnr₁ hnr₂ hb₁r₁ hr₁r₂ hr₂b₂ h₁ h₂ h₃ h₄ h₅ h₆
  have hnb₁r₂ : ¬ G.graph.Adj b₁ r₂ := fun h => hTF b₁ r₁ r₂ hb₁r₁ hr₁r₂ h
  have hnr₁b₂ : ¬ G.graph.Adj r₁ b₂ := fun h => hTF r₁ r₂ b₂ hr₁r₂ hr₂b₂ h
  have hnb₁b₂ : ¬ G.graph.Adj b₁ b₂ := fun h => hTF b₁ v b₂ hvb₁.symm hvb₂ h
  obtain ⟨hva, hab, hbc, hcd⟩ := pentagonToTuple_adj G v _ hpS hvS
  obtain ⟨hma, hmb, hmc, hmd⟩ := pentagonToTuple_mem G v _ hpS hvS
  obtain ⟨dva, dvb, dvc, dvd, dab, dac, dad, dbc, dbd, dcd⟩ :=
    pentagonToTuple_distinct G v _ hpS hvS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hma hmb hmc hmd
  -- the first step leaves `v` along one of its two pentagon edges
  have ha : (pentagonToTuple G v {v, b₁, r₁, r₂, b₂}).1 = b₁ ∨
      (pentagonToTuple G v {v, b₁, r₁, r₂, b₂}).1 = b₂ := by
    rcases hma with h | h | h | h | h
    · exact absurd h.symm dva
    · exact Or.inl h
    · exact absurd (h ▸ hva) hnr₁
    · exact absurd (h ▸ hva) hnr₂
    · exact Or.inr h
  rcases ha with ha | ha
  · -- a = b₁: the walk is forced to r₁, r₂, b₂
    have hb : (pentagonToTuple G v {v, b₁, r₁, r₂, b₂}).2.1 = r₁ := by
      rcases hmb with h | h | h | h | h
      · exact absurd h.symm dvb
      · have hx := dab; rw [ha, h] at hx; exact absurd rfl hx
      · exact h
      · have hx := hab; rw [ha, h] at hx; exact absurd hx hnb₁r₂
      · have hx := hab; rw [ha, h] at hx; exact absurd hx hnb₁b₂
    have hc : (pentagonToTuple G v {v, b₁, r₁, r₂, b₂}).2.2.1 = r₂ := by
      rcases hmc with h | h | h | h | h
      · exact absurd h.symm dvc
      · have hx := dac; rw [ha, h] at hx; exact absurd rfl hx
      · have hx := dbc; rw [hb, h] at hx; exact absurd rfl hx
      · exact h
      · have hx := hbc; rw [hb, h] at hx; exact absurd hx hnr₁b₂
    have hd : (pentagonToTuple G v {v, b₁, r₁, r₂, b₂}).2.2.2 = b₂ := by
      rcases hmd with h | h | h | h | h
      · exact absurd h.symm dvd
      · have hx := dad; rw [ha, h] at hx; exact absurd rfl hx
      · have hx := dbd; rw [hb, h] at hx; exact absurd rfl hx
      · have hx := dcd; rw [hc, h] at hx; exact absurd rfl hx
      · exact h
    exact Or.inl (Prod.ext ha (Prod.ext hb (Prod.ext hc hd)))
  · -- a = b₂: the same walk in the other direction
    have hb : (pentagonToTuple G v {v, b₁, r₁, r₂, b₂}).2.1 = r₂ := by
      rcases hmb with h | h | h | h | h
      · exact absurd h.symm dvb
      · have hx := hab; rw [ha, h] at hx; exact absurd hx.symm hnb₁b₂
      · have hx := hab; rw [ha, h] at hx; exact absurd hx.symm hnr₁b₂
      · exact h
      · have hx := dab; rw [ha, h] at hx; exact absurd rfl hx
    have hc : (pentagonToTuple G v {v, b₁, r₁, r₂, b₂}).2.2.1 = r₁ := by
      rcases hmc with h | h | h | h | h
      · exact absurd h.symm dvc
      · have hx := hbc; rw [hb, h] at hx; exact absurd hx.symm hnb₁r₂
      · exact h
      · have hx := dbc; rw [hb, h] at hx; exact absurd rfl hx
      · have hx := dac; rw [ha, h] at hx; exact absurd rfl hx
    have hd : (pentagonToTuple G v {v, b₁, r₁, r₂, b₂}).2.2.2 = b₁ := by
      rcases hmd with h | h | h | h | h
      · exact absurd h.symm dvd
      · exact h
      · have hx := dcd; rw [hc, h] at hx; exact absurd rfl hx
      · have hx := dbd; rw [hb, h] at hx; exact absurd rfl hx
      · have hx := dad; rw [ha, h] at hx; exact absurd rfl hx
    exact Or.inr (Prod.ext ha (Prod.ext hb (Prod.ext hc hd)))

/-! ## The surjection, free of `brrb_reduction`'s locals

`brrb_reduction` builds the colouring `G'` and the tuple set `brrbSet` as
`let`-bindings inside its own proof, so neither is reachable from here.  The
statement below therefore re-declares the colouring and takes `brrbSet`'s filter
as explicit hypotheses — in its exact shape, so that instantiating it inside that
proof is a matter of destructuring, not of re-deriving anything. -/

open Classical in
/-- The `v`-colouring of `brrb_reduction`: `N(v)` black, everything else red.
`Classical` for the same reason `brrb_reduction`'s own `col` is: `Flag`'s
adjacency carries no `DecidableRel`. -/
noncomputable def vColouring (G : Flag emptyType) (v : Fin G.size) :
    VertexColouring G.size :=
  fun u => if G.graph.Adj v u then 1 else 0

open Classical in
theorem vColouring_eq_one {G : Flag emptyType} {v u : Fin G.size} :
    vColouring G v u = 1 ↔ G.graph.Adj v u := by
  unfold vColouring
  constructor
  · intro h; by_contra hna; simp [hna] at h
  · intro h; simp [h]

open Classical in
theorem vColouring_eq_zero {G : Flag emptyType} {v u : Fin G.size} :
    vColouring G v u = 0 ↔ ¬ G.graph.Adj v u := by
  unfold vColouring
  constructor
  · intro h hadj; rw [if_pos hadj] at h; exact absurd h (by decide)
  · intro h; simp [h]

/-- **`(a2a)`'s surjection.**  Every BRRB tuple at the `v`-colouring is
`pentagonToTuple` of a pentagon through `v`, or that tuple's reversal.

Together with the injection already inside `brrb_reduction` this upgrades its
`2·P(G,v) ≤ brrbCount G'` to the equality `(a2a)` needs: the two images
`fwdImg ∪ revImg` are not merely contained in `brrbSet`, they exhaust it. -/
theorem exists_pentagon_of_brrb (hTF : IsTriangleFree G) (v : Fin G.size)
    {b₁ r₁ r₂ b₂ : Fin G.size}
    (h₁ : b₁ ≠ r₁) (h₂ : b₁ ≠ r₂) (h₃ : b₁ ≠ b₂)
    (h₄ : r₁ ≠ r₂) (h₅ : r₁ ≠ b₂) (h₆ : r₂ ≠ b₂)
    (hcb₁ : vColouring G v b₁ = 1) (hcr₁ : vColouring G v r₁ = 0)
    (hcr₂ : vColouring G v r₂ = 0) (hcb₂ : vColouring G v b₂ = 1)
    (hb₁r₁ : G.graph.Adj b₁ r₁) (hr₁r₂ : G.graph.Adj r₁ r₂)
    (hr₂b₂ : G.graph.Adj r₂ b₂) :
    ∃ S : Finset (Fin G.size), IsPentagon G S ∧ v ∈ S ∧
      (pentagonToTuple G v S = (b₁, r₁, r₂, b₂) ∨
       pentagonToTuple G v S = (b₂, r₂, r₁, b₁)) := by
  have hvb₁ : G.graph.Adj v b₁ := vColouring_eq_one.mp hcb₁
  have hvb₂ : G.graph.Adj v b₂ := vColouring_eq_one.mp hcb₂
  have hnr₁ : ¬ G.graph.Adj v r₁ := vColouring_eq_zero.mp hcr₁
  have hnr₂ : ¬ G.graph.Adj v r₂ := vColouring_eq_zero.mp hcr₂
  obtain ⟨hpS, hvS⟩ :=
    isPentagon_of_brrb hTF hvb₁ hvb₂ hnr₁ hnr₂ hb₁r₁ hr₁r₂ hr₂b₂ h₁ h₂ h₃ h₄ h₅ h₆
  exact ⟨{v, b₁, r₁, r₂, b₂}, hpS, hvS,
    pentagonToTuple_of_brrb hTF hvb₁ hvb₂ hnr₁ hnr₂ hb₁r₁ hr₁r₂ hr₂b₂ h₁ h₂ h₃ h₄ h₅ h₆⟩

/-- **The injection, extracted.**  `brrb_reduction` proves this inline as
`hfwd_mem` (`PentagonConjecture.lean:15423`), where `brrbSet` and the colouring
are local `let`s; stated here it is reusable, and pairs with
`exists_pentagon_of_brrb` to give `(a2a)`'s equality rather than its bound.

The conjuncts are in `brrbSet`'s own order, so a consumer destructures rather
than re-derives. -/
theorem brrb_of_pentagon (v : Fin G.size) (S : Finset (Fin G.size))
    (hpS : IsPentagon G S) (hvS : v ∈ S) :
    (pentagonToTuple G v S).1 ≠ (pentagonToTuple G v S).2.1 ∧
    (pentagonToTuple G v S).1 ≠ (pentagonToTuple G v S).2.2.1 ∧
    (pentagonToTuple G v S).1 ≠ (pentagonToTuple G v S).2.2.2 ∧
    (pentagonToTuple G v S).2.1 ≠ (pentagonToTuple G v S).2.2.1 ∧
    (pentagonToTuple G v S).2.1 ≠ (pentagonToTuple G v S).2.2.2 ∧
    (pentagonToTuple G v S).2.2.1 ≠ (pentagonToTuple G v S).2.2.2 ∧
    vColouring G v (pentagonToTuple G v S).1 = 1 ∧
    vColouring G v (pentagonToTuple G v S).2.1 = 0 ∧
    vColouring G v (pentagonToTuple G v S).2.2.1 = 0 ∧
    vColouring G v (pentagonToTuple G v S).2.2.2 = 1 ∧
    G.graph.Adj (pentagonToTuple G v S).1 (pentagonToTuple G v S).2.1 ∧
    G.graph.Adj (pentagonToTuple G v S).2.1 (pentagonToTuple G v S).2.2.1 ∧
    G.graph.Adj (pentagonToTuple G v S).2.2.1 (pentagonToTuple G v S).2.2.2 := by
  obtain ⟨hva, hab, hbc, hcd⟩ := pentagonToTuple_adj G v S hpS hvS
  obtain ⟨hnvb, hnvc, _, _, _⟩ := pentagonToTuple_nonadj G v S hpS hvS
  have hvd := pentagonToTuple_adj_closing G v S hpS hvS
  obtain ⟨_, _, _, _, dab, dac, dad, dbc, dbd, dcd⟩ :=
    pentagonToTuple_distinct G v S hpS hvS
  exact ⟨dab, dac, dad, dbc, dbd, dcd,
    vColouring_eq_one.mpr hva, vColouring_eq_zero.mpr hnvb,
    vColouring_eq_zero.mpr hnvc, vColouring_eq_one.mpr hvd.symm,
    hab, hbc, hcd⟩

/-- The reversal of a pentagon's tuple is also a BRRB tuple: the pentagon reads
the same backwards.  Needed because `brrbSet` contains *both* orientations, which
is the whole source of the factor 2. -/
theorem brrb_of_pentagon_rev (v : Fin G.size) (S : Finset (Fin G.size))
    (hpS : IsPentagon G S) (hvS : v ∈ S) :
    (pentagonToTuple G v S).2.2.2 ≠ (pentagonToTuple G v S).2.2.1 ∧
    (pentagonToTuple G v S).2.2.2 ≠ (pentagonToTuple G v S).2.1 ∧
    (pentagonToTuple G v S).2.2.2 ≠ (pentagonToTuple G v S).1 ∧
    (pentagonToTuple G v S).2.2.1 ≠ (pentagonToTuple G v S).2.1 ∧
    (pentagonToTuple G v S).2.2.1 ≠ (pentagonToTuple G v S).1 ∧
    (pentagonToTuple G v S).2.1 ≠ (pentagonToTuple G v S).1 ∧
    vColouring G v (pentagonToTuple G v S).2.2.2 = 1 ∧
    vColouring G v (pentagonToTuple G v S).2.2.1 = 0 ∧
    vColouring G v (pentagonToTuple G v S).2.1 = 0 ∧
    vColouring G v (pentagonToTuple G v S).1 = 1 ∧
    G.graph.Adj (pentagonToTuple G v S).2.2.2 (pentagonToTuple G v S).2.2.1 ∧
    G.graph.Adj (pentagonToTuple G v S).2.2.1 (pentagonToTuple G v S).2.1 ∧
    G.graph.Adj (pentagonToTuple G v S).2.1 (pentagonToTuple G v S).1 := by
  obtain ⟨d1, d2, d3, d4, d5, d6, c1, c2, c3, c4, a1, a2, a3⟩ :=
    brrb_of_pentagon v S hpS hvS
  exact ⟨d6.symm, d5.symm, d3.symm, d4.symm, d2.symm, d1.symm,
    c4, c3, c2, c1, a3.symm, a2.symm, a1.symm⟩

/-- **No fixed points.**  A pentagon's tuple is never its own reversal, because
its first and last components are distinct vertices of the cycle.  This is what
makes the two orientations contribute *separately* — `brrb_reduction` needs it as
`hfwd_ne_rev`, and without it the factor would be 1, not 2. -/
theorem pentagonToTuple_ne_rev (v : Fin G.size) (S : Finset (Fin G.size))
    (hpS : IsPentagon G S) (hvS : v ∈ S) :
    pentagonToTuple G v S ≠
      ((pentagonToTuple G v S).2.2.2, (pentagonToTuple G v S).2.2.1,
       (pentagonToTuple G v S).2.1, (pentagonToTuple G v S).1) := by
  intro h
  obtain ⟨_, _, _, _, _, _, dad, _, _, _⟩ := pentagonToTuple_distinct G v S hpS hvS
  exact dad (congrArg Prod.fst h)

open Classical in
/-- The `v`-colouring packaged as a `ColouredGraphClass`, exactly as
`brrb_reduction` builds it inline — so that `brrbCount` can be *named* at this
colouring from outside that proof. -/
noncomputable def vColouredClass (G : Flag emptyType) (v : Fin G.size)
    (htf : IsTriangleFree G) (hreg : IsRegular G) : ColouredGraphClass where
  graph := G
  colouring := vColouring G v
  triangleFree := htf
  regular := hreg
  blackCount := by
    have hfilt : (Finset.univ.filter (fun u : Fin G.size => vColouring G v u = 1)) =
        Finset.univ.filter (fun u => G.graph.Adj v u) := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => vColouring_eq_one.mp h, fun h => vColouring_eq_one.mpr h⟩
    rw [hfilt]; exact hreg v
  blackIndependent := fun u w hu hw hadj =>
    htf v u w (vColouring_eq_one.mp hu) hadj (vColouring_eq_one.mp hw)

@[simp] theorem vColouredClass_graph (G : Flag emptyType) (v : Fin G.size)
    (htf : IsTriangleFree G) (hreg : IsRegular G) :
    (vColouredClass G v htf hreg).graph = G := rfl

@[simp] theorem vColouredClass_colouring (G : Flag emptyType) (v : Fin G.size)
    (htf : IsTriangleFree G) (hreg : IsRegular G) :
    (vColouredClass G v htf hreg).colouring = vColouring G v := rfl

/-! ## The two images exhaust the BRRB tuples -/

/-- Reversing a 4-tuple. -/
def revTuple {n : ℕ} (p : Fin n × Fin n × Fin n × Fin n) : Fin n × Fin n × Fin n × Fin n :=
  (p.2.2.2, p.2.2.1, p.2.1, p.1)

open Classical in
/-- `brrbCount`'s filter set at the `v`-colouring, named. -/
noncomputable def brrbSetOf (G : Flag emptyType) (v : Fin G.size) :
    Finset (Fin G.size × Fin G.size × Fin G.size × Fin G.size) :=
  Finset.univ.filter (fun p =>
    p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2.1 ∧ p.1 ≠ p.2.2.2 ∧ p.2.1 ≠ p.2.2.1 ∧
    p.2.1 ≠ p.2.2.2 ∧ p.2.2.1 ≠ p.2.2.2 ∧
    vColouring G v p.1 = 1 ∧ vColouring G v p.2.1 = 0 ∧
    vColouring G v p.2.2.1 = 0 ∧ vColouring G v p.2.2.2 = 1 ∧
    G.graph.Adj p.1 p.2.1 ∧ G.graph.Adj p.2.1 p.2.2.1 ∧ G.graph.Adj p.2.2.1 p.2.2.2)

open Classical in
/-- The pentagons through `v`, named. -/
noncomputable def pentSetOf (G : Flag emptyType) (v : Fin G.size) :
    Finset (Finset (Fin G.size)) :=
  Finset.univ.filter (fun S => IsPentagon G S ∧ v ∈ S)

theorem brrbSetOf_card (G : Flag emptyType) (v : Fin G.size)
    (htf : IsTriangleFree G) (hreg : IsRegular G) :
    (brrbSetOf G v).card = brrbCount (vColouredClass G v htf hreg) := rfl

theorem pentSetOf_card (G : Flag emptyType) (v : Fin G.size) :
    (pentSetOf G v).card = pentagonCountAt G v := rfl

open Classical in
/-- **`(a2a)`'s set equality.**  The BRRB tuples are exactly the pentagon tuples
and their reversals — `⊇` is the injection, `⊆` the surjection.

`brrb_reduction` proves only `⊇` (as `fwdImg ∪ revImg ⊆ brrbSet`), which is what
limits it to an inequality. -/
theorem brrbSetOf_eq_union (htf : IsTriangleFree G) (v : Fin G.size) :
    brrbSetOf G v = (pentSetOf G v).image (pentagonToTuple G v) ∪
      (pentSetOf G v).image (fun S => revTuple (pentagonToTuple G v S)) := by
  ext p
  obtain ⟨b₁, r₁, r₂, b₂⟩ := p
  simp only [brrbSetOf, pentSetOf, revTuple, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d1, d2, d3, d4, d5, d6, c1, c2, c3, c4, a1, a2, a3⟩
    obtain ⟨S, hpS, hvS, h⟩ :=
      exists_pentagon_of_brrb htf v d1 d2 d3 d4 d5 d6 c1 c2 c3 c4 a1 a2 a3
    rcases h with h | h
    · exact Or.inl ⟨S, ⟨hpS, hvS⟩, h⟩
    · exact Or.inr ⟨S, ⟨hpS, hvS⟩, by rw [h]⟩
  · -- `rintro rfl` cannot fire here: the equation's right side is a *tuple of
    -- variables*, not one variable, so each component is substituted by hand.
    rintro (⟨S, hS, h⟩ | ⟨S, hS, h⟩)
    · have e1 : b₁ = (pentagonToTuple G v S).1 := by rw [h]
      have e2 : r₁ = (pentagonToTuple G v S).2.1 := by rw [h]
      have e3 : r₂ = (pentagonToTuple G v S).2.2.1 := by rw [h]
      have e4 : b₂ = (pentagonToTuple G v S).2.2.2 := by rw [h]
      subst e1; subst e2; subst e3; subst e4
      exact brrb_of_pentagon v S hS.1 hS.2
    · -- here `h` reads the *reversed* tuple, so the components come off it by
      -- projection rather than by rewriting
      have e1 : b₁ = (pentagonToTuple G v S).2.2.2 := (congrArg (·.1) h).symm
      have e2 : r₁ = (pentagonToTuple G v S).2.2.1 := (congrArg (·.2.1) h).symm
      have e3 : r₂ = (pentagonToTuple G v S).2.1 := (congrArg (·.2.2.1) h).symm
      have e4 : b₂ = (pentagonToTuple G v S).1 := (congrArg (·.2.2.2) h).symm
      subst e1; subst e2; subst e3; subst e4
      exact brrb_of_pentagon_rev v S hS.1 hS.2

/-! ## The card arithmetic -/

/-- A pentagon is recovered from its tuple: `S` is `v` together with the four
components.  This is what makes the two images disjoint — a tuple determines the
pentagon it came from, so a coincidence between the forward and reversed images
would force a pentagon's tuple to equal its own reversal. -/
theorem pentagonToTuple_span (v : Fin G.size) (S : Finset (Fin G.size))
    (hpS : IsPentagon G S) (hvS : v ∈ S) :
    S = {v, (pentagonToTuple G v S).1, (pentagonToTuple G v S).2.1,
         (pentagonToTuple G v S).2.2.1, (pentagonToTuple G v S).2.2.2} := by
  obtain ⟨ma, mb, mc, md⟩ := pentagonToTuple_mem G v S hpS hvS
  apply Finset.Subset.antisymm
  · intro x hx
    rcases pentagonToTuple_cover G v S hpS hvS x hx with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem revTuple_involutive {n : ℕ} (p : Fin n × Fin n × Fin n × Fin n) :
    revTuple (revTuple p) = p := rfl

theorem revTuple_injective {n : ℕ} : Function.Injective (revTuple (n := n)) :=
  fun p q h => by rw [← revTuple_involutive p, h, revTuple_involutive]

open Classical in
/-- The forward and reversed images are disjoint.  If a tuple lay in both, the
two pentagons would span the same vertex set, hence be equal — and then that
pentagon's tuple would be its own reversal, which `pentagonToTuple_ne_rev`
forbids. -/
theorem fwd_rev_disjoint (v : Fin G.size) :
    Disjoint ((pentSetOf G v).image (pentagonToTuple G v))
      ((pentSetOf G v).image (fun S => revTuple (pentagonToTuple G v S))) := by
  rw [Finset.disjoint_left]
  rintro p hp hq
  simp only [pentSetOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  obtain ⟨S₁, hS₁, h₁⟩ := hp
  obtain ⟨S₂, hS₂, h₂⟩ := hq
  -- `p` determines its pentagon, forwards and backwards alike
  have hspan₁ : S₁ = {v, p.1, p.2.1, p.2.2.1, p.2.2.2} := by
    rw [pentagonToTuple_span v S₁ hS₁.1 hS₁.2, h₁]
  have hrev : pentagonToTuple G v S₂ = revTuple p := by
    rw [← h₂, revTuple_involutive]
  have hspan₂ : S₂ = {v, p.2.2.2, p.2.2.1, p.2.1, p.1} := by
    rw [pentagonToTuple_span v S₂ hS₂.1 hS₂.2, hrev]; rfl
  have hSeq : S₁ = S₂ := by
    rw [hspan₁, hspan₂]; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  subst hSeq
  exact pentagonToTuple_ne_rev v S₁ hS₁.1 hS₁.2 (h₁.trans h₂.symm)

open Classical in
/-- **`(a2a)`'s BRRB equality.**  `brrb_reduction` gets `2·P(G,v) ≤ brrbCount G'`
and needs no more; `(a2a)` needs the equality, and this is it. -/
theorem brrbCount_eq_two_mul (htf : IsTriangleFree G) (hreg : IsRegular G)
    (v : Fin G.size) :
    brrbCount (vColouredClass G v htf hreg) = 2 * pentagonCountAt G v := by
  rw [← brrbSetOf_card G v htf hreg, ← pentSetOf_card G v, brrbSetOf_eq_union htf v,
    Finset.card_union_of_disjoint (fwd_rev_disjoint v)]
  have hinj : Set.InjOn (pentagonToTuple G v) ↑(pentSetOf G v) :=
    pentagonToTuple_injOn G v
  rw [Finset.card_image_of_injOn hinj,
    Finset.card_image_of_injOn (fun a ha b hb h => hinj ha hb (revTuple_injective h))]
  ring

/-! ## Towards the fibre count

`(a2a)`'s last step is `Σ_{|S|=8} n₁(G'[S]) = (#τ₁-embeddings)·C(Δ−1,4)`.  The
`C(Δ−1,4)` is the number of ways to complete a BRRB tuple to an 8-set, all four
extra vertices lying in the root's neighbourhood — and that count is `Δ−1`, not
`Δ`, exactly because the root has **one** neighbour inside the tuple.  Both
exclusions below are structural, not bookkeeping. -/

open Classical in
/-- The root's neighbourhood meets its own BRRB tuple in exactly `r₁`.

`r₂` is excluded by **triangle-freeness** (`b₁r₁r₂` would close), `b₂` by **black
independence** (both are black), and `b₁` by irreflexivity.  Drop either
structural hypothesis and the count below is no longer `Δ−1`. -/
theorem root_nbhd_inter_tuple (C : ColouredGraphClass) {b₁ r₁ r₂ b₂ : Fin C.graph.size}
    (hcb₁ : C.colouring b₁ = 1) (hcb₂ : C.colouring b₂ = 1)
    (hb₁r₁ : C.graph.graph.Adj b₁ r₁) (hr₁r₂ : C.graph.graph.Adj r₁ r₂)
    (hr₂b₂ : C.graph.graph.Adj r₂ b₂) :
    (Finset.univ.filter (fun u => C.graph.graph.Adj b₁ u)) ∩ {b₁, r₁, r₂, b₂} = {r₁} := by
  have hnr₂ : ¬ C.graph.graph.Adj b₁ r₂ := fun h => C.triangleFree b₁ r₁ r₂ hb₁r₁ hr₁r₂ h
  have hnb₂ : ¬ C.graph.graph.Adj b₁ b₂ := C.blackIndependent b₁ b₂ hcb₁ hcb₂
  ext u
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hadj, rfl | rfl | rfl | rfl⟩
    · exact absurd hadj (by simp)
    · rfl
    · exact absurd hadj hnr₂
    · exact absurd hadj hnb₂
  · rintro rfl
    exact ⟨hb₁r₁, Or.inr (Or.inl rfl)⟩

open Classical in
/-- Hence the root has exactly `Δ−1` neighbours outside its tuple — the pool the
four extra vertices of an 8-set are drawn from, giving `(a2a)`'s `C(Δ−1,4)`. -/
theorem card_root_nbhd_sdiff_tuple (C : ColouredGraphClass)
    {b₁ r₁ r₂ b₂ : Fin C.graph.size}
    (hcb₁ : C.colouring b₁ = 1) (hcb₂ : C.colouring b₂ = 1)
    (hb₁r₁ : C.graph.graph.Adj b₁ r₁) (hr₁r₂ : C.graph.graph.Adj r₁ r₂)
    (hr₂b₂ : C.graph.graph.Adj r₂ b₂) :
    ((Finset.univ.filter (fun u => C.graph.graph.Adj b₁ u)) \ {b₁, r₁, r₂, b₂}).card
      = maxDegree C.graph - 1 := by
  have hnb : (Finset.univ.filter (fun u => C.graph.graph.Adj b₁ u)).card
      = maxDegree C.graph := C.regular b₁
  have hsub : (Finset.univ.filter (fun u => C.graph.graph.Adj b₁ u)) ∩ {b₁, r₁, r₂, b₂}
      = {r₁} := root_nbhd_inter_tuple C hcb₁ hcb₂ hb₁r₁ hr₁r₂ hr₂b₂
  have hcard := Finset.card_sdiff_add_card_inter
    (Finset.univ.filter (fun u => C.graph.graph.Adj b₁ u)) ({b₁, r₁, r₂, b₂} : Finset _)
  rw [hsub, Finset.card_singleton, hnb] at hcard
  omega

/-- The four vertices of a tuple, as a set. -/
def tupleSet {n : ℕ} (p : Fin n × Fin n × Fin n × Fin n) : Finset (Fin n) :=
  {p.1, p.2.1, p.2.2.1, p.2.2.2}

theorem card_tupleSet {n : ℕ} {p : Fin n × Fin n × Fin n × Fin n}
    (d1 : p.1 ≠ p.2.1) (d2 : p.1 ≠ p.2.2.1) (d3 : p.1 ≠ p.2.2.2)
    (d4 : p.2.1 ≠ p.2.2.1) (d5 : p.2.1 ≠ p.2.2.2) (d6 : p.2.2.1 ≠ p.2.2.2) :
    (tupleSet p).card = 4 := by
  rw [tupleSet, Finset.card_insert_of_notMem (by simp [d1, d2, d3]),
    Finset.card_insert_of_notMem (by simp [d4, d5]),
    Finset.card_insert_of_notMem (by simp [d6]), Finset.card_singleton]

open Classical in
/-- The **fibre** over a BRRB tuple: the ways to complete it to an 8-set, every
added vertex lying in the root's neighbourhood.  This is `(a2a)`'s `C(Δ−1,4)`. -/
noncomputable def fibreOf (C : ColouredGraphClass)
    (p : Fin C.graph.size × Fin C.graph.size × Fin C.graph.size × Fin C.graph.size) :
    Finset (Finset (Fin C.graph.size)) :=
  (((Finset.univ.filter (fun u => C.graph.graph.Adj p.1 u)) \ tupleSet p)).powersetCard 4

open Classical in
/-- **The fibre has exactly `C(Δ−1,4)` elements.**  Immediate from
`card_root_nbhd_sdiff_tuple` — which is where triangle-freeness and black
independence were spent. -/
theorem card_fibreOf (C : ColouredGraphClass)
    {b₁ r₁ r₂ b₂ : Fin C.graph.size}
    (hcb₁ : C.colouring b₁ = 1) (hcb₂ : C.colouring b₂ = 1)
    (hb₁r₁ : C.graph.graph.Adj b₁ r₁) (hr₁r₂ : C.graph.graph.Adj r₁ r₂)
    (hr₂b₂ : C.graph.graph.Adj r₂ b₂) :
    (fibreOf C (b₁, r₁, r₂, b₂)).card = Nat.choose (maxDegree C.graph - 1) 4 := by
  unfold fibreOf
  rw [Finset.card_powersetCard]
  congr 1
  exact card_root_nbhd_sdiff_tuple C hcb₁ hcb₂ hb₁r₁ hr₁r₂ hr₂b₂

open Classical in
/-- Completing a tuple by a member of its fibre gives an 8-set. -/
theorem card_union_fibre (C : ColouredGraphClass)
    {p : Fin C.graph.size × Fin C.graph.size × Fin C.graph.size × Fin C.graph.size}
    (d1 : p.1 ≠ p.2.1) (d2 : p.1 ≠ p.2.2.1) (d3 : p.1 ≠ p.2.2.2)
    (d4 : p.2.1 ≠ p.2.2.1) (d5 : p.2.1 ≠ p.2.2.2) (d6 : p.2.2.1 ≠ p.2.2.2)
    {T : Finset (Fin C.graph.size)} (hT : T ∈ fibreOf C p) :
    (tupleSet p ∪ T).card = 8 := by
  unfold fibreOf at hT
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨hsub, hcard⟩ := hT
  have hdisj : Disjoint (tupleSet p) T := by
    rw [Finset.disjoint_right]
    intro x hx hxt
    exact (Finset.mem_sdiff.mp (hsub hx)).2 hxt
  rw [Finset.card_union_of_disjoint hdisj, card_tupleSet d1 d2 d3 d4 d5 d6, hcard]

open Classical in
/-- The completion map is injective: the added set is recovered as `S \ tuple`. -/
theorem union_fibre_injective (C : ColouredGraphClass)
    {p : Fin C.graph.size × Fin C.graph.size × Fin C.graph.size × Fin C.graph.size} :
    Set.InjOn (fun T => tupleSet p ∪ T) ↑(fibreOf C p) := by
  intro T₁ h₁ T₂ h₂ h
  simp only [fibreOf, Finset.coe_mem, Finset.mem_coe, Finset.mem_powersetCard] at h₁ h₂
  have hd₁ : Disjoint (tupleSet p) T₁ := Finset.disjoint_right.mpr
    (fun x hx hxt => (Finset.mem_sdiff.mp (h₁.1 hx)).2 hxt)
  have hd₂ : Disjoint (tupleSet p) T₂ := Finset.disjoint_right.mpr
    (fun x hx hxt => (Finset.mem_sdiff.mp (h₂.1 hx)).2 hxt)
  have e₁ := Finset.union_sdiff_cancel_left hd₁
  have e₂ := Finset.union_sdiff_cancel_left hd₂
  -- `h` arrives beta-unreduced; restate it at the reduced type
  have h' : tupleSet p ∪ T₁ = tupleSet p ∪ T₂ := h
  rw [← e₁, ← e₂, h']

open Classical in
/-- **Surjectivity of the completion map.**  Every 8-set that contains the tuple
and whose extra vertices all lie in the root's neighbourhood arises as
`tuple ∪ T` for a member `T` of the fibre — namely `T = S \ tuple`. -/
theorem union_fibre_surjective (C : ColouredGraphClass)
    {p : Fin C.graph.size × Fin C.graph.size × Fin C.graph.size × Fin C.graph.size}
    (hcard4 : (tupleSet p).card = 4)
    {S : Finset (Fin C.graph.size)} (hS8 : S.card = 8)
    (hsub : tupleSet p ⊆ S)
    (hnb : ∀ u ∈ S, u ∉ tupleSet p → C.graph.graph.Adj p.1 u) :
    ∃ T ∈ fibreOf C p, tupleSet p ∪ T = S := by
  refine ⟨S \ tupleSet p, ?_, Finset.union_sdiff_of_subset hsub⟩
  rw [fibreOf, Finset.mem_powersetCard]
  constructor
  · intro x hx
    rw [Finset.mem_sdiff] at hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hnb x hx.1 hx.2⟩, hx.2⟩
  · -- `Finset.card_sdiff` here is the unconditional form, `#(s \ t) = #s - #(t ∩ s)`
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hS8, hcard4]

open Classical in
/-- `brrbCount`'s filter set, named, for a general coloured class. -/
noncomputable def brrbFilter (C : ColouredGraphClass) :
    Finset (Fin C.graph.size × Fin C.graph.size × Fin C.graph.size × Fin C.graph.size) :=
  Finset.univ.filter (fun p =>
    p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2.1 ∧ p.1 ≠ p.2.2.2 ∧ p.2.1 ≠ p.2.2.1 ∧
    p.2.1 ≠ p.2.2.2 ∧ p.2.2.1 ≠ p.2.2.2 ∧
    C.colouring p.1 = 1 ∧ C.colouring p.2.1 = 0 ∧
    C.colouring p.2.2.1 = 0 ∧ C.colouring p.2.2.2 = 1 ∧
    C.graph.graph.Adj p.1 p.2.1 ∧ C.graph.graph.Adj p.2.1 p.2.2.1 ∧
    C.graph.graph.Adj p.2.2.1 p.2.2.2)

theorem brrbFilter_card (C : ColouredGraphClass) :
    (brrbFilter C).card = brrbCount C := rfl

open Classical in
/-- **The fibre count, summed.**  Every BRRB tuple has the *same* number of
completions, `C(Δ−1,4)`, so the total is a product.  This is `(a2a)`'s right-hand
side, still at the `Finset` level. -/
theorem sum_fibreOf_card (C : ColouredGraphClass) :
    Finset.sum (brrbFilter C) (fun p => (fibreOf C p).card)
      = brrbCount C * Nat.choose (maxDegree C.graph - 1) 4 := by
  rw [Finset.sum_congr rfl (fun p hp => ?_), Finset.sum_const, smul_eq_mul,
    brrbFilter_card]
  · rw [brrbFilter, Finset.mem_filter] at hp
    obtain ⟨-, -, -, -, -, -, -, c1, -, -, c4, a1, a2, a3⟩ := hp
    exact card_fibreOf C c1 c4 a1 a2 a3

/-! ## Towards the transfer across `genInducedSubflag`

`sum_n1_host`'s left side counts rooted embeddings into `C[S]`; the fibre count
above counts tuples in `C`.  The bridge is composition with the inclusion
`C[S] → C`, which exists already as `GenInducedEmbedding.comp`
(`Basic.lean:168`) — it is *not* missing infrastructure, contrary to a first
look that grepped only `LocalFlagAlgebra`. -/

/-- Composing with the subflag inclusion is injective on embeddings: the
inclusion is itself injective, so it cancels. -/
theorem incl_comp_injective {R : RelUniverse} {σ : GenFlagType R}
    {F G : GenFlag R σ} (S : Finset (Fin G.size))
    (hS : ∀ i : Fin σ.size, G.embedding i ∈ S) (hσ : σ.size ≤ S.card) :
    Function.Injective
      (fun e : GenInducedEmbedding R σ F (G.genInducedSubflag S hS hσ) =>
        GenInducedEmbedding.comp (G.genInducedSubflag_incl S hS hσ) e) := by
  intro e₁ e₂ h
  have hfun : ∀ x, (G.genInducedSubflag_incl S hS hσ).toFun (e₁.toFun x)
      = (G.genInducedSubflag_incl S hS hσ).toFun (e₂.toFun x) :=
    fun x => congrFun (congrArg GenInducedEmbedding.toFun h) x
  cases e₁; cases e₂
  simp only [GenInducedEmbedding.mk.injEq]
  funext x
  exact (G.genInducedSubflag_incl S hS hσ).injective (hfun x)

/-- The composite lands inside `S` — the inclusion's range *is* `S`. -/
theorem range_incl_comp {R : RelUniverse} {σ : GenFlagType R}
    {F G : GenFlag R σ} (S : Finset (Fin G.size))
    (hS : ∀ i : Fin σ.size, G.embedding i ∈ S) (hσ : σ.size ≤ S.card)
    (e : GenInducedEmbedding R σ F (G.genInducedSubflag S hS hσ)) :
    Set.range (GenInducedEmbedding.comp (G.genInducedSubflag_incl S hS hσ) e).toFun ⊆ ↑S := by
  rintro x ⟨z, rfl⟩
  exact Finset.mem_coe.mpr (Finset.orderEmbOfFin_mem S rfl _)

/-! The inverse direction is already in `Basic`: `GenInducedEmbedding.genRestrictToSubflag`
takes an embedding into `G` whose image lies in `S` and restricts it to `G[S]`,
and `Basic.lean:3014` proves the inclusion undoes it.  So both halves of the
correspondence exist; what `(a2a)` still needs is the **root condition**
transported across them. -/

/-- **Adjacency transfers across the subflag inclusion.**  The inclusion is
induced, and `colouredGraphUniverse`'s `comap` acts on the graph component as
`SimpleGraph.comap`, so adjacency inside `G[S]` is adjacency in `G` between the
images.  This is what lets the root condition be read on either side. -/
theorem subflag_adj_iff {k : ℕ} (G : GenFlag (colouredGraphUniverse k)
      (GenFlagType.empty (colouredGraphUniverse k)))
    (S : Finset (Fin G.size))
    (hS : ∀ i : Fin (GenFlagType.empty (colouredGraphUniverse k)).size, G.embedding i ∈ S)
    (hσ : (GenFlagType.empty (colouredGraphUniverse k)).size ≤ S.card)
    (x y : Fin (G.genInducedSubflag S hS hσ).size) :
    ((G.genInducedSubflag S hS hσ).str.1).Adj x y ↔
      (G.str.1).Adj ((G.genInducedSubflag_incl S hS hσ).toFun x)
        ((G.genInducedSubflag_incl S hS hσ).toFun y) := by
  conv_lhs => rw [← (G.genInducedSubflag_incl S hS hσ).isInduced]
  rfl

/-- **The root condition transfers.**  "Every vertex outside the image is
adjacent to the root's image" says the same thing in `G[S]` and in `G`, because
the inclusion is injective with range exactly `S`: a vertex of `G[S]` outside the
image corresponds to a vertex of `S` outside the composite's image. -/
theorem rootCond_iff {k : ℕ} (G : GenFlag (colouredGraphUniverse k)
      (GenFlagType.empty (colouredGraphUniverse k)))
    {F : GenFlag (colouredGraphUniverse k)
      (GenFlagType.empty (colouredGraphUniverse k))}
    (S : Finset (Fin G.size))
    (hS : ∀ i : Fin (GenFlagType.empty (colouredGraphUniverse k)).size, G.embedding i ∈ S)
    (hσ : (GenFlagType.empty (colouredGraphUniverse k)).size ≤ S.card)
    (e : GenInducedEmbedding (colouredGraphUniverse k)
      (GenFlagType.empty (colouredGraphUniverse k)) F (G.genInducedSubflag S hS hσ))
    (root : Fin F.size) :
    (∀ w : Fin (G.genInducedSubflag S hS hσ).size, (∀ i, e.toFun i ≠ w) →
        ((G.genInducedSubflag S hS hσ).str.1).Adj (e.toFun root) w)
      ↔ (∀ w : Fin G.size, w ∈ S →
          (∀ i, (GenInducedEmbedding.comp (G.genInducedSubflag_incl S hS hσ) e).toFun i ≠ w) →
          (G.str.1).Adj
            ((GenInducedEmbedding.comp (G.genInducedSubflag_incl S hS hσ) e).toFun root) w) := by
  set incl := G.genInducedSubflag_incl S hS hσ with hincl
  constructor
  · intro h w hwS hne
    -- `w ∈ S` is in the inclusion's range, so it is `incl z` for some `z`
    obtain ⟨z, hz⟩ : ∃ z, incl.toFun z = w := by
      have : w ∈ Set.range incl.toFun := by
        rw [hincl]
        exact ⟨(S.orderIsoOfFin rfl).symm ⟨w, hwS⟩, by
          change ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨w, hwS⟩)) = w
          simp [OrderIso.apply_symm_apply]⟩
      exact this
    subst hz
    exact (subflag_adj_iff G S hS hσ _ _).mp
      (h z (fun i hi => hne i (congrArg incl.toFun hi)))
  · intro h w hne
    have hwS : incl.toFun w ∈ S := Finset.orderEmbOfFin_mem S rfl _
    exact (subflag_adj_iff G S hS hσ _ _).mpr
      (h (incl.toFun w) hwS (fun i hi => hne i (incl.injective hi)))

/-- Two induced embeddings agreeing as functions are equal. -/
theorem genEmb_ext {R : RelUniverse} {σ : GenFlagType R} {F G : GenFlag R σ}
    {e₁ e₂ : GenInducedEmbedding R σ F G} (h : e₁.toFun = e₂.toFun) : e₁ = e₂ := by
  cases e₁; cases e₂; simp only [GenInducedEmbedding.mk.injEq]; exact h

theorem comp_restrict {R : RelUniverse} {σ : GenFlagType R} {F G : GenFlag R σ}
    (e : GenInducedEmbedding R σ F G) (S : Finset (Fin G.size))
    (hS : ∀ i : Fin σ.size, G.embedding i ∈ S) (hσ : σ.size ≤ S.card)
    (himg : ∀ x, e.toFun x ∈ S) :
    GenInducedEmbedding.comp (G.genInducedSubflag_incl S hS hσ)
      (e.genRestrictToSubflag S hS hσ himg) = e :=
  genEmb_ext (funext (fun x =>
    GenInducedEmbedding.genRestrictToSubflag_comp_incl e S hS hσ himg x))

open Classical in
/-- **The transfer.**  Rooted embeddings into `G[S]` are exactly the rooted
embeddings into `G` whose image lies in `S`, the root condition read relative to
`S`.  Every ingredient was proved separately; this assembles them. -/
theorem rootedCountG_subflag
    {F G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (S : Finset (Fin G.size))
    (hS : ∀ i : Fin (GenFlagType.empty (colouredGraphUniverse 2)).size, G.embedding i ∈ S)
    (hσ : (GenFlagType.empty (colouredGraphUniverse 2)).size ≤ S.card)
    (root : Fin F.size) :
    PentagonQIsoInvariance.rootedCountG F (G.genInducedSubflag S hS hσ) root
      = Nat.card {e : GenInducedEmbedding (colouredGraphUniverse 2)
            (GenFlagType.empty (colouredGraphUniverse 2)) F G //
          (∀ x, e.toFun x ∈ S) ∧
          (∀ w : Fin G.size, w ∈ S → (∀ i, e.toFun i ≠ w) →
            (G.str.1).Adj (e.toFun root) w)} := by
  unfold PentagonQIsoInvariance.rootedCountG
  apply Nat.card_eq_of_bijective (fun x =>
    ⟨GenInducedEmbedding.comp (G.genInducedSubflag_incl S hS hσ) x.1,
      fun z => Finset.orderEmbOfFin_mem S rfl _,
      (rootCond_iff G S hS hσ x.1 root).mp x.2⟩)
  constructor
  · rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ h
    have := incl_comp_injective S hS hσ (congrArg Subtype.val h)
    exact Subtype.ext this
  · rintro ⟨e, himg, hrc⟩
    refine ⟨⟨e.genRestrictToSubflag S hS hσ himg, ?_⟩, ?_⟩
    · rw [rootCond_iff G S hS hσ _ root, comp_restrict e S hS hσ himg]
      exact fun w hw hne => hrc w hw hne
    · exact Subtype.ext (comp_restrict e S hS hσ himg)

#print axioms genEmb_ext
#print axioms comp_restrict
#print axioms rootedCountG_subflag
#print axioms subflag_adj_iff
#print axioms rootCond_iff
#print axioms incl_comp_injective
#print axioms range_incl_comp
#print axioms union_fibre_surjective
#print axioms brrbFilter_card
#print axioms sum_fibreOf_card
#print axioms card_tupleSet
#print axioms card_fibreOf
#print axioms card_union_fibre
#print axioms union_fibre_injective
/-- **A BRRB tuple is automatically induced.**  `brrbFilter` asks only for the
three path edges, while an *induced* embedding additionally needs the three
non-edges — and on a `ColouredGraphClass` it gets them free: `b₁r₂` and `r₁b₂`
would close a triangle, `b₁b₂` would be a black edge.

This is why `brrbCount`, defined by a filter that never mentions non-edges,
agrees with an induced-embedding count (`brrbCount_eq_genInducedCount`).  It is
also what the fibre count needs when the tuple is read as a flag embedding. -/
theorem brrb_nonedges (C : ColouredGraphClass) {b₁ r₁ r₂ b₂ : Fin C.graph.size}
    (hcb₁ : C.colouring b₁ = 1) (hcb₂ : C.colouring b₂ = 1)
    (hb₁r₁ : C.graph.graph.Adj b₁ r₁) (hr₁r₂ : C.graph.graph.Adj r₁ r₂)
    (hr₂b₂ : C.graph.graph.Adj r₂ b₂) :
    ¬ C.graph.graph.Adj b₁ r₂ ∧ ¬ C.graph.graph.Adj r₁ b₂ ∧
      ¬ C.graph.graph.Adj b₁ b₂ :=
  ⟨fun h => C.triangleFree b₁ r₁ r₂ hb₁r₁ hr₁r₂ h,
   fun h => C.triangleFree r₁ r₂ b₂ hr₁r₂ hr₂b₂ h,
   C.blackIndependent b₁ b₂ hcb₁ hcb₂⟩

/-- **`τ₁` is the BRRB pattern.**  `tauFlag tau1 4` and `brrbGenFlag` are the
same flag: the path `0-1-2-3` coloured `B-R-R-B`, `tau1.cols = #[1,0,0,1]` matching
`brrbPattern`'s `if v = 0 ∨ v = 3 then 1 else 0`.

They are *not* definitionally equal — the graphs are `SimpleGraph.fromRel` of
different-but-equal relations, and `fromRel` does not reduce — so this goes
through extensionality.  Note what does **not** work: `tau1.padj` cannot be
evaluated at all, by `rfl`, `simp` or `decide`, because `Array.map` does not
kernel-reduce (`Array.range` does).  The way through is never to ask for the
array, only for its entries, which `simp [patC, tau1]` computes symbolically.

This identification lets `(a2a)` reuse `brrbCount_eq_genInducedCount`. -/
theorem tauFlag_tau1_eq_brrbGenFlag :
    PentagonQMuFlag.tauFlag PentagonQWeights.tau1 4 = brrbGenFlag :=
  GenFlag.empty_ext _ _ rfl <| by
    apply Prod.ext
    · ext u v
      simp only [PentagonQMuFlag.tauFlag, CGraph.toGenFlag, brrbGenFlag, brrbPattern,
        brrbFlag, ColouredGraph.toGenFlag, pathGraph4, SimpleGraph.fromRel_adj,
        PentagonQRooted.patC, PentagonQWeights.tau1]
      fin_cases u <;> fin_cases v <;> simp
    · funext v
      simp only [PentagonQMuFlag.tauFlag, CGraph.toGenFlag, brrbGenFlag, brrbPattern,
        ColouredGraph.toGenFlag, PentagonQRooted.patC, PentagonQWeights.tau1]
      fin_cases v <;> rfl

/-- **Reading a BRRB tuple off an embedding.**  An induced embedding of
`brrbGenFlag` carries its whole defining data in `isInduced`: the colour
component gives the two black endpoints, the graph component the three path
edges.  This is the direction the fibre count needs — enough to discharge
`card_fibreOf`'s hypotheses, without building a bijection. -/
theorem brrb_of_embedding (C : ColouredGraphClass)
    (e : GenInducedEmbedding CG2 (GenFlagType.empty CG2) brrbGenFlag C.toGenFlag) :
    (∀ i : Fin brrbGenFlag.size,
        C.colouring (e.toFun i) = brrbPattern.colouring i) ∧
    (∀ i j : Fin brrbGenFlag.size,
        C.graph.graph.Adj (e.toFun i) (e.toFun j) ↔ pathGraph4.Adj i j) := by
  have h := e.isInduced
  simp only [colouredGraphUniverse, brrbGenFlag, brrbPattern, brrbFlag,
    ColouredGraph.toGenFlag, ColouredGraphClass.toGenFlag,
    ColouredGraphClass.toColouredGraph] at h
  constructor
  · intro i
    have hc := congrArg Prod.snd h
    simp only at hc
    exact congrFun hc i
  · intro i j
    have hg := congrArg Prod.fst h
    simp only at hg
    rw [← hg]
    rfl

theorem brrbGenFlag_size : brrbGenFlag.size = 4 := rfl

open Classical in
/-- The four vertices of an embedding of `brrbGenFlag` form a BRRB tuple. -/
theorem mem_brrbFilter_of_embedding (C : ColouredGraphClass)
    (e : GenInducedEmbedding CG2 (GenFlagType.empty CG2) brrbGenFlag C.toGenFlag) :
    (e.toFun ⟨0, by rw [brrbGenFlag_size]; omega⟩,
     e.toFun ⟨1, by rw [brrbGenFlag_size]; omega⟩,
     e.toFun ⟨2, by rw [brrbGenFlag_size]; omega⟩,
     e.toFun ⟨3, by rw [brrbGenFlag_size]; omega⟩) ∈ brrbFilter C := by
  obtain ⟨hcol, hadj⟩ := brrb_of_embedding C e
  have hne : ∀ a b : Fin brrbGenFlag.size, a ≠ b → e.toFun a ≠ e.toFun b :=
    fun a b hab h => hab (e.injective h)
  rw [brrbFilter, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  refine ⟨hne _ _ (by decide), hne _ _ (by decide), hne _ _ (by decide),
    hne _ _ (by decide), hne _ _ (by decide), hne _ _ (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcol]; rfl
  · rw [hcol]; rfl
  · rw [hcol]; rfl
  · rw [hcol]; rfl
  · exact (hadj _ _).mpr (by simp [pathGraph4, SimpleGraph.fromRel_adj])
  · exact (hadj _ _).mpr (by simp [pathGraph4, SimpleGraph.fromRel_adj])
  · exact (hadj _ _).mpr (by simp [pathGraph4, SimpleGraph.fromRel_adj])

/-- Double counting: summing a filter's size over one index equals summing the
transposed filter's size over the other. -/
theorem double_count {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (P : α → β → Prop) [∀ a b, Decidable (P a b)] :
    Finset.sum A (fun a => (B.filter (fun b => P a b)).card)
      = Finset.sum B (fun b => (A.filter (fun a => P a b)).card) := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

open Classical in
/-- **The inner count.**  For a fixed BRRB tuple, the 8-sets containing it whose
extra vertices lie in the root's neighbourhood number exactly `C(Δ−1,4)` — the
completion map is a bijection from the fibre onto them. -/
theorem card_valid_eightSets (C : ColouredGraphClass)
    {p : Fin C.graph.size × Fin C.graph.size × Fin C.graph.size × Fin C.graph.size}
    (hp : p ∈ brrbFilter C) :
    (Finset.univ.filter (fun S : Finset (Fin C.graph.size) =>
        S.card = 8 ∧ tupleSet p ⊆ S ∧
          ∀ u ∈ S, u ∉ tupleSet p → C.graph.graph.Adj p.1 u)).card
      = Nat.choose (maxDegree C.graph - 1) 4 := by
  rw [brrbFilter, Finset.mem_filter] at hp
  obtain ⟨-, d1, d2, d3, d4, d5, d6, c1, -, -, c4, a1, a2, a3⟩ := hp
  have h4 : (tupleSet p).card = 4 := card_tupleSet d1 d2 d3 d4 d5 d6
  -- the valid 8-sets are exactly the completions
  have himg : (Finset.univ.filter (fun S : Finset (Fin C.graph.size) =>
        S.card = 8 ∧ tupleSet p ⊆ S ∧
          ∀ u ∈ S, u ∉ tupleSet p → C.graph.graph.Adj p.1 u))
      = (fibreOf C p).image (fun T => tupleSet p ∪ T) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hcard, hsub, hnb⟩
      obtain ⟨T, hT, hTS⟩ := union_fibre_surjective C h4 hcard hsub hnb
      exact ⟨T, hT, hTS⟩
    · rintro ⟨T, hT, rfl⟩
      refine ⟨card_union_fibre C d1 d2 d3 d4 d5 d6 hT, Finset.subset_union_left, ?_⟩
      intro u hu hnu
      rcases Finset.mem_union.mp hu with h | h
      · exact absurd h hnu
      · rw [fibreOf, Finset.mem_powersetCard] at hT
        exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hT.1 h)).1).2
  rw [himg, Finset.card_image_of_injOn (union_fibre_injective C), card_fibreOf C c1 c4 a1 a2 a3]

/-- The four vertices of an embedding of `brrbGenFlag`, as a tuple. -/
noncomputable def tupleOf (C : ColouredGraphClass)
    (e : GenInducedEmbedding CG2 (GenFlagType.empty CG2) brrbGenFlag C.toGenFlag) :
    Fin C.graph.size × Fin C.graph.size × Fin C.graph.size × Fin C.graph.size :=
  (e.toFun ⟨0, by rw [brrbGenFlag_size]; omega⟩,
   e.toFun ⟨1, by rw [brrbGenFlag_size]; omega⟩,
   e.toFun ⟨2, by rw [brrbGenFlag_size]; omega⟩,
   e.toFun ⟨3, by rw [brrbGenFlag_size]; omega⟩)

/-- The tuple's vertex set is the embedding's image.  `brrbGenFlag` has four
vertices, so "some `e i`" and "one of the four" are the same statement — which is
what lets the fibre count, phrased on tuples, be applied to embeddings. -/
theorem mem_tupleSet_iff (C : ColouredGraphClass)
    (e : GenInducedEmbedding CG2 (GenFlagType.empty CG2) brrbGenFlag C.toGenFlag)
    (u : Fin C.graph.size) :
    u ∈ tupleSet (tupleOf C e) ↔ ∃ i, e.toFun i = u := by
  simp only [tupleSet, tupleOf, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h | h) <;> exact ⟨_, h.symm⟩
  · rintro ⟨i, rfl⟩
    have : i.val < 4 := by rw [← brrbGenFlag_size]; exact i.isLt
    interval_cases hi : i.val
    · exact Or.inl (congrArg e.toFun (Fin.ext hi))
    · exact Or.inr (Or.inl (congrArg e.toFun (Fin.ext hi)))
    · exact Or.inr (Or.inr (Or.inl (congrArg e.toFun (Fin.ext hi))))
    · exact Or.inr (Or.inr (Or.inr (congrArg e.toFun (Fin.ext hi))))

open Classical in
/-- `rootedCountG` into a subflag, as a `Finset.card` rather than a `Nat.card` —
the shape `double_count` needs. -/
theorem rootedCountG_subflag_card
    {F : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (S : Finset (Fin G.size))
    (hS : ∀ i : Fin (GenFlagType.empty (colouredGraphUniverse 2)).size, G.embedding i ∈ S)
    (hσ : (GenFlagType.empty (colouredGraphUniverse 2)).size ≤ S.card)
    (root : Fin F.size) :
    PentagonQIsoInvariance.rootedCountG F (G.genInducedSubflag S hS hσ) root
      = (Finset.univ.filter (fun e : GenInducedEmbedding (colouredGraphUniverse 2)
            (GenFlagType.empty (colouredGraphUniverse 2)) F G =>
          (∀ x, e.toFun x ∈ S) ∧
          (∀ w : Fin G.size, w ∈ S → (∀ i, e.toFun i ≠ w) →
            (G.str.1).Adj (e.toFun root) w))).card := by
  rw [rootedCountG_subflag S hS hσ root, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The `τ₁` root: vertex `0` of `brrbGenFlag`, a black path endpoint. -/
def brrbRoot : Fin brrbGenFlag.size := ⟨0, by rw [brrbGenFlag_size]; omega⟩

open Classical in
/-- The two conditions read on an embedding are the two read on its tuple. -/
theorem embCond_iff_tupleCond (C : ColouredGraphClass)
    (e : GenInducedEmbedding CG2 (GenFlagType.empty CG2) brrbGenFlag C.toGenFlag)
    (S : Finset (Fin C.graph.size)) :
    ((∀ x, e.toFun x ∈ S) ∧
       (∀ w : Fin C.graph.size, w ∈ S → (∀ i, e.toFun i ≠ w) →
         (C.toGenFlag.str.1).Adj (e.toFun brrbRoot) w))
      ↔ (tupleSet (tupleOf C e) ⊆ S ∧
          ∀ u ∈ S, u ∉ tupleSet (tupleOf C e) → C.graph.graph.Adj (tupleOf C e).1 u) := by
  have hmem := mem_tupleSet_iff C e
  constructor
  · rintro ⟨himg, hrc⟩
    refine ⟨fun u hu => ?_, fun u hu hnu => ?_⟩
    · obtain ⟨i, rfl⟩ := (hmem u).mp hu; exact himg i
    · exact hrc u hu (fun i hi => hnu ((hmem u).mpr ⟨i, hi⟩))
  · rintro ⟨hsub, hrc⟩
    refine ⟨fun x => hsub ((hmem _).mpr ⟨x, rfl⟩), fun w hw hne => ?_⟩
    exact hrc w hw (fun hcon => by obtain ⟨i, hi⟩ := (hmem w).mp hcon; exact hne i hi)

open Classical in
/-- **`(a2a)`'s fibre count, at the flag level.**  Summing the rooted `τ₁`-count
over all 8-subsets gives the number of BRRB embeddings times `C(Δ−1,4)`.

The double-counting swap: the left side counts pairs (8-set, embedding into it),
the right counts the same pairs grouped by embedding, and each embedding has
exactly `C(Δ−1,4)` completions. -/
theorem sum_rootedCountG_eq_card_mul (C : ColouredGraphClass) :
    Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.graph.size) => S.card = 8))
        (fun S => PentagonQIsoInvariance.rootedCountG brrbGenFlag
          (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)) brrbRoot)
      = (Finset.univ : Finset (GenInducedEmbedding CG2
            (GenFlagType.empty CG2) brrbGenFlag C.toGenFlag)).card
          * Nat.choose (maxDegree C.graph - 1) 4 := by
  have h1 : Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.graph.size) => S.card = 8))
        (fun S => PentagonQIsoInvariance.rootedCountG brrbGenFlag
          (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)) brrbRoot)
      = Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.graph.size) => S.card = 8))
        (fun S => (Finset.univ.filter (fun e : GenInducedEmbedding CG2
              (GenFlagType.empty CG2) brrbGenFlag C.toGenFlag =>
            (∀ x, e.toFun x ∈ S) ∧
            (∀ w : Fin C.graph.size, w ∈ S → (∀ i, e.toFun i ≠ w) →
              (C.toGenFlag.str.1).Adj (e.toFun brrbRoot) w))).card) :=
    Finset.sum_congr rfl (fun S _ =>
      rootedCountG_subflag_card (F := brrbGenFlag) (G := C.toGenFlag) S
        (fun i => i.elim0) (Nat.zero_le _) brrbRoot)
  rw [h1, double_count]
  have h2 : ∀ e ∈ (Finset.univ : Finset (GenInducedEmbedding CG2
        (GenFlagType.empty CG2) brrbGenFlag C.toGenFlag)),
      ((Finset.univ.filter (fun S : Finset (Fin C.graph.size) => S.card = 8)).filter
        (fun S => (∀ x, e.toFun x ∈ S) ∧
          (∀ w : Fin C.graph.size, w ∈ S → (∀ i, e.toFun i ≠ w) →
            (C.toGenFlag.str.1).Adj (e.toFun brrbRoot) w))).card
        = Nat.choose (maxDegree C.graph - 1) 4 := by
    intro e _
    rw [← card_valid_eightSets C (mem_brrbFilter_of_embedding C e)]
    congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [embCond_iff_tupleCond C e S]
    exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul]

open Classical in
/-- **`(a2a)`.**  `Σ_{|S|=8} n₁(G'[S]) = 2·P(G,v)·C(Δ−1,4)`.

The three factors: the double-counting swap turns the sum into
(number of BRRB embeddings) × (completions each), `brrb_of_pentagon` and
`exists_pentagon_of_brrb` make the embedding count `2·P(G,v)` rather than merely
at least it, and the root having one neighbour inside its own tuple makes the
completion count `C(Δ−1,4)` rather than `C(Δ,4)`. -/
theorem sum_n1_eq_two_mul_pentagon (G : Flag emptyType) (v : Fin G.size)
    (htf : IsTriangleFree G) (hreg : IsRegular G) :
    Finset.sum (Finset.univ.filter
        (fun S : Finset (Fin (vColouredClass G v htf hreg).graph.size) => S.card = 8))
        (fun S => PentagonQIsoInvariance.rootedCountG brrbGenFlag
          ((vColouredClass G v htf hreg).toGenFlag.genInducedSubflag S
            (fun i => i.elim0) (Nat.zero_le _)) brrbRoot)
      = 2 * pentagonCountAt G v * Nat.choose (maxDegree G - 1) 4 := by
  rw [sum_rootedCountG_eq_card_mul, Finset.card_univ]
  -- `genInducedCount` is that `Fintype.card`, but not syntactically
  show genInducedCount CG2 (GenFlagType.empty CG2) brrbGenFlag
      (vColouredClass G v htf hreg).toGenFlag * _ = _
  rw [← brrbCount_eq_genInducedCount, brrbCount_eq_two_mul htf hreg v]
  rfl

/-! ## `(a2b)`: the pentagon flags

`(a2b)` needs `c(F₅₆;G') + 2·c(F₅₅;G') = Σ_{u ∈ N(v)} P(G,u)`, where `F₅₆` is the
pentagon with **exactly one** black vertex and `F₅₅` the one with two.
`sdpFlag55` exists (`PentagonConjecture.lean:2948`); `F₅₆` does not exist in Lean
at all, so it is defined here, in the same `fromRel` style and in the C₅
labelling `mkC5` uses, so that it matches `tauFlag tau2 5` on the nose. -/

/-- **F₅₆**: the 5-cycle `0-1-2-3-4-0` with exactly one black vertex.  Black at
`3`, matching `tau2`'s `cols = #[0,0,0,1,0]`. -/
noncomputable def sdpFlag56 : GenFlag CG2 (GenFlagType.empty CG2) where
  size := 5
  str := (SimpleGraph.fromRel (fun u v : Fin 5 => (u.val + 1) % 5 = v.val),
    fun v : Fin 5 => if v.val = 3 then (1 : Fin 2) else 0)
  embedding := ⟨Fin.elim0, fun {a} => Fin.elim0 a⟩
  isInduced := by apply CG2.comap_elim0
  hsize := Nat.zero_le _

/-- `τ₂`'s underlying flag *is* `F₅₆`.  Same extensionality route as
`tauFlag_tau1_eq_brrbGenFlag`: never ask for `tau2.padj` as an array, only for
its entries, which `simp` computes. -/
theorem tauFlag_tau2_eq_sdpFlag56 :
    PentagonQMuFlag.tauFlag PentagonQWeights.tau2 5 = sdpFlag56 :=
  GenFlag.empty_ext _ _ rfl <| by
    apply Prod.ext
    · ext u v
      simp only [PentagonQMuFlag.tauFlag, CGraph.toGenFlag, sdpFlag56,
        SimpleGraph.fromRel_adj, PentagonQRooted.patC, PentagonQWeights.tau2,
        PentagonQWeights.mkC5]
      fin_cases u <;> fin_cases v <;> simp
    · funext v
      simp only [PentagonQMuFlag.tauFlag, CGraph.toGenFlag, sdpFlag56,
        PentagonQRooted.patC, PentagonQWeights.tau2, PentagonQWeights.mkC5]
      fin_cases v <;> rfl

/-- The C₅-labelled representative of **F₅₅**: the 5-cycle with two non-adjacent
black vertices, at `2` and `4`, matching `tau3`'s `cols = #[0,0,1,0,1]`.

`sdpFlag55` (`PentagonConjecture.lean:2948`) is the same flag in a different
labelling — its cycle is `0-1-3-4-2-0` with black at `2, 3` — so relating the two
is an isomorphism, not an equality.  Counting is iso-invariant, so that suffices;
the iso is left for the step that needs it. -/
noncomputable def pentagonTwoBlack : GenFlag CG2 (GenFlagType.empty CG2) where
  size := 5
  str := (SimpleGraph.fromRel (fun u v : Fin 5 => (u.val + 1) % 5 = v.val),
    fun v : Fin 5 => if v.val = 2 ∨ v.val = 4 then (1 : Fin 2) else 0)
  embedding := ⟨Fin.elim0, fun {a} => Fin.elim0 a⟩
  isInduced := by apply CG2.comap_elim0
  hsize := Nat.zero_le _

/-- `τ₃`'s underlying flag is the two-black pentagon. -/
theorem tauFlag_tau3_eq_pentagonTwoBlack :
    PentagonQMuFlag.tauFlag PentagonQWeights.tau3 5 = pentagonTwoBlack :=
  GenFlag.empty_ext _ _ rfl <| by
    apply Prod.ext
    · ext u v
      simp only [PentagonQMuFlag.tauFlag, CGraph.toGenFlag, pentagonTwoBlack,
        SimpleGraph.fromRel_adj, PentagonQRooted.patC, PentagonQWeights.tau3,
        PentagonQWeights.mkC5]
      fin_cases u <;> fin_cases v <;> simp
    · funext v
      simp only [PentagonQMuFlag.tauFlag, CGraph.toGenFlag, pentagonTwoBlack,
        PentagonQRooted.patC, PentagonQWeights.tau3, PentagonQWeights.mkC5]
      fin_cases v <;> rfl

/-- The five vertices of an embedded pentagon, as a set. -/
def pentSet5 {n : ℕ} (p₀ p₁ p₂ p₃ p₄ : Fin n) : Finset (Fin n) := {p₀, p₁, p₂, p₃, p₄}

open Classical in
/-- **The τ₂/τ₃ analogue of `root_nbhd_inter_tuple`.**  A cycle vertex's
neighbourhood meets its own pentagon in exactly its two cycle-neighbours.

Only **triangle-freeness** is needed here, unlike the `τ₁` case which also spent
black independence: in a C₅ *every* chord closes a triangle, so `p₀p₂` and `p₀p₃`
are both excluded outright. -/
theorem pent_root_nbhd_inter (C : ColouredGraphClass)
    {p₀ p₁ p₂ p₃ p₄ : Fin C.graph.size}
    (a01 : C.graph.graph.Adj p₀ p₁) (a12 : C.graph.graph.Adj p₁ p₂)
    (a23 : C.graph.graph.Adj p₂ p₃) (a34 : C.graph.graph.Adj p₃ p₄)
    (a40 : C.graph.graph.Adj p₄ p₀) :
    (Finset.univ.filter (fun u => C.graph.graph.Adj p₀ u)) ∩ pentSet5 p₀ p₁ p₂ p₃ p₄
      = {p₁, p₄} := by
  have hn2 : ¬ C.graph.graph.Adj p₀ p₂ := fun h => C.triangleFree p₀ p₁ p₂ a01 a12 h
  have hn3 : ¬ C.graph.graph.Adj p₀ p₃ :=
    fun h => C.triangleFree p₀ p₄ p₃ a40.symm a34.symm h
  ext u
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, pentSet5,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hadj, rfl | rfl | rfl | rfl | rfl⟩
    · exact absurd hadj (by simp)
    · exact Or.inl rfl
    · exact absurd hadj hn2
    · exact absurd hadj hn3
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨a01, Or.inr (Or.inl rfl)⟩
    · exact ⟨a40.symm, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩

open Classical in
/-- Hence a cycle vertex has `Δ−2` neighbours outside its pentagon — the pool the
three extra vertices of an 8-set are drawn from, giving `(a2b)`'s `C(Δ−2,3)`.
Two are spent, against `τ₁`'s one, which is the whole difference between the two
binomials. -/
theorem card_pent_root_nbhd_sdiff (C : ColouredGraphClass)
    {p₀ p₁ p₂ p₃ p₄ : Fin C.graph.size}
    (a01 : C.graph.graph.Adj p₀ p₁) (a12 : C.graph.graph.Adj p₁ p₂)
    (a23 : C.graph.graph.Adj p₂ p₃) (a34 : C.graph.graph.Adj p₃ p₄)
    (a40 : C.graph.graph.Adj p₄ p₀) (hne : p₁ ≠ p₄) :
    ((Finset.univ.filter (fun u => C.graph.graph.Adj p₀ u)) \ pentSet5 p₀ p₁ p₂ p₃ p₄).card
      = maxDegree C.graph - 2 := by
  have hnb : (Finset.univ.filter (fun u => C.graph.graph.Adj p₀ u)).card
      = maxDegree C.graph := C.regular p₀
  have hsub := pent_root_nbhd_inter C a01 a12 a23 a34 a40
  have hcard := Finset.card_sdiff_add_card_inter
    (Finset.univ.filter (fun u => C.graph.graph.Adj p₀ u)) (pentSet5 p₀ p₁ p₂ p₃ p₄)
  rw [hsub, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton,
    hnb] at hcard
  omega

theorem card_pentSet5 {n : ℕ} {p₀ p₁ p₂ p₃ p₄ : Fin n}
    (d01 : p₀ ≠ p₁) (d02 : p₀ ≠ p₂) (d03 : p₀ ≠ p₃) (d04 : p₀ ≠ p₄)
    (d12 : p₁ ≠ p₂) (d13 : p₁ ≠ p₃) (d14 : p₁ ≠ p₄)
    (d23 : p₂ ≠ p₃) (d24 : p₂ ≠ p₄) (d34 : p₃ ≠ p₄) :
    (pentSet5 p₀ p₁ p₂ p₃ p₄).card = 5 := by
  rw [pentSet5, Finset.card_insert_of_notMem (by simp [d01, d02, d03, d04]),
    Finset.card_insert_of_notMem (by simp [d12, d13, d14]),
    Finset.card_insert_of_notMem (by simp [d23, d24]),
    Finset.card_insert_of_notMem (by simp [d34]), Finset.card_singleton]

open Classical in
/-- `(a2b)`'s fibre: the ways to complete a pentagon to an 8-set with every added
vertex in the root's neighbourhood.  **Three** added vertices (`8−5`), drawn from
a pool of `Δ−2` — against `(a2a)`'s four from `Δ−1`. -/
noncomputable def pentFibreOf (C : ColouredGraphClass)
    (p₀ p₁ p₂ p₃ p₄ : Fin C.graph.size) : Finset (Finset (Fin C.graph.size)) :=
  ((Finset.univ.filter (fun u => C.graph.graph.Adj p₀ u)) \ pentSet5 p₀ p₁ p₂ p₃ p₄).powersetCard 3

open Classical in
theorem card_pentFibreOf (C : ColouredGraphClass) {p₀ p₁ p₂ p₃ p₄ : Fin C.graph.size}
    (a01 : C.graph.graph.Adj p₀ p₁) (a12 : C.graph.graph.Adj p₁ p₂)
    (a23 : C.graph.graph.Adj p₂ p₃) (a34 : C.graph.graph.Adj p₃ p₄)
    (a40 : C.graph.graph.Adj p₄ p₀) (hne : p₁ ≠ p₄) :
    (pentFibreOf C p₀ p₁ p₂ p₃ p₄).card = Nat.choose (maxDegree C.graph - 2) 3 := by
  unfold pentFibreOf
  rw [Finset.card_powersetCard]
  congr 1
  exact card_pent_root_nbhd_sdiff C a01 a12 a23 a34 a40 hne

open Classical in
theorem card_union_pentFibre (C : ColouredGraphClass) {p₀ p₁ p₂ p₃ p₄ : Fin C.graph.size}
    (h5 : (pentSet5 p₀ p₁ p₂ p₃ p₄).card = 5)
    {T : Finset (Fin C.graph.size)} (hT : T ∈ pentFibreOf C p₀ p₁ p₂ p₃ p₄) :
    (pentSet5 p₀ p₁ p₂ p₃ p₄ ∪ T).card = 8 := by
  unfold pentFibreOf at hT
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨hsub, hcard⟩ := hT
  have hdisj : Disjoint (pentSet5 p₀ p₁ p₂ p₃ p₄) T :=
    Finset.disjoint_right.mpr (fun x hx hxp => (Finset.mem_sdiff.mp (hsub hx)).2 hxp)
  rw [Finset.card_union_of_disjoint hdisj, h5, hcard]

open Classical in
theorem union_pentFibre_injective (C : ColouredGraphClass)
    {p₀ p₁ p₂ p₃ p₄ : Fin C.graph.size} :
    Set.InjOn (fun T => pentSet5 p₀ p₁ p₂ p₃ p₄ ∪ T) ↑(pentFibreOf C p₀ p₁ p₂ p₃ p₄) := by
  intro T₁ h₁ T₂ h₂ h
  simp only [pentFibreOf, Finset.mem_coe, Finset.mem_powersetCard] at h₁ h₂
  have hd₁ : Disjoint (pentSet5 p₀ p₁ p₂ p₃ p₄) T₁ := Finset.disjoint_right.mpr
    (fun x hx hxp => (Finset.mem_sdiff.mp (h₁.1 hx)).2 hxp)
  have hd₂ : Disjoint (pentSet5 p₀ p₁ p₂ p₃ p₄) T₂ := Finset.disjoint_right.mpr
    (fun x hx hxp => (Finset.mem_sdiff.mp (h₂.1 hx)).2 hxp)
  have e₁ := Finset.union_sdiff_cancel_left hd₁
  have e₂ := Finset.union_sdiff_cancel_left hd₂
  have h' : pentSet5 p₀ p₁ p₂ p₃ p₄ ∪ T₁ = pentSet5 p₀ p₁ p₂ p₃ p₄ ∪ T₂ := h
  rw [← e₁, ← e₂, h']

open Classical in
theorem union_pentFibre_surjective (C : ColouredGraphClass)
    {p₀ p₁ p₂ p₃ p₄ : Fin C.graph.size} (h5 : (pentSet5 p₀ p₁ p₂ p₃ p₄).card = 5)
    {S : Finset (Fin C.graph.size)} (hS8 : S.card = 8)
    (hsub : pentSet5 p₀ p₁ p₂ p₃ p₄ ⊆ S)
    (hnb : ∀ u ∈ S, u ∉ pentSet5 p₀ p₁ p₂ p₃ p₄ → C.graph.graph.Adj p₀ u) :
    ∃ T ∈ pentFibreOf C p₀ p₁ p₂ p₃ p₄, pentSet5 p₀ p₁ p₂ p₃ p₄ ∪ T = S := by
  refine ⟨S \ pentSet5 p₀ p₁ p₂ p₃ p₄, ?_, Finset.union_sdiff_of_subset hsub⟩
  rw [pentFibreOf, Finset.mem_powersetCard]
  constructor
  · intro x hx
    rw [Finset.mem_sdiff] at hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hnb x hx.1 hx.2⟩, hx.2⟩
  · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hS8, h5]

/-- The C₅ `0-1-2-3-4-0` with an arbitrary colouring.  `sdpFlag56` and
`pentagonTwoBlack` are this flag at two colourings, so everything below is proved
once rather than twice. -/
noncomputable def pentFlag (c : Fin 5 → Fin 2) : GenFlag CG2 (GenFlagType.empty CG2) where
  size := 5
  str := (SimpleGraph.fromRel (fun u v : Fin 5 => (u.val + 1) % 5 = v.val), c)
  embedding := ⟨Fin.elim0, fun {a} => Fin.elim0 a⟩
  isInduced := by apply CG2.comap_elim0
  hsize := Nat.zero_le _

theorem sdpFlag56_eq_pentFlag :
    sdpFlag56 = pentFlag (fun v : Fin 5 => if v.val = 3 then (1 : Fin 2) else 0) := rfl

theorem pentagonTwoBlack_eq_pentFlag :
    pentagonTwoBlack = pentFlag (fun v : Fin 5 => if v.val = 2 ∨ v.val = 4 then (1 : Fin 2) else 0) :=
  rfl

theorem pentFlag_size (c : Fin 5 → Fin 2) : (pentFlag c).size = 5 := rfl

/-- `Fin (pentFlag c).size` *is* `Fin 5`; this names the identity, so indices can
be written as plain numerals instead of `⟨k, proof⟩` — the proof would otherwise
mention `c` and block `decide`. -/
def pidx {c : Fin 5 → Fin 2} (k : Fin 5) : Fin (pentFlag c).size := k

theorem pidx_ne {c : Fin 5 → Fin 2} {i j : Fin 5} (h : i ≠ j) :
    (pidx (c := c) i) ≠ pidx j := h

/-- Consecutive indices are adjacent in the C₅.  Stated so that the side
condition closes by `rfl`: `decide` is unavailable, because the index type
`Fin (pentFlag c).size` mentions the free `c` even though it reduces to `Fin 5`. -/
theorem c5_adj {i j : Fin 5} (h : (i.val + 1) % 5 = j.val) :
    (SimpleGraph.fromRel (fun u v : Fin 5 => (u.val + 1) % 5 = v.val)).Adj i j := by
  refine ⟨fun hij => ?_, Or.inl h⟩
  rw [hij] at h
  omega

/-- **Reading a pentagon off an embedding**, for either colouring at once.  As
with `brrb_of_embedding`, `isInduced` carries everything: colours from the second
component, adjacency *as an iff* from the first. -/
theorem pent_of_embedding (C : ColouredGraphClass) (c : Fin 5 → Fin 2)
    (e : GenInducedEmbedding CG2 (GenFlagType.empty CG2) (pentFlag c) C.toGenFlag) :
    (∀ i : Fin (pentFlag c).size, C.colouring (e.toFun i) = c i) ∧
    (∀ i j : Fin (pentFlag c).size,
      C.graph.graph.Adj (e.toFun i) (e.toFun j) ↔
        (SimpleGraph.fromRel (fun u v : Fin 5 => (u.val + 1) % 5 = v.val)).Adj i j) := by
  have h := e.isInduced
  simp only [colouredGraphUniverse, pentFlag, ColouredGraphClass.toGenFlag,
    ColouredGraph.toGenFlag, ColouredGraphClass.toColouredGraph] at h
  constructor
  · intro i
    have hc := congrArg Prod.snd h
    simp only at hc
    exact congrFun hc i
  · intro i j
    have hg := congrArg Prod.fst h
    simp only at hg
    rw [← hg]
    rfl

/-- The five vertices of an embedding of a pentagon flag. -/
noncomputable def pentTupleOf (C : ColouredGraphClass) (c : Fin 5 → Fin 2)
    (e : GenInducedEmbedding CG2 (GenFlagType.empty CG2) (pentFlag c) C.toGenFlag) :
    Finset (Fin C.graph.size) :=
  pentSet5 (e.toFun (pidx 0))
    (e.toFun (pidx 1))
    (e.toFun (pidx 2))
    (e.toFun (pidx 3))
    (e.toFun (pidx 4))

/-- That vertex set is the embedding's image. -/
theorem mem_pentTupleOf_iff (C : ColouredGraphClass) (c : Fin 5 → Fin 2)
    (e : GenInducedEmbedding CG2 (GenFlagType.empty CG2) (pentFlag c) C.toGenFlag)
    (u : Fin C.graph.size) :
    u ∈ pentTupleOf C c e ↔ ∃ i, e.toFun i = u := by
  simp only [pentTupleOf, pentSet5, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h | h | h) <;> exact ⟨_, h.symm⟩
  · rintro ⟨i, rfl⟩
    have : i.val < 5 := by rw [← pentFlag_size c]; exact i.isLt
    interval_cases hi : i.val
    · exact Or.inl (congrArg e.toFun (Fin.ext hi))
    · exact Or.inr (Or.inl (congrArg e.toFun (Fin.ext hi)))
    · exact Or.inr (Or.inr (Or.inl (congrArg e.toFun (Fin.ext hi))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg e.toFun (Fin.ext hi)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (congrArg e.toFun (Fin.ext hi)))))

open Classical in
/-- The five cycle edges and the distinctness, read off an embedding. -/
theorem pent_cycle_of_embedding (C : ColouredGraphClass) (c : Fin 5 → Fin 2)
    (e : GenInducedEmbedding CG2 (GenFlagType.empty CG2) (pentFlag c) C.toGenFlag) :
    C.graph.graph.Adj (e.toFun (pidx 0))
        (e.toFun (pidx 1)) ∧
    C.graph.graph.Adj (e.toFun (pidx 1))
        (e.toFun (pidx 2)) ∧
    C.graph.graph.Adj (e.toFun (pidx 2))
        (e.toFun (pidx 3)) ∧
    C.graph.graph.Adj (e.toFun (pidx 3))
        (e.toFun (pidx 4)) ∧
    C.graph.graph.Adj (e.toFun (pidx 4))
        (e.toFun (pidx 0)) := by
  obtain ⟨-, hadj⟩ := pent_of_embedding C c e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    exact (hadj _ _).mpr (c5_adj (by first | rfl | simp [pidx] | norm_num [pidx]))

open Classical in
/-- **`(a2b)`'s inner count.**  For a fixed embedded pentagon, the 8-sets
containing it whose extra vertices lie in the root's neighbourhood number exactly
`C(Δ−2,3)`. -/
theorem card_valid_eightSets_pent (C : ColouredGraphClass) (c : Fin 5 → Fin 2)
    (e : GenInducedEmbedding CG2 (GenFlagType.empty CG2) (pentFlag c) C.toGenFlag) :
    (Finset.univ.filter (fun S : Finset (Fin C.graph.size) =>
        S.card = 8 ∧ pentTupleOf C c e ⊆ S ∧
          ∀ u ∈ S, u ∉ pentTupleOf C c e →
            C.graph.graph.Adj (e.toFun (pidx 0)) u)).card
      = Nat.choose (maxDegree C.graph - 2) 3 := by
  unfold pentTupleOf
  obtain ⟨a01, a12, a23, a34, a40⟩ := pent_cycle_of_embedding C c e
  have hinj : ∀ a b : Fin 5, a ≠ b → e.toFun (pidx a) ≠ e.toFun (pidx b) :=
    fun a b hab h => hab (e.injective h)
  have h5 : (pentTupleOf C c e).card = 5 :=
    card_pentSet5 (hinj _ _ (by decide)) (hinj _ _ (by decide)) (hinj _ _ (by decide))
      (hinj _ _ (by decide)) (hinj _ _ (by decide)) (hinj _ _ (by decide))
      (hinj _ _ (by decide)) (hinj _ _ (by decide)) (hinj _ _ (by decide))
      (hinj _ _ (by decide))
  have hne14 : e.toFun (pidx 1)
      ≠ e.toFun (pidx 4) := hinj _ _ (by decide)
  have himg : (Finset.univ.filter (fun S : Finset (Fin C.graph.size) =>
        S.card = 8 ∧ pentSet5 (e.toFun (pidx 0)) (e.toFun (pidx 1)) (e.toFun (pidx 2)) (e.toFun (pidx 3)) (e.toFun (pidx 4)) ⊆ S ∧
          ∀ u ∈ S, u ∉ pentSet5 (e.toFun (pidx 0)) (e.toFun (pidx 1)) (e.toFun (pidx 2)) (e.toFun (pidx 3)) (e.toFun (pidx 4)) →
            C.graph.graph.Adj (e.toFun (pidx 0)) u))
      = (pentFibreOf C (e.toFun (pidx 0)) (e.toFun (pidx 1)) (e.toFun (pidx 2))
          (e.toFun (pidx 3)) (e.toFun (pidx 4))).image
          (fun T => pentSet5 (e.toFun (pidx 0)) (e.toFun (pidx 1)) (e.toFun (pidx 2))
            (e.toFun (pidx 3)) (e.toFun (pidx 4)) ∪ T) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hcard, hsub, hnb⟩
      exact union_pentFibre_surjective C h5 hcard hsub hnb
    · rintro ⟨T, hT, rfl⟩
      refine ⟨card_union_pentFibre C h5 hT, Finset.subset_union_left, ?_⟩
      intro u hu hnu
      rcases Finset.mem_union.mp hu with h | h
      · exact absurd h hnu
      · rw [pentFibreOf, Finset.mem_powersetCard] at hT
        exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (hT.1 h)).1).2
  -- finish by `exact`, not `rw`: the two `Finset.image` terms differ only in
  -- their `DecidableEq` instance, which defeq absorbs but `rw` will not match
  rw [himg, ← card_pentFibreOf C a01 a12 a23 a34 a40 hne14]
  exact Finset.card_image_of_injOn (union_pentFibre_injective C)

open Classical in
/-- The two conditions read on a pentagon embedding are the two read on its
vertex set. -/
theorem pentEmbCond_iff (C : ColouredGraphClass) (c : Fin 5 → Fin 2)
    (e : GenInducedEmbedding CG2 (GenFlagType.empty CG2) (pentFlag c) C.toGenFlag)
    (S : Finset (Fin C.graph.size)) :
    ((∀ x, e.toFun x ∈ S) ∧
       (∀ w : Fin C.graph.size, w ∈ S → (∀ i, e.toFun i ≠ w) →
         (C.toGenFlag.str.1).Adj (e.toFun (pidx 0)) w))
      ↔ (pentTupleOf C c e ⊆ S ∧
          ∀ u ∈ S, u ∉ pentTupleOf C c e →
            C.graph.graph.Adj (e.toFun (pidx 0)) u) := by
  have hmem := mem_pentTupleOf_iff C c e
  constructor
  · rintro ⟨himg, hrc⟩
    refine ⟨fun u hu => ?_, fun u hu hnu => ?_⟩
    · obtain ⟨i, rfl⟩ := (hmem u).mp hu; exact himg i
    · exact hrc u hu (fun i hi => hnu ((hmem u).mpr ⟨i, hi⟩))
  · rintro ⟨hsub, hrc⟩
    refine ⟨fun x => hsub ((hmem _).mpr ⟨x, rfl⟩), fun w hw hne => ?_⟩
    exact hrc w hw (fun hcon => by obtain ⟨i, hi⟩ := (hmem w).mp hcon; exact hne i hi)

open Classical in
/-- **`(a2b)`'s fibre count, at the flag level.**  Summing the rooted pentagon
count over 8-subsets gives the number of embeddings times `C(Δ−2,3)`. -/
theorem sum_pentRootedCountG_eq_card_mul (C : ColouredGraphClass) (c : Fin 5 → Fin 2) :
    Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.graph.size) => S.card = 8))
        (fun S => PentagonQIsoInvariance.rootedCountG (pentFlag c)
          (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)) (pidx 0))
      = (Finset.univ : Finset (GenInducedEmbedding CG2
            (GenFlagType.empty CG2) (pentFlag c) C.toGenFlag)).card
          * Nat.choose (maxDegree C.graph - 2) 3 := by
  have h1 : Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.graph.size) => S.card = 8))
        (fun S => PentagonQIsoInvariance.rootedCountG (pentFlag c)
          (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)) (pidx 0))
      = Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.graph.size) => S.card = 8))
        (fun S => (Finset.univ.filter (fun e : GenInducedEmbedding CG2
              (GenFlagType.empty CG2) (pentFlag c) C.toGenFlag =>
            (∀ x, e.toFun x ∈ S) ∧
            (∀ w : Fin C.graph.size, w ∈ S → (∀ i, e.toFun i ≠ w) →
              (C.toGenFlag.str.1).Adj (e.toFun (pidx 0)) w))).card) :=
    Finset.sum_congr rfl (fun S _ =>
      rootedCountG_subflag_card (F := pentFlag c) (G := C.toGenFlag) S
        (fun i => i.elim0) (Nat.zero_le _) (pidx 0))
  rw [h1, double_count]
  have h2 : ∀ e ∈ (Finset.univ : Finset (GenInducedEmbedding CG2
        (GenFlagType.empty CG2) (pentFlag c) C.toGenFlag)),
      ((Finset.univ.filter (fun S : Finset (Fin C.graph.size) => S.card = 8)).filter
        (fun S => (∀ x, e.toFun x ∈ S) ∧
          (∀ w : Fin C.graph.size, w ∈ S → (∀ i, e.toFun i ≠ w) →
            (C.toGenFlag.str.1).Adj (e.toFun (pidx 0)) w))).card
        = Nat.choose (maxDegree C.graph - 2) 3 := by
    intro e _
    rw [← card_valid_eightSets_pent C c e]
    congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [pentEmbCond_iff C c e S]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul]

/-! ## The automorphism factor

`genInducedCount = genFlagAutCount · copies`, so turning the embedding count into
a copy count needs `genFlagAutCount (pentFlag c) = 2`.

`genFlagAutCount` is **not** computable by `decide`: `colouredGraphUniverse`'s
`instDecEq` is `Classical.decEq` (`Basic.lean:103`), so the `Fintype` instance on
`GenInducedEmbedding` is noncomputable.  The automorphism group has to be
exhibited.

The non-trivial automorphism is the same map for both colourings — the reflection
fixing vertex `3`, which also swaps `2 ↔ 4` and so preserves both "black at `3`"
and "black at `2, 4`". -/

/-- The reflection of the C₅ fixing `3`: `k ↦ (6−k) mod 5`. -/
def pentRefl (k : Fin 5) : Fin 5 := ⟨(6 - k.val) % 5, by omega⟩

theorem pentRefl_involutive (k : Fin 5) : pentRefl (pentRefl k) = k := by
  fin_cases k <;> rfl

theorem pentRefl_injective : Function.Injective pentRefl :=
  Function.LeftInverse.injective pentRefl_involutive

theorem pentRefl_ne_id : pentRefl ≠ id := by
  intro h
  have := congrFun h (0 : Fin 5)
  simp [pentRefl] at this

theorem pentRefl_adj (i j : Fin 5) :
    (SimpleGraph.fromRel (fun u v : Fin 5 => (u.val + 1) % 5 = v.val)).Adj
        (pentRefl i) (pentRefl j)
      ↔ (SimpleGraph.fromRel (fun u v : Fin 5 => (u.val + 1) % 5 = v.val)).Adj i j := by
  fin_cases i <;> fin_cases j <;>
    simp [SimpleGraph.fromRel_adj, pentRefl]

/-- The reflection is an automorphism of `pentFlag c`, for any colouring it
preserves. -/
noncomputable def pentAut (c : Fin 5 → Fin 2) (hc : ∀ k, c (pentRefl k) = c k) :
    GenInducedEmbedding CG2 (GenFlagType.empty CG2) (pentFlag c) (pentFlag c) where
  toFun := pentRefl
  injective := pentRefl_injective
  isInduced := by
    apply Prod.ext
    · ext i j
      exact pentRefl_adj i j
    · funext k; exact hc k
  compat := fun i => i.elim0

theorem sdpFlag56_refl_colour :
    ∀ k, (fun v : Fin 5 => if v.val = 3 then (1 : Fin 2) else 0) (pentRefl k)
      = (fun v : Fin 5 => if v.val = 3 then (1 : Fin 2) else 0) k := by
  intro k; fin_cases k <;> rfl

theorem pentagonTwoBlack_refl_colour :
    ∀ k, (fun v : Fin 5 => if v.val = 2 ∨ v.val = 4 then (1 : Fin 2) else 0) (pentRefl k)
      = (fun v : Fin 5 => if v.val = 2 ∨ v.val = 4 then (1 : Fin 2) else 0) k := by
  intro k; fin_cases k <;> rfl

/-! ### Every C₅ automorphism fixing a vertex is the identity or the reflection

`decide` over all `5^5` maps overflows the stack ("deep recursion at expression
equality test"), so the argument is the mathematical one, with `decide` used only
on the five-case neighbour facts.  Adjacency is carried as a `Bool` (`c5adjB`)
rather than `SimpleGraph.Adj`, which has no `Decidable` instance here. -/

def c5adjB (i j : Fin 5) : Bool :=
  (i != j) && (((i.val + 1) % 5 == j.val) || ((j.val + 1) % 5 == i.val))
theorem c5adjB_symm : ∀ i j : Fin 5, c5adjB i j = c5adjB j i := by decide

theorem nbr3 : ∀ x : Fin 5, c5adjB 3 x = true → x = 2 ∨ x = 4 := by decide
theorem nbr2 : ∀ x : Fin 5, c5adjB 2 x = true → x = 1 ∨ x = 3 := by decide
theorem nbr4 : ∀ x : Fin 5, c5adjB 4 x = true → x = 3 ∨ x = 0 := by decide
theorem nbr1 : ∀ x : Fin 5, c5adjB 1 x = true → x = 0 ∨ x = 2 := by decide
theorem nbr0 : ∀ x : Fin 5, c5adjB 0 x = true → x = 1 ∨ x = 4 := by decide

theorem c5_rigid (φ : Fin 5 → Fin 5) (hinj : Function.Injective φ)
    (hadj : ∀ i j, c5adjB (φ i) (φ j) = c5adjB i j) (h3 : φ 3 = 3) :
    φ = id ∨ φ = pentRefl := by
  have a32 : c5adjB (φ 3) (φ 2) = true := by rw [hadj]; decide
  rw [h3] at a32
  rcases nbr3 _ a32 with h2 | h2
  · -- φ 2 = 2, the identity branch
    left
    have a21 : c5adjB (φ 2) (φ 1) = true := by rw [hadj]; decide
    rw [h2] at a21
    have h1 : φ 1 = 1 := by
      rcases nbr2 _ a21 with h | h
      · exact h
      · exact absurd (h.trans h3.symm) (fun k => by simpa using hinj k)
    have a43 : c5adjB (φ 4) (φ 3) = true := by rw [hadj]; decide
    rw [h3] at a43
    have h4 : φ 4 = 4 := by
      have := nbr3 (φ 4) (by rw [c5adjB_symm] at a43; exact a43)
      rcases this with h | h
      · exact absurd (h.trans h2.symm) (fun k => by simpa using hinj k)
      · exact h
    have a01 : c5adjB (φ 0) (φ 1) = true := by rw [hadj]; decide
    rw [h1] at a01
    have h0 : φ 0 = 0 := by
      have := nbr1 (φ 0) (by rw [c5adjB_symm] at a01; exact a01)
      rcases this with h | h
      · exact h
      · exact absurd (h.trans h2.symm) (fun k => by simpa using hinj k)
    funext k; fin_cases k <;> simp [h0, h1, h2, h3, h4]
  · -- φ 2 = 4, the reflection branch
    right
    have a21 : c5adjB (φ 2) (φ 1) = true := by rw [hadj]; decide
    rw [h2] at a21
    have h1 : φ 1 = 0 := by
      rcases nbr4 _ a21 with h | h
      · exact absurd (h.trans h3.symm) (fun k => by simpa using hinj k)
      · exact h
    have a43 : c5adjB (φ 4) (φ 3) = true := by rw [hadj]; decide
    rw [h3] at a43
    have h4 : φ 4 = 2 := by
      have := nbr3 (φ 4) (by rw [c5adjB_symm] at a43; exact a43)
      rcases this with h | h
      · exact h
      · exact absurd (h.trans h2.symm) (fun k => by simpa using hinj k)
    have a01 : c5adjB (φ 0) (φ 1) = true := by rw [hadj]; decide
    rw [h1] at a01
    have h0 : φ 0 = 1 := by
      have := nbr0 (φ 0) (by rw [c5adjB_symm] at a01; exact a01)
      rcases this with h | h
      · exact h
      · exact absurd (h.trans h2.symm) (fun k => by simpa using hinj k)
    funext k; fin_cases k <;> simp [h0, h1, h2, h3, h4, pentRefl] <;> rfl

theorem c5adjB_iff (i j : Fin 5) :
    c5adjB i j = true ↔
      (SimpleGraph.fromRel (fun u v : Fin 5 => (u.val + 1) % 5 = v.val)).Adj i j := by
  fin_cases i <;> fin_cases j <;> simp [c5adjB, SimpleGraph.fromRel_adj]

/-- The identity automorphism. -/
noncomputable def pentIdAut (c : Fin 5 → Fin 2) :
    GenInducedEmbedding CG2 (GenFlagType.empty CG2) (pentFlag c) (pentFlag c) where
  toFun := id
  injective := fun _ _ h => h
  isInduced := CG2.comap_id _
  compat := fun i => i.elim0

/-- An automorphism's data, unpacked: injective, colour-fixing, adjacency-fixing. -/
theorem pentAut_data (c : Fin 5 → Fin 2)
    (e : GenInducedEmbedding CG2 (GenFlagType.empty CG2) (pentFlag c) (pentFlag c)) :
    Function.Injective e.toFun ∧ (∀ k, c (e.toFun k) = c k) ∧
      (∀ i j, c5adjB (e.toFun i) (e.toFun j) = c5adjB i j) := by
  have h := e.isInduced
  simp only [colouredGraphUniverse, pentFlag] at h
  refine ⟨e.injective, fun k => congrFun (congrArg Prod.snd h) k, fun i j => ?_⟩
  have hg := congrArg Prod.fst h
  simp only at hg
  have : (SimpleGraph.fromRel (fun u v : Fin 5 => (u.val + 1) % 5 = v.val)).Adj
      (e.toFun i) (e.toFun j) ↔
      (SimpleGraph.fromRel (fun u v : Fin 5 => (u.val + 1) % 5 = v.val)).Adj i j := by
    conv_rhs => rw [← hg]
    rfl
  by_cases hij : c5adjB i j = true
  · rw [hij]
    exact (c5adjB_iff _ _).mpr (this.mpr ((c5adjB_iff i j).mp hij))
  · simp only [Bool.not_eq_true] at hij
    rw [hij]
    by_contra hcon
    simp only [Bool.not_eq_false] at hcon
    exact absurd ((c5adjB_iff i j).mpr (this.mp ((c5adjB_iff _ _).mp hcon))) (by simp [hij])

/-- For the one-black colouring, an automorphism fixes vertex `3`: it is the
unique black vertex. -/
theorem pentAut_fix3_56
    (e : GenInducedEmbedding CG2 (GenFlagType.empty CG2)
      (pentFlag (fun v : Fin 5 => if v.val = 3 then (1 : Fin 2) else 0))
      (pentFlag (fun v : Fin 5 => if v.val = 3 then (1 : Fin 2) else 0))) :
    e.toFun (pidx 3) = pidx 3 := by
  obtain ⟨-, hcol, -⟩ := pentAut_data _ e
  have h3 := hcol (pidx 3)
  simp only [show ((pidx 3 : Fin 5)).val = 3 from rfl, if_pos rfl] at h3
  by_contra hne
  have hv : (e.toFun (pidx 3)).val ≠ 3 := fun h => hne (Fin.ext h)
  rw [if_neg hv] at h3
  exact absurd h3 (by decide)

/-- **The automorphism count for `F₅₆`.**  Exactly two: the identity and the
reflection.  This is the factor 2 of `(a2b)`, earned rather than assumed. -/
theorem genFlagAutCount_sdpFlag56 :
    genFlagAutCount CG2 (GenFlagType.empty CG2)
      (pentFlag (fun v : Fin 5 => if v.val = 3 then (1 : Fin 2) else 0)) = 2 := by
  unfold genFlagAutCount genInducedCount
  rw [← Nat.card_eq_fintype_card, Nat.card_eq_two_iff]
  refine ⟨pentIdAut _, pentAut _ sdpFlag56_refl_colour, ?_, ?_⟩
  · intro h
    exact pentRefl_ne_id (congrArg GenInducedEmbedding.toFun h).symm
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨hinj, -, hadj⟩ := pentAut_data _ x
    rcases c5_rigid x.toFun hinj hadj (pentAut_fix3_56 x) with h | h
    · exact Or.inl (genEmb_ext h)
    · exact Or.inr (genEmb_ext h)

theorem black24 : ∀ x : Fin 5,
    (if x.val = 2 ∨ x.val = 4 then (1 : Fin 2) else 0) = 1 → x = 2 ∨ x = 4 := by decide

theorem common_nbr_24 : ∀ x : Fin 5,
    c5adjB x 2 = true → c5adjB x 4 = true → x = 3 := by decide

/-- For the two-black colouring, an automorphism still fixes vertex `3` — but for
a different reason than in the one-black case.  Here `3` is not the unique black
vertex; it is the unique **common neighbour of the two black vertices**, and an
automorphism permutes those. -/
theorem pentAut_fix3_55
    (e : GenInducedEmbedding CG2 (GenFlagType.empty CG2)
      (pentFlag (fun v : Fin 5 => if v.val = 2 ∨ v.val = 4 then (1 : Fin 2) else 0))
      (pentFlag (fun v : Fin 5 => if v.val = 2 ∨ v.val = 4 then (1 : Fin 2) else 0))) :
    e.toFun (pidx 3) = pidx 3 := by
  obtain ⟨hinj, hcol, hadj⟩ := pentAut_data _ e
  -- the black set is preserved
  have h2 : e.toFun (pidx 2) = pidx 2 ∨ e.toFun (pidx 2) = pidx 4 :=
    black24 _ (by rw [hcol (pidx 2)]; decide)
  have h4 : e.toFun (pidx 4) = pidx 2 ∨ e.toFun (pidx 4) = pidx 4 :=
    black24 _ (by rw [hcol (pidx 4)]; decide)
  have a32 : c5adjB (e.toFun (pidx 3)) (e.toFun (pidx 2)) = true := by rw [hadj]; decide
  have a34 : c5adjB (e.toFun (pidx 3)) (e.toFun (pidx 4)) = true := by rw [hadj]; decide
  rcases h2 with h2 | h2 <;> rcases h4 with h4 | h4
  -- the two mixed branches are the real ones; the other two collapse by injectivity
  · exact absurd (hinj (h2.trans h4.symm)) (pidx_ne (by decide))
  · rw [h2] at a32; rw [h4] at a34
    exact common_nbr_24 _ a32 a34
  · rw [h2] at a32; rw [h4] at a34
    exact common_nbr_24 _ a34 a32
  · exact absurd (hinj (h2.trans h4.symm)) (pidx_ne (by decide))

/-- **The automorphism count for `F₅₅`.**  Also two. -/
theorem genFlagAutCount_pentagonTwoBlack :
    genFlagAutCount CG2 (GenFlagType.empty CG2)
      (pentFlag (fun v : Fin 5 => if v.val = 2 ∨ v.val = 4 then (1 : Fin 2) else 0)) = 2 := by
  unfold genFlagAutCount genInducedCount
  rw [← Nat.card_eq_fintype_card, Nat.card_eq_two_iff]
  refine ⟨pentIdAut _, pentAut _ pentagonTwoBlack_refl_colour, ?_, ?_⟩
  · intro h
    exact pentRefl_ne_id (congrArg GenInducedEmbedding.toFun h).symm
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨hinj, -, hadj⟩ := pentAut_data _ x
    rcases c5_rigid x.toFun hinj hadj (pentAut_fix3_55 x) with h | h
    · exact Or.inl (genEmb_ext h)
    · exact Or.inr (genEmb_ext h)

open Classical in
/-- **`(a2b)`'s fibre count, in copies.**  The embedding count is
`genFlagAutCount · copies`, so with the automorphism count at 2 the sum is
`2 · c(F;G') · C(Δ−2,3)` — the plan's statement. -/
theorem sum_pentRooted_eq_two_mul_copies (C : ColouredGraphClass) (c : Fin 5 → Fin 2)
    (haut : genFlagAutCount CG2 (GenFlagType.empty CG2) (pentFlag c) = 2) :
    Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.graph.size) => S.card = 8))
        (fun S => PentagonQIsoInvariance.rootedCountG (pentFlag c)
          (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)) (pidx 0))
      = 2 * PentagonQOrbit.subsetCopies (pentFlag c) C.toGenFlag
          * Nat.choose (maxDegree C.graph - 2) 3 := by
  rw [sum_pentRootedCountG_eq_card_mul, Finset.card_univ]
  show genInducedCount CG2 (GenFlagType.empty CG2) (pentFlag c) C.toGenFlag * _ = _
  rw [PentagonQOrbit.genInducedCount_eq_autCount_mul_copies, haut,
    PentagonQOrbit.copies_eq_subsetCopies]

open Classical in
/-- `(a2b)` for `τ₂`, at `F₅₆`. -/
theorem sum_n2_eq_two_mul_copies (C : ColouredGraphClass) :
    Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.graph.size) => S.card = 8))
        (fun S => PentagonQIsoInvariance.rootedCountG sdpFlag56
          (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)) (pidx 0))
      = 2 * PentagonQOrbit.subsetCopies sdpFlag56 C.toGenFlag
          * Nat.choose (maxDegree C.graph - 2) 3 :=
  sum_pentRooted_eq_two_mul_copies C _ genFlagAutCount_sdpFlag56

open Classical in
/-- `(a2b)` for `τ₃`, at the two-black pentagon. -/
theorem sum_n3_eq_two_mul_copies (C : ColouredGraphClass) :
    Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.graph.size) => S.card = 8))
        (fun S => PentagonQIsoInvariance.rootedCountG pentagonTwoBlack
          (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)) (pidx 0))
      = 2 * PentagonQOrbit.subsetCopies pentagonTwoBlack C.toGenFlag
          * Nat.choose (maxDegree C.graph - 2) 3 :=
  sum_pentRooted_eq_two_mul_copies C _ genFlagAutCount_pentagonTwoBlack

/-! ## The pentagon-visit identity

`c(F₅₆;G') + 2·c(F₅₅;G') = Σ_{u ∈ N(v)} P(G,u)`.  Counted the other way round,
the right side is `Σ_{pentagons S} |S ∩ black|`, so the identity says a pentagon
carries **one or two** black vertices and is counted once per black vertex.

That it is never three is the structural input, and it is where black
independence is spent: a C₅ has independence number 2. -/

/-- In a C₅, any three distinct vertices contain an adjacent pair. -/
theorem c5_three_meet : ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k →
    c5adjB i j = true ∨ c5adjB i k = true ∨ c5adjB j k = true := by decide

/-- **A pentagon carries at most two black vertices.**  Black is `N(v)`, which is
independent, and a C₅ has independence number 2 — so three black vertices would
force a black edge. -/
theorem pent_black_le_two (C : ColouredGraphClass) (c : Fin 5 → Fin 2)
    (e : GenInducedEmbedding CG2 (GenFlagType.empty CG2) (pentFlag c) C.toGenFlag)
    (i j k : Fin 5) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : C.colouring (e.toFun (pidx i)) = 1)
    (hj : C.colouring (e.toFun (pidx j)) = 1)
    (hk : C.colouring (e.toFun (pidx k)) = 1) : False := by
  obtain ⟨-, hadj⟩ := pent_of_embedding C c e
  have hA : ∀ a b : Fin 5, c5adjB a b = true →
      C.graph.graph.Adj (e.toFun (pidx a)) (e.toFun (pidx b)) :=
    fun a b h => (hadj _ _).mpr ((c5adjB_iff a b).mp h)
  rcases c5_three_meet i j k hij hik hjk with h | h | h
  · exact C.blackIndependent _ _ hi hj (hA _ _ h)
  · exact C.blackIndependent _ _ hi hk (hA _ _ h)
  · exact C.blackIndependent _ _ hj hk (hA _ _ h)

open Classical in
/-- The black vertices, i.e. `N(v)` at the `v`-colouring. -/
noncomputable def blackSet (C : ColouredGraphClass) : Finset (Fin C.graph.size) :=
  Finset.univ.filter (fun u => C.colouring u = 1)

open Classical in
/-- All pentagons of the host. -/
noncomputable def pentAll (C : ColouredGraphClass) : Finset (Finset (Fin C.graph.size)) :=
  Finset.univ.filter (fun S => IsPentagon C.graph S)

open Classical in
/-- **The reindexing.**  `Σ_{u ∈ N(v)} P(G,u)` counts pairs (black vertex,
pentagon through it); grouping by pentagon instead gives
`Σ_{pentagons} |S ∩ N(v)|`.  Another instance of `double_count`. -/
theorem sum_black_pentagonCount (C : ColouredGraphClass) :
    Finset.sum (blackSet C) (fun u => pentagonCountAt C.graph u)
      = Finset.sum (pentAll C) (fun S => ((blackSet C).filter (fun u => u ∈ S)).card) := by
  have hL : ∀ u ∈ blackSet C, pentagonCountAt C.graph u
      = ((pentAll C).filter (fun S => u ∈ S)).card := by
    intro u _
    unfold pentagonCountAt pentAll
    congr 1
    rw [Finset.filter_filter]
  rw [Finset.sum_congr rfl hL]
  exact double_count (blackSet C) (pentAll C) (fun u S => u ∈ S)

open Classical in
/-- **The split.**  With at most two black vertices per pentagon, the sum
`Σ_S |S ∩ N(v)|` is `#{one black} + 2·#{two black}` — the shape the identity
needs.  Pentagons with no black vertex contribute nothing, which is why they are
absent from the statement. -/
theorem sum_blackCard_split (C : ColouredGraphClass)
    (hle : ∀ S ∈ pentAll C, ((blackSet C).filter (fun u => u ∈ S)).card ≤ 2) :
    Finset.sum (pentAll C) (fun S => ((blackSet C).filter (fun u => u ∈ S)).card)
      = ((pentAll C).filter
            (fun S => ((blackSet C).filter (fun u => u ∈ S)).card = 1)).card
        + 2 * ((pentAll C).filter
            (fun S => ((blackSet C).filter (fun u => u ∈ S)).card = 2)).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  have h := hle S hS
  interval_cases hb : ((blackSet C).filter (fun u => u ∈ S)).card <;> simp

/-! ### Rotations of the C₅

The classification needs to relabel a pentagon so its black vertices sit in
standard position — at `3` for `F₅₆`, at `2, 4` for `F₅₅`.  Rotations are the
relabellings that do it, and they preserve the cycle. -/

/-- Rotation of the C₅ by `d`. -/
def pentRot (d : Fin 5) (k : Fin 5) : Fin 5 := ⟨(k.val + d.val) % 5, by omega⟩

theorem pentRot_zero (k : Fin 5) : pentRot 0 k = k := by fin_cases k <;> rfl

theorem pentRot_comp (d e : Fin 5) (k : Fin 5) :
    pentRot d (pentRot e k) = pentRot (⟨(d.val + e.val) % 5, by omega⟩) k := by
  fin_cases d <;> fin_cases e <;> fin_cases k <;> rfl

theorem pentRot_injective (d : Fin 5) : Function.Injective (pentRot d) := by
  intro a b h
  fin_cases d <;> fin_cases a <;> fin_cases b <;> simp_all [pentRot] <;> rfl

theorem pentRot_adj (d : Fin 5) (i j : Fin 5) :
    c5adjB (pentRot d i) (pentRot d j) = c5adjB i j := by
  fin_cases d <;> fin_cases i <;> fin_cases j <;> rfl

/-- Every vertex can be rotated to any other: the rotation taking `m` to `3`. -/
theorem pentRot_to_three (m : Fin 5) : pentRot ⟨(8 - m.val) % 5, by omega⟩ m = 3 := by
  fin_cases m <;> rfl

/-- **The structural bridge for the classification.**  A structure-preserving
injection of `pentFlag c` into the host with image inside a 5-set `S` makes `C[S]`
*isomorphic* to `pentFlag c` — the two flags then have the same size, and
`genFlagIso_of_embedding_sameSize` upgrades the embedding to an isomorphism.

This reduces "`S` induces `F₅₆`" to "produce the map", which is what the
rotations are for. -/
theorem genFlagClass_eq_of_map (C : ColouredGraphClass) (c : Fin 5 → Fin 2)
    (S : Finset (Fin C.graph.size)) (hcard : S.card = 5)
    (g : Fin 5 → Fin C.graph.size) (hinj : Function.Injective g)
    (himg : ∀ x, g x ∈ S)
    (hstr : CG2.comap g C.toGenFlag.str = (pentFlag c).str) :
    GenFlagClass.mk (pentFlag c)
      = GenFlagClass.mk (C.toGenFlag.genInducedSubflag S (fun i => i.elim0)
          (Nat.zero_le _)) := by
  rw [GenFlagClass.mk_eq]
  -- `let`, not `have`: `have` would make `e.toFun` opaque, and the `himg`
  -- hypothesis below is only *definitionally* about `e.toFun`
  let e : GenInducedEmbedding CG2 (GenFlagType.empty CG2) (pentFlag c) C.toGenFlag :=
    ⟨g, hinj, hstr, fun i => i.elim0⟩
  have himg' : ∀ x : Fin (pentFlag c).size, e.toFun x ∈ S := himg
  refine PentagonQOrbit.genFlagIso_of_embedding_sameSize
    (e.genRestrictToSubflag S (fun i => i.elim0) (Nat.zero_le _) himg') ?_
  show (5 : ℕ) = S.card
  omega

/-- **From a matching cyclic labelling to the flag class.**  If a pentagon's
cyclic labelling already carries the colouring `c`, then `S` induces `pentFlag c`.
What remains after this is purely combinatorial: rotate the labelling until the
colours line up. -/
theorem genFlagClass_eq_of_cyclic (C : ColouredGraphClass) (c : Fin 5 → Fin 2)
    (S : Finset (Fin C.graph.size)) (hcard : S.card = 5)
    (f : Fin 5 → Fin C.graph.size) (hfinj : Function.Injective f)
    (hfimg : ∀ k, f k ∈ S)
    (hfadj : ∀ i j, C.graph.graph.Adj (f i) (f j) ↔ c5adjB i j = true)
    (hfcol : ∀ k, C.colouring (f k) = c k) :
    GenFlagClass.mk (pentFlag c)
      = GenFlagClass.mk (C.toGenFlag.genInducedSubflag S (fun i => i.elim0)
          (Nat.zero_le _)) := by
  refine genFlagClass_eq_of_map C c S hcard f hfinj hfimg ?_
  apply Prod.ext
  · ext i j
    simp only [colouredGraphUniverse, pentFlag, ColouredGraphClass.toGenFlag,
      ColouredGraph.toGenFlag, ColouredGraphClass.toColouredGraph, SimpleGraph.comap_adj]
    rw [hfadj i j, c5adjB_iff]
  · funext k
    exact hfcol k

/-- `IsPentagon`'s data, in the form `genFlagClass_eq_of_cyclic` wants.
`cycleGraph5` (`PentagonConjecture.lean:54`) is *literally* `pentFlag`'s graph —
both are `fromRel (fun u v => (u+1) % 5 = v)` — so the adjacency clause transfers
through `c5adjB_iff` with nothing to prove. -/
theorem pentagon_cyclic (C : ColouredGraphClass) (S : Finset (Fin C.graph.size))
    (hS : IsPentagon C.graph S) :
    ∃ f : Fin 5 → Fin C.graph.size, Function.Injective f ∧ (∀ k, f k ∈ S) ∧
      S.card = 5 ∧ (∀ i j, C.graph.graph.Adj (f i) (f j) ↔ c5adjB i j = true) := by
  obtain ⟨f, hinj, himg, hadj⟩ := hS
  refine ⟨f, hinj, fun k => ?_, ?_, fun i j => ?_⟩
  on_goal 2 => rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fin]
  · rw [← himg]; exact Finset.mem_image_of_mem f (Finset.mem_univ k)
  · rw [← hadj i j, c5adjB_iff]
    rfl

theorem pentRot_three_to (m : Fin 5) :
    pentRot ⟨(m.val + 2) % 5, by omega⟩ 3 = m := by fin_cases m <;> rfl

theorem fin2_ne_one (x : Fin 2) (h : x ≠ 1) : x = 0 := by fin_cases x <;> simp_all

open Classical in
/-- The black positions of a pentagon, pulled back along its cyclic labelling.
`f` is a bijection onto `S`, so this has the same size as `S ∩ N(v)`. -/
theorem black_positions_card (C : ColouredGraphClass) (S : Finset (Fin C.graph.size))
    (f : Fin 5 → Fin C.graph.size) (hinj : Function.Injective f)
    (himg : Finset.image f Finset.univ = S) :
    (Finset.univ.filter (fun k : Fin 5 => C.colouring (f k) = 1)).card
      = ((blackSet C).filter (fun u => u ∈ S)).card := by
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext u
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [blackSet]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    · rw [← himg]; exact Finset.mem_image_of_mem f (Finset.mem_univ k)
  · rintro ⟨hb, hu⟩
    rw [blackSet, Finset.mem_filter] at hb
    rw [← himg] at hu
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨k, hb.2, rfl⟩

open Classical in
/-- **The τ₂ classification.**  A pentagon with exactly one black vertex induces
`F₅₆`.  The rotation carrying that vertex to position `3` is the whole content. -/
theorem genFlagClass_F56_of_one_black (C : ColouredGraphClass)
    (S : Finset (Fin C.graph.size)) (hS : IsPentagon C.graph S)
    (hone : ((blackSet C).filter (fun u => u ∈ S)).card = 1) :
    GenFlagClass.mk sdpFlag56
      = GenFlagClass.mk (C.toGenFlag.genInducedSubflag S (fun i => i.elim0)
          (Nat.zero_le _)) := by
  obtain ⟨f, hinj, himg, hadj⟩ := hS
  have hBcard : (Finset.univ.filter (fun k : Fin 5 => C.colouring (f k) = 1)).card = 1 := by
    rw [black_positions_card C S f hinj himg, hone]
  obtain ⟨m, hm⟩ := Finset.card_eq_one.mp hBcard
  have hmem : ∀ k : Fin 5, C.colouring (f k) = 1 ↔ k = m := by
    intro k
    constructor
    · intro h
      have : k ∈ Finset.univ.filter (fun k : Fin 5 => C.colouring (f k) = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [hm, Finset.mem_singleton] at this; exact this
    · intro hkm
      have hmm : m ∈ Finset.univ.filter (fun k : Fin 5 => C.colouring (f k) = 1) := by
        rw [hm]; exact Finset.mem_singleton_self m
      rw [hkm]; exact (Finset.mem_filter.mp hmm).2
  set d : Fin 5 := ⟨(m.val + 2) % 5, by omega⟩ with hd
  have hρ3 : pentRot d 3 = m := pentRot_three_to m
  rw [sdpFlag56_eq_pentFlag]
  refine genFlagClass_eq_of_cyclic C _ S ?_ (fun k => f (pentRot d k))
    (hinj.comp (pentRot_injective d)) (fun k => ?_) (fun i j => ?_) (fun k => ?_)
  · rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · rw [← himg]; exact Finset.mem_image_of_mem f (Finset.mem_univ _)
  · rw [← hadj (pentRot d i) (pentRot d j), ← pentRot_adj d i j]
    exact (c5adjB_iff _ _).symm
  · show C.colouring (f (pentRot d k)) = _
    by_cases hk : k = 3
    · subst hk
      rw [hρ3, (hmem m).mpr rfl]
      rw [if_pos (show ((3 : Fin 5)).val = 3 from rfl)]
    · have hne : pentRot d k ≠ m := by
        rw [← hρ3]; exact fun h => hk (pentRot_injective d h)
      have : C.colouring (f (pentRot d k)) ≠ 1 := fun h => hne ((hmem _).mp h)
      rw [fin2_ne_one _ this]
      rw [if_neg (show ¬(k.val = 3) from fun h => hk (Fin.ext h))]

/-- Rotations act transitively on the five non-adjacent pairs of the C₅, so any
such pair can be carried to `{2, 4}` — no reflection needed. -/
theorem c5_pair_rotate : ∀ a b : Fin 5, a ≠ b → c5adjB a b = false →
    ∃ d : Fin 5, (pentRot d 2 = a ∧ pentRot d 4 = b) ∨
      (pentRot d 2 = b ∧ pentRot d 4 = a) := by decide

open Classical in
/-- **The τ₃ classification.**  A pentagon with exactly two black vertices
induces `F₅₅`.  The pair is non-adjacent — black independence — hence at cycle
distance two, and `c5_pair_rotate` carries it to `{2, 4}`. -/
theorem genFlagClass_F55_of_two_black (C : ColouredGraphClass)
    (S : Finset (Fin C.graph.size)) (hS : IsPentagon C.graph S)
    (htwo : ((blackSet C).filter (fun u => u ∈ S)).card = 2) :
    GenFlagClass.mk pentagonTwoBlack
      = GenFlagClass.mk (C.toGenFlag.genInducedSubflag S (fun i => i.elim0)
          (Nat.zero_le _)) := by
  obtain ⟨f, hinj, himg, hadj⟩ := hS
  have hBcard : (Finset.univ.filter (fun k : Fin 5 => C.colouring (f k) = 1)).card = 2 := by
    rw [black_positions_card C S f hinj himg, htwo]
  obtain ⟨a, b, hab, hB⟩ := Finset.card_eq_two.mp hBcard
  have hmem : ∀ k : Fin 5, C.colouring (f k) = 1 ↔ (k = a ∨ k = b) := by
    intro k
    constructor
    · intro h
      have hk : k ∈ Finset.univ.filter (fun k : Fin 5 => C.colouring (f k) = 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [hB, Finset.mem_insert, Finset.mem_singleton] at hk; exact hk
    · intro hk
      have hkm : k ∈ Finset.univ.filter (fun k : Fin 5 => C.colouring (f k) = 1) := by
        rw [hB, Finset.mem_insert, Finset.mem_singleton]; exact hk
      exact (Finset.mem_filter.mp hkm).2
  -- the black pair is non-adjacent, so at cycle distance two
  have hna : c5adjB a b = false := by
    by_contra hcon
    simp only [Bool.not_eq_false] at hcon
    exact C.blackIndependent _ _ ((hmem a).mpr (Or.inl rfl)) ((hmem b).mpr (Or.inr rfl))
      ((hadj a b).mp ((c5adjB_iff a b).mp hcon))
  obtain ⟨d, hd⟩ := c5_pair_rotate a b hab hna
  rw [pentagonTwoBlack_eq_pentFlag]
  refine genFlagClass_eq_of_cyclic C _ S ?_ (fun k => f (pentRot d k))
    (hinj.comp (pentRot_injective d)) (fun k => ?_) (fun i j => ?_) (fun k => ?_)
  · rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · rw [← himg]; exact Finset.mem_image_of_mem f (Finset.mem_univ _)
  · rw [← hadj (pentRot d i) (pentRot d j), ← pentRot_adj d i j]
    exact (c5adjB_iff _ _).symm
  · show C.colouring (f (pentRot d k)) = _
    by_cases hk : k = 2 ∨ k = 4
    · have hblack : C.colouring (f (pentRot d k)) = 1 := by
        rcases hk with rfl | rfl
        · rcases hd with ⟨h2, -⟩ | ⟨h2, -⟩
          · rw [h2]; exact (hmem a).mpr (Or.inl rfl)
          · rw [h2]; exact (hmem b).mpr (Or.inr rfl)
        · rcases hd with ⟨-, h4⟩ | ⟨-, h4⟩
          · rw [h4]; exact (hmem b).mpr (Or.inr rfl)
          · rw [h4]; exact (hmem a).mpr (Or.inl rfl)
      rw [hblack, if_pos]
      rcases hk with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · have hne : pentRot d k ≠ a ∧ pentRot d k ≠ b := by
        constructor <;> intro hcon <;> apply hk
        · rcases hd with ⟨h2, -⟩ | ⟨-, h4⟩
          · exact Or.inl (pentRot_injective d (hcon.trans h2.symm))
          · exact Or.inr (pentRot_injective d (hcon.trans h4.symm))
        · rcases hd with ⟨-, h4⟩ | ⟨h2, -⟩
          · exact Or.inr (pentRot_injective d (hcon.trans h4.symm))
          · exact Or.inl (pentRot_injective d (hcon.trans h2.symm))
      have hred : C.colouring (f (pentRot d k)) ≠ 1 := by
        intro h
        rcases (hmem _).mp h with h' | h'
        · exact hne.1 h'
        · exact hne.2 h'
      rw [fin2_ne_one _ hred, if_neg]
      intro hcon
      exact hk (by rcases hcon with h | h
                   · exact Or.inl (Fin.ext h)
                   · exact Or.inr (Fin.ext h))

open Classical in
/-- **The converse.**  If `C[S]` is isomorphic to a pentagon flag, then `S`
carries a cyclic labelling with the matching colouring — the same data
`genFlagClass_eq_of_cyclic` consumes, read back off the isomorphism.

The isomorphism's `Equiv` becomes an embedding into `C[S]`; composing with the
subflag inclusion lands it in the host, where `pent_of_embedding` reads off the
structure. -/
theorem cyclic_of_genFlagClass_eq (C : ColouredGraphClass) (c : Fin 5 → Fin 2)
    (S : Finset (Fin C.graph.size))
    (h : GenFlagClass.mk (pentFlag c)
      = GenFlagClass.mk (C.toGenFlag.genInducedSubflag S (fun i => i.elim0)
          (Nat.zero_le _))) :
    ∃ f : Fin 5 → Fin C.graph.size, Function.Injective f ∧
      Finset.image f Finset.univ = S ∧
      (∀ i j, C.graph.graph.Adj (f i) (f j) ↔ c5adjB i j = true) ∧
      (∀ k, C.colouring (f k) = c k) := by
  rw [GenFlagClass.mk_eq] at h
  obtain ⟨φ, hstr, -⟩ := h
  let e₀ : GenInducedEmbedding CG2 (GenFlagType.empty CG2) (pentFlag c)
      (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)) :=
    ⟨φ, φ.injective, hstr, fun i => i.elim0⟩
  let incl := C.toGenFlag.genInducedSubflag_incl S (fun i => i.elim0) (Nat.zero_le _)
  let e := GenInducedEmbedding.comp incl e₀
  obtain ⟨hcol, hadj⟩ := pent_of_embedding C c e
  refine ⟨e.toFun, e.injective, ?_, fun i j => ?_, fun k => hcol k⟩
  · ext u
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩
      exact Finset.orderEmbOfFin_mem S rfl _
    · intro hu
      obtain ⟨z, hz⟩ : ∃ z, incl.toFun z = u :=
        ⟨(S.orderIsoOfFin rfl).symm ⟨u, hu⟩, by
          change ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨u, hu⟩)) = u
          simp [OrderIso.apply_symm_apply]⟩
      exact ⟨φ.symm z, by show incl.toFun (φ (φ.symm z)) = u; rw [Equiv.apply_symm_apply, hz]⟩
  · rw [hadj i j, ← c5adjB_iff]

open Classical in
/-- A subset inducing a pentagon flag **is** a pentagon. -/
theorem isPentagon_of_genFlagClass_eq (C : ColouredGraphClass) (c : Fin 5 → Fin 2)
    (S : Finset (Fin C.graph.size))
    (h : GenFlagClass.mk (pentFlag c)
      = GenFlagClass.mk (C.toGenFlag.genInducedSubflag S (fun i => i.elim0)
          (Nat.zero_le _))) :
    IsPentagon C.graph S := by
  obtain ⟨f, hinj, himg, hadj, -⟩ := cyclic_of_genFlagClass_eq C c S h
  -- `exact`, not `rw`: `cycleGraph5` and `fromRel …` are defeq but not syntactic
  exact ⟨f, hinj, himg, fun i j => (c5adjB_iff i j).symm.trans (hadj i j).symm⟩

open Classical in
/-- …and its black count is the flag's. -/
theorem blackCard_of_genFlagClass_eq (C : ColouredGraphClass) (c : Fin 5 → Fin 2)
    (S : Finset (Fin C.graph.size))
    (h : GenFlagClass.mk (pentFlag c)
      = GenFlagClass.mk (C.toGenFlag.genInducedSubflag S (fun i => i.elim0)
          (Nat.zero_le _))) :
    ((blackSet C).filter (fun u => u ∈ S)).card
      = (Finset.univ.filter (fun k : Fin 5 => c k = 1)).card := by
  obtain ⟨f, hinj, himg, -, hcol⟩ := cyclic_of_genFlagClass_eq C c S h
  rw [← black_positions_card C S f hinj himg]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcol k]

theorem card_black_F56 :
    (Finset.univ.filter
      (fun k : Fin 5 => (if k.val = 3 then (1 : Fin 2) else 0) = 1)).card = 1 := by decide

theorem card_black_F55 :
    (Finset.univ.filter
      (fun k : Fin 5 => (if k.val = 2 ∨ k.val = 4 then (1 : Fin 2) else 0) = 1)).card = 2 := by
  decide

open Classical in
/-- The pentagons with `n` black vertices are exactly the subsets inducing the
corresponding flag — both directions, which is what `subsetCopies` needs. -/
theorem pentFilter_eq_copies (C : ColouredGraphClass) (c : Fin 5 → Fin 2)
    (n : ℕ) (hn : (Finset.univ.filter (fun k : Fin 5 => c k = 1)).card = n)
    (hfwd : ∀ S : Finset (Fin C.graph.size), IsPentagon C.graph S →
      ((blackSet C).filter (fun u => u ∈ S)).card = n →
      GenFlagClass.mk (pentFlag c)
        = GenFlagClass.mk (C.toGenFlag.genInducedSubflag S (fun i => i.elim0)
            (Nat.zero_le _))) :
    (pentAll C).filter
        (fun S => ((blackSet C).filter (fun u => u ∈ S)).card = n)
      = Finset.univ.filter (fun S : Finset (Fin C.graph.size) =>
          GenFlagClass.mk (C.toGenFlag.genInducedSubflag S (fun i => i.elim0)
            (Nat.zero_le _)) = GenFlagClass.mk (pentFlag c)) := by
  ext S
  simp only [pentAll, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, hb⟩
    exact (hfwd S hp hb).symm
  · intro h
    exact ⟨isPentagon_of_genFlagClass_eq C c S h.symm,
      by rw [blackCard_of_genFlagClass_eq C c S h.symm, hn]⟩

open Classical in
/-- At most two black positions, phrased on a cyclic labelling rather than an
embedding — the form the identity needs. -/
theorem black_positions_le_two (C : ColouredGraphClass) (f : Fin 5 → Fin C.graph.size)
    (hadj : ∀ i j, C.graph.graph.Adj (f i) (f j) ↔ c5adjB i j = true) :
    (Finset.univ.filter (fun k : Fin 5 => C.colouring (f k) = 1)).card ≤ 2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := Finset.two_lt_card_iff.mp hcon
  have hb : ∀ x ∈ Finset.univ.filter (fun k : Fin 5 => C.colouring (f k) = 1),
      C.colouring (f x) = 1 := fun x hx => (Finset.mem_filter.mp hx).2
  rcases c5_three_meet i j k hij hik hjk with h | h | h
  · exact C.blackIndependent _ _ (hb i hi) (hb j hj) ((hadj i j).mpr h)
  · exact C.blackIndependent _ _ (hb i hi) (hb k hk) ((hadj i k).mpr h)
  · exact C.blackIndependent _ _ (hb j hj) (hb k hk) ((hadj j k).mpr h)

open Classical in
/-- **The pentagon-visit identity.**  `c(F₅₆;G') + 2·c(F₅₅;G') = Σ_{u ∈ N(v)} P(G,u)`.

The last genuinely new combinatorial lemma of item (a); nothing in the repo
proved it. -/
theorem pentagon_visit_identity (C : ColouredGraphClass) :
    PentagonQOrbit.subsetCopies sdpFlag56 C.toGenFlag
      + 2 * PentagonQOrbit.subsetCopies pentagonTwoBlack C.toGenFlag
      = Finset.sum (blackSet C) (fun u => pentagonCountAt C.graph u) := by
  have hle : ∀ S ∈ pentAll C, ((blackSet C).filter (fun u => u ∈ S)).card ≤ 2 := by
    intro S hS
    obtain ⟨g, hginj, hgimg, hgadj⟩ := (Finset.mem_filter.mp hS).2
    rw [← black_positions_card C S g hginj hgimg]
    exact black_positions_le_two C g
      (fun i j => (hgadj i j).symm.trans (c5adjB_iff i j).symm)
  rw [sum_black_pentagonCount, sum_blackCard_split C hle]
  rw [pentFilter_eq_copies C _ 1 card_black_F56
        (fun S hp hb => genFlagClass_F56_of_one_black C S hp hb |>.trans rfl),
    pentFilter_eq_copies C _ 2 card_black_F55
        (fun S hp hb => genFlagClass_F55_of_two_black C S hp hb |>.trans rfl)]
  rfl

#print axioms black_positions_le_two
#print axioms pentagon_visit_identity
#print axioms card_black_F56
#print axioms card_black_F55
#print axioms pentFilter_eq_copies
#print axioms isPentagon_of_genFlagClass_eq
#print axioms blackCard_of_genFlagClass_eq
#print axioms cyclic_of_genFlagClass_eq
#print axioms c5_pair_rotate
#print axioms genFlagClass_F55_of_two_black
#print axioms genFlagClass_F56_of_one_black
#print axioms pentRot_three_to
#print axioms black_positions_card
#print axioms pentagon_cyclic
#print axioms genFlagClass_eq_of_cyclic
#print axioms genFlagClass_eq_of_map
#print axioms pentRot_comp
#print axioms pentRot_injective
#print axioms pentRot_adj
#print axioms pentRot_to_three
#print axioms sum_blackCard_split
#print axioms blackSet
#print axioms sum_black_pentagonCount
#print axioms c5_three_meet
#print axioms pent_black_le_two
#print axioms sum_pentRooted_eq_two_mul_copies
#print axioms sum_n2_eq_two_mul_copies
#print axioms sum_n3_eq_two_mul_copies
#print axioms pentAut_fix3_55
#print axioms genFlagAutCount_pentagonTwoBlack
#print axioms genFlagAutCount_sdpFlag56
#print axioms c5adjB_iff
#print axioms pentIdAut
#print axioms pentAut_data
#print axioms pentAut_fix3_56
#print axioms c5_rigid
#print axioms pentRefl_involutive
#print axioms pentRefl_adj
#print axioms pentAut
#print axioms sdpFlag56_refl_colour
#print axioms pentagonTwoBlack_refl_colour
#print axioms pentEmbCond_iff
#print axioms sum_pentRootedCountG_eq_card_mul
#print axioms pent_cycle_of_embedding
#print axioms card_valid_eightSets_pent
#print axioms pentFlag
#print axioms sdpFlag56_eq_pentFlag
#print axioms pentagonTwoBlack_eq_pentFlag
#print axioms pent_of_embedding
#print axioms mem_pentTupleOf_iff
#print axioms card_pentSet5
#print axioms card_pentFibreOf
#print axioms card_union_pentFibre
#print axioms union_pentFibre_injective
#print axioms union_pentFibre_surjective
#print axioms pent_root_nbhd_inter
#print axioms card_pent_root_nbhd_sdiff
/-! ### `pentagonTwoBlack` and `sdpFlag55` are the same flag

Deferred when `pentagonTwoBlack` was introduced: the two differ only in
labelling, so relating them is an **isomorphism, not an equality**.
`sdpFlag55`'s cycle is `0-1-3-4-2-0` with black at `2, 3`, which sit at cycle
positions `2` and `4` — exactly where `pentagonTwoBlack` puts them.  The
relabelling is therefore `![0,1,3,4,2]`. -/

/-- The relabelling carrying `pentagonTwoBlack` to `sdpFlag55`. -/
def ptbToF55 : Fin 5 → Fin 5 := ![0, 1, 3, 4, 2]

/-- Its inverse. -/
def f55ToPtb : Fin 5 → Fin 5 := ![0, 1, 4, 2, 3]

theorem ptbToF55_left_inv : ∀ i, f55ToPtb (ptbToF55 i) = i := by decide

theorem ptbToF55_right_inv : ∀ i, ptbToF55 (f55ToPtb i) = i := by decide

/-- The relabelling as an equivalence. -/
def ptbEquiv : Fin 5 ≃ Fin 5 where
  toFun := ptbToF55
  invFun := f55ToPtb
  left_inv := ptbToF55_left_inv
  right_inv := ptbToF55_right_inv

/-- **`pentagonTwoBlack ≅ sdpFlag55`.**  Counting is isomorphism-invariant, so
this is what lets `(a2b)`'s `c(F₅₅;G')` be read at either flag. -/
theorem pentagonTwoBlack_iso_sdpFlag55 :
    GenFlagClass.mk pentagonTwoBlack = GenFlagClass.mk sdpFlag55 := by
  rw [GenFlagClass.mk_eq]
  refine ⟨ptbEquiv, ?_, fun i => i.elim0⟩
  apply Prod.ext
  · ext i j
    simp only [colouredGraphUniverse, pentagonTwoBlack, sdpFlag55,
      SimpleGraph.comap_adj, SimpleGraph.fromRel_adj, ptbEquiv, ptbToF55]
    fin_cases i <;> fin_cases j <;> simp
  · funext i
    simp only [colouredGraphUniverse, pentagonTwoBlack, sdpFlag55, ptbEquiv, ptbToF55]
    fin_cases i <;> rfl

#print axioms ptbToF55_left_inv
#print axioms pentagonTwoBlack_iso_sdpFlag55

#print axioms pentagonTwoBlack
#print axioms tauFlag_tau3_eq_pentagonTwoBlack
#print axioms sdpFlag56
#print axioms tauFlag_tau2_eq_sdpFlag56
#print axioms sum_n1_eq_two_mul_pentagon
#print axioms embCond_iff_tupleCond
#print axioms sum_rootedCountG_eq_card_mul
#print axioms tupleOf
#print axioms mem_tupleSet_iff
#print axioms rootedCountG_subflag_card
#print axioms double_count
#print axioms card_valid_eightSets
#print axioms mem_brrbFilter_of_embedding
#print axioms brrb_of_embedding
#print axioms tauFlag_tau1_eq_brrbGenFlag
#print axioms brrb_nonedges
#print axioms root_nbhd_inter_tuple
#print axioms card_root_nbhd_sdiff_tuple
#print axioms pentagonToTuple_span
#print axioms fwd_rev_disjoint
#print axioms brrbCount_eq_two_mul
#print axioms brrbSetOf_card
#print axioms pentSetOf_card
#print axioms brrbSetOf_eq_union
#print axioms brrb_of_pentagon_rev
#print axioms pentagonToTuple_ne_rev
#print axioms vColouredClass
#print axioms brrb_of_pentagon
#print axioms vColouring_eq_one
#print axioms vColouring_eq_zero
#print axioms exists_pentagon_of_brrb
#print axioms v_ne_of_brrb
#print axioms isPentagon_of_brrb
#print axioms pentagonToTuple_of_brrb

end PentagonQBrrbSurj
end Davey2024
