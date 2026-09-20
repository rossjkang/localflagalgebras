import DaveyThesis2024.PentagonDelta3


/-!
# Pentagons in triangle-free graphs of maximum degree ≤ 4 (Δ = 4)

The per-vertex pentagon bound at Δ = 4: in a triangle-free graph with maximum degree
at most 4, every vertex lies on at most `24` pentagons, hence `5·P(G) ≤ 24·|G|`, i.e.
`P(G) ≤ 24|G|/5 = 4.8|G|`.

This is the bound the local (per-vertex) certificate method proves outright, mirroring the
Δ = 3 / Δ = 5 development (`pentagon_bound_delta3` / `pentagon_delta5_tight`).  It is weaker
than the sharp Δ = 4 bound `P ≤ 4|G|` (ratio `1/64`, attained by the circulant `C₁₂(2,3)`
with `pentagonCount = 48`, and by `C₁₃(2,3)` with `52`).  That sharp bound is now an
unconditional Lean theorem, `Delta4Gen.pentagon_bound_delta4_sharp`, on the three standard
kernel axioms; equality is *not* classified.  Its finite check lives in
`DaveyThesis2024/Delta4/` (hand-written) and `Delta4/Generated/` (machine-written), which sit
outside the default build because the check costs about two hours -- see
`Delta4/Generated/generator/README.md`.

**No per-vertex argument can close the gap**, which is why the two differ: the per-vertex
maximum decouples from the density.  `PentagonDelta4Witness.lean` gives an 11-vertex graph
with a vertex on exactly `24 > 20` pentagons, so the `24` below is attained and no unweighted
per-vertex local-max argument reaches `4|G|`.

The Lean route to the sharp bound instead goes through the rerooting row `pentagonQ ≤ 160`
(see `pentagon_bound_delta4_of_regular_transport_family` at the end of this file): shell
saturation, the punctured neighbour count `r_a ≤ 13`, the `Q`-split `Q(v) = 6 p(v) + Σ r_a`,
the low branch (shell objective `≤ 18`), the shell T-identity, the neighbour layer (F4),
conservativity, and the high-root classification, which the finite check discharges.  Nothing
in that route remains open.

The certificate here gives the sharp per-vertex bound, `24`
(`certY4 = (0,1,4,5,0)`: `2pq ≤ certY4 p + certY4 q` for `p+q ≤ 4` and
`(4−k)·certY4 k ≤ 4k`, so `2·Σ ≤ Σ_x (4−k_x)·certY4 k_x ≤ 4·Σ_x k_x ≤ 4·12`).
-/

namespace Davey2024

namespace PentagonLocal

open Finset
open scoped Classical

variable {G : Flag emptyType}

/-! ### The shell fibre map is a bijection

`pentagonCountAt_le_sum` (`PentagonConjecture.lean`) bounds the pentagon count at `v` by the
weighted shell-edge count.  That bound is in fact an **equality**, and it needs no degree
hypothesis at all — triangle-freeness alone.

The map sends a pentagon through `v` to its opposite shell edge `(x,y)`, and the inverse
picks `a ∈ A_x`, `b ∈ A_y`.  Triangle-freeness is what makes that inverse land back in the
pentagons, and it is used exactly four times: to force `a ≠ b` and to kill the three possible
chords `a∼b`, `a∼y`, `x∼b` (the remaining two, `v∼x` and `v∼y`, are excluded by `x, y` lying
in the shell).

This closes a gap in the stated identities of the development notes, whose
auditors asserted the bijection.  It is **not** on the critical path to `P ≤ 4|G|`: that
chain uses `p(v) ≤ T(v)` and `r_a ≤ T_a` as inequalities pointing the safe way, so the
equality is never needed.  It is recorded because it is true, sharper than the inequality it
refines, and was otherwise proved only in a scratch file. -/

/-- **Step 1 of the fibre lemma (`SHELL_BOX_AND_FIBRE.tex`, Lemma 4.?):**
    `Ψ(x,y,a,b) = {v,a,x,y,b}` lands in `𝒫_v`.  Triangle-freeness is used
    exactly four times: `a ≠ b`, `¬ a∼b`, `¬ a∼y`, `¬ x∼b`. -/
lemma isPentagon_of_shell_attach (hTF : IsTriangleFree G) {v x y a b : Fin G.size}
    (hx : x ∈ shellSet G v) (hy : y ∈ shellSet G v) (hxy : G.graph.Adj x y)
    (ha : a ∈ attachSet G v x) (hb : b ∈ attachSet G v y) :
    IsPentagon G {v, a, x, y, b} := by
  rw [shellSet, Finset.mem_filter] at hx hy
  rw [attachSet, Finset.mem_filter] at ha hb
  obtain ⟨-, hxne, hvx⟩ := hx
  obtain ⟨-, hyne, hvy⟩ := hy
  obtain ⟨-, hva, hxa⟩ := ha
  obtain ⟨-, hvb, hyb⟩ := hb
  -- the five cycle edges (both orientations)
  have e1 : G.graph.Adj v a := hva
  have e1' : G.graph.Adj a v := hva.symm
  have e2 : G.graph.Adj a x := hxa.symm
  have e2' : G.graph.Adj x a := hxa
  have e3 : G.graph.Adj x y := hxy
  have e3' : G.graph.Adj y x := hxy.symm
  have e4 : G.graph.Adj y b := hyb
  have e4' : G.graph.Adj b y := hyb.symm
  have e5 : G.graph.Adj b v := hvb.symm
  have e5' : G.graph.Adj v b := hvb
  -- the five chords, absent
  have n1 : ¬ G.graph.Adj v x := hvx
  have n1' : ¬ G.graph.Adj x v := fun h => hvx h.symm
  have n2 : ¬ G.graph.Adj v y := hvy
  have n2' : ¬ G.graph.Adj y v := fun h => hvy h.symm
  have n3 : ¬ G.graph.Adj a b := fun h => hTF v a b hva h hvb
  have n3' : ¬ G.graph.Adj b a := fun h => n3 h.symm
  have n4 : ¬ G.graph.Adj a y := fun h => hTF x a y hxa h hxy
  have n4' : ¬ G.graph.Adj y a := fun h => n4 h.symm
  have n5 : ¬ G.graph.Adj x b := fun h => hTF x y b hxy hyb h
  have n5' : ¬ G.graph.Adj b x := fun h => n5 h.symm
  -- five distinct vertices
  have dva : v ≠ a := G.graph.ne_of_adj hva
  have dvx : v ≠ x := fun h => hxne h.symm
  have dvy : v ≠ y := fun h => hyne h.symm
  have dvb : v ≠ b := G.graph.ne_of_adj hvb
  have dax : a ≠ x := fun h => G.graph.ne_of_adj e2 h
  have day : a ≠ y := fun h => n2 (h ▸ hva)
  have dab : a ≠ b := by rintro rfl; exact hTF x y a hxy hyb hxa
  have dxy : x ≠ y := G.graph.ne_of_adj hxy
  have dxb : x ≠ b := by rintro rfl; exact n1 e5'
  have dyb : y ≠ b := G.graph.ne_of_adj hyb
  refine ⟨![v, a, x, y, b], ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · have huniv : (Finset.univ : Finset (Fin 5)) = {0,1,2,3,4} := by decide
    rw [huniv]
    simp [Finset.image_insert]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      first
        | exact iff_of_true (by decide) (by assumption)
        | exact iff_of_false (by decide) (by assumption)
        | exact iff_of_false (by decide) (G.graph.irrefl)






/-- The three filters of the constructed pentagon compute to `{x,y}`, `{a}`, `{b}`. -/
lemma fibre_filters (hTF : IsTriangleFree G) {v x y a b : Fin G.size}
    (hx : x ∈ shellSet G v) (hy : y ∈ shellSet G v) (hxy : G.graph.Adj x y)
    (ha : a ∈ attachSet G v x) (hb : b ∈ attachSet G v y) :
    (({v,a,x,y,b} : Finset (Fin G.size)).filter fun u => u ≠ v ∧ ¬G.graph.Adj v u)
        = {x,y} ∧
    (({v,a,x,y,b} : Finset (Fin G.size)).filter
        fun u => G.graph.Adj v u ∧ G.graph.Adj x u) = {a} ∧
    (({v,a,x,y,b} : Finset (Fin G.size)).filter
        fun u => G.graph.Adj v u ∧ G.graph.Adj y u) = {b} := by
  rw [shellSet, Finset.mem_filter] at hx hy
  rw [attachSet, Finset.mem_filter] at ha hb
  obtain ⟨-, hxne, hvx⟩ := hx
  obtain ⟨-, hyne, hvy⟩ := hy
  obtain ⟨-, hva, hxa⟩ := ha
  obtain ⟨-, hvb, hyb⟩ := hb
  have n4 : ¬ G.graph.Adj y a := fun h => hTF x a y hxa h.symm hxy
  have n5 : ¬ G.graph.Adj x b := fun h => hTF x y b hxy hyb h
  refine ⟨?_, ?_, ?_⟩
  · ext u
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl | rfl, h1, h2⟩
      · exact absurd rfl h1
      · exact absurd hva h2
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hvb h2
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), hxne, hvx⟩
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), hyne, hvy⟩
  · ext u
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl | rfl, h1, h2⟩
      · exact absurd h1 (G.graph.irrefl)
      · rfl
      · exact absurd h1 hvx
      · exact absurd h1 hvy
      · exact absurd h2 n5
    · rintro rfl
      exact ⟨Or.inr (Or.inl rfl), hva, hxa⟩
  · ext u
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | rfl | rfl | rfl, h1, h2⟩
      · exact absurd h1 (G.graph.irrefl)
      · exact absurd h2 n4
      · exact absurd h1 hvx
      · exact absurd h1 hvy
      · rfl
    · rintro rfl
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inr rfl))), hvb, hyb⟩





/-- **The fibre identity** (`SHELL_BOX_AND_FIBRE.tex` Lemma "Shell fibre bijection"):
    in a triangle-free graph the pentagon count at `v` equals the weighted shell-edge
    count.  No degree bound, regularity or connectivity is used. -/
theorem pentagonCountAt_eq_sum (hTF : IsTriangleFree G) (v : Fin G.size) :
    pentagonCountAt G v
      = ∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card := by
  rw [pentagonCountAt]
  have hmaps : Set.MapsTo (oppEdge G v)
      ↑(Finset.univ.filter (fun S => IsPentagon G S ∧ v ∈ S)) ↑(shellPairsLt G v) := by
    intro S hS
    rw [Finset.mem_coe, Finset.mem_filter] at hS
    obtain ⟨a, b, x, y, hlt, hadjxy, hxsh, hysh, -, -, hfil, -, -, -⟩ :=
      pentagon_decomp hTF hS.2.1 hS.2.2
    have hopp : oppEdge G v S = (x, y) := by
      rw [oppEdge, hfil, pickMin_pair hlt, pickMax_pair hlt]
    rw [hopp, Finset.mem_coe, shellPairsLt, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hxsh, hysh⟩, hlt, hadjxy⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.card_product]
  rw [shellPairsLt, Finset.mem_filter, Finset.mem_product] at hp
  obtain ⟨⟨hp1, hp2⟩, hlt, hadj⟩ := hp
  refine Finset.card_bij (fun S _ => abPair G v p S) ?_ ?_ ?_
  -- (i) the map lands in the product  [existing: pentagonCountAt_le_sum]
  · intro S hS
    dsimp only
    rw [Finset.mem_filter] at hS
    obtain ⟨hS1, hS2⟩ := hS
    rw [Finset.mem_filter] at hS1
    obtain ⟨a, b, x, y, hlt', hadjxy, hxsh, hysh, ha, hb, hfil, hfa, hfb, hSeq⟩ :=
      pentagon_decomp hTF hS1.2.1 hS1.2.2
    have hopp : oppEdge G v S = (x, y) := by
      rw [oppEdge, hfil, pickMin_pair hlt', pickMax_pair hlt']
    have hpx : p.1 = x := by rw [← hS2, hopp]
    have hpy : p.2 = y := by rw [← hS2, hopp]
    rw [Finset.mem_product, abPair, hpx, hpy, hfa, hfb,
      pickMin_singleton, pickMin_singleton]
    exact ⟨ha, hb⟩
  -- (ii) injectivity  [existing: pentagonCountAt_le_sum]
  · intro S1 hS1 S2 hS2 heq
    dsimp only at heq
    rw [Finset.mem_filter] at hS1 hS2
    obtain ⟨h1Pv, h1opp⟩ := hS1
    obtain ⟨h2Pv, h2opp⟩ := hS2
    rw [Finset.mem_filter] at h1Pv h2Pv
    obtain ⟨a1, b1, x1, y1, hlt1, -, -, -, -, -, hfil1, hfa1, hfb1, hSeq1⟩ :=
      pentagon_decomp hTF h1Pv.2.1 h1Pv.2.2
    obtain ⟨a2, b2, x2, y2, hlt2, -, -, -, -, -, hfil2, hfa2, hfb2, hSeq2⟩ :=
      pentagon_decomp hTF h2Pv.2.1 h2Pv.2.2
    have hopp1 : oppEdge G v S1 = (x1, y1) := by
      rw [oppEdge, hfil1, pickMin_pair hlt1, pickMax_pair hlt1]
    have hopp2 : oppEdge G v S2 = (x2, y2) := by
      rw [oppEdge, hfil2, pickMin_pair hlt2, pickMax_pair hlt2]
    have hx1 : p.1 = x1 := by rw [← h1opp, hopp1]
    have hy1 : p.2 = y1 := by rw [← h1opp, hopp1]
    have hx2 : p.1 = x2 := by rw [← h2opp, hopp2]
    have hy2 : p.2 = y2 := by rw [← h2opp, hopp2]
    have hab1 : abPair G v p S1 = (a1, b1) := by
      rw [abPair, hx1, hy1, hfa1, hfb1, pickMin_singleton, pickMin_singleton]
    have hab2 : abPair G v p S2 = (a2, b2) := by
      rw [abPair, hx2, hy2, hfa2, hfb2, pickMin_singleton, pickMin_singleton]
    rw [hab1, hab2, Prod.mk.injEq] at heq
    rw [hSeq1, hSeq2, heq.1, heq.2, ← hx1, ← hy1, ← hx2, ← hy2]
  -- (iii) SURJECTIVITY  [the missing step]
  · intro q hq
    rw [Finset.mem_product] at hq
    obtain ⟨hq1, hq2⟩ := hq
    obtain ⟨hfil, hfa, hfb⟩ := fibre_filters hTF hp1 hp2 hadj hq1 hq2
    refine ⟨{v, q.1, p.1, p.2, q.2}, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _,
        isPentagon_of_shell_attach hTF hp1 hp2 hadj hq1 hq2, by simp⟩, ?_⟩
      rw [oppEdge, hfil, pickMin_pair hlt, pickMax_pair hlt]
    · dsimp only
      rw [abPair, hfa, hfb, pickMin_singleton, pickMin_singleton]

/-- Δ = 4 dual-certificate weights: `certY4 = (0, 1, 4, 5, 0, …)`. -/
def certY4 : ℕ → ℕ
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | _ => 0

lemma certY4_pair {p q : ℕ} (h : p + q ≤ 4) : 2 * (p * q) ≤ certY4 p + certY4 q := by
  have hp : p ≤ 4 := by omega
  have hq : q ≤ 4 := by omega
  interval_cases p <;> interval_cases q <;> revert h <;> decide

lemma certY4_token (k : ℕ) : (4 - k) * certY4 k ≤ 4 * k := by
  match k with
  | 0 | 1 | 2 | 3 => decide
  | n + 4 => rw [show 4 - (n + 4) = 0 by omega]; simp

/-- On a shell edge, the two attachment counts fit inside the actual root
    neighbourhood.  This degree-sensitive form is needed below when the ambient
    maximum degree is four but the root degree is at most three. -/
lemma attach_card_add_le_degree (hTF : IsTriangleFree G)
    {v x y : Fin G.size} (hxy : G.graph.Adj x y) :
    (attachSet G v x).card + (attachSet G v y).card ≤ vertexDegree G v := by
  rw [← Finset.card_union_of_disjoint (attachSet_disjoint hTF hxy)]
  change (attachSet G v x ∪ attachSet G v y).card ≤
    (Finset.univ.filter fun a => G.graph.Adj v a).card
  refine Finset.card_le_card ?_
  intro a ha
  rw [Finset.mem_union, attachSet, attachSet, Finset.mem_filter, Finset.mem_filter] at ha
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ a, by tauto⟩

/-- On a shell edge, the two attachment counts sum to at most 4 (Δ = 4 budget). -/
lemma attach_card_add_le4 (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 4)
    {v x y : Fin G.size} (hxy : G.graph.Adj x y) :
    (attachSet G v x).card + (attachSet G v y).card ≤ 4 :=
  le_trans (attach_card_add_le_degree hTF hxy) (vertexDegree_le_maxDegree G v |>.trans hΔ)

/-- **Double counting the shell attachment.**  Summing the attachment sizes `|A_x|`
    over the second shell is the same as counting, for each neighbour `a` of the root,
    how many shell vertices are adjacent to `a`.  Both the capacity bound below and the
    saturation equality of a regular graph are read off from this one exchange. -/
lemma sum_attach_card_swap (v : Fin G.size) :
    ∑ x ∈ shellSet G v, (attachSet G v x).card
      = ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
          ((shellSet G v).filter fun x => G.graph.Adj x a).card := by
  simp only [attachSet, Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hva : G.graph.Adj v a <;> simp [hva]

/-- Degree-sensitive capacity: every neighbour of the root has at most three
    shell neighbours, so total shell attachment is at most `3 * deg(v)`. -/
lemma sum_attach_card_le_three_mul_degree (hΔ : maxDegree G ≤ 4) (v : Fin G.size) :
    ∑ x ∈ shellSet G v, (attachSet G v x).card ≤ vertexDegree G v * 3 := by
  rw [sum_attach_card_swap]
  have hbound : ∀ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
      ((shellSet G v).filter fun x => G.graph.Adj x a).card ≤ 3 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    have hsub : (shellSet G v).filter (fun x => G.graph.Adj x a)
        ⊆ (Finset.univ.filter fun w => G.graph.Adj a w).erase v := by
      intro x hx
      rw [Finset.mem_filter, shellSet, Finset.mem_filter] at hx
      rw [Finset.mem_erase, Finset.mem_filter]
      exact ⟨hx.1.2.1, Finset.mem_univ x, hx.2.symm⟩
    have hvmem : v ∈ Finset.univ.filter fun w => G.graph.Adj a w := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ v, ha.2.symm⟩
    calc ((shellSet G v).filter fun x => G.graph.Adj x a).card
        ≤ ((Finset.univ.filter fun w => G.graph.Adj a w).erase v).card :=
          Finset.card_le_card hsub
      _ = (Finset.univ.filter fun w => G.graph.Adj a w).card - 1 :=
          Finset.card_erase_of_mem hvmem
      _ ≤ 3 := by have := deg_le_of_maxDegree_le hΔ a; omega
  calc ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
        ((shellSet G v).filter fun x => G.graph.Adj x a).card
      ≤ ∑ _a ∈ Finset.univ.filter (fun a => G.graph.Adj v a), 3 :=
        Finset.sum_le_sum hbound
    _ = (Finset.univ.filter (fun a => G.graph.Adj v a)).card * 3 := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = vertexDegree G v * 3 := rfl

/-- Capacity: total attachment over the shell is at most `4 · 3 = 12` (Δ = 4 budget). -/
lemma sum_attach_card_le4 (hΔ : maxDegree G ≤ 4) (v : Fin G.size) :
    ∑ x ∈ shellSet G v, (attachSet G v x).card ≤ 12 := by
  have h := sum_attach_card_le_three_mul_degree hΔ v
  have hd := vertexDegree_le_maxDegree G v
  omega

/-! ### Saturation: the Δ = 4 capacity bound is an equality on regular graphs

The capacity bound `sum_attach_card_le4` says the shell can absorb at most `12` units of
attachment.  When the graph is `4`-regular that budget is spent exactly: each of the four
root neighbours has three neighbours outside `N[v]`, none of which can be `v` itself and
none of which can be a root neighbour (that would close a triangle).  This turns the shell
of a high root from "a weighted graph satisfying some inequalities" into a *saturated*
object, which is what pins the attachment multiset down to a finite list. -/

/-- For a genuine root neighbour `a`, membership of `a` in the attachment set `A_x` is
    just adjacency of `a` to `x`: the condition `G.graph.Adj v a` in `attachSet` is
    already discharged by the hypothesis. -/
lemma filter_mem_attachSet_eq {v a : Fin G.size} (hva : G.graph.Adj v a) :
    (shellSet G v).filter (fun x => a ∈ attachSet G v x)
      = (shellSet G v).filter (fun x => G.graph.Adj x a) := by
  refine Finset.filter_congr fun x _ => ?_
  simp [attachSet, hva]

/-- **Saturation, per-letter form.**  In a triangle-free `4`-regular graph every
    neighbour `a` of the root `v` occurs in exactly three attachment sets, i.e. `a` has
    exactly three neighbours in the second shell.

    Indeed `a` has four neighbours in all; one of them is `v`; and every other neighbour
    `x` of `a` lies in the shell, since `x = v` is excluded and `G.graph.Adj v x` would
    make `v, a, x` a triangle. -/
theorem attach_multiplicity_eq_three (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) {v a : Fin G.size} (hva : G.graph.Adj v a) :
    ((shellSet G v).filter fun x => a ∈ attachSet G v x).card = 3 := by
  have hset : (shellSet G v).filter (fun x => a ∈ attachSet G v x)
      = (Finset.univ.filter fun w => G.graph.Adj a w).erase v := by
    ext x
    simp only [Finset.mem_filter, shellSet, attachSet, Finset.mem_erase,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hxv, -⟩, -, hxa⟩
      exact ⟨hxv, hxa.symm⟩
    · rintro ⟨hxv, hax⟩
      refine ⟨⟨hxv, ?_⟩, hva, hax.symm⟩
      intro hvx
      exact hTF v a x hva hax hvx
  have hvmem : v ∈ Finset.univ.filter fun w => G.graph.Adj a w := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ v, hva.symm⟩
  rw [hset, Finset.card_erase_of_mem hvmem, hReg a, hdeg]

/-- **Saturation, summed form (Lemma B4, equality half).**  In a triangle-free
    `4`-regular graph the total attachment over the shell of any root is exactly `12`,
    so the capacity bound `sum_attach_card_le4` is tight. -/
theorem sum_attach_card_eq_twelve (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size) :
    ∑ x ∈ shellSet G v, (attachSet G v x).card = 12 := by
  rw [sum_attach_card_swap]
  have hcell : ∀ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
      ((shellSet G v).filter fun x => G.graph.Adj x a).card = 3 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [← filter_mem_attachSet_eq ha.2]
    exact attach_multiplicity_eq_three hTF hReg hdeg ha.2
  rw [Finset.sum_congr rfl hcell, Finset.sum_const, smul_eq_mul, hReg v, hdeg]

/-- Shell degree and attachment count fit in the Δ = 4 degree budget. -/
lemma shellDeg_add_attach_le4 (hΔ : maxDegree G ≤ 4) (v x : Fin G.size) :
    ((shellSet G v).filter fun y => G.graph.Adj x y).card + (attachSet G v x).card ≤ 4 := by
  have hdisj : Disjoint ((shellSet G v).filter fun y => G.graph.Adj x y)
      (attachSet G v x) := by
    rw [Finset.disjoint_left]
    intro u hu ha
    rw [Finset.mem_filter, shellSet, Finset.mem_filter] at hu
    rw [attachSet, Finset.mem_filter] at ha
    exact hu.1.2.2 ha.2.1
  rw [← Finset.card_union_of_disjoint hdisj]
  refine le_trans (Finset.card_le_card ?_) (deg_le_of_maxDegree_le hΔ x)
  intro u hu
  rw [Finset.mem_union, Finset.mem_filter, attachSet, Finset.mem_filter] at hu
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ u, ?_⟩
  rcases hu with h | h
  · exact h.2
  · exact h.2.2

/-- **The shell objective is at most `24`.**  On a shell edge the `certY4` certificate gives
    `2 k_x k_y ≤ certY4 k_x + certY4 k_y`; exchanging the edge sum for a vertex sum, each
    shell vertex contributes at most `(4 - k_x)·certY4 k_x ≤ 4 k_x`, and total attachment is
    at most `12`.  Hence `2T ≤ 48`.

    No regularity is required, which is why this — rather than the identity-based
    `shellObjective_le_24_of_regular` — is the general form. -/
theorem shellObjective_le_24 (G : Flag emptyType) (hTF : IsTriangleFree G)
    (hΔ : maxDegree G ≤ 4) (v : Fin G.size) :
    ∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card ≤ 24 := by
  set T := ∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card
    with hT
  have hchain : 2 * T ≤ 48 := by
    have h1 : 2 * T
        ≤ ∑ p ∈ shellPairsLt G v, (certY4 (attachSet G v p.1).card
            + certY4 (attachSet G v p.2).card) := by
      rw [hT, Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      have hadj : G.graph.Adj p.1 p.2 :=
        ((Finset.mem_filter.mp hp).2).2
      exact certY4_pair (attach_card_add_le4 hTF hΔ hadj)
    have h2 : ∑ p ∈ shellPairsLt G v, (certY4 (attachSet G v p.1).card
            + certY4 (attachSet G v p.2).card)
        = ∑ x ∈ shellSet G v, ((shellSet G v).filter fun y => G.graph.Adj x y).card
            * certY4 (attachSet G v x).card := by
      rw [sum_pairsLt_endpoints v (fun u => certY4 (attachSet G v u).card),
        sum_pairsAdj_eq v (fun u => certY4 (attachSet G v u).card)]
    have h3 : ∑ x ∈ shellSet G v, ((shellSet G v).filter fun y => G.graph.Adj x y).card
            * certY4 (attachSet G v x).card
        ≤ ∑ x ∈ shellSet G v, 4 * (attachSet G v x).card := by
      refine Finset.sum_le_sum fun x _ => ?_
      have hbudget := shellDeg_add_attach_le4 hΔ v x
      calc ((shellSet G v).filter fun y => G.graph.Adj x y).card
              * certY4 (attachSet G v x).card
          ≤ (4 - (attachSet G v x).card) * certY4 (attachSet G v x).card :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 4 * (attachSet G v x).card := certY4_token _
    have h4 : ∑ x ∈ shellSet G v, 4 * (attachSet G v x).card ≤ 48 := by
      rw [← Finset.mul_sum]
      have := sum_attach_card_le4 hΔ v
      omega
    omega
  omega

/-- **The per-vertex pentagon bound at Δ ≤ 4**: every vertex of a triangle-free graph of
    maximum degree at most 4 lies on at most 24 pentagons.

    This is **sharp**, and the bound together with its witness pins the per-vertex maximum
    at exactly `24`: `pentagonCountAt_le_24_tight` (`PentagonDelta4Witness.lean`) exhibits an
    11-vertex triangle-free graph of maximum degree four with a vertex on exactly `24`
    pentagons.  (An earlier version of this docstring called the bound loose and claimed a
    true maximum of `21`; that is refuted by the witness in this same development.) -/
theorem pentagonCountAt_le_24 (G : Flag emptyType) (hTF : IsTriangleFree G)
    (hΔ : maxDegree G ≤ 4) (v : Fin G.size) : pentagonCountAt G v ≤ 24 :=
  le_trans (pentagonCountAt_le_sum hTF (le_trans hΔ (by norm_num)) v)
    (shellObjective_le_24 G hTF hΔ v)

/-! ### A sharper root-degree-three certificate inside a degree-four graph -/

/-- Dual weights for a root of degree at most three in an ambient graph of
    maximum degree four: `certY43 = (0,1,3,0,...)`. -/
def certY43 : ℕ → ℕ
  | 1 => 1
  | 2 => 3
  | _ => 0

lemma certY43_pair {p q : ℕ} (h : p + q ≤ 3) :
    2 * (p * q) ≤ certY43 p + certY43 q := by
  have hp : p ≤ 3 := by omega
  have hq : q ≤ 3 := by omega
  interval_cases p <;> interval_cases q <;> revert h <;> decide

lemma certY43_token (k : ℕ) : (4 - k) * certY43 k ≤ 3 * k := by
  match k with
  | 0 | 1 | 2 | 3 | 4 => decide
  | n + 5 => rw [show 4 - (n + 5) = 0 by omega]; simp

/-- A vertex of degree at most three in a triangle-free graph of ambient
    maximum degree four lies on at most thirteen pentagons.  The doubled shell
    objective is at most `3 * sum_x |A_x| <= 3 * 9 = 27`, hence its integral
    value is at most thirteen. -/
theorem pentagonCountAt_le_thirteen_of_vertexDegree_le_three
    (G : Flag emptyType) (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 4)
    (v : Fin G.size) (hv : vertexDegree G v ≤ 3) :
    pentagonCountAt G v ≤ 13 := by
  have hfiber := pentagonCountAt_le_sum hTF (le_trans hΔ (by norm_num)) v
  set T := ∑ p ∈ shellPairsLt G v,
    (attachSet G v p.1).card * (attachSet G v p.2).card with hT
  have hchain : 2 * T ≤ 27 := by
    have h1 : 2 * T
        ≤ ∑ p ∈ shellPairsLt G v, (certY43 (attachSet G v p.1).card
            + certY43 (attachSet G v p.2).card) := by
      rw [hT, Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      have hadj : G.graph.Adj p.1 p.2 := ((Finset.mem_filter.mp hp).2).2
      have hpair := attach_card_add_le_degree (v := v) hTF hadj
      exact certY43_pair (hpair.trans hv)
    have h2 : ∑ p ∈ shellPairsLt G v, (certY43 (attachSet G v p.1).card
            + certY43 (attachSet G v p.2).card)
        = ∑ x ∈ shellSet G v,
            ((shellSet G v).filter fun y => G.graph.Adj x y).card
              * certY43 (attachSet G v x).card := by
      rw [sum_pairsLt_endpoints v (fun u => certY43 (attachSet G v u).card),
        sum_pairsAdj_eq v (fun u => certY43 (attachSet G v u).card)]
    have h3 : ∑ x ∈ shellSet G v,
          ((shellSet G v).filter fun y => G.graph.Adj x y).card
            * certY43 (attachSet G v x).card
        ≤ ∑ x ∈ shellSet G v, 3 * (attachSet G v x).card := by
      refine Finset.sum_le_sum fun x _ => ?_
      have hbudget := shellDeg_add_attach_le4 hΔ v x
      calc
        ((shellSet G v).filter fun y => G.graph.Adj x y).card
              * certY43 (attachSet G v x).card
            ≤ (4 - (attachSet G v x).card)
              * certY43 (attachSet G v x).card :=
                Nat.mul_le_mul_right _ (by omega)
        _ ≤ 3 * (attachSet G v x).card := certY43_token _
    have h4 : ∑ x ∈ shellSet G v, 3 * (attachSet G v x).card ≤ 27 := by
      rw [← Finset.mul_sum]
      have hcap := sum_attach_card_le_three_mul_degree hΔ v
      omega
    omega
  omega

/-! ### The punctured root: pentagons through a neighbour that avoid the root

The neighbour layer needs `r_a`, the number of pentagons through `a ∈ N(v)` that do NOT
contain `v`.  The natural home for that count is the vertex-deleted graph `G - v`, which
does not exist for `Flag emptyType` and is not worth building.  Everything below instead
works inside `G` with the punctured predicate `v ∉ S`, erasing `v` from the attachment
sets by hand.  The bound `r_a ≤ 13` that comes out is exactly tight. -/

/-- `r_a ≤ T_a` **without** constructing the vertex-deleted graph `H = G - v`:
    pentagons through `a` that avoid a neighbour `v` of `a` are bounded by the
    shell objective of `a` computed with `v` erased from every attachment set.
    (`shellSet G a` already excludes `v`, since `v ∼ a`.) -/
theorem pentagonCountAt_avoid_le_sum (hTF : IsTriangleFree G) (v a : Fin G.size) :
    (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)).card
      ≤ ∑ p ∈ shellPairsLt G a,
          ((attachSet G a p.1).erase v).card * ((attachSet G a p.2).erase v).card := by
  have hmaps : Set.MapsTo (oppEdge G a)
      ↑(Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S))
      ↑(shellPairsLt G a) := by
    intro S hS
    rw [Finset.mem_coe, Finset.mem_filter] at hS
    obtain ⟨x', y', x, y, hlt, hadjxy, hxsh, hysh, -, -, hfil, -, -, -⟩ :=
      pentagon_decomp hTF hS.2.1 hS.2.2.1
    have hopp : oppEdge G a S = (x, y) := by
      rw [oppEdge, hfil, pickMin_pair hlt, pickMax_pair hlt]
    rw [hopp, Finset.mem_coe, shellPairsLt, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hxsh, hysh⟩, hlt, hadjxy⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (abPair G a p) ?_ ?_
  · intro S hS
    rw [Finset.mem_coe, Finset.mem_filter] at hS
    obtain ⟨hS1, hS2⟩ := hS
    rw [Finset.mem_filter] at hS1
    obtain ⟨c, d, x, y, hlt, -, -, -, hc, hd, hfil, hfa, hfb, hSeq⟩ :=
      pentagon_decomp hTF hS1.2.1 hS1.2.2.1
    have hopp : oppEdge G a S = (x, y) := by
      rw [oppEdge, hfil, pickMin_pair hlt, pickMax_pair hlt]
    have hpx : p.1 = x := by rw [← hS2, hopp]
    have hpy : p.2 = y := by rw [← hS2, hopp]
    have hcS : c ∈ S := by rw [hSeq]; simp
    have hdS : d ∈ S := by rw [hSeq]; simp
    have hcv : c ≠ v := fun h => hS1.2.2.2 (h ▸ hcS)
    have hdv : d ≠ v := fun h => hS1.2.2.2 (h ▸ hdS)
    rw [Finset.mem_coe, Finset.mem_product, abPair, hpx, hpy, hfa, hfb,
      pickMin_singleton, pickMin_singleton]
    exact ⟨Finset.mem_erase.mpr ⟨hcv, hc⟩, Finset.mem_erase.mpr ⟨hdv, hd⟩⟩
  · intro S1 hS1 S2 hS2 heq
    rw [Finset.mem_coe, Finset.mem_filter] at hS1 hS2
    obtain ⟨h1Pv, h1opp⟩ := hS1
    obtain ⟨h2Pv, h2opp⟩ := hS2
    rw [Finset.mem_filter] at h1Pv h2Pv
    obtain ⟨a1, b1, x1, y1, hlt1, -, -, -, -, -, hfil1, hfa1, hfb1, hSeq1⟩ :=
      pentagon_decomp hTF h1Pv.2.1 h1Pv.2.2.1
    obtain ⟨a2, b2, x2, y2, hlt2, -, -, -, -, -, hfil2, hfa2, hfb2, hSeq2⟩ :=
      pentagon_decomp hTF h2Pv.2.1 h2Pv.2.2.1
    have hopp1 : oppEdge G a S1 = (x1, y1) := by
      rw [oppEdge, hfil1, pickMin_pair hlt1, pickMax_pair hlt1]
    have hopp2 : oppEdge G a S2 = (x2, y2) := by
      rw [oppEdge, hfil2, pickMin_pair hlt2, pickMax_pair hlt2]
    have hx1 : p.1 = x1 := by rw [← h1opp, hopp1]
    have hy1 : p.2 = y1 := by rw [← h1opp, hopp1]
    have hx2 : p.1 = x2 := by rw [← h2opp, hopp2]
    have hy2 : p.2 = y2 := by rw [← h2opp, hopp2]
    have hab1 : abPair G a p S1 = (a1, b1) := by
      rw [abPair, hx1, hy1, hfa1, hfb1, pickMin_singleton, pickMin_singleton]
    have hab2 : abPair G a p S2 = (a2, b2) := by
      rw [abPair, hx2, hy2, hfa2, hfb2, pickMin_singleton, pickMin_singleton]
    rw [hab1, hab2, Prod.mk.injEq] at heq
    rw [hSeq1, hSeq2, heq.1, heq.2, ← hx1, ← hy1, ← hx2, ← hy2]



/-- The `r_a ≤ 13` pair budget, with `v` erased: on a shell edge of `a`, the two
    `v`-erased attachment sets fit in `N(a) \ {v}`, which has size ≤ 3. -/
lemma attach_erase_add_le_three (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 4)
    {a v x y : Fin G.size} (hav : G.graph.Adj a v) (hxy : G.graph.Adj x y) :
    ((attachSet G a x).erase v).card + ((attachSet G a y).erase v).card ≤ 3 := by
  have hdisj : Disjoint ((attachSet G a x).erase v) ((attachSet G a y).erase v) :=
    (attachSet_disjoint hTF hxy).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  rw [← Finset.card_union_of_disjoint hdisj]
  have hsub : ((attachSet G a x).erase v) ∪ ((attachSet G a y).erase v)
      ⊆ (Finset.univ.filter fun u => G.graph.Adj a u).erase v := by
    intro u hu
    rw [Finset.mem_union, Finset.mem_erase, Finset.mem_erase, attachSet, attachSet,
      Finset.mem_filter, Finset.mem_filter] at hu
    rw [Finset.mem_erase, Finset.mem_filter]
    rcases hu with h | h
    · exact ⟨h.1, Finset.mem_univ u, h.2.2.1⟩
    · exact ⟨h.1, Finset.mem_univ u, h.2.2.1⟩
  have hvmem : v ∈ Finset.univ.filter fun u => G.graph.Adj a u := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ v, hav⟩
  calc (((attachSet G a x).erase v) ∪ ((attachSet G a y).erase v)).card
      ≤ ((Finset.univ.filter fun u => G.graph.Adj a u).erase v).card :=
        Finset.card_le_card hsub
    _ = (Finset.univ.filter fun u => G.graph.Adj a u).card - 1 :=
        Finset.card_erase_of_mem hvmem
    _ ≤ 3 := by have := deg_le_of_maxDegree_le hΔ a; omega



/-- **Double counting the `v`-erased shell attachment.**  Summing `|A_x \ {v}|` over the
    second shell of `a` is the same as counting, for each neighbour `b ≠ v` of `a`, how
    many shell vertices are adjacent to `b`. -/
lemma sum_attach_erase_card_swap (a v : Fin G.size) :
    ∑ x ∈ shellSet G a, ((attachSet G a x).erase v).card
      = ∑ b ∈ (Finset.univ.filter (fun b => G.graph.Adj a b)).erase v,
          ((shellSet G a).filter fun x => G.graph.Adj x b).card := by
  have hset : ∀ x : Fin G.size, (attachSet G a x).erase v
      = Finset.univ.filter (fun u => (G.graph.Adj a u ∧ G.graph.Adj x u) ∧ u ≠ v) := by
    intro x
    ext u
    simp only [Finset.mem_erase, attachSet, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hR : (Finset.univ.filter (fun b => G.graph.Adj a b)).erase v
      = Finset.univ.filter (fun b => G.graph.Adj a b ∧ b ≠ v) := by
    ext b
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [hR]
  simp only [hset, Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : G.graph.Adj a b
  · by_cases hbv : b = v <;> simp [hab, hbv]
  · simp [hab]

/-- **Erased capacity.**  With one neighbour `v` of the root `a` deleted, the total shell
    attachment drops to at most `3 · (deg(a) − 1) ≤ 3 · 3 = 9`. -/
lemma sum_attach_erase_card_le_nine (hΔ : maxDegree G ≤ 4) {a v : Fin G.size}
    (hav : G.graph.Adj a v) :
    ∑ x ∈ shellSet G a, ((attachSet G a x).erase v).card ≤ 9 := by
  rw [sum_attach_erase_card_swap]
  have hbound : ∀ b ∈ (Finset.univ.filter (fun b => G.graph.Adj a b)).erase v,
      ((shellSet G a).filter fun x => G.graph.Adj x b).card ≤ 3 := by
    intro b hb
    rw [Finset.mem_erase, Finset.mem_filter] at hb
    have hab : G.graph.Adj a b := hb.2.2
    have hsub : (shellSet G a).filter (fun x => G.graph.Adj x b)
        ⊆ (Finset.univ.filter fun w => G.graph.Adj b w).erase a := by
      intro x hx
      rw [Finset.mem_filter, shellSet, Finset.mem_filter] at hx
      rw [Finset.mem_erase, Finset.mem_filter]
      exact ⟨hx.1.2.1, Finset.mem_univ x, hx.2.symm⟩
    have hamem : a ∈ Finset.univ.filter fun w => G.graph.Adj b w := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ a, hab.symm⟩
    calc ((shellSet G a).filter fun x => G.graph.Adj x b).card
        ≤ ((Finset.univ.filter fun w => G.graph.Adj b w).erase a).card :=
          Finset.card_le_card hsub
      _ = (Finset.univ.filter fun w => G.graph.Adj b w).card - 1 :=
          Finset.card_erase_of_mem hamem
      _ ≤ 3 := by have := deg_le_of_maxDegree_le hΔ b; omega
  have hvmem : v ∈ Finset.univ.filter fun b => G.graph.Adj a b := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ v, hav⟩
  have hcard : ((Finset.univ.filter (fun b => G.graph.Adj a b)).erase v).card ≤ 3 := by
    rw [Finset.card_erase_of_mem hvmem]
    have := deg_le_of_maxDegree_le hΔ a
    omega
  calc ∑ b ∈ (Finset.univ.filter (fun b => G.graph.Adj a b)).erase v,
        ((shellSet G a).filter fun x => G.graph.Adj x b).card
      ≤ ∑ _b ∈ (Finset.univ.filter (fun b => G.graph.Adj a b)).erase v, 3 :=
        Finset.sum_le_sum hbound
    _ = ((Finset.univ.filter (fun b => G.graph.Adj a b)).erase v).card * 3 := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 9 := by omega

/-- **`r_a ≤ 13`.**  In a triangle-free graph of maximum degree at most four, a vertex `a`
    lies on at most thirteen pentagons that avoid a given neighbour `v` of `a`.
    Same `certY43` chain as `pentagonCountAt_le_thirteen_of_vertexDegree_le_three`, run
    with `v` erased from every attachment set: the doubled shell objective is at most
    `3 · Σ_x |A_x \ {v}| ≤ 3 · 9 = 27`. -/
theorem pentagonCountAt_avoid_le_thirteen (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 4)
    {a v : Fin G.size} (hav : G.graph.Adj a v) :
    (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)).card ≤ 13 := by
  have hfiber := pentagonCountAt_avoid_le_sum hTF v a
  set T := ∑ p ∈ shellPairsLt G a,
    ((attachSet G a p.1).erase v).card * ((attachSet G a p.2).erase v).card with hT
  have hchain : 2 * T ≤ 27 := by
    have h1 : 2 * T
        ≤ ∑ p ∈ shellPairsLt G a, (certY43 ((attachSet G a p.1).erase v).card
            + certY43 ((attachSet G a p.2).erase v).card) := by
      rw [hT, Finset.mul_sum]
      refine Finset.sum_le_sum fun p hp => ?_
      have hadj : G.graph.Adj p.1 p.2 := ((Finset.mem_filter.mp hp).2).2
      exact certY43_pair (attach_erase_add_le_three hTF hΔ hav hadj)
    have h2 : ∑ p ∈ shellPairsLt G a, (certY43 ((attachSet G a p.1).erase v).card
            + certY43 ((attachSet G a p.2).erase v).card)
        = ∑ x ∈ shellSet G a,
            ((shellSet G a).filter fun y => G.graph.Adj x y).card
              * certY43 ((attachSet G a x).erase v).card := by
      rw [sum_pairsLt_endpoints a (fun u => certY43 ((attachSet G a u).erase v).card),
        sum_pairsAdj_eq a (fun u => certY43 ((attachSet G a u).erase v).card)]
    have h3 : ∑ x ∈ shellSet G a,
          ((shellSet G a).filter fun y => G.graph.Adj x y).card
            * certY43 ((attachSet G a x).erase v).card
        ≤ ∑ x ∈ shellSet G a, 3 * ((attachSet G a x).erase v).card := by
      refine Finset.sum_le_sum fun x _ => ?_
      have hbudget := shellDeg_add_attach_le4 hΔ a x
      have herase : ((attachSet G a x).erase v).card ≤ (attachSet G a x).card :=
        Finset.card_erase_le
      calc
        ((shellSet G a).filter fun y => G.graph.Adj x y).card
              * certY43 ((attachSet G a x).erase v).card
            ≤ (4 - ((attachSet G a x).erase v).card)
              * certY43 ((attachSet G a x).erase v).card :=
                Nat.mul_le_mul_right _ (by omega)
        _ ≤ 3 * ((attachSet G a x).erase v).card := certY43_token _
    have h4 : ∑ x ∈ shellSet G a, 3 * ((attachSet G a x).erase v).card ≤ 27 := by
      rw [← Finset.mul_sum]
      have hcap := sum_attach_erase_card_le_nine hΔ hav
      omega
    omega
  omega

/-! ### The shell T-identity

An exact, subtraction-free identity for the shell objective `T = Σ_{xy ∈ E} k_x k_y` at a
root of a triangle-free 4-regular graph.  Writing `S⁺` for the shell vertices of positive
weight, `u_x` for the slack `4 - k_x - d_{F⁺}(x)`, and `e₂₂` for the number of shell edges
with both endpoint weights equal to two,

  `2T + 4·n₃ + 12·n₄ + Σ_{x ∈ S⁺} (2k_x - 1)·u_x = 36 + 2·e₂₂`,

which is the Nat-safe form of `T = 18 + e₂₂ - 2n₃ - 6n₄ - ½ Σ (2k_x - 1) u_x`.

Two ingredients do the work.  Per shell edge, `2pq = (2p-1) + (2q-1) + 2·[p=q=2]` whenever
`p, q ≥ 1` and `p + q ≤ 4` — which is why the positive-weight restriction `S⁺` is needed.
Per shell vertex, `(4-k)(2k-1) + 4·[k=3] + 12·[k=4] = 3k` for `1 ≤ k ≤ 4`, so summing
against saturation `Σ k_x = 12` gives the constant `36`.

This is leverage rather than decoration: it is what makes the high-root search space
finite and small, and it exhibits the extremal shape behind `T ≤ 24`. -/

/-! ### Generic pair sets over an arbitrary vertex set -/

/-- Ordered adjacent pairs `(x,y)` with `x < y` drawn from a vertex set `S`. -/
noncomputable def pairsLtOn (G : Flag emptyType) (S : Finset (Fin G.size)) :
    Finset (Fin G.size × Fin G.size) :=
  (S ×ˢ S).filter fun p => p.1 < p.2 ∧ G.graph.Adj p.1 p.2

/-- Ordered adjacent pairs drawn from a vertex set `S`, both orientations. -/
noncomputable def pairsAdjOn (G : Flag emptyType) (S : Finset (Fin G.size)) :
    Finset (Fin G.size × Fin G.size) :=
  (S ×ˢ S).filter fun p => G.graph.Adj p.1 p.2

lemma pairsLtOn_shellSet (v : Fin G.size) :
    pairsLtOn G (shellSet G v) = shellPairsLt G v := rfl

lemma pairsAdjOn_shellSet (v : Fin G.size) :
    pairsAdjOn G (shellSet G v) = shellPairsAdj G v := rfl

/-- Generic form of `sum_pairsLt_endpoints`. -/
lemma sum_pairsLtOn_endpoints (S : Finset (Fin G.size)) (f : Fin G.size → ℕ) :
    ∑ p ∈ pairsLtOn G S, (f p.1 + f p.2) = ∑ q ∈ pairsAdjOn G S, f q.1 := by
  have hsplit : pairsAdjOn G S = pairsLtOn G S ∪ (pairsLtOn G S).image Prod.swap := by
    ext q
    simp only [pairsAdjOn, pairsLtOn, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨h1, h2⟩, hadj⟩
      rcases lt_trichotomy q.1 q.2 with hlt | heq | hgt
      · exact Or.inl ⟨⟨h1, h2⟩, hlt, hadj⟩
      · exact absurd heq (G.graph.ne_of_adj hadj)
      · exact Or.inr ⟨(q.2, q.1), ⟨⟨h2, h1⟩, hgt, hadj.symm⟩, rfl⟩
    · rintro (⟨⟨h1, h2⟩, _, hadj⟩ | ⟨p, ⟨⟨h1, h2⟩, _, hadj⟩, rfl⟩)
      · exact ⟨⟨h1, h2⟩, hadj⟩
      · exact ⟨⟨h2, h1⟩, hadj.symm⟩
  have hdisj : Disjoint (pairsLtOn G S) ((pairsLtOn G S).image Prod.swap) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp'
    rw [pairsLtOn, Finset.mem_filter] at hp hq
    have h1 : q.1 < q.2 := hq.2.1
    have h2 : q.2 < q.1 := by simpa using hp.2.1
    exact absurd h1 (lt_asymm h2)
  rw [hsplit, Finset.sum_union hdisj,
    Finset.sum_image (fun p _ q _ h => Prod.swap_injective h),
    Finset.sum_add_distrib]
  rfl

/-- Generic form of `sum_pairsAdj_eq`. -/
lemma sum_pairsAdjOn_eq (S : Finset (Fin G.size)) (f : Fin G.size → ℕ) :
    ∑ q ∈ pairsAdjOn G S, f q.1
      = ∑ x ∈ S, (S.filter fun y => G.graph.Adj x y).card * f x := by
  rw [pairsAdjOn, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_filter]
  change (∑ _a ∈ S.filter fun a => G.graph.Adj x a, f x)
      = (S.filter fun y => G.graph.Adj x y).card * f x
  rw [Finset.sum_const, smul_eq_mul]

/-! ### The positive shell `S⁺`, its degrees, its slack, and `e₂₂` -/

/-- `S⁺`: shell vertices carrying at least one attachment. -/
noncomputable def shellPos (G : Flag emptyType) (v : Fin G.size) : Finset (Fin G.size) :=
  (shellSet G v).filter fun x => 1 ≤ (attachSet G v x).card

/-- `d_{F⁺}(x)`: the number of `S⁺`-neighbours of `x`. -/
noncomputable def shellPosDeg (G : Flag emptyType) (v x : Fin G.size) : ℕ :=
  ((shellPos G v).filter fun y => G.graph.Adj x y).card

/-- `u_x`: the unused part of the degree-4 budget of `x` after attachments and
    `S⁺`-neighbours are paid for. -/
noncomputable def shellSlack (G : Flag emptyType) (v x : Fin G.size) : ℕ :=
  4 - (attachSet G v x).card - shellPosDeg G v x

/-- `e₂₂`: the number of shell edges both of whose endpoints have attachment 2. -/
noncomputable def e22 (G : Flag emptyType) (v : Fin G.size) : ℕ :=
  ((shellPairsLt G v).filter fun p =>
    (attachSet G v p.1).card = 2 ∧ (attachSet G v p.2).card = 2).card

lemma shellPos_subset (v : Fin G.size) : shellPos G v ⊆ shellSet G v :=
  Finset.filter_subset _ _

lemma mem_shellPos {v x : Fin G.size} :
    x ∈ shellPos G v ↔ x ∈ shellSet G v ∧ 1 ≤ (attachSet G v x).card := by
  rw [shellPos, Finset.mem_filter]

/-! ### Step A: the per-edge identity -/

/-- **Step A.**  For positive attachment weights inside the Δ = 4 budget the
    doubled product splits exactly into the two token weights `2k-1`, with a
    correction of `2` exactly on the `(2,2)` edges. -/
lemma two_mul_prod_split {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p + q ≤ 4) :
    2 * (p * q)
      = (2 * p - 1) + (2 * q - 1) + 2 * (if p = 2 ∧ q = 2 then 1 else 0) := by
  have hp4 : p ≤ 4 := by omega
  have hq4 : q ≤ 4 := by omega
  interval_cases p <;> interval_cases q <;> revert hpq <;> decide

/-! ### Step E: the weight-class identity -/

/-- **Step E.**  Pointwise, `(4-k)(2k-1) + 4·[k=3] + 12·[k=4] = 3k` for `1 ≤ k ≤ 4`. -/
lemma weight_class_identity {k : ℕ} (hk : 1 ≤ k) (hk4 : k ≤ 4) :
    (4 - k) * (2 * k - 1) + 4 * (if k = 3 then 1 else 0)
        + 12 * (if k = 4 then 1 else 0) = 3 * k := by
  interval_cases k <;> decide

/-! ### Step B: restricting `T` to `S⁺` -/

/-- **Step B.**  Shell edges with a zero-weight endpoint contribute nothing to `T`. -/
lemma sum_T_restrict (v : Fin G.size) :
    ∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card
      = ∑ p ∈ pairsLtOn G (shellPos G v),
          (attachSet G v p.1).card * (attachSet G v p.2).card := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro p hp
    rw [pairsLtOn, Finset.mem_filter, Finset.mem_product] at hp
    rw [← pairsLtOn_shellSet, pairsLtOn, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨shellPos_subset v hp.1.1, shellPos_subset v hp.1.2⟩, hp.2⟩
  · intro p hp hnot
    rw [← pairsLtOn_shellSet, pairsLtOn, Finset.mem_filter, Finset.mem_product] at hp
    by_cases h1 : 1 ≤ (attachSet G v p.1).card
    · by_cases h2 : 1 ≤ (attachSet G v p.2).card
      · exfalso
        refine hnot ?_
        rw [pairsLtOn, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨mem_shellPos.mpr ⟨hp.1.1, h1⟩, mem_shellPos.mpr ⟨hp.1.2, h2⟩⟩, hp.2⟩
      · have : (attachSet G v p.2).card = 0 := by omega
        rw [this, Nat.mul_zero]
    · have : (attachSet G v p.1).card = 0 := by omega
      rw [this, Nat.zero_mul]

/-- The `(2,2)` shell edges all live inside `S⁺`. -/
lemma e22_eq_pos (v : Fin G.size) :
    ((pairsLtOn G (shellPos G v)).filter fun p =>
        (attachSet G v p.1).card = 2 ∧ (attachSet G v p.2).card = 2).card = e22 G v := by
  rw [e22]
  congr 1
  ext p
  rw [Finset.mem_filter, Finset.mem_filter, ← pairsLtOn_shellSet, pairsLtOn, pairsLtOn,
    Finset.mem_filter, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨hm1, hm2⟩, hlt⟩, hc⟩
    exact ⟨⟨⟨shellPos_subset v hm1, shellPos_subset v hm2⟩, hlt⟩, hc⟩
  · rintro ⟨⟨⟨hm1, hm2⟩, hlt⟩, hc⟩
    refine ⟨⟨⟨mem_shellPos.mpr ⟨hm1, ?_⟩, mem_shellPos.mpr ⟨hm2, ?_⟩⟩, hlt⟩, hc⟩
    · omega
    · omega

/-! ### Step C: exchanging the edge sum for a vertex sum -/

/-- **Steps A + B + C.**  `2T` as a vertex sum over `S⁺` plus the `(2,2)` correction. -/
lemma two_mul_T_eq (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 4) (v : Fin G.size) :
    2 * (∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card)
      = (∑ x ∈ shellPos G v,
            shellPosDeg G v x * (2 * (attachSet G v x).card - 1)) + 2 * e22 G v := by
  rw [sum_T_restrict v, Finset.mul_sum]
  have hpt : ∀ p ∈ pairsLtOn G (shellPos G v),
      2 * ((attachSet G v p.1).card * (attachSet G v p.2).card)
        = ((2 * (attachSet G v p.1).card - 1) + (2 * (attachSet G v p.2).card - 1))
            + 2 * (if (attachSet G v p.1).card = 2 ∧ (attachSet G v p.2).card = 2
                   then 1 else 0) := by
    intro p hp
    rw [pairsLtOn, Finset.mem_filter, Finset.mem_product] at hp
    have h1 : 1 ≤ (attachSet G v p.1).card := (mem_shellPos.mp hp.1.1).2
    have h2 : 1 ≤ (attachSet G v p.2).card := (mem_shellPos.mp hp.1.2).2
    have hsum : (attachSet G v p.1).card + (attachSet G v p.2).card ≤ 4 :=
      attach_card_add_le4 hTF hΔ hp.2.2
    exact two_mul_prod_split h1 h2 hsum
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib,
    sum_pairsLtOn_endpoints (shellPos G v) (fun u => 2 * (attachSet G v u).card - 1),
    sum_pairsAdjOn_eq (shellPos G v) (fun u => 2 * (attachSet G v u).card - 1),
    ← Finset.mul_sum, ← Finset.card_filter, e22_eq_pos v]
  rfl

/-! ### Step D: substituting the slack -/

/-- `S⁺`-degree and attachment count fit in the Δ = 4 budget. -/
lemma shellPosDeg_add_attach_le4 (hΔ : maxDegree G ≤ 4) (v x : Fin G.size) :
    (attachSet G v x).card + shellPosDeg G v x ≤ 4 := by
  have h1 : shellPosDeg G v x ≤ ((shellSet G v).filter fun y => G.graph.Adj x y).card := by
    rw [shellPosDeg]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (shellPos_subset v))
  have h2 := shellDeg_add_attach_le4 hΔ v x
  omega

/-- **Step D.**  The box condition, subtraction-free. -/
lemma shellPosDeg_add_slack_add_attach (hΔ : maxDegree G ≤ 4) (v x : Fin G.size) :
    shellPosDeg G v x + shellSlack G v x + (attachSet G v x).card = 4 := by
  have := shellPosDeg_add_attach_le4 hΔ v x
  rw [shellSlack]
  omega

/-! ### Saturation on `S⁺` -/

/-- Saturation, restricted to `S⁺` (the discarded shell vertices carry weight 0). -/
lemma sum_attach_shellPos_eq_twelve (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size) :
    ∑ x ∈ shellPos G v, (attachSet G v x).card = 12 := by
  rw [← sum_attach_card_eq_twelve hTF hReg hdeg v]
  refine Finset.sum_subset (shellPos_subset v) ?_
  intro x hx hnot
  by_contra hne
  exact hnot (mem_shellPos.mpr ⟨hx, by omega⟩)

/-! ### The identity -/

/-- **The shell T-identity at a root of a triangle-free 4-regular graph.** -/
theorem shellObjective_identity (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size) :
    2 * (∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card)
        + 4 * ((shellPos G v).filter fun x => (attachSet G v x).card = 3).card
        + 12 * ((shellPos G v).filter fun x => (attachSet G v x).card = 4).card
        + ∑ x ∈ shellPos G v, (2 * (attachSet G v x).card - 1) * shellSlack G v x
      = 36 + 2 * e22 G v := by
  have hΔ : maxDegree G ≤ 4 := le_of_eq hdeg
  rw [two_mul_T_eq hTF hΔ v, Finset.card_filter, Finset.card_filter,
    Finset.mul_sum, Finset.mul_sum]
  have hmain : (∑ x ∈ shellPos G v,
          shellPosDeg G v x * (2 * (attachSet G v x).card - 1))
      + (∑ x ∈ shellPos G v, 4 * (if (attachSet G v x).card = 3 then 1 else 0))
      + (∑ x ∈ shellPos G v, 12 * (if (attachSet G v x).card = 4 then 1 else 0))
      + (∑ x ∈ shellPos G v, (2 * (attachSet G v x).card - 1) * shellSlack G v x)
      = 36 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have hpt : ∀ x ∈ shellPos G v,
        shellPosDeg G v x * (2 * (attachSet G v x).card - 1)
          + 4 * (if (attachSet G v x).card = 3 then 1 else 0)
          + 12 * (if (attachSet G v x).card = 4 then 1 else 0)
          + (2 * (attachSet G v x).card - 1) * shellSlack G v x
        = 3 * (attachSet G v x).card := by
      intro x hx
      have h1 : 1 ≤ (attachSet G v x).card := (mem_shellPos.mp hx).2
      have h4 : (attachSet G v x).card ≤ 4 := by
        have := shellDeg_add_attach_le4 hΔ v x; omega
      have hbox := shellPosDeg_add_slack_add_attach hΔ v x
      have hE := weight_class_identity h1 h4
      have hdu : shellPosDeg G v x + shellSlack G v x = 4 - (attachSet G v x).card := by
        omega
      set m := 2 * (attachSet G v x).card - 1 with hm
      have key : shellPosDeg G v x * m + m * shellSlack G v x
          = (4 - (attachSet G v x).card) * m := by
        rw [Nat.mul_comm m (shellSlack G v x), ← Nat.add_mul, hdu]
      calc shellPosDeg G v x * m
              + 4 * (if (attachSet G v x).card = 3 then 1 else 0)
              + 12 * (if (attachSet G v x).card = 4 then 1 else 0)
              + m * shellSlack G v x
          = (shellPosDeg G v x * m + m * shellSlack G v x)
              + 4 * (if (attachSet G v x).card = 3 then 1 else 0)
              + 12 * (if (attachSet G v x).card = 4 then 1 else 0) := by ring
        _ = (4 - (attachSet G v x).card) * m
              + 4 * (if (attachSet G v x).card = 3 then 1 else 0)
              + 12 * (if (attachSet G v x).card = 4 then 1 else 0) := by rw [key]
        _ = 3 * (attachSet G v x).card := hE
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum,
      sum_attach_shellPos_eq_twelve hTF hReg hdeg v]
    norm_num
  omega

/-! ### Corollary: `T ≤ 24` -/

/-- Weight-2 shell vertices. -/
noncomputable def shellTwo (G : Flag emptyType) (v : Fin G.size) : Finset (Fin G.size) :=
  (shellSet G v).filter fun x => (attachSet G v x).card = 2

lemma e22_eq_card_pairsLtOn_shellTwo (v : Fin G.size) :
    e22 G v = (pairsLtOn G (shellTwo G v)).card := by
  rw [e22]
  congr 1
  ext p
  rw [Finset.mem_filter, ← pairsLtOn_shellSet, pairsLtOn, pairsLtOn, Finset.mem_filter,
    Finset.mem_filter, Finset.mem_product, Finset.mem_product, shellTwo,
    Finset.mem_filter, Finset.mem_filter]
  tauto

lemma card_shellTwo_le_six (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size) : (shellTwo G v).card ≤ 6 := by
  have hsub : shellTwo G v ⊆ shellSet G v := Finset.filter_subset _ _
  have hle : ∑ x ∈ shellTwo G v, (attachSet G v x).card
      ≤ ∑ x ∈ shellSet G v, (attachSet G v x).card :=
    Finset.sum_le_sum_of_subset hsub
  have hcell : ∀ x ∈ shellTwo G v, (attachSet G v x).card = 2 := by
    intro x hx
    rw [shellTwo, Finset.mem_filter] at hx
    exact hx.2
  have heq : ∑ x ∈ shellTwo G v, (attachSet G v x).card = 2 * (shellTwo G v).card := by
    rw [Finset.sum_congr rfl hcell, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  rw [sum_attach_card_eq_twelve hTF hReg hdeg v] at hle
  omega

lemma two_mul_e22_le (hΔ : maxDegree G ≤ 4) (v : Fin G.size) :
    2 * e22 G v ≤ 2 * (shellTwo G v).card := by
  have hhand : ∑ p ∈ pairsLtOn G (shellTwo G v), ((1 : ℕ) + 1)
      = ∑ x ∈ shellTwo G v, ((shellTwo G v).filter fun y => G.graph.Adj x y).card * 1 := by
    rw [sum_pairsLtOn_endpoints (shellTwo G v) (fun _ => (1 : ℕ)),
      sum_pairsAdjOn_eq (shellTwo G v) (fun _ => (1 : ℕ))]
  have hL : ∑ p ∈ pairsLtOn G (shellTwo G v), ((1 : ℕ) + 1)
      = 2 * (pairsLtOn G (shellTwo G v)).card := by
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hdeg2 : ∀ x ∈ shellTwo G v,
      ((shellTwo G v).filter fun y => G.graph.Adj x y).card * 1 ≤ 2 := by
    intro x hx
    rw [shellTwo, Finset.mem_filter] at hx
    have hsub : ((shellSet G v).filter fun y => G.graph.Adj x y).card
        ≤ 4 - (attachSet G v x).card := by
      have := shellDeg_add_attach_le4 hΔ v x; omega
    have h1 : ((shellTwo G v).filter fun y => G.graph.Adj x y).card
        ≤ ((shellSet G v).filter fun y => G.graph.Adj x y).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
    rw [hx.2] at hsub
    omega
  have hR : ∑ x ∈ shellTwo G v, ((shellTwo G v).filter fun y => G.graph.Adj x y).card * 1
      ≤ ∑ _x ∈ shellTwo G v, 2 := Finset.sum_le_sum hdeg2
  rw [Finset.sum_const, smul_eq_mul] at hR
  rw [e22_eq_card_pairsLtOn_shellTwo v]
  omega

/-- At most six shell vertices carry weight two, since each contributes `2` to a total
    attachment of `12`; and the weight-2 vertices span a subgraph of maximum degree at most
    `4 - 2 = 2`, so it has at most as many edges as vertices.  Hence `e₂₂ ≤ 6`.

    This is the bound that makes the high-root enumeration finite: combined with the
    identity it pins the shell objective to `T ≤ 18 + e₂₂ ≤ 24`. -/
theorem e22_le_six (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size) : e22 G v ≤ 6 := by
  have h1 := two_mul_e22_le (le_of_eq hdeg) v
  have h2 := card_shellTwo_le_six hTF hReg hdeg v
  omega

/-- **Corollary of the identity: `T ≤ 24` on a regular root.**

    Note this is *not* a strengthening: `shellObjective_le_24` below proves the same bound
    from the `certY4` certificate under strictly weaker hypotheses (no regularity).  What
    this version adds is a second, independent route — via `e₂₂ ≤ 6` — which also exhibits
    the extremal shape, since equality forces `e₂₂ = 6` and six weight-2 vertices.  The
    census confirms that: `T = 24` occurs exactly once among the 18,703 triangle-free
    4-regular graphs of order at most 16, at the 11-vertex graph `g24Flag` already in
    `PentagonDelta4Witness.lean`, with `e₂₂ = 6`. -/
theorem shellObjective_le_24_of_regular (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size) :
    ∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card ≤ 24 := by
  have hid := shellObjective_identity hTF hReg hdeg v
  have h := e22_le_six hTF hReg hdeg v
  omega

/-! ### The neighbour layer: (F4) and the defect budget at a root neighbour

The transport row needs more than the root's own shell: it needs, for each neighbour `a` of
the root `v`, the defect `D_a = 27 - 2 T_a` of `a`'s own shell computed in `G - v`.  As
elsewhere in this file the vertex-deleted graph is avoided — everything is expressed with
attachment sets punctured at `v`.  That costs nothing here, because `shellSet G a` already
excludes `v` (they are adjacent).

Two facts make up the layer.  **Saturation at `a`**: the three letters of `B_a = N(a) \ {v}`
each attach to exactly three shell vertices of `a`, so the punctured attachment totals `9`,
whence the `27`.  **(F4)**: on a punctured shell edge the weights are `(1,1)` or `(1,2)`,
where the `certY43` inequality holds *with equality*, so

  `Σ_{z ∈ S_a⁺} d_{J_a}(z)·c(k_a(z)) = 2 T_a`

exactly, not merely `≤`.  Combining the two with the token inequality gives `2 T_a ≤ 27`,
the sharp form of the punctured pentagon budget.

This is the first half of Stage 3 of the sharp Δ = 4 route.  The second half —
conservativity, `D^vis ≤ D` — is not attempted here. -/

/-- `k_a(z)`: the attachment set of `z` at the neighbour `a`, punctured at the root `v`. -/
noncomputable def avoidAttach (G : Flag emptyType) (a v z : Fin G.size) : Finset (Fin G.size) :=
  (attachSet G a z).erase v

/-- `S_a⁺`: the shell of `a` restricted to positive punctured weight. -/
noncomputable def shellPosAvoid (G : Flag emptyType) (a v : Fin G.size) : Finset (Fin G.size) :=
  (shellSet G a).filter fun z => 1 ≤ (avoidAttach G a v z).card

/-- `d_{J_a}(z)`: degree of `z` inside `S_a⁺`. -/
noncomputable def avoidPosDeg (G : Flag emptyType) (a v z : Fin G.size) : ℕ :=
  ((shellPosAvoid G a v).filter fun y => G.graph.Adj z y).card

/-- `T_a`: the punctured shell objective at `a`. -/
noncomputable def avoidObjective (G : Flag emptyType) (a v : Fin G.size) : ℕ :=
  ∑ p ∈ pairsLtOn G (shellPosAvoid G a v),
    (avoidAttach G a v p.1).card * (avoidAttach G a v p.2).card

lemma mem_shellPosAvoid {a v z : Fin G.size} :
    z ∈ shellPosAvoid G a v ↔ z ∈ shellSet G a ∧ 1 ≤ (avoidAttach G a v z).card := by
  rw [shellPosAvoid, Finset.mem_filter]

lemma shellPosAvoid_subset (a v : Fin G.size) : shellPosAvoid G a v ⊆ shellSet G a :=
  Finset.filter_subset _ _

/-- **The certificate is EXACT on a punctured shell edge.**  The weights there are `(1,1)`
    or `(1,2)`, where `2pq = certY43 p + certY43 q` holds with equality. -/
lemma certY43_pair_eq {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p + q ≤ 3) :
    2 * (p * q) = certY43 p + certY43 q := by
  have hp3 : p ≤ 3 := by omega
  have hq3 : q ≤ 3 := by omega
  interval_cases p <;> interval_cases q <;> revert hpq <;> decide

/-- **(F4).**  `Σ_z d_{J_a}(z)·c(k_a(z)) = 2 T_a`. -/
theorem avoid_F4_identity (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 4)
    {a v : Fin G.size} (hav : G.graph.Adj a v) :
    ∑ z ∈ shellPosAvoid G a v,
        avoidPosDeg G a v z * certY43 (avoidAttach G a v z).card
      = 2 * avoidObjective G a v := by
  rw [avoidObjective, Finset.mul_sum]
  have hpt : ∀ p ∈ pairsLtOn G (shellPosAvoid G a v),
      2 * ((avoidAttach G a v p.1).card * (avoidAttach G a v p.2).card)
        = certY43 (avoidAttach G a v p.1).card + certY43 (avoidAttach G a v p.2).card := by
    intro p hp
    rw [pairsLtOn, Finset.mem_filter, Finset.mem_product] at hp
    have h1 : 1 ≤ (avoidAttach G a v p.1).card := (mem_shellPosAvoid.mp hp.1.1).2
    have h2 : 1 ≤ (avoidAttach G a v p.2).card := (mem_shellPosAvoid.mp hp.1.2).2
    have hsum : (avoidAttach G a v p.1).card + (avoidAttach G a v p.2).card ≤ 3 :=
      attach_erase_add_le_three hTF hΔ hav hp.2.2
    exact certY43_pair_eq h1 h2 hsum
  rw [Finset.sum_congr rfl hpt,
    sum_pairsLtOn_endpoints (shellPosAvoid G a v)
      (fun u => certY43 (avoidAttach G a v u).card),
    sum_pairsAdjOn_eq (shellPosAvoid G a v)
      (fun u => certY43 (avoidAttach G a v u).card)]
  rfl

/-- The `S_a⁺`-degree and the punctured attachment count are disjoint parts of `N(z)`:
    one sees vertices non-adjacent to `a`, the other vertices adjacent to `a`. -/
lemma avoidPosDeg_add_avoidAttach_le4 (hΔ : maxDegree G ≤ 4) (a v z : Fin G.size) :
    avoidPosDeg G a v z + (avoidAttach G a v z).card ≤ 4 := by
  have hbudget := shellDeg_add_attach_le4 hΔ a z
  have h1 : avoidPosDeg G a v z ≤ ((shellSet G a).filter fun y => G.graph.Adj z y).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ (shellPosAvoid_subset a v))
  have h2 : (avoidAttach G a v z).card ≤ (attachSet G a z).card :=
    Finset.card_erase_le
  omega

/-- **Saturation at a neighbour.**  Each of the three letters of `B_a = N(a) \ {v}` is
    attached to exactly three shell vertices of `a`, so the punctured attachment over the
    shell of `a` totals `9`.  This is the `27` of the defect identity, divided by three. -/
theorem sum_avoidAttach_eq_nine (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) {a v : Fin G.size} (hav : G.graph.Adj a v) :
    ∑ z ∈ shellSet G a, (avoidAttach G a v z).card = 9 := by
  have hswap := sum_attach_erase_card_swap a v
  simp only [avoidAttach]
  rw [hswap]
  have hcell : ∀ b ∈ (Finset.univ.filter fun b => G.graph.Adj a b).erase v,
      ((shellSet G a).filter fun x => G.graph.Adj x b).card = 3 := by
    intro b hb
    rw [Finset.mem_erase, Finset.mem_filter] at hb
    rw [← filter_mem_attachSet_eq hb.2.2]
    exact attach_multiplicity_eq_three hTF hReg hdeg hb.2.2
  rw [Finset.sum_congr rfl hcell, Finset.sum_const, smul_eq_mul]
  have hvmem : v ∈ Finset.univ.filter fun b => G.graph.Adj a b := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ v, hav⟩
  rw [Finset.card_erase_of_mem hvmem, hReg a, hdeg]

/-- The same sum restricted to `S_a⁺`; the discarded terms are zero. -/
theorem sum_avoidAttach_shellPos_eq_nine (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) {a v : Fin G.size} (hav : G.graph.Adj a v) :
    ∑ z ∈ shellPosAvoid G a v, (avoidAttach G a v z).card = 9 := by
  rw [← sum_avoidAttach_eq_nine hTF hReg hdeg hav]
  refine Finset.sum_subset (shellPosAvoid_subset a v) ?_
  intro z hz hnot
  by_cases h : 1 ≤ (avoidAttach G a v z).card
  · exact absurd (mem_shellPosAvoid.mpr ⟨hz, h⟩) hnot
  · omega

/-- **Conservativity, the unseen-vertex case (Prop. `prop:cons`, third bullet).**  For every
    shell vertex `z` of a neighbour `a`, the defect term `3 k_a(z) - d_{J_a}(z)·c(k_a(z))` is
    non-negative — stated subtraction-free as `d_{J_a}(z)·c(k_a(z)) ≤ 3 k_a(z)`.

    The reason is that `k_a(z)` and `d_{J_a}(z)` count *disjoint* parts of `N(z)`: the former
    sees vertices adjacent to `a`, the latter vertices non-adjacent to `a`.  So
    `d_{J_a}(z) ≤ 4 - k_a(z)` and the token inequality `certY43_token` finishes it.

    The memo needs this only for the unseen vertices `U_a`, but it holds for every vertex of
    `S_a⁺`, so no `K_a`/`U_a` split is required here.  The other two cases of conservativity
    — that visible root-type vertices contribute exactly and visible shell-type vertices
    contribute at least as much — need the visible-defect vocabulary and are not proved. -/
theorem avoid_defect_term_nonneg (hΔ : maxDegree G ≤ 4) (a v z : Fin G.size) :
    avoidPosDeg G a v z * certY43 (avoidAttach G a v z).card
      ≤ 3 * (avoidAttach G a v z).card := by
  have hb := avoidPosDeg_add_avoidAttach_le4 hΔ a v z
  calc avoidPosDeg G a v z * certY43 (avoidAttach G a v z).card
      ≤ (4 - (avoidAttach G a v z).card) * certY43 (avoidAttach G a v z).card :=
        Nat.mul_le_mul_right _ (by omega)
    _ ≤ 3 * (avoidAttach G a v z).card := certY43_token _

/-- **The neighbour-layer budget: `2 T_a ≤ 27`.**  Combining (F4) with the token
    inequality and saturation at `a`.  In particular `T_a ≤ 13`, which is the sharp form
    of the punctured pentagon bound `pentagonCountAt_avoid_le_thirteen`. -/
theorem two_mul_avoidObjective_le_27 (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) {a v : Fin G.size} (hav : G.graph.Adj a v) :
    2 * avoidObjective G a v ≤ 27 := by
  have hΔ : maxDegree G ≤ 4 := le_of_eq hdeg
  rw [← avoid_F4_identity hTF hΔ hav]
  calc ∑ z ∈ shellPosAvoid G a v,
          avoidPosDeg G a v z * certY43 (avoidAttach G a v z).card
      ≤ ∑ z ∈ shellPosAvoid G a v,
          3 * (avoidAttach G a v z).card :=
        Finset.sum_le_sum fun z _ => avoid_defect_term_nonneg hΔ a v z
    _ = 27 := by
        rw [← Finset.mul_sum, sum_avoidAttach_shellPos_eq_nine hTF hReg hdeg hav]
        norm_num

/-! ### Consolidating `r_a ≤ 13` onto the F4 route

`pentagonCountAt_avoid_le_thirteen` above proves the punctured pentagon bound by its own
`certY43` chain.  (F4) gives the same bound by a sharper route — through the *equality*
`2 T_a = Σ_z d_{J_a}(z)·c(k_a(z))` rather than an inequality.  The link the two need is that
`avoidObjective` (a sum over `S_a⁺` pairs) equals the sum over *all* shell pairs of `a`, the
discarded terms being literally zero.

Both are kept.  They are **not** interchangeable: the original needs only triangle-freeness
and `maxDegree ≤ 4`, whereas the F4 route additionally needs regularity, which enters through
`sum_avoidAttach_eq_nine`.  So the version below is the same bound under stronger hypotheses,
not a replacement. -/

/-- **Punctured Step B.**  Shell edges of `a` with a zero punctured weight at an endpoint
    contribute nothing, so the full `shellPairsLt G a` sum is exactly `T_a`.  Mirror of
    `sum_T_restrict`, with `shellPos`/`attachSet` replaced by
    `shellPosAvoid`/`avoidAttach`. -/
theorem sum_avoid_restrict (a v : Fin G.size) :
    ∑ p ∈ shellPairsLt G a,
        ((attachSet G a p.1).erase v).card * ((attachSet G a p.2).erase v).card
      = avoidObjective G a v := by
  rw [avoidObjective]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro p hp
    rw [pairsLtOn, Finset.mem_filter, Finset.mem_product] at hp
    rw [← pairsLtOn_shellSet, pairsLtOn, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨shellPosAvoid_subset a v hp.1.1, shellPosAvoid_subset a v hp.1.2⟩, hp.2⟩
  · intro p hp hnot
    rw [← pairsLtOn_shellSet, pairsLtOn, Finset.mem_filter, Finset.mem_product] at hp
    by_cases h1 : 1 ≤ ((attachSet G a p.1).erase v).card
    · by_cases h2 : 1 ≤ ((attachSet G a p.2).erase v).card
      · exfalso
        refine hnot ?_
        rw [pairsLtOn, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨mem_shellPosAvoid.mpr ⟨hp.1.1, h1⟩,
          mem_shellPosAvoid.mpr ⟨hp.1.2, h2⟩⟩, hp.2⟩
      · have : ((attachSet G a p.2).erase v).card = 0 := by omega
        rw [this, Nat.mul_zero]
    · have : ((attachSet G a p.1).erase v).card = 0 := by omega
      rw [this, Nat.zero_mul]

/-- **`r_a ≤ 13`, via the sharp F4 chain.**  Same bound as
    `pentagonCountAt_avoid_le_thirteen`, but routed through the neighbour-layer budget
    `2 T_a ≤ 27` (which comes from the exact identity `avoid_F4_identity` plus saturation
    at `a`) instead of a separate `certY43` argument.

    Note the hypotheses are *stronger*: saturation at `a` (`sum_avoidAttach_eq_nine`) needs
    regularity and `maxDegree G = 4`, whereas `pentagonCountAt_avoid_le_thirteen` needs only
    triangle-freeness and `maxDegree G ≤ 4`.  So this is not a replacement — it is the same
    bound by a sharper route on a smaller class. -/
theorem pentagonCountAt_avoid_le_thirteen' (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) {a v : Fin G.size} (hav : G.graph.Adj a v) :
    (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)).card ≤ 13 := by
  have hfiber := pentagonCountAt_avoid_le_sum hTF v a
  rw [sum_avoid_restrict a v] at hfiber
  have hsharp := two_mul_avoidObjective_le_27 hTF hReg hdeg hav
  omega

/-! ### The visible defect

The vocabulary for conservativity (`D^vis ≤ D`) and, after it, the transport to the finite
model.  Fixing these definitions is the gate the rest of the Δ = 4 route waits on, so the
design decisions are recorded here rather than left implicit.

**Visibility is a root-layer predicate.**  The memo defines `K_a` and `U_a` by
`K_a = S_a⁺ ∩ ((N(v)∖{a}) ∪ (S⁺∖B_a))` and `U_a = S_a⁺ ∩ S³`, and splits `d̂_a` into
root-type and shell-type cases.  All of that collapses: `IsVisible v z` mentions neither `a`
nor `B_a`, and `K_a`/`U_a` are its two filters of `S_a⁺`.  The case split on `d̂_a` also
disappears, because for a root-type `z` every neighbour `w` of `z` automatically has
`z ∈ A_w`, so `unseenDeg v z = 0` there and the uniform `d̂ = visibleDeg + unseenDeg` already
gives the memo's two cases.

**No subtraction is ever formed.**  The per-term defect `3k_a(z) - c(k_a(z))·d̂_a(z)` can look
negative, and in `ℕ` a truncated term would *inflate* `D^vis` — harmless for the census half
`D^vis ≥ 12T - 212` but silently fatal for conservativity, which is the direction that needs
it.  Two independent designs both measured that truncation never actually fires (a companion
of `avoid_defect_term_nonneg` bounds `d̂ + k ≤ 4`), but that bound is tight with slack zero,
so relying on it would leave no margin.  Instead the difference is simply never formed:
everything downstream is an inequality between the two subtraction-free sums `visibleCredit`
and `visibleCharge`.  Conservativity will read

  `visibleCredit G a v + 2 * avoidObjective G a v ≤ 27 + visibleCharge G a v`,

legitimate because `2 T_a ≤ 27` is already a theorem and `27 = 3·Σ_{S_a⁺} k_a`.

**Validated against the reference.**  These definitions were checked against
the development notes's enumeration, whose minimum margins reproduce
`high_shell_certificate.json` exactly.  Over 3,677 roots of the triangle-free 4-regular
graphs on 8–14 vertices and 74,866 visible terms: the direct `u_z = |N(z) ∩ S³|` agrees
everywhere with the slot form `4 - k_z - d_{F⁺}(z)`; `unseenDeg` is `0` at every root-type
vertex, as the uniform `d̂` requires; no visible term is ever negative; and `D^vis ≤ D` holds
at every root, with equality at 555 of them — including the sharp circulants, where
`D^vis = D = 28 = 12·20 - 212` and the transport row `Q(v) = 160` is attained exactly. -/

/-- **Visibility from the root.**  `z` is visible when it is a neighbour of `v` or carries a
    positive root attachment.  Its negation cuts out the third layer `S³`. -/
noncomputable def IsVisible (G : Flag emptyType) (v z : Fin G.size) : Prop :=
  G.graph.Adj v z ∨ 1 ≤ (attachSet G v z).card

/-- `K_a`: the visible part of `S_a⁺`. -/
noncomputable def visibleAvoid (G : Flag emptyType) (a v : Fin G.size) : Finset (Fin G.size) :=
  (shellPosAvoid G a v).filter fun z => IsVisible G v z

/-- `U_a`: the unseen part of `S_a⁺`. -/
noncomputable def unseenAvoid (G : Flag emptyType) (a v : Fin G.size) : Finset (Fin G.size) :=
  (shellPosAvoid G a v).filter fun z => ¬ IsVisible G v z

/-- `S³`, the third layer. -/
noncomputable def unseenSet (G : Flag emptyType) (v : Fin G.size) : Finset (Fin G.size) :=
  Finset.univ.filter fun w => ¬ IsVisible G v w

/-- `u_z = |N(z) ∩ S³|`. -/
noncomputable def unseenDeg (G : Flag emptyType) (v z : Fin G.size) : ℕ :=
  ((unseenSet G v).filter fun w => G.graph.Adj z w).card

/-- `|N(z) ∩ K_a|`. -/
noncomputable def visibleDeg (G : Flag emptyType) (a v z : Fin G.size) : ℕ :=
  ((visibleAvoid G a v).filter fun y => G.graph.Adj z y).card

/-- **`d̂_a(z)`**, uniformly — no root-type / shell-type split. -/
noncomputable def dhat (G : Flag emptyType) (a v z : Fin G.size) : ℕ :=
  visibleDeg G a v z + unseenDeg G v z

/-- The visible **credit** `Σ_{z ∈ K_a} 3 k_a(z)`. -/
noncomputable def visibleCredit (G : Flag emptyType) (a v : Fin G.size) : ℕ :=
  ∑ z ∈ visibleAvoid G a v, 3 * (avoidAttach G a v z).card

/-- The visible **charge** `Σ_{z ∈ K_a} d̂_a(z)·c(k_a(z))`. -/
noncomputable def visibleCharge (G : Flag emptyType) (a v : Fin G.size) : ℕ :=
  ∑ z ∈ visibleAvoid G a v, dhat G a v z * certY43 (avoidAttach G a v z).card

/-- Root neighbourhood as a `Finset`. -/
noncomputable def rootNbrs (G : Flag emptyType) (v : Fin G.size) : Finset (Fin G.size) :=
  Finset.univ.filter fun a => G.graph.Adj v a

/-- Total visible credit over `N(v)`. -/
noncomputable def visibleCreditTotal (G : Flag emptyType) (v : Fin G.size) : ℕ :=
  ∑ a ∈ rootNbrs G v, visibleCredit G a v

/-- Total visible charge over `N(v)`. -/
noncomputable def visibleChargeTotal (G : Flag emptyType) (v : Fin G.size) : ℕ :=
  ∑ a ∈ rootNbrs G v, visibleCharge G a v

lemma mem_visibleAvoid {a v z : Fin G.size} :
    z ∈ visibleAvoid G a v ↔ z ∈ shellPosAvoid G a v ∧ IsVisible G v z := by
  rw [visibleAvoid, Finset.mem_filter]

lemma mem_unseenAvoid {a v z : Fin G.size} :
    z ∈ unseenAvoid G a v ↔ z ∈ shellPosAvoid G a v ∧ ¬ IsVisible G v z := by
  rw [unseenAvoid, Finset.mem_filter]

lemma visibleAvoid_subset (a v : Fin G.size) : visibleAvoid G a v ⊆ shellPosAvoid G a v :=
  Finset.filter_subset _ _

lemma unseenAvoid_subset (a v : Fin G.size) : unseenAvoid G a v ⊆ shellPosAvoid G a v :=
  Finset.filter_subset _ _

/-- `S_a⁺ = K_a ⊔ U_a`, as a sum split. -/
lemma sum_visible_add_unseen (a v : Fin G.size) (f : Fin G.size → ℕ) :
    ∑ z ∈ visibleAvoid G a v, f z + ∑ z ∈ unseenAvoid G a v, f z
      = ∑ z ∈ shellPosAvoid G a v, f z :=
  Finset.sum_filter_add_sum_filter_not _ _ _

/-! ### Conservativity: `D^vis ≤ D`

The memo's Proposition `prop:cons`.  Its content is a single pointwise lemma,
`avoidPosDeg_le_dhat`, containing **no graph theory at all**: `N(z)` meets `S_a⁺` in `K_a` and
`U_a`; the first part is exactly `visibleDeg`, and `U_a ⊆ S³` by construction, so the second
is at most `unseenDeg`.  The rest is the (F4) equality, `avoid_defect_term_nonneg`, and Nat
arithmetic.

Everything stays subtraction-free, as the visible-defect design requires: `D^vis_a ≤ D_a`
appears as `visibleCredit + 2·T_a ≤ 27 + visibleCharge`. -/

/-- The `K_a`-part of `N(z) ∩ S_a⁺` is exactly the set counted by `visibleDeg`. -/
lemma filter_adj_visible_eq (a v z : Fin G.size) :
    (((shellPosAvoid G a v).filter fun y => G.graph.Adj z y).filter
        fun y => IsVisible G v y)
      = (visibleAvoid G a v).filter fun y => G.graph.Adj z y := by
  ext y
  simp only [Finset.mem_filter, visibleAvoid]
  tauto

/-- The `U_a`-part of `N(z) ∩ S_a⁺` sits inside `N(z) ∩ S³`. -/
lemma filter_adj_unseen_subset (a v z : Fin G.size) :
    (((shellPosAvoid G a v).filter fun y => G.graph.Adj z y).filter
        fun y => ¬ IsVisible G v y)
      ⊆ (unseenSet G v).filter fun w => G.graph.Adj z w := by
  intro y hy
  simp only [Finset.mem_filter, unseenSet, Finset.mem_univ, true_and] at hy ⊢
  exact ⟨hy.2, hy.1.2⟩

/-- **Conservativity, pointwise.**  `d_{J_a}(z) ≤ d̂_a(z)`. -/
theorem avoidPosDeg_le_dhat (a v z : Fin G.size) :
    avoidPosDeg G a v z ≤ dhat G a v z := by
  have hsplit :
      (((shellPosAvoid G a v).filter fun y => G.graph.Adj z y).filter
          fun y => IsVisible G v y).card
        + (((shellPosAvoid G a v).filter fun y => G.graph.Adj z y).filter
            fun y => ¬ IsVisible G v y).card
        = ((shellPosAvoid G a v).filter fun y => G.graph.Adj z y).card :=
    Finset.card_filter_add_card_filter_not _
  have hvis : (((shellPosAvoid G a v).filter fun y => G.graph.Adj z y).filter
      fun y => IsVisible G v y).card = visibleDeg G a v z := by
    rw [filter_adj_visible_eq, visibleDeg]
  have hun : (((shellPosAvoid G a v).filter fun y => G.graph.Adj z y).filter
      fun y => ¬ IsVisible G v y).card ≤ unseenDeg G v z :=
    Finset.card_le_card (filter_adj_unseen_subset a v z)
  rw [avoidPosDeg, dhat]
  omega


/-! ### TARGET 2 — conservativity at a single neighbour -/

/-- The credit split: `Σ_{K_a} 3 k_a + Σ_{U_a} 3 k_a = 27`. -/
lemma credit_split_eq_27 (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) {a v : Fin G.size} (hav : G.graph.Adj a v) :
    (∑ z ∈ visibleAvoid G a v, 3 * (avoidAttach G a v z).card)
      + ∑ z ∈ unseenAvoid G a v, 3 * (avoidAttach G a v z).card = 27 := by
  rw [sum_visible_add_unseen a v (fun z => 3 * (avoidAttach G a v z).card),
    ← Finset.mul_sum, sum_avoidAttach_shellPos_eq_nine hTF hReg hdeg hav]
  norm_num

/-- The charge split, via (F4): `Σ_{K_a} d_J·c + Σ_{U_a} d_J·c = 2 T_a`. -/
lemma charge_split_eq_two_mul (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 4)
    {a v : Fin G.size} (hav : G.graph.Adj a v) :
    (∑ z ∈ visibleAvoid G a v,
        avoidPosDeg G a v z * certY43 (avoidAttach G a v z).card)
      + ∑ z ∈ unseenAvoid G a v,
          avoidPosDeg G a v z * certY43 (avoidAttach G a v z).card
      = 2 * avoidObjective G a v := by
  rw [sum_visible_add_unseen a v
    (fun z => avoidPosDeg G a v z * certY43 (avoidAttach G a v z).card)]
  exact avoid_F4_identity hTF hΔ hav

/-- On `K_a` the true charge is dominated by the visible charge (TARGET 1, summed). -/
lemma visible_part_le_visibleCharge (a v : Fin G.size) :
    (∑ z ∈ visibleAvoid G a v,
        avoidPosDeg G a v z * certY43 (avoidAttach G a v z).card)
      ≤ visibleCharge G a v :=
  Finset.sum_le_sum fun z _ =>
    Nat.mul_le_mul (avoidPosDeg_le_dhat a v z) (le_refl _)

/-- On `U_a` the true charge is dominated by the credit (`avoid_defect_term_nonneg`). -/
lemma unseen_part_le_credit (hΔ : maxDegree G ≤ 4) (a v : Fin G.size) :
    (∑ z ∈ unseenAvoid G a v,
        avoidPosDeg G a v z * certY43 (avoidAttach G a v z).card)
      ≤ ∑ z ∈ unseenAvoid G a v, 3 * (avoidAttach G a v z).card :=
  Finset.sum_le_sum fun z _ => avoid_defect_term_nonneg hΔ a v z

/-- **Conservativity at a neighbour `a` of the root `v`.** -/
theorem conservativity_at (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) {a v : Fin G.size} (hav : G.graph.Adj a v) :
    visibleCredit G a v + 2 * avoidObjective G a v ≤ 27 + visibleCharge G a v := by
  have hΔ : maxDegree G ≤ 4 := le_of_eq hdeg
  have hcred := credit_split_eq_27 hTF hReg hdeg hav
  have hF4 := charge_split_eq_two_mul hTF hΔ hav
  have hKle := visible_part_le_visibleCharge (G := G) a v
  have hUle := unseen_part_le_credit (G := G) hΔ a v
  simp only [visibleCredit]
  omega


/-! ### TARGET 3 — conservativity totalled over `N(v)` -/

/-- In a 4-regular graph the root has exactly four neighbours. -/
lemma card_rootNbrs (hReg : IsRegular G) (hdeg : maxDegree G = 4) (v : Fin G.size) :
    (rootNbrs G v).card = 4 := by
  rw [rootNbrs, hReg v, hdeg]

/-- **Conservativity, totalled over the root neighbourhood.** -/
theorem conservativity_total (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size) :
    visibleCreditTotal G v + 2 * (∑ a ∈ rootNbrs G v, avoidObjective G a v)
      ≤ 108 + visibleChargeTotal G v := by
  have hstep : ∑ a ∈ rootNbrs G v, (visibleCredit G a v + 2 * avoidObjective G a v)
      ≤ ∑ a ∈ rootNbrs G v, (27 + visibleCharge G a v) := by
    refine Finset.sum_le_sum fun a ha => ?_
    rw [rootNbrs, Finset.mem_filter] at ha
    exact conservativity_at hTF hReg hdeg ha.2.symm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, card_rootNbrs hReg hdeg v, smul_eq_mul] at hstep
  simp only [visibleCreditTotal, visibleChargeTotal]
  omega

/-! ### Radius-2 locality: removing the third layer

`d̂_a(z)` is the only quantity in the transport row that appears to look past distance two:
`unseenDeg` counts neighbours of `z` lying in the third layer `S³`, which no bounded model
could see.  Under `4`-regularity it never needs to.  `N(z)` splits three ways — the root
attachment, the positive-weight shell, and the invisible rest — so the invisible count is the
*slot count* `4 - k_z - d_{F⁺}(z)`, computed from radius-2 data alone.

**This removes one obstruction to the transport; it does not by itself achieve it.**  After
these lemmas, `visibleCreditTotal` and `visibleChargeTotal` read only the marked ball of
radius two around the root.  Still missing, and none of it attempted here: a restriction of
the shell objective `T` to `shellPos × shellPos` (mathematically easy, formally absent — there
is no analogue of `sum_avoid_restrict` for it), a definition of the ball itself, the statement
that each quantity is an isomorphism invariant of the marked ball, and the enumeration of
realizable balls.  The `∀ H` in `pentagon_bound_delta4_of_visible_enumeration` does **not** yet
collapse to a finite check.

Measured over the census (268 connected triangle-free 4-regular graphs on 8–14 vertices):
`unseenDeg = shellSlack` at all 32,208 shell vertices, with `shellSlack` strictly positive on
53% of them, so the identity is not vacuous; the uniform `dhat_eq_local` reproduces `d̂` on all
74,866 visible terms; and both fail on Petersen, which is 3-regular — an independent check
that the degree hypothesis is doing work. -/

/-- **The three-way split of a neighbourhood.**  For a vertex `z` not adjacent to the root,
    `N(z)` decomposes into the root attachment `A_z`, the positive-weight shell neighbours,
    and the invisible rest.  Under `4`-regularity those three cards sum to `4`.

    Both hypotheses are load-bearing.  Dropping `hvz` makes the statement FALSE at every
    root-type vertex (there the sum is `3`, not `4`); dropping regularity makes it false on
    most non-regular hosts. -/
theorem unseenDeg_add_attach_add_shellPosDeg_eq_four (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    {v z : Fin G.size} (hvz : ¬ G.graph.Adj v z) :
    unseenDeg G v z + (attachSet G v z).card + shellPosDeg G v z = 4 := by
  have hne_of_adj : ∀ u : Fin G.size, G.graph.Adj z u → u ≠ v := by
    intro u hu huv
    exact hvz (huv ▸ hu).symm
  set N : Finset (Fin G.size) := Finset.univ.filter fun u => G.graph.Adj z u with hNdef
  have hN : N.card = 4 := by
    have h := hReg z
    rw [hdeg] at h
    exact h
  set N' : Finset (Fin G.size) := N.filter fun u => ¬ G.graph.Adj v u with hN'def
  have hsplit1 : (N.filter fun u => G.graph.Adj v u).card + N'.card = N.card :=
    Finset.card_filter_add_card_filter_not _
  have hsplit2 :
      (N'.filter fun u => 1 ≤ (attachSet G v u).card).card
        + (N'.filter fun u => ¬ 1 ≤ (attachSet G v u).card).card = N'.card :=
    Finset.card_filter_add_card_filter_not _
  have hA : (N.filter fun u => G.graph.Adj v u) = attachSet G v z := by
    ext u
    simp only [hNdef, attachSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hB : (N'.filter fun u => 1 ≤ (attachSet G v u).card)
      = (shellPos G v).filter fun y => G.graph.Adj z y := by
    ext u
    simp only [hN'def, hNdef, shellPos, shellSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hzu, hvu⟩, hpos⟩
      exact ⟨⟨⟨hne_of_adj u hzu, hvu⟩, hpos⟩, hzu⟩
    · rintro ⟨⟨⟨-, hvu⟩, hpos⟩, hzu⟩
      exact ⟨⟨hzu, hvu⟩, hpos⟩
  have hC : (N'.filter fun u => ¬ 1 ≤ (attachSet G v u).card)
      = (unseenSet G v).filter fun w => G.graph.Adj z w := by
    ext u
    simp only [hN'def, hNdef, unseenSet, IsVisible, Finset.mem_filter, Finset.mem_univ,
      true_and, not_or]
    constructor
    · rintro ⟨⟨hzu, hvu⟩, hpos⟩
      exact ⟨⟨hvu, hpos⟩, hzu⟩
    · rintro ⟨⟨hvu, hpos⟩, hzu⟩
      exact ⟨⟨hzu, hvu⟩, hpos⟩
  rw [hA] at hsplit1
  rw [hB, hC] at hsplit2
  rw [hN] at hsplit1
  have hsd : shellPosDeg G v z = ((shellPos G v).filter fun y => G.graph.Adj z y).card := rfl
  have hud : unseenDeg G v z = ((unseenSet G v).filter fun w => G.graph.Adj z w).card := rfl
  omega

theorem unseenDeg_eq_shellSlack (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    {v z : Fin G.size} (hvz : ¬ G.graph.Adj v z) :
    unseenDeg G v z = shellSlack G v z := by
  have h1 := unseenDeg_add_attach_add_shellPosDeg_eq_four hReg hdeg hvz
  have h2 := shellPosDeg_add_slack_add_attach (G := G) (le_of_eq hdeg) v z
  omega

/-- **The root-type case.**  A neighbour of the root has no invisible neighbours at all: if
    `z ∼ v` and `w ∼ z` then `z ∈ A_w`, so `w` is visible.  Needs neither regularity nor a
    degree bound. -/
theorem unseenDeg_eq_zero_of_adj {v z : Fin G.size} (hvz : G.graph.Adj v z) : unseenDeg G v z = 0 := by
  rw [unseenDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w hw
  rw [unseenSet, Finset.mem_filter] at hw
  intro hzw
  exact hw.2 (Or.inr (by
    have : z ∈ attachSet G v w := by
      rw [attachSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hvz, hzw.symm⟩
    exact Finset.card_pos.mpr ⟨z, this⟩))

/-- **`d̂` reads only radius-2 data**, uniformly over both vertex types.  `unseenDeg` is the
    one quantity in the transport row that looks into the third layer `S³`; this replaces it
    by the slot count `shellSlack`, which is computed from the root attachment and the shell
    adjacency alone.

    Verified on all 74,866 visible terms of the census: the right-hand side reproduces `d̂`
    with no mismatch.  Note the `if`: the shell-type branch needs the slot count, the
    root-type branch contributes nothing, and an earlier version of this lemma covered only
    the shell-type half (58% of terms) and was silently wrong on the rest. -/
theorem dhat_eq_local (hReg : IsRegular G) (hdeg : maxDegree G = 4) {a v z : Fin G.size} :
    dhat G a v z
      = visibleDeg G a v z + (if G.graph.Adj v z then 0 else shellSlack G v z) := by
  by_cases h : G.graph.Adj v z
  · rw [dhat, unseenDeg_eq_zero_of_adj h, if_pos h]
  · rw [dhat, unseenDeg_eq_shellSlack hReg hdeg h, if_neg h]

/-! ### The radius-2 ball, and where the transport quantities live

`B₂(v) = {v} ∪ N(v) ∪ S⁺`.  Note `shellPos`, not `shellSet`: the zero-weight shell is
unbounded and must stay out of the ball.

Every index set the transport row ranges over lies inside it — `T`'s summation range (after
`sum_T_restrict`), the outer sum of the totals over `N(v)`, and every inner sum over `K_a`.
Together with `dhat_eq_local`, which already removed the one quantity that read the third
layer, the row is now *expressible* in ball-internal data.

**The bound `17` is attained, not slack.**  When the four root neighbours have pairwise
disjoint second neighbourhoods, all twelve shell vertices carry attachment exactly one, so
`|S⁺| = 12` and `|B₂(v)| = 1 + 4 + 12 = 17`; a 4-regular triangle-free witness on 19 vertices
realises it.  The census maximum of 14 reflects only the orders enumerated there, not a
provable ceiling, so the finite model must be sized for 17.

**What this does not give.**  Containment plus a size bound is necessary for "henum is
determined by bounded local data", not sufficient.  The missing step is *invariance*: that
`T`, `visibleCreditTotal` and `visibleChargeTotal` are unchanged under an isomorphism of the
induced structure on the ball.  That is untouched here, and it is what the model-transport
stage has to supply. -/

/-- Membership in the shell, unfolded (local copy: `PentagonUnique` is not imported here). -/
lemma mem_shellSet' {v x : Fin G.size} :
    x ∈ shellSet G v ↔ x ≠ v ∧ ¬ G.graph.Adj v x := by
  rw [shellSet, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **The radius-2 ball at `v`**: the root, its neighbours, and the positive shell `S⁺`. -/
noncomputable def ball2 (G : Flag emptyType) (v : Fin G.size) : Finset (Fin G.size) :=
  insert v ((Finset.univ.filter fun u => G.graph.Adj v u) ∪ shellPos G v)

/-- The neighbour block of `ball2` is exactly `rootNbrs` (definitional). -/
lemma ball2_eq (v : Fin G.size) :
    ball2 G v = insert v (rootNbrs G v ∪ shellPos G v) := rfl

lemma mem_ball2 {v z : Fin G.size} :
    z ∈ ball2 G v ↔ z = v ∨ G.graph.Adj v z ∨ z ∈ shellPos G v := by
  simp [ball2, Finset.mem_insert, Finset.mem_union, Finset.mem_filter]

/-! ### Target 2: the support lemmas -/

theorem shellPos_subset_ball2 (v : Fin G.size) : shellPos G v ⊆ ball2 G v := by
  intro z hz
  exact mem_ball2.mpr (Or.inr (Or.inr hz))

theorem rootNbrs_subset_ball2 (v : Fin G.size) : rootNbrs G v ⊆ ball2 G v := by
  intro z hz
  rw [rootNbrs, Finset.mem_filter] at hz
  exact mem_ball2.mpr (Or.inr (Or.inl hz.2))

/-- The shell `S⁺` of a *neighbour* `a` of `v`, cut down to the vertices visible from `v`,
    still sits inside the radius-2 ball at `v`.  This is the only support lemma with
    content: visibility is a disjunction, and the non-adjacent branch needs `z ≠ v`, which
    comes from `z` lying in the shell of `a` together with `v ∼ a`. -/
theorem visibleAvoid_subset_ball2 {a v : Fin G.size} (hav : G.graph.Adj v a) :
    visibleAvoid G a v ⊆ ball2 G v := by
  intro z hz
  obtain ⟨hzS, hvis⟩ := mem_visibleAvoid.mp hz
  by_cases hadj : G.graph.Adj v z
  · exact mem_ball2.mpr (Or.inr (Or.inl hadj))
  · -- `z` is not adjacent to `v`, so visibility forces a positive root attachment.
    have hpos : 1 ≤ (attachSet G v z).card := hvis.resolve_left hadj
    -- `z` lies in the shell of `a`, hence is not adjacent to `a`; but `v ∼ a`, so `z ≠ v`.
    have hzSa : z ∈ shellSet G a := shellPosAvoid_subset a v hzS
    have hna : ¬ G.graph.Adj a z := (mem_shellSet'.mp hzSa).2
    have hzv : z ≠ v := by
      intro h
      exact hna (h ▸ hav.symm)
    exact mem_ball2.mpr (Or.inr (Or.inr
      (mem_shellPos.mpr ⟨mem_shellSet'.mpr ⟨hzv, hadj⟩, hpos⟩)))

/-- The `T`-summation range, after `sum_T_restrict`, is a set of pairs from the ball. -/
theorem pairsLtOn_shellPos_subset_ball2 (v : Fin G.size) :
    pairsLtOn G (shellPos G v) ⊆ ball2 G v ×ˢ ball2 G v := by
  intro p hp
  rw [pairsLtOn, Finset.mem_filter, Finset.mem_product] at hp
  exact Finset.mem_product.mpr
    ⟨shellPos_subset_ball2 v hp.1.1, shellPos_subset_ball2 v hp.1.2⟩

/-- **The transport row's index set lies in `B₂(v) × B₂(v)`.**  Both the outer sum of
    `visibleCreditTotal` / `visibleChargeTotal` (over `N(v)`) and every inner sum (over
    `K_a`) range inside the ball. -/
theorem visibleTotal_index_subset_ball2 (v : Fin G.size) :
    ∀ a ∈ rootNbrs G v, a ∈ ball2 G v ∧ visibleAvoid G a v ⊆ ball2 G v := by
  intro a ha
  refine ⟨rootNbrs_subset_ball2 v ha, visibleAvoid_subset_ball2 ?_⟩
  rw [rootNbrs, Finset.mem_filter] at ha
  exact ha.2

/-! ### Target 3: the size bound -/

/-- Every vertex of `S⁺` carries at least one attachment, and the attachments total `12`. -/
theorem card_shellPos_le_twelve (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size) : (shellPos G v).card ≤ 12 := by
  have hsum := sum_attach_shellPos_eq_twelve hTF hReg hdeg v
  calc (shellPos G v).card = ∑ _x ∈ shellPos G v, 1 := by simp
    _ ≤ ∑ x ∈ shellPos G v, (attachSet G v x).card :=
        Finset.sum_le_sum fun x hx => (mem_shellPos.mp hx).2
    _ = 12 := hsum

/-- **The ball is bounded: `|B₂(v)| ≤ 17`.**  `1` for the root, `4` for the neighbourhood
    (regularity plus `Δ = 4`), and `12` for `S⁺` (saturation: the attachments sum to `12`
    and each `S⁺` vertex carries at least one). -/
theorem card_ball2_le (hTF : IsTriangleFree G) (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    (v : Fin G.size) : (ball2 G v).card ≤ 17 := by
  have h1 : (rootNbrs G v).card = 4 := card_rootNbrs hReg hdeg v
  have h2 : (shellPos G v).card ≤ 12 := card_shellPos_le_twelve hTF hReg hdeg v
  have hu : (rootNbrs G v ∪ shellPos G v).card ≤ 16 := by
    refine le_trans (Finset.card_union_le _ _) ?_
    omega
  refine le_trans (le_of_eq (congrArg Finset.card (ball2_eq v))) ?_
  exact le_trans (Finset.card_insert_le _ _) (by omega)

/-- **Exact size.**  The three layers are pairwise disjoint, so the ball has exactly
    `1 + 4 + |S⁺|` vertices on a 4-regular graph; only `|S⁺| ≤ 12` is an inequality. -/
theorem card_ball2_eq (hReg : IsRegular G) (hdeg : maxDegree G = 4) (v : Fin G.size) :
    (ball2 G v).card = 5 + (shellPos G v).card := by
  have hdisj : Disjoint (Finset.univ.filter fun u => G.graph.Adj v u) (shellPos G v) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [Finset.mem_filter] at hu
    have := (mem_shellPos.mp hu').1
    rw [shellSet, Finset.mem_filter] at this
    exact this.2.2 hu.2
  have hvnot : v ∉ (Finset.univ.filter fun u => G.graph.Adj v u) ∪ shellPos G v := by
    intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact G.graph.irrefl (Finset.mem_filter.mp hv).2
    · have := (mem_shellPos.mp hv).1
      rw [shellSet, Finset.mem_filter] at this
      exact this.2.1 rfl
  rw [ball2, Finset.card_insert_of_notMem hvnot,
    Finset.card_union_of_disjoint hdisj, hReg v, hdeg]
  omega

/-! ### Transfer along a closed induced injection

Every quantity in the transport row is unchanged by a map `φ : Fin H.size → Fin G.size` that
is injective, induced, and *closed* (`∀ i u, G.Adj (φ i) u → ∃ j, φ j = u`).  The capstone
`visibleRow_transfer` states the whole `henum` row, gate included, as an `↔`.

**Read the strength of this correctly: it is component invariance, not locality.**  The
closure hypothesis is exactly the statement that the image is a union of connected components
of `G`, so what these lemmas prove is that the row at `v` depends only on `v`'s component —
equivalently, that bolting extra components onto `G` changes nothing.  That is real and
reusable, but it does **not** finitise the `∀ H` of
`pentagon_bound_delta4_of_visible_enumeration`, because the connected triangle-free `4`-regular
graphs are themselves an infinite family.

**What the transport actually needs is invariance under isomorphism of the rooted radius-2
ball**, which is strictly stronger and is still open.  Two facts about it, both checked:

* Ball isomorphism alone does **not** suffice without a degree hypothesis.  `T` and
  `visibleCreditTotal` are determined by the ball, but `visibleChargeTotal` is not: two
  triangle-free graphs can have identical rooted induced balls and differ in `unseenDeg`,
  hence in the charge — the difference lives at distance three, which the ball cannot see.
* Under `4`-regularity it **does** suffice, and the bridge already exists:
  `unseenDeg_add_attach_add_shellPosDeg_eq_four` forces `unseenDeg = 4 - |A_z| - d_{F⁺}(z)`,
  which is ball-internal.  So the ball-invariance lemma should be proved *through*
  `dhat_eq_local`, paying regularity to remove the layer-3 lookup.  `henum` already quantifies
  only over regular hosts, so those hypotheses cost its consumer nothing.

The lemmas below deliberately take the other trade — they avoid `dhat_eq_local` and keep the
hypothesis set to the embedding triple, which makes them more general but leaves the layer-3
lookup in place.  They are the right tool for component-level reasoning and the wrong one for
finitisation. -/

section Transfer

variable {H G : Flag emptyType} {φ : Fin H.size → Fin G.size}

/-- Outside the image of a closed embedding there is no attachment at all. -/
theorem attachSet_eq_empty_of_not_mem_range
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (i₀ : Fin H.size) {u : Fin G.size} (hu : ∀ j, φ j ≠ u) :
    attachSet G (φ i₀) u = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro a ha
  rw [attachSet, Finset.mem_filter] at ha
  obtain ⟨-, h1, h2⟩ := ha
  obtain ⟨j, rfl⟩ := hclosed i₀ a h1
  obtain ⟨k, hk⟩ := hclosed j u h2.symm
  exact hu k hk

/-- The attachment set transfers along a closed induced embedding. -/
theorem attachSet_image
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (i₀ x : Fin H.size) :
    attachSet G (φ i₀) (φ x) = (attachSet H i₀ x).image φ := by
  ext a
  constructor
  · intro ha
    rw [attachSet, Finset.mem_filter] at ha
    obtain ⟨-, h1, h2⟩ := ha
    obtain ⟨j, rfl⟩ := hclosed i₀ a h1
    refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
    rw [attachSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hiff i₀ j).mpr h1, (hiff x j).mpr h2⟩
  · intro ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    rw [attachSet, Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_univ _, (hiff i₀ j).mp hj.2.1, (hiff x j).mp hj.2.2⟩

/-- **T1.**  Attachment counts are invariant along a closed induced embedding. -/
theorem attachSet_transfer
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (i₀ x : Fin H.size) :
    (attachSet G (φ i₀) (φ x)).card = (attachSet H i₀ x).card := by
  rw [attachSet_image hiff hclosed i₀ x, Finset.card_image_of_injective _ hinj]

end Transfer


/-! ### Doubling: the `<`-ordered pair sum against the both-orientations pair sum

`pairsLtOn` selects one of the two orientations by the *order* on `Fin G.size`, which a
graph embedding need not respect.  These three lemmas move the symmetric pair objective onto
`pairsAdjOn`, which is order-free; the first two are the `hsplit` / `hdisj` steps already
proved inline inside `sum_pairsLtOn_endpoints`, extracted verbatim. -/

section Doubling

variable {G : Flag emptyType}

lemma pairsAdjOn_eq_union (S : Finset (Fin G.size)) :
    pairsAdjOn G S = pairsLtOn G S ∪ (pairsLtOn G S).image Prod.swap := by
  ext q
  simp only [pairsAdjOn, pairsLtOn, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨h1, h2⟩, hadj⟩
    rcases lt_trichotomy q.1 q.2 with hlt | heq | hgt
    · exact Or.inl ⟨⟨h1, h2⟩, hlt, hadj⟩
    · exact absurd heq (G.graph.ne_of_adj hadj)
    · exact Or.inr ⟨(q.2, q.1), ⟨⟨h2, h1⟩, hgt, hadj.symm⟩, rfl⟩
  · rintro (⟨⟨h1, h2⟩, _, hadj⟩ | ⟨p, ⟨⟨h1, h2⟩, _, hadj⟩, rfl⟩)
    · exact ⟨⟨h1, h2⟩, hadj⟩
    · exact ⟨⟨h2, h1⟩, hadj.symm⟩

lemma pairsLtOn_disjoint_swap (S : Finset (Fin G.size)) :
    Disjoint (pairsLtOn G S) ((pairsLtOn G S).image Prod.swap) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp'
  rw [pairsLtOn, Finset.mem_filter] at hp hq
  have h1 : q.1 < q.2 := hq.2.1
  have h2 : q.2 < q.1 := by simpa using hp.2.1
  exact absurd h1 (lt_asymm h2)

/-- A symmetric pair objective over both orientations is twice the `<`-ordered one. -/
lemma sum_pairsAdjOn_prod (S : Finset (Fin G.size)) (f : Fin G.size → ℕ) :
    ∑ p ∈ pairsAdjOn G S, f p.1 * f p.2 = 2 * ∑ p ∈ pairsLtOn G S, f p.1 * f p.2 := by
  rw [pairsAdjOn_eq_union, Finset.sum_union (pairsLtOn_disjoint_swap S),
    Finset.sum_image (fun p _ q _ h => Prod.swap_injective h)]
  have : ∑ p ∈ pairsLtOn G S, f (Prod.swap p).1 * f (Prod.swap p).2
      = ∑ p ∈ pairsLtOn G S, f p.1 * f p.2 :=
    Finset.sum_congr rfl fun p _ => by simp [Nat.mul_comm]
  rw [this, two_mul]

end Doubling

section Transfer2

variable {H G : Flag emptyType} {φ : Fin H.size → Fin G.size}

/-- A vertex carrying a positive root attachment lies in the image. -/
lemma mem_range_of_attach_pos
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    {i₀ : Fin H.size} {u : Fin G.size} (hpos : 1 ≤ (attachSet G (φ i₀) u).card) :
    ∃ j, φ j = u := by
  by_contra hno
  push_neg at hno
  rw [attachSet_eq_empty_of_not_mem_range hclosed i₀ hno] at hpos
  simp at hpos

/-- The positive shell transfers: it is exactly the image of the positive shell of `H`. -/
theorem shellPos_image
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (i₀ : Fin H.size) :
    shellPos G (φ i₀) = (shellPos H i₀).image φ := by
  ext u
  constructor
  · intro hu
    obtain ⟨hS, hpos⟩ := mem_shellPos.mp hu
    obtain ⟨y, rfl⟩ := mem_range_of_attach_pos hclosed hpos
    obtain ⟨hne, hnadj⟩ := mem_shellSet'.mp hS
    refine Finset.mem_image.mpr ⟨y, mem_shellPos.mpr ⟨mem_shellSet'.mpr ⟨?_, ?_⟩, ?_⟩, rfl⟩
    · exact fun h => hne (congrArg φ h)
    · exact fun h => hnadj ((hiff i₀ y).mp h)
    · rwa [attachSet_transfer hinj hiff hclosed i₀ y] at hpos
  · intro hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hS, hpos⟩ := mem_shellPos.mp hy
    obtain ⟨hne, hnadj⟩ := mem_shellSet'.mp hS
    refine mem_shellPos.mpr ⟨mem_shellSet'.mpr ⟨?_, ?_⟩, ?_⟩
    · exact fun h => hne (hinj h)
    · exact fun h => hnadj ((hiff i₀ y).mpr h)
    · rwa [attachSet_transfer hinj hiff hclosed i₀ y]

/-- `Prod.map φ φ`, as an injection on pairs. -/
lemma prodMap_injective (hinj : Function.Injective φ) :
    Function.Injective (fun p : Fin H.size × Fin H.size => (φ p.1, φ p.2)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  obtain ⟨h1, h2⟩ := Prod.mk.injEq _ _ _ _ ▸ h
  exact Prod.ext (hinj h1) (hinj h2)

/-- Both-orientation adjacent pairs drawn from an image set are the image of the pairs. -/
theorem pairsAdjOn_image
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (S : Finset (Fin H.size)) :
    pairsAdjOn G (S.image φ) =
      (pairsAdjOn H S).image (fun p : Fin H.size × Fin H.size => (φ p.1, φ p.2)) := by
  ext ⟨q₁, q₂⟩
  simp only [pairsAdjOn, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, hadj⟩
    obtain ⟨a, ha, rfl⟩ := h1
    obtain ⟨b, hb, rfl⟩ := h2
    exact ⟨(a, b), ⟨⟨ha, hb⟩, (hiff a b).mpr hadj⟩, rfl⟩
  · rintro ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hadj⟩, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, (hiff a b).mp hadj⟩

/-- **T2.**  The shell objective `T(v)` is invariant along a closed induced embedding. -/
theorem shellObjective_transfer
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (i₀ : Fin H.size) :
    (∑ p ∈ shellPairsLt G (φ i₀),
        (attachSet G (φ i₀) p.1).card * (attachSet G (φ i₀) p.2).card)
      = ∑ p ∈ shellPairsLt H i₀,
          (attachSet H i₀ p.1).card * (attachSet H i₀ p.2).card := by
  rw [sum_T_restrict (φ i₀), sum_T_restrict i₀]
  have key : 2 * (∑ p ∈ pairsLtOn G (shellPos G (φ i₀)),
        (attachSet G (φ i₀) p.1).card * (attachSet G (φ i₀) p.2).card)
      = 2 * ∑ p ∈ pairsLtOn H (shellPos H i₀),
          (attachSet H i₀ p.1).card * (attachSet H i₀ p.2).card := by
    rw [← sum_pairsAdjOn_prod (shellPos G (φ i₀)) (fun u => (attachSet G (φ i₀) u).card),
      ← sum_pairsAdjOn_prod (shellPos H i₀) (fun u => (attachSet H i₀ u).card),
      shellPos_image hinj hiff hclosed i₀, pairsAdjOn_image hiff,
      Finset.sum_image (prodMap_injective hinj).injOn]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [attachSet_transfer hinj hiff hclosed i₀ p.1,
      attachSet_transfer hinj hiff hclosed i₀ p.2]
  omega

end Transfer2


section Transfer3

variable {H G : Flag emptyType} {φ : Fin H.size → Fin G.size}

/-- The root neighbourhood transfers. -/
theorem rootNbrs_image
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (i₀ : Fin H.size) :
    rootNbrs G (φ i₀) = (rootNbrs H i₀).image φ := by
  ext u
  rw [rootNbrs, Finset.mem_filter]
  constructor
  · rintro ⟨-, hadj⟩
    obtain ⟨j, rfl⟩ := hclosed i₀ u hadj
    refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
    rw [rootNbrs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hiff i₀ j).mpr hadj⟩
  · intro hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    rw [rootNbrs, Finset.mem_filter] at hj
    exact ⟨Finset.mem_univ _, (hiff i₀ j).mp hj.2⟩

/-- The punctured attachment set transfers. -/
theorem avoidAttach_image
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (a i₀ z : Fin H.size) :
    avoidAttach G (φ a) (φ i₀) (φ z) = (avoidAttach H a i₀ z).image φ := by
  rw [avoidAttach, avoidAttach, attachSet_image hiff hclosed a z, Finset.image_erase hinj]

/-- Punctured attachment counts are invariant. -/
theorem avoidAttach_transfer
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (a i₀ z : Fin H.size) :
    (avoidAttach G (φ a) (φ i₀) (φ z)).card = (avoidAttach H a i₀ z).card := by
  rw [avoidAttach_image hinj hiff hclosed a i₀ z, Finset.card_image_of_injective _ hinj]

lemma mem_range_of_avoidAttach_pos
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    {a i₀ : Fin H.size} {u : Fin G.size}
    (hpos : 1 ≤ (avoidAttach G (φ a) (φ i₀) u).card) : ∃ j, φ j = u := by
  refine mem_range_of_attach_pos hclosed (i₀ := a) ?_
  have h : (avoidAttach G (φ a) (φ i₀) u).card ≤ (attachSet G (φ a) u).card :=
    Finset.card_le_card (Finset.erase_subset _ _)
  omega

/-- The punctured positive shell transfers. -/
theorem shellPosAvoid_image
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (a i₀ : Fin H.size) :
    shellPosAvoid G (φ a) (φ i₀) = (shellPosAvoid H a i₀).image φ := by
  ext u
  constructor
  · intro hu
    obtain ⟨hS, hpos⟩ := mem_shellPosAvoid.mp hu
    obtain ⟨z, rfl⟩ := mem_range_of_avoidAttach_pos hclosed hpos
    obtain ⟨hne, hnadj⟩ := mem_shellSet'.mp hS
    refine Finset.mem_image.mpr ⟨z, mem_shellPosAvoid.mpr ⟨mem_shellSet'.mpr ⟨?_, ?_⟩, ?_⟩, rfl⟩
    · exact fun h => hne (congrArg φ h)
    · exact fun h => hnadj ((hiff a z).mp h)
    · rwa [avoidAttach_transfer hinj hiff hclosed a i₀ z] at hpos
  · intro hu
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hS, hpos⟩ := mem_shellPosAvoid.mp hz
    obtain ⟨hne, hnadj⟩ := mem_shellSet'.mp hS
    refine mem_shellPosAvoid.mpr ⟨mem_shellSet'.mpr ⟨?_, ?_⟩, ?_⟩
    · exact fun h => hne (hinj h)
    · exact fun h => hnadj ((hiff a z).mpr h)
    · rwa [avoidAttach_transfer hinj hiff hclosed a i₀ z]

/-- Visibility from the root transfers. -/
theorem isVisible_transfer
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (i₀ z : Fin H.size) :
    IsVisible G (φ i₀) (φ z) ↔ IsVisible H i₀ z := by
  rw [IsVisible, IsVisible, attachSet_transfer hinj hiff hclosed i₀ z]
  exact or_congr (hiff i₀ z).symm Iff.rfl

/-- The visible part `K_a` transfers. -/
theorem visibleAvoid_image
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (a i₀ : Fin H.size) :
    visibleAvoid G (φ a) (φ i₀) = (visibleAvoid H a i₀).image φ := by
  ext u
  constructor
  · intro hu
    obtain ⟨hS, hvis⟩ := mem_visibleAvoid.mp hu
    rw [shellPosAvoid_image hinj hiff hclosed a i₀] at hS
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_image.mpr ⟨z, mem_visibleAvoid.mpr ⟨hz,
      (isVisible_transfer hinj hiff hclosed i₀ z).mp hvis⟩, rfl⟩
  · intro hu
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hS, hvis⟩ := mem_visibleAvoid.mp hz
    refine mem_visibleAvoid.mpr ⟨?_, (isVisible_transfer hinj hiff hclosed i₀ z).mpr hvis⟩
    rw [shellPosAvoid_image hinj hiff hclosed a i₀]
    exact Finset.mem_image_of_mem φ hS

/-- The visible credit at a single neighbour is invariant. -/
theorem visibleCredit_transfer
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (a i₀ : Fin H.size) :
    visibleCredit G (φ a) (φ i₀) = visibleCredit H a i₀ := by
  rw [visibleCredit, visibleCredit, visibleAvoid_image hinj hiff hclosed a i₀,
    Finset.sum_image hinj.injOn]
  exact Finset.sum_congr rfl fun z _ => by
    rw [avoidAttach_transfer hinj hiff hclosed a i₀ z]

/-- **T3.**  The total visible credit is invariant along a closed induced embedding. -/
theorem visibleCreditTotal_transfer
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (i₀ : Fin H.size) :
    visibleCreditTotal G (φ i₀) = visibleCreditTotal H i₀ := by
  rw [visibleCreditTotal, visibleCreditTotal, rootNbrs_image hiff hclosed i₀,
    Finset.sum_image hinj.injOn]
  exact Finset.sum_congr rfl fun a _ => visibleCredit_transfer hinj hiff hclosed a i₀

end Transfer3


/-! ### T4: the visible charge

`visibleCharge` carries `dhat = visibleDeg + unseenDeg`, and `unseenDeg` is the one quantity
that reads the third layer `S³`.  It still transfers, and **without** `dhat_eq_local`: the
route taken here is direct.  `unseenSet G (φ i₀)` is much bigger than the image of
`unseenSet H i₀` — every vertex outside the image is invisible from `φ i₀`, since `hclosed`
makes it non-adjacent to `φ i₀` and `attachSet_eq_empty_of_not_mem_range` kills its
attachment.  But `unseenDeg` filters that set by adjacency to `φ z`, and `hclosed` at `z`
puts every neighbour of `φ z` back inside the image.  So the extra vertices are all discarded
by the filter, and the filtered set is exactly the image of the `H`-side one.

The alternative route — rewrite `dhat` by `dhat_eq_local` and transfer `shellSlack` instead —
would have needed `IsRegular` and `maxDegree = 4` on both sides, and a transfer lemma for
`shellPosDeg` plus a truncated-subtraction argument.  The direct route needs no hypothesis on
either graph beyond the three embedding conditions. -/

section Transfer4

variable {H G : Flag emptyType} {φ : Fin H.size → Fin G.size}

/-- The visible degree transfers. -/
theorem visibleDeg_transfer
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (a i₀ z : Fin H.size) :
    visibleDeg G (φ a) (φ i₀) (φ z) = visibleDeg H a i₀ z := by
  have hfil : ((visibleAvoid H a i₀).filter fun y => G.graph.Adj (φ z) (φ y))
      = (visibleAvoid H a i₀).filter fun y => H.graph.Adj z y := by
    ext y
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ => (hiff z y).symm
  rw [visibleDeg, visibleDeg, visibleAvoid_image hinj hiff hclosed a i₀,
    Finset.filter_image, Finset.card_image_of_injective _ hinj, hfil]

/-- The unseen degree transfers: the third layer outside the image is invisible, but it is
    also unreachable from the image, so the adjacency filter discards it. -/
theorem unseenDeg_transfer
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (i₀ z : Fin H.size) :
    unseenDeg G (φ i₀) (φ z) = unseenDeg H i₀ z := by
  have himg : ((unseenSet G (φ i₀)).filter fun w => G.graph.Adj (φ z) w)
      = ((unseenSet H i₀).filter fun w => H.graph.Adj z w).image φ := by
    ext u
    constructor
    · intro hu
      rw [Finset.mem_filter, unseenSet, Finset.mem_filter] at hu
      obtain ⟨⟨-, hvis⟩, hadj⟩ := hu
      obtain ⟨w, rfl⟩ := hclosed z u hadj
      refine Finset.mem_image.mpr ⟨w, ?_, rfl⟩
      rw [Finset.mem_filter, unseenSet, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _,
        fun h => hvis ((isVisible_transfer hinj hiff hclosed i₀ w).mpr h)⟩,
        (hiff z w).mpr hadj⟩
    · intro hu
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      rw [Finset.mem_filter, unseenSet, Finset.mem_filter] at hw
      rw [Finset.mem_filter, unseenSet, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _,
        fun h => hw.1.2 ((isVisible_transfer hinj hiff hclosed i₀ w).mp h)⟩,
        (hiff z w).mp hw.2⟩
  rw [unseenDeg, unseenDeg, himg, Finset.card_image_of_injective _ hinj]

/-- `d̂` transfers. -/
theorem dhat_transfer
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (a i₀ z : Fin H.size) :
    dhat G (φ a) (φ i₀) (φ z) = dhat H a i₀ z := by
  rw [dhat, dhat, visibleDeg_transfer hinj hiff hclosed a i₀ z,
    unseenDeg_transfer hinj hiff hclosed i₀ z]

/-- The visible charge at a single neighbour is invariant. -/
theorem visibleCharge_transfer
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (a i₀ : Fin H.size) :
    visibleCharge G (φ a) (φ i₀) = visibleCharge H a i₀ := by
  rw [visibleCharge, visibleCharge, visibleAvoid_image hinj hiff hclosed a i₀,
    Finset.sum_image hinj.injOn]
  exact Finset.sum_congr rfl fun z _ => by
    rw [dhat_transfer hinj hiff hclosed a i₀ z,
      avoidAttach_transfer hinj hiff hclosed a i₀ z]

/-- **T4.**  The total visible charge is invariant along a closed induced embedding. -/
theorem visibleChargeTotal_transfer
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (i₀ : Fin H.size) :
    visibleChargeTotal G (φ i₀) = visibleChargeTotal H i₀ := by
  rw [visibleChargeTotal, visibleChargeTotal, rootNbrs_image hiff hclosed i₀,
    Finset.sum_image hinj.injOn]
  exact Finset.sum_congr rfl fun a _ => visibleCharge_transfer hinj hiff hclosed a i₀

end Transfer4


/-! ### The payoff: the whole `henum` row is an invariant of the closed induced image -/

section Row

variable {H G : Flag emptyType} {φ : Fin H.size → Fin G.size}

/-- **The `henum` row transfers, gate and all.**  Both the `19 ≤ T(v)` hypothesis and the
    conclusion `D^vis + 12·T ≤ credit + 212` are invariant along a closed induced embedding,
    so the row holds at `φ i₀` in `G` iff it holds at `i₀` in `H`.  This is the invariance
    half of the collapse of the `∀ H` in `pentagon_bound_delta4_of_visible_enumeration`; the
    remaining half is realizing every bounded local configuration by some `H`. -/
theorem visibleRow_transfer
    (hinj : Function.Injective φ)
    (hiff : ∀ i j, H.graph.Adj i j ↔ G.graph.Adj (φ i) (φ j))
    (hclosed : ∀ i u, G.graph.Adj (φ i) u → ∃ j, φ j = u)
    (i₀ : Fin H.size) :
    ((19 ≤ ∑ p ∈ shellPairsLt G (φ i₀),
          (attachSet G (φ i₀) p.1).card * (attachSet G (φ i₀) p.2).card) →
        visibleChargeTotal G (φ i₀)
            + 12 * (∑ p ∈ shellPairsLt G (φ i₀),
                (attachSet G (φ i₀) p.1).card * (attachSet G (φ i₀) p.2).card)
          ≤ visibleCreditTotal G (φ i₀) + 212)
      ↔ ((19 ≤ ∑ p ∈ shellPairsLt H i₀,
            (attachSet H i₀ p.1).card * (attachSet H i₀ p.2).card) →
          visibleChargeTotal H i₀
              + 12 * (∑ p ∈ shellPairsLt H i₀,
                  (attachSet H i₀ p.1).card * (attachSet H i₀ p.2).card)
            ≤ visibleCreditTotal H i₀ + 212) := by
  rw [shellObjective_transfer hinj hiff hclosed i₀,
    visibleChargeTotal_transfer hinj hiff hclosed i₀,
    visibleCreditTotal_transfer hinj hiff hclosed i₀]

end Row

/-! ### The visible set decomposes into a root part and a shell part

`K_a = visibleAvoid G a v` splits into the root neighbours other than `a` that carry positive
punctured attachment, and the positive shell vertices non-adjacent to `a` that do — and the
two parts are disjoint.

**This is the gate the model transport waits on.**  It says `K_a ⊆ N(v) ∪ S⁺`, so the visible
set never escapes radius two.  Had it escaped, the finite model would have had to reach radius
three and the transport design would be wrong.  Verified over 190,878 root-neighbour pairs of
triangle-free graphs of maximum degree at most four — including non-regular and disconnected
hosts, since neither statement assumes regularity or connectivity — with zero escapes, zero
decomposition failures and zero disjointness failures.

Triangle-freeness is load-bearing and is consumed exactly twice, both in the `⊇` direction and
both killing the triangle `v–a–z`: once to get `¬Adj v z` from `Adj v a, Adj a z`, and once in
the root branch to get `¬Adj a z` from `Adj v a, Adj v z`.  Dropping it breaks both statements
on thousands of small hosts.  The `⊆` direction needs no triangle-freeness at all — only
`z ≠ v`, which follows from `z ∈ shellSet G a` with `Adj v a`.  Disjointness needs no
hypothesis whatever.

Note `visibleAvoid_subset_rootNbrs_union_shellPos` is strictly sharper than the earlier
`visibleAvoid_subset_ball2`: `ball2` also contains the root `v`, which `K_a` never does. -/

/-- Membership in the root neighbourhood, unfolded. -/
lemma mem_rootNbrs {v b : Fin G.size} : b ∈ rootNbrs G v ↔ G.graph.Adj v b := by
  rw [rootNbrs, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-! ### Obligation 2 -/

/-- **Every neighbour of a root neighbour, other than the root itself, lies in `S⁺(v)`.**
    Triangle-freeness gives `¬ Adj v z` (so `z` is in the shell) and the witness `a` gives
    the positive attachment. -/
theorem nbr_of_rootNbr_mem_shellPos (hTF : IsTriangleFree G) {v a z : Fin G.size}
    (hva : G.graph.Adj v a) (haz : G.graph.Adj a z) (hzv : z ≠ v) :
    z ∈ PentagonLocal.shellPos G v := by
  have hvz : ¬ G.graph.Adj v z := fun h => hTF v a z hva haz h
  refine mem_shellPos.mpr ⟨mem_shellSet'.mpr ⟨hzv, hvz⟩, ?_⟩
  have hmem : a ∈ attachSet G v z := by
    rw [attachSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hva, haz.symm⟩
  exact Finset.card_pos.mpr ⟨a, hmem⟩

/-! ### Obligation 3 -/

/-- **The decomposition of `K_a`.**  `visibleAvoid G a v` is exactly the positive-weight
    part of `(N(v) \ {a}) ∪ (S⁺(v) \ N(a))`.  Both blocks live inside the radius-2 ball at
    the root, so `K_a` never reaches the third layer. -/
theorem visibleAvoid_eq (hTF : IsTriangleFree G) {a v : Fin G.size}
    (hav : G.graph.Adj v a) :
    PentagonLocal.visibleAvoid G a v
      = ((PentagonLocal.rootNbrs G v).erase a).filter
            (fun b => 1 ≤ (PentagonLocal.avoidAttach G a v b).card)
        ∪ ((PentagonLocal.shellPos G v).filter (fun y => ¬ G.graph.Adj a y)).filter
            (fun y => 1 ≤ (PentagonLocal.avoidAttach G a v y).card) := by
  ext z
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
  constructor
  · intro hz
    obtain ⟨hzS, hvis⟩ := mem_visibleAvoid.mp hz
    obtain ⟨hzSa, hpos⟩ := mem_shellPosAvoid.mp hzS
    obtain ⟨hza, hnaz⟩ := mem_shellSet'.mp hzSa
    by_cases hvz : G.graph.Adj v z
    · exact Or.inl ⟨⟨hza, mem_rootNbrs.mpr hvz⟩, hpos⟩
    · -- not adjacent to the root, so visibility is a positive root attachment
      have hattach : 1 ≤ (attachSet G v z).card := hvis.resolve_left hvz
      -- `z ≠ v` because `z` misses `a` while the root meets it
      have hzv : z ≠ v := fun h => hnaz (h ▸ hav.symm)
      exact Or.inr ⟨⟨mem_shellPos.mpr ⟨mem_shellSet'.mpr ⟨hzv, hvz⟩, hattach⟩, hnaz⟩, hpos⟩
  · rintro (⟨⟨hza, hzN⟩, hpos⟩ | ⟨⟨hzSp, hnaz⟩, hpos⟩)
    · -- root block: triangle-freeness supplies `¬ Adj a z`
      have hvz : G.graph.Adj v z := mem_rootNbrs.mp hzN
      have hnaz : ¬ G.graph.Adj a z := fun h => hTF a v z hav.symm hvz h
      exact mem_visibleAvoid.mpr
        ⟨mem_shellPosAvoid.mpr ⟨mem_shellSet'.mpr ⟨hza, hnaz⟩, hpos⟩, Or.inl hvz⟩
    · -- shell block: `z ≠ a` because `z` misses the root while `a` meets it
      have hzS := mem_shellPos.mp hzSp
      have hvz : ¬ G.graph.Adj v z := (mem_shellSet'.mp hzS.1).2
      have hza : z ≠ a := fun h => hvz (h ▸ hav)
      exact mem_visibleAvoid.mpr
        ⟨mem_shellPosAvoid.mpr ⟨mem_shellSet'.mpr ⟨hza, hnaz⟩, hpos⟩, Or.inr hzS.2⟩

/-- **The two blocks are disjoint**, so `visibleAvoid_eq` is a partition: the root block
    is adjacent to `v` and the shell block is not. -/
theorem visibleAvoid_decomp_disjoint {a v : Fin G.size} :
    Disjoint
      (((PentagonLocal.rootNbrs G v).erase a).filter
          (fun b => 1 ≤ (PentagonLocal.avoidAttach G a v b).card))
      (((PentagonLocal.shellPos G v).filter (fun y => ¬ G.graph.Adj a y)).filter
          (fun y => 1 ≤ (PentagonLocal.avoidAttach G a v y).card)) := by
  rw [Finset.disjoint_left]
  intro z h1 h2
  simp only [Finset.mem_filter, Finset.mem_erase] at h1 h2
  exact (mem_shellSet'.mp (mem_shellPos.mp h2.1.1).1).2 (mem_rootNbrs.mp h1.1.2)

/-- **The gate, stated as the containment it was asked for.**  `K_a` lives in
    `N(v) ∪ S⁺(v)`: no third-layer vertex is ever visible from the root through `a`. -/
theorem visibleAvoid_subset_rootNbrs_union_shellPos (hTF : IsTriangleFree G)
    {a v : Fin G.size} (hav : G.graph.Adj v a) :
    PentagonLocal.visibleAvoid G a v ⊆ rootNbrs G v ∪ shellPos G v := by
  rw [visibleAvoid_eq hTF hav]
  refine Finset.union_subset (fun z hz => ?_) (fun z hz => ?_)
  · exact Finset.mem_union_left _ (Finset.mem_of_mem_erase (Finset.mem_filter.mp hz).1)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1

/-- The cardinality form the transport sums consume: the two blocks add. -/
theorem card_visibleAvoid_eq (hTF : IsTriangleFree G) {a v : Fin G.size}
    (hav : G.graph.Adj v a) :
    (PentagonLocal.visibleAvoid G a v).card
      = (((PentagonLocal.rootNbrs G v).erase a).filter
            (fun b => 1 ≤ (PentagonLocal.avoidAttach G a v b).card)).card
        + (((PentagonLocal.shellPos G v).filter (fun y => ¬ G.graph.Adj a y)).filter
            (fun y => 1 ≤ (PentagonLocal.avoidAttach G a v y).card)).card := by
  rw [visibleAvoid_eq hTF hav, Finset.card_union_of_disjoint visibleAvoid_decomp_disjoint]

/-- The sum form: any `K_a`-indexed sum splits along the decomposition.  This is the shape
    obligations 12 and 13 (`transport_credit`, `transport_charge`) actually consume. -/
theorem sum_visibleAvoid_eq (hTF : IsTriangleFree G) {a v : Fin G.size}
    (hav : G.graph.Adj v a) (f : Fin G.size → ℕ) :
    ∑ z ∈ PentagonLocal.visibleAvoid G a v, f z
      = ∑ z ∈ ((PentagonLocal.rootNbrs G v).erase a).filter
            (fun b => 1 ≤ (PentagonLocal.avoidAttach G a v b).card), f z
        + ∑ z ∈ ((PentagonLocal.shellPos G v).filter (fun y => ¬ G.graph.Adj a y)).filter
            (fun y => 1 ≤ (PentagonLocal.avoidAttach G a v y).card), f z := by
  rw [visibleAvoid_eq hTF hav, Finset.sum_union visibleAvoid_decomp_disjoint]

end PentagonLocal

/-- **Per-vertex pentagon bound at Δ ≤ 4.** -/
theorem pentagonCountAt_le_24_of_maxDegree_le_four :
    ∀ G : Flag emptyType, IsTriangleFree G → maxDegree G ≤ 4 →
      ∀ v : Fin G.size, pentagonCountAt G v ≤ 24 :=
  fun G hTF hd v => PentagonLocal.pentagonCountAt_le_24 G hTF hd v

/-- **Pentagon density bound at Δ = 4** (the local-method bound): every triangle-free graph
    of maximum degree at most 4 has `5·P(G) ≤ 24·|G|`, i.e. `P(G) ≤ 24|G|/5`.
    The sharp bound is `P ≤ 4|G|` (ratio `1/64`, attained by `C₁₂(2,3)` and `C₁₃(2,3)`),
    proved as `Delta4Gen.pentagon_bound_delta4_sharp` in `DaveyThesis2024/Delta4/`; the gap
    reflects the per-vertex method's intrinsic looseness at Δ = 4, not a defect of this
    proof. -/
theorem pentagon_bound_delta4 (G : Flag emptyType)
    (hTF : IsTriangleFree G) (hdeg : maxDegree G ≤ 4) :
    5 * pentagonCount G ≤ 24 * G.size := by
  rw [← pentagonCount_sum]
  calc ∑ v : Fin G.size, pentagonCountAt G v
      ≤ ∑ _v : Fin G.size, 24 :=
        Finset.sum_le_sum fun v _ =>
          pentagonCountAt_le_24_of_maxDegree_le_four G hTF hdeg v
    _ = 24 * G.size := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          Nat.mul_comm]

/-! ## Exact bridge from the degree-four rerooting row

The candidate local row is the specialization of `pentagonQ` at degree four:
`4 * P(G,v) + sum_{u~v} P(G,u) <= 160`.  Summing it in a 4-regular graph gives
`40 * P(G) <= 160 * |G|`.  The second theorem combines this identity with the
already formalized regularization reduction, so proving the row only for
4-regular graphs is sufficient for the sharp maximum-degree-four theorem.
-/

/-- In a 4-regular graph, the pointwise `pentagonQ <= 160` row implies
    `P(G) <= 4|G|`.  Triangle-freeness is not needed for this summation bridge;
    it belongs in the hypothesis used to establish the local row. -/
theorem pentagon_bound_delta4_of_regular_transport (G : Flag emptyType)
    (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    (htransport : ∀ v : Fin G.size, pentagonQ G v ≤ 160) :
    pentagonCount G ≤ 4 * G.size := by
  have hsum : (Finset.univ : Finset (Fin G.size)).sum (pentagonQ G)
      ≤ ∑ _v : Fin G.size, (160 : ℝ) :=
    Finset.sum_le_sum fun v _ => htransport v
  have hleft : (Finset.univ : Finset (Fin G.size)).sum (pentagonQ G) =
      40 * (pentagonCount G : ℝ) := by
    rw [pentagon_Q_sum G hReg, hdeg]
    norm_num
  have hright : (∑ _v : Fin G.size, (160 : ℝ)) = 160 * G.size := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hleft, hright] at hsum
  have hreal : (pentagonCount G : ℝ) ≤ 4 * G.size := by linarith
  exact_mod_cast hreal

/-- **Conditional sharp degree-four theorem.**  It is enough to prove the
    `pentagonQ <= 160` row on triangle-free 4-regular graphs.  The existing
    iterated-doubling regularization transfers the resulting density bound to
    every triangle-free graph of maximum degree at most four; the degree-at-most
    three branch is already stronger by `pentagon_bound_delta3`. -/
theorem pentagon_bound_delta4_of_regular_transport_family
    (htransport : ∀ H : Flag emptyType, IsTriangleFree H → IsRegular H →
      maxDegree H = 4 → ∀ v : Fin H.size, pentagonQ H v ≤ 160)
    (G : Flag emptyType) (hTF : IsTriangleFree G) (hdeg : maxDegree G ≤ 4) :
    pentagonCount G ≤ 4 * G.size := by
  classical
  by_cases hsmall : maxDegree G ≤ 3
  · have h3 := pentagon_bound_delta3 G hTF hsmall
    omega
  have heq : maxDegree G = 4 := by omega
  obtain ⟨H, hHTF, hHReg, hHdeg, hratio⟩ := pentagon_regular_suffices G hTF
  have hHdeg4 : maxDegree H = 4 := by omega
  have hHbound : pentagonCount H ≤ 4 * H.size :=
    pentagon_bound_delta4_of_regular_transport H hHReg hHdeg4
      (htransport H hHTF hHReg hHdeg4)
  have hmaxle : maxDegree H ≤ H.size := by
    unfold maxDegree
    apply Finset.sup_le
    intro v _
    calc
      (Finset.univ.filter (fun u => H.graph.Adj v u)).card
          ≤ (Finset.univ : Finset (Fin H.size)).card := Finset.card_filter_le _ _
      _ = H.size := by rw [Finset.card_univ, Fintype.card_fin]
  have hHsize : 0 < H.size := by omega
  have hHboundReal : (pentagonCount H : ℝ) ≤ 4 * H.size := by
    exact_mod_cast hHbound
  have hHsizeReal : 0 < (H.size : ℝ) := by exact_mod_cast hHsize
  have hGsizeNonneg : 0 ≤ (G.size : ℝ) := Nat.cast_nonneg _
  have hreal : (pentagonCount G : ℝ) ≤ 4 * G.size := by
    nlinarith
  exact_mod_cast hreal

section QSplit

open Finset
open scoped Classical
open PentagonLocal

variable {G : Flag emptyType}

/-! ## The `Q`-split: `Q(v) = 6·p(v) + Σ_{a ∈ N(v)} r_a`

An induced `C₅` through `v` contains exactly two neighbours of `v`, so summing the
"pentagons through both `v` and `a`" counts over `a ∈ N(v)` double counts the pentagons
through `v`.  That collapses the rerooting row to a root term and a sum of *punctured*
neighbour counts, which is the shape the shell analysis bounds. -/


/-- An induced `C₅` through `v` meets `N(v)` in exactly two vertices: the two cycle
    neighbours of `v`.  The remaining two vertices of the pentagon are non-adjacent
    to `v` precisely because the `C₅` is *induced*. -/
theorem pentagon_neighbours_card_eq_two (hTF : IsTriangleFree G)
    {S : Finset (Fin G.size)} (hS : IsPentagon G S) {v : Fin G.size} (hv : v ∈ S) :
    (S.filter fun a => G.graph.Adj v a).card = 2 := by
  classical
  obtain ⟨a, b, x, y, hxylt, hxy, hxsh, hysh, hamem, hbmem, hfilxy, hfa, hfb, hS5⟩ :=
    pentagon_decomp hTF hS hv
  -- unpack the memberships
  have hva : G.graph.Adj v a := by
    rw [attachSet, Finset.mem_filter] at hamem; exact hamem.2.1
  have hvb : G.graph.Adj v b := by
    rw [attachSet, Finset.mem_filter] at hbmem; exact hbmem.2.1
  have hnvx : ¬ G.graph.Adj v x := by
    rw [shellSet, Finset.mem_filter] at hxsh; exact hxsh.2.2
  have hnvy : ¬ G.graph.Adj v y := by
    rw [shellSet, Finset.mem_filter] at hysh; exact hysh.2.2
  -- `a ≠ b`, from the fact that `S` has five elements
  have hab : a ≠ b := by
    intro h
    subst h
    have hsub : ({v, a, x, y, a} : Finset (Fin G.size)) ⊆ ({v, a, x, y} : Finset _) := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
      rcases hu with rfl | rfl | rfl | rfl | rfl <;> tauto
    have h5 : S.card = 5 := IsPentagon.card_eq_five hS
    have c1 : ({y} : Finset (Fin G.size)).card = 1 := Finset.card_singleton _
    have c2 := Finset.card_insert_le x ({y} : Finset (Fin G.size))
    have c3 := Finset.card_insert_le a (insert x {y} : Finset (Fin G.size))
    have c4 := Finset.card_insert_le v (insert a (insert x {y}) : Finset (Fin G.size))
    have c5 : S.card ≤ ({v, a, x, y} : Finset (Fin G.size)).card := by
      rw [hS5]; exact Finset.card_le_card hsub
    simp only [Finset.insert_eq] at *
    omega
  -- the neighbour trace of `S` is exactly `{a, b}`
  have hset : (S.filter fun u => G.graph.Adj v u) = {a, b} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hu, hadj⟩
      rw [hS5] at hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact absurd hadj G.graph.irrefl
      · exact Or.inl rfl
      · exact absurd hadj hnvx
      · exact absurd hadj hnvy
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · refine ⟨?_, hva⟩
        rw [hS5]; simp
      · refine ⟨?_, hvb⟩
        rw [hS5]; simp
  rw [hset, Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]

/-- Splitting the pentagons through `a` by whether they contain `v`. -/
theorem pentagonCountAt_split_at_neighbour (v a : Fin G.size) :
    pentagonCountAt G a
      = (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∈ S)).card
        + (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)).card := by
  classical
  have hunion : (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S))
      = (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∈ S))
        ∪ (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)) := by
    ext S
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hvS : v ∈ S
      · exact Or.inl ⟨h1, h2, hvS⟩
      · exact Or.inr ⟨h1, h2, hvS⟩
    · rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> exact ⟨h1, h2⟩
  have hdisj : Disjoint (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∈ S))
      (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)) := by
    rw [Finset.disjoint_left]
    intro S hS1 hS2
    rw [Finset.mem_filter] at hS1 hS2
    exact hS2.2.2.2 hS1.2.2.2
  rw [pentagonCountAt, hunion, Finset.card_union_of_disjoint hdisj]

/-- **Double counting the incidences `(a, S)` with `a ∈ N(v)`, `v ∈ S`.**
    Each pentagon through `v` contributes exactly its two `N(v)`-vertices. -/
theorem sum_edge_pentagons_eq_two_mul (hTF : IsTriangleFree G) (v : Fin G.size) :
    ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
        (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∈ S)).card
      = 2 * pentagonCountAt G v := by
  classical
  have key : ∀ S : Finset (Fin G.size),
      ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
          (if IsPentagon G S ∧ a ∈ S ∧ v ∈ S then 1 else 0)
        = (if IsPentagon G S ∧ v ∈ S then 2 else 0) := by
    intro S
    by_cases hc : IsPentagon G S ∧ v ∈ S
    · rw [if_pos hc]
      have hterm : ∀ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
          (if IsPentagon G S ∧ a ∈ S ∧ v ∈ S then 1 else 0)
            = (if a ∈ S then (1 : ℕ) else 0) := by
        intro a _
        by_cases ha : a ∈ S
        · rw [if_pos ⟨hc.1, ha, hc.2⟩, if_pos ha]
        · rw [if_neg (by tauto), if_neg ha]
      rw [Finset.sum_congr rfl hterm, ← Finset.card_filter]
      have hset : (Finset.univ.filter (fun a => G.graph.Adj v a)).filter (fun a => a ∈ S)
          = S.filter (fun a => G.graph.Adj v a) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      rw [hset]
      exact pentagon_neighbours_card_eq_two hTF hc.1 hc.2
    · rw [if_neg hc]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [if_neg (by tauto)]
  calc ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
          (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∈ S)).card
      = ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
          ∑ S : Finset (Fin G.size),
            (if IsPentagon G S ∧ a ∈ S ∧ v ∈ S then 1 else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.card_filter]
    _ = ∑ S : Finset (Fin G.size),
          ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
            (if IsPentagon G S ∧ a ∈ S ∧ v ∈ S then 1 else 0) := Finset.sum_comm
    _ = ∑ S : Finset (Fin G.size), (if IsPentagon G S ∧ v ∈ S then 2 else 0) :=
        Finset.sum_congr rfl fun S _ => key S
    _ = 2 * pentagonCountAt G v := by
        rw [pentagonCountAt, Finset.card_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        by_cases hc : IsPentagon G S ∧ v ∈ S
        · rw [if_pos hc, if_pos hc, Nat.mul_one]
        · rw [if_neg hc, if_neg hc, Nat.mul_zero]

/-- **The Q-split on a 4-regular graph.**
    `Q(v) = 6·p(v) + Σ_{a ∈ N(v)} r_a`, with `r_a` the number of pentagons through
    `a` that avoid `v`. -/
theorem pentagonQ_eq_six_mul_add_avoid (hTF : IsTriangleFree G) (hdeg : maxDegree G = 4)
    (v : Fin G.size) :
    pentagonQ G v
      = 6 * (pentagonCountAt G v : ℝ)
        + ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
            ((Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)).card : ℝ) := by
  classical
  rw [pentagonQ, hdeg]
  have hsplit : ∀ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
      (pentagonCountAt G a : ℝ)
        = ((Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∈ S)).card : ℝ)
          + ((Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)).card : ℝ) := by
    intro a _
    have := pentagonCountAt_split_at_neighbour (G := G) v a
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have h2 : ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
      ((Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∈ S)).card : ℝ)
      = 2 * (pentagonCountAt G v : ℝ) := by
    have := sum_edge_pentagons_eq_two_mul hTF v
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this
  rw [h2]
  push_cast
  ring

/-- **The low branch of the degree-four row.**  If the root lies on at most eighteen
    pentagons and each of its neighbours lies on at most thirteen pentagons avoiding it,
    then the rerooting row holds: `6·18 + 4·13 = 160`.

    Regularity is *not* needed.  `maxDegree G = 4` already caps `|N(v)|` at four, which is
    all the sum needs; requiring `IsRegular` would only shrink the class the lemma applies
    to.  Triangle-freeness enters solely through the `Q`-split identity. -/
theorem pentagonQ_le_160_of_le_eighteen (hTF : IsTriangleFree G)
    (hdeg : maxDegree G = 4) (v : Fin G.size)
    (hp : pentagonCountAt G v ≤ 18)
    (havoid : ∀ a, G.graph.Adj v a →
      (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)).card ≤ 13) :
    pentagonQ G v ≤ 160 := by
  classical
  rw [pentagonQ_eq_six_mul_add_avoid hTF hdeg v]
  have hcard : (Finset.univ.filter (fun a => G.graph.Adj v a)).card ≤ 4 := by
    have h := Finset.le_sup (f := fun w : Fin G.size =>
      (Finset.univ.filter (fun u => G.graph.Adj w u)).card) (Finset.mem_univ v)
    rw [← maxDegree, hdeg] at h
    exact h
  have hcard' : ((Finset.univ.filter (fun a => G.graph.Adj v a)).card : ℝ) ≤ 4 := by
    exact_mod_cast hcard
  have hsum : ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
      ((Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)).card : ℝ) ≤ 52 := by
    calc ∑ a ∈ Finset.univ.filter (fun a => G.graph.Adj v a),
            ((Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)).card : ℝ)
        ≤ ∑ _a ∈ Finset.univ.filter (fun a => G.graph.Adj v a), (13 : ℝ) := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [Finset.mem_filter] at ha
          exact_mod_cast havoid a ha.2
      _ ≤ 52 := by rw [Finset.sum_const, nsmul_eq_mul]; nlinarith
  have hp' : (pentagonCountAt G v : ℝ) ≤ 18 := by exact_mod_cast hp
  linarith

/-- **The low branch, driven by the shell objective.**  The fibre bound `p(v) ≤ T(v)`
    turns the hypothesis of the previous theorem into a condition on the shell objective,
    which is the quantity the high-root classification actually splits on.  Together with
    the `T(v) ≥ 19` case this is a complete case distinction: the certificate enumeration
    covers exactly the objectives `19, 20, 21, 24`. -/
theorem pentagonQ_le_160_of_shellObjective_le_eighteen (hTF : IsTriangleFree G)
    (hdeg : maxDegree G = 4) (v : Fin G.size)
    (hT : ∑ p ∈ PentagonLocal.shellPairsLt G v,
        (PentagonLocal.attachSet G v p.1).card * (PentagonLocal.attachSet G v p.2).card ≤ 18)
    (havoid : ∀ a, G.graph.Adj v a →
      (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)).card ≤ 13) :
    pentagonQ G v ≤ 160 := by
  refine pentagonQ_le_160_of_le_eighteen hTF hdeg v ?_ havoid
  exact le_trans (PentagonLocal.pentagonCountAt_le_sum hTF (by rw [hdeg]; norm_num) v) hT

/-- **The low branch with the neighbour bound discharged.**  `r_a ≤ 13` is a theorem, so
    the only remaining hypothesis of the low branch is the objective bound itself. -/
theorem pentagonQ_le_160_of_shellObjective_le_eighteen' (hTF : IsTriangleFree G)
    (hdeg : maxDegree G = 4) (v : Fin G.size)
    (hT : ∑ p ∈ PentagonLocal.shellPairsLt G v,
        (PentagonLocal.attachSet G v p.1).card * (PentagonLocal.attachSet G v p.2).card ≤ 18) :
    pentagonQ G v ≤ 160 :=
  pentagonQ_le_160_of_shellObjective_le_eighteen hTF hdeg v hT fun _a hva =>
    PentagonLocal.pentagonCountAt_avoid_le_thirteen hTF (le_of_eq hdeg) hva.symm

end QSplit

/-! ## The high-root branch of the transport row

With conservativity in hand the whole Δ = 4 row reduces to one inequality about the visible
defect at high roots.  The census input `D^vis ≥ 12T − 212` appears subtraction-free as
`visibleChargeTotal + 12·T ≤ visibleCreditTotal + 212`.

**Verified numerically before and after formalising.**  Over the 268 connected triangle-free
4-regular graphs on 8–14 vertices — 3,677 roots, 14,708 root-neighbour pairs — the pointwise
lemma, `conservativity_at`, `conservativity_total` and the census hypothesis all hold with
zero violations, and `Q(v) ≤ 160` is never violated.  The chain is tight end to end: on
`C₁₂(2,3)`, `C₁₃(1,5)` and `C₁₃(2,3)` the census hypothesis is an *equality*
(`80 + 12·20 = 320 = 108 + 212`), the pointwise slack `d̂ − d_J` is identically zero at every
shell vertex, and `Q(v) = 160` is attained at every vertex.  3,553 of the 3,677 roots fall in
the low branch; 124 need this one. -/

section HighRootBranch

open Finset
open scoped Classical
open PentagonLocal

variable {G : Flag emptyType}

/-- `r_a ≤ T_a`: the punctured pentagon count at a neighbour is at most the punctured
    shell objective there.  `pentagonCountAt_avoid_le_sum` with the zero terms discarded
    by `sum_avoid_restrict`. -/
theorem avoid_count_le_avoidObjective (hTF : IsTriangleFree G) (v a : Fin G.size) :
    (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)).card
      ≤ avoidObjective G a v := by
  have h := pentagonCountAt_avoid_le_sum hTF v a
  rwa [sum_avoid_restrict a v] at h

/-- **The high-root branch of the degree-four transport row.** -/
theorem pentagonQ_le_160_of_visible_bound (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size)
    (henum : visibleChargeTotal G v
        + 12 * (∑ p ∈ PentagonLocal.shellPairsLt G v,
            (PentagonLocal.attachSet G v p.1).card * (PentagonLocal.attachSet G v p.2).card)
        ≤ visibleCreditTotal G v + 212) :
    pentagonQ G v ≤ 160 := by
  classical
  set T := ∑ p ∈ PentagonLocal.shellPairsLt G v,
    (PentagonLocal.attachSet G v p.1).card * (PentagonLocal.attachSet G v p.2).card with hT
  have hcons := conservativity_total hTF hReg hdeg v
  have hp : pentagonCountAt G v ≤ T :=
    pentagonCountAt_le_sum hTF (by rw [hdeg]; norm_num) v
  have hra : ∑ a ∈ rootNbrs G v,
        (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)).card
      ≤ ∑ a ∈ rootNbrs G v, avoidObjective G a v :=
    Finset.sum_le_sum fun a _ => avoid_count_le_avoidObjective hTF v a
  have hnat : 6 * pentagonCountAt G v
      + ∑ a ∈ rootNbrs G v,
          (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)).card ≤ 160 := by
    omega
  rw [pentagonQ_eq_six_mul_add_avoid hTF hdeg v]
  have hcast : ((6 * pentagonCountAt G v
      + ∑ a ∈ rootNbrs G v,
          (Finset.univ.filter (fun S => IsPentagon G S ∧ a ∈ S ∧ v ∉ S)).card : ℕ) : ℝ)
      ≤ (160 : ℝ) := by exact_mod_cast hnat
  push_cast at hcast
  exact hcast

/-- **Both branches merged.**  The low branch (`shell objective ≤ 18`) is already a
    theorem, so the only thing the transport row still waits on is the enumeration
    hypothesis on the high roots. -/
theorem pentagonQ_le_160_of_visible_bound_high (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size)
    (henum : 19 ≤ (∑ p ∈ PentagonLocal.shellPairsLt G v,
          (PentagonLocal.attachSet G v p.1).card * (PentagonLocal.attachSet G v p.2).card) →
        visibleChargeTotal G v
          + 12 * (∑ p ∈ PentagonLocal.shellPairsLt G v,
              (PentagonLocal.attachSet G v p.1).card
                * (PentagonLocal.attachSet G v p.2).card)
          ≤ visibleCreditTotal G v + 212) :
    pentagonQ G v ≤ 160 := by
  by_cases h : (∑ p ∈ PentagonLocal.shellPairsLt G v,
      (PentagonLocal.attachSet G v p.1).card
        * (PentagonLocal.attachSet G v p.2).card) ≤ 18
  · exact pentagonQ_le_160_of_shellObjective_le_eighteen' hTF hdeg v h
  · exact pentagonQ_le_160_of_visible_bound hTF hReg hdeg v (henum (by omega))

/-- **The sharp Δ = 4 pentagon bound, conditional on the high-root visible-defect
    inequality.**  `P(G) ≤ 4|G|` for every triangle-free graph of maximum degree at most
    four, given that inequality at every high root of every triangle-free 4-regular graph.

    **Read the hypothesis carefully: it is NOT a finite check.**  `henum` quantifies over
    *all* triangle-free 4-regular `H : Flag emptyType`, of every order, and over every vertex
    of each.  Nothing here reduces it to a finite statement.  That reduction — showing the
    quantity depends only on a bounded neighbourhood, so the `∀ H` collapses to an
    enumeration over finitely many local configurations — is the model-transport stage, and
    it is **not done**.  The census enumeration alone does not discharge this hypothesis
    without it.

    What this theorem does establish is that the *analytic* layer is complete: no further
    counting, identity or inequality about pentagons is needed, only the transport. -/
theorem pentagon_bound_delta4_of_visible_enumeration
    (henum : ∀ H : Flag emptyType, IsTriangleFree H → IsRegular H → maxDegree H = 4 →
      ∀ v : Fin H.size,
        19 ≤ (∑ p ∈ PentagonLocal.shellPairsLt H v,
            (PentagonLocal.attachSet H v p.1).card
              * (PentagonLocal.attachSet H v p.2).card) →
        visibleChargeTotal H v
          + 12 * (∑ p ∈ PentagonLocal.shellPairsLt H v,
              (PentagonLocal.attachSet H v p.1).card
                * (PentagonLocal.attachSet H v p.2).card)
          ≤ visibleCreditTotal H v + 212)
    (G : Flag emptyType) (hTF : IsTriangleFree G) (hdeg : maxDegree G ≤ 4) :
    pentagonCount G ≤ 4 * G.size :=
  pentagon_bound_delta4_of_regular_transport_family
    (fun H hHTF hHReg hHdeg v =>
      pentagonQ_le_160_of_visible_bound_high hHTF hHReg hHdeg v (henum H hHTF hHReg hHdeg v))
    G hTF hdeg

end HighRootBranch

end Davey2024
