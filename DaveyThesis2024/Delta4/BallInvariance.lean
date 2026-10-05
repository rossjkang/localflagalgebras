import DaveyThesis2024.PentagonDelta4

/-!
# Δ = 4: invariance of the transport row under a rooted radius-2 ball isomorphism

The step the model transport actually needs, and the one two independent verifiers identified
after the earlier `visibleRow_transfer` turned out to give only *component* invariance.

Ball isomorphism alone does **not** suffice without a degree hypothesis: two triangle-free
graphs can have identical rooted induced balls and still differ in `visibleChargeTotal`,
because `unseenDeg` reads distance three, which the ball cannot see.  Under `4`-regularity it
does suffice, and the bridge is `unseenDeg_add_attach_add_shellPosDeg_eq_four`, which makes the
unseen count a ball-internal slot count.  So everything below routes through `dhat_eq_local`
and `unseenDeg` never appears.
-/

namespace Davey2024

namespace PentagonLocal

open Finset
open scoped Classical

/-! ## 0.  Ball support lemmas that do not need triangle-freeness

`nbr_of_rootNbr_mem_shellPos` needs `hTF` because it lands in `shellPos`.  For the ball the
`hTF` is unnecessary: a neighbour `z` of a root neighbour `a` is `v`, or a neighbour of `v`,
or a shell vertex with `a` as an attachment witness — and all three are in `ball2 G v`. -/

section Support

variable {G : Flag emptyType}

theorem mem_ball2_self (v : Fin G.size) : v ∈ ball2 G v := mem_ball2.mpr (Or.inl rfl)

theorem mem_ball2_of_adj (v : Fin G.size) {z : Fin G.size} (h : G.graph.Adj v z) :
    z ∈ ball2 G v := mem_ball2.mpr (Or.inr (Or.inl h))

/-- **Every neighbour of a root neighbour lies in the radius-2 ball.**  Unlike
`nbr_of_rootNbr_mem_shellPos` this needs no triangle-freeness: the case `G.Adj v z` lands in
the neighbour layer instead of contradicting a triangle. -/
theorem mem_ball2_of_adj_rootNbr {v a z : Fin G.size}
    (hva : G.graph.Adj v a) (haz : G.graph.Adj a z) : z ∈ ball2 G v := by
  by_cases hzv : z = v
  · exact hzv ▸ mem_ball2_self v
  by_cases hvz : G.graph.Adj v z
  · exact mem_ball2_of_adj v hvz
  · refine mem_ball2.mpr (Or.inr (Or.inr (mem_shellPos.mpr ⟨mem_shellSet'.mpr ⟨hzv, hvz⟩, ?_⟩)))
    refine Finset.card_pos.mpr ⟨a, ?_⟩
    rw [attachSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hva, haz.symm⟩

/-- The attachment set is a subset of `N(v)`, hence of the ball. -/
theorem attachSet_subset_ball2 (v x : Fin G.size) : attachSet G v x ⊆ ball2 G v := by
  intro a ha
  rw [attachSet, Finset.mem_filter] at ha
  exact mem_ball2_of_adj v ha.2.1

/-- The punctured attachment set at a root neighbour is a subset of `N(a) ⊆ ball2 G v`. -/
theorem avoidAttach_subset_ball2 {a v : Fin G.size} (hva : G.graph.Adj v a) (z : Fin G.size) :
    avoidAttach G a v z ⊆ ball2 G v := by
  intro b hb
  rw [avoidAttach, Finset.mem_erase, attachSet, Finset.mem_filter] at hb
  exact mem_ball2_of_adj_rootNbr hva hb.2.2.1

end Support

/-! ## 1.  `K_a` is a ball filter

`visibleAvoid G a v` is cut out of the ball by four conditions each of which reads only
radius-2 data.  Two versions:

* `visibleAvoid_eq_ball2_filter` uses only `visibleAvoid_subset_ball2` and needs **no
  triangle-freeness**.  It is the workhorse below;
* `visibleAvoid_eq_visible_filter` uses the landed gate
  `visibleAvoid_subset_rootNbrs_union_shellPos`, which is sharper — it excludes the root —
  at the cost of `hTF`.  The sharpness is real but it is not what ball invariance needs:
  the invariance proof only ever has to *pull a member back*, and `ball2` is already an
  enclosing set for that.  The exclusion of the root is recorded separately as
  `root_notMem_visibleAvoid`; it is the fact that makes the model's split of `K_a` into a
  root block and a shell block exhaustive.
-/

section Filter

variable {G : Flag emptyType}

/-- **`K_a` is a filter of the ball.**  No triangle-freeness. -/
theorem visibleAvoid_eq_ball2_filter {a v : Fin G.size} (hav : G.graph.Adj v a) :
    visibleAvoid G a v
      = (ball2 G v).filter
          (fun z => z ≠ a ∧ ¬ G.graph.Adj a z ∧ 1 ≤ (avoidAttach G a v z).card
                      ∧ IsVisible G v z) := by
  ext z
  rw [Finset.mem_filter, mem_visibleAvoid, mem_shellPosAvoid, mem_shellSet']
  constructor
  · rintro ⟨⟨⟨hza, hnaz⟩, hpos⟩, hvis⟩
    refine ⟨?_, hza, hnaz, hpos, hvis⟩
    exact visibleAvoid_subset_ball2 hav
      (mem_visibleAvoid.mpr
        ⟨mem_shellPosAvoid.mpr ⟨mem_shellSet'.mpr ⟨hza, hnaz⟩, hpos⟩, hvis⟩)
  · rintro ⟨-, hza, hnaz, hpos, hvis⟩
    exact ⟨⟨⟨hza, hnaz⟩, hpos⟩, hvis⟩

/-- The same filter, taken over the **sharper** enclosing set supplied by the gate. -/
theorem visibleAvoid_eq_visible_filter (hTF : IsTriangleFree G) {a v : Fin G.size}
    (hav : G.graph.Adj v a) :
    visibleAvoid G a v
      = (rootNbrs G v ∪ shellPos G v).filter
          (fun z => z ≠ a ∧ ¬ G.graph.Adj a z ∧ 1 ≤ (avoidAttach G a v z).card
                      ∧ IsVisible G v z) := by
  ext z
  rw [Finset.mem_filter, mem_visibleAvoid, mem_shellPosAvoid, mem_shellSet']
  constructor
  · rintro ⟨⟨⟨hza, hnaz⟩, hpos⟩, hvis⟩
    refine ⟨?_, hza, hnaz, hpos, hvis⟩
    exact visibleAvoid_subset_rootNbrs_union_shellPos hTF hav
      (mem_visibleAvoid.mpr
        ⟨mem_shellPosAvoid.mpr ⟨mem_shellSet'.mpr ⟨hza, hnaz⟩, hpos⟩, hvis⟩)
  · rintro ⟨-, hza, hnaz, hpos, hvis⟩
    exact ⟨⟨⟨hza, hnaz⟩, hpos⟩, hvis⟩

/-- **The root is never visible through one of its own neighbours.**  This is the content of
the gate that `ball2` cannot express, and it is what makes the model's two-block split of
`K_a` exhaustive. -/
theorem root_notMem_visibleAvoid {a v : Fin G.size} (hav : G.graph.Adj v a) :
    v ∉ visibleAvoid G a v := by
  intro hv
  exact (mem_shellSet'.mp (mem_shellPosAvoid.mp (mem_visibleAvoid.mp hv).1).1).2 hav.symm

end Filter

/-! ## 2.  Rooted induced ball isomorphisms -/

/-- **A rooted induced isomorphism of radius-2 balls.**  `φ` is only ever constrained on
`ball2 G v`; it is a total function purely for convenience (`Fin H.size` is inhabited by
`w`, so any partial map extends). -/
structure BallIso (G H : Flag emptyType) (v : Fin G.size) (w : Fin H.size)
    (φ : Fin G.size → Fin H.size) : Prop where
  /-- the root goes to the root -/
  root : φ v = w
  /-- the ball maps into the ball -/
  maps : ∀ x, x ∈ ball2 G v → φ x ∈ ball2 H w
  /-- injective on the ball -/
  inj : ∀ x, x ∈ ball2 G v → ∀ y, y ∈ ball2 G v → φ x = φ y → x = y
  /-- onto the ball -/
  surj : ∀ y, y ∈ ball2 H w → ∃ x, x ∈ ball2 G v ∧ φ x = y
  /-- induced: adjacency is preserved *and reflected* inside the ball -/
  adj : ∀ x, x ∈ ball2 G v → ∀ y, y ∈ ball2 G v → (G.graph.Adj x y ↔ H.graph.Adj (φ x) (φ y))

namespace BallIso

variable {G H : Flag emptyType} {v : Fin G.size} {w : Fin H.size}
  {φ : Fin G.size → Fin H.size}

theorem injOn (hφ : BallIso G H v w φ) {S : Finset (Fin G.size)} (hS : S ⊆ ball2 G v) :
    Set.InjOn φ ↑S := fun x hx y hy h => hφ.inj x (hS hx) y (hS hy) h

theorem card_image (hφ : BallIso G H v w φ) {S : Finset (Fin G.size)} (hS : S ⊆ ball2 G v) :
    (S.image φ).card = S.card := Finset.card_image_of_injOn (hφ.injOn hS)

/-- Adjacency to the root transfers. -/
theorem adjRoot (hφ : BallIso G H v w φ) {x : Fin G.size} (hx : x ∈ ball2 G v) :
    G.graph.Adj v x ↔ H.graph.Adj w (φ x) := by
  have := hφ.adj v (mem_ball2_self v) x hx
  rwa [hφ.root] at this

/-- Being the root transfers. -/
theorem eq_root (hφ : BallIso G H v w φ) {x : Fin G.size} (hx : x ∈ ball2 G v) :
    x = v ↔ φ x = w := by
  constructor
  · rintro rfl; exact hφ.root
  · intro h
    exact hφ.inj x hx v (mem_ball2_self v) (by rw [h, hφ.root])

/-! ### The three ball layers transfer -/

/-- The root neighbourhood transfers. -/
theorem rootNbrs_image (hφ : BallIso G H v w φ) :
    (rootNbrs G v).image φ = rootNbrs H w := by
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact mem_rootNbrs.mpr
      ((hφ.adjRoot (rootNbrs_subset_ball2 v ha)).mp (mem_rootNbrs.mp ha))
  · intro hb
    obtain ⟨x, hx, rfl⟩ := hφ.surj b (rootNbrs_subset_ball2 w hb)
    exact Finset.mem_image_of_mem φ
      (mem_rootNbrs.mpr ((hφ.adjRoot hx).mpr (mem_rootNbrs.mp hb)))

/-- The attachment set at a ball vertex transfers. -/
theorem attachSet_image (hφ : BallIso G H v w φ) {x : Fin G.size} (hx : x ∈ ball2 G v) :
    (attachSet G v x).image φ = attachSet H w (φ x) := by
  ext c
  constructor
  · intro hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    rw [attachSet, Finset.mem_filter] at ha
    have haB : a ∈ ball2 G v := mem_ball2_of_adj v ha.2.1
    rw [attachSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hφ.adjRoot haB).mp ha.2.1, (hφ.adj x hx a haB).mp ha.2.2⟩
  · intro hc
    rw [attachSet, Finset.mem_filter] at hc
    obtain ⟨a, ha, rfl⟩ := hφ.surj c (mem_ball2_of_adj w hc.2.1)
    refine Finset.mem_image_of_mem φ ?_
    rw [attachSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (hφ.adjRoot ha).mpr hc.2.1, (hφ.adj x hx a ha).mpr hc.2.2⟩

/-- Attachment counts transfer. -/
theorem attach_card (hφ : BallIso G H v w φ) {x : Fin G.size} (hx : x ∈ ball2 G v) :
    (attachSet H w (φ x)).card = (attachSet G v x).card := by
  rw [← hφ.attachSet_image hx, hφ.card_image (attachSet_subset_ball2 v x)]

/-- The positive shell transfers. -/
theorem shellPos_image (hφ : BallIso G H v w φ) :
    (shellPos G v).image φ = shellPos H w := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hxB : x ∈ ball2 G v := shellPos_subset_ball2 v hx
    obtain ⟨hxS, hpos⟩ := mem_shellPos.mp hx
    obtain ⟨hne, hnadj⟩ := mem_shellSet'.mp hxS
    refine mem_shellPos.mpr ⟨mem_shellSet'.mpr ⟨?_, ?_⟩, ?_⟩
    · exact fun h => hne ((hφ.eq_root hxB).mpr h)
    · exact fun h => hnadj ((hφ.adjRoot hxB).mpr h)
    · rwa [hφ.attach_card hxB]
  · intro hy
    obtain ⟨x, hxB, rfl⟩ := hφ.surj y (shellPos_subset_ball2 w hy)
    obtain ⟨hyS, hpos⟩ := mem_shellPos.mp hy
    obtain ⟨hne, hnadj⟩ := mem_shellSet'.mp hyS
    refine Finset.mem_image_of_mem φ (mem_shellPos.mpr ⟨mem_shellSet'.mpr ⟨?_, ?_⟩, ?_⟩)
    · exact fun h => hne ((hφ.eq_root hxB).mp h)
    · exact fun h => hnadj ((hφ.adjRoot hxB).mp h)
    · rwa [hφ.attach_card hxB] at hpos

/-! ### `T` -/

theorem prodMap_injOn (hφ : BallIso G H v w φ) {S : Finset (Fin G.size)}
    (hS : S ⊆ ball2 G v) :
    Set.InjOn (fun p : Fin G.size × Fin G.size => (φ p.1, φ p.2))
      ↑(S ×ˢ S) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hab hcd
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (hφ.inj a (hS hab.1) c (hS hcd.1) h.1)
    (hφ.inj b (hS hab.2) d (hS hcd.2) h.2)

/-- Both-orientation shell edges transfer. -/
theorem pairsAdjOn_shellPos_image (hφ : BallIso G H v w φ) :
    pairsAdjOn H (shellPos H w)
      = (pairsAdjOn G (shellPos G v)).image (fun p => (φ p.1, φ p.2)) := by
  ext ⟨q₁, q₂⟩
  simp only [pairsAdjOn, Finset.mem_filter, Finset.mem_product, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, hadj⟩
    rw [← hφ.shellPos_image] at h1 h2
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h2
    exact ⟨(x, y), ⟨⟨hx, hy⟩,
      (hφ.adj x (shellPos_subset_ball2 v hx) y (shellPos_subset_ball2 v hy)).mpr hadj⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hadj⟩, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hφ.shellPos_image]; exact Finset.mem_image_of_mem φ hx
    · rw [← hφ.shellPos_image]; exact Finset.mem_image_of_mem φ hy
    · exact (hφ.adj x (shellPos_subset_ball2 v hx) y (shellPos_subset_ball2 v hy)).mp hadj

/-- **The shell objective `T` is determined by the rooted ball.**  No degree hypothesis and
no triangle-freeness: `T` reads `shellPos` and the attachment counts, both ball-internal. -/
theorem shellObjective_eq (hφ : BallIso G H v w φ) :
    (∑ p ∈ shellPairsLt H w, (attachSet H w p.1).card * (attachSet H w p.2).card)
      = ∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card := by
  rw [sum_T_restrict w, sum_T_restrict v]
  have key : 2 * (∑ p ∈ pairsLtOn H (shellPos H w),
        (attachSet H w p.1).card * (attachSet H w p.2).card)
      = 2 * ∑ p ∈ pairsLtOn G (shellPos G v),
          (attachSet G v p.1).card * (attachSet G v p.2).card := by
    rw [← sum_pairsAdjOn_prod (shellPos H w) (fun u => (attachSet H w u).card),
      ← sum_pairsAdjOn_prod (shellPos G v) (fun u => (attachSet G v u).card),
      hφ.pairsAdjOn_shellPos_image,
      Finset.sum_image ((hφ.prodMap_injOn (shellPos_subset_ball2 v)).mono
        (by intro p hp; exact Finset.mem_coe.mpr (Finset.mem_filter.mp hp).1))]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    rw [hφ.attach_card (shellPos_subset_ball2 v h1),
      hφ.attach_card (shellPos_subset_ball2 v h2)]
  omega

/-! ### `K_a` and the visible credit -/

/-- The punctured attachment set at a root neighbour transfers. -/
theorem avoidAttach_image (hφ : BallIso G H v w φ) {a : Fin G.size} (ha : a ∈ rootNbrs G v)
    {z : Fin G.size} (hz : z ∈ ball2 G v) :
    (avoidAttach G a v z).image φ = avoidAttach H (φ a) w (φ z) := by
  have hav : G.graph.Adj v a := mem_rootNbrs.mp ha
  have haB : a ∈ ball2 G v := rootNbrs_subset_ball2 v ha
  have hav' : H.graph.Adj w (φ a) := (hφ.adjRoot haB).mp hav
  ext c
  constructor
  · intro hc
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
    rw [avoidAttach, Finset.mem_erase, attachSet, Finset.mem_filter] at hb
    obtain ⟨hbv, -, hab, hzb⟩ := hb
    have hbB : b ∈ ball2 G v := mem_ball2_of_adj_rootNbr hav hab
    rw [avoidAttach, Finset.mem_erase, attachSet, Finset.mem_filter]
    exact ⟨fun h => hbv ((hφ.eq_root hbB).mpr h), Finset.mem_univ _,
      (hφ.adj a haB b hbB).mp hab, (hφ.adj z hz b hbB).mp hzb⟩
  · intro hc
    rw [avoidAttach, Finset.mem_erase, attachSet, Finset.mem_filter] at hc
    obtain ⟨hcw, -, hac, hzc⟩ := hc
    obtain ⟨b, hbB, rfl⟩ := hφ.surj c (mem_ball2_of_adj_rootNbr hav' hac)
    refine Finset.mem_image_of_mem φ ?_
    rw [avoidAttach, Finset.mem_erase, attachSet, Finset.mem_filter]
    exact ⟨fun h => hcw ((hφ.eq_root hbB).mp h), Finset.mem_univ _,
      (hφ.adj a haB b hbB).mpr hac, (hφ.adj z hz b hbB).mpr hzc⟩

/-- Punctured attachment counts transfer. -/
theorem avoidAttach_card (hφ : BallIso G H v w φ) {a : Fin G.size} (ha : a ∈ rootNbrs G v)
    {z : Fin G.size} (hz : z ∈ ball2 G v) :
    (avoidAttach H (φ a) w (φ z)).card = (avoidAttach G a v z).card := by
  rw [← hφ.avoidAttach_image ha hz,
    hφ.card_image (avoidAttach_subset_ball2 (mem_rootNbrs.mp ha) z)]

/-- Visibility from the root transfers. -/
theorem isVisible_iff (hφ : BallIso G H v w φ) {z : Fin G.size} (hz : z ∈ ball2 G v) :
    IsVisible G v z ↔ IsVisible H w (φ z) := by
  rw [IsVisible, IsVisible, hφ.attach_card hz]
  exact or_congr (hφ.adjRoot hz) Iff.rfl

/-- Membership of `K_a` transfers, one ball vertex at a time. -/
theorem mem_visibleAvoid_iff (hφ : BallIso G H v w φ) {a : Fin G.size}
    (ha : a ∈ rootNbrs G v) {z : Fin G.size} (hz : z ∈ ball2 G v) :
    z ∈ visibleAvoid G a v ↔ φ z ∈ visibleAvoid H (φ a) w := by
  have hav : G.graph.Adj v a := mem_rootNbrs.mp ha
  have haB : a ∈ ball2 G v := rootNbrs_subset_ball2 v ha
  have hav' : H.graph.Adj w (φ a) := (hφ.adjRoot haB).mp hav
  rw [visibleAvoid_eq_ball2_filter hav, visibleAvoid_eq_ball2_filter hav',
    Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨-, hza, hnaz, hpos, hvis⟩
    refine ⟨hφ.maps z hz, fun h => hza (hφ.inj z hz a haB h),
      fun h => hnaz ((hφ.adj a haB z hz).mpr h), ?_, (hφ.isVisible_iff hz).mp hvis⟩
    rwa [hφ.avoidAttach_card ha hz]
  · rintro ⟨-, hza, hnaz, hpos, hvis⟩
    refine ⟨hz, fun h => hza (congrArg φ h),
      fun h => hnaz ((hφ.adj a haB z hz).mp h), ?_, (hφ.isVisible_iff hz).mpr hvis⟩
    rwa [hφ.avoidAttach_card ha hz] at hpos

/-- **`K_a` transfers.**  No triangle-freeness and no degree hypothesis. -/
theorem visibleAvoid_image (hφ : BallIso G H v w φ) {a : Fin G.size}
    (ha : a ∈ rootNbrs G v) :
    (visibleAvoid G a v).image φ = visibleAvoid H (φ a) w := by
  have hav : G.graph.Adj v a := mem_rootNbrs.mp ha
  have hav' : H.graph.Adj w (φ a) := (hφ.adjRoot (rootNbrs_subset_ball2 v ha)).mp hav
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact (hφ.mem_visibleAvoid_iff ha (visibleAvoid_subset_ball2 hav hz)).mp hz
  · intro hy
    obtain ⟨z, hzB, rfl⟩ := hφ.surj y (visibleAvoid_subset_ball2 hav' hy)
    exact Finset.mem_image_of_mem φ ((hφ.mem_visibleAvoid_iff ha hzB).mpr hy)

/-- The visible credit at a single neighbour is determined by the ball. -/
theorem visibleCredit_eq (hφ : BallIso G H v w φ) {a : Fin G.size} (ha : a ∈ rootNbrs G v) :
    visibleCredit H (φ a) w = visibleCredit G a v := by
  have hsub := visibleAvoid_subset_ball2 (G := G) (mem_rootNbrs.mp ha)
  rw [visibleCredit, visibleCredit, ← hφ.visibleAvoid_image ha,
    Finset.sum_image (hφ.injOn hsub)]
  exact Finset.sum_congr rfl fun z hz => by rw [hφ.avoidAttach_card ha (hsub hz)]

/-- **The total visible credit is determined by the rooted ball.**  No degree hypothesis and
no triangle-freeness. -/
theorem visibleCreditTotal_eq (hφ : BallIso G H v w φ) :
    visibleCreditTotal H w = visibleCreditTotal G v := by
  rw [visibleCreditTotal, visibleCreditTotal, ← hφ.rootNbrs_image,
    Finset.sum_image (hφ.injOn (rootNbrs_subset_ball2 v))]
  exact Finset.sum_congr rfl fun a ha => hφ.visibleCredit_eq ha

/-! ### The visible charge — this is where regularity is spent

`dhat = visibleDeg + unseenDeg`, and `unseenDeg G v z` counts neighbours of `z` in the third
layer `S³`, which the ball cannot see.  The route is through `dhat_eq_local`, which replaces
`unseenDeg` by `shellSlack = 4 − |A_z| − d_{F⁺}(z)` — a ball-internal quantity — at the cost
of `IsRegular` and `maxDegree = 4`.  The hypothesis is paid **on both sides**, and it is not
avoidable: see `§ Sharpness`.

Note that the direct route of `unseenDeg_transfer` is unavailable here.  That proof works
because `hclosed` makes every neighbour of a vertex in the image lie in the image, so the
extra invisible vertices are discarded by the adjacency filter.  A ball isomorphism promises
nothing of the kind: a shell vertex of `G` may have neighbours outside `ball2 G v` and the
corresponding shell vertex of `H` may have none. -/

/-- The visible degree is determined by the ball. -/
theorem visibleDeg_eq (hφ : BallIso G H v w φ) {a : Fin G.size} (ha : a ∈ rootNbrs G v)
    {z : Fin G.size} (hz : z ∈ ball2 G v) :
    visibleDeg H (φ a) w (φ z) = visibleDeg G a v z := by
  have hsub := visibleAvoid_subset_ball2 (G := G) (mem_rootNbrs.mp ha)
  have hfil : ((visibleAvoid G a v).filter fun y => H.graph.Adj (φ z) (φ y))
      = (visibleAvoid G a v).filter fun y => G.graph.Adj z y := by
    ext y
    simp only [Finset.mem_filter]
    exact and_congr_right fun hy => (hφ.adj z hz y (hsub hy)).symm
  rw [visibleDeg, visibleDeg, ← hφ.visibleAvoid_image ha, Finset.filter_image,
    hφ.card_image ((Finset.filter_subset _ _).trans hsub), hfil]

/-- The positive-shell degree is determined by the ball. -/
theorem shellPosDeg_eq (hφ : BallIso G H v w φ) {z : Fin G.size} (hz : z ∈ ball2 G v) :
    shellPosDeg H w (φ z) = shellPosDeg G v z := by
  have hfil : ((shellPos G v).filter fun y => H.graph.Adj (φ z) (φ y))
      = (shellPos G v).filter fun y => G.graph.Adj z y := by
    ext y
    simp only [Finset.mem_filter]
    exact and_congr_right fun hy => (hφ.adj z hz y (shellPos_subset_ball2 v hy)).symm
  rw [shellPosDeg, shellPosDeg, ← hφ.shellPos_image, Finset.filter_image,
    hφ.card_image ((Finset.filter_subset _ _).trans (shellPos_subset_ball2 v)), hfil]

/-- The slot count is determined by the ball. -/
theorem shellSlack_eq (hφ : BallIso G H v w φ) {z : Fin G.size} (hz : z ∈ ball2 G v) :
    shellSlack H w (φ z) = shellSlack G v z := by
  rw [shellSlack, shellSlack, hφ.attach_card hz, hφ.shellPosDeg_eq hz]

/-- **`d̂` is determined by the ball, given 4-regularity on both sides.** -/
theorem dhat_eq (hφ : BallIso G H v w φ)
    (hRegG : IsRegular G) (hdegG : maxDegree G = 4)
    (hRegH : IsRegular H) (hdegH : maxDegree H = 4)
    {a : Fin G.size} (ha : a ∈ rootNbrs G v) {z : Fin G.size} (hz : z ∈ ball2 G v) :
    dhat H (φ a) w (φ z) = dhat G a v z := by
  rw [dhat_eq_local hRegH hdegH, dhat_eq_local hRegG hdegG, hφ.visibleDeg_eq ha hz]
  by_cases h : G.graph.Adj v z
  · rw [if_pos h, if_pos ((hφ.adjRoot hz).mp h)]
  · rw [if_neg h, if_neg fun h' => h ((hφ.adjRoot hz).mpr h'), hφ.shellSlack_eq hz]

/-- The visible charge at a single neighbour is determined by the ball. -/
theorem visibleCharge_eq (hφ : BallIso G H v w φ)
    (hRegG : IsRegular G) (hdegG : maxDegree G = 4)
    (hRegH : IsRegular H) (hdegH : maxDegree H = 4)
    {a : Fin G.size} (ha : a ∈ rootNbrs G v) :
    visibleCharge H (φ a) w = visibleCharge G a v := by
  have hsub := visibleAvoid_subset_ball2 (G := G) (mem_rootNbrs.mp ha)
  rw [visibleCharge, visibleCharge, ← hφ.visibleAvoid_image ha,
    Finset.sum_image (hφ.injOn hsub)]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [hφ.dhat_eq hRegG hdegG hRegH hdegH ha (hsub hz), hφ.avoidAttach_card ha (hsub hz)]

/-- **The total visible charge is determined by the rooted ball**, given 4-regularity on both
sides. -/
theorem visibleChargeTotal_eq (hφ : BallIso G H v w φ)
    (hRegG : IsRegular G) (hdegG : maxDegree G = 4)
    (hRegH : IsRegular H) (hdegH : maxDegree H = 4) :
    visibleChargeTotal H w = visibleChargeTotal G v := by
  rw [visibleChargeTotal, visibleChargeTotal, ← hφ.rootNbrs_image,
    Finset.sum_image (hφ.injOn (rootNbrs_subset_ball2 v))]
  exact Finset.sum_congr rfl fun a ha => hφ.visibleCharge_eq hRegG hdegG hRegH hdegH ha

/-! ### The capstone -/

/-- **The whole `henum` row is an invariant of the rooted radius-2 ball.**  Gate included:
both `19 ≤ T` and the conclusion transfer, so the row holds at `w` in `H` iff it holds at `v`
in `G`.  Compare `visibleRow_transfer`, which proves the same `↔` from a *closed* induced
injection — i.e. only along a union of connected components.  This statement instead reads a
set of at most `17` vertices (`card_ball2_le`), which is what collapses the `∀ H` of
`pentagon_bound_delta4_of_visible_enumeration` to a finite check. -/
theorem visibleRow_ball_iff (hφ : BallIso G H v w φ)
    (hRegG : IsRegular G) (hdegG : maxDegree G = 4)
    (hRegH : IsRegular H) (hdegH : maxDegree H = 4) :
    ((19 ≤ ∑ p ∈ shellPairsLt H w, (attachSet H w p.1).card * (attachSet H w p.2).card) →
        visibleChargeTotal H w
            + 12 * (∑ p ∈ shellPairsLt H w,
                (attachSet H w p.1).card * (attachSet H w p.2).card)
          ≤ visibleCreditTotal H w + 212)
      ↔ ((19 ≤ ∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card) →
          visibleChargeTotal G v
              + 12 * (∑ p ∈ shellPairsLt G v,
                  (attachSet G v p.1).card * (attachSet G v p.2).card)
            ≤ visibleCreditTotal G v + 212) := by
  rw [hφ.shellObjective_eq, hφ.visibleCreditTotal_eq,
    hφ.visibleChargeTotal_eq hRegG hdegG hRegH hdegH]

end BallIso

/-! ### Non-vacuity, and the relation to the landed transfer lemmas -/

/-- `BallIso` is satisfiable: the identity is one.  (Anti-vacuity guard for everything
above — a `BallIso` hypothesis that no map could meet would make the whole section empty.) -/
theorem ballIso_id (G : Flag emptyType) (v : Fin G.size) : BallIso G G v v id where
  root := rfl
  maps := fun _ hx => hx
  inj := fun _ _ _ _ h => h
  surj := fun y hy => ⟨y, hy, rfl⟩
  adj := fun _ _ _ _ => Iff.rfl

/-- **A closed induced injection gives a ball isomorphism.**  So `BallIso` is *implied by*
the hypothesis triple of `visibleRow_transfer`: on the regular class the statements above
cover everything the component-level transfer covered, and strictly more — `BallIso` also
relates hosts that share no component at all. -/
theorem ballIso_of_closed_embedding {H₀ G₀ : Flag emptyType} {ψ : Fin H₀.size → Fin G₀.size}
    (hinj : Function.Injective ψ)
    (hiff : ∀ i j, H₀.graph.Adj i j ↔ G₀.graph.Adj (ψ i) (ψ j))
    (hclosed : ∀ i u, G₀.graph.Adj (ψ i) u → ∃ j, ψ j = u)
    (i₀ : Fin H₀.size) : BallIso H₀ G₀ i₀ (ψ i₀) ψ where
  root := rfl
  maps := by
    intro x hx
    rcases mem_ball2.mp hx with rfl | hx | hx
    · exact mem_ball2_self _
    · exact mem_ball2_of_adj _ ((hiff i₀ x).mp hx)
    · refine mem_ball2.mpr (Or.inr (Or.inr ?_))
      rw [shellPos_image hinj hiff hclosed i₀]
      exact Finset.mem_image_of_mem ψ hx
  inj := fun _ _ _ _ h => hinj h
  surj := by
    intro y hy
    rcases mem_ball2.mp hy with rfl | hy | hy
    · exact ⟨i₀, mem_ball2_self _, rfl⟩
    · obtain ⟨j, rfl⟩ := hclosed i₀ y hy
      exact ⟨j, mem_ball2_of_adj _ ((hiff i₀ j).mpr hy), rfl⟩
    · rw [shellPos_image hinj hiff hclosed i₀] at hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨x, shellPos_subset_ball2 _ hx, rfl⟩
  adj := fun x _ y _ => hiff x y

/-- **The three row quantities, packaged.**  Stated with the hypothesis set the task asked
for — triangle-freeness included — even though the proof never uses `hTFG`/`hTFH`; see
`BallIso.shellObjective_eq`, `BallIso.visibleCreditTotal_eq` and
`BallIso.visibleChargeTotal_eq` for the exact cost of each conclusion. -/
theorem ball_determines_row {G H : Flag emptyType} {v : Fin G.size} {w : Fin H.size}
    {φ : Fin G.size → Fin H.size} (hφ : BallIso G H v w φ)
    (_hTFG : IsTriangleFree G) (hRegG : IsRegular G) (hdegG : maxDegree G = 4)
    (_hTFH : IsTriangleFree H) (hRegH : IsRegular H) (hdegH : maxDegree H = 4) :
    (∑ p ∈ shellPairsLt H w, (attachSet H w p.1).card * (attachSet H w p.2).card)
        = (∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card)
      ∧ visibleCreditTotal H w = visibleCreditTotal G v
      ∧ visibleChargeTotal H w = visibleChargeTotal G v :=
  ⟨hφ.shellObjective_eq, hφ.visibleCreditTotal_eq,
    hφ.visibleChargeTotal_eq hRegG hdegG hRegH hdegH⟩

/-! ## 3.  How the invariance is consumed

The `∀ H` of `pentagon_bound_delta4_of_visible_enumeration` collapses to a family of
representatives as soon as every rooted host is ball-isomorphic to one of them.  This is the
*invariance* half; supplying such a family — realizing every `Box`-legal configuration by an
actual graph — is the *realization* half, and it is not attempted here. -/

/-- **The collapse.**  Given representatives `R i` rooted at `rt i` such that every rooted
triangle-free 4-regular host has a radius-2 ball isomorphic to one of them, checking the
`henum` row on the representatives proves it for every host. -/
theorem visible_enumeration_of_ball_representatives {ι : Type}
    (R : ι → Flag emptyType) (rt : ∀ i, Fin (R i).size)
    (hreg : ∀ i, IsRegular (R i)) (hdeg : ∀ i, maxDegree (R i) = 4)
    (hrep : ∀ H : Flag emptyType, IsTriangleFree H → IsRegular H → maxDegree H = 4 →
      ∀ w : Fin H.size, ∃ i, ∃ φ : Fin (R i).size → Fin H.size, BallIso (R i) H (rt i) w φ)
    (hrow : ∀ i,
      (19 ≤ ∑ p ∈ shellPairsLt (R i) (rt i),
          (attachSet (R i) (rt i) p.1).card * (attachSet (R i) (rt i) p.2).card) →
        visibleChargeTotal (R i) (rt i)
            + 12 * (∑ p ∈ shellPairsLt (R i) (rt i),
                (attachSet (R i) (rt i) p.1).card * (attachSet (R i) (rt i) p.2).card)
          ≤ visibleCreditTotal (R i) (rt i) + 212) :
    ∀ H : Flag emptyType, IsTriangleFree H → IsRegular H → maxDegree H = 4 →
      ∀ w : Fin H.size,
        (19 ≤ ∑ p ∈ shellPairsLt H w, (attachSet H w p.1).card * (attachSet H w p.2).card) →
          visibleChargeTotal H w
              + 12 * (∑ p ∈ shellPairsLt H w,
                  (attachSet H w p.1).card * (attachSet H w p.2).card)
            ≤ visibleCreditTotal H w + 212 := by
  intro H hTFH hRegH hdegH w
  obtain ⟨i, φ, hφ⟩ := hrep H hTFH hRegH hdegH w
  exact (hφ.visibleRow_ball_iff (hreg i) (hdeg i) hRegH hdegH).mpr (hrow i)

/-! ## 4.  Sharpness — exactly which hypotheses are load-bearing

### (a) Regularity is necessary for the charge, and `maxDegree ≤ 4` is no substitute

Witness (`p2_ballinv_check.py`).  Both graphs have vertex set
`{v, a₁, a₂, a₃, a₄, z, b, u}` and the edges `v ∼ a₁, a₂, a₃, a₄`, `a₁ ∼ z`, `a₂ ∼ b`,
`z ∼ b`; in `G` the vertex `u` is isolated, in `H` it is a pendant, `z ∼ u`.  Both are
triangle-free with `maxDegree = 4`; neither is regular.

`u` sits at distance three from `v`, so it is invisible and carries no attachment:
`u ∉ ball2 H v`, the two balls are the *same* vertex set with the *same* induced edges, and
the identity map is a `BallIso G H v v`.  Yet

| | `T` | `visibleCreditTotal` | `visibleChargeTotal` |
|---|---|---|---|
| `G` | 1 | 6 | **0** |
| `H` | 1 | 6 | **1** |

The whole difference is `unseenDeg v z`: `0` in `G`, `1` in `H`, while `shellSlack v z = 2`
in both — precisely the failure of `unseenDeg_eq_shellSlack` off the regular class.  Here
`z ∈ K_{a₂}` with `k_{a₂}(z) = 1`, and `certY43 1 = 1` carries the difference into the charge.
Note that `T` and the credit are equal, as
`BallIso.shellObjective_eq` / `BallIso.visibleCreditTotal_eq` predict with no degree
hypothesis at all.

### (b) Triangle-freeness is not needed anywhere

No statement above consumes `hTF`.  The three places where the earlier development reached
for it are all avoidable: `mem_ball2_of_adj_rootNbr` replaces
`nbr_of_rootNbr_mem_shellPos` (the case `G.Adj v z` lands in the neighbour layer instead of
contradicting a triangle), and `visibleAvoid_eq_ball2_filter` replaces `visibleAvoid_eq`
(the invariance proof only ever has to *pull a member back*, for which an enclosing set is
enough; it never needs the two-block split).  `ball_determines_row` carries `IsTriangleFree`
as an unused argument only because the task asked for that signature.

The gate `visibleAvoid_subset_rootNbrs_union_shellPos` is genuinely sharper than
`visibleAvoid_subset_ball2` — it excludes the root — and that sharpness is recorded here as
`visibleAvoid_eq_visible_filter` and `root_notMem_visibleAvoid`, the fact that makes the
model's root-block/shell-block split of `K_a` exhaustive.  It is not, however, what ball
invariance needs.

### (c) `root` and `surj` are both load-bearing

`root : φ v = w` cannot be dropped: the row is a function of the root, not of the ball graph.
It is *not* a consequence of the other clauses — the unrooted ball graph carries no marker
for `v`.  (Searched for a witness that the unrooted ball fails to determine the row — 755
ball graphs from the census below, grouped by order, size and degree sequence, exact
backtracking isomorphism inside each group — and found none.  So the requirement is kept
because the statement needs it, not because a counterexample is in hand.)

`surj` cannot be dropped either, and the witness is trivial: take `G` a one-vertex graph
rooted at its vertex (`T = credit = charge = 0`) and `φ` the map to any root `w` of any `H`.
That `φ` is injective, induced and root-preserving on `ball2 G v = {v}`, and it fails only
surjectivity; the rows differ.  `surj` is exactly what lets the backward directions of
`rootNbrs_image`, `attachSet_image`, `shellPos_image` and `visibleAvoid_image` pull an
`H`-side member back to the `G` side.

### (d) The positive direction was measured

On 49 triangle-free 4-regular hosts (circulants `C_n(i,j)` for `9 ≤ n ≤ 20`, plus random
4-regular graphs on `12 … 22` vertices), all 755 roots: recomputing `T`,
`visibleCreditTotal` and `visibleChargeTotal` *inside the induced subgraph on `ball2` alone*
— with `d̂` replaced by its ball-internal form — returns the true values, zero mismatches.
Largest ball met: 13 vertices (the provable ceiling is 17, `card_ball2_le`).  On the
non-regular pair of (a) the same recomputation returns `4` for both `G` and `H`, agreeing
with neither: off the regular class the ball-internal formula is simply not the charge. -/

end PentagonLocal

end Davey2024
