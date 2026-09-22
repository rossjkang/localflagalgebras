import DaveyThesis2024.Delta4.Transport

/-!
# Δ = 4, Stage 4: obligations 12 and 13 — credit and charge transport

`visibleCreditTotal`, `visibleChargeTotal` and the doubled shell objective `2T` of a rooted
triangle-free 4-regular graph are exactly the model quantities `credit`, `charge` and `twoT`
of the encoded triple `(nOf G v, KOf G v, AOf G v)`.

Everything here is assembly on top of what is already landed:

* `visibleAvoid_eq` / `sum_visibleAvoid_eq` (obligation 3) split `K_a` into its root block
  and its shell block;
* `avoidAttach_card_root` / `avoidAttach_card_shell` (obligation 4) turn the two blocks'
  punctured attachment counts into `rootW` / `shellW`;
* `dhat_eq_local` removes `unseenDeg`, and `kwt_KOf` / `deg_AOf` turn the slot count
  `shellSlack` into the model's `slack`;
* `sum_range_shellAt` / `sum_range_rootAt` (`Transport.lean`) move a `Finset` sum onto
  `Finset.range`, where `sumUpto_eq_sum_range` meets it.

No new definition of any model quantity is introduced (plan §6(e)): every model symbol below
is `Delta4Model`'s.
-/

namespace Davey2024
namespace PentagonLocal

open Finset
open scoped Classical

variable {G : Flag emptyType}

/-! ## 0.  One indexing lemma

`pos_shellAt : pos (shellAt i) = i` and `idx_rootAt : idx (rootAt a) = a` are now exported by
`Transport.lean` (§7.3), proved from `enum_idxOf_getD` — the generic duplicate-free-enumeration
lemma — rather than from `Finset.sort`, because the shell array is no longer the vertex-index
sort.  Only the injectivity corollary the charge transport consumes is stated here. -/

/-- `rootAt` is injective on the four letters, in the form the transport consumes. -/
lemma rootAt_eq_iff (hReg : IsRegular G) (hdeg : maxDegree G = 4) {v b : Fin G.size} {ℓ : ℕ}
    (hℓ : ℓ < 4) (hb : b ∈ rootNbrs G v) : rootAt G v ℓ = b ↔ ℓ = idx G v b := by
  have hcard : (rootNbrs G v).card = 4 := card_rootNbrs hReg hdeg v
  constructor
  · intro h; rw [← h, idx_rootAt (by omega)]
  · intro h; rw [h, rootAt_idx hb]

/-! ## 1.  The two certificates agree -/

/-- The model's dual weights are the graph side's `certY43`. -/
lemma cert_eq_certY43 (k : ℕ) : Delta4Model.cert k = certY43 k := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | (_ + 3) => rfl

/-! ## 2.  `shellW`, on the whole shell

`avoidAttach_card_shell` covers the slots the decomposition keeps and `shellW_eq_zero_of_adj`
the slots it drops; together they give one equation valid at every shell vertex, which is
what lets the model sum over all `n` slots while the graph sums over the filtered block. -/

/-- **`shellW` at every shell vertex.**  Zero on the vertices adjacent to `a` (which are not
    in `K_a`), the punctured attachment count elsewhere. -/
lemma shellW_eq (hTF : IsTriangleFree G) (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    {a v y : Fin G.size} (hav : G.graph.Adj v a) (hy : y ∈ shellPos G v) :
    Delta4Model.shellW (nOf G v) (KOf G v) (AOf G v) (idx G v a) (pos G v y)
      = if G.graph.Adj a y then 0 else (avoidAttach G a v y).card := by
  by_cases h : G.graph.Adj a y
  · rw [if_pos h, shellW_eq_zero_of_adj hReg hdeg hav hy h]
  · rw [if_neg h, avoidAttach_card_shell hTF hReg hdeg hav hy h]

/-- `shellW` is nonzero exactly on the shell block of `K_a`. -/
lemma shellW_ne_zero_iff (hTF : IsTriangleFree G) (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    {a v y : Fin G.size} (hav : G.graph.Adj v a) (hy : y ∈ shellPos G v) :
    Delta4Model.shellW (nOf G v) (KOf G v) (AOf G v) (idx G v a) (pos G v y) ≠ 0
      ↔ (¬ G.graph.Adj a y ∧ 1 ≤ (avoidAttach G a v y).card) := by
  rw [shellW_eq hTF hReg hdeg hav hy]
  by_cases h : G.graph.Adj a y
  · rw [if_pos h]
    exact ⟨fun hne => absurd rfl hne, fun hc => absurd h hc.1⟩
  · rw [if_neg h]
    exact ⟨fun hne => ⟨h, Nat.pos_of_ne_zero hne⟩, fun hc => by omega⟩

/-! ## 3.  Reading the encoding back at a named vertex -/

/-- The letter bit at a shell vertex, indexed by the vertex rather than its slot. -/
lemma hasL_at (hReg : IsRegular G) (hdeg : maxDegree G = 4) {v y b : Fin G.size}
    (hy : y ∈ shellPos G v) (hb : b ∈ rootNbrs G v) :
    Delta4Model.hasL (KOf G v) (pos G v y) (idx G v b)
      = if G.graph.Adj y b then 1 else 0 := by
  rw [hasL_KOf (pos_lt hy) (idx_lt_four hReg hdeg hb), rootAt_idx hb, shellAt_pos hy]

/-- The shell adjacency bit, indexed by vertices rather than slots. -/
lemma edg_at (hTF : IsTriangleFree G) (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    {v y z : Fin G.size} (hy : y ∈ shellPos G v) (hz : z ∈ shellPos G v) :
    Delta4Model.edg (AOf G v) (pos G v y) (pos G v z)
      = if G.graph.Adj y z then 1 else 0 := by
  rw [edg_AOf (card_shellPos_le_twelve hTF hReg hdeg v) (pos_lt hy) (pos_lt hz),
    shellAt_pos hy, shellAt_pos hz]

/-- The model's slack is the graph's slot count. -/
lemma slack_eq_shellSlack (hTF : IsTriangleFree G) (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    {v y : Fin G.size} (hy : y ∈ shellPos G v) :
    Delta4Model.slack (nOf G v) (KOf G v) (AOf G v) (pos G v y) = shellSlack G v y := by
  rw [Delta4Model.slack, kwt_KOf hReg hdeg (pos_lt hy), deg_AOf hTF hReg hdeg (pos_lt hy),
    shellAt_pos hy, shellSlack]

/-! ## 4.  The two blocks of `K_a`, as model-shaped sums

`sum_visibleAvoid_eq` splits a `K_a`-indexed sum into a root block and a shell block.  The two
lemmas below put each block into the shape the model folds over: `Finset.range 4` for the root
letters, `shellPos` (reached from `Finset.range n` by `sum_range_shellAt`) for the slots.
Both keep the positivity filter as an `if`, because the charge's summand does not vanish with
the weight — only the *outer factor* `cert` does. -/

/-- The model's four-letter fold, as a sum over the root neighbourhood. -/
lemma sumUpto_four_eq_sum_rootNbrs (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    (v : Fin G.size) (g : ℕ → ℕ) :
    Delta4Model.sumUpto g 4 0 = ∑ b ∈ rootNbrs G v, g (idx G v b) := by
  have h4 : (4 : ℕ) = (rootNbrs G v).card := (card_rootNbrs hReg hdeg v).symm
  rw [Delta4Model.sumUpto_eq_sum_range, h4, ← sum_range_rootAt v (fun b => g (idx G v b))]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [idx_rootAt (Finset.mem_range.mp hℓ)]

/-- The model's `n`-slot fold, as a sum over the positive shell. -/
lemma sumUpto_eq_sum_shellPos (v : Fin G.size) (g : ℕ → ℕ) :
    Delta4Model.sumUpto g (nOf G v) 0 = ∑ y ∈ shellPos G v, g (pos G v y) := by
  rw [Delta4Model.sumUpto_eq_sum_range, ← sum_range_shellAt v (fun y => g (pos G v y))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [pos_shellAt (Finset.mem_range.mp hi)]

/-- **The root block of `K_a`, indexed by letters.** -/
lemma sum_rootBlock_eq_range (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    {a v : Fin G.size} (ha : a ∈ rootNbrs G v) (f : Fin G.size → ℕ) :
    ∑ z ∈ ((rootNbrs G v).erase a).filter (fun b => 1 ≤ (avoidAttach G a v b).card), f z
      = ∑ ℓ ∈ Finset.range 4,
          (if ℓ = idx G v a then 0
           else if 1 ≤ (avoidAttach G a v (rootAt G v ℓ)).card then f (rootAt G v ℓ) else 0) := by
  have h4 : (4 : ℕ) = (rootNbrs G v).card := (card_rootNbrs hReg hdeg v).symm
  have hstep : ∑ z ∈ ((rootNbrs G v).erase a).filter
        (fun b => 1 ≤ (avoidAttach G a v b).card), f z
      = ∑ z ∈ rootNbrs G v,
          (if z ≠ a then (if 1 ≤ (avoidAttach G a v z).card then f z else 0) else 0) := by
    rw [Finset.sum_filter, ← Finset.filter_ne' (rootNbrs G v) a, Finset.sum_filter]
  rw [hstep, h4, ← sum_range_rootAt v
    (fun z => if z ≠ a then (if 1 ≤ (avoidAttach G a v z).card then f z else 0) else 0)]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hℓ4 : ℓ < 4 := by rw [h4]; exact Finset.mem_range.mp hℓ
  by_cases hR : rootAt G v ℓ = a
  · rw [if_neg (not_not_intro hR), if_pos ((rootAt_eq_iff hReg hdeg hℓ4 ha).mp hR)]
  · rw [if_pos hR, if_neg (fun hc => hR ((rootAt_eq_iff hReg hdeg hℓ4 ha).mpr hc))]

/-- **The shell block of `K_a`, indexed by shell vertices.** -/
lemma sum_shellBlock_eq_shellPos {a v : Fin G.size} (f : Fin G.size → ℕ) :
    ∑ z ∈ ((shellPos G v).filter (fun y => ¬ G.graph.Adj a y)).filter
        (fun y => 1 ≤ (avoidAttach G a v y).card), f z
      = ∑ y ∈ shellPos G v,
          (if ¬ G.graph.Adj a y ∧ 1 ≤ (avoidAttach G a v y).card then f y else 0) := by
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h1 : G.graph.Adj a y <;> by_cases h2 : 1 ≤ (avoidAttach G a v y).card <;>
    simp [h1, h2]

/-! ## 5.  Obligation 12 — `visibleCreditTotal = credit` -/

/-- **Credit at one root letter.**  `Σ_{z ∈ K_a} 3 k_a(z)` is the model's `creditAt`. -/
theorem visibleCredit_eq_model (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) {a v : Fin G.size} (hav : G.graph.Adj v a) :
    visibleCredit G a v = Delta4Model.creditAt (nOf G v) (KOf G v) (AOf G v) (idx G v a) := by
  have ha : a ∈ rootNbrs G v := mem_rootNbrs.mpr hav
  have hcard4 : (rootNbrs G v).card = 4 := card_rootNbrs hReg hdeg v
  rw [visibleCredit, sum_visibleAvoid_eq hTF hav (fun z => 3 * (avoidAttach G a v z).card),
    Delta4Model.creditAt]
  congr 1
  · -- the root block
    rw [sum_rootBlock_eq_range hReg hdeg ha (fun z => 3 * (avoidAttach G a v z).card),
      Delta4Model.sumUpto_eq_sum_range]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have hℓ4 : ℓ < 4 := Finset.mem_range.mp hℓ
    by_cases hEq : ℓ = idx G v a
    · rw [if_pos hEq, if_pos hEq]
    · rw [if_neg hEq, if_neg hEq]
      have hmem : rootAt G v ℓ ∈ rootNbrs G v := rootAt_mem (by rw [hcard4]; exact hℓ4)
      have hne : rootAt G v ℓ ≠ a := fun hc => hEq ((rootAt_eq_iff hReg hdeg hℓ4 ha).mp hc)
      have hcard := avoidAttach_card_root hTF hReg hdeg hav (Finset.mem_erase.mpr ⟨hne, hmem⟩)
      rw [idx_rootAt (by rw [hcard4]; exact hℓ4)] at hcard
      rw [hcard]
      by_cases hpos : 1 ≤ Delta4Model.rootW (nOf G v) (KOf G v) (idx G v a) ℓ
      · rw [if_pos hpos]
      · rw [if_neg hpos]
        have hz : Delta4Model.rootW (nOf G v) (KOf G v) (idx G v a) ℓ = 0 := by omega
        rw [hz]
  · -- the shell block
    rw [sum_shellBlock_eq_shellPos (fun z => 3 * (avoidAttach G a v z).card),
      sumUpto_eq_sum_shellPos]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [shellW_eq hTF hReg hdeg hav hy]
    by_cases h1 : G.graph.Adj a y
    · rw [if_pos h1, if_neg (fun hc => hc.1 h1)]
    · rw [if_neg h1]
      by_cases h2 : 1 ≤ (avoidAttach G a v y).card
      · rw [if_pos ⟨h1, h2⟩]
      · rw [if_neg (fun hc => h2 hc.2)]
        have hz : (avoidAttach G a v y).card = 0 := by omega
        rw [hz]

/-- **Obligation 12.**  The graph's total visible credit is the model's `credit`. -/
theorem visibleCreditTotal_eq_model (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size) :
    visibleCreditTotal G v = Delta4Model.credit (nOf G v) (KOf G v) (AOf G v) := by
  rw [visibleCreditTotal, Delta4Model.credit,
    sumUpto_four_eq_sum_rootNbrs hReg hdeg v
      (Delta4Model.creditAt (nOf G v) (KOf G v) (AOf G v))]
  exact Finset.sum_congr rfl fun a ha =>
    visibleCredit_eq_model hTF hReg hdeg (mem_rootNbrs.mp ha)

/-! ## 6.  `d̂`, at both vertex types

The model splits `d̂_a` by vertex type and the graph does not; `dhat_eq_local` is exactly that
case split and is already a theorem, so what is left is to read each of `dhatRoot` and
`dhatShell` off the decomposition of `K_a`. -/

/-- `|N(z) ∩ K_a|`, split along the two blocks of `K_a`. -/
lemma visibleDeg_split (hTF : IsTriangleFree G) {a v z : Fin G.size} (hav : G.graph.Adj v a) :
    visibleDeg G a v z
      = (∑ w ∈ ((rootNbrs G v).erase a).filter (fun b => 1 ≤ (avoidAttach G a v b).card),
            (if G.graph.Adj z w then 1 else 0))
        + ∑ w ∈ ((shellPos G v).filter (fun y => ¬ G.graph.Adj a y)).filter
              (fun y => 1 ≤ (avoidAttach G a v y).card), (if G.graph.Adj z w then 1 else 0) := by
  rw [visibleDeg, Finset.card_filter,
    sum_visibleAvoid_eq hTF hav (fun w => if G.graph.Adj z w then 1 else 0)]

/-- **`d̂` at a root-type vertex.**  `unseenDeg` vanishes there (`unseenDeg_eq_zero_of_adj`)
    and the root block of `K_a` contributes nothing, because two neighbours of the root are
    never adjacent — that is where triangle-freeness enters. -/
theorem dhatRoot_eq_dhat (hTF : IsTriangleFree G) (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    {a v b : Fin G.size} (hav : G.graph.Adj v a) (hb : b ∈ rootNbrs G v) :
    Delta4Model.dhatRoot (nOf G v) (KOf G v) (AOf G v) (idx G v a) (idx G v b)
      = dhat G a v b := by
  have hvb : G.graph.Adj v b := mem_rootNbrs.mp hb
  rw [dhat, unseenDeg_eq_zero_of_adj hvb, Nat.add_zero, visibleDeg_split hTF hav]
  have hroot : ∑ w ∈ ((rootNbrs G v).erase a).filter
      (fun c => 1 ≤ (avoidAttach G a v c).card), (if G.graph.Adj b w then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero fun w hw => ?_
    have hwN : w ∈ rootNbrs G v := Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1
    exact if_neg (fun hbw => hTF v b w hvb hbw (mem_rootNbrs.mp hwN))
  rw [hroot, Nat.zero_add, sum_shellBlock_eq_shellPos, Delta4Model.dhatRoot,
    sumUpto_eq_sum_shellPos]
  refine Finset.sum_congr rfl fun y hy => ?_
  by_cases hc : ¬ G.graph.Adj a y ∧ 1 ≤ (avoidAttach G a v y).card
  · rw [if_neg ((shellW_ne_zero_iff hTF hReg hdeg hav hy).mpr hc), if_pos hc,
      hasL_at hReg hdeg hy hb]
    exact if_congr (G.graph.adj_comm y b) rfl rfl
  · have heq : Delta4Model.shellW (nOf G v) (KOf G v) (AOf G v) (idx G v a) (pos G v y) = 0 := by
      by_contra hne
      exact hc ((shellW_ne_zero_iff hTF hReg hdeg hav hy).mp hne)
    rw [if_pos heq, if_neg hc]

/-- **`d̂` at a shell-type vertex.**  Here `unseenDeg` is the slot count `shellSlack`
    (`dhat_eq_local`), which the model carries as `slack`; the visible part splits along the
    two blocks of `K_a` exactly as the model's two folds do. -/
theorem dhatShell_eq_dhat (hTF : IsTriangleFree G) (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    {a v y : Fin G.size} (hav : G.graph.Adj v a) (hy : y ∈ shellPos G v) :
    Delta4Model.dhatShell (nOf G v) (KOf G v) (AOf G v) (idx G v a) (pos G v y)
      = dhat G a v y := by
  have ha : a ∈ rootNbrs G v := mem_rootNbrs.mpr hav
  have hcard4 : (rootNbrs G v).card = 4 := card_rootNbrs hReg hdeg v
  have hvy : ¬ G.graph.Adj v y := (mem_shellSet'.mp (mem_shellPos.mp hy).1).2
  rw [dhat_eq_local hReg hdeg, if_neg hvy, visibleDeg_split hTF hav, Delta4Model.dhatShell,
    slack_eq_shellSlack hTF hReg hdeg hy]
  congr 1
  congr 1
  · -- the root block
    rw [sum_rootBlock_eq_range hReg hdeg ha (fun w => if G.graph.Adj y w then 1 else 0),
      Delta4Model.sumUpto_eq_sum_range]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have hℓ4 : ℓ < 4 := Finset.mem_range.mp hℓ
    by_cases hEq : ℓ = idx G v a
    · rw [if_pos hEq, if_pos hEq]
    · rw [if_neg hEq, if_neg hEq]
      have hmem : rootAt G v ℓ ∈ rootNbrs G v := rootAt_mem (by rw [hcard4]; exact hℓ4)
      have hne : rootAt G v ℓ ≠ a := fun hc => hEq ((rootAt_eq_iff hReg hdeg hℓ4 ha).mp hc)
      have hidx : idx G v (rootAt G v ℓ) = ℓ := idx_rootAt (by rw [hcard4]; exact hℓ4)
      have hcard := avoidAttach_card_root hTF hReg hdeg hav (Finset.mem_erase.mpr ⟨hne, hmem⟩)
      rw [hidx] at hcard
      have hbit : Delta4Model.hasL (KOf G v) (pos G v y) ℓ
          = if G.graph.Adj y (rootAt G v ℓ) then 1 else 0 := by
        rw [← hidx, hasL_at hReg hdeg hy hmem, hidx]
      rw [hcard, hbit]
      by_cases hpos : 1 ≤ Delta4Model.rootW (nOf G v) (KOf G v) (idx G v a) ℓ
      · rw [if_pos hpos, if_neg (by omega)]
      · rw [if_neg hpos, if_pos (by omega)]
  · -- the shell block
    rw [sum_shellBlock_eq_shellPos (fun w => if G.graph.Adj y w then 1 else 0),
      sumUpto_eq_sum_shellPos]
    refine Finset.sum_congr rfl fun z hz => ?_
    by_cases hpz : pos G v z = pos G v y
    · have hzy : z = y := by rw [← shellAt_pos hz, ← shellAt_pos hy, hpz]
      rw [if_pos hpz, hzy, if_neg (fun h => G.graph.ne_of_adj h rfl), ite_self]
    · rw [if_neg hpz, edg_at hTF hReg hdeg hy hz]
      by_cases hc : ¬ G.graph.Adj a z ∧ 1 ≤ (avoidAttach G a v z).card
      · rw [if_neg ((shellW_ne_zero_iff hTF hReg hdeg hav hz).mpr hc), if_pos hc]
      · have heq : Delta4Model.shellW (nOf G v) (KOf G v) (AOf G v) (idx G v a)
            (pos G v z) = 0 := by
          by_contra hne
          exact hc ((shellW_ne_zero_iff hTF hReg hdeg hav hz).mp hne)
        rw [if_pos heq, if_neg hc]

/-! ## 7.  Obligation 13 — `visibleChargeTotal = charge` -/

/-- **Charge at one root letter.**  `Σ_{z ∈ K_a} d̂_a(z)·c(k_a(z))` is the model's `chargeAt`.
    The graph sums over `K_a` and the model over all four letters and all `n` slots; the extra
    model terms vanish because `cert 0 = 0`. -/
theorem visibleCharge_eq_model (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) {a v : Fin G.size} (hav : G.graph.Adj v a) :
    visibleCharge G a v = Delta4Model.chargeAt (nOf G v) (KOf G v) (AOf G v) (idx G v a) := by
  have ha : a ∈ rootNbrs G v := mem_rootNbrs.mpr hav
  have hcard4 : (rootNbrs G v).card = 4 := card_rootNbrs hReg hdeg v
  rw [visibleCharge, sum_visibleAvoid_eq hTF hav
      (fun z => dhat G a v z * certY43 (avoidAttach G a v z).card),
    Delta4Model.chargeAt]
  congr 1
  · -- the root block
    rw [sum_rootBlock_eq_range hReg hdeg ha
        (fun z => dhat G a v z * certY43 (avoidAttach G a v z).card),
      Delta4Model.sumUpto_eq_sum_range]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have hℓ4 : ℓ < 4 := Finset.mem_range.mp hℓ
    by_cases hEq : ℓ = idx G v a
    · rw [if_pos hEq, if_pos hEq]
    · rw [if_neg hEq, if_neg hEq]
      have hmem : rootAt G v ℓ ∈ rootNbrs G v := rootAt_mem (by rw [hcard4]; exact hℓ4)
      have hne : rootAt G v ℓ ≠ a := fun hc => hEq ((rootAt_eq_iff hReg hdeg hℓ4 ha).mp hc)
      have hidx : idx G v (rootAt G v ℓ) = ℓ := idx_rootAt (by rw [hcard4]; exact hℓ4)
      have hcard := avoidAttach_card_root hTF hReg hdeg hav (Finset.mem_erase.mpr ⟨hne, hmem⟩)
      rw [hidx] at hcard
      have hdh : Delta4Model.dhatRoot (nOf G v) (KOf G v) (AOf G v) (idx G v a) ℓ
          = dhat G a v (rootAt G v ℓ) := by
        have hd := dhatRoot_eq_dhat hTF hReg hdeg hav hmem
        rwa [hidx] at hd
      rw [hcard, hdh, cert_eq_certY43]
      by_cases hpos : 1 ≤ Delta4Model.rootW (nOf G v) (KOf G v) (idx G v a) ℓ
      · rw [if_pos hpos]
      · rw [if_neg hpos]
        have hz : Delta4Model.rootW (nOf G v) (KOf G v) (idx G v a) ℓ = 0 := by omega
        rw [hz]
        exact (Nat.mul_zero _).symm
  · -- the shell block
    rw [sum_shellBlock_eq_shellPos
        (fun z => dhat G a v z * certY43 (avoidAttach G a v z).card),
      sumUpto_eq_sum_shellPos]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [dhatShell_eq_dhat hTF hReg hdeg hav hy, shellW_eq hTF hReg hdeg hav hy,
      cert_eq_certY43]
    by_cases h1 : G.graph.Adj a y
    · rw [if_pos h1, if_neg (fun hc => hc.1 h1)]
      exact (Nat.mul_zero _).symm
    · rw [if_neg h1]
      by_cases h2 : 1 ≤ (avoidAttach G a v y).card
      · rw [if_pos ⟨h1, h2⟩]
      · rw [if_neg (fun hc => h2 hc.2)]
        have hz : (avoidAttach G a v y).card = 0 := by omega
        rw [hz]
        exact (Nat.mul_zero _).symm

/-- **Obligation 13.**  The graph's total visible charge is the model's `charge`. -/
theorem visibleChargeTotal_eq_model (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size) :
    visibleChargeTotal G v = Delta4Model.charge (nOf G v) (KOf G v) (AOf G v) := by
  rw [visibleChargeTotal, Delta4Model.charge,
    sumUpto_four_eq_sum_rootNbrs hReg hdeg v
      (Delta4Model.chargeAt (nOf G v) (KOf G v) (AOf G v))]
  exact Finset.sum_congr rfl fun a ha =>
    visibleCharge_eq_model hTF hReg hdeg (mem_rootNbrs.mp ha)

/-! ## 8.  The shell objective (plan obligation 11)

The model carries the *doubled* objective, so the honest statement is `2 T = twoT`; the
`T = twoT / 2` form is a corollary and is stated second so the factor of two is never
implicit. -/

/-- **`2T = twoT`.**  `sum_T_restrict` puts the graph's edge sum on `S⁺`, `sum_pairsAdjOn_prod`
    doubles it into the ordered-pair sum, and the model's double fold is that sum read through
    the slot indexing. -/
theorem two_mul_shellObjective_eq_model (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size) :
    2 * (∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card)
      = Delta4Model.twoT (nOf G v) (KOf G v) (AOf G v) := by
  have hL : ∑ p ∈ pairsAdjOn G (shellPos G v),
        (attachSet G v p.1).card * (attachSet G v p.2).card
      = ∑ x ∈ shellPos G v, ∑ y ∈ shellPos G v,
          (if G.graph.Adj x y then 1 else 0)
            * (attachSet G v x).card * (attachSet G v y).card := by
    rw [pairsAdjOn, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    by_cases h : G.graph.Adj x y <;> simp [h]
  have hR : Delta4Model.twoT (nOf G v) (KOf G v) (AOf G v)
      = ∑ x ∈ shellPos G v, ∑ y ∈ shellPos G v,
          (if G.graph.Adj x y then 1 else 0)
            * (attachSet G v x).card * (attachSet G v y).card := by
    rw [Delta4Model.twoT, sumUpto_eq_sum_shellPos]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [sumUpto_eq_sum_shellPos]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [edg_at hTF hReg hdeg hx hy, kwt_KOf hReg hdeg (pos_lt hx),
      kwt_KOf hReg hdeg (pos_lt hy), shellAt_pos hx, shellAt_pos hy]
  rw [sum_T_restrict v, ← sum_pairsAdjOn_prod (shellPos G v) (fun u => (attachSet G v u).card),
    hL, hR]

/-- `T = twoT / 2`, the form the plan names.  Use `two_mul_shellObjective_eq_model` in proofs;
    this is the convenience wrapper. -/
theorem shellObjective_eq_model (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size) :
    (∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card)
      = Delta4Model.twoT (nOf G v) (KOf G v) (AOf G v) / 2 := by
  rw [← two_mul_shellObjective_eq_model hTF hReg hdeg v, Nat.mul_div_cancel_left _ (by norm_num)]

/-! ## 9.  The consumer shape

`henum` is an inequality in `12 T`; the model's leaf test is written in `6 · 2T` (plan §5, D13).
The two lemmas below do that bookkeeping once, so no later stage has to remember the factor of
two. -/

/-- **The model's leaf inequality, transported.**  `12 T = 6 · 2T`, so the model's
    `charge + 6 · twoT ≤ credit + 212` is exactly the graph's high-root obligation. -/
theorem visible_bound_of_model (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size)
    (h : Delta4Model.charge (nOf G v) (KOf G v) (AOf G v)
          + 6 * Delta4Model.twoT (nOf G v) (KOf G v) (AOf G v)
        ≤ Delta4Model.credit (nOf G v) (KOf G v) (AOf G v) + 212) :
    visibleChargeTotal G v
        + 12 * (∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card)
      ≤ visibleCreditTotal G v + 212 := by
  rw [visibleChargeTotal_eq_model hTF hReg hdeg v, visibleCreditTotal_eq_model hTF hReg hdeg v]
  have h2 := two_mul_shellObjective_eq_model hTF hReg hdeg v
  omega

/-- **`henum` at one root, from `leafOK`.**  The `twoT < 38` disjunct of the leaf test is the
    low-root branch, excluded here by `19 ≤ T`. -/
theorem visible_enumeration_at_of_leafOK (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size)
    (h : Delta4Model.leafOK (nOf G v) (KOf G v) (AOf G v) = true)
    (h19 : 19 ≤ ∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card) :
    visibleChargeTotal G v
        + 12 * (∑ p ∈ shellPairsLt G v, (attachSet G v p.1).card * (attachSet G v p.2).card)
      ≤ visibleCreditTotal G v + 212 := by
  have h2 := two_mul_shellObjective_eq_model hTF hReg hdeg v
  rw [Delta4Model.leafOK, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · exact visible_bound_of_model hTF hReg hdeg v h

/-! ## 10.  Non-vacuity guards

Both headline theorems equate a graph quantity with a model quantity, and both sides are
definitions in this tree, so an encoding that collapsed everything to zero would satisfy them.
The two facts below rule that out by pinning the transported quantities to numbers proved
*before* the model existed: the model's `credit` is `108` minus the unseen credit (so it is on
the scale of the analytic layer, not zero), and the two transports together reproduce
`conservativity_total`. -/

/-- **Guard 1.**  `credit` is `108` minus the unseen credit — in particular it equals `108`
    exactly at a root that sees all of its neighbours' shells. -/
theorem model_credit_add_unseen_eq (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size) :
    Delta4Model.credit (nOf G v) (KOf G v) (AOf G v)
        + ∑ a ∈ rootNbrs G v, ∑ z ∈ unseenAvoid G a v, 3 * (avoidAttach G a v z).card
      = 108 := by
  rw [← visibleCreditTotal_eq_model hTF hReg hdeg v, visibleCreditTotal,
    ← Finset.sum_add_distrib]
  have hpt : ∀ a ∈ rootNbrs G v,
      visibleCredit G a v + ∑ z ∈ unseenAvoid G a v, 3 * (avoidAttach G a v z).card = 27 := by
    intro a ha
    rw [visibleCredit]
    exact credit_split_eq_27 hTF hReg hdeg (mem_rootNbrs.mp ha).symm
  rw [Finset.sum_congr rfl hpt, Finset.sum_const, card_rootNbrs hReg hdeg v, smul_eq_mul]

/-- **Guard 2.**  Conservativity, read entirely in model quantities. -/
theorem model_conservativity (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size) :
    Delta4Model.credit (nOf G v) (KOf G v) (AOf G v)
        + 2 * (∑ a ∈ rootNbrs G v, avoidObjective G a v)
      ≤ 108 + Delta4Model.charge (nOf G v) (KOf G v) (AOf G v) := by
  rw [← visibleCreditTotal_eq_model hTF hReg hdeg v, ← visibleChargeTotal_eq_model hTF hReg hdeg v]
  exact conservativity_total hTF hReg hdeg v

end PentagonLocal

/-! ## 11.  What is left of Stage 4, stated exactly

With obligations 11, 12 and 13 closed, the whole *graph* side of `henum` is discharged: the
sharp Δ = 4 bound now follows from a statement with **no graph quantity in it at all** — that
the model's leaf test passes at every encoded root.  Closing that is the remaining Stage-4
work (obligation 10, `Box`, plus the search, obligations 17–21); nothing further about
pentagons, credit, charge or `T` is needed. -/

section ModelLeaf

open Finset
open scoped Classical
open PentagonLocal

/-- **The sharp Δ = 4 pentagon bound, conditional on the model's leaf test alone.**
    `P(G) ≤ 4|G|` for every triangle-free graph of maximum degree at most four, given only
    that `leafOK` holds at the encoding `(nOf, KOf, AOf)` of every root of every triangle-free
    4-regular graph.  Compare `pentagon_bound_delta4_of_visible_enumeration`, whose hypothesis
    still mentions `visibleChargeTotal`, `visibleCreditTotal` and `T`: obligations 11–13
    replace all three by `Nat` arithmetic on the encoded triple.

    This hypothesis is still not finite — it quantifies over all `H` — but it is now a
    statement *about the model*, which `Box` (obligation 10) plus the search (obligations
    17–21) collapse to a kernel check. -/
theorem pentagon_bound_delta4_of_model_leaf
    (hleaf : ∀ H : Flag emptyType, IsTriangleFree H → IsRegular H → maxDegree H = 4 →
      ∀ v : Fin H.size, Delta4Model.leafOK (nOf H v) (KOf H v) (AOf H v) = true)
    (G : Flag emptyType) (hTF : IsTriangleFree G) (hdeg : maxDegree G ≤ 4) :
    pentagonCount G ≤ 4 * G.size :=
  pentagon_bound_delta4_of_visible_enumeration
    (fun H hHTF hHReg hHdeg v h19 =>
      visible_enumeration_at_of_leafOK hHTF hHReg hHdeg v (hleaf H hHTF hHReg hHdeg v) h19)
    G hTF hdeg

end ModelLeaf

end Davey2024

section AxiomCheck
open Davey2024.PentagonLocal

end AxiomCheck
