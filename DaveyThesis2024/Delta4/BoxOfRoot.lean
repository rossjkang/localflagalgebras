import DaveyThesis2024.Delta4.Transport
import DaveyThesis2024.Delta4.BoxCore

/-!
# Δ = 4, obligation 10: the encoded rooted ball satisfies the model box

`Delta4Model.Box` has eleven clauses (`Delta4Model.BoxSpec`), and all eleven are proved here
*unconditionally* for the encoding `(nOf G v, KOf G v, AOf G v)` of an arbitrary root of an
arbitrary triangle-free 4-regular graph: `box_of_root`.

Ten of the clauses are properties of the rooted graph and are proved in §1 from
`IsTriangleFree`, `IsRegular` and `maxDegree = 4` alone.  The eleventh, `sorted` (clause D16,
"masks non-decreasing along the shell slots"), is **not** a property of the rooted graph: it
is a property of the enumeration `Transport.shellArr` chooses for `S⁺(v)`.  It is false for
the vertex-index order — in `C₁₀(1,3)` rooted at `0` the shell `2,4,6,8` carries masks
`11,7,14,13` — so `shellArr` is not the vertex-index order: it is that list re-sorted by
attachment mask (`Transport` §7.1), which makes (D16) true by construction
(`Transport.shellArr_pairwise`).  Re-pointing it costs nothing downstream, because every
support lemma the transport needs is proved at `Transport` §7.0 for an *arbitrary*
duplicate-free enumeration.

`box_of_root_of_sorted` is kept as the conditional form — the ten graph clauses, with (D16)
as the only hypothesis — so the split between "graph facts" and "labelling convention" stays
visible.
-/

namespace Davey2024
namespace PentagonLocal

open Finset
open scoped Classical

variable {G : Flag emptyType}

/-! ## 0.  Bit helpers -/

/-- A value below `2 ^ j` has no bit `j`. -/
private lemma bitv_eq_zero_of_lt {m j : ℕ} (h : m < 2 ^ j) : Delta4Model.bitv m j = 0 := by
  show m / 2 ^ j % 2 = 0
  rw [Nat.div_eq_of_lt h]

private lemma ite_lt_two (p : Prop) [Decidable p] : (if p then 1 else 0) < 2 := by
  split <;> omega

/-- The packed row of a shell slot is an `n`-bit number.  (`Transport.rowAt_lt` gives the
    weaker `< 4096`, which is the `A`-digit bound; clause `rowLt` needs `< 2 ^ n`.) -/
lemma rowAt_lt_two_pow (v : Fin G.size) (i : ℕ) : rowAt G v i < 2 ^ nOf G v :=
  Delta4Model.packD_lt (nOf G v) _ fun _ => ite_lt_two _

/-- A set shell-adjacency bit is an edge of `G`. -/
lemma adj_of_edg_eq_one {v : Fin G.size} (hn : nOf G v ≤ 12) {i j : ℕ}
    (hi : i < nOf G v) (hj : j < nOf G v) (h : Delta4Model.edg (AOf G v) i j = 1) :
    G.graph.Adj (shellAt G v i) (shellAt G v j) := by
  by_cases hadj : G.graph.Adj (shellAt G v i) (shellAt G v j)
  · exact hadj
  · rw [edg_AOf hn hi hj, if_neg hadj] at h
    exact absurd h (by omega)

/-! ## 1.  The ten unconditional clauses -/

/-- **(B1) mask positivity.**  Every recorded shell slot carries an attachment, because
    `shellPos` is exactly the shell block with positive attachment. -/
theorem maskPos_of_root (hReg : IsRegular G) (hdeg : maxDegree G = 4) {v : Fin G.size}
    {i : ℕ} (hi : i < nOf G v) : 1 ≤ Delta4Model.msk (KOf G v) i := by
  have hk : 1 ≤ Delta4Model.kwt (KOf G v) i := by
    rw [kwt_KOf hReg hdeg hi]
    exact (mem_shellPos.mp (shellAt_mem hi)).2
  rcases Nat.eq_zero_or_pos (Delta4Model.msk (KOf G v) i) with hm | hm
  · exfalso
    simp [Delta4Model.kwt, Delta4Model.hasL, Delta4Model.bitv, hm] at hk
  · exact hm

/-- Irreflexivity of the shell adjacency: `G` is a simple graph. -/
theorem irrefl_of_root {v : Fin G.size} (hn : nOf G v ≤ 12) {i : ℕ} (hi : i < nOf G v) :
    Delta4Model.edg (AOf G v) i i = 0 := by
  rw [edg_AOf hn hi hi, if_neg G.graph.irrefl]

/-- Symmetry of the shell adjacency. -/
theorem symm_of_root {v : Fin G.size} (hn : nOf G v ≤ 12) {i j : ℕ}
    (hi : i < nOf G v) (hj : j < nOf G v) :
    Delta4Model.edg (AOf G v) i j = Delta4Model.edg (AOf G v) j i := by
  rw [edg_AOf hn hi hj, edg_AOf hn hj hi]
  exact if_congr (G.graph.adj_comm _ _) rfl rfl

/-- **(B2) the degree cap**, from `shellPosDeg_add_attach_le4`. -/
theorem degCap_of_root (hTF : IsTriangleFree G) (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    {v : Fin G.size} {i : ℕ} (hi : i < nOf G v) :
    Delta4Model.kwt (KOf G v) i + Delta4Model.deg (nOf G v) (AOf G v) i ≤ 4 := by
  rw [kwt_KOf hReg hdeg hi, deg_AOf hTF hReg hdeg hi]
  exact shellPosDeg_add_attach_le4 (le_of_eq hdeg) v (shellAt G v i)

/-- **(B3) mask disjointness on a shell edge**, from triangle-freeness: a common root letter
    of two adjacent shell vertices would close a triangle.  Bits `≥ 4` vanish because a mask
    is a 4-bit digit. -/
theorem maskDisj_of_root (hTF : IsTriangleFree G) {v : Fin G.size} {i j : ℕ}
    (hi : i < nOf G v) (hj : j < nOf G v)
    (hadj : G.graph.Adj (shellAt G v i) (shellAt G v j)) :
    Delta4Model.msk (KOf G v) i &&& Delta4Model.msk (KOf G v) j = 0 := by
  refine (Delta4Model.land_eq_zero_iff _ _).2 fun t => ?_
  by_cases ht : t < 4
  · show Delta4Model.hasL (KOf G v) i t * Delta4Model.hasL (KOf G v) j t = 0
    rw [hasL_KOf hi ht, hasL_KOf hj ht]
    by_cases p : G.graph.Adj (shellAt G v i) (rootAt G v t)
    · by_cases q : G.graph.Adj (shellAt G v j) (rootAt G v t)
      · exact (hTF _ _ _ hadj q p).elim
      · rw [if_neg q, Nat.mul_zero]
    · rw [if_neg p, Nat.zero_mul]
  · have h16 : (16 : ℕ) ≤ 2 ^ t :=
      le_trans (by norm_num : (16 : ℕ) ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [bitv_eq_zero_of_lt (lt_of_lt_of_le (Delta4Model.msk_lt_16 (KOf G v) i) h16),
      Nat.zero_mul]

/-- **(B5) row disjointness on a shell edge**: two adjacent shell slots have no common
    positive-shell neighbour, again by triangle-freeness.  Bits `≥ n` vanish because a row is
    an `n`-bit number. -/
theorem rowDisj_of_root (hTF : IsTriangleFree G) {v : Fin G.size} (hn : nOf G v ≤ 12)
    {i j : ℕ} (hi : i < nOf G v) (hj : j < nOf G v)
    (hadj : G.graph.Adj (shellAt G v i) (shellAt G v j)) :
    Delta4Model.row (AOf G v) i &&& Delta4Model.row (AOf G v) j = 0 := by
  refine (Delta4Model.land_eq_zero_iff _ _).2 fun t => ?_
  by_cases ht : t < nOf G v
  · show Delta4Model.edg (AOf G v) i t * Delta4Model.edg (AOf G v) j t = 0
    rw [edg_AOf hn hi ht, edg_AOf hn hj ht]
    by_cases p : G.graph.Adj (shellAt G v i) (shellAt G v t)
    · by_cases q : G.graph.Adj (shellAt G v j) (shellAt G v t)
      · exact (hTF _ _ _ hadj q p).elim
      · rw [if_neg q, Nat.mul_zero]
    · rw [if_neg p, Nat.zero_mul]
  · have hlt : Delta4Model.row (AOf G v) i < 2 ^ t := by
      rw [row_AOf hn hi]
      exact lt_of_lt_of_le (rowAt_lt_two_pow v i)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [bitv_eq_zero_of_lt hlt, Nat.zero_mul]

/-- **The six clauses the model arithmetic consumes, unconditionally.**  `BoxCore` is
    `Box` minus the size bounds, the packing bounds, sortedness and the row half of
    (B3)/(B5); it is what `ModelArith`'s T-identity and `e₂₂ ≤ 6` run on. -/
theorem boxCore_of_root (hTF : IsTriangleFree G) (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    (v : Fin G.size) :
    Delta4Model.BoxDischarge.BoxCore (nOf G v) (KOf G v) (AOf G v) := by
  have hn : nOf G v ≤ 12 := card_shellPos_le_twelve hTF hReg hdeg v
  exact
    { maskPos := fun i hi => maskPos_of_root hReg hdeg hi
      sat := fun a ha => sum_hasL_eq_three hTF hReg hdeg ha
      irrefl := fun i hi => irrefl_of_root hn hi
      symm := fun i hi j hj => symm_of_root hn hi hj
      degCap := fun i hi => degCap_of_root hTF hReg hdeg hi
      maskDisj := fun i hi j hj hij =>
        maskDisj_of_root hTF hi hj (adj_of_edg_eq_one hn hi hj hij) }

/-- **(N), lower half.**  `3 ≤ n`, from (B1) + (B4) via `BoxCore.core_size_bounds`. -/
theorem nOf_ge_three (hTF : IsTriangleFree G) (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    (v : Fin G.size) : 3 ≤ nOf G v :=
  (Delta4Model.BoxDischarge.core_size_bounds (boxCore_of_root hTF hReg hdeg v)).1

/-- Canonical packing of `K`: no base-16 digits above the shell. -/
theorem packK_of_root (v : Fin G.size) : KOf G v < 16 ^ nOf G v :=
  Delta4Model.packD_lt (nOf G v) (maskAt G v) (maskAt_lt v)

/-- Canonical packing of `A`: no base-4096 digits above the shell. -/
theorem packA_of_root {v : Fin G.size} (hn : nOf G v ≤ 12) : AOf G v < 4096 ^ nOf G v :=
  Delta4Model.packD_lt (nOf G v) (rowAt G v) fun _ => rowAt_lt hn _

/-- Each row uses only the `n` shell bits. -/
theorem rowLt_of_root {v : Fin G.size} (hn : nOf G v ≤ 12) {i : ℕ} (hi : i < nOf G v) :
    Delta4Model.row (AOf G v) i < 2 ^ nOf G v := by
  rw [row_AOf hn hi]; exact rowAt_lt_two_pow v i

/-! ## 2.  `Box`, modulo the sortedness clause

Clause `sorted` (D16) is the one clause of `BoxSpec` that is not a statement about the rooted
graph: the masks are read off in the order `Transport.shellArr` lists `S⁺(v)`, and no property
of the *graph* forces any particular order.  Read in **vertex** order it genuinely fails: in
the circulant `C₁₀(1,3)` rooted at `0` the root letters are `1 < 3 < 7 < 9` and the shell is
`2, 4, 6, 8` with masks `11, 7, 14, 13` — already `msk 0 = 11 > 7 = msk 1`.  (Measured over
188 triangle-free 4-regular hosts — circulants `C_n(i,j)` for `9 ≤ n ≤ 20`, `K₄,₄`, `Q₄` and
40 random 4-regular graphs on 12…22 vertices — 3221 of 3253 roots have non-monotone masks in
vertex order; the 32 exceptions are the highly symmetric `K₄,₄` and half of `Q₄`.)  All ten
other clauses hold at every one of those roots — they are proved above with no hypothesis
beyond `hTF`, `hReg`, `hdeg`.

That is why `shellArr` enumerates `S⁺(v)` in mask order instead; §3 turns
`Transport.shellArr_pairwise` into the hypothesis of the theorem below, and §4 discharges it. -/

/-- **Obligation 10, conditional on D16.**  Every clause of `Box` except sortedness is
    discharged from `IsTriangleFree`, `IsRegular` and `maxDegree = 4` alone. -/
theorem box_of_root_of_sorted (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) (v : Fin G.size)
    (hsorted : ∀ i, i < nOf G v - 1 →
      Delta4Model.msk (KOf G v) i ≤ Delta4Model.msk (KOf G v) (i + 1)) :
    Delta4Model.Box (nOf G v) (KOf G v) (AOf G v) = true := by
  have hn : nOf G v ≤ 12 := card_shellPos_le_twelve hTF hReg hdeg v
  refine (Delta4Model.box_iff _ _ _).2 ?_
  exact
    { size_lb := nOf_ge_three hTF hReg hdeg v
      size_ub := hn
      packK := packK_of_root v
      packA := packA_of_root hn
      rowLt := fun i hi => rowLt_of_root hn hi
      maskPos := fun i hi => maskPos_of_root hReg hdeg hi
      sorted := hsorted
      sat := fun a ha => sum_hasL_eq_three hTF hReg hdeg ha
      irrefl := fun i hi => irrefl_of_root hn hi
      symm := fun i hi j hj => symm_of_root hn hi hj
      degCap := fun i hi => degCap_of_root hTF hReg hdeg hi
      edgeDisj := fun i hi j hj => by
        by_cases hadj : G.graph.Adj (shellAt G v i) (shellAt G v j)
        · exact Or.inr ⟨maskDisj_of_root hTF hi hj hadj, rowDisj_of_root hTF hn hi hj hadj⟩
        · exact Or.inl (by rw [edg_AOf hn hi hj, if_neg hadj]) }

/-! ## 3.  The sortedness clause, read on the graph

`Transport.maskOf G v x` is the attachment mask of a *vertex* (not of a slot), and
`maskAt G v i = maskOf G v (shellAt G v i)` holds by definition, so the model's `msk` is that
function read along the shell enumeration.  Since `Transport.shellArr` *is* the mask-sorted
enumeration, the clause is exactly `Transport.shellArr_pairwise`. -/

lemma maskAt_eq_maskOf (v : Fin G.size) (i : ℕ) : maskAt G v i = maskOf G v (shellAt G v i) :=
  rfl

theorem msk_KOf_eq_maskOf {v : Fin G.size} {i : ℕ} (hi : i < nOf G v) :
    Delta4Model.msk (KOf G v) i = maskOf G v (shellAt G v i) := by
  rw [msk_KOf hi, maskAt_eq_maskOf]

private lemma getD_eq_getElem₂ {α : Type*} {l : List α} {i : ℕ} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- **The masks are non-decreasing along the shell slots.**  This is what `shellArr` is: the
    positive shell enumerated in non-decreasing mask order (`Transport` §7.1).  Note that it
    is a fact about the *enumeration*, proved from `shellArr_pairwise`; no hypothesis on `G`
    is needed. -/
lemma maskOf_shellAt_le {v : Fin G.size} {i j : ℕ} (hj : j < nOf G v) (hij : i < j) :
    maskOf G v (shellAt G v i) ≤ maskOf G v (shellAt G v j) := by
  have hi' : i < (shellArr G v).length := by rw [shellArr_length]; omega
  have hj' : j < (shellArr G v).length := by rw [shellArr_length]; exact hj
  have hp := List.pairwise_iff_getElem.mp (shellArr_pairwise v) i j hi' hj' hij
  have ei : shellAt G v i = (shellArr G v)[i] := getD_eq_getElem₂ hi'
  have ej : shellAt G v j = (shellArr G v)[j] := getD_eq_getElem₂ hj'
  rw [ei, ej]
  exact hp

/-! ## 4.  Obligation 10, unconditionally -/

/-- **OBLIGATION 10.**  The encoding `(nOf G v, KOf G v, AOf G v)` of *every* root of *every*
    triangle-free 4-regular graph satisfies `Delta4Model.Box`.  No hypothesis beyond
    `IsTriangleFree`, `IsRegular` and `maxDegree = 4`; in particular no assumption on the
    vertex labelling, because `Transport.shellArr` canonicalises the shell order itself.

    This is what `Delta4Assembly.BoxOfRoot` names, so the assembly's theorems — and hence the
    reduction of `P(G) ≤ 4|G|` to the single closed `Bool` `checkAll` — are no longer
    conditional on anything but that `Bool`. -/
theorem box_of_root (hTF : IsTriangleFree G) (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    (v : Fin G.size) : Delta4Model.Box (nOf G v) (KOf G v) (AOf G v) = true := by
  refine box_of_root_of_sorted hTF hReg hdeg v fun i hi => ?_
  have h1 : i + 1 < nOf G v := by omega
  rw [msk_KOf_eq_maskOf (by omega), msk_KOf_eq_maskOf h1]
  exact maskOf_shellAt_le h1 (Nat.lt_succ_self i)

/-! ## 5.  The enumeration, as a standalone fact

The shell enumeration is a duplicate-free, mask-sorted listing of `S⁺(v)` of the right
length — the four properties §4 and the transport consume, collected in one place. -/

/-- `Transport.shellArr` is a duplicate-free enumeration of `S⁺(v)` along which the masks are
    non-decreasing. -/
theorem exists_maskSorted_enumeration (v : Fin G.size) :
    ∃ L : List (Fin G.size), L.Nodup ∧ (∀ x, x ∈ L ↔ x ∈ shellPos G v) ∧
      L.length = nOf G v ∧ L.Pairwise (fun x y => maskOf G v x ≤ maskOf G v y) :=
  ⟨shellArr G v, shellArr_nodup v, mem_shellArr v, shellArr_length v, shellArr_pairwise v⟩

end PentagonLocal
end Davey2024
