import DaveyThesis2024.Delta4.Model
import DaveyThesis2024.PentagonDelta4

/-!
# Δ = 4: transporting a rooted graph into the finite model

Obligation 4 of the merged Stage-4 plan, identified as the residual risk once
the rank-1 row was retired: the model's punctured attachment weights `rootW` and `shellW` really
do reproduce `(avoidAttach G a v z).card`.  With the indexing maps `nOf`/`KOf`/`AOf` this is
what lets a rooted graph be replaced by three natural numbers.
-/

namespace Delta4Model

/-! ## 6.  ADDITIONS (not in the plan's canonical model)

Two additions, both forced by obligation 4 and neither touching any canonical definition.

* `packD b f n = ∑_{i<n} f i · b^i`, the little-endian digit packer, plus `packD_lt` and
  `digit_packD`.  The plan's obligation 6 packs a `List ℕ`; obligation 4 needs the packer
  applied to a *function* (`fun i => mask of shell slot i`), because the indexing map
  `shellAt` is a function, not a list, and routing through a list would add a
  `List.getD`-vs-function agreement lemma for nothing.  `digit_packD` is stated once at a
  general base and instantiated three times: at `b = 16` it is `msk_KOf`, at `b = 4096` it is
  `row_AOf`, and at `b = 2` it is the bit-extraction inside a single mask or row.  This is the
  same content as obligation 6 in the shape obligation 4 consumes; a `List` version follows
  from it by `packD b (l.getD · 0) l.length`.
* `sumUpto_eq_sum_range`, the bridge from the model's structural fold to `Finset.sum`, so the
  transport can use `Finset.sum_nbij'`.
-/

/-- `∑_{i<n} f i · b^i`, little-endian, structurally recursive. -/
def packD (b : Nat) (f : Nat → Nat) : Nat → Nat
  | 0   => 0
  | n+1 => f 0 + b * packD b (fun i => f (i+1)) n

theorem packD_lt {b : Nat} :
    ∀ (n : Nat) (f : Nat → Nat), (∀ i, f i < b) → packD b f n < b ^ n := by
  intro n
  induction n with
  | zero => intro f _; simp [packD]
  | succ n ih =>
      intro f hf
      have h : packD b (fun i => f (i+1)) n + 1 ≤ b ^ n := ih (fun i => f (i+1)) fun i => hf (i+1)
      have hf0 := hf 0
      calc packD b f (n+1)
          = f 0 + b * packD b (fun i => f (i+1)) n := rfl
        _ < b + b * packD b (fun i => f (i+1)) n := by omega
        _ = b * (packD b (fun i => f (i+1)) n + 1) := by ring
        _ ≤ b * b ^ n := Nat.mul_le_mul_left b h
        _ = b ^ (n+1) := by rw [pow_succ]; ring

/-- Digit `i` of `packD b f n` is `f i`, for every slot inside the packed range. -/
theorem digit_packD {b : Nat} (hb : 0 < b) :
    ∀ (n : Nat) (f : Nat → Nat), (∀ i, f i < b) → ∀ i, i < n →
      packD b f n / b ^ i % b = f i := by
  intro n
  induction n with
  | zero => intro f _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      intro f hf i hi
      have hpk : packD b f (n+1) = f 0 + b * packD b (fun j => f (j+1)) n := rfl
      match i with
      | 0 => rw [hpk, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
               Nat.mod_eq_of_lt (hf 0)]
      | i+1 =>
          have hdiv : (f 0 + b * packD b (fun j => f (j+1)) n) / b
              = packD b (fun j => f (j+1)) n := by
            rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt (hf 0), Nat.zero_add]
          have hstep : packD b f (n+1) / b ^ (i+1)
              = packD b (fun j => f (j+1)) n / b ^ i := by
            rw [pow_succ', ← Nat.div_div_eq_div_mul, hpk, hdiv]
          rw [hstep]
          exact ih (fun j => f (j+1)) (fun j => hf (j+1)) i (Nat.lt_of_succ_lt_succ hi)

/-- The structural fold is the `Finset.range` sum. -/
theorem sumUpto_eq_sum_range (f : Nat → Nat) (n : Nat) :
    sumUpto f n 0 = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumUpto_succ, ih, Finset.sum_range_succ]
end Delta4Model

namespace Davey2024
namespace PentagonLocal


open Finset
open scoped Classical

variable {G : Flag emptyType}

/-! ## 7.  The indexing maps (plan obligation 8)

`orderIsoOfFin` is the plan's suggestion; a *list* is used instead, because the model is
`ℕ`-indexed and `Fin (nOf G v)` would have to be cast at every use.  All the transport asks of
that list is that it be a duplicate-free enumeration of the block it indexes — §7.0 proves the
five support lemmas at that generality — so the shell list is free to be reordered, and §7.1
reorders it by attachment mask to make `Box`'s clause (D16) true by construction.

Out-of-range slots return the root `v`, which lies in neither `rootNbrs G v` nor
`shellPos G v` and is adjacent to no shell vertex — so an out-of-range letter contributes a
zero bit and nothing downstream has to case on the range. -/

/-- `List.getD` at an in-range index, from the core `getD?` lemma (`Mathlib.Data.List.GetD`
    is not in this file's import closure, and obligation 4 should not widen it). -/
private lemma getD_eq_getElem' {α : Type*} {l : List α} {i : ℕ} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- A one-bit digit is a digit. -/
private lemma ite_one_zero_lt_two (p : Prop) [Decidable p] : (if p then 1 else 0) < 2 := by
  split <;> omega

/-! ### 7.0  The five properties the transport asks of an enumeration

The shell enumeration below is **not** the vertex-index sort, so the support lemmas are proved
once for an *arbitrary* duplicate-free enumeration of a finset and then instantiated twice:
at the vertex-index sort (for `rootArr`) and at the mask sort (for `shellArr`).  Nothing in
this section — and nothing downstream of it — mentions the order of the enumeration. -/

section Enumeration

variable {S : Finset (Fin G.size)} {L : List (Fin G.size)} {d : Fin G.size}

/-- A duplicate-free enumeration has the finset's cardinality. -/
lemma enum_length (hmem : ∀ x, x ∈ L ↔ x ∈ S) (hnd : L.Nodup) : L.length = S.card := by
  classical
  have hfin : L.toFinset = S := by ext x; rw [List.mem_toFinset]; exact hmem x
  rw [← List.toFinset_card_of_nodup hnd, hfin]

/-- An enumeration lands in the finset. -/
lemma enum_getD_mem (hmem : ∀ x, x ∈ L ↔ x ∈ S) {i : ℕ} (hi : i < L.length) :
    L.getD i d ∈ S := by
  rw [getD_eq_getElem' hi]
  exact (hmem _).1 (List.getElem_mem hi)

/-- A member of the finset occupies a slot. -/
lemma enum_idxOf_lt (hmem : ∀ x, x ∈ L ↔ x ∈ S) {x : Fin G.size} (hx : x ∈ S) :
    L.idxOf x < L.length :=
  List.idxOf_lt_length_iff.2 ((hmem x).2 hx)

/-- Slot-of-vertex, then vertex-of-slot. -/
lemma enum_getD_idxOf (hmem : ∀ x, x ∈ L ↔ x ∈ S) {x : Fin G.size} (hx : x ∈ S) :
    L.getD (L.idxOf x) d = x := by
  have hlt : L.idxOf x < L.length := enum_idxOf_lt hmem hx
  rw [getD_eq_getElem' hlt]
  exact List.getElem_idxOf hlt

/-- Vertex-of-slot, then slot-of-vertex; this is where `Nodup` is consumed. -/
lemma enum_idxOf_getD (hnd : L.Nodup) {i : ℕ} (hi : i < L.length) :
    L.idxOf (L.getD i d) = i := by
  rw [getD_eq_getElem' hi]
  exact List.Nodup.idxOf_getElem hnd i hi

/-- The index transport, for an arbitrary duplicate-free enumeration. -/
lemma enum_sum_range (hmem : ∀ x, x ∈ L ↔ x ∈ S) (hnd : L.Nodup) (f : Fin G.size → ℕ) :
    ∑ i ∈ Finset.range L.length, f (L.getD i d) = ∑ x ∈ S, f x := by
  refine Finset.sum_nbij' (fun i => L.getD i d) (fun x => L.idxOf x) ?_ ?_ ?_ ?_ ?_
  · exact fun i hi => enum_getD_mem hmem (Finset.mem_range.1 hi)
  · exact fun x hx => Finset.mem_range.2 (enum_idxOf_lt hmem hx)
  · exact fun i hi => enum_idxOf_getD hnd (Finset.mem_range.1 hi)
  · exact fun x hx => enum_getD_idxOf hmem hx
  · exact fun _ _ => rfl

end Enumeration

/-! ### 7.1  The two arrays

`rootArr` is the vertex-index sort of the root neighbourhood; which of the four neighbours
gets which letter is immaterial and nothing downstream reads the order.

`shellArr` is **not** the vertex-index sort.  `Delta4Model.Box` carries clause (D16), "masks
non-decreasing along the slots", and the vertex order has no reason to satisfy it — in
`C₁₀(1,3)` rooted at `0` the shell `2,4,6,8` carries masks `11,7,14,13`.  So the shell is
enumerated in non-decreasing **mask** order: the vertex-index sort re-sorted by
`maskOf`, which makes (D16) true by construction (`shellArr_pairwise`) and leaves every other
transport lemma untouched, since all of them go through §7.0.

There is no circularity: `maskOf` reads adjacency to `rootAt`, i.e. to `rootArr`, and never
mentions `shellArr`.  (`List.insertionSort` is stable, so ties in the mask are still broken by
vertex index; nothing depends on that.) -/

/-- The root neighbourhood, sorted: slots `0,1,2,3` are the four root letters. -/
noncomputable def rootArr (G : Flag emptyType) (v : Fin G.size) : List (Fin G.size) :=
  (rootNbrs G v).sort (· ≤ ·)

/-- Root letter `a` as a vertex; out of range, the root `v`. -/
noncomputable def rootAt (G : Flag emptyType) (v : Fin G.size) (a : ℕ) : Fin G.size :=
  (rootArr G v).getD a v

/-- The 4-bit attachment mask of a shell **vertex**: bit `a` says the vertex sees root letter
    `a`.  It depends on `rootArr` only, which is what lets `shellArr` be sorted by it. -/
noncomputable def maskOf (G : Flag emptyType) (v x : Fin G.size) : ℕ :=
  Delta4Model.packD 2 (fun a => if G.graph.Adj x (rootAt G v a) then 1 else 0) 4

/-- The positive shell, enumerated in non-decreasing attachment-mask order: slots
    `0,…,n-1`.  This is clause (D16) of `Delta4Model.Box`, made true by construction. -/
noncomputable def shellArr (G : Flag emptyType) (v : Fin G.size) : List (Fin G.size) :=
  List.insertionSort (fun x y => maskOf G v x ≤ maskOf G v y) ((shellPos G v).sort (· ≤ ·))

/-- `n = |S⁺(v)|`, the model's shell size. -/
noncomputable def nOf (G : Flag emptyType) (v : Fin G.size) : ℕ := (shellPos G v).card

/-- Shell slot `i` as a vertex; out of range, the root `v`. -/
noncomputable def shellAt (G : Flag emptyType) (v : Fin G.size) (i : ℕ) : Fin G.size :=
  (shellArr G v).getD i v

/-- The root letter of a root neighbour. -/
noncomputable def idx (G : Flag emptyType) (v : Fin G.size) (b : Fin G.size) : ℕ :=
  (rootArr G v).idxOf b

/-- The shell slot of a positive shell vertex. -/
noncomputable def pos (G : Flag emptyType) (v : Fin G.size) (x : Fin G.size) : ℕ :=
  (shellArr G v).idxOf x

/-! ### 7.2  Both arrays are duplicate-free enumerations -/

lemma mem_rootArr (v : Fin G.size) : ∀ x, x ∈ rootArr G v ↔ x ∈ rootNbrs G v :=
  fun _ => Finset.mem_sort (· ≤ ·)

lemma rootArr_nodup (v : Fin G.size) : (rootArr G v).Nodup := Finset.sort_nodup _ _

lemma rootArr_length (v : Fin G.size) : (rootArr G v).length = (rootNbrs G v).card :=
  enum_length (mem_rootArr v) (rootArr_nodup v)

lemma mem_shellArr (v : Fin G.size) : ∀ x, x ∈ shellArr G v ↔ x ∈ shellPos G v := by
  intro x
  rw [shellArr, List.mem_insertionSort]
  exact Finset.mem_sort (· ≤ ·)

lemma shellArr_nodup (v : Fin G.size) : (shellArr G v).Nodup :=
  ((List.perm_insertionSort _ _).nodup_iff).2 (Finset.sort_nodup _ _)

lemma shellArr_length (v : Fin G.size) : (shellArr G v).length = nOf G v :=
  enum_length (mem_shellArr v) (shellArr_nodup v)

/-- **The shell enumeration is mask-sorted.**  This is the whole point of the insertion sort,
    and it is what discharges clause (D16) of `Delta4Model.Box` in `BoxOfRoot.lean`. -/
lemma shellArr_pairwise (v : Fin G.size) :
    (shellArr G v).Pairwise (fun x y => maskOf G v x ≤ maskOf G v y) := by
  haveI : IsTrans (Fin G.size) (fun x y => maskOf G v x ≤ maskOf G v y) :=
    ⟨fun _ _ _ h₁ h₂ => Nat.le_trans h₁ h₂⟩
  haveI : Std.Total (fun x y : Fin G.size => maskOf G v x ≤ maskOf G v y) :=
    ⟨fun _ _ => Nat.le_total _ _⟩
  exact List.pairwise_insertionSort _ _

/-! ### 7.3  The five support lemmas, at the two arrays -/

lemma shellAt_mem {v : Fin G.size} {i : ℕ} (hi : i < nOf G v) :
    shellAt G v i ∈ shellPos G v :=
  enum_getD_mem (mem_shellArr v) (by rw [shellArr_length]; exact hi)

lemma rootAt_mem {v : Fin G.size} {a : ℕ} (ha : a < (rootNbrs G v).card) :
    rootAt G v a ∈ rootNbrs G v :=
  enum_getD_mem (mem_rootArr v) (by rw [rootArr_length]; exact ha)

lemma pos_lt {v x : Fin G.size} (hx : x ∈ shellPos G v) : pos G v x < nOf G v := by
  have h := enum_idxOf_lt (mem_shellArr v) hx
  rwa [shellArr_length] at h

lemma shellAt_pos {v x : Fin G.size} (hx : x ∈ shellPos G v) :
    shellAt G v (pos G v x) = x := enum_getD_idxOf (mem_shellArr v) hx

lemma pos_shellAt {v : Fin G.size} {i : ℕ} (hi : i < nOf G v) :
    pos G v (shellAt G v i) = i :=
  enum_idxOf_getD (shellArr_nodup v) (by rw [shellArr_length]; exact hi)

lemma idx_lt {v b : Fin G.size} (hb : b ∈ rootNbrs G v) :
    idx G v b < (rootNbrs G v).card := by
  have h := enum_idxOf_lt (mem_rootArr v) hb
  rwa [rootArr_length] at h

lemma rootAt_idx {v b : Fin G.size} (hb : b ∈ rootNbrs G v) : rootAt G v (idx G v b) = b :=
  enum_getD_idxOf (mem_rootArr v) hb

lemma idx_rootAt {v : Fin G.size} {a : ℕ} (ha : a < (rootNbrs G v).card) :
    idx G v (rootAt G v a) = a :=
  enum_idxOf_getD (rootArr_nodup v) (by rw [rootArr_length]; exact ha)

/-- `idx` lands in the four letters.  Only `maxDegree G ≤ 4` is needed: the root letters are
    the root's neighbours and there are at most four of them.  Regularity is *not* used. -/
lemma idx_lt_four_of_maxDegree (hΔ : maxDegree G ≤ 4) {v b : Fin G.size}
    (hb : b ∈ rootNbrs G v) : idx G v b < 4 :=
  lt_of_lt_of_le (idx_lt hb) (deg_le_of_maxDegree_le hΔ v)

/-- `idx` lands in the four letters, on a 4-regular graph.  Stated with `hReg` for uniformity
    with the rest of the transport layer, which always has it; it is not used. -/
lemma idx_lt_four (_hReg : IsRegular G) (hdeg : maxDegree G = 4) {v b : Fin G.size}
    (hb : b ∈ rootNbrs G v) : idx G v b < 4 :=
  idx_lt_four_of_maxDegree (le_of_eq hdeg) hb

/-- The index transport, at the positive shell. -/
lemma sum_range_shellAt (v : Fin G.size) (f : Fin G.size → ℕ) :
    ∑ i ∈ Finset.range (nOf G v), f (shellAt G v i) = ∑ x ∈ shellPos G v, f x := by
  rw [← shellArr_length (G := G) v]
  exact enum_sum_range (mem_shellArr v) (shellArr_nodup v) f

/-! ## 8.  The encoding `(n, K, A)` of the rooted ball -/

/-- The 4-bit attachment mask of shell slot `i`. -/
noncomputable def maskAt (G : Flag emptyType) (v : Fin G.size) (i : ℕ) : ℕ :=
  Delta4Model.packD 2 (fun a => if G.graph.Adj (shellAt G v i) (rootAt G v a) then 1 else 0) 4

/-- The `n`-bit positive-shell adjacency row of shell slot `i`. -/
noncomputable def rowAt (G : Flag emptyType) (v : Fin G.size) (i : ℕ) : ℕ :=
  Delta4Model.packD 2
    (fun j => if G.graph.Adj (shellAt G v i) (shellAt G v j) then 1 else 0) (nOf G v)

/-- `K`: the base-16 packing of the masks. -/
noncomputable def KOf (G : Flag emptyType) (v : Fin G.size) : ℕ :=
  Delta4Model.packD 16 (maskAt G v) (nOf G v)

/-- `A`: the base-4096 packing of the rows. -/
noncomputable def AOf (G : Flag emptyType) (v : Fin G.size) : ℕ :=
  Delta4Model.packD 4096 (rowAt G v) (nOf G v)

lemma maskAt_lt (v : Fin G.size) (i : ℕ) : maskAt G v i < 16 := by
  have := Delta4Model.packD_lt (b := 2) 4
    (fun a => if G.graph.Adj (shellAt G v i) (rootAt G v a) then 1 else 0)
    (fun a => ite_one_zero_lt_two _)
  simpa [maskAt] using this

lemma rowAt_lt {v : Fin G.size} (hn : nOf G v ≤ 12) (i : ℕ) : rowAt G v i < 4096 := by
  have h := Delta4Model.packD_lt (b := 2) (nOf G v)
    (fun j => if G.graph.Adj (shellAt G v i) (shellAt G v j) then 1 else 0)
    (fun a => ite_one_zero_lt_two _)
  have hpow : (2 : ℕ) ^ nOf G v ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hn
  exact lt_of_lt_of_le h (by simpa using hpow)

/-- Digit extraction for `K`. -/
lemma msk_KOf {v : Fin G.size} {i : ℕ} (hi : i < nOf G v) :
    Delta4Model.msk (KOf G v) i = maskAt G v i :=
  Delta4Model.digit_packD (by norm_num) (nOf G v) (maskAt G v) (maskAt_lt v) i hi

/-- Digit extraction for `A`. -/
lemma row_AOf {v : Fin G.size} (hn : nOf G v ≤ 12) {i : ℕ} (hi : i < nOf G v) :
    Delta4Model.row (AOf G v) i = rowAt G v i :=
  Delta4Model.digit_packD (by norm_num) (nOf G v) (rowAt G v) (fun _ => rowAt_lt hn _) i hi

/-- **The letter bit is adjacency to the root letter.** -/
lemma hasL_KOf {v : Fin G.size} {i a : ℕ} (hi : i < nOf G v) (ha : a < 4) :
    Delta4Model.hasL (KOf G v) i a
      = if G.graph.Adj (shellAt G v i) (rootAt G v a) then 1 else 0 := by
  rw [Delta4Model.hasL, msk_KOf hi, maskAt]
  exact Delta4Model.digit_packD (by norm_num) 4 _ (fun a => ite_one_zero_lt_two _) a ha

/-- **The shell adjacency bit is adjacency in `G`.** -/
lemma edg_AOf {v : Fin G.size} (hn : nOf G v ≤ 12) {i j : ℕ}
    (hi : i < nOf G v) (hj : j < nOf G v) :
    Delta4Model.edg (AOf G v) i j
      = if G.graph.Adj (shellAt G v i) (shellAt G v j) then 1 else 0 := by
  rw [Delta4Model.edg, row_AOf hn hi, rowAt]
  exact Delta4Model.digit_packD (by norm_num) (nOf G v) _
    (fun a => ite_one_zero_lt_two _) j hj

/-! ## 9.  Obligation 4 — the model's attachment weights are the graph's punctured counts

`rootW` and `shellW` are the two halves of `k_a(z) = |N(a) ∩ N(z) \ {v}|` along the
decomposition `visibleAvoid_eq` landed at the gate: the root half indexes `z` by a root
letter, the shell half by a shell slot.  Both reduce to one set identity,
`avoidAttach_eq_filter_shellPos`, which is obligation 2 restated: **every neighbour of a root
neighbour other than the root is a positive shell vertex**, so the punctured attachment set is
a subset of `S⁺(v)` and is counted by the model's `n` slots. -/

/-- `(if p then 1 else 0) * (if q then 1 else 0) = if p ∧ q then 1 else 0`. -/
private lemma ite_and_mul (p q : Prop) [Decidable p] [Decidable q] :
    (if p then 1 else 0) * (if q then 1 else 0) = if p ∧ q then (1:ℕ) else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- **The punctured attachment set lives on the positive shell.**  For *every* `z`,
    `k_a(z) = (N(a) ∩ N(z)) \ {v}` is exactly the set of `S⁺(v)`-vertices adjacent to both
    `a` and `z`.  Triangle-freeness is consumed here, through obligation 2. -/
theorem avoidAttach_eq_filter_shellPos (hTF : IsTriangleFree G) {a v : Fin G.size}
    (hav : G.graph.Adj v a) (z : Fin G.size) :
    avoidAttach G a v z
      = (shellPos G v).filter (fun x => G.graph.Adj x a ∧ G.graph.Adj x z) := by
  ext w
  simp only [avoidAttach, attachSet, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨hwv, haw, hzw⟩
    exact ⟨nbr_of_rootNbr_mem_shellPos hTF hav haw hwv, haw.symm, hzw.symm⟩
  · rintro ⟨hw, haw, hzw⟩
    exact ⟨(mem_shellSet'.mp (mem_shellPos.mp hw).1).1, haw.symm, hzw.symm⟩

/-- The counting form of `avoidAttach_eq_filter_shellPos`. -/
theorem card_avoidAttach_eq (hTF : IsTriangleFree G) {a v : Fin G.size}
    (hav : G.graph.Adj v a) (z : Fin G.size) :
    (avoidAttach G a v z).card
      = ∑ x ∈ shellPos G v, (if G.graph.Adj x a ∧ G.graph.Adj x z then 1 else 0) := by
  rw [avoidAttach_eq_filter_shellPos hTF hav z, Finset.card_filter]

/-- **Obligation 4, root half.**  For a root neighbour `b ≠ a`, the punctured attachment
    count `k_a(b)` is the model's `rootW`: the number of shell slots carrying both root
    letters. -/
theorem avoidAttach_card_root (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) {a v b : Fin G.size} (hav : G.graph.Adj v a)
    (hb : b ∈ (rootNbrs G v).erase a) :
    (avoidAttach G a v b).card
      = Delta4Model.rootW (nOf G v) (KOf G v) (idx G v a) (idx G v b) := by
  have hbN : b ∈ rootNbrs G v := Finset.mem_of_mem_erase hb
  have haN : a ∈ rootNbrs G v := mem_rootNbrs.mpr hav
  have hia : idx G v a < 4 := idx_lt_four hReg hdeg haN
  have hib : idx G v b < 4 := idx_lt_four hReg hdeg hbN
  simp only [Delta4Model.rootW, Delta4Model.sumUpto_eq_sum_range]
  rw [card_avoidAttach_eq hTF hav,
    ← sum_range_shellAt v (fun x => if G.graph.Adj x a ∧ G.graph.Adj x b then 1 else 0)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < nOf G v := Finset.mem_range.mp hi
  rw [hasL_KOf hi' hia, hasL_KOf hi' hib, rootAt_idx haN, rootAt_idx hbN, ite_and_mul]

/-- **Obligation 4, shell half.**  For a positive shell vertex `y` not adjacent to `a`, the
    punctured attachment count `k_a(y)` is the model's `shellW`: the number of shell slots
    carrying the root letter `a` and adjacent to slot `y`.  The leading factor
    `1 − hasL K y a` of `shellW` is `1` exactly because `¬ Adj a y`. -/
theorem avoidAttach_card_shell (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) {a v y : Fin G.size} (hav : G.graph.Adj v a)
    (hy : y ∈ shellPos G v) (hay : ¬ G.graph.Adj a y) :
    (avoidAttach G a v y).card
      = Delta4Model.shellW (nOf G v) (KOf G v) (AOf G v) (idx G v a) (pos G v y) := by
  have hn : nOf G v ≤ 12 := card_shellPos_le_twelve hTF hReg hdeg v
  have haN : a ∈ rootNbrs G v := mem_rootNbrs.mpr hav
  have hia : idx G v a < 4 := idx_lt_four hReg hdeg haN
  have hpy : pos G v y < nOf G v := pos_lt hy
  have hsy : shellAt G v (pos G v y) = y := shellAt_pos hy
  have hfac : Delta4Model.hasL (KOf G v) (pos G v y) (idx G v a) = 0 := by
    rw [hasL_KOf hpy hia, rootAt_idx haN, hsy, if_neg (fun h => hay h.symm)]
  simp only [Delta4Model.shellW, hfac, Nat.sub_zero, Nat.one_mul,
    Delta4Model.sumUpto_eq_sum_range]
  rw [card_avoidAttach_eq hTF hav,
    ← sum_range_shellAt v (fun x => if G.graph.Adj x a ∧ G.graph.Adj x y then 1 else 0)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < nOf G v := Finset.mem_range.mp hi
  rw [hasL_KOf hi' hia, rootAt_idx haN, edg_AOf hn hpy hi', hsy, ite_and_mul]
  exact if_congr (and_congr_right fun _ => G.graph.adj_comm _ _) rfl rfl

/-! ## 10.  Non-vacuity guards for the encoding

Obligation 4 is an equation between a graph count and a model count, and both sides are
definitions written in this file, so it could in principle be satisfied by a degenerate
encoding (all-zero masks on both sides).  The two lemmas below rule that out by tying the
encoding to facts proved *before* the model existed:

* `kwt_KOf`: the popcount of the mask of slot `i` is `|A_{x_i}|`, the attachment count of the
  corresponding shell vertex — the plan's obligation 8 (`wt_maskNat`).
* `sum_hasL_eq_three`: clause **(B4)** of `Box`, saturation, the model side of
  `attach_multiplicity_eq_three`.  An all-zero mask cannot sum to three.

Together they say the mask carries the right bits and the right number of them. -/

/-- A root neighbour's shell neighbours all carry positive attachment, so filtering the
    shell and filtering the positive shell agree. -/
lemma filter_adj_shellPos_eq_shellSet {v c : Fin G.size} (hvc : G.graph.Adj v c) :
    (shellPos G v).filter (fun x => G.graph.Adj x c)
      = (shellSet G v).filter (fun x => G.graph.Adj x c) := by
  ext x
  simp only [Finset.mem_filter, mem_shellPos]
  constructor
  · rintro ⟨⟨hx, -⟩, hxc⟩; exact ⟨hx, hxc⟩
  · rintro ⟨hx, hxc⟩
    refine ⟨⟨hx, Finset.card_pos.mpr ⟨c, ?_⟩⟩, hxc⟩
    rw [attachSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hvc, hxc⟩

/-- The index transport, at the root neighbourhood. -/
lemma sum_range_rootAt (v : Fin G.size) (f : Fin G.size → ℕ) :
    ∑ a ∈ Finset.range (rootNbrs G v).card, f (rootAt G v a) = ∑ b ∈ rootNbrs G v, f b := by
  rw [← rootArr_length (G := G) v]
  exact enum_sum_range (mem_rootArr v) (rootArr_nodup v) f

/-- **The mask popcount is the attachment count** (plan obligation 8, `wt_maskNat`). -/
theorem kwt_KOf (hReg : IsRegular G) (hdeg : maxDegree G = 4) {v : Fin G.size} {i : ℕ}
    (hi : i < nOf G v) :
    Delta4Model.kwt (KOf G v) i = (attachSet G v (shellAt G v i)).card := by
  have hcard : (rootNbrs G v).card = 4 := card_rootNbrs hReg hdeg v
  have hfilter : (rootNbrs G v).filter (fun b => G.graph.Adj (shellAt G v i) b)
      = attachSet G v (shellAt G v i) := by
    ext b
    simp only [Finset.mem_filter, mem_rootNbrs, attachSet, Finset.mem_univ, true_and]
  calc Delta4Model.kwt (KOf G v) i
      = ∑ a ∈ Finset.range (rootNbrs G v).card,
          (fun b => if G.graph.Adj (shellAt G v i) b then 1 else 0) (rootAt G v a) := by
        rw [hcard, Delta4Model.kwt, hasL_KOf hi (by norm_num), hasL_KOf hi (by norm_num),
          hasL_KOf hi (by norm_num), hasL_KOf hi (by norm_num)]
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
    _ = ∑ b ∈ rootNbrs G v, (if G.graph.Adj (shellAt G v i) b then 1 else 0) :=
        sum_range_rootAt v (fun b => if G.graph.Adj (shellAt G v i) b then 1 else 0)
    _ = ((rootNbrs G v).filter fun b => G.graph.Adj (shellAt G v i) b).card :=
        (Finset.card_filter _ _).symm
    _ = (attachSet G v (shellAt G v i)).card := by rw [hfilter]

/-- **Clause (B4) of `Box`: saturation.**  Every root letter is carried by exactly three
    shell slots.  This is `attach_multiplicity_eq_three` read through the encoding, and it is
    the guard that the masks are not vacuously zero. -/
theorem sum_hasL_eq_three (hTF : IsTriangleFree G) (hReg : IsRegular G)
    (hdeg : maxDegree G = 4) {v : Fin G.size} {a : ℕ} (ha : a < 4) :
    Delta4Model.sumUpto (fun i => Delta4Model.hasL (KOf G v) i a) (nOf G v) 0 = 3 := by
  have hcard : (rootNbrs G v).card = 4 := card_rootNbrs hReg hdeg v
  have haN : rootAt G v a ∈ rootNbrs G v := rootAt_mem (by omega)
  have hvc : G.graph.Adj v (rootAt G v a) := mem_rootNbrs.mp haN
  calc Delta4Model.sumUpto (fun i => Delta4Model.hasL (KOf G v) i a) (nOf G v) 0
      = ∑ i ∈ Finset.range (nOf G v), Delta4Model.hasL (KOf G v) i a :=
        Delta4Model.sumUpto_eq_sum_range _ _
    _ = ∑ i ∈ Finset.range (nOf G v),
          (fun x => if G.graph.Adj x (rootAt G v a) then 1 else 0) (shellAt G v i) :=
        Finset.sum_congr rfl fun i hi => hasL_KOf (Finset.mem_range.mp hi) ha
    _ = ∑ x ∈ shellPos G v, (if G.graph.Adj x (rootAt G v a) then 1 else 0) :=
        sum_range_shellAt v (fun x => if G.graph.Adj x (rootAt G v a) then 1 else 0)
    _ = ((shellPos G v).filter fun x => G.graph.Adj x (rootAt G v a)).card :=
        (Finset.card_filter _ _).symm
    _ = ((shellSet G v).filter fun x => G.graph.Adj x (rootAt G v a)).card := by
        rw [filter_adj_shellPos_eq_shellSet hvc]
    _ = ((shellSet G v).filter fun x => rootAt G v a ∈ attachSet G v x).card := by
        rw [filter_mem_attachSet_eq hvc]
    _ = 3 := attach_multiplicity_eq_three hTF hReg hdeg hvc

/-- **The model's shell degree is `d_{F⁺}`** — the guard on `A`, independent of obligation 4:
    it ties `AOf` to `shellPosDeg`, a notion that predates the model.  Together with `kwt_KOf`
    this is clause **(B2)** of `Box` modulo `shellPosDeg_add_attach_le4`. -/
theorem deg_AOf (hTF : IsTriangleFree G) (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    {v : Fin G.size} {i : ℕ} (hi : i < nOf G v) :
    Delta4Model.deg (nOf G v) (AOf G v) i = shellPosDeg G v (shellAt G v i) := by
  have hn : nOf G v ≤ 12 := card_shellPos_le_twelve hTF hReg hdeg v
  calc Delta4Model.deg (nOf G v) (AOf G v) i
      = ∑ j ∈ Finset.range (nOf G v), Delta4Model.edg (AOf G v) i j :=
        Delta4Model.sumUpto_eq_sum_range _ _
    _ = ∑ j ∈ Finset.range (nOf G v),
          (fun y => if G.graph.Adj (shellAt G v i) y then 1 else 0) (shellAt G v j) :=
        Finset.sum_congr rfl fun j hj => edg_AOf hn hi (Finset.mem_range.mp hj)
    _ = ∑ y ∈ shellPos G v, (if G.graph.Adj (shellAt G v i) y then 1 else 0) :=
        sum_range_shellAt v (fun y => if G.graph.Adj (shellAt G v i) y then 1 else 0)
    _ = shellPosDeg G v (shellAt G v i) := (Finset.card_filter _ _).symm

/-- `shellW` vanishes on the shell slots the decomposition excludes: a shell vertex adjacent
    to `a` is not in `K_a`, and the model's leading factor `1 − hasL K y a` kills it.  This is
    what lets obligation 12 sum `shellW` over *all* `n` slots while the graph sums over the
    filtered shell block only. -/
theorem shellW_eq_zero_of_adj (hReg : IsRegular G) (hdeg : maxDegree G = 4)
    {a v y : Fin G.size} (hav : G.graph.Adj v a) (hy : y ∈ shellPos G v)
    (hay : G.graph.Adj a y) :
    Delta4Model.shellW (nOf G v) (KOf G v) (AOf G v) (idx G v a) (pos G v y) = 0 := by
  have haN : a ∈ rootNbrs G v := mem_rootNbrs.mpr hav
  have hfac : Delta4Model.hasL (KOf G v) (pos G v y) (idx G v a) = 1 := by
    rw [hasL_KOf (pos_lt hy) (idx_lt_four hReg hdeg haN), rootAt_idx haN, shellAt_pos hy,
      if_pos hay.symm]
  simp [Delta4Model.shellW, hfac]

/-- **Obligation 4, root half, with the hypotheses it actually needs.**  Regularity and
    `maxDegree = 4` enter only through `idx a, idx b < 4`, so `maxDegree G ≤ 4` suffices. -/
theorem avoidAttach_card_root_of_maxDegree (hTF : IsTriangleFree G) (hΔ : maxDegree G ≤ 4)
    {a v b : Fin G.size} (hav : G.graph.Adj v a) (hb : b ∈ (rootNbrs G v).erase a) :
    (avoidAttach G a v b).card
      = Delta4Model.rootW (nOf G v) (KOf G v) (idx G v a) (idx G v b) := by
  have hbN : b ∈ rootNbrs G v := Finset.mem_of_mem_erase hb
  have haN : a ∈ rootNbrs G v := mem_rootNbrs.mpr hav
  have hia : idx G v a < 4 := idx_lt_four_of_maxDegree hΔ haN
  have hib : idx G v b < 4 := idx_lt_four_of_maxDegree hΔ hbN
  simp only [Delta4Model.rootW, Delta4Model.sumUpto_eq_sum_range]
  rw [card_avoidAttach_eq hTF hav,
    ← sum_range_shellAt v (fun x => if G.graph.Adj x a ∧ G.graph.Adj x b then 1 else 0)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < nOf G v := Finset.mem_range.mp hi
  rw [hasL_KOf hi' hia, hasL_KOf hi' hib, rootAt_idx haN, rootAt_idx hbN, ite_and_mul]

end PentagonLocal
end Davey2024
