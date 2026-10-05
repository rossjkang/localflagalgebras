import DaveyThesis2024.Delta4.Search

/-!
# Δ = 4 finite model: chunk algebra (plan obligation 20) and an end-to-end pilot (obligation 21)

Everything here is new; nothing in `Model.lean` / `Search.lean` is redefined
(plan §6(e): never define a second copy of a model quantity).

## What obligation 20 has to buy

`searchNP leafOK n K = true` is one kernel evaluation of a tree with up to ~5·10⁵ nodes
per mask multiset, ~3·10⁶ in total.  That does not fit in one `decide +kernel`
declaration (plan §5 D10: a 20,000-node ceiling).  So the tree must be cut into
chunks, each chunk its own declaration, and the *cutting itself* must be free of
any trusted step — a chunk generator that silently drops a subtree would otherwise
produce a set of `true`s that prove nothing (plan §6(e), the failure mode B
demonstrated on itself).

This file cuts in two moves.

* **Horizontal cut (§B).**  `expand n K d s` runs the traversal to depth `d` and
  returns the *frontier*: the list of states still to be explored.  `goNP` at `s`
  is proved equal to the conjunction over the frontier
  (`goNP_eq_goAll_expand`).  Nothing about `expand` is trusted: it is a `def` the
  kernel evaluates, and the equality is a theorem.

* **Vertical cut (§C).**  The frontier list is sliced with `List.drop`/`List.take`
  at *numeric offsets*.  `goAll_peel` is the one lemma, and the residual list is
  forced to be `[]` at the end.  **There is no chunk literal anywhere**, so the
  plan's layer-5 defence ("`expand d root = c₁ ++ … ++ c_k`, machine-checked")
  is not merely checked, it is *unnecessary*: `List.take_append_drop` is the
  cover, and a dropped chunk shows up as a non-empty residual that fails to
  typecheck.  See §C for why this is strictly stronger than the plan's shape.

## The counting instance (§A) — the anti-vacuity accumulator

`goNP` is `Bool`-valued and `&&` short-circuits, so a `true` carries no evidence
about how much was traversed.  `goCnt` is the same traversal returning
`(nodes, violations)`; it never short-circuits.  Plan §6(e) layer 2 asks for one
traversal with two accumulators so the counted and checked versions "cannot
diverge"; here they are two `def`s tied by a *theorem*
(`goNP_eq_true_iff_goCnt`), which is a proof-level guarantee rather than a
syntactic one.  The kernel assertions are then `goAllCnt … = (N, 0)` — node count
and zero violations in one equation, as plan §6(e) layer 3 requires.
-/

namespace Delta4Model

/-- A search state: the pairs still to be decided, and the adjacency committed so far.
    This is exactly the pair of arguments `goNP` recurses on. -/
abbrev St : Type := List (Nat × Nat) × Nat

@[inline] def addP (x y : Nat × Nat) : Nat × Nat := (x.1 + y.1, x.2 + y.2)

@[simp] theorem addP_fst (x y : Nat × Nat) : (addP x y).1 = x.1 + y.1 := rfl
@[simp] theorem addP_snd (x y : Nat × Nat) : (addP x y).2 = x.2 + y.2 := rfl

/-! ## A.  The counting instance of the traversal -/

/-- `goCnt` walks exactly the tree `goNP` walks and returns `(nodes, violations)`:
    one node per call, one violation per leaf at which `leafP` is `false`.
    Unlike `goNP` it does **not** short-circuit, so `.1` is the exact node count. -/
def goCnt (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    List (Nat × Nat) → Nat → Nat × Nat
  | [],      A => (1, if leafP n K A then 0 else 1)
  | p :: ps, A =>
      addP (1, 0)
        (addP (goCnt leafP n K ps A)
          (if takeGuard n K A p.1 p.2 then goCnt leafP n K ps (addEdge A p.1 p.2) else (0, 0)))

/-- **The two accumulators agree.**  A zero violation count is exactly a `true`
    from the `Bool` traversal.  This is what makes `goCnt` a legitimate stand-in
    for `goNP` in a kernel assertion. -/
theorem goNP_eq_true_iff_goCnt (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    ∀ (ps : List (Nat × Nat)) (A : Nat),
      goNP leafP n K ps A = true ↔ (goCnt leafP n K ps A).2 = 0 := by
  intro ps
  induction ps with
  | nil =>
      intro A
      rw [goNP, goCnt]
      cases h : leafP n K A <;> simp
  | cons p ps ih =>
      intro A
      rw [goNP, goCnt, Bool.and_eq_true, addP_snd, addP_snd]
      by_cases hg : takeGuard n K A p.1 p.2 = true
      · rw [if_pos hg, if_pos hg]
        rw [ih A, ih (addEdge A p.1 p.2)]
        simp only []
        omega
      · rw [if_neg hg, if_neg hg]
        rw [ih A]
        simp

/-! ## B.  The horizontal cut: the depth-`d` frontier -/

/-- `expand n K d s` runs the traversal from `s` for `d` levels and returns the
    frontier of states still to be explored.  `d = 0`, or an exhausted pair list,
    stops.  The guard is evaluated exactly where `goNP` evaluates it, so a pruned
    branch contributes no frontier state at all. -/
def expand (n K : Nat) : Nat → St → List St
  | 0,     s => [s]
  | d + 1, s =>
      match s with
      | ([], A)      => [([], A)]
      | (p :: ps, A) =>
          expand n K d (ps, A)
            ++ (if takeGuard n K A p.1 p.2 then expand n K d (ps, addEdge A p.1 p.2) else [])

/-- The `Bool` traversal over a list of states. -/
def goAll (leafP : Nat → Nat → Nat → Bool) (n K : Nat) : List St → Bool
  | []      => true
  | s :: ss => goNP leafP n K s.1 s.2 && goAll leafP n K ss

/-- The counting traversal over a list of states. -/
def goAllCnt (leafP : Nat → Nat → Nat → Bool) (n K : Nat) : List St → Nat × Nat
  | []      => (0, 0)
  | s :: ss => addP (goCnt leafP n K s.1 s.2) (goAllCnt leafP n K ss)

theorem goAll_append (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    ∀ xs ys : List St,
      goAll leafP n K (xs ++ ys) = (goAll leafP n K xs && goAll leafP n K ys) := by
  intro xs
  induction xs with
  | nil => intro ys; simp [goAll]
  | cons s ss ih => intro ys; simp [goAll, ih, Bool.and_assoc]

theorem goAllCnt_append (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    ∀ xs ys : List St,
      goAllCnt leafP n K (xs ++ ys)
        = addP (goAllCnt leafP n K xs) (goAllCnt leafP n K ys) := by
  intro xs
  induction xs with
  | nil => intro ys; simp [goAllCnt, addP]
  | cons s ss ih =>
      intro ys
      simp only [List.cons_append, goAllCnt, ih, addP, Prod.mk.injEq]
      omega

/-- The list-level form of §A: zero violations over a list of states is exactly
    `true` over that list. -/
theorem goAll_eq_true_iff_goAllCnt (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    ∀ L : List St, goAll leafP n K L = true ↔ (goAllCnt leafP n K L).2 = 0 := by
  intro L
  induction L with
  | nil => simp [goAll, goAllCnt]
  | cons s ss ih =>
      rw [goAll, goAllCnt, Bool.and_eq_true, addP_snd, ih,
        goNP_eq_true_iff_goCnt leafP n K s.1 s.2]
      omega

/-- **The chunk-declaration consumer.**  A `decide +kernel` fact of the shape
    `goAllCnt leafOK n K c = (N, 0)` — node count *and* zero violations in one
    equation — yields the `Bool` fact.  A generator that dropped work would have
    to have guessed `N` wrong as well to stay consistent with the reference
    enumerator, which is the point of carrying `N`. -/
theorem goAll_of_goAllCnt {leafP : Nat → Nat → Nat → Bool} {n K : Nat} {L : List St}
    {N : Nat} (h : goAllCnt leafP n K L = (N, 0)) : goAll leafP n K L = true :=
  (goAll_eq_true_iff_goAllCnt leafP n K L).2 (by rw [h])

/-- **The horizontal cut is sound.**  Running the traversal `d` levels and then
    conjoining over the frontier is the traversal. -/
theorem goNP_eq_goAll_expand (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    ∀ (d : Nat) (s : St), goNP leafP n K s.1 s.2 = goAll leafP n K (expand n K d s) := by
  intro d
  induction d with
  | zero => intro s; simp [expand, goAll]
  | succ d ih =>
      rintro ⟨ps, A⟩
      cases ps with
      | nil => simp [expand, goAll]
      | cons p ps =>
          rw [expand, goAll_append, goNP]
          by_cases hg : takeGuard n K A p.1 p.2 = true
          · rw [if_pos hg, if_pos hg, ← ih (ps, A), ← ih (ps, addEdge A p.1 p.2)]
          · rw [if_neg hg, if_neg hg, ← ih (ps, A)]
            simp [goAll]

/-! ### The node-count accounting, as a theorem

  The frontier decomposition also splits the *node count*: the nodes of the whole
  tree are the internal nodes above the frontier plus the nodes of the chunks.
  `expandNodes` counts the internal ones (it is `expand` with the list replaced by
  a counter), and `goCnt_fst_eq` is the accounting identity.

  This is what turns plan §6(e) layer 3 from a convention into a check with teeth.
  The chunk declarations pin `Σᵢ Nᵢ`; `expandNodes … = I` is a second, independent
  kernel fact; and `I + Σᵢ Nᵢ` must then equal the node count of the *monolithic*
  traversal.  A generator that loses a subtree between the frontier and the chunk
  table therefore contradicts an arithmetic identity, not just a reference table. -/

/-- Internal nodes strictly above the depth-`d` frontier. -/
def expandNodes (n K : Nat) : Nat → St → Nat
  | 0,     _ => 0
  | d + 1, s =>
      match s with
      | ([], _)      => 0
      | (p :: ps, A) =>
          expandNodes n K d (ps, A) + 1
            + (if takeGuard n K A p.1 p.2 then expandNodes n K d (ps, addEdge A p.1 p.2) else 0)

/-- **Node accounting.**  `nodes(tree) = internal + Σ nodes(chunks)`. -/
theorem goCnt_fst_eq (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    ∀ (d : Nat) (s : St),
      (goCnt leafP n K s.1 s.2).1
        = expandNodes n K d s + (goAllCnt leafP n K (expand n K d s)).1 := by
  intro d
  induction d with
  | zero => intro s; simp [expand, expandNodes, goAllCnt, addP]
  | succ d ih =>
      rintro ⟨ps, A⟩
      cases ps with
      | nil => simp [expand, expandNodes, goAllCnt, addP]
      | cons p ps =>
          rw [expand, expandNodes, goCnt, goAllCnt_append]
          by_cases hg : takeGuard n K A p.1 p.2 = true
          · rw [if_pos hg, if_pos hg, if_pos hg]
            have h1 := ih (ps, A)
            have h2 := ih (ps, addEdge A p.1 p.2)
            simp only [addP_fst] at *
            omega
          · rw [if_neg hg, if_neg hg, if_neg hg]
            have h1 := ih (ps, A)
            simp only [addP_fst, goAllCnt] at *
            omega

/-- The violation count splits with no internal contribution. -/
theorem goCnt_snd_eq (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    ∀ (d : Nat) (s : St),
      (goCnt leafP n K s.1 s.2).2 = (goAllCnt leafP n K (expand n K d s)).2 := by
  intro d
  induction d with
  | zero => intro s; simp [expand, goAllCnt, addP]
  | succ d ih =>
      rintro ⟨ps, A⟩
      cases ps with
      | nil => simp [expand, goAllCnt, addP]
      | cons p ps =>
          rw [expand, goCnt, goAllCnt_append]
          by_cases hg : takeGuard n K A p.1 p.2 = true
          · rw [if_pos hg, if_pos hg]
            have h1 := ih (ps, A)
            have h2 := ih (ps, addEdge A p.1 p.2)
            simp only [addP_snd] at *
            omega
          · rw [if_neg hg, if_neg hg]
            have h1 := ih (ps, A)
            simp only [addP_snd, goAllCnt] at *
            omega

/-! ## C.  The vertical cut: slicing the frontier by offsets

  The plan (obligation 20, §6(e) layer 5) proposes literal chunk lists `c₁ … c_k`
  plus one machine-checked equation `expand d root = c₁ ++ … ++ c_k`.  That works,
  and `goAll_append` above is exactly what consumes it.  But the literals are
  large (a chunk is a list of states, each carrying a pair list), they must be
  transcribed correctly by the generator, and the frontier equation is then a
  ~10⁴-token `decide` in its own right.

  Slicing by `List.drop`/`List.take` at numeric offsets removes all of that.
  `List.take_append_drop` *is* the cover, so:

  * the generator emits three numerals per chunk — the offset, the width and the
    node count — and nothing that can be mistranscribed into a *different list*;
  * there is no frontier equation to check;
  * a chunk that is dropped, duplicated or mis-ordered cannot be hidden — the
    peeling chain below only closes when the final residual `L.drop a` is `[]`,
    and the offsets are forced to chain as `a ↦ a + b`.
-/

/-- **Peel one chunk.**  `hc` is the chunk declaration; `hr` is the rest of the
    chain.  The offsets chain as `a ↦ a + b`, which is what forbids a gap. -/
theorem goAll_peel {leafP : Nat → Nat → Nat → Bool} {n K : Nat} {L : List St}
    {a b c : Nat} (h : a + b = c)
    (hc : goAll leafP n K ((L.drop a).take b) = true)
    (hr : goAll leafP n K (L.drop c) = true) :
    goAll leafP n K (L.drop a) = true := by
  have hsplit : (L.drop a).take b ++ L.drop c = L.drop a := by
    have h1 : (L.drop a).drop b = L.drop c := by rw [List.drop_drop, h]
    rw [← h1]; exact List.take_append_drop b (L.drop a)
  rw [← hsplit, goAll_append, hc, hr]
  rfl

/-- The counting analogue of `goAll_peel`: it chains the chunk *counts* without
    a second traversal, so `Σᵢ Nᵢ` is available to Lean, not just to the
    generator. -/
theorem goAllCnt_peel (leafP : Nat → Nat → Nat → Bool) (n K : Nat) (L : List St)
    (a b c : Nat) (h : a + b = c) :
    goAllCnt leafP n K (L.drop a)
      = addP (goAllCnt leafP n K ((L.drop a).take b)) (goAllCnt leafP n K (L.drop c)) := by
  have hsplit : (L.drop a).take b ++ L.drop c = L.drop a := by
    have h1 : (L.drop a).drop b = L.drop c := by rw [List.drop_drop, h]
    rw [← h1]; exact List.take_append_drop b (L.drop a)
  have e : goAllCnt leafP n K (L.drop a)
      = goAllCnt leafP n K ((L.drop a).take b ++ L.drop c) := by rw [hsplit]
  rw [e, goAllCnt_append]

/-- **The end of the chain.**  Nothing is left. -/
theorem goAll_nil {leafP : Nat → Nat → Nat → Bool} {n K : Nat} {L : List St} {a : Nat}
    (h : L.drop a = []) : goAll leafP n K (L.drop a) = true := by
  rw [h]; rfl

/-- **The entry point.**  Chain `goAll_peel` down to `goAll_nil` on the frontier
    `expand n K d (pairList n, 0)` and this converts the result into
    `searchNP leafP n K = true`, the hypothesis of `searchNP_leafOK_complete`. -/
theorem searchNP_of_frontier (leafP : Nat → Nat → Nat → Bool) (n K d : Nat)
    (h : goAll leafP n K ((expand n K d (pairList n, 0)).drop 0) = true) :
    searchNP leafP n K = true := by
  rw [List.drop_zero] at h
  rw [searchNP, goNP_eq_goAll_expand leafP n K d (pairList n, 0)]
  exact h

/-- The same, for the degree-cached traversal `searchNPD` (`Search.lean` §H).
    The two searches are equal (`searchNPD_eq_searchNP`), so the chunk table can
    be evaluated at whichever is cheaper — measured 27% faster and 24% smaller
    for `goNPD`; see the measurement note at the end of this file. -/
theorem searchNPD_of_frontier (leafP : Nat → Nat → Nat → Bool) (n K d : Nat) (hn : n ≤ 12)
    (h : goAll leafP n K ((expand n K d (pairList n, 0)).drop 0) = true) :
    searchNPD leafP n K = true := by
  rw [searchNPD_eq_searchNP leafP n K hn]
  exact searchNP_of_frontier leafP n K d h

/-- **The whole pipeline, in one statement.**  Feed it a chained `goAll` fact and
    it discharges the model-side universal: every `Box`-satisfying `(n, K, A)`
    passes the leaf test.  This is the shape the generated declarations of
    obligation 21 have to land in (~590 of them at the ceiling §D argues for). -/
theorem leafOK_of_frontier {n K d : Nat}
    (h : goAll leafOK n K ((expand n K d (pairList n, 0)).drop 0) = true) :
    ∀ A : Nat, Box n K A = true → leafOK n K A = true :=
  fun A hbox => searchNP_leafOK_complete n K A hbox (searchNP_of_frontier leafOK n K d h)

-- BEGIN GENERATED (p3_gen.py)
/-! ### Generated by p3_gen.py — do not edit by hand. -/

-- pilot: n = 7, masks = [3, 3, 3, 4, 8, 12, 12], K = 214450995
-- total nodes 11577, leaves 2027, violations 0
-- frontier depth 10: 28 states, 11532 subtree nodes,
--   45 internal nodes, 45 + 11532 = 11577
-- Box-satisfying A: 2027, of which missing from the leaf set: 0
-- high leaf witness: A = 14172866872256797933664, twoT = 42, credit = 102,
--   charge = 22, margin = 40

def nPil : Nat := 7
def KPil : Nat := 214450995
def dPil : Nat := 10
/-- The depth-`dPil` frontier.  `irreducible` so that a mis-chained peel is a
    crisp type mismatch instead of a `whnf` timeout in the unifier; the kernel
    ignores the attribute, so `decide +kernel` still evaluates it. -/
@[irreducible] def FPil : List St := expand nPil KPil dPil (pairList nPil, 0)

theorem FPil_def : FPil = expand nPil KPil dPil (pairList nPil, 0) := by
  unfold FPil
  rfl

/-- The monolithic check: one declaration for the whole multiset. -/
theorem pilot_mono : goCnt leafOK nPil KPil (pairList nPil) 0 = (11577, 0) := by
  decide +kernel

/-- chunk 0: frontier states [0, 1), 861 nodes, 162 leaves. -/
theorem pilot_chunk_0 :
    goAllCnt leafOK nPil KPil ((FPil.drop 0).take 1) = (861, 0) := by
  decide +kernel

/-- chunk 1: frontier states [1, 2), 733 nodes, 134 leaves. -/
theorem pilot_chunk_1 :
    goAllCnt leafOK nPil KPil ((FPil.drop 1).take 1) = (733, 0) := by
  decide +kernel

/-- chunk 2: frontier states [2, 4), 1058 nodes, 195 leaves. -/
theorem pilot_chunk_2 :
    goAllCnt leafOK nPil KPil ((FPil.drop 2).take 2) = (1058, 0) := by
  decide +kernel

/-- chunk 3: frontier states [4, 6), 1046 nodes, 180 leaves. -/
theorem pilot_chunk_3 :
    goAllCnt leafOK nPil KPil ((FPil.drop 4).take 2) = (1046, 0) := by
  decide +kernel

/-- chunk 4: frontier states [6, 8), 776 nodes, 134 leaves. -/
theorem pilot_chunk_4 :
    goAllCnt leafOK nPil KPil ((FPil.drop 6).take 2) = (776, 0) := by
  decide +kernel

/-- chunk 5: frontier states [8, 10), 1012 nodes, 180 leaves. -/
theorem pilot_chunk_5 :
    goAllCnt leafOK nPil KPil ((FPil.drop 8).take 2) = (1012, 0) := by
  decide +kernel

/-- chunk 6: frontier states [10, 14), 1431 nodes, 244 leaves. -/
theorem pilot_chunk_6 :
    goAllCnt leafOK nPil KPil ((FPil.drop 10).take 4) = (1431, 0) := by
  decide +kernel

/-- chunk 7: frontier states [14, 17), 1263 nodes, 222 leaves. -/
theorem pilot_chunk_7 :
    goAllCnt leafOK nPil KPil ((FPil.drop 14).take 3) = (1263, 0) := by
  decide +kernel

/-- chunk 8: frontier states [17, 20), 1014 nodes, 180 leaves. -/
theorem pilot_chunk_8 :
    goAllCnt leafOK nPil KPil ((FPil.drop 17).take 3) = (1014, 0) := by
  decide +kernel

/-- chunk 9: frontier states [20, 24), 1187 nodes, 198 leaves. -/
theorem pilot_chunk_9 :
    goAllCnt leafOK nPil KPil ((FPil.drop 20).take 4) = (1187, 0) := by
  decide +kernel

/-- chunk 10: frontier states [24, 28), 1151 nodes, 198 leaves. -/
theorem pilot_chunk_10 :
    goAllCnt leafOK nPil KPil ((FPil.drop 24).take 4) = (1151, 0) := by
  decide +kernel

theorem pilot_residual : FPil.drop 28 = [] := by decide +kernel

/-- The internal nodes above the frontier: a second, independent kernel fact. -/
theorem pilot_internal : expandNodes nPil KPil dPil (pairList nPil, 0) = 45 := by
  decide +kernel

/-- **The chunk counts, chained.**  No traversal is re-run: `goAllCnt_peel`
    assembles the eleven chunk declarations into the frontier total. -/
theorem pilot_frontier_count :
    goAllCnt leafOK nPil KPil (FPil.drop 0) = (11532, 0) := by
  rw [goAllCnt_peel leafOK nPil KPil FPil 0 1 1 rfl, pilot_chunk_0,
      goAllCnt_peel leafOK nPil KPil FPil 1 1 2 rfl, pilot_chunk_1,
      goAllCnt_peel leafOK nPil KPil FPil 2 2 4 rfl, pilot_chunk_2,
      goAllCnt_peel leafOK nPil KPil FPil 4 2 6 rfl, pilot_chunk_3,
      goAllCnt_peel leafOK nPil KPil FPil 6 2 8 rfl, pilot_chunk_4,
      goAllCnt_peel leafOK nPil KPil FPil 8 2 10 rfl, pilot_chunk_5,
      goAllCnt_peel leafOK nPil KPil FPil 10 4 14 rfl, pilot_chunk_6,
      goAllCnt_peel leafOK nPil KPil FPil 14 3 17 rfl, pilot_chunk_7,
      goAllCnt_peel leafOK nPil KPil FPil 17 3 20 rfl, pilot_chunk_8,
      goAllCnt_peel leafOK nPil KPil FPil 20 4 24 rfl, pilot_chunk_9,
      goAllCnt_peel leafOK nPil KPil FPil 24 4 28 rfl, pilot_chunk_10,
      pilot_residual]
  rfl

/-- **The monolithic node count, derived.**  `goCnt_fst_eq` + `pilot_internal`
    + the chained chunk counts.  The kernel computed the same number a second
    time and independently in `pilot_mono`: 45 + 11532 = 11577. -/
theorem pilot_mono_derived :
    goCnt leafOK nPil KPil (pairList nPil) 0 = (11577, 0) := by
  have hfc : goAllCnt leafOK nPil KPil (expand nPil KPil dPil (pairList nPil, 0))
      = (11532, 0) := by
    have h := pilot_frontier_count
    rw [List.drop_zero, FPil_def] at h
    exact h
  have h1 := goCnt_fst_eq leafOK nPil KPil dPil (pairList nPil, 0)
  have h2 := goCnt_snd_eq leafOK nPil KPil dPil (pairList nPil, 0)
  simp only [hfc, pilot_internal] at h1 h2
  exact Prod.ext h1 h2

/-- **The peeling chain**: chunk declarations in, one `goAll` fact out.  Written
    backwards, from the residual up, so that every step carries an explicit
    type: a missing or misplaced chunk is then a type error at that `have`,
    not a `whnf` timeout in the unifier. -/
theorem pilot_frontier_ok : goAll leafOK nPil KPil (FPil.drop 0) = true := by
  have h11 : goAll leafOK nPil KPil (FPil.drop 28) = true :=
    goAll_nil pilot_residual
  have h10 : goAll leafOK nPil KPil (FPil.drop 24) = true :=
    goAll_peel (b := 4) (c := 28) rfl (goAll_of_goAllCnt pilot_chunk_10) h11
  have h9 : goAll leafOK nPil KPil (FPil.drop 20) = true :=
    goAll_peel (b := 4) (c := 24) rfl (goAll_of_goAllCnt pilot_chunk_9) h10
  have h8 : goAll leafOK nPil KPil (FPil.drop 17) = true :=
    goAll_peel (b := 3) (c := 20) rfl (goAll_of_goAllCnt pilot_chunk_8) h9
  have h7 : goAll leafOK nPil KPil (FPil.drop 14) = true :=
    goAll_peel (b := 3) (c := 17) rfl (goAll_of_goAllCnt pilot_chunk_7) h8
  have h6 : goAll leafOK nPil KPil (FPil.drop 10) = true :=
    goAll_peel (b := 4) (c := 14) rfl (goAll_of_goAllCnt pilot_chunk_6) h7
  have h5 : goAll leafOK nPil KPil (FPil.drop 8) = true :=
    goAll_peel (b := 2) (c := 10) rfl (goAll_of_goAllCnt pilot_chunk_5) h6
  have h4 : goAll leafOK nPil KPil (FPil.drop 6) = true :=
    goAll_peel (b := 2) (c := 8) rfl (goAll_of_goAllCnt pilot_chunk_4) h5
  have h3 : goAll leafOK nPil KPil (FPil.drop 4) = true :=
    goAll_peel (b := 2) (c := 6) rfl (goAll_of_goAllCnt pilot_chunk_3) h4
  have h2 : goAll leafOK nPil KPil (FPil.drop 2) = true :=
    goAll_peel (b := 2) (c := 4) rfl (goAll_of_goAllCnt pilot_chunk_2) h3
  have h1 : goAll leafOK nPil KPil (FPil.drop 1) = true :=
    goAll_peel (b := 1) (c := 2) rfl (goAll_of_goAllCnt pilot_chunk_1) h2
  have h0 : goAll leafOK nPil KPil (FPil.drop 0) = true :=
    goAll_peel (b := 1) (c := 1) rfl (goAll_of_goAllCnt pilot_chunk_0) h1
  exact h0

theorem pilot_search : searchNP leafOK nPil KPil = true := by
  have h := pilot_frontier_ok
  rw [FPil_def] at h
  exact searchNP_of_frontier leafOK nPil KPil dPil h

/-- **The pilot, end to end**: from the chunk declarations to a universally
    quantified model statement. -/
theorem pilot_all_boxes (A : Nat) (hbox : Box nPil KPil A = true) :
    leafOK nPil KPil A = true := by
  have h := pilot_frontier_ok
  rw [FPil_def] at h
  exact leafOK_of_frontier h A hbox

/-! ### Non-vacuity regressions (plan §6(e) layer 6) -/

def AHigh : Nat := 14172866872256797933664

theorem high_in_box : Box nPil KPil AHigh = true := by decide +kernel
theorem high_twoT : twoT nPil KPil AHigh = 42 := by decide +kernel
theorem high_credit : credit nPil KPil AHigh = 102 := by decide +kernel
theorem high_charge : charge nPil KPil AHigh = 22 := by decide +kernel
/-- The leaf test is *not* vacuous here: `twoT ≥ 38`, so the second disjunct
    of `leafOK` is what fires, with margin exactly 40. -/
theorem high_margin :
    charge nPil KPil AHigh + 6 * twoT nPil KPil AHigh + 40
      = credit nPil KPil AHigh + 212 := by decide +kernel
theorem high_not_low : ¬ (twoT nPil KPil AHigh < 38) := by decide +kernel

-- END GENERATED

/-! ## D.  Measurements — 2026-09-18, 10-core / 16 GB, Lean 4.28.0

  Every figure is `/usr/bin/time -l lake env lean <file>` on a file holding the
  import, these definitions, and **one** `decide +kernel` declaration, with a
  harness that samples concurrent `lean` processes and reports zero for all of
  them (an earlier reading of
  55 s for a 12 s job was pure contention).  Baseline — import plus definitions,
  no `decide` — is **0.6–1.1 s, 0.63 GB**.  Repeat runs vary by ±10% in time;
  peak RSS is reproducible to three digits.

  ### The pilot in this file

  `n = 7`, masks `[3,3,3,4,8,12,12]`, `K = 214450995`: **11,577 nodes, 2,027
  leaves, 117 of them high** (`twoT ≥ 38`), 0 violations.  The node count agrees
  across four independent implementations — a literal Python transcription of
  `Model.lean`/`Search.lean`, a bitwise Python re-derivation, a C re-derivation,
  and the Lean kernel — and the 117 high leaves are confirmed kernel-side by
  running the same traversal with the leaf test `twoT < 38` and checking the
  violation count is exactly 117.  The 2,027 leaves are exactly the 2,027 `A`
  with `Box 7 K A = true`, brute-forced over all subsets of the mask-disjoint
  pairs: the traversal neither over- nor under-counts the model's fibre.

  | what | wall | peak RSS |
  |---|---|---|
  | `pilot_mono`, one declaration, 11,577 nodes | 15.4 s (6 runs) | 5.11 GB |
  | this whole file: 20 kernel evaluations + the assembly | 26.2 s | 5.79 GB |
  | `searchNP  leafOK 7 K = true` (`Bool`, short-circuits) | 14.9 s | 5.01 GB |
  | `searchNPD leafOK 7 K = true` (`Bool` + degree cache)  | 11.0 s | 3.82 GB |

  * **The counting accumulator is free.**  `goCnt` costs what the
    short-circuiting `goNP` costs (15.4 s vs 14.9 s, inside the run-to-run
    spread).  Plan §6(e) layer 3 — carry the node count, not a `Bool` — is
    therefore not a trade-off.  Take it.
  * **Memory does not accumulate across declarations.**  Twenty kernel
    evaluations in one file peak at 5.79 GB, barely above the 5.11 GB of the
    largest single one.  Independently confirms the premise of §5 D10.
  * **`goNPD` is worth 27% of the time and 24% of the memory.**  The chunk table
    should evaluate the *cached* traversal.  This file's algebra is stated at the
    `goNP` level, so realising that needs a `goNPD`-level `expand`/`goAll`:
    `dg (degPack n A) t = deg n A t` (a base-16 digit lemma in the style of
    `dg_bump_gt`) plus `WF` and `Clear` for every frontier state (two inductions
    on `d`).  **≈180 lines, not done here.**  `searchNPD_of_frontier` above
    closes the gap at the *assembly* level only.

  ### §6(d): what the real `leafOK` costs

  Same tree, leaf test varied (named `def`s, never lambdas — a lambda leaf is not
  a fair comparison in the kernel):

  | leaf                       | wall | peak RSS |
  |---|---|---|
  | `fun _ _ _ => true`        |  7.7 s | 2.49 GB |
  | `decide (twoT n K A < 38)` | 12.5 s | 4.26 GB |
  | `leafOK`                   | 15.4 s | 5.11 GB |

  Net of baseline that is **≈0.6 ms per node** for the traversal, **≈2.4 ms per
  leaf** for `twoT`, and **≈25 ms per *high* leaf** for `charge`/`credit`.  A's
  synthetic `bench_leaf2` figure of ~17.5 ms per leaf was therefore right in
  order of magnitude for high leaves and ~10× too pessimistic for the other 94%.
  Projected onto the plan's pruned census (2,923,555 nodes, 231,461 leaves,
  31,902 high): 29 + 9 + 13 ≈ **51 minutes** — the top of §5 D10's 25–60 min
  budget, and only if chunks stay small.

  ### §6(f): the chunk ceiling is NOT 20,000

  Consecutive frontier slices of `n = 8`, masks `[3,3,3,4,4,8,8,12]`, real `leafOK`:

  | nodes | wall | peak RSS | ms/node | MB/node |
  |---|---|---|---|---|
  |  5,006 |   6.4 s | 2.25 GB |  1.27 | 0.32 |
  |  9,993 |  12.7 s | 4.25 GB |  1.27 | 0.36 |
  | 19,997 |  55.0 s | 7.42 GB |  2.75 | 0.34 |
  | 29,987 | 350.5 s | 7.00 GB | 11.7  | 0.21 |

  Memory is linear at ~0.34 MB per node; time is linear to ~10,000 nodes and then
  leaves the rails.  The 30,000-node point costs 6.4× the 20,000-node point for
  1.5× the work at a peak RSS that *stops rising* — it is paging, not computing.
  **Set the ceiling at 5,000 nodes**: 2.25 GB and 1.27 ms/node, which also lets
  the chunk files be checked in parallel on an ordinary machine.  The plan's 270
  declarations become ~590; that is a generator parameter, not a redesign.

  ### The prune is load-bearing, and by how much

  `goNP` as it stands has **no prune**.  Prune-free node counts of the whole
  search, by shell size (C re-derivation; agrees with Python wherever both ran):

  | n | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
  |---|---|---|---|---|---|---|---|---|---|
  | multisets | 1 | 14 | 92 | 221 | 249 | 172 | 81 | 25 | 6 |
  | nodes | 4 | 105 | 2,020 | 48,173 | 901,642 | 17,685,901 | 352,942,234 | 5,312,915,624 | 91,596,831,556 |

  The multiset counts sum to **862**, the number obligation 19 asserts — an
  independent confirmation of `msGen`'s target, from a generator written for a
  different purpose.

  The cheap per-multiset feasibility filter of `enum9.py`
  (`base₂ + 2·min(|P₂₂|, |W₂|) ≥ 38`) leaves **151 of the 862** and — usefully —
  **none at all at n = 11 or n = 12**, so the two worst shell sizes never enter a
  search at all.  Over the 151 survivors the prune-free tree is still
  **614,272,866 nodes** (n=6: 11,268; n=7: 213,245; n=8: 6,433,072;
  n=9: 62,038,398; n=10: 545,576,883).

  At 0.6 ms per node that is **102 hours**.  The plan's budget is 2,923,555 nodes,
  so obligations **14–16** have to buy a further factor of **210** *inside* the
  search.  §6(c) calls the prune "load-bearing with no plan B"; this is the number
  that says how load-bearing.  Nothing in this file or in `Search.lean` is
  affordable at census scale without it.

  ### Negative controls — the generator cannot hide a mistake

  Each of these was built and compiled; each fails.  (Where `sorry` appears below
  it stands in for the expensive `decide +kernel` bodies, so that the *structural*
  failure is what is being observed; the real file has no `sorry` anywhere.)

  1. **A chunk dropped from the peeling chain.**  `Application type mismatch: h6
     has type goAll … (List.drop 10 FPil) = true but is expected to have type
     goAll … (List.drop 8 FPil) = true`, pointing at the exact `have`.
  2. **A chunk stated at the wrong offset** (`drop 5` where the chain needs
     `drop 4`): the same crisp mismatch, plus a `rewrite failed` in
     `pilot_frontier_count`.
  3. **The residual claimed one state early** (`FPil.drop 27 = []`):
     `Tactic 'decide' proved that the proposition … is false`.
  4. **A wrong node count** (`(11576, 0)` for the pilot): the `decide` fails.
  5. **A bug inside `expand` itself** (drop the take-branch — exactly the shape of
     the off-by-one that produced `(37576, 2523, 2285)` in plan §6(e)):
     `goNP_eq_goAll_expand` and `goCnt_fst_eq` stop compiling.  This is layer 1
     of §6(e) in action: the generator is a `def` the soundness theorem is proved
     *about*, so a traversal bug is unprovable rather than undetected.

  Controls 1–3 report a wrong *line*, which matters at ~590 declarations.  Two
  choices above are what buy that: the peeling chain is written backwards from
  the residual so every step carries an explicit type, and `FPil` is
  `irreducible` so the unifier reports a mismatch instead of trying to normalise
  two 28-element lists (without it, control 1 is a `whnf` heartbeat timeout —
  still a failure, but an unreadable one).  The kernel ignores `irreducible`, so
  `decide +kernel` is unaffected.
-/

end Delta4Model
