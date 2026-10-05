import DaveyThesis2024.Delta4.Prune
import DaveyThesis2024.Delta4.AssemblyLayers

/-!
# Δ = 4: the chunk algebra for the PRUNED traversal

`Delta4/Chunk.lean` splits a search across declarations, but it is written for the prune-free
`goNP`, whose tree is about **614 million** nodes (~200 h).  `checkAll` names `searchP`, i.e.
`goPrune pruneOK`, whose tree is **2,685,792** nodes.  So that algebra does not apply, and this
file is the version that does.

**The prune is a parameter, and both instances are theorems, not conventions.**  `goG` is one
traversal; `goG_eq_goP` specialises it at `pruneOK` and `goG_noPr_eq_goNP` at the constant-false
prune, recovering `goNP`.  So the algebra is proved once rather than twice, and `Chunk.lean`
could later be rebuilt on this file instead of duplicating it.

**The frontier is a `List Nat`, deliberately.**  The traversal peels one pair per level, so every
depth-`d` state carries the same undecided list `ps.drop d` — including states that ran out
early.  The frontier is therefore just the surviving adjacency words, and a chunk can name a
*literal* list tied to the traversal by one kernel-checked equation.  This defuses a measured
trap: `@[irreducible]` does **not** stop the kernel, so a `(F.drop a).take b` frontier
re-evaluates from the root in every chunk (~14.4 s and 5.45 GB per declaration).

**Node counts are the assertion, and they have to be.**  `LayerOK n` is a closed decidable
proposition, so it reduces to `true = true` and a proof about one layer is defeq-accepted for
another — verified.  `layerOK_of_msCnt` instead consumes `msCnt n (msGen n) = (N, 0)`, where
`(3764, 0)` and `(92, 0)` are different propositions.  Negative controls confirm the discipline
cannot be gamed: dropping a frontier chunk, dropping a mask slice, claiming a residual one entry
early, and asserting a wrong count each FAIL to typecheck.

**Scale caveats for whoever generates against this.**  The largest instance demonstrated here is
881 nodes over a 7-state frontier, and the real workload is far lumpier: the heaviest single mask
at `n = 10` is 614,485 nodes — 23% of the whole census in one mask — and its frontier opens
slowly (depth 12 gives only 16 states).  Build **one layer-9 heavy mask end to end** before
committing to thousands of declarations.  Note also that `decide +kernel` reports a *false*
statement and an *exhausted* one with the same message, so a generator cannot distinguish a real
violation from a resource wall by the error text; re-check any failing chunk at smaller width.
-/

namespace Delta4Chunk
open Delta4Model

/-- A prune predicate: shell size, mask word, partial adjacency, undecided pairs. -/
abbrev Pr : Type := Nat → Nat → Nat → List (Nat × Nat) → Bool

/-- The constant-`false` prune: the instance that recovers `Search.goNP`. -/
def noPr : Pr := fun _ _ _ _ => false

@[inline] def pAdd (x y : Nat × Nat) : Nat × Nat := (x.1 + y.1, x.2 + y.2)

@[simp] theorem pAdd_fst (x y : Nat × Nat) : (pAdd x y).1 = x.1 + y.1 := rfl
@[simp] theorem pAdd_snd (x y : Nat × Nat) : (pAdd x y).2 = x.2 + y.2 := rfl

/-! ## A.  One traversal, parametrised by the prune -/

/-- `goG pr leafP n K ps A`: `Search.goNP` with a prune test at every internal node.
    `pr = noPr` gives `goNP` back; `pr = pruneOK`, `leafP = leafOK` gives `Prune.goP`. -/
def goG (pr : Pr) (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    List (Nat × Nat) → Nat → Bool
  | [],      A => leafP n K A
  | p :: ps, A =>
      if pr n K A (p :: ps) then true
      else
        goG pr leafP n K ps A
          && (if takeGuard n K A p.1 p.2 then goG pr leafP n K ps (addEdge A p.1 p.2) else true)

/-- Instance 1: the pruned traversal of `Prune.lean` is `goG` at `leafOK`. -/
theorem goG_eq_goPrune (pr : Pr) (n K : Nat) :
    ∀ (ps : List (Nat × Nat)) (A : Nat), goG pr leafOK n K ps A = goPrune pr n K ps A := by
  intro ps
  induction ps with
  | nil => intro A; rfl
  | cons p ps ih =>
      intro A
      rw [goG, goPrune, ih A, ih (addEdge A p.1 p.2)]

theorem goG_eq_goP (n K : Nat) (ps : List (Nat × Nat)) (A : Nat) :
    goG pruneOK leafOK n K ps A = goP n K ps A :=
  goG_eq_goPrune pruneOK n K ps A

/-- Instance 2: the prune-free traversal of `Search.lean` is `goG` at `noPr`.
    So the algebra below subsumes `Chunk.lean`'s, which is the point of the parameter. -/
theorem goG_noPr_eq_goNP (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    ∀ (ps : List (Nat × Nat)) (A : Nat), goG noPr leafP n K ps A = goNP leafP n K ps A := by
  intro ps
  induction ps with
  | nil => intro A; rfl
  | cons p ps ih =>
      intro A
      rw [goG, goNP, ih A, ih (addEdge A p.1 p.2)]
      rw [if_neg (by simp [noPr])]

/-! ## B.  The counting twin -/

/-- `goGCnt` walks exactly the tree `goG` walks and returns `(nodes, violations)`.
    It does not short-circuit, so `.1` is the exact node count; a pruned node counts
    as one node with no children, which is what the traversal actually visits. -/
def goGCnt (pr : Pr) (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    List (Nat × Nat) → Nat → Nat × Nat
  | [],      A => (1, if leafP n K A then 0 else 1)
  | p :: ps, A =>
      if pr n K A (p :: ps) then (1, 0)
      else
        pAdd (1, 0)
          (pAdd (goGCnt pr leafP n K ps A)
            (if takeGuard n K A p.1 p.2 then goGCnt pr leafP n K ps (addEdge A p.1 p.2)
             else (0, 0)))

/-- **The two accumulators agree.**  Zero violations is exactly a `true`. -/
theorem goG_eq_true_iff_goGCnt (pr : Pr) (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    ∀ (ps : List (Nat × Nat)) (A : Nat),
      goG pr leafP n K ps A = true ↔ (goGCnt pr leafP n K ps A).2 = 0 := by
  intro ps
  induction ps with
  | nil =>
      intro A
      rw [goG, goGCnt]
      cases h : leafP n K A <;> simp
  | cons p ps ih =>
      intro A
      by_cases hp : pr n K A (p :: ps) = true
      · rw [goG, goGCnt, if_pos hp, if_pos hp]
        simp
      · rw [goG, goGCnt, if_neg hp, if_neg hp, Bool.and_eq_true, pAdd_snd, pAdd_snd]
        by_cases hg : takeGuard n K A p.1 p.2 = true
        · rw [if_pos hg, if_pos hg, ih A, ih (addEdge A p.1 p.2)]
          simp only []
          omega
        · rw [if_neg hg, if_neg hg, ih A]
          simp

/-! ## C.  The horizontal cut: a depth-`d` frontier that is a `List Nat`

  `Chunk.lean`'s frontier is a `List St = List (List (Nat × Nat) × Nat)`.  It need not be:
  the traversal peels exactly one pair per level, so **every** state on the depth-`d`
  frontier carries the same undecided list, `ps.drop d` — including the states that ran
  out of pairs early, since `ps.drop k = []` already forces `ps.drop d = []` for `d ≥ k`.
  So the frontier is a list of adjacency words, a `List Nat`, and the common pair list is
  carried once as an argument.

  That is not cosmetic.  It is what lets a generated chunk name the frontier as a
  **numeric literal** instead of as `expand n K d (pairList n, 0)`: with the latter, every
  chunk declaration re-runs the whole depth-`d` expansion inside the kernel (measured
  ~14 s and 5.45 GB per declaration, and `@[irreducible]` does not stop it, because the
  kernel ignores the attribute).  With a literal, `List.drop`/`List.take` is a walk down a
  cons-list and the expansion is kernel-checked exactly once, in `F_eq` below. -/

/-- The depth-`d` frontier from `(ps, A)`, as the list of surviving adjacency words.
    A node at which the prune fires returns `true` outright, so it contributes **no**
    frontier state — that is the one case `Chunk.lean`'s `expand` does not have. -/
def expandP (pr : Pr) (n K : Nat) : Nat → List (Nat × Nat) → Nat → List Nat
  | 0,     _,       A => [A]
  | _ + 1, [],      A => [A]
  | d + 1, p :: ps, A =>
      if pr n K A (p :: ps) then []
      else
        expandP pr n K d ps A
          ++ (if takeGuard n K A p.1 p.2 then expandP pr n K d ps (addEdge A p.1 p.2) else [])

/-- Internal nodes strictly above the depth-`d` frontier.  A pruned node is internal and
    childless, hence the `1`. -/
def expandPNodes (pr : Pr) (n K : Nat) : Nat → List (Nat × Nat) → Nat → Nat
  | 0,     _,       _ => 0
  | _ + 1, [],      _ => 0
  | d + 1, p :: ps, A =>
      if pr n K A (p :: ps) then 1
      else
        expandPNodes pr n K d ps A + 1
          + (if takeGuard n K A p.1 p.2 then expandPNodes pr n K d ps (addEdge A p.1 p.2) else 0)

/-- The `Bool` traversal over a frontier: one common undecided list, many adjacency words. -/
def goAllP (pr : Pr) (leafP : Nat → Nat → Nat → Bool) (n K : Nat)
    (ps : List (Nat × Nat)) : List Nat → Bool
  | []      => true
  | A :: As => goG pr leafP n K ps A && goAllP pr leafP n K ps As

/-- The counting traversal over a frontier. -/
def goAllPCnt (pr : Pr) (leafP : Nat → Nat → Nat → Bool) (n K : Nat)
    (ps : List (Nat × Nat)) : List Nat → Nat × Nat
  | []      => (0, 0)
  | A :: As => pAdd (goGCnt pr leafP n K ps A) (goAllPCnt pr leafP n K ps As)

theorem goAllP_append (pr : Pr) (leafP : Nat → Nat → Nat → Bool) (n K : Nat)
    (ps : List (Nat × Nat)) :
    ∀ xs ys : List Nat,
      goAllP pr leafP n K ps (xs ++ ys)
        = (goAllP pr leafP n K ps xs && goAllP pr leafP n K ps ys) := by
  intro xs
  induction xs with
  | nil => intro ys; simp [goAllP]
  | cons A As ih => intro ys; simp [goAllP, ih, Bool.and_assoc]

theorem goAllPCnt_append (pr : Pr) (leafP : Nat → Nat → Nat → Bool) (n K : Nat)
    (ps : List (Nat × Nat)) :
    ∀ xs ys : List Nat,
      goAllPCnt pr leafP n K ps (xs ++ ys)
        = pAdd (goAllPCnt pr leafP n K ps xs) (goAllPCnt pr leafP n K ps ys) := by
  intro xs
  induction xs with
  | nil => intro ys; simp [goAllPCnt, pAdd]
  | cons A As ih =>
      intro ys
      simp only [List.cons_append, goAllPCnt, ih, pAdd, Prod.mk.injEq]
      omega

theorem goAllP_eq_true_iff_goAllPCnt (pr : Pr) (leafP : Nat → Nat → Nat → Bool) (n K : Nat)
    (ps : List (Nat × Nat)) :
    ∀ L : List Nat, goAllP pr leafP n K ps L = true ↔ (goAllPCnt pr leafP n K ps L).2 = 0 := by
  intro L
  induction L with
  | nil => simp [goAllP, goAllPCnt]
  | cons A As ih =>
      rw [goAllP, goAllPCnt, Bool.and_eq_true, pAdd_snd, ih,
        goG_eq_true_iff_goGCnt pr leafP n K ps A]
      omega

/-- **The chunk-declaration consumer.**  A `decide +kernel` fact of the shape
    `goAllPCnt … c = (N, 0)` — node count *and* zero violations in one equation. -/
theorem goAllP_of_goAllPCnt {pr : Pr} {leafP : Nat → Nat → Nat → Bool} {n K : Nat}
    {ps : List (Nat × Nat)} {L : List Nat} {N : Nat}
    (h : goAllPCnt pr leafP n K ps L = (N, 0)) : goAllP pr leafP n K ps L = true :=
  (goAllP_eq_true_iff_goAllPCnt pr leafP n K ps L).2 (by rw [h])

/-- **The horizontal cut is sound.**  Running `d` levels and conjoining over the frontier
    is the traversal.  The undecided list on the frontier is `ps.drop d`, uniformly. -/
theorem goG_eq_goAllP_expandP (pr : Pr) (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    ∀ (d : Nat) (ps : List (Nat × Nat)) (A : Nat),
      goG pr leafP n K ps A = goAllP pr leafP n K (ps.drop d) (expandP pr n K d ps A) := by
  intro d
  induction d with
  | zero => intro ps A; simp [expandP, goAllP]
  | succ d ih =>
      intro ps A
      cases ps with
      | nil => simp [expandP, goAllP, goG]
      | cons p ps =>
          rw [List.drop_succ_cons, expandP, goG]
          by_cases hp : pr n K A (p :: ps) = true
          · rw [if_pos hp, if_pos hp]; rfl
          · rw [if_neg hp, if_neg hp, goAllP_append]
            by_cases hg : takeGuard n K A p.1 p.2 = true
            · rw [if_pos hg, if_pos hg, ← ih ps A, ← ih ps (addEdge A p.1 p.2)]
            · rw [if_neg hg, if_neg hg, ← ih ps A]
              simp [goAllP]

/-- **Node accounting, as a theorem.**  `nodes(tree) = internal + Σ nodes(chunks)`. -/
theorem goGCnt_fst_eq (pr : Pr) (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    ∀ (d : Nat) (ps : List (Nat × Nat)) (A : Nat),
      (goGCnt pr leafP n K ps A).1
        = expandPNodes pr n K d ps A
          + (goAllPCnt pr leafP n K (ps.drop d) (expandP pr n K d ps A)).1 := by
  intro d
  induction d with
  | zero => intro ps A; simp [expandP, expandPNodes, goAllPCnt, pAdd]
  | succ d ih =>
      intro ps A
      cases ps with
      | nil => simp [expandP, expandPNodes, goAllPCnt, goGCnt, pAdd]
      | cons p ps =>
          rw [List.drop_succ_cons, expandP, expandPNodes, goGCnt]
          by_cases hp : pr n K A (p :: ps) = true
          · rw [if_pos hp, if_pos hp, if_pos hp]
            simp [goAllPCnt]
          · rw [if_neg hp, if_neg hp, if_neg hp, goAllPCnt_append]
            by_cases hg : takeGuard n K A p.1 p.2 = true
            · rw [if_pos hg, if_pos hg, if_pos hg]
              have h1 := ih ps A
              have h2 := ih ps (addEdge A p.1 p.2)
              simp only [pAdd_fst] at *
              omega
            · rw [if_neg hg, if_neg hg, if_neg hg]
              have h1 := ih ps A
              simp only [pAdd_fst, goAllPCnt] at *
              omega

/-- The violation count splits with no internal contribution: a pruned node is not a
    violation, and it has no leaves below it in the counted tree. -/
theorem goGCnt_snd_eq (pr : Pr) (leafP : Nat → Nat → Nat → Bool) (n K : Nat) :
    ∀ (d : Nat) (ps : List (Nat × Nat)) (A : Nat),
      (goGCnt pr leafP n K ps A).2
        = (goAllPCnt pr leafP n K (ps.drop d) (expandP pr n K d ps A)).2 := by
  intro d
  induction d with
  | zero => intro ps A; simp [expandP, goAllPCnt, pAdd]
  | succ d ih =>
      intro ps A
      cases ps with
      | nil => simp [expandP, goAllPCnt, goGCnt, pAdd]
      | cons p ps =>
          rw [List.drop_succ_cons, expandP, goGCnt]
          by_cases hp : pr n K A (p :: ps) = true
          · rw [if_pos hp, if_pos hp]
            simp [goAllPCnt]
          · rw [if_neg hp, if_neg hp, goAllPCnt_append]
            by_cases hg : takeGuard n K A p.1 p.2 = true
            · rw [if_pos hg, if_pos hg]
              have h1 := ih ps A
              have h2 := ih ps (addEdge A p.1 p.2)
              simp only [pAdd_snd] at *
              omega
            · rw [if_neg hg, if_neg hg]
              have h1 := ih ps A
              simp only [pAdd_snd, goAllPCnt] at *
              omega

/-! ## D.  The vertical cut: slicing the frontier by offsets

  Exactly `Chunk.lean` §C, one type lower.  **There is no chunk literal**: the generator
  emits three numerals per chunk (offset, width, node count) and the cover is
  `List.take_append_drop`, so a dropped, duplicated or misordered chunk cannot be hidden —
  the chain closes only when the residual is `[]` and the offsets chain as `a ↦ a + b`. -/

theorem goAllP_peel {pr : Pr} {leafP : Nat → Nat → Nat → Bool} {n K : Nat}
    {ps : List (Nat × Nat)} {L : List Nat} {a b c : Nat} (h : a + b = c)
    (hc : goAllP pr leafP n K ps ((L.drop a).take b) = true)
    (hr : goAllP pr leafP n K ps (L.drop c) = true) :
    goAllP pr leafP n K ps (L.drop a) = true := by
  have hsplit : (L.drop a).take b ++ L.drop c = L.drop a := by
    have h1 : (L.drop a).drop b = L.drop c := by rw [List.drop_drop, h]
    rw [← h1]; exact List.take_append_drop b (L.drop a)
  rw [← hsplit, goAllP_append, hc, hr]
  rfl

theorem goAllPCnt_peel (pr : Pr) (leafP : Nat → Nat → Nat → Bool) (n K : Nat)
    (ps : List (Nat × Nat)) (L : List Nat) (a b c : Nat) (h : a + b = c) :
    goAllPCnt pr leafP n K ps (L.drop a)
      = pAdd (goAllPCnt pr leafP n K ps ((L.drop a).take b))
          (goAllPCnt pr leafP n K ps (L.drop c)) := by
  have hsplit : (L.drop a).take b ++ L.drop c = L.drop a := by
    have h1 : (L.drop a).drop b = L.drop c := by rw [List.drop_drop, h]
    rw [← h1]; exact List.take_append_drop b (L.drop a)
  have e : goAllPCnt pr leafP n K ps (L.drop a)
      = goAllPCnt pr leafP n K ps ((L.drop a).take b ++ L.drop c) := by rw [hsplit]
  rw [e, goAllPCnt_append]

theorem goAllP_nil {pr : Pr} {leafP : Nat → Nat → Nat → Bool} {n K : Nat}
    {ps : List (Nat × Nat)} {L : List Nat} {a : Nat} (h : L.drop a = []) :
    goAllP pr leafP n K ps (L.drop a) = true := by
  rw [h]; rfl

/-! ## E.  Entry points into `Prune.lean` -/

/-- From a chained frontier fact to `searchP n K = true`. -/
theorem searchP_of_frontier (n K d : Nat)
    (h : goAllP pruneOK leafOK n K ((pairList n).drop d)
          ((expandP pruneOK n K d (pairList n) 0).drop 0) = true) :
    searchP n K = true := by
  rw [List.drop_zero] at h
  rw [searchP, ← goG_eq_goP, goG_eq_goAllP_expandP pruneOK leafOK n K d (pairList n) 0]
  exact h

/-- **The whole pipeline, in one statement**: chunk declarations in, the model-side
    universal out.  `searchP_complete` is `Prune.lean`'s, unchanged. -/
theorem leafOK_of_frontierP {n K d : Nat}
    (h : goAllP pruneOK leafOK n K ((pairList n).drop d)
          ((expandP pruneOK n K d (pairList n) 0).drop 0) = true) :
    ∀ A : Nat, Box n K A = true → leafOK n K A = true :=
  fun A hbox => searchP_complete n K A hbox (searchP_of_frontier n K d h)

/-! ## F.  The outer layer: the loop over `msGen n` -/

def searchPCnt (n K : Nat) : Nat × Nat := goGCnt pruneOK leafOK n K (pairList n) 0

theorem searchP_eq_true_iff_searchPCnt (n K : Nat) :
    searchP n K = true ↔ (searchPCnt n K).2 = 0 := by
  rw [searchP, ← goG_eq_goP, searchPCnt, goG_eq_true_iff_goGCnt]

/-- `msCnt n Ks`: nodes and violations summed over a slice of the mask list. -/
def msCnt (n : Nat) : List Nat → Nat × Nat
  | []      => (0, 0)
  | K :: Ks => pAdd (searchPCnt n K) (msCnt n Ks)

theorem msCnt_append (n : Nat) :
    ∀ xs ys : List Nat, msCnt n (xs ++ ys) = pAdd (msCnt n xs) (msCnt n ys) := by
  intro xs
  induction xs with
  | nil => intro ys; simp [msCnt, pAdd]
  | cons K Ks ih =>
      intro ys
      simp only [List.cons_append, msCnt, ih, pAdd, Prod.mk.injEq]
      omega

/-- Slice the **mask list** exactly as the frontier is sliced: three numerals per chunk,
    no literal, and the offsets chain as `a ↦ a + b`. -/
theorem msCnt_peel (n : Nat) (Ks : List Nat) (a b c : Nat) (h : a + b = c) :
    msCnt n (Ks.drop a)
      = pAdd (msCnt n ((Ks.drop a).take b)) (msCnt n (Ks.drop c)) := by
  have hsplit : (Ks.drop a).take b ++ Ks.drop c = Ks.drop a := by
    have h1 : (Ks.drop a).drop b = Ks.drop c := by rw [List.drop_drop, h]
    rw [← h1]; exact List.take_append_drop b (Ks.drop a)
  have e : msCnt n (Ks.drop a) = msCnt n ((Ks.drop a).take b ++ Ks.drop c) := by rw [hsplit]
  rw [e, msCnt_append]

theorem msCnt_nil {n : Nat} {Ks : List Nat} {a : Nat} (h : Ks.drop a = []) :
    msCnt n (Ks.drop a) = (0, 0) := by rw [h]; rfl

theorem msAll_eq_true_iff_msCnt (n : Nat) :
    ∀ Ks : List Nat, Ks.all (fun K => searchP n K) = true ↔ (msCnt n Ks).2 = 0 := by
  intro Ks
  induction Ks with
  | nil => simp [msCnt]
  | cons K Ks ih =>
      rw [List.all_cons, msCnt, Bool.and_eq_true, pAdd_snd, ih,
        searchP_eq_true_iff_searchPCnt n K]
      omega

/-- **What lets a layer be split across declarations.** -/
theorem msAll_of_msCnt {n : Nat} {Ks : List Nat} {N : Nat} (h : msCnt n Ks = (N, 0)) :
    Ks.all (fun K => searchP n K) = true :=
  (msAll_eq_true_iff_msCnt n Ks).2 (by rw [h])

/-- **The heavy-mask bridge.**  A one-element mask list costs exactly its mask.

    This is what carries a heavy mask — closed separately as `searchPCnt n K = (N, 0)` via the
    frontier cut — into the outer `msCnt` chain, where it sits alongside the light slices.
    `msCnt_peel` only ever splits `Ks.drop a` and `msCnt_nil` only kills a residual, so without
    this nothing evaluates a singleton.  Two independent attempts at closing a layer both found
    it missing at exactly this point. -/
theorem msCnt_singleton (n K : Nat) : msCnt n [K] = searchPCnt n K := by
  show pAdd (searchPCnt n K) (msCnt n []) = searchPCnt n K
  show ((searchPCnt n K).1 + 0, (searchPCnt n K).2 + 0) = searchPCnt n K
  rw [Nat.add_zero, Nat.add_zero]

/-- The same, consuming the per-mask fact directly. -/
theorem msCnt_single {n K N V : Nat} (h : searchPCnt n K = (N, V)) : msCnt n [K] = (N, V) := by
  rw [msCnt_singleton, h]

/-- …and the same fact in the shape `AssemblyLayers.checkAll_of_layers` consumes.
    Note what the hypothesis says: a **node count**.  `LayerOK n` on its own is a closed
    decidable proposition and is therefore defeq-accepted across layers; `msCnt 6 … =
    (3764, 0)` and `msCnt 5 … = (92, 0)` are different propositions. -/
theorem layerOK_of_msCnt {n N : Nat} (h : msCnt n (msGen n) = (N, 0)) :
    Delta4Assembly.LayerOK n :=
  msAll_of_msCnt h

/-! ### The same lemmas under the names a `goP`-level generator wants

  §A–§E are stated for an arbitrary prune, which is what removes the duplication.  These
  are the `pruneOK`/`leafOK` instances under the plain names, so that generated code never
  has to mention `goG` or carry the two parameters. -/

/-- The counting twin of `Prune.goP`. -/
abbrev goPCnt (n K : Nat) : List (Nat × Nat) → Nat → Nat × Nat := goGCnt pruneOK leafOK n K

theorem goP_eq_true_iff_goPCnt (n K : Nat) (ps : List (Nat × Nat)) (A : Nat) :
    goP n K ps A = true ↔ (goPCnt n K ps A).2 = 0 := by
  rw [← goG_eq_goP]; exact goG_eq_true_iff_goGCnt pruneOK leafOK n K ps A

theorem goP_eq_goAllP_expandP (n K d : Nat) (ps : List (Nat × Nat)) (A : Nat) :
    goP n K ps A = goAllP pruneOK leafOK n K (ps.drop d) (expandP pruneOK n K d ps A) := by
  rw [← goG_eq_goP]; exact goG_eq_goAllP_expandP pruneOK leafOK n K d ps A

theorem goPCnt_fst_eq (n K d : Nat) (ps : List (Nat × Nat)) (A : Nat) :
    (goPCnt n K ps A).1
      = expandPNodes pruneOK n K d ps A
        + (goAllPCnt pruneOK leafOK n K (ps.drop d) (expandP pruneOK n K d ps A)).1 :=
  goGCnt_fst_eq pruneOK leafOK n K d ps A

theorem goPCnt_snd_eq (n K d : Nat) (ps : List (Nat × Nat)) (A : Nat) :
    (goPCnt n K ps A).2
      = (goAllPCnt pruneOK leafOK n K (ps.drop d) (expandP pruneOK n K d ps A)).2 :=
  goGCnt_snd_eq pruneOK leafOK n K d ps A

theorem searchPCnt_eq (n K : Nat) : searchPCnt n K = goPCnt n K (pairList n) 0 := rfl

/-! ## G.  A kernel-checked instance of the frontier cut

  `n = 6`, mask word `K = 13419315` — the heaviest multiset of layer 6 at **881 pruned
  nodes** (the prune-free tree of layer 6 alone is 48,173 nodes).  Depth-5 frontier:
  7 states, 9 internal nodes, 872 subtree nodes, `9 + 872 = 881`.

  The frontier is written as a **literal `List Nat`** (`F6`) and tied to the generator by
  one kernel-checked equation (`F6_eq`).  Every chunk below is then a `drop`/`take` of a
  cons-list of numerals; nothing re-runs the expansion.  Contrast `Chunk.lean`, where the
  chunk statements name `expand …` itself and each declaration re-expands from the root. -/

def K6 : Nat := 13419315
def dep6 : Nat := 5

/-- The undecided pairs shared by every depth-5 frontier state.  There is exactly one such
    list, which is what makes a `List Nat` frontier possible at all. -/
abbrev PS6 : List (Nat × Nat) := (pairList 6).drop dep6

/-- The depth-`dep6` frontier, as a literal.  `irreducible` so that a mis-chained peel is a
    crisp type mismatch in the unifier instead of a `whnf` timeout; the kernel ignores the
    attribute, so `decide +kernel` still evaluates it — and, because it is a *literal*,
    evaluating it is a walk down a cons-list, not a re-run of the expansion. -/
@[irreducible] def F6 : List Nat :=
  [0, 1152921504606847008, 2305843009213825024, 3458764513820672032, 4611686018964258816, 5764607523571105824, 6917529028178083840]

/-- …tied to the traversal by one kernel evaluation.  This is the *only* place the
    expansion is computed. -/
theorem F6_eq : expandP pruneOK 6 K6 dep6 (pairList 6) 0 = F6 := by decide +kernel

/-- The internal nodes above it: a second, independent kernel fact. -/
theorem F6_internal : expandPNodes pruneOK 6 K6 dep6 (pairList 6) 0 = 9 := by decide +kernel


/-- frontier chunk 0: states [0, 2), 196 nodes. -/
theorem f6_chunk_0 :
    goAllPCnt pruneOK leafOK 6 K6 PS6 ((F6.drop 0).take 2) = (196, 0) := by decide +kernel


/-- frontier chunk 1: states [2, 5), 385 nodes. -/
theorem f6_chunk_1 :
    goAllPCnt pruneOK leafOK 6 K6 PS6 ((F6.drop 2).take 3) = (385, 0) := by decide +kernel


/-- frontier chunk 2: states [5, 7), 291 nodes. -/
theorem f6_chunk_2 :
    goAllPCnt pruneOK leafOK 6 K6 PS6 ((F6.drop 5).take 2) = (291, 0) := by decide +kernel


theorem F6_residual : F6.drop 7 = [] := by decide +kernel


/-- **The chunk counts, chained.**  No traversal is re-run. -/
theorem f6_frontier_count :
    goAllPCnt pruneOK leafOK 6 K6 PS6 (F6.drop 0) = (872, 0) := by
  rw [goAllPCnt_peel pruneOK leafOK 6 K6 PS6 F6 0 2 2 rfl, f6_chunk_0,
      goAllPCnt_peel pruneOK leafOK 6 K6 PS6 F6 2 3 5 rfl, f6_chunk_1,
      goAllPCnt_peel pruneOK leafOK 6 K6 PS6 F6 5 2 7 rfl, f6_chunk_2,
      F6_residual]
  rfl


/-- **The peeling chain**, written backwards from the residual so that every step carries
    an explicit type: a missing or misplaced chunk is a type error at that `have`. -/
theorem f6_frontier_ok : goAllP pruneOK leafOK 6 K6 PS6 (F6.drop 0) = true := by
  have h3 : goAllP pruneOK leafOK 6 K6 PS6 (F6.drop 7) = true :=
    goAllP_nil F6_residual
  have h2 : goAllP pruneOK leafOK 6 K6 PS6 (F6.drop 5) = true :=
    goAllP_peel (b := 2) (c := 7) rfl (goAllP_of_goAllPCnt f6_chunk_2) h3
  have h1 : goAllP pruneOK leafOK 6 K6 PS6 (F6.drop 2) = true :=
    goAllP_peel (b := 3) (c := 5) rfl (goAllP_of_goAllPCnt f6_chunk_1) h2
  have h0 : goAllP pruneOK leafOK 6 K6 PS6 (F6.drop 0) = true :=
    goAllP_peel (b := 2) (c := 2) rfl (goAllP_of_goAllPCnt f6_chunk_0) h1
  exact h0


/-- **The node count of the whole mask, derived** from the chunk declarations and the
    internal count — `goGCnt_fst_eq`/`goGCnt_snd_eq` do the arithmetic, and nothing
    traverses the tree a second time. -/
theorem f6_mask_count : searchPCnt 6 K6 = (881, 0) := by
  have hfc : goAllPCnt pruneOK leafOK 6 K6 PS6 (expandP pruneOK 6 K6 dep6 (pairList 6) 0)
      = (872, 0) := by
    have h := f6_frontier_count
    rw [List.drop_zero] at h
    rw [F6_eq]
    exact h
  have h1 := goGCnt_fst_eq pruneOK leafOK 6 K6 dep6 (pairList 6) 0
  have h2 := goGCnt_snd_eq pruneOK leafOK 6 K6 dep6 (pairList 6) 0
  simp only [hfc, F6_internal] at h1 h2
  exact Prod.ext h1 h2

/-- The `Bool` route to the same mask, through `Prune.searchP_complete`: from the chunk
    declarations to a universally quantified model statement. -/
theorem f6_all_boxes (A : Nat) (hbox : Box 6 K6 A = true) : leafOK 6 K6 A = true := by
  have h := f6_frontier_ok
  rw [List.drop_zero, ← F6_eq] at h
  exact leafOK_of_frontierP (d := dep6) (by rw [List.drop_zero]; exact h) A hbox


/-! ## H.  A kernel-checked instance of the outer cut: **the whole of layer 6**

  221 mask multisets, **3,764 pruned nodes**, 0 violations — the layer node count from the
  independent census.  Seven declarations, each ≤ 885 nodes (measured ~3 ms and ~4 MB per
  pruned node, so ~900 nodes is where a declaration stays near 3.7 GB).

  What is asserted is a node count.  `LayerOK 6` on its own would be defeq-accepted as a
  proof of `LayerOK 5`; `msCnt 6 M6 = (3764, 0)` is not `msCnt 5 (msGen 5) = (92, 0)`. -/

/-- The 221 mask words of layer 6, as a literal — same reason as `F6`. -/
@[irreducible] def M6 : List Nat :=
  [15655185, 16695825, 15651345, 15647505, 16688145, 15643665, 15639825, 16680465,
   15635985, 16557585, 15574545, 15513105, 15632145, 15509265, 16630305, 15585825,
   16565025, 15581985, 16745505, 16684065, 16622625, 16561185, 15578145, 16680225,
   15635745, 16557345, 15574305, 15512865, 16614945, 16553505, 15570465, 14525985,
   14464545, 16549665, 15566625, 15505185, 14460705, 13416225, 15516465, 16679985,
   15635505, 16557105, 15574065, 15512625, 15631665, 15508785, 16549425, 15566385,
   15504945, 14460465, 13415985, 15501105, 13412145, 16491585, 15447105, 16426305,
   15443265, 16483905, 16422465, 15439425, 14394945, 13350465, 16418625, 15435585,
   15374145, 14329665, 13346625, 15377745, 16418385, 15435345, 15373905, 14329425,
   13346385, 15370065, 13281105, 16352865, 14386785, 15308385, 14325345, 13342305,
   16287585, 15304545, 14321505, 13338465, 13277025, 15239025, 13272945, 14537250,
   14533410, 16618530, 14529570, 16614690, 16553250, 15570210, 14525730, 14464290,
   14521890, 14518050, 14456610, 14467890, 16614450, 16553010, 15569970, 14525490,
   14464050, 16549170, 15566130, 15504690, 14460210, 13415730, 14517810, 14456370,
   14452530, 13408050, 16487490, 14398530, 16483650, 16422210, 15439170, 14394690,
   13350210, 16356930, 14390850, 16353090, 14387010, 15308610, 14325570, 13342530,
   16418130, 15435090, 15373650, 14329170, 13346130, 16352850, 14386770, 15308370,
   14325330, 13342290, 16287570, 15304530, 14321490, 13338450, 13277010, 14259810,
   14255970, 13211490, 14190450, 13207410, 13419315, 16548915, 15565875, 15504435,
   14459955, 13415475, 15500595, 13411635, 14452275, 13407795, 13403955, 16483395,
   16421955, 15438915, 14394435, 13349955, 16418115, 15435075, 15373635, 14329155,
   13346115, 16352835, 14386755, 15308355, 14325315, 13342275, 16287555, 15304515,
   14321475, 13338435, 13276995, 15369555, 13280595, 16287315, 15304275, 14321235,
   13338195, 13276755, 15238995, 13272915, 14255715, 13211235, 14190435, 13207395,
   13141875, 12301380, 12297540, 12293700, 12289860, 12228420, 12232020, 12289620,
   12228180, 12224340, 11179860, 12162660, 12158820, 11114340, 12093300, 11110260,
   11183445, 12224085, 11179605, 11175765, 12158565, 11114085, 12093285, 11110245,
   11044725, 10065510, 10061670, 9996150, 8947575]

theorem M6_eq : msGen 6 = M6 := by decide +kernel


/-- layer-6 slice 0: masks [0, 148), 412 nodes. -/
theorem l6_chunk_0 : msCnt 6 ((M6.drop 0).take 148) = (412, 0) := by decide +kernel


/-- layer-6 slice 1: masks [148, 153), 885 nodes. -/
theorem l6_chunk_1 : msCnt 6 ((M6.drop 148).take 5) = (885, 0) := by decide +kernel


/-- layer-6 slice 2: masks [153, 208), 502 nodes. -/
theorem l6_chunk_2 : msCnt 6 ((M6.drop 153).take 55) = (502, 0) := by decide +kernel


/-- layer-6 slice 3: masks [208, 210), 882 nodes. -/
theorem l6_chunk_3 : msCnt 6 ((M6.drop 208).take 2) = (882, 0) := by decide +kernel


/-- layer-6 slice 4: masks [210, 217), 173 nodes. -/
theorem l6_chunk_4 : msCnt 6 ((M6.drop 210).take 7) = (173, 0) := by decide +kernel


/-- layer-6 slice 5: masks [217, 218), 881 nodes. -/
theorem l6_chunk_5 : msCnt 6 ((M6.drop 217).take 1) = (881, 0) := by decide +kernel


/-- layer-6 slice 6: masks [218, 221), 29 nodes. -/
theorem l6_chunk_6 : msCnt 6 ((M6.drop 218).take 3) = (29, 0) := by decide +kernel


theorem M6_residual : M6.drop 221 = [] := by decide +kernel


/-- **The layer, chained.**  Seven chunk declarations in, one node count out. -/
theorem l6_count : msCnt 6 M6 = (3764, 0) := by
  rw [← List.drop_zero (l := M6),
      msCnt_peel 6 M6 0 148 148 rfl, l6_chunk_0,
      msCnt_peel 6 M6 148 5 153 rfl, l6_chunk_1,
      msCnt_peel 6 M6 153 55 208 rfl, l6_chunk_2,
      msCnt_peel 6 M6 208 2 210 rfl, l6_chunk_3,
      msCnt_peel 6 M6 210 7 217 rfl, l6_chunk_4,
      msCnt_peel 6 M6 217 1 218 rfl, l6_chunk_5,
      msCnt_peel 6 M6 218 3 221 rfl, l6_chunk_6,
      M6_residual]
  rfl

/-- **Layer 6 of `checkAll`, from the chunk declarations.**  `LayerOK 6` is what
    `AssemblyLayers.checkAll_of_layers` consumes. -/
theorem l6_layer : Delta4Assembly.LayerOK 6 := by
  refine layerOK_of_msCnt (N := 3764) ?_
  rw [M6_eq]
  exact l6_count


/-! ### The three layers that the prune kills at the root, for comparison

  Layers 3–5 are 1, 14 and 92 nodes: one node per multiset, i.e. the prune fires at every
  root.  They fit in one declaration each, and they are *different propositions* from each
  other and from layer 6. -/

theorem l3_count : msCnt 3 (msGen 3) = (1, 0) := by decide +kernel
theorem l4_count : msCnt 4 (msGen 4) = (14, 0) := by decide +kernel
theorem l5_count : msCnt 5 (msGen 5) = (92, 0) := by decide +kernel

theorem l3_layer : Delta4Assembly.LayerOK 3 := layerOK_of_msCnt l3_count
theorem l4_layer : Delta4Assembly.LayerOK 4 := layerOK_of_msCnt l4_count
theorem l5_layer : Delta4Assembly.LayerOK 5 := layerOK_of_msCnt l5_count

/-! ## I.  The prune-free instance, for free

  `noPr` is the constant-`false` prune, and `goG_noPr_eq_goNP` identifies `goG noPr` with
  `Search.goNP`.  So every lemma above is *also* a lemma about the prune-free traversal:
  `Chunk.lean`'s `goCnt`, `expand`, `goAll`, `goAllCnt`, the two accounting identities and
  the peel chain are the `noPr` instance of §B–§D, over `List Nat` instead of `List St`.
  The demonstration below runs the whole chain at `noPr` on `K₄,₄` (`n = 3`, `K = 4095`),
  where the prune-free tree is small enough to check twice. -/

theorem npFree_frontier :
    goAllPCnt noPr leafOK 3 4095 ((pairList 3).drop 2) (expandP noPr 3 4095 2 (pairList 3) 0)
      = (2, 0) := by decide +kernel

theorem npFree_internal : expandPNodes noPr 3 4095 2 (pairList 3) 0 = 2 := by decide +kernel

/-- The prune-free traversal of `K₄,₄`'s multiset, assembled from the frontier: 2 internal
    nodes plus a 1-state frontier of 2 nodes.  `2 + 2 = 4` is exactly the prune-free node
    count `Chunk.lean` §D reports for the whole of layer 3 — and the *pruned* count of the
    same layer is 1 (`l3_count`), the prune firing at the root. -/
theorem npFree_search : searchNP leafOK 3 4095 = true := by
  rw [searchNP, ← goG_noPr_eq_goNP,
    goG_eq_goAllP_expandP noPr leafOK 3 4095 2 (pairList 3) 0]
  exact goAllP_of_goAllPCnt npFree_frontier

/-! ## J.  Negative controls — the generator cannot hide a mistake

  Each control was built and compiled; each fails, and the failures are reported below
  verbatim.  (Where the controls used `sorry` it stood in for the expensive
  `decide +kernel` bodies, so that the *structural* failure is what is being observed.
  This file has no `sorry`.)

  1. **A chunk dropped from the peeling chain** (`f6_chunk_1` removed, `h0` wired to `h2`):

     ```
     error: Application type mismatch: The argument h2 has type
       goAllP pruneOK leafOK 6 K6 PS6 (List.drop 5 F6) = true
     but is expected to have type
       goAllP pruneOK leafOK 6 K6 PS6 (List.drop 2 F6) = true
     ```

     — the exact `have`, by line.  `F6` must be `irreducible` for this: without it the
     unifier tries to normalise two cons-lists of 64-bit numerals and the control fails
     as a `whnf` heartbeat timeout instead (observed, then fixed).

  2. **A chunk dropped from the count chain** (`l6_chunk_3` removed):

     ```
     error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
       msCnt 6 (List.drop 210 M6)
     in the target expression
       pAdd (412, 0) (pAdd (885, 0) (pAdd (502, 0) (msCnt 6 (List.drop 208 M6)))) = (3764, 0)
     ```

     The offsets are forced to chain as `a ↦ a + b`, so the gap is visible at the gap.

  3. **The residual claimed one entry early** (`M6.drop 220 = []`, and the last peel
     re-aimed at 220 to match).  *Two* failures, one of each kind:

     ```
     error: Tactic `decide` failed for proposition List.drop 220 M6 = []
     error: Application type mismatch: The argument rfl has type ?m = ?m
            but is expected to have type 218 + 3 = 220
     ```

     Leave the arithmetic alone and the residual claim is false; fix the residual claim and
     the arithmetic `218 + 3 = 221` is what breaks.  There is no third option.

  4. **A wrong total** (`l6_count` claiming `(3763, 0)`):

     ```
     error: Tactic `rfl` failed: The left-hand side
       pAdd (412, 0) (pAdd (885, 0) (pAdd (502, 0) (pAdd (882, 0) (pAdd (173, 0)
         (pAdd (881, 0) (pAdd (29, 0) (msCnt 6 [])))))))
     is not definitionally equal to the right-hand side (3763, 0)
     ```

     The chunk counts are summed *by Lean*, so the total cannot be asserted independently
     of the chunks.

  5. **The `LayerOK` defeq hole, and why node counts close it.**  Both of these were
     compiled in one file:

     ```
     theorem hole4  : Delta4Assembly.LayerOK 4      := l3_layer   -- ACCEPTED
     theorem hole4b : msCnt 4 (msGen 4) = (14, 0)   := l3_count   -- REJECTED
     ```

     The first typechecks, reproducing `AssemblyLayers.lean`'s warning: a layer-3 proof is
     defeq-accepted as a layer-4 proof, because `LayerOK n` is a closed decidable
     proposition that reduces to `true = true`.  The second fails:

     ```
     error: Type mismatch: l3_count has type msCnt 3 (msGen 3) = (1, 0)
            but is expected to have type msCnt 4 (msGen 4) = (14, 0)
     ```

     A mislabelled generated file is therefore caught *by arithmetic* the moment its
     assertions carry node counts, and only then.  Same with `l6_count` offered as
     `msCnt 5 (msGen 5) = (92, 0)`: rejected.

## K.  Measurements — 2026-09-19, 10-core / 16 GB, Lean 4.28.0

  `/usr/bin/time -l lake env lean <file>`.  Baseline — imports plus every definition and
  proof of §A–§F, no `decide +kernel` — is **1.9 s, 3.07 GB**.

  | what | nodes | wall | peak RSS | ms/node | MB/node |
  |---|---|---|---|---|---|
  | one mask, `searchPCnt 6 15516465`      |    53 |  2.0 s | 3.11 GB | 0.4 | 0.7 |
  | one mask, `searchPCnt 6 13419315`      |   881 |  4.6 s | 3.73 GB | 3.0 | 0.75 |
  | 21 masks, `msCnt 6 ((msGen 6).drop 200).take 21` | 2,025 |  9.8 s | 5.84 GB | 3.9 | 1.37 |
  | **this whole file**: 17 kernel evaluations + assembly | 3,764 + 872 + 12 | 18.5 s | 5.13 GB | — | — |

  Three things follow, and they are what a generator for the full census needs.

  * **A pruned node costs ~5× a prune-free node.**  `Chunk.lean` §D measures 0.6 ms and
    0.34 MB per node for `goNP`; the pruned traversal is 3–4 ms and 0.75–1.4 MB, because
    `pruneOK` recomputes `e22`, `rem22`, `touched` and `fixedSlack` from scratch at every
    node.  The prune still wins by 229× on node count (2,685,792 against ~6.1·10⁸), so the
    census goes from ~102 h to **≈2.2 h** of kernel time — but the per-node constant is
    where the next optimisation is, and `Prune.lean` §"Not yet done" already names it
    (carry `e22` and `deg` as accumulators, tabulate `rem22`/`touched` per `(n, K)`).
  * **The chunk ceiling is ~900 nodes, not 5,000.**  Memory per node grows with chunk size
    (0.75 → 1.37 MB between 881 and 2,025 nodes), so a 5,000-node declaration would sit at
    ~10 GB and page.  Every chunk in §G/§H is ≤ 885 nodes, and the whole file peaks at
    5.13 GB — barely above its largest single declaration, confirming again that memory
    does not accumulate across declarations.  At that ceiling the census needs **≈3,000
    generated declarations**.
  * **The literal frontier is what makes the chunks cheap.**  Every chunk statement here
    names `F6` or `M6`, so the kernel walks a cons-list of numerals; the expansion itself
    is evaluated exactly once, in `F6_eq`.  Stating chunks against `expandP …` instead
    would re-run the expansion inside every one of those ~3,000 declarations, and
    `@[irreducible]` does not prevent it — the kernel ignores the attribute.  Keep it on
    the literals anyway: it is what makes control 1 above a type mismatch rather than a
    timeout.
-/

/-! ### Axiom audit -/













end Delta4Chunk
