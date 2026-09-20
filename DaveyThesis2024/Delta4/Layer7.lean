import DaveyThesis2024.Delta4.ChunkP

/-!
# Δ = 4, layer 7: a whole layer closed by hand, through the outer `msCnt` layer

`Delta4/ChunkP.lean` §H closes layer 6 (221 masks, 3,764 nodes, every mask light) and
a standalone spike closes one *heavy* mask of layer 9 to
`searchPCnt 9 K = (115553, 0)`.  Neither carries a heavy mask through the **outer** layer.
This file does: layer 7 — **249 masks, 28,957 nodes, 0 violations** — reaching
`Delta4Assembly.LayerOK 7`, with three heavy masks cut at a frontier and bridged into the
mask-slice chain.

Nothing is redefined.  `expandP`, `goAllP(Cnt)`, the peel lemmas, `msCnt`, `msCnt_peel`,
`msCnt_nil` and `layerOK_of_msCnt` are `Delta4Chunk`'s, used verbatim.  No `native_decide`,
no axiom, no `sorry`.

## The shape of layer 7

Layer 7 is the first layer with masks above the ~3,000-node chunk ceiling.  Its profile,
from an independent Python twin of `goGCnt pruneOK leafOK` (which reproduces the census
anchors 1 / 14 / 92 / 3,764 / 28,957 for layers 3–7 and the `msGen` lengths 1 / 14 / 92 /
221 / 249):

* **three heavy masks**, at indices 60, 133 and 209 of `msGen 7`, **3,120 nodes each**;
* 246 light masks, 19,597 nodes, the largest 1,996.

The three heavy masks have *identical* frontier profiles, so one literal `F7` serves all
three — but each is tied to its own mask by its own kernel-checked `expandP` equation.

The cut is at depth **3** of the 21-pair traversal: the shallowest depth at which every
subtree fits a declaration (depth 2 leaves a 3,118-node subtree; depth 3 gives **2 states**
with 1,564 and 1,553 nodes, above 3 internal nodes).

## THE SEAM, and what it costs

The hop this file exists to run is

```
  searchPCnt 7 K = (3120, 0)        ⟶        msCnt 7 ((M7.drop 60).take 1) = (3120, 0)
```

It is **not** a one-liner as ChunkP's `msCnt_peel`/`msCnt_nil` stand.  Two things are
missing, and both are supplied here.

1. **`msCnt_singleton`** — `msCnt n [K] = searchPCnt n K`.  `ChunkP` has `msCnt_append`,
   `msCnt_peel` and `msCnt_nil`, but nothing that evaluates a one-element mask list, and
   `msCnt_peel` cannot produce one: it only ever splits `Ks.drop a`.  Three lines, no
   traversal.  **This belongs in `ChunkP` §F.**

2. **The mask-list lookup has to lift the seal.**  `(M7.drop 60).take 1 = [K7a]` is a
   `List Nat` equation, and `decide +kernel` *fails* on it while `M7` is `@[irreducible]`:

   ```
   error: Tactic `decide` failed for proposition
     List.take 1 (List.drop 60 M7) = [K7a]
   because its `Decidable` instance
     instDecidableEqList (List.take 1 (List.drop 60 M7)) [K7a]
   did not reduce to `isTrue` or `isFalse`.
   ```

   This is a *new* trap, not the one ChunkP documents.  ChunkP's warning is that the kernel
   **ignores** `@[irreducible]`; true, but `decide +kernel` still asks the **elaborator** to
   reduce the `Decidable` instance first, and there `@[irreducible]` bites.  It does not bite
   on the `msCnt … = (N, 0)` chunk statements (their instance is `Nat`/`Prod` equality and
   reduces), which is why ChunkP never met it.  The fix is one token — `unseal M7 in` on
   exactly the lookup declarations — and it is scoped, so `M7` stays sealed everywhere the
   negative controls need it.  (`with_unfolding_all decide` also works; `unseal … in
   decide +kernel` is kept because it is the single-kernel-evaluation route.)

With those two, each heavy mask's hop is three lines and re-runs nothing.

## Layout

249 masks in **14** `msCnt` slices — 11 light batches of ≤ 2,600 nodes and the three heavy
masks as `take 1` slices — plus 6 frontier chunks, 3 `expandP` equations, 3 internal counts
and the assembly.  The light batches never straddle a heavy mask, so the offsets chain
`a ↦ a + b` across the whole of `M7` with no gap.

## Negative controls on the seam

Built and compiled, with `sorry`/`axiom` standing in for the expensive `decide +kernel`
bodies so that only the structural failure is observed.  All three FAIL.

1. **The seam claiming a count the mask fact does not carry** (`(3119, 0)`):

   ```
   error: Type mismatch
     f7a_mask_count has type searchPCnt 7 K7a = (3120, 0)
     but is expected to have type searchPCnt 7 K7a = (3119, 0)
   ```

2. **Mask b's seam wired to mask a's count**:

   ```
   error: Type mismatch
     f7a_mask_count has type searchPCnt 7 K7a = (3120, 0)
     but is expected to have type searchPCnt 7 K7b = (3120, 0)
   ```

   This control is why `K7a`/`K7b`/`K7c` are `@[irreducible]`.  With them as plain `def`s
   the control still fails, but as a `(deterministic) timeout at whnf` — the unifier tries to
   evaluate `searchPCnt 7 K7a =?= searchPCnt 7 K7b`.  A generator must not have to read a
   timeout as a mistake, so seal the mask constants exactly as the list literals are sealed.

3. **The seam aimed at the wrong offset** (lookup for 60, claim for 61):

   ```
   error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
     List.take 1 (List.drop 60 M7)
   in the target expression
     msCnt 7 (List.take 1 (List.drop 61 M7)) = (3120, 0)
   ```

`ChunkP` §J's four controls (dropped frontier chunk, dropped mask slice, early residual,
wrong total) apply to this file unchanged; they are not repeated here.

## Measurements — 2026-09-19, 10-core / 16 GB, Lean 4.28.0

`/usr/bin/time -l lake env lean layer7.lean`: **78.4 s wall, 5.52 GB peak RSS**, 46
declarations, 28,957 nodes, standard kernel axioms only (`propext`, `Classical.choice`,
`Quot.sound`).  That is 2.7 ms/node, matching `spike9`'s figure at a shallower cut, and it
says a whole layer of this size fits comfortably in one module.
-/

namespace Layer7
open Delta4Model Delta4Chunk

/-! ## 0.  The lemma `ChunkP` lacks -/

/-- **Missing from `ChunkP` §F.**  A one-mask slice is that mask's own count.  This is the
    whole algebraic content of the last hop: `msCnt_peel` hands out `(Ks.drop a).take b`
    slices, and with `b = 1` there is nothing in `ChunkP` that turns such a slice back into
    the per-mask fact a frontier cut produces.

    It now also lives in `ChunkP` as `Delta4Chunk.msCnt_singleton`; this local copy is kept so
    the file records what closing a layer actually required. -/
theorem msCnt_singleton (n K : Nat) : msCnt n [K] = searchPCnt n K := by
  show pAdd (searchPCnt n K) (msCnt n []) = searchPCnt n K
  show ((searchPCnt n K).1 + 0, (searchPCnt n K).2 + 0) = searchPCnt n K
  rw [Nat.add_zero, Nat.add_zero]

/-! ## 1.  The mask list of layer 7 -/

/-- The 249 mask words of layer 7, as a literal — `irreducible` for the same reason as
    `ChunkP.M6`: a mis-chained peel is then a type mismatch, not a `whnf` timeout. -/
@[irreducible] def M7 : List Nat :=
  [250355985, 250233105, 250110225, 248144145, 265036305, 249307665, 248263185, 266879505,
   250167825, 264913425, 249184785, 248201745, 250106385, 248140305, 264790545, 249061905,
   248078865, 231367185, 214655505, 248017425, 214594065, 250102545, 248136465, 248013585,
   214590225, 262816785, 247088145, 246043665, 262693905, 246965265, 245982225, 229270545,
   213541905, 245920785, 212497425, 245916945, 212493585, 260597265, 244868625, 229139985,
   213411345, 212428305, 243824145, 212366865, 232530465, 231485985, 265830945, 264847905,
   249119265, 232407585, 231424545, 264786465, 249057825, 248074785, 231363105, 214651425,
   232284705, 231301665, 231240225, 214528545, 214709025, 264782625, 249053985, 248070945,
   231359265, 214647585, 248009505, 214586145, 231236385, 214524705, 214463265, 263734305,
   262751265, 247022625, 230310945, 213599265, 262689825, 246961185, 245978145, 229266465,
   213537825, 261645345, 230188065, 244933665, 229205025, 213476385, 260600865, 244872225,
   229143585, 213414945, 212431905, 245912865, 212489505, 260597025, 244868385, 229139745,
   213411105, 212428065, 243823905, 212366625, 228091425, 211379745, 227046945, 211318305,
   210269985, 248005425, 214582065, 214459185, 262685745, 246957105, 245974065, 229262385,
   213533745, 245912625, 212489265, 260596785, 244868145, 229139505, 213410865, 212427825,
   243823665, 212366385, 243819825, 212362545, 227042865, 211314225, 210269745, 196756545,
   195712065, 196633665, 195650625, 195589185, 178877505, 178935105, 195585345, 178873665,
   178812225, 194537025, 177825345, 193492545, 177763905, 176715585, 178808145, 193488465,
   177759825, 176715345, 160982625, 159938145, 143161185, 232342050, 232280610, 231297570,
   232276770, 231293730, 231232290, 214520610, 261702690, 230245410, 261641250, 230183970,
   244929570, 229200930, 213472290, 228156450, 228095010, 211383330, 260592930, 244864290,
   229135650, 213407010, 212423970, 228091170, 211379490, 227046690, 211318050, 231228210,
   214516530, 214455090, 261637170, 230179890, 244925490, 229196850, 213468210, 260592690,
   244864050, 229135410, 213406770, 212423730, 228090930, 211379250, 227046450, 211317810,
   243815730, 212358450, 227042610, 211313970, 210269490, 196691010, 196629570, 195646530,
   194602050, 194540610, 177828930, 195581250, 178869570, 194536770, 177825090, 193492290,
   177763650, 161048130, 160986690, 159938370, 178804050, 193488210, 177759570, 176715090,
   160982610, 159938130, 143161170, 214450995, 260588595, 244859955, 229131315, 213402675,
   212419635, 243815475, 212358195, 227042355, 211313715, 210269235, 210265395, 196625475,
   195642435, 195580995, 178869315, 194536515, 177824835, 193492035, 177763395, 178804035,
   193488195, 177759555, 176715075, 160982595, 159938115, 143161155, 176710995, 159934035,
   143160915]

theorem M7_eq : msGen 7 = M7 := by decide +kernel

/-! ## 2.  The three heavy masks, cut at depth 3

  All three carry 3,120 nodes and the *same* depth-3 frontier `[0, 37778931867355208220672]`
  — 3 internal nodes above it, subtrees of 1,564 and 1,553.  One literal, three equations. -/

/-- `msGen 7` index 60.  `irreducible`: it makes a seam wired to the wrong mask a crisp
    type mismatch instead of a `whnf` timeout (negative control 2). -/
@[irreducible] def K7a : Nat := 214709025
/-- `msGen 7` index 133.  `irreducible`: it makes a seam wired to the wrong mask a crisp
    type mismatch instead of a `whnf` timeout (negative control 2). -/
@[irreducible] def K7b : Nat := 178935105
/-- `msGen 7` index 209.  `irreducible`: it makes a seam wired to the wrong mask a crisp
    type mismatch instead of a `whnf` timeout (negative control 2). -/
@[irreducible] def K7c : Nat := 161048130

def dep7 : Nat := 3

/-- The undecided pairs shared by every depth-3 frontier state: 18 of the 21. -/
abbrev PS7 : List (Nat × Nat) := (pairList 7).drop dep7

/-- The depth-3 frontier, as a literal `List Nat`.  Shared by the three heavy masks, but
    tied to each of them by its own kernel evaluation below. -/
@[irreducible] def F7 : List Nat := [0, 37778931867355208220672]

theorem F7a_eq : expandP pruneOK 7 K7a dep7 (pairList 7) 0 = F7 := by decide +kernel
theorem F7b_eq : expandP pruneOK 7 K7b dep7 (pairList 7) 0 = F7 := by decide +kernel
theorem F7c_eq : expandP pruneOK 7 K7c dep7 (pairList 7) 0 = F7 := by decide +kernel

theorem F7a_internal : expandPNodes pruneOK 7 K7a dep7 (pairList 7) 0 = 3 := by decide +kernel
theorem F7b_internal : expandPNodes pruneOK 7 K7b dep7 (pairList 7) 0 = 3 := by decide +kernel
theorem F7c_internal : expandPNodes pruneOK 7 K7c dep7 (pairList 7) 0 = 3 := by decide +kernel

theorem F7_residual : F7.drop 2 = [] := by decide +kernel


/-! ### Heavy mask a (`msGen 7` index 60) -/

/-- frontier chunk 0: state [0, 1), 1564 nodes. -/
theorem f7a_chunk_0 :
    goAllPCnt pruneOK leafOK 7 K7a PS7 ((F7.drop 0).take 1) = (1564, 0) := by decide +kernel

/-- frontier chunk 1: state [1, 2), 1553 nodes. -/
theorem f7a_chunk_1 :
    goAllPCnt pruneOK leafOK 7 K7a PS7 ((F7.drop 1).take 1) = (1553, 0) := by decide +kernel

/-- The two chunk counts, chained; nothing is re-traversed. -/
theorem f7a_frontier_count :
    goAllPCnt pruneOK leafOK 7 K7a PS7 (F7.drop 0) = (3117, 0) := by
  rw [goAllPCnt_peel pruneOK leafOK 7 K7a PS7 F7 0 1 1 rfl, f7a_chunk_0,
      goAllPCnt_peel pruneOK leafOK 7 K7a PS7 F7 1 1 2 rfl, f7a_chunk_1,
      F7_residual]
  rfl

/-- The mask's node count, derived: 3 internal nodes plus the two chunks. -/
theorem f7a_mask_count : searchPCnt 7 K7a = (3120, 0) := by
  have hfc : goAllPCnt pruneOK leafOK 7 K7a PS7 (expandP pruneOK 7 K7a dep7 (pairList 7) 0)
      = (3117, 0) := by
    have h := f7a_frontier_count
    rw [List.drop_zero] at h
    rw [F7a_eq]
    exact h
  have h1 := goGCnt_fst_eq pruneOK leafOK 7 K7a dep7 (pairList 7) 0
  have h2 := goGCnt_snd_eq pruneOK leafOK 7 K7a dep7 (pairList 7) 0
  simp only [hfc, F7a_internal] at h1 h2
  exact Prod.ext h1 h2

-- The mask-list lookup: `unseal` is needed, see the seam note in the header.
unseal M7 in
theorem M7_at_60 : (M7.drop 60).take 1 = [K7a] := by decide +kernel

/-- **THE SEAM.**  Per-mask fact in, mask-slice fact out. -/
theorem l7_slice_60 : msCnt 7 ((M7.drop 60).take 1) = (3120, 0) := by
  rw [M7_at_60, msCnt_singleton]
  exact f7a_mask_count


/-! ### Heavy mask b (`msGen 7` index 133) -/

/-- frontier chunk 0: state [0, 1), 1564 nodes. -/
theorem f7b_chunk_0 :
    goAllPCnt pruneOK leafOK 7 K7b PS7 ((F7.drop 0).take 1) = (1564, 0) := by decide +kernel

/-- frontier chunk 1: state [1, 2), 1553 nodes. -/
theorem f7b_chunk_1 :
    goAllPCnt pruneOK leafOK 7 K7b PS7 ((F7.drop 1).take 1) = (1553, 0) := by decide +kernel

/-- The two chunk counts, chained; nothing is re-traversed. -/
theorem f7b_frontier_count :
    goAllPCnt pruneOK leafOK 7 K7b PS7 (F7.drop 0) = (3117, 0) := by
  rw [goAllPCnt_peel pruneOK leafOK 7 K7b PS7 F7 0 1 1 rfl, f7b_chunk_0,
      goAllPCnt_peel pruneOK leafOK 7 K7b PS7 F7 1 1 2 rfl, f7b_chunk_1,
      F7_residual]
  rfl

/-- The mask's node count, derived: 3 internal nodes plus the two chunks. -/
theorem f7b_mask_count : searchPCnt 7 K7b = (3120, 0) := by
  have hfc : goAllPCnt pruneOK leafOK 7 K7b PS7 (expandP pruneOK 7 K7b dep7 (pairList 7) 0)
      = (3117, 0) := by
    have h := f7b_frontier_count
    rw [List.drop_zero] at h
    rw [F7b_eq]
    exact h
  have h1 := goGCnt_fst_eq pruneOK leafOK 7 K7b dep7 (pairList 7) 0
  have h2 := goGCnt_snd_eq pruneOK leafOK 7 K7b dep7 (pairList 7) 0
  simp only [hfc, F7b_internal] at h1 h2
  exact Prod.ext h1 h2

-- The mask-list lookup: `unseal` is needed, see the seam note in the header.
unseal M7 in
theorem M7_at_133 : (M7.drop 133).take 1 = [K7b] := by decide +kernel

/-- **THE SEAM.**  Per-mask fact in, mask-slice fact out. -/
theorem l7_slice_133 : msCnt 7 ((M7.drop 133).take 1) = (3120, 0) := by
  rw [M7_at_133, msCnt_singleton]
  exact f7b_mask_count


/-! ### Heavy mask c (`msGen 7` index 209) -/

/-- frontier chunk 0: state [0, 1), 1564 nodes. -/
theorem f7c_chunk_0 :
    goAllPCnt pruneOK leafOK 7 K7c PS7 ((F7.drop 0).take 1) = (1564, 0) := by decide +kernel

/-- frontier chunk 1: state [1, 2), 1553 nodes. -/
theorem f7c_chunk_1 :
    goAllPCnt pruneOK leafOK 7 K7c PS7 ((F7.drop 1).take 1) = (1553, 0) := by decide +kernel

/-- The two chunk counts, chained; nothing is re-traversed. -/
theorem f7c_frontier_count :
    goAllPCnt pruneOK leafOK 7 K7c PS7 (F7.drop 0) = (3117, 0) := by
  rw [goAllPCnt_peel pruneOK leafOK 7 K7c PS7 F7 0 1 1 rfl, f7c_chunk_0,
      goAllPCnt_peel pruneOK leafOK 7 K7c PS7 F7 1 1 2 rfl, f7c_chunk_1,
      F7_residual]
  rfl

/-- The mask's node count, derived: 3 internal nodes plus the two chunks. -/
theorem f7c_mask_count : searchPCnt 7 K7c = (3120, 0) := by
  have hfc : goAllPCnt pruneOK leafOK 7 K7c PS7 (expandP pruneOK 7 K7c dep7 (pairList 7) 0)
      = (3117, 0) := by
    have h := f7c_frontier_count
    rw [List.drop_zero] at h
    rw [F7c_eq]
    exact h
  have h1 := goGCnt_fst_eq pruneOK leafOK 7 K7c dep7 (pairList 7) 0
  have h2 := goGCnt_snd_eq pruneOK leafOK 7 K7c dep7 (pairList 7) 0
  simp only [hfc, F7c_internal] at h1 h2
  exact Prod.ext h1 h2

-- The mask-list lookup: `unseal` is needed, see the seam note in the header.
unseal M7 in
theorem M7_at_209 : (M7.drop 209).take 1 = [K7c] := by decide +kernel

/-- **THE SEAM.**  Per-mask fact in, mask-slice fact out. -/
theorem l7_slice_209 : msCnt 7 ((M7.drop 209).take 1) = (3120, 0) := by
  rw [M7_at_209, msCnt_singleton]
  exact f7c_mask_count


/-! ## 3.  The light masks, in 11 batches of ≤ 2,600 nodes -/


/-- layer-7 slice: masks [0, 60), 380 nodes. -/
theorem l7_light_0 : msCnt 7 ((M7.drop 0).take 60) = (380, 0) := by decide +kernel


/-- layer-7 slice: masks [61, 107), 2017 nodes. -/
theorem l7_light_1 : msCnt 7 ((M7.drop 61).take 46) = (2017, 0) := by decide +kernel


/-- layer-7 slice: masks [107, 133), 1496 nodes. -/
theorem l7_light_2 : msCnt 7 ((M7.drop 107).take 26) = (1496, 0) := by decide +kernel


/-- layer-7 slice: masks [134, 146), 1790 nodes. -/
theorem l7_light_3 : msCnt 7 ((M7.drop 134).take 12) = (1790, 0) := by decide +kernel


/-- layer-7 slice: masks [146, 176), 2175 nodes. -/
theorem l7_light_4 : msCnt 7 ((M7.drop 146).take 30) = (2175, 0) := by decide +kernel


/-- layer-7 slice: masks [176, 209), 2593 nodes. -/
theorem l7_light_5 : msCnt 7 ((M7.drop 176).take 33) = (2593, 0) := by decide +kernel


/-- layer-7 slice: masks [210, 216), 2057 nodes. -/
theorem l7_light_6 : msCnt 7 ((M7.drop 210).take 6) = (2057, 0) := by decide +kernel


/-- layer-7 slice: masks [216, 219), 792 nodes. -/
theorem l7_light_7 : msCnt 7 ((M7.drop 216).take 3) = (792, 0) := by decide +kernel


/-- layer-7 slice: masks [219, 230), 2550 nodes. -/
theorem l7_light_8 : msCnt 7 ((M7.drop 219).take 11) = (2550, 0) := by decide +kernel


/-- layer-7 slice: masks [230, 243), 1828 nodes. -/
theorem l7_light_9 : msCnt 7 ((M7.drop 230).take 13) = (1828, 0) := by decide +kernel


/-- layer-7 slice: masks [243, 249), 1919 nodes. -/
theorem l7_light_10 : msCnt 7 ((M7.drop 243).take 6) = (1919, 0) := by decide +kernel


theorem M7_residual : M7.drop 249 = [] := by decide +kernel

/-! ## 4.  The layer, chained

  14 slices, offsets chaining `a ↦ a + b` from 0 to 249.  The three heavy slices enter as
  `take 1` facts derived from the frontier cuts; nothing below re-runs a traversal. -/

theorem l7_count : msCnt 7 M7 = (28957, 0) := by
  rw [← List.drop_zero (l := M7),
      msCnt_peel 7 M7 0 60 60 rfl, l7_light_0,
      msCnt_peel 7 M7 60 1 61 rfl, l7_slice_60,
      msCnt_peel 7 M7 61 46 107 rfl, l7_light_1,
      msCnt_peel 7 M7 107 26 133 rfl, l7_light_2,
      msCnt_peel 7 M7 133 1 134 rfl, l7_slice_133,
      msCnt_peel 7 M7 134 12 146 rfl, l7_light_3,
      msCnt_peel 7 M7 146 30 176 rfl, l7_light_4,
      msCnt_peel 7 M7 176 33 209 rfl, l7_light_5,
      msCnt_peel 7 M7 209 1 210 rfl, l7_slice_209,
      msCnt_peel 7 M7 210 6 216 rfl, l7_light_6,
      msCnt_peel 7 M7 216 3 219 rfl, l7_light_7,
      msCnt_peel 7 M7 219 11 230 rfl, l7_light_8,
      msCnt_peel 7 M7 230 13 243 rfl, l7_light_9,
      msCnt_peel 7 M7 243 6 249 rfl, l7_light_10,
      M7_residual]
  rfl

/-- **THE DELIVERABLE.**  Layer 7 of `checkAll`, in the shape
    `AssemblyLayers.checkAll_of_layers` consumes — and asserted through a node count, so it
    is not the defeq-transferable `LayerOK` on its own. -/
theorem l7_layer : Delta4Assembly.LayerOK 7 := by
  refine layerOK_of_msCnt (N := 28957) ?_
  rw [M7_eq]
  exact l7_count

/-! ### Axiom audit -/













end Layer7
