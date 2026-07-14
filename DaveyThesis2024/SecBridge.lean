import DaveyThesis2024.SecCertificate
import DaveyThesis2024.SecBasis
import DaveyThesis2024.LocalFlagAlgebra
import DaveyThesis2024.CG22
import DaveyThesis2024.CGraph22Bridge
import DaveyThesis2024.StrongEdgeColouring

/-!
# SecBridge — algebra-level objective + axioms for the size-5 general SEC SDP

**Status (Phase S3.A–D REDO with CG22, 2026-05-14):** the previous S3.A–D
attempt (commit `5fa06d9`, reverted in `173c00e`) used `CG2` with a
placeholder `flagBasis_sec` — structurally wrong because SEC's flag basis
is (2,2)-coloured (vertex colours **and** edge colours, both `Fin 2`). This
redo builds the bridge properly over the `CG22` `RelUniverse` (commits
`d35a282`, `13f6bb4`) with the **real** flag basis from
`DaveyThesis2024.SecBasis.flagBasis_sec` (17,950 entries, concrete
hex-decoded; emitted in commit `4ae864e`).

**Status (B1 repair, Phase L4 — 2026-07-11):** the original F-free chain
(`secGenGraphClass`, `colouredGraph22OfVertex`, `sec_seq_to_genFlag`, the
old `phi_evalAlg_O_sec_alg_eq_target_sum`, the false axiom
`sec_combinatorial_identity_step1`, the old bound/locality axioms and the
`sec_density_bridge_strong`/`sec_sdp_limit_bound_via_bridge` consumers) has
been **retired**. It applied the SDP identity to all of `L(G)²`, which is
`K_{3,3}`-refutable (the false identity — see the B1 incident record). The
surviving objective objects (`secGenDelta`, `secBasisSize`, `targetArr`,
`O_sec_coef`, `O_sec_alg`) are class-independent and are reused verbatim by
the F-faithful replacement below.

## What this file provides

* `secGenDelta : GenGraphParam CG22` — the SEC degree parameter, defined as
  the max degree of the underlying simple graph. Analog of `brrbGenDelta`.
* `O_sec_coef k : ℝ` — the sign-flipped cert coefficient
  `-(target[k] / linearScale)`. SEC SDPAs use the `min -(...)` objective,
  so we flip to recover the true non-negative SEC flag coefficient.
* `O_sec_alg : GenFlagAlg CG22 (GenFlagType.empty CG22)` — the
  algebra-level SEC objective `Σ_k O_sec_coef k • single (flagBasis_sec k)`.
* **§8 (F-faithful)** — `secGenGraphClassF`, `colouredGraph22OfEdgeF`,
  `SecFSeqItem`/`secF_seq_to_genFlag`, `strongFDegree`,
  `fEdgesInNeighbourhood`, `phi_evalAlg_O_sec_alg_eq_target_sum_F`, the
  restated F-faithful axioms (`sec_combinatorial_identity_F`,
  `phi_evalAlg_O_sec_alg_le_bound_F`, `flagBasis_sec_isLocalFlag_F`) and the
  PROVED `secF_density_bridge`. This is the sound chain that the four
  deterministic SEC headlines route through; it restricts the SDP identity
  to the F-subset `H[F]` (HJK/BPP architecture) rather than all of `L(G)²`.

## What is NOT in this file

* The consumer chain (F-peeling, degeneracy greedy, degree-scale colouring,
  combined bounds, the four headlines) lives in `SecFPeeling.lean`,
  `SecFPadding.lean`, and `StrongChromaticIndex.lean`.
* The bipartite analog (`SecBipartiteBridge.lean`) and the asymmetric
  bipartite chain (`SecAsymmetricBipartiteBridge.lean`). All declarations
  here are for the general (symmetric) SEC SDP only.

## Sign convention

Both SEC SDPAs (general and bipartite) use the SDPA `Minimizing: -(...)`
convention; the cert's `target_str` is the negative of the underlying
SEC flag coefficient. `O_sec_coef` flips this sign so that
`O_sec_coef k = -target[k] / linearScale ≥ 0`, exactly mirroring Pentagon
Q's `O_Q_coef` (see `project_sec_sign_convention.md`).
-/

namespace Davey2024.SecBridge

open Davey2024 SecCertificate SecBasis

open Finset Classical in
noncomputable section

/-! ## §1. SEC graph class + Δ parameter at `CG22` -/

/-- The **SEC degree parameter** at `CG22`: maximum degree of the
underlying simple graph (first component of the `CG22.Str` triple).

SEC analog of `brrbGenDelta : GenGraphParam CG2`. -/
noncomputable def secGenDelta : GenGraphParam CG22 :=
  fun G => Finset.sup Finset.univ (fun v => (Finset.univ.filter (G.str.1.Adj v)).card)

/-! ## §2. Algebra-level objective `O_sec_alg` (S3.A) -/

/-- The number of size-5 flags in the general SEC basis (= 17,950). -/
abbrev secBasisSize : Nat := SecCertificate.numConstraints

/-- The cert's `target` vector cached as an `Array Int` for O(1) indexing.

Wraps `SecCertificate.target : List Int`; computed once to avoid re-parsing
on every basis index lookup. -/
def targetArr : Array Int :=
  (Davey2024.SecCertificate.target).toArray

/-- The ℝ coefficient for SEC basis index `k`.

**Sign convention** (matches Pentagon Q's `O_Q_coef`, see
`project_sec_sign_convention.md`). The general SEC SDPA file
`certificates/strong_edge_colouring.sdpa` uses the `min -(...)` objective:

```
Minimizing: -(2·[|Σ F·ext({2,id2},0)|] + [|Σ F·ext({2,id1},0)|])
```

so SDPA's `c` vector represents the negative of the actual SEC flag
coefficients. The Python emitter `local-flags-certificates/emit_lean_cert.py`
writes `target_int = c_rat · DENOM_Y` with no sign flip; hence
`targetArr[k] ≤ 0` for every basis index `k`. `O_sec_coef` flips this
sign so it represents the TRUE non-negative SEC flag coefficient at basis
index `k`:

```
O_sec_coef k = -target[k] / linearScale ≥ 0
```

(`linearScale = 10^12` is the rationalisation precision used by the
emitter.)

This sign flip makes the combinatorial identity
`edgesInNbhd / C(Δ,2) = (1/16) · Σ_k O_sec_coef k · density(flagBasis_sec k)`
sign-consistent: LHS ≥ 0 (count / count), RHS ≥ 0 (both factors
non-negative). -/
noncomputable def O_sec_coef (k : Fin secBasisSize) : ℝ :=
  -((targetArr[k.val]! : ℝ) /
    (Davey2024.SecCertificate.linearScale : ℝ))

/-- **Algebra-level SEC objective.**

`O_sec_alg = Σ_{k=0}^{17949}  O_sec_coef k • GenFlagAlg.single (flagBasis_sec k)`,
where `O_sec_coef k = -target[k] / linearScale ≥ 0` is the TRUE
(non-negative) SEC flag coefficient at basis index `k` (see `O_sec_coef`
docstring for the SDPA `min -(...)` sign-convention rationale).

The 17,950-term `Finset.sum` is symbolic (`noncomputable`); it does not
unfold during elaboration. Pentagon Q's analogue (`O_Q_alg`) has 9295
terms; SEC is ~2× larger but the structure is identical. -/
noncomputable def O_sec_alg : GenFlagAlg CG22 (GenFlagType.empty CG22) :=
  (Finset.univ : Finset (Fin secBasisSize)).sum
    (fun k => O_sec_coef k • GenFlagAlg.single (SecBasis.flagBasis_sec k))

/-! ## §8. F-faithful constructions (B1 repair, Phase L1 — 2026-07-11)

Everything below implements Phase L1.1 of the development notes: the
F-faithful chain that replaced the retired F-free constructions
(`colouredGraph22OfVertex` / `sec_seq_to_genFlag` / `secGenGraphClass`,
deleted in Phase L4.2), which encoded the SEC reduction WITHOUT the
HJK/BPP F-subset structure (the root cause of the third axiom-inconsistency
incident — the retired `sec_combinatorial_identity_step1` was
`K_{3,3}`-refutable; see the plan's §0 item 4).

**Colour polarity** (pinned table, plan §5 L1.2 — BASIS convention,
opposite of the pentagon bridge for vertices):
* vertex colour **0** = black = X = the strong-neighbourhood set
  `N(u) ∪ N(w)` of the designated edge `{u, w}` (≤ 2Δ vertices);
  vertex colour 1 = red = Y = everything else.
* edge colour **1** = F-edge; edge colour 0 = non-F edge (and non-edges). -/

/-- `IsFEdge G F a b`: the pair `{a, b}` is an edge of `G` designated as
an **F-edge** by `F`, where `F` is a vertex set of `L(G)²` (vertices of
`lineGraphSqFlag G` are canonical edges of `G` via
`(edgeFinset G).equivFin`). Symmetric in `a, b` by construction. -/
def IsFEdge (G : Flag emptyType) (F : Finset (Fin (lineGraphSqFlag G).size))
    (a b : Fin G.size) : Prop :=
  ∃ i ∈ F, ((edgeFinset G).equivFin.symm i).val = (a, b) ∨
           ((edgeFinset G).equivFin.symm i).val = (b, a)

/-- `IsFEdge` is symmetric. -/
theorem isFEdge_comm (G : Flag emptyType)
    (F : Finset (Fin (lineGraphSqFlag G).size)) (a b : Fin G.size) :
    IsFEdge G F a b ↔ IsFEdge G F b a := by
  constructor
  · rintro ⟨i, hi, h | h⟩
    · exact ⟨i, hi, Or.inr h⟩
    · exact ⟨i, hi, Or.inl h⟩
  · rintro ⟨i, hi, h | h⟩
    · exact ⟨i, hi, Or.inr h⟩
    · exact ⟨i, hi, Or.inl h⟩

/-- F-edges are edges. -/
theorem IsFEdge.adj {G : Flag emptyType}
    {F : Finset (Fin (lineGraphSqFlag G).size)} {a b : Fin G.size}
    (h : IsFEdge G F a b) : G.graph.Adj a b := by
  obtain ⟨i, _, hi | hi⟩ := h
  · have hadj : G.graph.Adj ((edgeFinset G).equivFin.symm i).val.1
        ((edgeFinset G).equivFin.symm i).val.2 :=
      (Finset.mem_filter.mp ((edgeFinset G).equivFin.symm i).property).2.1
    rw [hi] at hadj
    exact hadj
  · have hadj : G.graph.Adj ((edgeFinset G).equivFin.symm i).val.1
        ((edgeFinset G).equivFin.symm i).val.2 :=
      (Finset.mem_filter.mp ((edgeFinset G).equivFin.symm i).property).2.1
    rw [hi] at hadj
    exact hadj.symm

open Classical in
/-- **F-faithful (2,2)-coloured host** for the SEC reduction
(thesis §4.3 Figure 4.2), replacing the F-free `colouredGraph22OfVertex`.

Given a graph `G`, an F-set `F` (as vertices of `L(G)²`), and the two
endpoints `u, w` of a designated edge:
* vertex colour **0** (black/X) on the strong neighbourhood
  `N(u) ∪ N(w)`, vertex colour 1 (red/Y) elsewhere;
* edge colour **1** exactly on F-edges, 0 elsewhere.

Polarity per the pinned table (plan §5 L1.2): this matches the Rust
generator (`strong_edge_colouring.rs`: X = 0 = strong-neighbourhood
set; raw edge value 1 = F_EDGE) and the basis projection
(`SecBasis.lean` `extractVertexCol22` identity / `extractEdgeCol22`
raw-1 ↦ 1). It is the OPPOSITE vertex polarity of the pentagon bridge
(`[[feedback_colour_convention]]`: pentagon black = 1) — do not "fix"
this back. -/
noncomputable def colouredGraph22OfEdgeF (G : Flag emptyType)
    (F : Finset (Fin (lineGraphSqFlag G).size)) (u w : Fin G.size) :
    ColouredGraph22 where
  graph := G
  vertexColour := fun x =>
    if G.graph.Adj u x ∨ G.graph.Adj w x then 0 else 1
  edgeColour := fun a b =>
    if IsFEdge G F a b then 1 else 0
  edgeSymm := fun a b => by
    by_cases h : IsFEdge G F a b
    · rw [if_pos h, if_pos ((isFEdge_comm G F a b).mp h)]
    · rw [if_neg h, if_neg (fun h' => h ((isFEdge_comm G F a b).mpr h'))]

/-- The vertex colour of `colouredGraph22OfEdgeF` is `0` (black/X)
exactly on `N(u) ∪ N(w)`. -/
theorem colouredGraph22OfEdgeF_vertexColour_eq_zero_iff
    (G : Flag emptyType) (F : Finset (Fin (lineGraphSqFlag G).size))
    (u w : Fin G.size) (x : Fin G.size) :
    (colouredGraph22OfEdgeF G F u w).vertexColour x = 0 ↔
      (G.graph.Adj u x ∨ G.graph.Adj w x) := by
  unfold colouredGraph22OfEdgeF
  by_cases h : G.graph.Adj u x ∨ G.graph.Adj w x <;> simp [h]

/-- The edge colour of `colouredGraph22OfEdgeF` is `1` exactly on
F-edges. -/
theorem colouredGraph22OfEdgeF_edgeColour_eq_one_iff
    (G : Flag emptyType) (F : Finset (Fin (lineGraphSqFlag G).size))
    (u w : Fin G.size) (a b : Fin G.size) :
    (colouredGraph22OfEdgeF G F u w).edgeColour a b = 1 ↔ IsFEdge G F a b := by
  unfold colouredGraph22OfEdgeF
  by_cases h : IsFEdge G F a b <;> simp [h]

/-- **Per-`k` datum of an F-faithful SEC sequence** (the shape the Phase
L2 restated axioms quantify over): a graph `G`, an F-set `F` of
`L(G)²`-vertices, and a designated vertex `v ∈ F`.

The membership field `hv` structurally excludes the `F = ∅` trivial
witness (the Hurley-incident trap, plan L2 gate (c)): every item's
F-set is nonempty and its designated vertex is an F-edge. -/
structure SecFSeqItem where
  /-- The underlying graph `G_k`. -/
  G : Flag emptyType
  /-- The F-set `F_k`, as a set of vertices of `L(G)²` (= edges of `G`). -/
  F : Finset (Fin (lineGraphSqFlag G).size)
  /-- The designated `L(G)²`-vertex `v_k` (an edge of `G`). -/
  v : Fin (lineGraphSqFlag G).size
  /-- The designated vertex is an F-edge. -/
  hv : v ∈ F

/-- The designated edge of an item, as a canonical (`u < w`) vertex pair
of `G`. -/
noncomputable def SecFSeqItem.designatedEdge (it : SecFSeqItem) :
    Fin it.G.size × Fin it.G.size :=
  ((edgeFinset it.G).equivFin.symm it.v).val

/-- The F-faithful (2,2)-coloured host of an item: `colouredGraph22OfEdgeF`
at the item's designated edge. Replaces `sec_seq_to_colouredGraph22`
(which coloured only `N(u)` — with the wrong polarity — and had NO
F-edges). -/
noncomputable def SecFSeqItem.toColouredGraph22 (it : SecFSeqItem) :
    ColouredGraph22 :=
  colouredGraph22OfEdgeF it.G it.F it.designatedEdge.1 it.designatedEdge.2

/-- The F-faithful `GenFlag CG22 ∅` of an item. Replaces
`sec_seq_to_genFlag`. -/
noncomputable def SecFSeqItem.toGenFlag (it : SecFSeqItem) :
    GenFlag CG22 (GenFlagType.empty CG22) :=
  it.toColouredGraph22.toGenFlag

/-- **F-faithful sequence → `GenFlag CG22 ∅` bridge** (Phase L2 axioms'
host, analogue of `sec_seq_to_genFlag` over `SecFSeqItem`). -/
noncomputable def secF_seq_to_genFlag (seq : ℕ → SecFSeqItem) (k : ℕ) :
    GenFlag CG22 (GenFlagType.empty CG22) :=
  (seq k).toGenFlag

/-- The `size` of an item's flag is the graph's size. -/
@[simp] theorem SecFSeqItem.toGenFlag_size (it : SecFSeqItem) :
    it.toGenFlag.size = it.G.size := rfl

/-- The `str.1` of an item's flag is the underlying simple graph. -/
theorem SecFSeqItem.toGenFlag_str_graph (it : SecFSeqItem) :
    it.toGenFlag.str.1 = it.G.graph := rfl

/-- `secGenDelta` of an item's flag is `maxDegree it.G`. -/
theorem secGenDelta_SecFSeqItem_toGenFlag (it : SecFSeqItem) :
    secGenDelta it.toGenFlag.forget = maxDegree it.G := rfl

/-- **F-faithful SEC graph class** (replaces `secGenGraphClass`, whose
third clause has both the polarity and the bound wrong — see the pinned
table, plan §5 L1.2). Two clauses:
1. edge-colour symmetry;
2. bounded **black** (= colour-**0**) vertex count ≤ **2·Δ** — the
   strong neighbourhood `N(u) ∪ N(w)` of an edge has at most 2Δ
   vertices (Rust generator's X-set bound).

No F/edge-colour clause: per the pinned table, the F structure lives in
the L2 gate/axiom hypotheses, not in the class. -/
noncomputable def secGenGraphClassF : GenGraphClass CG22 :=
  fun G =>
    let graph := G.str.1
    let vcol  := G.str.2.1
    let ecol  := G.str.2.2
    -- Edge-colour symmetry.
    (∀ u v : Fin G.size, ecol u v = ecol v u) ∧
    -- Bounded black-vertex (colour-0) count: ≤ 2 · max degree.
    (Finset.univ.filter (fun v : Fin G.size => vcol v = 0)).card ≤
      2 * Finset.sup Finset.univ (fun v => (Finset.univ.filter (graph.Adj v)).card)

/-- Every item's flag belongs to `secGenGraphClassF`:
1. edge symmetry from `ColouredGraph22.edgeSymm`;
2. the colour-0 set is `N(u) ∪ N(w)`, of size ≤ deg(u) + deg(w) ≤ 2Δ.

(Dry run of L1 gate (d): membership needs NO regularity — the 2Δ bound
is unconditional, unlike the old class's `= Δ` count which needed
`IsRegular`.) -/
theorem SecFSeqItem.toGenFlag_mem_classF (it : SecFSeqItem) :
    secGenGraphClassF it.toGenFlag.forget := by
  refine ⟨?_, ?_⟩
  · -- Edge-colour symmetry.
    intro a b
    exact it.toColouredGraph22.edgeSymm a b
  · -- Black (colour-0) count ≤ 2Δ.
    have hfil :
        (Finset.univ.filter
          (fun x : Fin it.toGenFlag.forget.size =>
            it.toGenFlag.forget.str.2.1 x = 0)) =
        (Finset.univ.filter
          (fun x : Fin it.G.size =>
            it.G.graph.Adj it.designatedEdge.1 x ∨
            it.G.graph.Adj it.designatedEdge.2 x)) :=
      Finset.filter_congr fun x _ =>
        colouredGraph22OfEdgeF_vertexColour_eq_zero_iff
          it.G it.F it.designatedEdge.1 it.designatedEdge.2 x
    rw [hfil, Finset.filter_or]
    calc ((Finset.univ.filter
            (fun x => it.G.graph.Adj it.designatedEdge.1 x)) ∪
          (Finset.univ.filter
            (fun x => it.G.graph.Adj it.designatedEdge.2 x))).card
        ≤ (Finset.univ.filter
            (fun x => it.G.graph.Adj it.designatedEdge.1 x)).card +
          (Finset.univ.filter
            (fun x => it.G.graph.Adj it.designatedEdge.2 x)).card :=
          Finset.card_union_le _ _
      _ ≤ Finset.sup Finset.univ
            (fun v => (Finset.univ.filter (it.G.graph.Adj v)).card) +
          Finset.sup Finset.univ
            (fun v => (Finset.univ.filter (it.G.graph.Adj v)).card) :=
          add_le_add
            (Finset.le_sup
              (f := fun v => (Finset.univ.filter (it.G.graph.Adj v)).card)
              (Finset.mem_univ it.designatedEdge.1))
            (Finset.le_sup
              (f := fun v => (Finset.univ.filter (it.G.graph.Adj v)).card)
              (Finset.mem_univ it.designatedEdge.2))
      _ = 2 * Finset.sup Finset.univ
            (fun v => (Finset.univ.filter (it.G.graph.Adj v)).card) :=
          (two_mul _).symm

/-! ### §8b. F-degree primitives + F-class functional plumbing (Phase L2 prep)

Definitions and PROVED theorems only. The restated L2 axioms themselves are
drafted for review in the development notes (B1-repair
standing rule: new axiom declarations are review-gated) and are NOT
declared here yet. -/

/-- **Strong F-degree** of an `L(G)²`-vertex `e` (= edge of `G`) with
respect to an F-set `F`: the number of F-elements adjacent to `e` in
`L(G)²`. For `e ∈ F` this is `deg_{H[F]}(e)` in the sense of HJK Thm 3.1
/ thesis `lemma:sec_degree_non_incident` (Lemma 4.3). The L2 gate states
the min-degree hypothesis as the exact-integer inequality
`17297 * Δ(G)² ≤ 10000 * strongFDegree G F e` (2 − η at η = 0.2703,
matching the cert's R3 constraint line in
`local-flags-certificates/certificates/strong_edge_colouring.sdpa`:
`(Σ F - 1.7297*2*ext({2,id2},0)*ext({2,id2},0))*ext({2,id2},0) ≥ 0`). -/
noncomputable def strongFDegree (G : Flag emptyType)
    (F : Finset (Fin (lineGraphSqFlag G).size))
    (e : Fin (lineGraphSqFlag G).size) : ℕ :=
  (F.filter (fun i => (lineGraphSqFlag G).graph.Adj e i)).card

/-- **Within-F neighbourhood edge count** `|E(H[N_{H[F]}(v)])|` for
`H = L(G)²`: the number of pairs `{i, j}` of F-elements that are both
`H`-adjacent to `v` and `H`-adjacent to each other. This is the quantity
HJK Thm 3.1 bounds and the L2 identity axiom's LHS numerator (normalised
at the `C(2Δ², 2)` scale — NOT `C(Δ(L(G)²), 2)`). Shape mirrors
`edgesInNeighbourhood`. -/
noncomputable def fEdgesInNeighbourhood (G : Flag emptyType)
    (F : Finset (Fin (lineGraphSqFlag G).size))
    (v : Fin (lineGraphSqFlag G).size) : ℕ :=
  let nbrs := F.filter (fun i => (lineGraphSqFlag G).graph.Adj v i)
  ((nbrs ×ˢ nbrs).filter
    (fun p => p.1 < p.2 ∧ (lineGraphSqFlag G).graph.Adj p.1 p.2)).card

/-- `secGenDelta` of `secF_seq_to_genFlag` is the underlying max degree. -/
theorem secGenDelta_secF_seq_to_genFlag (seq : ℕ → SecFSeqItem) (k : ℕ) :
    secGenDelta (secF_seq_to_genFlag seq k).forget = maxDegree (seq k).G := rfl

/-- Wrap an F-faithful item sequence as a
`GenDeltaIncreasingSeq CG22 ∅ secGenDelta` (mirror of `sec_toGenDeltaSeq`). -/
noncomputable def secF_toGenDeltaSeq (seq : ℕ → SecFSeqItem)
    (hΔ : StrictMono (fun k => maxDegree (seq k).G)) :
    GenDeltaIncreasingSeq CG22 (GenFlagType.empty CG22) secGenDelta where
  seq k := secF_seq_to_genFlag seq k
  increasing := by
    intro a b hab
    change secGenDelta (secF_seq_to_genFlag seq a).forget <
           secGenDelta (secF_seq_to_genFlag seq b).forget
    rw [secGenDelta_secF_seq_to_genFlag, secGenDelta_secF_seq_to_genFlag]
    exact hΔ hab

/-- **F-faithful phi construction**: build a
`GenLimitFunctional CG22 ∅ secGenGraphClassF secGenDelta` from an
F-faithful item sequence (mirror of `sec_phi_construction` over the new
class). Class membership is unconditional
(`SecFSeqItem.toGenFlag_mem_classF`), so no `IsRegular` argument is
needed here — the cert-side hypotheses (regularity, per-F-edge
min-degree) are carried by the `secPhiRegularF`-style gate of the L2
axioms, not by this construction. -/
noncomputable def secF_phi_construction (seq : ℕ → SecFSeqItem)
    (hΔ : StrictMono (fun k => maxDegree (seq k).G))
    (sub : ℕ → ℕ) (hsub : StrictMono sub) :
    GenLimitFunctional CG22 (GenFlagType.empty CG22)
      secGenGraphClassF secGenDelta := by
  let cseq : ℕ → SecFSeqItem := fun k => seq (sub k)
  have hΔ' : StrictMono (fun k => maxDegree (cseq k).G) := hΔ.comp hsub
  exact genLimit_functional_construction CG22 (GenFlagType.empty CG22)
    secGenGraphClassF secGenDelta
    (secF_toGenDeltaSeq cseq hΔ')
    (fun k => (cseq k).toGenFlag_mem_classF)

/-- **Eval-level basis expansion at the F-faithful class** (new-class copy
of `phi_evalAlg_O_sec_alg_eq_target_sum`; the algebra element `O_sec_alg`
is class-independent, only the functional's class parameter changes). -/
theorem phi_evalAlg_O_sec_alg_eq_target_sum_F
    (phi : GenLimitFunctional CG22 (GenFlagType.empty CG22)
      secGenGraphClassF secGenDelta) :
    phi.evalAlg O_sec_alg
      = (Finset.univ : Finset (Fin secBasisSize)).sum
          (fun k => O_sec_coef k * phi.eval (SecBasis.flagBasis_sec k)) := by
  unfold O_sec_alg
  rw [phi.evalAlg_finset_sum_genFlagAlg]
  apply Finset.sum_congr rfl
  intro k _
  rw [phi.evalAlg_smul, phi.evalAlg_single]

/-! ### §8c. Restated (F-faithful) SEC axioms — Phase L2 (2026-07-11)

Landed after coordinator review of the development notes
(amendments A1: `secIdentityTol = 1/100000`; A2/gate-(d) revision: NO strict
bound axioms — see below). The `_F` suffixes mark L2–L3 coexistence with the
old (known-false / known-vacuous) axioms above, whose consumers are rewired
in Phase L3.4 and which are deleted in Phase L4.2.

**No strict-bound axiom (gate L2(d) finding, 2026-07-11).** The pre-repair
strict constants — general `10.6424 = 10.644 − 16/10000` and bipartite
`4.0922 = 4.093 − 8/10000` — are supported by NO artefact: the thesis records
the solver optimum `10.643189` (rounded UP to the lemma constant 10.644,
`appendices/sdp_verification.tex:89–90`), SCS gives `10.6430`, and
`second_solver_verification.md`'s SDPA-LR figure `10.6444` is an unreconciled
outlier within that document; every recorded optimum exceeds 10.6424 (and
similarly all bipartite optima exceed 4.0922). Both strict axioms are
therefore DROPPED rather than restated: the LOOSE bounds already close the
thesis-tight headlines — general ς = 1 − 10.644/16 = 0.33475 →
2(1−ε(ς)) = 1.72981 < 1.73 (headroom ≈ 1.8×10⁻⁴ after the 10⁻⁵ tolerance);
bipartite ς = 1 − 4.093/8 = 0.488375 → 1.62539 < 1.6255 (headroom
≈ 1.0×10⁻⁴); the max-branch values 1.7297 / 1.6254 also stay under. -/

/-- Tolerance for the F-faithful combinatorial identity axioms: absorbs the
10⁻¹²-scale integerisation of the cert target vectors (residue bounds: crude
≤ 2.2×10⁻⁶, refined ≤ 1.8×10⁻⁹ — full derivation in
the development notes §1.2). Sized at 10⁻⁵ so that the
THESIS-TIGHT headlines survive from the LOOSE bounds: the tight-path
headline cost is ≈ 2·(dε/dς)·tol ≈ 7×10⁻⁶ in the constant, vs tight headroom
≈ 1.9×10⁻⁴ (general 1.73 at λ = 10.644) / ≈ 1.1×10⁻⁴ (bipartite 1.6255 at
λ = 4.093); a tolerance of 10⁻³ would break 1.73 (density 0.66525 + 10⁻³
gives ς = 0.33375, 2(1−ε(ς)) ≈ 1.73052). -/
noncomputable def secIdentityTol : ℝ := 1/100000

/-- A SEC limit functional at the F-faithful class is *regularly
F-constructed* iff it arises from `secF_phi_construction` on an item sequence
satisfying the full cert-side gate: strictly increasing max degree, per-k
regularity, and the per-F-edge min-strong-degree at η = 0.2703. These are
exactly the constraints the SDP cert was generated with (`Degree::regularity`
plus the R3 min-degree constraint, `strong_edge_colouring.rs:161`, emitted as
`[|(Σ F - 1.7297*2*ext({2,id2},0)*ext({2,id2},0))*ext({2,id2},0)|] ≥ 0` in
`certificates/strong_edge_colouring.sdpa`); restricting the bound axioms to
`secPhiRegularF phi` keeps them faithful to the cert's hypotheses. The gates
are conjuncts of the predicate (not construction arguments), so nothing is
discharged by a degenerate construction input; satisfiability: Δ-regular
girth-≥5 graphs with F = E(G) have `strongFDegree = 2Δ(Δ−1)`, which passes
the gate for Δ ≥ 8 (the development notes §5.3). -/
def secPhiRegularF
    (phi : GenLimitFunctional CG22 (GenFlagType.empty CG22)
      secGenGraphClassF secGenDelta) : Prop :=
  ∃ (seq : ℕ → SecFSeqItem)
    (hΔ : StrictMono (fun k => maxDegree (seq k).G))
    (sub : ℕ → ℕ) (hsub : StrictMono sub),
    (∀ k, IsRegular (seq k).G) ∧
    (∀ k, ∀ e ∈ (seq k).F,
      17297 * (maxDegree (seq k).G) ^ 2 ≤
        10000 * strongFDegree (seq k).G (seq k).F e) ∧
    phi = secF_phi_construction seq hΔ sub hsub

/-- **Domain axiom — F-faithful SEC combinatorial identity (asymptotic,
one-sided, toleranced).** Replaces the refuted (retired)
`sec_combinatorial_identity_step1`; the `K_{3,3}` refutation of the old
axiom is recorded in the development notes §0 item 4 (the mechanised
`SecIdentityRefutation.lean` was deleted in L4.2 together with the axiom it
refuted).

## Statement

For every F-faithful item sequence `(G_k, F_k, v_k)` (with `v_k ∈ F_k`
structural, `SecFSeqItem.hv`) that is Δ-strictly-increasing, per-k regular,
and satisfies the per-F-edge min-strong-degree gate `(2−η)Δ² ≤ deg_{H[F]}(e)`
at `η = 0.2703` in exact integers (`17297·Δ² ≤ 10000·strongFDegree`),
eventually in `k`:

    |E(H[N_{H[F_k]}(v_k)])| / C(2Δ_k², 2)
      ≤ (1/16)·Σ_j O_sec_coef j · d_j(G'_k)  +  secIdentityTol,

where `H = L(G_k)²`, `d_j` is the `C(Δ,5)`-normalised unlabelled density of
the j-th basis flag, and `G'_k` is the F-faithful host
(`colouredGraph22OfEdgeF`: black-0 vertices on `N(u) ∪ N(w)`, edge colour 1
exactly on `F_k` — thesis §4.3 Figure 4.2 / `fig:transform`). The `1/16`
factor: `ρ(O;G') ~ 2|E_O|/C(Δ,2)²` (thesis `lemma:sec_objective`) with
`C(Δ,2)² ~ Δ⁴/4` gives `|E_O| ~ ρ·Δ⁴/8`, while `C(2Δ²,2) ~ 2Δ⁴`, so
`|E_O|/C(2Δ²,2) ~ ρ/16` (thesis proof of the SEC bound theorem,
σ = 1 − λ/16); the `secIdentityTol = 10⁻⁵` absorbs the cert target's 10⁻¹²
integerisation.

## Why this axiom is needed

The chain from `|E(H[N_{H[F]}(f)])|` to the flag-density sum decomposes as:
(i) discard `L(G)`-incident pairs — `o(Δ⁴)`, thesis Lemma 4.2
(`lemma:count_non_incident_pairs`, `strong_edge_colouring.tex:159`);
(ii) identify the survivors with `E_O(G')` pairs up to the `≤ 2Δ²` pairs
containing `v_k` — thesis Lemma 4.4 (`lemma:sec_black_edge_degree`, tex:205)
and its Corollary 4.4.1 (`corollary:strong_density_graph_class`, tex:240);
(iii) the E_O-pair ↔ size-5-flag-embedding classification with the cert's
target weights — thesis `lemma:sec_objective` (tex:356),
`ρ(O;G') ~ 2|E_O|/C(Δ,2)²`. Step (iii) at 17,950 classes is the same
cert-arithmetic-infeasible scale as before (~10⁵ LOC; per-k `native_decide`
impossible since the host is abstract); steps (i)–(ii) additionally make any
EXACT finite-k statement false — that exactness was part of the refuted
axiom's falsity — hence the eventual-≤-with-tolerance form. A tolerance-free
`Tendsto` form would also be false: the rounding residue of the integerised
target is a constant-scale offset (the development notes §1.2).

## Why this axiom is correct

1. Thesis Lemmas 4.2/4.3/4.4 + Cor 4.4.1 + `lemma:sec_objective` prove the
   two-sided asymptotic `LHS_k = (1/16)·ρ(O;G'_k) + o(1)` for exactly this
   class of hosts (regular, ≤ 2Δ black vertices, per-F-edge min-degree — the
   gate reproduces the class hypotheses verbatim).
2. The Rust generator enumerates the same size-5 basis and emits
   `target[j] = round(c_j·10¹²)` of the true objective coefficients
   (`emit_lean_cert.py`); the rounding residue is bounded by 2.2×10⁻⁶ (crude)
   / 1.8×10⁻⁹ (refined, derivation in the development notes
   §1.2) ≪ `secIdentityTol = 10⁻⁵`, so the one-sided inequality holds with
   the tolerance.
3. The pentagon peer `pentagonQ_basis_combinatorial_identity_step1`
   (`PentagonQBridge.lean`) packages the same tuple-classification content at
   size 8 where it IS exact (its LHS is an exact tuple count); the SEC
   differences (corrections (i)–(ii), rounding) are precisely what the `∀ᶠ` +
   tolerance weakening accounts for.
4. A0.2/L1 evidence: the objective support (7,794 nonzero targets) consists
   exclusively of ≥2-F-edge flags and the F-faithful host realises them with
   nonzero density (smoke test `SecBridgeSmokeL1.lean`), so both sides are
   non-trivially engaged — the identity is not vacuous. Truth tests
   (the development notes §5): on K_{m,m} the gate is
   unsatisfiable for EVERY F (`strongFDegree ≤ m²−1 < 1.7297·m²`), so the L0
   refutation family lies outside the hypotheses; Δ-regular girth-≥5 graphs
   with F = E(G) satisfy the gate for Δ ≥ 8, so the hypotheses are
   satisfiable. -/
axiom sec_combinatorial_identity_F
    (seq : ℕ → SecFSeqItem)
    (hΔ : StrictMono (fun k => maxDegree (seq k).G))
    (hReg : ∀ k, IsRegular (seq k).G)
    (hFdeg : ∀ k, ∀ e ∈ (seq k).F,
      17297 * (maxDegree (seq k).G) ^ 2 ≤
        10000 * strongFDegree (seq k).G (seq k).F e) :
    ∀ᶠ k in Filter.atTop,
      (fEdgesInNeighbourhood (seq k).G (seq k).F (seq k).v : ℝ) /
          (Nat.choose (2 * (maxDegree (seq k).G) ^ 2) 2 : ℝ) ≤
        (1/16 : ℝ) *
          (Finset.univ : Finset (Fin secBasisSize)).sum
            (fun j => O_sec_coef j *
              genUnlabelledDensity CG22 (GenFlagType.empty CG22)
                (SecBasis.flagBasis_sec j)
                (secF_seq_to_genFlag seq k).forget
                secGenDelta)
        + secIdentityTol

/-- **Domain axiom — SEC eval-level upper bound (F-faithful class, loose).**

## Statement

Every limit functional at the F-faithful class that is regularly
F-constructed (`secPhiRegularF`: built by `secF_phi_construction` from a
Δ-increasing, per-k-regular item sequence satisfying the per-F-edge
min-strong-degree gate at η = 0.2703) satisfies

    phi.evalAlg O_sec_alg ≤ 10.644 = secDensityBound.

`O_sec_alg` is unchanged from the pre-repair bridge (the algebra element is
class-independent); only the functional's class and the provenance gate
change.

## Why this axiom is needed

Unchanged from the pre-repair `phi_evalAlg_O_sec_alg_le_bound`: the per-block
iso table mapping `cls.out.forget → flagBasis_sec k` needed to lift the 39
`native_decide`-verified LDL block witnesses to the eval-level cone
inequality is missing (Phase 1.D spike: the BRRB pattern does not transfer at
≥ 5 flags; the 17,950-class enumeration at hand-coded density is ~10⁵ LOC).

## Why this axiom is correct

1. **Exhaustive constraint discharge (the F-repair's point).** The SDPA
   program (`solve` at `strong_edge_colouring.rs:152–178`) has exactly FIVE
   linear-constraint families beyond the Cauchy–Schwarz blocks; each maps to
   a Lean-side hypothesis:
   * `flag ≥ 0`, 17,950 rows (`flags_are_nonnegative`) — intrinsic to
     `GenLimitFunctional.nonneg_on_flags`.
   * R3 min-degree, 1 row (rs:161; sdpa header comment
     `[|(Σ F − 1.7297·2·ext({2,id2},0)·ext({2,id2},0))·ext({2,id2},0)|] ≥ 0`,
     `eta = 0.2703`) — carried by the `hFdeg` conjunct of `secPhiRegularF`
     via `strongFDegree` (thesis Lemma 4.3, `lemma:sec_degree_non_incident`:
     `ρ(D'(bredge)) ≥ 2(2−η)` for gated sequences).
   * Regularity family (`Degree::regularity`, rs:164–165; the sdpa
     `ext({4,idX}, i) − ext({4,idX}, j) ≥ 0` pairs) — carried by the per-k
     `IsRegular` conjunct (thesis Cor `unlabel_extension` family).
   * Black-vertex ≤ 2Δ encodings (`size_of_x`, rs:111–140): the per-size-4-
     type inequalities `2·ext_t − ext_X(t) ≥ 0` (rs:116–120) AND the
     single-black-vertex density row `(b1·ext^{n−1}) ≤ 2` (rs:136–140) —
     both carried by `secGenGraphClassF`'s vcol-0-count ≤ 2Δ clause (thesis
     `lemma:black_extension_vector` + its corollary `Φ(ext_{B,1}) ≤ 2`).
   * Black-count moment equalities
     `(ext_{B,k} − ext_{B,1}^k)·ext^{n−(k+1)} = 0` for k = 2, 3, 4
     (rs:121–134; sdpa rows 2502–2504) — discharged by asymptotic moment
     factorisation for hosts with DETERMINISTIC black count: the F-faithful
     construction colours exactly `N(u) ∪ N(w)` black, a fixed vertex set
     per host, so the black-count extension moments factorise in the limit
     (thesis corollaries after `lemma:black_extension_vector`,
     `strong_edge_colouring.tex:429–439`: `Φ(ext_{B,i}) = Φ(ext_{B,1})^i`).
2. **SDPA-LR solver's numerical certificate** for exactly this constrained
   program (thesis `appendices/sdp_verification.tex:89–90` records the
   solver optimum `10.643189`, rounded UP to the lemma constant `10.644`);
   dual feasibility `max |tr(F_k Y) − c_k| ~ 10⁻⁸`.
3. **Per-block PSD witnesses.** All 39 blocks ship `native_decide`-verified
   LDL witnesses in `SecCertificate`, plus the slack-budget theorem
   `cert_slack_within_budget` (`secSlackBudget = 2×10²³`, measured ≈ 1.6×
   safety) at the nominal pair `(10644, 1000)`.
4. **Independent artefacts.** `verify_sec_cert.py` (pure-Python re-check of
   all block identities, GREEN); SCS cross-check bracketing 10.6430–10.6464
   (`second_solver_verification.md`; that document's SDPA-LR figure 10.6444
   is an unreconciled outlier within it — noted per gate L2(d)). -/
axiom phi_evalAlg_O_sec_alg_le_bound_F
    (phi : GenLimitFunctional CG22 (GenFlagType.empty CG22)
      secGenGraphClassF secGenDelta)
    (hreg : secPhiRegularF phi) :
    phi.evalAlg O_sec_alg ≤ 10.644

/-- **Domain axiom — SEC basis flag locality (F-faithful class).**

## Statement

Every one of the 17,950 basis flags is a local ∅-flag for the F-faithful
class/degree pair:

    GenIsLocalFlag ∅ (flagBasis_sec k) secGenGraphClassF secGenDelta.

## Why this axiom is needed

Unchanged from the pre-repair `flagBasis_sec_isLocalFlag`: `phi.convergence`
requires per-flag locality; the algorithmic witness extraction (a CG22
vertex-order property + a generic IC bound, ~600–1000 LOC, mirroring Pentagon
Q's proved `flagBasis_isLocalFlag`) is deferred exactly as before.

## Why this axiom is correct

Thesis locality criterion (`strong_edge_colouring.tex:255`): a flag is local
iff every connected component contains a black vertex or a labelled vertex;
the Rust basis enumeration generates exactly the local flags. The class
change (black-vertex count `≤ Δ` → `≤ 2Δ`) only doubles the anchor budget in
the `IC ≤ (2Δ)^c·Δ^(5−c)` bound — bounded density is preserved (the claim is
monotone in the anchor budget). Pentagon Q's proved analog
(`PentagonQBridge.lean:9518`, strong induction on unlabelled size + per-flag
`native_decide` witness) is the structural template. -/
axiom flagBasis_sec_isLocalFlag_F (k : Fin secBasisSize) :
    GenIsLocalFlag (GenFlagType.empty CG22) (SecBasis.flagBasis_sec k)
      secGenGraphClassF secGenDelta

/-! ### §8d. F-faithful density bridge (Phase L3.4(a) — PROVED)

Mirror of `sec_density_bridge_strong` over the F-faithful chain. The
conclusion is the ONE-SIDED toleranced bound (the L2 identity axiom's
shape): any subsequential limit of the within-F density
`fEdgesInNeighbourhood / C(2Δ², 2)` along a gated item sequence is at most
`10.644/16 + secIdentityTol`. -/

/-- **F-faithful SEC density bridge (PROVED).** For a gated item sequence
(Δ-strictly-increasing, per-k regular, per-F-edge min-strong-degree at
η = 0.2703) and any convergent subsequence of the within-F density, the
limit is at most `10.644/16 + secIdentityTol`.

Proof structure (mirrors `sec_density_bridge_strong` Steps 1–8, with
`tendsto_nhds_unique` replaced by `le_of_tendsto_of_tendsto` for the
one-sided identity axiom):
1. `phi := secF_phi_construction seq hΔ sub hsub` (class membership is
   unconditional; the gates feed `secPhiRegularF`).
2. `sec_combinatorial_identity_F` composed along the diagonal
   subsequence (`Tendsto.eventually`).
3. Per-flag density convergence via `phi.convergence` +
   `flagBasis_sec_isLocalFlag_F`; aggregate with `tendsto_finset_sum`.
4. `le_of_tendsto_of_tendsto` + `phi_evalAlg_O_sec_alg_eq_target_sum_F`
   + `phi_evalAlg_O_sec_alg_le_bound_F`. -/
theorem secF_density_bridge
    (seq : ℕ → SecFSeqItem)
    (hΔ : StrictMono (fun k => maxDegree (seq k).G))
    (hReg : ∀ k, IsRegular (seq k).G)
    (hFdeg : ∀ k, ∀ e ∈ (seq k).F,
      17297 * (maxDegree (seq k).G) ^ 2 ≤
        10000 * strongFDegree (seq k).G (seq k).F e)
    (sub : ℕ → ℕ) (L : ℝ) (hsub : StrictMono sub)
    (htend : Filter.Tendsto (fun k =>
      (fEdgesInNeighbourhood (seq (sub k)).G (seq (sub k)).F (seq (sub k)).v : ℝ) /
      (Nat.choose (2 * (maxDegree (seq (sub k)).G) ^ 2) 2 : ℝ))
      Filter.atTop (nhds L)) :
    L ≤ 10.644 / 16 + secIdentityTol := by
  set phi := secF_phi_construction seq hΔ sub hsub with hphi_def
  have hreg : secPhiRegularF phi := ⟨seq, hΔ, sub, hsub, hReg, hFdeg, hphi_def⟩
  -- The composed diagonal index n ↦ sub (phi.sub n).
  set cseq : ℕ → SecFSeqItem := fun k => seq (sub k) with hcseq_def
  -- Step 1: limit of the LHS along the diagonal.
  have htend_diag : Filter.Tendsto (fun n =>
      (fEdgesInNeighbourhood (seq (sub (phi.sub n))).G (seq (sub (phi.sub n))).F
        (seq (sub (phi.sub n))).v : ℝ) /
      (Nat.choose (2 * (maxDegree (seq (sub (phi.sub n))).G) ^ 2) 2 : ℝ))
      Filter.atTop (nhds L) :=
    htend.comp phi.sub_strictMono.tendsto_atTop
  -- Step 2: the identity axiom, composed along the diagonal.
  have hIdent := sec_combinatorial_identity_F seq hΔ hReg hFdeg
  have hcompTop : Filter.Tendsto (fun n => sub (phi.sub n))
      Filter.atTop Filter.atTop :=
    (hsub.comp phi.sub_strictMono).tendsto_atTop
  have hIdent_diag : ∀ᶠ n in Filter.atTop,
      (fEdgesInNeighbourhood (seq (sub (phi.sub n))).G (seq (sub (phi.sub n))).F
        (seq (sub (phi.sub n))).v : ℝ) /
      (Nat.choose (2 * (maxDegree (seq (sub (phi.sub n))).G) ^ 2) 2 : ℝ) ≤
      (1/16 : ℝ) *
        (Finset.univ : Finset (Fin secBasisSize)).sum
          (fun j => O_sec_coef j *
            genUnlabelledDensity CG22 (GenFlagType.empty CG22)
              (SecBasis.flagBasis_sec j)
              (secF_seq_to_genFlag seq (sub (phi.sub n))).forget
              secGenDelta)
      + secIdentityTol :=
    hcompTop.eventually hIdent
  -- Step 3: per-flag density convergence along the diagonal.
  set uD : Fin secBasisSize → ℕ → ℝ := fun j n =>
    genUnlabelledDensity CG22 (GenFlagType.empty CG22)
      (SecBasis.flagBasis_sec j)
      (secF_seq_to_genFlag cseq (phi.sub n)).forget
      secGenDelta with huD_def
  have huD_tend : ∀ j : Fin secBasisSize,
      Filter.Tendsto (uD j) Filter.atTop
        (nhds (phi.eval (SecBasis.flagBasis_sec j))) := by
    intro j
    exact phi.convergence (SecBasis.flagBasis_sec j) (flagBasis_sec_isLocalFlag_F j)
  -- Step 4: aggregate.
  have hSum_tend : Filter.Tendsto
      (fun n => (1/16 : ℝ) *
        (Finset.univ : Finset (Fin secBasisSize)).sum
          (fun j => O_sec_coef j * uD j n) + secIdentityTol)
      Filter.atTop
      (nhds ((1/16 : ℝ) *
        (Finset.univ : Finset (Fin secBasisSize)).sum
          (fun j => O_sec_coef j * phi.eval (SecBasis.flagBasis_sec j))
        + secIdentityTol)) := by
    apply Filter.Tendsto.add_const
    apply Filter.Tendsto.const_mul
    apply tendsto_finset_sum
    intro j _
    exact (huD_tend j).const_mul (O_sec_coef j)
  -- Step 5: one-sided limit comparison.
  have hL_le : L ≤ (1/16 : ℝ) *
      (Finset.univ : Finset (Fin secBasisSize)).sum
        (fun j => O_sec_coef j * phi.eval (SecBasis.flagBasis_sec j))
      + secIdentityTol :=
    le_of_tendsto_of_tendsto htend_diag hSum_tend hIdent_diag
  -- Step 6: convert to evalAlg and apply the loose bound axiom.
  have hAggr := phi_evalAlg_O_sec_alg_eq_target_sum_F phi
  have hBound := phi_evalAlg_O_sec_alg_le_bound_F phi hreg
  rw [hAggr] at hBound
  linarith [hL_le, hBound]

end  -- noncomputable section

end Davey2024.SecBridge
