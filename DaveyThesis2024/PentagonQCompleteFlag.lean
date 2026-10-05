import DaveyThesis2024.PentagonQMuFlag
import DaveyThesis2024.PentagonQAssembly
import DaveyThesis2024.PentagonQMuBasis
import DaveyThesis2024.PentagonQNzIdx
import DaveyThesis2024.PentagonQOfFlag

/-!
# Completeness, stated in `μ`

Item C's chain takes a τ-embedding as a hypothesis.  This supplies it from
`μ ≠ 0`, closing the loop: a triangle-free, black-independent 8-vertex coloured
graph whose `μ` is non-zero is isomorphic to one of the 69.

Three parallel branches, one per pattern, each the same four steps —
`muG_ne_zero_iff` to find the positive count, `nonempty_of_rootedCountG_pos` to
get an embedding, `cgraph_data_of_rooted_embedding` to unpack it, and
`is_basis_flag_of_embedding` to conclude.
-/

namespace Davey2024
namespace PentagonQCompleteFlag

open Davey2024.PentagonQBasis Davey2024.PentagonQWeights
open Davey2024.PentagonQRooted Davey2024.PentagonQMuFlag
open Davey2024.PentagonQFamily Davey2024.PentagonQAssembly
open Davey2024.PentagonQPatFacts Davey2024.PentagonQIsoInvariance

/-- **Completeness in terms of `μ`.**  The form the regrouping consumes. -/
theorem exists_basis_of_muG_ne_zero (g : CGraph 8)
    (hsym : ∀ i j, g.adj i j = g.adj j i) (hirr : ∀ i, g.adj i i = false)
    (htf : triangleFreeC g = true) (hbi : blackIndepC g = true)
    (h : muG g.toGenFlag ≠ 0) :
    ∃ j ∈ PentagonQComplete.nzIdx,
      GenFlagClass.mk g.toGenFlag
        = GenFlagClass.mk (flagBasisCGraph j).toGenFlag := by
  rcases (muG_ne_zero_iff g.toGenFlag).mp h with hp | hp | hp
  · obtain ⟨e, he⟩ := nonempty_of_rootedCountG_pos _ hp
    obtain ⟨hcol, hadj, hdom⟩ :=
      cgraph_data_of_rooted_embedding tau1 3 patC_tau1_symm patC_tau1_irrefl
        g hsym hirr e he
    exact is_basis_flag_of_embedding g tau1 (by simp) hsym hirr htf hbi
      e.toFun e.injective (fun i => (hcol i).symm) (fun i j => (hadj i j).symm)
      (by decide) hdom
  · obtain ⟨e, he⟩ := nonempty_of_rootedCountG_pos _ hp
    obtain ⟨hcol, hadj, hdom⟩ :=
      cgraph_data_of_rooted_embedding tau2 4 patC_tau2_symm patC_tau2_irrefl
        g hsym hirr e he
    exact is_basis_flag_of_embedding g tau2 (by simp) hsym hirr htf hbi
      e.toFun e.injective (fun i => (hcol i).symm) (fun i j => (hadj i j).symm)
      (by decide) hdom
  · obtain ⟨e, he⟩ := nonempty_of_rootedCountG_pos _ hp
    obtain ⟨hcol, hadj, hdom⟩ :=
      cgraph_data_of_rooted_embedding tau3 4 patC_tau3_symm patC_tau3_irrefl
        g hsym hirr e he
    exact is_basis_flag_of_embedding g tau3 (by simp) hsym hirr htf hbi
      e.toFun e.injective (fun i => (hcol i).symm) (fun i j => (hadj i j).symm)
      (by decide) hdom

/-! ## The two facts the regrouping needs about a matching index -/

/-- Membership in the 69 is exactly a non-zero weight. -/
theorem weight_ne_zero_of_mem_nzIdx {j : Fin basisSize}
    (hj : j ∈ PentagonQComplete.nzIdx) : 4 * n1 j + n2 j + 2 * n3 j ≠ 0 := by
  have := (List.mem_filter.mp hj).2
  simpa using this

/-- If a graph's class is a basis flag's, its `μ` is that flag's weight: the
class equality gives an isomorphism, `μ` is invariant under it (B3), and at a
basis flag `μ` is the weight (`muG_flagBasis`). -/
theorem muG_eq_weight_of_class_eq {g : CGraph 8} {j : Fin basisSize}
    (h : GenFlagClass.mk g.toGenFlag = GenFlagClass.mk (flagBasisCGraph j).toGenFlag) :
    muG g.toGenFlag = 4 * n1 j + n2 j + 2 * n3 j := by
  rw [muG_flagIso (Quotient.exact h)]
  exact PentagonQMuBasis.muG_flagBasis j

/-! ## The two predicates, from the flag side

`muG_eq_sum_nzFinset` asks for `triangleFreeC` and `blackIndepC` on a `CGraph`,
while a host supplies its properties on the flag's `SimpleGraph` and colouring.
These convert, with no transport: stated at `g.toGenFlag` rather than at an
arbitrary flag equal to it, so no `▸` appears. -/

theorem triangleFreeC_of_flag {g : CGraph 8}
    (hTF : ∀ a b c : Fin 8, (g.toGenFlag.str.1).Adj a b → (g.toGenFlag.str.1).Adj b c →
      (g.toGenFlag.str.1).Adj a c → False) : triangleFreeC g = true := by
  unfold triangleFreeC
  simp only [List.all_eq_true, List.mem_finRange, forall_const]
  intro a b c
  simp only [Bool.not_eq_true']
  by_contra hcon
  simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hcon
  obtain ⟨⟨⟨⟨hab, hbc⟩, e1⟩, e2⟩, e3⟩ := hcon
  have hne1 : a ≠ b := fun hx => by rw [hx] at hab; omega
  have hne2 : b ≠ c := fun hx => by rw [hx] at hbc; omega
  have hne3 : a ≠ c := fun hx => by rw [hx] at hab; omega
  exact hTF a b c ⟨hne1, Or.inl (by simpa using e1)⟩ ⟨hne2, Or.inl (by simpa using e2)⟩
    ⟨hne3, Or.inl (by simpa using e3)⟩

theorem blackIndepC_of_flag {g : CGraph 8}
    (hBI : ∀ a b : Fin 8, (g.toGenFlag.str.1).Adj a b →
      g.toGenFlag.str.2 a = 1 → g.toGenFlag.str.2 b = 1 → False) :
    blackIndepC g = true := by
  unfold blackIndepC
  simp only [List.all_eq_true, List.mem_finRange, forall_const]
  intro a b
  simp only [Bool.not_eq_true']
  by_contra hcon
  simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨⟨hab, e⟩, c1⟩, c2⟩ := hcon
  exact hBI a b ⟨by intro hx; rw [hx] at hab; omega, Or.inl (by simpa using e)⟩ c1 c2

/-! ## The per-subset identity

`μ` of an 8-vertex graph is the sum, over the 69, of each weight taken when the
graph's class matches.  A `Finset` sum, not a `List` one: Mathlib has
`Finset.sum_eq_single_of_mem` and no list analogue, and the outer sum over
8-subsets is a `Finset` sum too.

Both branches use all four supporting facts.  When `μ = 0` no index can match,
because a match would force `μ` to be that index's weight, which is non-zero by
membership.  When `μ ≠ 0` completeness supplies a match, uniqueness makes every
other term vanish, and invariance evaluates the surviving one. -/

open scoped Classical in
/-- The 69, as a `Finset`. -/
noncomputable def nzFinset : Finset (Fin basisSize) := PentagonQComplete.nzIdx.toFinset

open scoped Classical in
/-- **E's per-subset identity.** -/
theorem muG_eq_sum_nzFinset (g : CGraph 8)
    (hsym : ∀ i j, g.adj i j = g.adj j i) (hirr : ∀ i, g.adj i i = false)
    (htf : triangleFreeC g = true) (hbi : blackIndepC g = true) :
    muG g.toGenFlag
      = Finset.sum nzFinset (fun j =>
          if GenFlagClass.mk g.toGenFlag
              = GenFlagClass.mk (flagBasisCGraph j).toGenFlag
            then 4 * n1 j + n2 j + 2 * n3 j else 0) := by
  by_cases h : muG g.toGenFlag = 0
  · rw [h]
    symm
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [if_neg]
    intro hcls
    exact weight_ne_zero_of_mem_nzIdx (List.mem_toFinset.mp hj)
      (by rw [← muG_eq_weight_of_class_eq hcls, h])
  · obtain ⟨j0, hj0, hcls0⟩ := exists_basis_of_muG_ne_zero g hsym hirr htf hbi h
    have hzero : ∀ b ∈ nzFinset, b ≠ j0 →
        (if GenFlagClass.mk g.toGenFlag
            = GenFlagClass.mk (flagBasisCGraph b).toGenFlag
          then 4 * n1 b + n2 b + 2 * n3 b else 0) = 0 := by
      intro b hb hbne
      rw [if_neg]
      intro hcls
      exact hbne (PentagonQNzIdx.nz_class_injective (List.mem_toFinset.mp hb) hj0
        (hcls.symm.trans hcls0))
    have hmem0 : j0 ∈ nzFinset := List.mem_toFinset.mpr hj0
    rw [Finset.sum_eq_single_of_mem j0 hmem0 hzero, if_pos hcls0]
    exact muG_eq_weight_of_class_eq hcls0

/-! ## Where the host's black-independence comes from

`(a1)`'s host colours `u` black exactly when `u ∈ N(v)`
(`pentagonQ_seq_to_colouredGraphClass`).  Black-independence is then not an extra
assumption at all: a black–black edge `x–y` together with `v–x` and `v–y` **is** a
triangle, so triangle-freeness alone rules it out.

Stated for a bare `SimpleGraph`, so it needs none of the flag machinery. -/

open Classical in
theorem blackIndep_of_nbhd_colouring {n : ℕ} (H : SimpleGraph (Fin n)) (v : Fin n)
    (hTF : ∀ a b c : Fin n, H.Adj a b → H.Adj b c → H.Adj a c → False)
    (x y : Fin n) (hxy : H.Adj x y)
    (hx : (if H.Adj v x then (1 : Fin 2) else 0) = 1)
    (hy : (if H.Adj v y then (1 : Fin 2) else 0) = 1) : False := by
  have hvx : H.Adj v x := by by_contra h; simp [h] at hx
  have hvy : H.Adj v y := by by_contra h; simp [h] at hy
  exact hTF v x y hvx hxy hvy

/-! ## The subset's own `CGraph`, built from the host

The inheritance step wants: a subflag of a triangle-free, black-independent host
is itself both.  Going through `exists_cgraph_of_size_eight_struct` and then
rewriting does **not** work — the subflag's index type is `Fin S.card`, the
target is `Fin 8`, and `S.card = 8` is propositional, so the rewrite is
ill-typed in the hypothesis direction.

`Finset.orderEmbOfFin` takes that proof as an argument and hands back
`Fin 8 ↪o Fin G.size` directly, so building the `CGraph` from the host through it
never leaves `Fin 8`.  Both predicates then read straight off the host's. -/

open Classical in
/-- The `CGraph` on an eight-element vertex subset of a host flag. -/
noncomputable def subCGraph {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (S : Finset (Fin G.size)) (hS : S.card = 8) : CGraph 8 where
  adj i j := decide ((G.str.1).Adj (S.orderEmbOfFin hS i) (S.orderEmbOfFin hS j))
  col v := G.str.2 (S.orderEmbOfFin hS v)

open Classical in
theorem subCGraph_symm {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (S : Finset (Fin G.size)) (hS : S.card = 8) :
    ∀ i j, (subCGraph S hS).adj i j = (subCGraph S hS).adj j i := by
  intro i j; simp [subCGraph, SimpleGraph.adj_comm]

open Classical in
theorem subCGraph_irrefl {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (S : Finset (Fin G.size)) (hS : S.card = 8) :
    ∀ i, (subCGraph S hS).adj i i = false := by
  intro i; simp [subCGraph]

open Classical in
/-- Triangle-freeness is inherited. -/
theorem subCGraph_triangleFree {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (S : Finset (Fin G.size)) (hS : S.card = 8)
    (hTF : ∀ x y z : Fin G.size, (G.str.1).Adj x y → (G.str.1).Adj y z →
      (G.str.1).Adj x z → False) :
    triangleFreeC (subCGraph S hS) = true := by
  unfold triangleFreeC
  simp only [List.all_eq_true, List.mem_finRange, forall_const]
  intro a b c
  simp only [Bool.not_eq_true']
  by_contra hcon
  simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq, subCGraph] at hcon
  obtain ⟨⟨⟨⟨-, -⟩, e1⟩, e2⟩, e3⟩ := hcon
  exact hTF _ _ _ e1 e2 e3

open Classical in
/-- Black-independence is inherited. -/
theorem subCGraph_blackIndep {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (S : Finset (Fin G.size)) (hS : S.card = 8)
    (hBI : ∀ x y : Fin G.size, (G.str.1).Adj x y → G.str.2 x = 1 → G.str.2 y = 1 → False) :
    blackIndepC (subCGraph S hS) = true := by
  unfold blackIndepC
  simp only [List.all_eq_true, List.mem_finRange, forall_const]
  intro a b
  simp only [Bool.not_eq_true']
  by_contra hcon
  simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    subCGraph] at hcon
  obtain ⟨⟨⟨-, e⟩, c1⟩, c2⟩ := hcon
  exact hBI _ _ e c1 c2

/-! ## The two enumerations of `S` agree

`genInducedSubflag` enumerates `S` at `Fin S.card` (via `orderEmbOfFin rfl`);
`subCGraph` enumerates it at `Fin 8` (via `orderEmbOfFin hS`).  Relating the two
flags needs these to be the same enumeration up to the index cast — which
`orderEmbOfFin_unique` gives, since the composite is strictly monotone into `S`
and that characterises the enumeration. -/

theorem orderEmbOfFin_finCongr {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (S : Finset (Fin G.size)) (hS : S.card = 8) :
    (fun i : Fin 8 => S.orderEmbOfFin rfl (finCongr hS.symm i))
      = fun i : Fin 8 => S.orderEmbOfFin hS i := by
  have h := Finset.orderEmbOfFin_unique (s := S) hS
    (f := fun i : Fin 8 => S.orderEmbOfFin rfl (finCongr hS.symm i))
    (fun x => Finset.orderEmbOfFin_mem _ _ _)
    (fun a b hab =>
      (S.orderEmbOfFin rfl).strictMono (Fin.lt_def.mpr (Fin.lt_def.mp hab)))
  simpa using h

/-! ## `subCGraph` presents the subflag

The class identification the size mismatch forced us into: not an equality of
flags — their index types differ — but an equality of *classes*, with
`finCongr hS.symm` as the vertex bijection and `orderEmbOfFin_finCongr` saying
the two enumerations agree. -/

open Classical in
theorem subCGraph_class_eq {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (S : Finset (Fin G.size)) (hS : S.card = 8) :
    GenFlagClass.mk (subCGraph S hS).toGenFlag
      = GenFlagClass.mk (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)) := by
  refine Quotient.sound ⟨finCongr hS.symm, ?_, fun i => i.elim0⟩
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · show (G.str.1.comap (S.orderEmbOfFin rfl)).comap (finCongr hS.symm)
        = SimpleGraph.fromRel (fun i j : Fin 8 => ((subCGraph S hS).adj i j : Bool) = true)
    have : (G.str.1.comap (S.orderEmbOfFin rfl)).comap (finCongr hS.symm)
        = G.str.1.comap (fun i : Fin 8 => S.orderEmbOfFin hS i) := by
      rw [← orderEmbOfFin_finCongr S hS]; rfl
    rw [this, ← PentagonQOfFlag.fromRel_adj_self
      (G.str.1.comap (fun i : Fin 8 => S.orderEmbOfFin hS i))]
    rfl
  · funext v
    rfl

/-! ## Discharging the per-subset hypothesis

`sum_muG_eq_sum_weights_mul_copies` takes the per-subset identity as a
hypothesis; this supplies it at one subset, given a `CGraph` presenting that
subflag.

**Phrased in terms of `g`, not of the subflag.**  The subflag's index type is
`Fin S.card`, the `CGraph` lemmas want `Fin 8`, and `S.card = 8` is a
propositional equality — routing the hypotheses through `g.toGenFlag` keeps both
sides at `Fin 8` and leaves no transport anywhere.  The caller gets `g` and `hg`
from `exists_cgraph_of_size_eight_struct`, whose `h8` is exactly `S.card = 8`. -/

open scoped Classical in
theorem persub_of_cgraph
    {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (S : Finset (Fin G.size)) (g : CGraph 8)
    (hg : g.toGenFlag = G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
    (hsym : ∀ i j, g.adj i j = g.adj j i) (hirr : ∀ i, g.adj i i = false)
    (hTF : ∀ a b c : Fin 8, (g.toGenFlag.str.1).Adj a b → (g.toGenFlag.str.1).Adj b c →
      (g.toGenFlag.str.1).Adj a c → False)
    (hBI : ∀ a b : Fin 8, (g.toGenFlag.str.1).Adj a b →
      g.toGenFlag.str.2 a = 1 → g.toGenFlag.str.2 b = 1 → False) :
    muG (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
      = Finset.sum nzFinset (fun j =>
          if GenFlagClass.mk (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
              = GenFlagClass.mk (flagBasisCGraph j).toGenFlag
            then 4 * n1 j + n2 j + 2 * n3 j else 0) := by
  rw [← hg]
  exact muG_eq_sum_nzFinset g hsym hirr (triangleFreeC_of_flag hTF) (blackIndepC_of_flag hBI)

/-! ## The per-pattern split

The audit's finding: `(a2a)` and `(a2b)` consume `Σ_S nᵢ(G'[S])` **separately**,
while `basis_identity_host` only ever produces the combination `μ`.  These give
the per-pattern versions.

The argument is the same case split, with one change: when no basis flag matches,
it is `μ(g) = 0` that follows from completeness, and each `nᵢ` vanishes because
the weights are non-negative — which is what `hzero` asks the caller to supply,
by `omega` at each pattern. -/

open scoped Classical in
theorem count_eq_sum_nzFinset (g : CGraph 8)
    (hsym : ∀ i j, g.adj i j = g.adj j i) (hirr : ∀ i, g.adj i i = false)
    (htf : triangleFreeC g = true) (hbi : blackIndepC g = true)
    (F : GenFlag (colouredGraphUniverse 2) (GenFlagType.empty (colouredGraphUniverse 2)))
    (root : Fin F.size) (nf : Fin basisSize → ℕ)
    (hnf : ∀ j, rootedCountG F (flagBasisCGraph j).toGenFlag root = nf j)
    (hzero : ∀ h : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2)), muG h = 0 → rootedCountG F h root = 0) :
    rootedCountG F g.toGenFlag root
      = Finset.sum nzFinset (fun j =>
          if GenFlagClass.mk g.toGenFlag
              = GenFlagClass.mk (flagBasisCGraph j).toGenFlag
            then nf j else 0) := by
  by_cases hex : ∃ j ∈ nzFinset, GenFlagClass.mk g.toGenFlag
      = GenFlagClass.mk (flagBasisCGraph j).toGenFlag
  · obtain ⟨j0, hj0, hcls0⟩ := hex
    have hz : ∀ b ∈ nzFinset, b ≠ j0 →
        (if GenFlagClass.mk g.toGenFlag
            = GenFlagClass.mk (flagBasisCGraph b).toGenFlag then nf b else 0) = 0 := by
      intro b hb hbne
      rw [if_neg]
      intro hcls
      exact hbne (PentagonQNzIdx.nz_class_injective (List.mem_toFinset.mp hb)
        (List.mem_toFinset.mp hj0) (hcls.symm.trans hcls0))
    rw [Finset.sum_eq_single_of_mem j0 hj0 hz, if_pos hcls0, ← hnf j0]
    exact rootedCountG_flagIso_target root (Quotient.exact hcls0)
  · push_neg at hex
    have hmu : muG g.toGenFlag = 0 := by
      by_contra h
      obtain ⟨j, hj, hc⟩ := exists_basis_of_muG_ne_zero g hsym hirr htf hbi h
      exact hex j (List.mem_toFinset.mpr hj) hc
    rw [hzero _ hmu]
    symm
    exact Finset.sum_eq_zero (fun j hj => if_neg (hex j hj))

/-! ## Discharging it at a host

`persub_of_cgraph` asks for `g.toGenFlag = subflag`, an **equality** of flags.
That is well-typed — `size` is a field, not an index — but proving it needs a
transport along `S.card = 8` in the `str` component, which is the cast the whole
`subCGraph` detour exists to avoid.  The class version asks only for
`mk g.toGenFlag = mk subflag`, which `subCGraph_class_eq` supplies outright, and
`μ`'s isomorphism-invariance closes the gap. -/

open scoped Classical in
theorem persub_of_cgraph_class
    {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (S : Finset (Fin G.size)) (g : CGraph 8)
    (hclass : GenFlagClass.mk g.toGenFlag
      = GenFlagClass.mk (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)))
    (hsym : ∀ i j, g.adj i j = g.adj j i) (hirr : ∀ i, g.adj i i = false)
    (htf : triangleFreeC g = true) (hbi : blackIndepC g = true) :
    muG (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
      = Finset.sum nzFinset (fun j =>
          if GenFlagClass.mk (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
              = GenFlagClass.mk (flagBasisCGraph j).toGenFlag
            then 4 * n1 j + n2 j + 2 * n3 j else 0) := by
  rw [← muG_flagIso (Quotient.exact hclass), muG_eq_sum_nzFinset g hsym hirr htf hbi]
  exact Finset.sum_congr rfl (fun j _ => by rw [hclass])

open Classical in
/-- **The per-subset hypothesis, discharged at every 8-subset of a host** that is
triangle-free and black-independent. -/
theorem persub_of_host
    {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (hTF : ∀ x y z : Fin G.size, (G.str.1).Adj x y → (G.str.1).Adj y z →
      (G.str.1).Adj x z → False)
    (hBI : ∀ x y : Fin G.size, (G.str.1).Adj x y → G.str.2 x = 1 → G.str.2 y = 1 → False)
    (S : Finset (Fin G.size)) (hS : S.card = 8) :
    muG (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
      = Finset.sum nzFinset (fun j =>
          if GenFlagClass.mk (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
              = GenFlagClass.mk (flagBasisCGraph j).toGenFlag
            then 4 * n1 j + n2 j + 2 * n3 j else 0) :=
  persub_of_cgraph_class S (subCGraph S hS) (subCGraph_class_eq S hS)
    (subCGraph_symm S hS) (subCGraph_irrefl S hS)
    (subCGraph_triangleFree S hS hTF) (subCGraph_blackIndep S hS hBI)

/-! ## The outer sum

Summing the per-subset identity and swapping the order turns `Σ_S μ(G[S])` into
`Σⱼ μⱼ · c(Fⱼ;G)` — the shape item E's right-hand side needs.

**Restricted to 8-subsets, and that restriction is not cosmetic.**  A first
version of this summed over *every* subset.  It was true, but its hypothesis
could never be discharged: for `|S| = 4` with `G[S]` a τ₁-shaped coloured graph,
a bijective embedding leaves no vertex outside the image, so the root-domination
clause is vacuous and `μ(G[S]) > 0` — while no basis flag, all of size 8, can
match it, so the right-hand side is `0`.  A theorem with an undischargeable
hypothesis is worse than a false one: it looks usable.

The two sides still agree on the *unrestricted* right-hand side, because a class
match forces `S.card = 8` — which is what `card_eq_eight_of_class_eq` says.

**This is the step where a factor error would typecheck**, so it is kept to one
`sum_comm`, one `sum_ite` and that one cardinality argument. -/

/-- A subset whose induced subflag is a basis flag has exactly eight vertices. -/
theorem card_eq_eight_of_class_eq
    {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    {S : Finset (Fin G.size)} {j : Fin basisSize}
    (h : GenFlagClass.mk (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
        = GenFlagClass.mk (flagBasisCGraph j).toGenFlag) : S.card = 8 :=
  genFlagIso_size_eq (Quotient.exact h)

open scoped Classical in
theorem sum_muG_eq_sum_weights_mul_copies
    {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (persub : ∀ S : Finset (Fin G.size), S.card = 8 →
      muG (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
        = Finset.sum nzFinset (fun j =>
            if GenFlagClass.mk (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
                = GenFlagClass.mk (flagBasisCGraph j).toGenFlag
              then 4 * n1 j + n2 j + 2 * n3 j else 0)) :
    Finset.sum (Finset.univ.filter (fun S : Finset (Fin G.size) => S.card = 8))
        (fun S => muG (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)))
      = Finset.sum nzFinset (fun j =>
          (4 * n1 j + n2 j + 2 * n3 j) *
            PentagonQOrbit.subsetCopies (flagBasisCGraph j).toGenFlag G) := by
  rw [Finset.sum_congr rfl (fun S hS => persub S (Finset.mem_filter.mp hS).2),
    Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul,
    mul_comm]
  congr 1
  show ((Finset.univ.filter (fun S : Finset (Fin G.size) => S.card = 8)).filter _).card = _
  unfold PentagonQOrbit.subsetCopies
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hS => hS.2, fun hS => ⟨card_eq_eight_of_class_eq hS, hS⟩⟩

open Classical in
/-- **E's combinatorial half, at a host.**  For a triangle-free,
black-independent host, the sum of `μ` over its 8-subsets is the weighted sum of
the 69 flags' subset counts — the paper's `Σ_S μ(G'[S]) = Σⱼ μⱼ · c(Fⱼ;G')`. -/
theorem sum_muG_host_eq_sum_weights_mul_copies
    {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (hTF : ∀ x y z : Fin G.size, (G.str.1).Adj x y → (G.str.1).Adj y z →
      (G.str.1).Adj x z → False)
    (hBI : ∀ x y : Fin G.size, (G.str.1).Adj x y → G.str.2 x = 1 → G.str.2 y = 1 → False) :
    Finset.sum (Finset.univ.filter (fun S : Finset (Fin G.size) => S.card = 8))
        (fun S => muG (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)))
      = Finset.sum nzFinset (fun j =>
          (4 * n1 j + n2 j + 2 * n3 j) *
            PentagonQOrbit.subsetCopies (flagBasisCGraph j).toGenFlag G) :=
  sum_muG_eq_sum_weights_mul_copies (fun S hS => persub_of_host hTF hBI S hS)

/-! ## From the 69 back to all 9295

The certificate's objective sums over **every** basis flag; the regrouping sums
over the 69.  They agree because the other 9226 carry weight zero — which is
what membership in `nzIdx` means, read the other way. -/

theorem weight_eq_zero_of_not_mem_nzIdx {j : Fin basisSize}
    (hj : j ∉ PentagonQComplete.nzIdx) : 4 * n1 j + n2 j + 2 * n3 j = 0 := by
  by_contra hne
  exact hj (List.mem_filter.mpr ⟨List.mem_finRange j, by simpa using hne⟩)

/-! The per-pattern consequences.  `weight_eq_zero_of_not_mem_nzIdx` says the
*combination* `4n₁+n₂+2n₃` vanishes off the 69; since the three counts are
naturals, each vanishes separately.  Without these the per-pattern sums below
could not be moved onto the same index set as the weighted one. -/

theorem n1_eq_zero_of_not_mem_nzIdx {j : Fin basisSize}
    (hj : j ∉ PentagonQComplete.nzIdx) : n1 j = 0 := by
  have := weight_eq_zero_of_not_mem_nzIdx hj; omega

theorem n2_eq_zero_of_not_mem_nzIdx {j : Fin basisSize}
    (hj : j ∉ PentagonQComplete.nzIdx) : n2 j = 0 := by
  have := weight_eq_zero_of_not_mem_nzIdx hj; omega

theorem n3_eq_zero_of_not_mem_nzIdx {j : Fin basisSize}
    (hj : j ∉ PentagonQComplete.nzIdx) : n3 j = 0 := by
  have := weight_eq_zero_of_not_mem_nzIdx hj; omega

open scoped Classical in
/-- A sum over the 69 is a sum over all 9295, when the summand vanishes off the
69. -/
theorem sum_nzFinset_eq_sum_univ (f : Fin basisSize → ℕ)
    (hf : ∀ j, j ∉ PentagonQComplete.nzIdx → f j = 0) :
    Finset.sum nzFinset f = Finset.sum Finset.univ f := by
  refine Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => hf j ?_)
  exact fun hmem => hj (List.mem_toFinset.mpr hmem)

open Classical in
/-- **E's combinatorial half, over the whole basis.**  The form the certificate's
objective is written in: a sum over all 9295 flags, not just the 69. -/
theorem sum_muG_host_eq_sum_univ
    {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (hTF : ∀ x y z : Fin G.size, (G.str.1).Adj x y → (G.str.1).Adj y z →
      (G.str.1).Adj x z → False)
    (hBI : ∀ x y : Fin G.size, (G.str.1).Adj x y → G.str.2 x = 1 → G.str.2 y = 1 → False) :
    Finset.sum (Finset.univ.filter (fun S : Finset (Fin G.size) => S.card = 8))
        (fun S => muG (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)))
      = Finset.sum Finset.univ (fun j =>
          (4 * n1 j + n2 j + 2 * n3 j) *
            PentagonQOrbit.subsetCopies (flagBasisCGraph j).toGenFlag G) := by
  rw [← sum_nzFinset_eq_sum_univ _ (fun j hj => by
    rw [weight_eq_zero_of_not_mem_nzIdx hj, zero_mul])]
  exact sum_muG_host_eq_sum_weights_mul_copies hTF hBI

/-! ## The arithmetic pairing

`Σⱼ (μⱼ/6720)·(c(Fⱼ;G)/D) = (1/(6720·D))·Σ_S μ(G[S])` — the paper's identity,
with `D` left abstract (it is `C(Δ,8)`, supplied by the density collapse).

Everything above is combinatorics; this is the only place the constant `6720`
and the density's denominator meet, so it is written as one `push_cast` and one
`ring` per term, with no rearrangement hidden in between. -/

open Classical in
theorem sum_weighted_density_eq
    {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (hTF : ∀ x y z : Fin G.size, (G.str.1).Adj x y → (G.str.1).Adj y z →
      (G.str.1).Adj x z → False)
    (hBI : ∀ x y : Fin G.size, (G.str.1).Adj x y → G.str.2 x = 1 → G.str.2 y = 1 → False)
    (D : ℝ) :
    Finset.sum Finset.univ (fun j =>
        ((4 * n1 j + n2 j + 2 * n3 j : ℕ) : ℝ) / 6720 *
          (((PentagonQOrbit.subsetCopies (flagBasisCGraph j).toGenFlag G : ℕ) : ℝ) / D))
      = (1 / (6720 * D)) *
        ((Finset.sum (Finset.univ.filter (fun S : Finset (Fin G.size) => S.card = 8))
          (fun S => muG (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))) : ℕ) : ℝ) := by
  rw [sum_muG_host_eq_sum_univ hTF hBI]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-! ## In the objective's own terms

Substituting the density collapse for the abstract `D` puts the left-hand side in
the form the certificate's objective is written in: a weighted sum of
`genUnlabelledDensity` over the basis.  What is left after this is the
identification of `μⱼ/6720` with `O_Q_coef j`, which is obligation (b). -/

open Classical in
theorem sum_weight_mul_density_eq
    {G : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2))}
    (hTF : ∀ x y z : Fin G.size, (G.str.1).Adj x y → (G.str.1).Adj y z →
      (G.str.1).Adj x z → False)
    (hBI : ∀ x y : Fin G.size, (G.str.1).Adj x y → G.str.2 x = 1 → G.str.2 y = 1 → False)
    (Δfn : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2)) → ℕ) :
    Finset.sum Finset.univ (fun j =>
        ((4 * n1 j + n2 j + 2 * n3 j : ℕ) : ℝ) / 6720 *
          genUnlabelledDensity (colouredGraphUniverse 2)
            (GenFlagType.empty (colouredGraphUniverse 2))
            (flagBasisCGraph j).toGenFlag G Δfn)
      = (1 / (6720 * (Nat.choose (Δfn G.forget) 8 : ℝ))) *
        ((Finset.sum (Finset.univ.filter (fun S : Finset (Fin G.size) => S.card = 8))
          (fun S => muG (G.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))) : ℕ) : ℝ) := by
  have hden : ∀ j : Fin basisSize,
      genUnlabelledDensity (colouredGraphUniverse 2)
          (GenFlagType.empty (colouredGraphUniverse 2))
          (flagBasisCGraph j).toGenFlag G Δfn
        = ((PentagonQOrbit.subsetCopies (flagBasisCGraph j).toGenFlag G : ℕ) : ℝ)
            / (Nat.choose (Δfn G.forget) 8 : ℝ) := by
    intro j
    rw [PentagonQOrbit.genUnlabelledDensity_eq_copies_div,
      PentagonQOrbit.copies_eq_subsetCopies]
    rfl
  simp only [hden]
  exact sum_weighted_density_eq hTF hBI _

/-! ## At the actual host type

`ColouredGraphClass` carries `triangleFree` and `blackIndependent` as **fields**,
and `toGenFlag` sets `str := ⟨graph.graph, colouring⟩`, so both hypotheses of the
identity are the structure's own data — no derivation needed.

(That makes `blackIndep_of_nbhd_colouring` unnecessary *for this path*.  It is
still the reason the field holds for `pentagonQ_seq_to_colouredGraphClass`, whose
colouring is the `N(v)` indicator, so it is kept rather than deleted.) -/

theorem host_hTF (C : ColouredGraphClass) :
    ∀ x y z : Fin C.toGenFlag.size, (C.toGenFlag.str.1).Adj x y →
      (C.toGenFlag.str.1).Adj y z → (C.toGenFlag.str.1).Adj x z → False :=
  C.triangleFree

theorem host_hBI (C : ColouredGraphClass) :
    ∀ x y : Fin C.toGenFlag.size, (C.toGenFlag.str.1).Adj x y →
      C.toGenFlag.str.2 x = 1 → C.toGenFlag.str.2 y = 1 → False :=
  fun x y hadj hx hy => C.blackIndependent x y hx hy hadj

open Classical in
/-- **(a1)'s identity at the host type the bridge actually uses.** -/
theorem sum_weight_mul_density_host (C : ColouredGraphClass)
    (Δfn : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2)) → ℕ) :
    Finset.sum Finset.univ (fun j =>
        ((4 * n1 j + n2 j + 2 * n3 j : ℕ) : ℝ) / 6720 *
          genUnlabelledDensity (colouredGraphUniverse 2)
            (GenFlagType.empty (colouredGraphUniverse 2))
            (flagBasisCGraph j).toGenFlag C.toGenFlag Δfn)
      = (1 / (6720 * (Nat.choose (Δfn C.toGenFlag.forget) 8 : ℝ))) *
        ((Finset.sum (Finset.univ.filter
            (fun S : Finset (Fin C.toGenFlag.size) => S.card = 8))
          (fun S => muG (C.toGenFlag.genInducedSubflag S (fun i => i.elim0)
            (Nat.zero_le _))) : ℕ) : ℝ) :=
  sum_weight_mul_density_eq (host_hTF C) (host_hBI C) Δfn

/-! ## In the certificate's own coefficients

The last step: obligation (b) says `O_Q_weight j = 4n₁+n₂+2n₃`, so the weight
this file has carried throughout **is** the certificate's coefficient, once
divided by `6720`. -/

theorem weight_div_eq_coef (j : Fin basisSize) :
    ((4 * n1 j + n2 j + 2 * n3 j : ℕ) : ℝ) / 6720 = PentagonQObjective.O_Q_coef j := by
  unfold PentagonQObjective.O_Q_coef
  rw [O_Q_weight_eq_combinatorial j]
  push_cast
  ring

open Classical in
/-- **(a1)'s identity, in the certificate's coefficients.**

    Σⱼ O_Q_coef j · ρ(Fⱼ;G)  =  (1/(6720·C(Δ,8))) · Σ_{|S|=8} μ(G[S])

for any `ColouredGraphClass` host.  Every factor on the left is the objective's
own; every term on the right is a rooted count. -/
theorem basis_identity_host (C : ColouredGraphClass)
    (Δfn : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2)) → ℕ) :
    Finset.sum Finset.univ (fun j =>
        PentagonQObjective.O_Q_coef j *
          genUnlabelledDensity (colouredGraphUniverse 2)
            (GenFlagType.empty (colouredGraphUniverse 2))
            (flagBasisCGraph j).toGenFlag C.toGenFlag Δfn)
      = (1 / (6720 * (Nat.choose (Δfn C.toGenFlag.forget) 8 : ℝ))) *
        ((Finset.sum (Finset.univ.filter
            (fun S : Finset (Fin C.toGenFlag.size) => S.card = 8))
          (fun S => muG (C.toGenFlag.genInducedSubflag S (fun i => i.elim0)
            (Nat.zero_le _))) : ℕ) : ℝ) := by
  simp only [← weight_div_eq_coef]
  exact sum_weight_mul_density_host C Δfn


/-! `basis_identity_at_axiom_host` removed 2026-10-01: it restated the identity
at `PentagonQBridge.pentagonQ_seq_to_colouredGraphClass`, which forced this module
to depend on `PentagonQBridge` and so made the axiom impossible to discharge in
place.  Nothing used it; `PentagonQAssembleA` supersedes it. -/

/-! ## The per-pattern sums at a host

What `(a2a)` and `(a2b)` consume. -/

open Classical in
theorem persub_count_of_host (C : ColouredGraphClass)
    (F : GenFlag (colouredGraphUniverse 2) (GenFlagType.empty (colouredGraphUniverse 2)))
    (root : Fin F.size) (nf : Fin basisSize → ℕ)
    (hnf : ∀ j, rootedCountG F (flagBasisCGraph j).toGenFlag root = nf j)
    (hzero : ∀ h : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2)), muG h = 0 → rootedCountG F h root = 0)
    (S : Finset (Fin C.toGenFlag.size)) (hS : S.card = 8) :
    rootedCountG F (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)) root
      = Finset.sum nzFinset (fun j =>
          if GenFlagClass.mk (C.toGenFlag.genInducedSubflag S (fun i => i.elim0)
              (Nat.zero_le _)) = GenFlagClass.mk (flagBasisCGraph j).toGenFlag
            then nf j else 0) := by
  have hclass := subCGraph_class_eq S hS
  rw [← rootedCountG_flagIso_target root (Quotient.exact hclass),
    count_eq_sum_nzFinset (subCGraph S hS) (subCGraph_symm S hS) (subCGraph_irrefl S hS)
      (subCGraph_triangleFree S hS (host_hTF C)) (subCGraph_blackIndep S hS (host_hBI C))
      F root nf hnf hzero]
  exact Finset.sum_congr rfl (fun j _ => by rw [hclass])

open Classical in
/-- **The per-pattern subset sum**, the form `(a2a)` and `(a2b)` consume. -/
theorem sum_count_host (C : ColouredGraphClass)
    (F : GenFlag (colouredGraphUniverse 2) (GenFlagType.empty (colouredGraphUniverse 2)))
    (root : Fin F.size) (nf : Fin basisSize → ℕ)
    (hnf : ∀ j, rootedCountG F (flagBasisCGraph j).toGenFlag root = nf j)
    (hzero : ∀ h : GenFlag (colouredGraphUniverse 2)
      (GenFlagType.empty (colouredGraphUniverse 2)), muG h = 0 → rootedCountG F h root = 0) :
    Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.toGenFlag.size) => S.card = 8))
        (fun S => rootedCountG F
          (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _)) root)
      = Finset.sum nzFinset (fun j =>
          nf j * PentagonQOrbit.subsetCopies (flagBasisCGraph j).toGenFlag C.toGenFlag) := by
  rw [Finset.sum_congr rfl (fun S hS =>
      persub_count_of_host C F root nf hnf hzero S (Finset.mem_filter.mp hS).2),
    Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul,
    mul_comm]
  congr 1
  show ((Finset.univ.filter (fun S : Finset (Fin C.toGenFlag.size) => S.card = 8)).filter _).card
      = _
  unfold PentagonQOrbit.subsetCopies
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hS => hS.2, fun hS => ⟨card_eq_eight_of_class_eq hS, hS⟩⟩

open Classical in
/-- `Σ_S n₁(G'[S]) = Σⱼ n₁(Fⱼ)·c(Fⱼ;G')` — `(a2a)`'s left-hand side. -/
theorem sum_n1_host (C : ColouredGraphClass) :
    Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.toGenFlag.size) => S.card = 8))
        (fun S => rootedCountG (tauFlag tau1 4)
          (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
          ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩)
      = Finset.sum nzFinset (fun j =>
          n1 j * PentagonQOrbit.subsetCopies (flagBasisCGraph j).toGenFlag C.toGenFlag) :=
  sum_count_host C _ _ n1 PentagonQMuBasis.rootedCountG_tau1_flagBasis
    (fun h hmu => by unfold muG at hmu; omega)

open Classical in
/-- `Σ_S n₂(G'[S]) = Σⱼ n₂(Fⱼ)·c(Fⱼ;G')` — half of `(a2b)`'s left-hand side. -/
theorem sum_n2_host (C : ColouredGraphClass) :
    Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.toGenFlag.size) => S.card = 8))
        (fun S => rootedCountG (tauFlag tau2 5)
          (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
          ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩)
      = Finset.sum nzFinset (fun j =>
          n2 j * PentagonQOrbit.subsetCopies (flagBasisCGraph j).toGenFlag C.toGenFlag) :=
  sum_count_host C _ _ n2 PentagonQMuBasis.rootedCountG_tau2_flagBasis
    (fun h hmu => by unfold muG at hmu; omega)

open Classical in
/-- `Σ_S n₃(G'[S]) = Σⱼ n₃(Fⱼ)·c(Fⱼ;G')` — the other half. -/
theorem sum_n3_host (C : ColouredGraphClass) :
    Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.toGenFlag.size) => S.card = 8))
        (fun S => rootedCountG (tauFlag tau3 5)
          (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
          ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩)
      = Finset.sum nzFinset (fun j =>
          n3 j * PentagonQOrbit.subsetCopies (flagBasisCGraph j).toGenFlag C.toGenFlag) :=
  sum_count_host C _ _ n3 PentagonQMuBasis.rootedCountG_tau3_flagBasis
    (fun h hmu => by unfold muG at hmu; omega)

/-! ## The per-pattern sums over the whole basis

`basis_identity_host` and `sum_muG_host_eq_sum_univ` emit sums over all 9295
flags.  These three put the per-pattern sums on that same index set, so a
consumer of `(a2a)`/`(a2b)` can combine them with the weighted identity without
first reconciling `nzFinset` against `Finset.univ`. -/

open Classical in
/-- `sum_n1_host` over all 9295 flags. -/
theorem sum_n1_host_univ (C : ColouredGraphClass) :
    Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.toGenFlag.size) => S.card = 8))
        (fun S => rootedCountG (tauFlag tau1 4)
          (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
          ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩)
      = Finset.sum Finset.univ (fun j =>
          n1 j * PentagonQOrbit.subsetCopies (flagBasisCGraph j).toGenFlag C.toGenFlag) := by
  rw [← sum_nzFinset_eq_sum_univ _ (fun j hj => by
    rw [n1_eq_zero_of_not_mem_nzIdx hj, zero_mul])]
  exact sum_n1_host C

open Classical in
/-- `sum_n2_host` over all 9295 flags. -/
theorem sum_n2_host_univ (C : ColouredGraphClass) :
    Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.toGenFlag.size) => S.card = 8))
        (fun S => rootedCountG (tauFlag tau2 5)
          (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
          ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩)
      = Finset.sum Finset.univ (fun j =>
          n2 j * PentagonQOrbit.subsetCopies (flagBasisCGraph j).toGenFlag C.toGenFlag) := by
  rw [← sum_nzFinset_eq_sum_univ _ (fun j hj => by
    rw [n2_eq_zero_of_not_mem_nzIdx hj, zero_mul])]
  exact sum_n2_host C

open Classical in
/-- `sum_n3_host` over all 9295 flags. -/
theorem sum_n3_host_univ (C : ColouredGraphClass) :
    Finset.sum (Finset.univ.filter (fun S : Finset (Fin C.toGenFlag.size) => S.card = 8))
        (fun S => rootedCountG (tauFlag tau3 5)
          (C.toGenFlag.genInducedSubflag S (fun i => i.elim0) (Nat.zero_le _))
          ⟨0, by simp [tauFlag, CGraph.toGenFlag]⟩)
      = Finset.sum Finset.univ (fun j =>
          n3 j * PentagonQOrbit.subsetCopies (flagBasisCGraph j).toGenFlag C.toGenFlag) := by
  rw [← sum_nzFinset_eq_sum_univ _ (fun j hj => by
    rw [n3_eq_zero_of_not_mem_nzIdx hj, zero_mul])]
  exact sum_n3_host C

#print axioms sum_n1_host_univ
#print axioms sum_n2_host_univ
#print axioms sum_n3_host_univ
#print axioms sum_n1_host
#print axioms sum_n2_host
#print axioms sum_n3_host
#print axioms weight_div_eq_coef
#print axioms basis_identity_host
#print axioms sum_weight_mul_density_host
#print axioms sum_weight_mul_density_eq
#print axioms sum_weighted_density_eq
#print axioms sum_muG_host_eq_sum_univ
#print axioms weight_eq_zero_of_not_mem_nzIdx
#print axioms sum_nzFinset_eq_sum_univ
#print axioms sum_muG_host_eq_sum_weights_mul_copies
#print axioms sum_muG_eq_sum_weights_mul_copies
#print axioms muG_eq_sum_nzFinset
#print axioms weight_ne_zero_of_mem_nzIdx
#print axioms muG_eq_weight_of_class_eq
#print axioms exists_basis_of_muG_ne_zero

end PentagonQCompleteFlag
end Davey2024
