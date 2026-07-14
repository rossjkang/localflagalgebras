import DaveyThesis2024.FlagIso
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Finsupp.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Davey 2024: Local Flag Algebras — Algebraic Structure

The algebraic structure from Chapter 2 of Eoin Davey's MSc thesis
"Local Flags: Bounding the Strong Chromatic Index" (UvA, 2024).

Defines the local flag algebra 𝓛^σ and its key properties:
* Product structure: F · F' = Σ_H p(F,F';H) · H (Def 2.6)
* Product limit theorem: ρ(f;G)ρ(g;G) = ρ(f·g;G) + O(1/Δ) (Thm 2.3)
* Algebra properties: commutative, associative, unital (Lem 2.4)
* Limit functionals: φ(F) = lim ρ(F;G_k) along Δ-increasing sequences (§2.2)
* Positivity and the semantic cone C^σ_sem (§2.3)
* Averaging operator ⟦·⟧ and positivity preservation (§2.4)

The algebra `FlagAlg σ` is constructed concretely as `FlagClass σ →₀ ℝ`
(Finsupp over isomorphism classes from `FlagIso.lean`). Vector space operations,
density evaluation, limit functional evaluation, normalisation factor, and the
averaging operator are all defined concretely with proved properties.

## Main results

* `product_comm`, `product_unit`, `product_assoc` — algebra properties (Lem 2.4)
* `product_limit` — product limit theorem (Thm 2.3)
* `limit_functional_construction` — Tychonoff limit functional (§2.2)
* `averaging_preserves_positivity` — averaging preserves semantic cone (Lem 2.7/2.8)
* `sdp_method` — semidefinite method (§2.5)

## Status

SimpleGraph specialization: fully proved (0 axioms, 0 sorries).
Generic `RelUniverse` infrastructure: 0 axioms, 6 sorries (orbit counting
translation from SimpleGraph proofs, deferred).

## References

* E. Davey, "Local Flags: Bounding the Strong Chromatic Index", MSc thesis, UvA, 2024.
-/

open Finset BigOperators

set_option linter.style.openClassical false
set_option linter.unusedSectionVars false

open Classical

namespace Davey2024

/-! ## §2.2: The Local Flag Algebra 𝓛^σ = ℝ𝒢^σ_loc

The formal real vector space of local σ-flags, constructed as `Finsupp`
over isomorphism classes `FlagClass σ`. In the thesis, 𝓛^σ = ℝ𝒢^σ_loc
is the space of formal ℝ-linear combinations of local σ-flags (not
quotiented by a chain rule subspace, unlike the classic algebra
𝒜^σ = ℝ𝒢^σ / 𝒦^σ). -/

/-- The **local flag algebra** 𝓛^σ: formal ℝ-linear combinations of local σ-flags,
    indexed by isomorphism classes `FlagClass σ`. -/
noncomputable abbrev FlagAlg (σ : FlagType) := FlagClass σ →₀ ℝ

/-- Zero element of 𝓛^σ. -/
noncomputable def FlagAlg.zero (σ : FlagType) : FlagAlg σ := 0

/-- Basis element: a single local σ-flag F viewed as an element of 𝓛^σ. -/
noncomputable def FlagAlg.single (σ : FlagType) (F : Flag σ) : FlagAlg σ :=
  Finsupp.single (FlagClass.mk F) 1

/-- Scalar multiplication c · v in 𝓛^σ. -/
noncomputable def FlagAlg.smul (c : ℝ) (v : FlagAlg σ) : FlagAlg σ :=
  v.mapRange (c * ·) (by simp)

/-- Vector addition v + w in 𝓛^σ. -/
noncomputable def FlagAlg.add (v w : FlagAlg σ) : FlagAlg σ := v + w

/-! ### Density evaluation

Linearly extend the local density ρ to all of 𝓛^σ. -/

/-- Lift `localDensity σ · G Δ` to isomorphism classes. -/
noncomputable def classLocalDensity (σ : FlagType) (G : Flag σ) (Δ : GraphParam)
    (cls : FlagClass σ) : ℝ :=
  Quotient.lift (fun F => localDensity σ F G Δ)
    (fun _ _ h => localDensity_flagIso h) cls

/-- Evaluate the local density of a vector v ∈ 𝓛^σ at a σ-flag G with parameter Δ:
    ρ(v; G) = Σ_F coeff(F) · ρ(F; G). -/
noncomputable def FlagAlg.evalDensity (v : FlagAlg σ) (G : Flag σ) (Δ : GraphParam) : ℝ :=
  v.sum (fun cls c => c * classLocalDensity σ G Δ cls)

/-- ρ(F; G) for a basis element equals the local density.

    **Status**: Intentional standalone — `@[simp]`-tagged def-equivalence;
    no named consumer expected (consumed by `simp` reduction). -/
@[simp]
theorem classLocalDensity_mk (σ : FlagType) (F G : Flag σ) (Δ : GraphParam) :
    classLocalDensity σ G Δ (FlagClass.mk F) = localDensity σ F G Δ := by
  simp [classLocalDensity, FlagClass.mk]

/-- ρ(F; G) for a basis element equals the local density. -/
theorem FlagAlg.evalDensity_single (σ : FlagType) (F G : Flag σ) (Δ : GraphParam) :
    (FlagAlg.single σ F).evalDensity G Δ = localDensity σ F G Δ := by
  simp [FlagAlg.single, FlagAlg.evalDensity, Finsupp.sum_single_index]

/-- ρ(c·v; G) = c · ρ(v; G). -/
theorem FlagAlg.evalDensity_smul (c : ℝ) (v : FlagAlg σ) (G : Flag σ) (Δ : GraphParam) :
    (FlagAlg.smul c v).evalDensity G Δ = c * v.evalDensity G Δ := by
  simp only [FlagAlg.smul, FlagAlg.evalDensity]
  rw [Finsupp.sum_mapRange_index (by simp)]
  simp only [Finsupp.sum, mul_assoc]
  rw [← Finset.mul_sum]

/-- ρ(v + w; G) = ρ(v; G) + ρ(w; G). -/
theorem FlagAlg.evalDensity_add (v w : FlagAlg σ) (G : Flag σ) (Δ : GraphParam) :
    (FlagAlg.add v w).evalDensity G Δ = v.evalDensity G Δ + w.evalDensity G Δ := by
  simp only [FlagAlg.add, FlagAlg.evalDensity]
  rw [Finsupp.sum_add_index (by simp) (by intros; ring)]

/-! ## §2.2: Local Flag Product (Def 2.6)

The product F · F' = Σ_{H ∈ 𝒢^σ_{loc,n}} p(F, F'; H) · H where n = |F|+|F'|-|σ|.
Uses the *induced density* p (not the local density ρ). -/

/-- Convert a (graph, embedding) sigma pair to a Flag. -/
def flagOfSigma (σ : FlagType) (n : ℕ) (hn : σ.size ≤ n)
    (p : Σ (g : SimpleGraph (Fin n)), (σ.graph ↪g g)) : Flag σ :=
  ⟨n, p.1, p.2, hn⟩

/-- The finite set of isomorphism classes of σ-flags of size n. -/
noncomputable def classesOfSize (σ : FlagType) (n : ℕ) (hn : σ.size ≤ n) :
    Finset (FlagClass σ) :=
  (Finset.univ : Finset (Σ (g : SimpleGraph (Fin n)), (σ.graph ↪g g))).image
    (fun p => FlagClass.mk (flagOfSigma σ n hn p))

/-- The canonical representative of a class in `classesOfSize` has size n. -/
theorem classesOfSize_out_size {σ : FlagType} {n : ℕ} {hn : σ.size ≤ n}
    {cls : FlagClass σ} (hcls : cls ∈ classesOfSize σ n hn) :
    cls.out.size = n := by
  rw [classesOfSize, Finset.mem_image] at hcls
  obtain ⟨p, _, rfl⟩ := hcls
  have hiso := Quotient.exact (Quotient.out_eq (FlagClass.mk (flagOfSigma σ n hn p)))
  exact (flagIso_size_eq hiso).symm ▸ rfl

/-- The **flag automorphism count** |Aut_σ(F)|: the number of σ-compatible induced
    self-embeddings of F. Since F has finite vertex set and self-embeddings are
    injective, these are exactly the flag automorphisms.
    Always ≥ 1 (the identity is an automorphism). -/
noncomputable def flagAutCount (σ : FlagType) (F : Flag σ) : ℕ :=
  inducedCount σ F F

/-- The identity embedding witnesses `flagAutCount σ F ≥ 1`. -/
theorem flagAutCount_pos (σ : FlagType) (F : Flag σ) : 0 < flagAutCount σ F := by
  unfold flagAutCount inducedCount
  rw [Fintype.card_pos_iff]
  exact ⟨⟨id, Function.injective_id,
    fun _ _ h => h, fun _ _ _ h => h, fun _ => rfl⟩⟩

/-- The type σ viewed as a σ-flag has exactly one automorphism (the identity),
    since all vertices are labelled and must be fixed. -/
theorem flagAutCount_toFlag (σ : FlagType) : flagAutCount σ σ.toFlag = 1 := by
  unfold flagAutCount inducedCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨id, Function.injective_id,
    fun _ _ h => h, fun _ _ _ h => h, fun _ => rfl⟩, fun e => ?_⟩
  -- e must fix all vertices since σ.toFlag.embedding = refl and all vertices are labelled
  have hfun : e.toFun = id := funext fun x => by
    have hx : x.val < σ.size := by
      exact x.isLt
    have : x = σ.toFlag.embedding ⟨x.val, hx⟩ := by
      simp [FlagType.toFlag, SimpleGraph.Embedding.refl]
    rw [this]; exact e.compat _
  cases e; simp only [InducedEmbedding.mk.injEq]; exact hfun

/-- The **local flag product** F · F' on basis elements.
    F · F' := (1/|Aut_σ(F)|·|Aut_σ(F')|) · Σ_{[H] : |H|=n} p(F, F'; H) · [H]
    where n = |F| + |F'| - |σ| and p is the joint induced density.
    The automorphism normalization converts from labelled embedding counts
    to the standard flag algebra product. (Thesis Definition 2.6) -/
noncomputable def localFlagProduct (σ : FlagType) (F F' : Flag σ) : FlagAlg σ :=
  let n := F.size + F'.size - σ.size
  if hn : σ.size ≤ n then
    ((flagAutCount σ F : ℝ) * (flagAutCount σ F' : ℝ))⁻¹ •
      (classesOfSize σ n hn).sum (fun cls =>
        Finsupp.single cls (jointInducedDensity σ F F' cls.out))
  else 0

/-! ### Iso-invariance of joint counts and products

These lemmas establish that `jointCount`, `jointInducedDensity`, `flagAutCount`,
and `localFlagProduct` respect flag isomorphism, which is needed to lift the
product to isomorphism classes `FlagClass σ`. -/

/-- The range of `mapIsoInv φ hφ e` equals the range of `e`:
    `range(e.toFun ∘ φ.symm) = range(e.toFun)` since `φ.symm` is surjective. -/
theorem InducedEmbedding.range_mapIsoInv {σ : FlagType} {F₁ F₂ G : Flag σ}
    (φ : F₁.graph ≃g F₂.graph) (hφ : ∀ i : Fin σ.size, φ (F₁.embedding i) = F₂.embedding i)
    (e : InducedEmbedding σ F₁ G) :
    Set.range (InducedEmbedding.mapIsoInv φ hφ e).toFun = Set.range e.toFun := by
  simp only [InducedEmbedding.mapIsoInv, InducedEmbedding.mapIso]
  ext x
  simp only [Set.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨φ.symm y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨φ y, by simp⟩

/-- The range of `mapIso φ hφ e` equals the range of `e`:
    `range(e.toFun ∘ φ) = range(e.toFun)` since `φ` is surjective. -/
theorem InducedEmbedding.range_mapIso {σ : FlagType} {F₁ F₂ G : Flag σ}
    (φ : F₁.graph ≃g F₂.graph) (hφ : ∀ i : Fin σ.size, φ (F₁.embedding i) = F₂.embedding i)
    (e : InducedEmbedding σ F₂ G) :
    Set.range (InducedEmbedding.mapIso φ hφ e).toFun = Set.range e.toFun := by
  simp only [InducedEmbedding.mapIso]
  ext x
  simp only [Set.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨φ y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨φ.symm y, by simp⟩

/-- Joint count is invariant under flag isomorphism on the left argument. -/
theorem jointCount_flagIso_left {σ : FlagType} {F₁ F₁' F₂ G : Flag σ}
    (h : FlagIso σ F₁ F₁') : jointCount σ F₁ F₂ G = jointCount σ F₁' F₂ G := by
  obtain ⟨φ, hφ⟩ := h
  unfold jointCount
  apply Fintype.card_congr
  have hfwd : ∀ (e : InducedEmbedding σ F₁ G),
      Set.range (InducedEmbedding.mapIsoInv φ hφ e).toFun = Set.range e.toFun :=
    InducedEmbedding.range_mapIsoInv φ hφ
  have hbwd : ∀ (e : InducedEmbedding σ F₁' G),
      Set.range (InducedEmbedding.mapIso φ hφ e).toFun = Set.range e.toFun :=
    InducedEmbedding.range_mapIso φ hφ
  refine {
    toFun := fun x =>
      let e₁ := x.val.1; let e₂ := x.val.2
      let hoverlap := x.property.1; let hcovering := x.property.2
      ⟨⟨InducedEmbedding.mapIsoInv φ hφ e₁, e₂⟩,
        fun i => by rw [show (InducedEmbedding.mapIsoInv φ hφ e₁, e₂).1 =
          InducedEmbedding.mapIsoInv φ hφ e₁ from rfl, hfwd]; exact hoverlap i,
        fun i => by rw [show (InducedEmbedding.mapIsoInv φ hφ e₁, e₂).1 =
          InducedEmbedding.mapIsoInv φ hφ e₁ from rfl, hfwd]; exact hcovering i⟩
    invFun := fun x =>
      let e₁' := x.val.1; let e₂ := x.val.2
      let hoverlap := x.property.1; let hcovering := x.property.2
      ⟨⟨InducedEmbedding.mapIso φ hφ e₁', e₂⟩,
        fun i => by rw [show (InducedEmbedding.mapIso φ hφ e₁', e₂).1 =
          InducedEmbedding.mapIso φ hφ e₁' from rfl, hbwd]; exact hoverlap i,
        fun i => by rw [show (InducedEmbedding.mapIso φ hφ e₁', e₂).1 =
          InducedEmbedding.mapIso φ hφ e₁' from rfl, hbwd]; exact hcovering i⟩
    left_inv := fun x => by
      apply Subtype.ext; apply Prod.ext
      · exact (InducedEmbedding.equivOfIso φ hφ).left_inv x.val.1
      · rfl
    right_inv := fun x => by
      apply Subtype.ext; apply Prod.ext
      · exact (InducedEmbedding.equivOfIso φ hφ).right_inv x.val.1
      · rfl
  }

/-- Joint count is invariant under flag isomorphism on the right argument. -/
theorem jointCount_flagIso_right {σ : FlagType} {F₁ F₂ F₂' G : Flag σ}
    (h : FlagIso σ F₂ F₂') : jointCount σ F₁ F₂ G = jointCount σ F₁ F₂' G := by
  rw [jointCount_comm, jointCount_flagIso_left h, jointCount_comm]

/-- Joint induced density is invariant under flag isomorphism on the left argument. -/
theorem jointInducedDensity_flagIso_left {σ : FlagType} {F₁ F₁' F₂ G : Flag σ}
    (h : FlagIso σ F₁ F₁') :
    jointInducedDensity σ F₁ F₂ G = jointInducedDensity σ F₁' F₂ G := by
  unfold jointInducedDensity
  rw [jointCount_flagIso_left h, flagIso_size_eq h]

/-- Joint induced density is invariant under flag isomorphism on the right argument. -/
theorem jointInducedDensity_flagIso_right {σ : FlagType} {F₁ F₂ F₂' G : Flag σ}
    (h : FlagIso σ F₂ F₂') :
    jointInducedDensity σ F₁ F₂ G = jointInducedDensity σ F₁ F₂' G := by
  unfold jointInducedDensity
  rw [jointCount_flagIso_right h, flagIso_size_eq h]

/-- Flag automorphism count is invariant under flag isomorphism.
    The bijection `IE σ F₁ F₁ ≃ IE σ F₂ F₂` is by conjugation: `e ↦ φ ∘ e ∘ φ⁻¹`. -/
theorem flagAutCount_flagIso {σ : FlagType} {F₁ F₂ : Flag σ}
    (h : FlagIso σ F₁ F₂) : flagAutCount σ F₁ = flagAutCount σ F₂ := by
  obtain ⟨φ, hφ⟩ := h
  unfold flagAutCount inducedCount
  apply Fintype.card_congr
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  -- Forward: e ↦ φ ∘ e ∘ φ⁻¹
  · exact {
      toFun := φ ∘ e.toFun ∘ φ.symm
      injective := (RelIso.injective φ).comp (e.injective.comp (RelIso.injective φ.symm))
      map_adj := fun u v hadj => by
        change F₂.graph.Adj (φ (e.toFun (φ.symm u))) (φ (e.toFun (φ.symm v)))
        exact φ.map_rel_iff'.mpr (e.map_adj _ _ (φ.symm.map_rel_iff'.mpr hadj))
      map_non_adj := fun u v hne hnadj => by
        change ¬F₂.graph.Adj (φ (e.toFun (φ.symm u))) (φ (e.toFun (φ.symm v)))
        intro hadj
        exact e.map_non_adj _ _ ((RelIso.injective φ.symm).ne hne)
          (fun h => hnadj (φ.symm.map_rel_iff'.mp h)) (φ.map_rel_iff'.mp hadj)
      compat := fun i => by
        change φ (e.toFun (φ.symm (F₂.embedding i))) = F₂.embedding i
        rw [show φ.symm (F₂.embedding i) = F₁.embedding i from by simp [← hφ i]]
        rw [e.compat, hφ] }
  -- Backward: e ↦ φ⁻¹ ∘ e ∘ φ
  · exact {
      toFun := φ.symm ∘ e.toFun ∘ φ
      injective := (RelIso.injective φ.symm).comp (e.injective.comp (RelIso.injective φ))
      map_adj := fun u v hadj => by
        change F₁.graph.Adj (φ.symm (e.toFun (φ u))) (φ.symm (e.toFun (φ v)))
        exact φ.symm.map_rel_iff'.mpr (e.map_adj _ _ (φ.map_rel_iff'.mpr hadj))
      map_non_adj := fun u v hne hnadj => by
        change ¬F₁.graph.Adj (φ.symm (e.toFun (φ u))) (φ.symm (e.toFun (φ v)))
        intro hadj
        exact e.map_non_adj _ _ ((RelIso.injective φ).ne hne)
          (fun h => hnadj (φ.map_rel_iff'.mp h)) (φ.symm.map_rel_iff'.mp hadj)
      compat := fun i => by
        change φ.symm (e.toFun (φ (F₁.embedding i))) = F₁.embedding i
        rw [hφ, e.compat, ← hφ i, RelIso.symm_apply_apply] }
  -- left_inv
  · cases e with | mk f _ _ _ _ =>
    simp only [InducedEmbedding.mk.injEq]
    funext x; simp
  -- right_inv
  · cases e with | mk f _ _ _ _ =>
    simp only [InducedEmbedding.mk.injEq]
    funext x; simp

/-- The local flag product is invariant under flag isomorphism on the left argument. -/
theorem localFlagProduct_flagIso_left {σ : FlagType} {F₁ F₁' F₂ : Flag σ}
    (h : FlagIso σ F₁ F₁') : localFlagProduct σ F₁ F₂ = localFlagProduct σ F₁' F₂ := by
  unfold localFlagProduct
  have hsz := flagIso_size_eq h
  have haut := flagAutCount_flagIso h
  simp only [hsz, haut]
  split_ifs with hn
  · congr 1
    apply Finset.sum_congr rfl
    intro cls _
    rw [jointInducedDensity_flagIso_left h]
  · rfl

/-- The local flag product is invariant under flag isomorphism on the right argument. -/
theorem localFlagProduct_flagIso_right {σ : FlagType} {F₁ F₂ F₂' : Flag σ}
    (h : FlagIso σ F₂ F₂') : localFlagProduct σ F₁ F₂ = localFlagProduct σ F₁ F₂' := by
  unfold localFlagProduct
  have hsz := flagIso_size_eq h
  have haut := flagAutCount_flagIso h
  simp only [hsz, haut]
  split_ifs with hn
  · congr 1
    apply Finset.sum_congr rfl
    intro cls _
    rw [jointInducedDensity_flagIso_right h]
  · rfl

/-- The local flag product is invariant under flag isomorphism on both arguments. -/
theorem localFlagProduct_flagIso {σ : FlagType} {F₁ F₁' F₂ F₂' : Flag σ}
    (h₁ : FlagIso σ F₁ F₁') (h₂ : FlagIso σ F₂ F₂') :
    localFlagProduct σ F₁ F₂ = localFlagProduct σ F₁' F₂' :=
  (localFlagProduct_flagIso_left h₁).trans (localFlagProduct_flagIso_right h₂)

/-! ### Product on isomorphism classes and bilinear extension -/

/-- Product on isomorphism classes: well-defined via iso-invariance. -/
noncomputable def localFlagProduct_class (σ : FlagType) (cls₁ cls₂ : FlagClass σ) :
    FlagAlg σ :=
  Quotient.lift₂ (fun F₁ F₂ => localFlagProduct σ F₁ F₂)
    (fun _ _ _ _ h₁ h₂ => localFlagProduct_flagIso h₁ h₂) cls₁ cls₂

theorem localFlagProduct_class_mk (σ : FlagType) (F₁ F₂ : Flag σ) :
    localFlagProduct_class σ (FlagClass.mk F₁) (FlagClass.mk F₂) =
      localFlagProduct σ F₁ F₂ := by
  simp [localFlagProduct_class, FlagClass.mk, Quotient.lift₂]

/-- Bilinear extension of the product to all of 𝓛^σ. -/
noncomputable def FlagAlg.mul (v w : FlagAlg σ) : FlagAlg σ :=
  v.sum (fun cls₁ c₁ =>
    w.sum (fun cls₂ c₂ =>
      (c₁ * c₂) • localFlagProduct_class σ cls₁ cls₂))

/-- Product on basis elements agrees with `localFlagProduct`. -/
theorem FlagAlg.mul_single (σ : FlagType) (F F' : Flag σ) :
    (FlagAlg.single σ F).mul (FlagAlg.single σ F') = localFlagProduct σ F F' := by
  simp only [FlagAlg.mul, FlagAlg.single]
  rw [Finsupp.sum_single_index (by simp)]
  rw [Finsupp.sum_single_index (by simp)]
  rw [localFlagProduct_class_mk]
  simp

/-! ## §2.2: Product Closure Theorem

The key theorem that makes the product well-defined within local flags.

### Counting inequalities

The proof relies on two counting facts about how positive joint density
lets us decompose copies of H into copies of F and F'. -/

/-- **Counting inequality for product closure** (thesis p.27, lines 310-330):
    If `p(F,F';H) > 0` then every σ-compatible copy of H in G decomposes into
    a σ-compatible copy of F and a σ-compatible copy of F' that overlap exactly
    on `im(θ_G)`. This decomposition is injective (different copies of H yield
    different pairs), so `c(H;G) ≤ c(F;G) · c(F';G)`.

    This is a combinatorial counting argument: `p(F,F';H) > 0` means there exist
    vertex subsets U, U' of H with U ∩ U' = im(θ_H), H[U] ≅ F, H[U'] ≅ F',
    and U ∪ U' = V(H). Any embedding H ↪ G restricts to embeddings F ↪ G[U']
    and F' ↪ G[U], and different H-embeddings give different pairs. -/
private theorem inducedCount_le_product_of_joint_pos (σ : FlagType)
    (F F' H G : Flag σ)
    (hp : jointInducedDensity σ F F' H > 0) :
    (inducedCount σ H G : ℝ) ≤ (inducedCount σ F G : ℝ) * (inducedCount σ F' G : ℝ) := by
  -- Step 1: Extract a witness pair (e₁, e₂) from jointInducedDensity > 0.
  have hjc_pos : (0 : ℝ) < (jointCount σ F F' H : ℝ) := by
    unfold jointInducedDensity at hp
    by_contra h; push_neg at h
    have h0 : (jointCount σ F F' H : ℝ) = 0 :=
      le_antisymm h (Nat.cast_nonneg _)
    rw [h0] at hp; simp at hp
  have hjc_nat : 0 < jointCount σ F F' H := Nat.cast_pos.mp hjc_pos
  unfold jointCount at hjc_nat
  rw [Fintype.card_pos_iff] at hjc_nat
  obtain ⟨⟨⟨e₁, e₂⟩, _, hcovering⟩⟩ := hjc_nat
  -- e₁ : InducedEmbedding σ F H, e₂ : InducedEmbedding σ F' H
  -- hcovering : ∀ i, i ∈ range e₁.toFun ∨ i ∈ range e₂.toFun
  -- Step 2: Reduce to ℕ inequality.
  suffices h : inducedCount σ H G ≤ inducedCount σ F G * inducedCount σ F' G by
    exact_mod_cast h
  -- Step 3: Build the injection φ ↦ (φ ∘ e₁, φ ∘ e₂).
  unfold inducedCount
  rw [← Fintype.card_prod]
  apply Fintype.card_le_of_injective
    (fun (φ : InducedEmbedding σ H G) =>
      (({ toFun := φ.toFun ∘ e₁.toFun
          injective := φ.injective.comp e₁.injective
          map_adj := fun u v hadj => φ.map_adj _ _ (e₁.map_adj u v hadj)
          map_non_adj := fun u v hne hnadj =>
            φ.map_non_adj _ _ (e₁.injective.ne hne)
              (e₁.map_non_adj u v hne hnadj)
          compat := fun i => by
            simp only [Function.comp_apply]
            rw [e₁.compat, φ.compat] } : InducedEmbedding σ F G),
       ({ toFun := φ.toFun ∘ e₂.toFun
          injective := φ.injective.comp e₂.injective
          map_adj := fun u v hadj => φ.map_adj _ _ (e₂.map_adj u v hadj)
          map_non_adj := fun u v hne hnadj =>
            φ.map_non_adj _ _ (e₂.injective.ne hne)
              (e₂.map_non_adj u v hne hnadj)
          compat := fun i => by
            simp only [Function.comp_apply]
            rw [e₂.compat, φ.compat] } : InducedEmbedding σ F' G)))
  -- Step 4: Prove injectivity using the covering condition.
  intro φ₁ φ₂ heq
  have h1 : φ₁.toFun ∘ e₁.toFun = φ₂.toFun ∘ e₁.toFun :=
    congr_arg InducedEmbedding.toFun (congr_arg Prod.fst heq)
  have h2 : φ₁.toFun ∘ e₂.toFun = φ₂.toFun ∘ e₂.toFun :=
    congr_arg InducedEmbedding.toFun (congr_arg Prod.snd heq)
  have hfun : φ₁.toFun = φ₂.toFun := by
    funext i
    rcases hcovering i with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [← hj]; exact congr_fun h1 j
    · rw [← hj]; exact congr_fun h2 j
  cases φ₁; cases φ₂; simp only at hfun; subst hfun; rfl

/-- **Density product bound** (thesis p.27): If p(F,F';H) > 0 then for any G and Δ:
    ρ(H;G) ≤ ρ(F;G) · ρ(F';G) · C(|H|-|σ|, |F|-|σ|)².

    The proof uses:
    1. c(H;G) ≤ c(F;G) · c(F';G) (counting inequality from joint decomposition)
    2. c(X;G) = ρ(X;G) · C(Δ, |X|-|σ|)  when  C(Δ, |X|-|σ|) > 0
    3. C(Δ,a)·C(Δ,b) ≤ C(a+b,a)² · C(Δ,a+b) (Vandermonde-type bound, `choose_mul_choose_le`)
    4. |H|-|σ| = (|F|-|σ|) + (|F'|-|σ|)  from p(F,F';H) > 0

    The bound C(|H|-|σ|, |F|-|σ|)² depends only on the flag sizes, not on G or Δ.

    Note: The thesis states C(h,f) rather than C(h,f)², but the stronger bound requires
    additional hypotheses on Δ (e.g., Δ(G) ≥ |G|-|σ|). The squared version holds
    unconditionally and suffices for downstream use (bounded density). -/
private lemma localDensity_le_product_of_joint_pos (σ : FlagType)
    (F F' H G : Flag σ) (Δ : GraphParam)
    (hp : jointInducedDensity σ F F' H > 0) :
    localDensity σ H G Δ ≤
      localDensity σ F G Δ * localDensity σ F' G Δ *
        ((Nat.choose (H.size - σ.size) (F.size - σ.size) : ℝ) ^ 2) := by
  set f := F.size - σ.size
  set f' := F'.size - σ.size
  set h := H.size - σ.size
  set n := Δ G.forget
  have hsize : h = f + f' := by
    have hjc_pos : 0 < jointCount σ F F' H := by
      unfold jointInducedDensity at hp; by_contra hle; push_neg at hle
      have := Nat.le_zero.mp hle
      simp [this] at hp
    unfold jointCount at hjc_pos; rw [Fintype.card_pos_iff] at hjc_pos
    obtain ⟨⟨⟨e₁, e₂⟩, hoverlap, hcovering⟩⟩ := hjc_pos
    set S₁ := Finset.univ.image e₁.toFun
    set S₂ := Finset.univ.image e₂.toFun
    set Sσ := Finset.univ.image H.embedding
    have hS₁ : S₁.card = F.size :=
      by rw [Finset.card_image_of_injective _ e₁.injective, Finset.card_univ, Fintype.card_fin]
    have hS₂ : S₂.card = F'.size :=
      by rw [Finset.card_image_of_injective _ e₂.injective, Finset.card_univ, Fintype.card_fin]
    have hSσ : Sσ.card = σ.size :=
      by rw [Finset.card_image_of_injective _ H.embedding.injective, Finset.card_univ,
          Fintype.card_fin]
    have hinter : S₁ ∩ S₂ = Sσ := by
      ext i; constructor
      · intro hi
        rw [Finset.mem_inter] at hi
        rw [Finset.mem_image] at hi ⊢
        simp only [Finset.mem_univ, true_and] at hi ⊢
        have hi₁ : i ∈ Set.range e₁.toFun := by obtain ⟨j, rfl⟩ := hi.1; exact ⟨j, rfl⟩
        have hi₂ : i ∈ Set.range e₂.toFun := by
          rw [Finset.mem_image] at hi; simp only [Finset.mem_univ, true_and] at hi
          obtain ⟨j, rfl⟩ := hi.2; exact ⟨j, rfl⟩
        obtain ⟨j, rfl⟩ := (hoverlap i).mp ⟨hi₁, hi₂⟩; exact ⟨j, rfl⟩
      · intro hi
        rw [Finset.mem_inter]
        rw [Finset.mem_image] at hi
        simp only [Finset.mem_univ, true_and] at hi
        have himσ : i ∈ Set.range H.embedding := by obtain ⟨j, rfl⟩ := hi; exact ⟨j, rfl⟩
        obtain ⟨h₁, h₂⟩ := (hoverlap i).mpr himσ
        constructor <;> rw [Finset.mem_image] <;> simp only [Finset.mem_univ, true_and]
        · exact ⟨h₁.choose, h₁.choose_spec⟩
        · exact ⟨h₂.choose, h₂.choose_spec⟩
    have hunion : S₁ ∪ S₂ = Finset.univ := by
      ext i; exact ⟨fun _ => Finset.mem_univ _, fun _ => by
        rw [Finset.mem_union]
        rcases hcovering i with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · left; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        · right; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    have hcard := Finset.card_union_add_card_inter S₁ S₂
    rw [hunion, hinter, Finset.card_univ, Fintype.card_fin, hS₁, hS₂, hSσ] at hcard
    have := F.hsize; have := F'.hsize; have := H.hsize; omega
  have hcount := inducedCount_le_product_of_joint_pos σ F F' H G hp
  unfold localDensity
  by_cases hdenom : Nat.choose n h = 0
  · rw [hdenom, Nat.cast_zero, div_zero]
    exact mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) (pow_nonneg (Nat.cast_nonneg _) 2)
  · have hh_le_n : h ≤ n := Nat.choose_ne_zero_iff.mp hdenom
    have hvander : Nat.choose n f * Nat.choose n f' ≤
        Nat.choose h f ^ 2 * Nat.choose n h := by
      rw [hsize]; exact choose_mul_choose_le f f' n (hsize ▸ hh_le_n)
    have hcombined_real : (inducedCount σ H G : ℝ) *
        ((Nat.choose n f : ℝ) * (Nat.choose n f' : ℝ)) ≤
        (inducedCount σ F G : ℝ) * (inducedCount σ F' G : ℝ) *
          (((Nat.choose h f : ℝ) ^ 2) * (Nat.choose n h : ℝ)) := by
      exact_mod_cast Nat.mul_le_mul (by exact_mod_cast hcount : inducedCount σ H G ≤
        inducedCount σ F G * inducedCount σ F' G) hvander
    rw [div_mul_div_comm, div_mul_eq_mul_div,
      div_le_div_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hdenom))
        (mul_pos (by exact_mod_cast Nat.choose_pos (by omega) : (0 : ℝ) < (Nat.choose n f : ℝ))
          (by exact_mod_cast Nat.choose_pos (by omega) : (0 : ℝ) < (Nat.choose n f' : ℝ)))]
    linarith

private theorem bounded_density_of_joint_pos (σ : FlagType)
    (F F' H : Flag σ) (𝒢 : GraphClass) (Δ : GraphParam)
    (hbF : IsBoundedDensity σ F 𝒢 Δ) (hbF' : IsBoundedDensity σ F' 𝒢 Δ)
    (hp : jointInducedDensity σ F F' H > 0) :
    IsBoundedDensity σ H 𝒢 Δ := by
  -- Extract constants from the bounded density hypotheses.
  obtain ⟨C_F, hCF_nn, hCF⟩ := hbF
  obtain ⟨C_F', hCF'_nn, hCF'⟩ := hbF'
  -- The uniform bound is C_F · C_F' · C(|H|-|σ|, |F|-|σ|)².
  set R := (Nat.choose (H.size - σ.size) (F.size - σ.size) : ℝ) with hR_def
  have hR_nn : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hR2_nn : (0 : ℝ) ≤ R ^ 2 := pow_nonneg hR_nn 2
  refine ⟨C_F * C_F' * R ^ 2,
    mul_nonneg (mul_nonneg hCF_nn hCF'_nn) hR2_nn, fun G hG => ?_⟩
  -- Apply the density product bound.
  have hprod : localDensity σ F G Δ * localDensity σ F' G Δ ≤ C_F * C_F' :=
    mul_le_mul (hCF G hG) (hCF' G hG)
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (le_trans (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hCF G hG))
  calc localDensity σ H G Δ
      ≤ localDensity σ F G Δ * localDensity σ F' G Δ * R ^ 2 :=
        localDensity_le_product_of_joint_pos σ F F' H G Δ hp
    _ ≤ C_F * C_F' * R ^ 2 :=
        mul_le_mul_of_nonneg_right hprod hR2_nn

/-! ### Helper: Extracting witness decomposition from positive joint density

From `jointInducedDensity sigma F F' H > 0` we extract embeddings `e1 : F -> H`,
`e2 : F' -> H` that cover H and overlap exactly on `im(theta_H)`. We then
determine which side contains a given vertex of H. -/

/-- Extract covering embeddings from positive joint density. -/
private theorem joint_pos_witness (σ : FlagType) (F F' H : Flag σ)
    (hp : jointInducedDensity σ F F' H > 0) :
    ∃ (e₁ : InducedEmbedding σ F H) (e₂ : InducedEmbedding σ F' H),
      (∀ i : Fin H.size,
        (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
          i ∈ Set.range H.embedding) ∧
      (∀ i : Fin H.size, i ∈ Set.range e₁.toFun ∨ i ∈ Set.range e₂.toFun) := by
  have hjc_nat := jointCount_pos_of_jointInducedDensity_pos σ F F' H hp
  unfold jointCount at hjc_nat
  rw [Fintype.card_pos_iff] at hjc_nat
  obtain ⟨⟨⟨e₁, e₂⟩, hoverlap, hcovering⟩⟩ := hjc_nat
  exact ⟨e₁, e₂, hoverlap, hcovering⟩

/-- From covering, every vertex of H is in the range of e1 or e2. Combined with the
    fact that `ext.vertex` is NOT in `im(theta_H)` (it's unlabelled), the overlap
    condition `(in e1 ∧ in e2) ↔ in theta_H` shows that ext.vertex is in exactly
    one of range e1, range e2 (exclusively). -/
private theorem vertex_in_exactly_one_side (σ : FlagType) (F F' H : Flag σ)
    (e₁ : InducedEmbedding σ F H) (e₂ : InducedEmbedding σ F' H)
    (hoverlap : ∀ i : Fin H.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range H.embedding)
    (hcovering : ∀ i : Fin H.size,
      i ∈ Set.range e₁.toFun ∨ i ∈ Set.range e₂.toFun)
    (v : Fin H.size) (hv : v ∉ Set.range H.embedding) :
    (v ∈ Set.range e₁.toFun ∧ v ∉ Set.range e₂.toFun) ∨
    (v ∉ Set.range e₁.toFun ∧ v ∈ Set.range e₂.toFun) := by
  have hnot_both : ¬(v ∈ Set.range e₁.toFun ∧ v ∈ Set.range e₂.toFun) := by
    intro hboth; exact hv ((hoverlap v).mp hboth)
  rcases hcovering v with h1 | h2
  · left; exact ⟨h1, fun h2 => hnot_both ⟨h1, h2⟩⟩
  · right; exact ⟨fun h1 => hnot_both ⟨h1, h2⟩, h2⟩

/-! ### Decomposition at label extensions

The thesis (p.27, lines 344-356) proves that the decomposition V(H) = U ∪ U'
lifts through label extensions. The argument uses a mixed-level counting bound:
c(H^v; G) ≤ c(F^v; G) · c(F'; G), where F^v is a σ'-flag (from labelling v in F)
and F' remains a σ-flag. This is axiomatized because:

1. **Dependent type transport**: The extended types `ext.extendedType` (from H)
   and `F_ext.extendedType` (from F) are provably but not definitionally equal.
   Transporting `Flag` and `IsLocalFlag` across this equality hits Lean's
   dependent type limitations (the motive for rewriting involves both the type
   and flags of that type simultaneously).

2. **Mixed-level counting**: The thesis bounds c(H^v; G) using c(F^v; G) at the
   σ'-level and c(F'; G) at the σ-level. Our `jointInducedDensity` requires
   both flags at the same type level. Formalizing the mixed-level argument would
   require either a new counting framework or restructuring `product_closure_aux`.

3. **B's locality**: In the σ'-decomposition of H^v, B = H[U' ∪ {v}] — an
   "augmentation" of F' by one vertex. Proving B is local requires a separate
   induction argument (bounded density from F' + one vertex contributes O(Δ)).
   This is captured by `augmented_local_flag` below. -/

/-- **Augmentation preserves locality** (thesis p.27, implicit in product closure proof):
    If F' is a local σ-flag and B is a flag at type σ' (with |σ'| = |σ| + 1,
    |B| = |F'| + 1) whose graph extends F'.graph by one vertex and whose
    labelling extends F'.embedding, then B is local at σ'.

    The extra hypothesis `hNewLabelled` ensures the new σ'-label (the last one)
    points to the new vertex (index F'.size in B). This is satisfied at the
    unique call site where B is constructed with `bEmbMap (Fin.last σ.size) = Fin.last F'.size`.

    Proof: By strong induction on F'.unlabelledSize.
    - IsBoundedDensity: each σ'-embedding of B into G restricts (dropping the
      new vertex, which is labelled and hence fixed) to a σ-embedding of F'
      into G|_σ. This injection gives localDensity σ' B G ≤ localDensity σ F' G|_σ ≤ C.
    - Extensions: for each label extension ext' of B at unlabelled vertex v
      (with v.val < F'.size since F'.size is labelled), the extension of F'
      at the corresponding vertex v' is local (from hF'.extensions). Applying
      the IH (with a label swap to match the embedding order) gives locality
      of ext'.extendedFlag. -/
private theorem augmented_local_flag_aux (n : ℕ) :
    ∀ (σ : FlagType) (F' : Flag σ) (𝒢 : GraphClass) (Δ : GraphParam),
    IsLocalFlag σ F' 𝒢 Δ →
    F'.unlabelledSize ≤ n →
    ∀ (σ' : FlagType) (B : Flag σ')
      (hσ' : σ'.size = σ.size + 1) (hB : B.size = F'.size + 1),
    (∀ i j : Fin F'.size, F'.graph.Adj i j ↔
      B.graph.Adj (Fin.cast hB.symm (Fin.castSucc i))
                  (Fin.cast hB.symm (Fin.castSucc j))) →
    (∀ k : Fin σ.size,
      (B.embedding (Fin.cast hσ'.symm (Fin.castSucc k))).val = (F'.embedding k).val) →
    (B.embedding (Fin.cast hσ'.symm (Fin.last σ.size))).val = F'.size →
    IsLocalFlag σ' B 𝒢 Δ := by
  induction n with
  | zero =>
    intro σ F' 𝒢 Δ hF' hn σ' B hσ' hB hadj hcompat hNewLabelled
    have hBs : B.size = σ'.size := by
      have := Nat.le_antisymm (by unfold Flag.unlabelledSize at hn; omega) F'.hsize; omega
    have hsurj := B.embedding.injective.surjective_of_finite (finCongr hBs.symm)
    apply IsLocalFlag.intro
    · refine ⟨1, le_of_lt one_pos, fun G hG => ?_⟩
      unfold localDensity
      rw [show B.size - σ'.size = 0 from by omega, Nat.choose_zero_right, Nat.cast_one, div_one]
      suffices h : Fintype.card (InducedEmbedding σ' B G) ≤ 1 by exact_mod_cast h
      rw [Fintype.card_le_one_iff_subsingleton]; constructor; intro e₁ e₂
      have : e₁.toFun = e₂.toFun := by
        funext x; obtain ⟨i, hi⟩ := hsurj x; rw [← hi, e₁.compat, e₂.compat]
      cases e₁; cases e₂; simpa [InducedEmbedding.mk.injEq] using this
    · intro ext'; exact absurd (hsurj ext'.vertex) ext'.unlabelled
  | succ n ih =>
    intro σ F' 𝒢 Δ hF' hn σ' B hσ' hB hadj hcompat hNewLabelled
    apply IsLocalFlag.intro
    · obtain ⟨C, hC0, hCbound⟩ := hF'.bounded
      refine ⟨C, hC0, fun G hG => ?_⟩
      let G_σ_emb_fun : Fin σ.size → Fin G.size :=
        fun k => G.embedding (Fin.cast hσ'.symm (Fin.castSucc k))
      have G_σ_emb_adj : ∀ a b : Fin σ.size,
          σ.graph.Adj a b ↔ G.graph.Adj (G_σ_emb_fun a) (G_σ_emb_fun b) := by
        intro a b
        calc σ.graph.Adj a b
            ↔ F'.graph.Adj (F'.embedding a) (F'.embedding b) := F'.embedding.map_rel_iff'.symm
          _ ↔ B.graph.Adj (Fin.cast hB.symm (Fin.castSucc (F'.embedding a)))
                          (Fin.cast hB.symm (Fin.castSucc (F'.embedding b))) := hadj _ _
          _ ↔ B.graph.Adj (B.embedding (Fin.cast hσ'.symm (Fin.castSucc a)))
                          (B.embedding (Fin.cast hσ'.symm (Fin.castSucc b))) := by
              rw [show B.embedding (Fin.cast hσ'.symm (Fin.castSucc a)) =
                  Fin.cast hB.symm (Fin.castSucc (F'.embedding a)) from
                Fin.ext (by simp only [Fin.val_cast, Fin.val_castSucc]; exact hcompat a),
                show B.embedding (Fin.cast hσ'.symm (Fin.castSucc b)) =
                  Fin.cast hB.symm (Fin.castSucc (F'.embedding b)) from
                Fin.ext (by simp only [Fin.val_cast, Fin.val_castSucc]; exact hcompat b)]
          _ ↔ σ'.graph.Adj (Fin.cast hσ'.symm (Fin.castSucc a))
                           (Fin.cast hσ'.symm (Fin.castSucc b)) := B.embedding.map_rel_iff'
          _ ↔ G.graph.Adj (G.embedding (Fin.cast hσ'.symm (Fin.castSucc a)))
                           (G.embedding (Fin.cast hσ'.symm (Fin.castSucc b))) :=
              G.embedding.map_rel_iff'.symm
      let G_σ : Flag σ :=
        { size := G.size
          graph := G.graph
          embedding :=
            ⟨⟨G_σ_emb_fun, fun a b hab =>
              (Fin.castSucc_injective _) ((Fin.cast_injective _)
                (G.embedding.injective hab))⟩,
              fun {a b} => (G_σ_emb_adj a b).symm⟩
          hsize := by have := G.hsize; omega }
      have hG_σ_forget : G_σ.forget = G.forget := rfl
      have h_inj_count : inducedCount σ' B G ≤ inducedCount σ F' G_σ := by
        unfold inducedCount
        apply Fintype.card_le_of_injective
          (fun (e : InducedEmbedding σ' B G) =>
            (⟨fun i => e.toFun (Fin.cast hB.symm (Fin.castSucc i)),
              fun {a b} hab => by
                have h1 : Fin.cast hB.symm (Fin.castSucc a) = Fin.cast hB.symm (Fin.castSucc b) :=
                  e.injective hab
                exact Fin.ext (by simp only [Fin.ext_iff] at h1; exact h1),
              fun u v huv => e.map_adj _ _ ((hadj u v).mp huv),
              fun u v hne hnadj => by
                apply e.map_non_adj
                · intro h; apply hne; exact Fin.ext (by simp only [Fin.ext_iff] at h; exact h)
                · exact fun h => hnadj ((hadj u v).mpr h),
              fun k => by
                change e.toFun (Fin.cast hB.symm (Fin.castSucc (F'.embedding k))) =
                  G.embedding (Fin.cast hσ'.symm (Fin.castSucc k))
                rw [show Fin.cast hB.symm (Fin.castSucc (F'.embedding k)) =
                    B.embedding (Fin.cast hσ'.symm (Fin.castSucc k)) from
                  Fin.ext (by simp only [Fin.val_cast, Fin.val_castSucc]
                              exact (hcompat k).symm)]
                exact e.compat _⟩
              : InducedEmbedding σ F' G_σ))
        intro e₁ e₂ h
        have h_eq : e₁.toFun = e₂.toFun := by
          funext x; by_cases hx : x.val < F'.size
          · rw [show x = Fin.cast hB.symm (Fin.castSucc ⟨x.val, hx⟩) from Fin.ext (by simp)]
            exact congr_fun (congr_arg InducedEmbedding.toFun h) ⟨x.val, hx⟩
          · rw [show x = B.embedding (Fin.cast hσ'.symm (Fin.last σ.size)) from
              Fin.ext (by rw [hNewLabelled]; have := x.isLt; simp only [hB] at this; omega),
              e₁.compat, e₂.compat]
        cases e₁; cases e₂; simpa [InducedEmbedding.mk.injEq] using h_eq
      calc localDensity σ' B G Δ
            = (inducedCount σ' B G : ℝ) / (Nat.choose (Δ G.forget) (B.size - σ'.size) : ℝ) := rfl
          _ ≤ (inducedCount σ F' G_σ : ℝ) / (Nat.choose (Δ G.forget) (B.size - σ'.size) : ℝ) :=
              div_le_div_of_nonneg_right (Nat.cast_le.mpr h_inj_count) (Nat.cast_nonneg _)
          _ = (inducedCount σ F' G_σ : ℝ) /
              (Nat.choose (Δ G_σ.forget) (F'.size - σ.size) : ℝ) := by
              rw [hG_σ_forget,
                  show B.size - σ'.size = F'.size - σ.size from by omega]
          _ = localDensity σ F' G_σ Δ := rfl
          _ ≤ C := hCbound G_σ (hG_σ_forget ▸ hG)
    · intro ext'
      have hv_lt : ext'.vertex.val < F'.size := by
        have : ext'.vertex.val ≠ F'.size := fun heq =>
          ext'.unlabelled ⟨Fin.cast hσ'.symm (Fin.last σ.size),
            Fin.ext (by simp [hNewLabelled, heq])⟩
        have := ext'.vertex.isLt; simp only [hB] at this; omega
      let ext_F' : LabelExtension σ F' :=
        ⟨⟨ext'.vertex.val, hv_lt⟩, fun ⟨k, hk⟩ => ext'.unlabelled
          ⟨Fin.cast hσ'.symm (Fin.castSucc k), Fin.ext (by
            rw [hcompat k]; exact congr_arg Fin.val hk)⟩⟩
      have h_unl_le : ext_F'.extendedFlag.unlabelledSize ≤ n := by
        unfold Flag.unlabelledSize at hn ⊢
        simp only [LabelExtension.extendedFlag, LabelExtension.extendedType]; omega
      have h_ext_sz : ext'.extendedType.size = σ.size + 2 := by
        simp only [LabelExtension.extendedType, hσ']
      have h_extF_sz : ext_F'.extendedType.size = σ.size + 1 := by
        simp only [LabelExtension.extendedType]
      let π : Equiv.Perm (Fin ext'.extendedType.size) :=
        Equiv.swap (⟨σ.size, by omega⟩) (⟨σ.size + 1, by omega⟩)
      have h_rel_local :
          IsLocalFlag (ext'.extendedType.relabel π) (ext'.extendedFlag.relabel π) 𝒢 Δ := by
        have ih_hσ' : (ext'.extendedType.relabel π).size = ext_F'.extendedType.size + 1 := by
          simp only [FlagType.relabel]; omega
        have ih_hB : (ext'.extendedFlag.relabel π).size = ext_F'.extendedFlag.size + 1 := by
          simp only [Flag.relabel]; exact hB
        have ih_hadj : ∀ i j : Fin ext_F'.extendedFlag.size,
            ext_F'.extendedFlag.graph.Adj i j ↔
            (ext'.extendedFlag.relabel π).graph.Adj
              (Fin.cast ih_hB.symm (Fin.castSucc i))
              (Fin.cast ih_hB.symm (Fin.castSucc j)) := fun i j => by
          simp only [Flag.relabel, LabelExtension.extendedFlag]; exact hadj i j
        have ih_hcompat : ∀ k : Fin ext_F'.extendedType.size,
            ((ext'.extendedFlag.relabel π).embedding
              (Fin.cast ih_hσ'.symm (Fin.castSucc k))).val =
            (ext_F'.extendedFlag.embedding k).val := by
          intro k
          simp only [Flag.relabel_embedding_apply]
          obtain ⟨m, rfl⟩ | rfl := k.eq_castSucc_or_eq_last
          · rw [Equiv.swap_apply_of_ne_of_ne
                (by intro h; have := congrArg Fin.val h; simp at this; omega)
                (by intro h; have := congrArg Fin.val h; simp at this; omega)]
            change (ext'.vertexMap ⟨m.val, by omega⟩).val =
              (ext_F'.vertexMap (Fin.castSucc m)).val
            rw [show (⟨m.val, (by omega : m.val < σ'.size + 1)⟩ : Fin (σ'.size + 1)) =
                Fin.castSucc (⟨m.val, by omega⟩ : Fin σ'.size) from Fin.ext (by simp),
                LabelExtension.vertexMap, Fin.lastCases_castSucc,
                show (⟨m.val, (by omega : m.val < σ'.size)⟩ : Fin σ'.size) =
                Fin.cast hσ'.symm (Fin.castSucc m) from Fin.ext (by simp),
                LabelExtension.vertexMap, Fin.lastCases_castSucc]
            exact hcompat m
          · rw [show π (Fin.cast ih_hσ'.symm (Fin.castSucc (Fin.last σ.size))) =
                (⟨σ.size + 1, by omega⟩ : Fin ext'.extendedType.size) from by
              rw [show (Fin.cast ih_hσ'.symm (Fin.castSucc (Fin.last σ.size)) :
                  Fin ext'.extendedType.size) = ⟨σ.size, by omega⟩ from Fin.ext (by simp)]
              exact Equiv.swap_apply_left _ _]
            change (ext'.vertexMap (⟨σ.size + 1, by omega⟩ : Fin (σ'.size + 1))).val =
              (ext_F'.vertexMap (Fin.last σ.size)).val
            rw [show (⟨σ.size + 1, (by omega : σ.size + 1 < σ'.size + 1)⟩ :
                Fin (σ'.size + 1)) = Fin.last σ'.size from Fin.ext (by simp [hσ']),
                LabelExtension.vertexMap, Fin.lastCases_last,
                LabelExtension.vertexMap, Fin.lastCases_last]
        have ih_hNewLabelled :
            ((ext'.extendedFlag.relabel π).embedding
              (Fin.cast ih_hσ'.symm (Fin.last ext_F'.extendedType.size))).val =
            ext_F'.extendedFlag.size := by
          simp only [Flag.relabel_embedding_apply]
          rw [show π (Fin.cast ih_hσ'.symm (Fin.last ext_F'.extendedType.size)) =
              (⟨σ.size, by omega⟩ : Fin ext'.extendedType.size) from by
            rw [show (Fin.cast ih_hσ'.symm (Fin.last ext_F'.extendedType.size) :
                Fin ext'.extendedType.size) = ⟨σ.size + 1, by omega⟩ from by
              simp [Fin.ext_iff, hσ']]
            exact Equiv.swap_apply_right _ _]
          change (ext'.vertexMap (⟨σ.size, by omega⟩ : Fin (σ'.size + 1))).val = F'.size
          rw [show (⟨σ.size, (by omega : σ.size < σ'.size + 1)⟩ : Fin (σ'.size + 1)) =
              Fin.castSucc (⟨σ.size, by omega⟩ : Fin σ'.size) from Fin.ext (by simp),
              LabelExtension.vertexMap, Fin.lastCases_castSucc,
              show (⟨σ.size, (by omega : σ.size < σ'.size)⟩ : Fin σ'.size) =
              Fin.cast hσ'.symm (Fin.last σ.size) from Fin.ext (by simp)]
          exact hNewLabelled
        exact ih ext_F'.extendedType ext_F'.extendedFlag 𝒢 Δ (hF'.extensions ext_F') h_unl_le
          (ext'.extendedType.relabel π) (ext'.extendedFlag.relabel π)
          ih_hσ' ih_hB ih_hadj ih_hcompat ih_hNewLabelled
      exact IsLocalFlag_flagIso_gen
        ((ext'.extendedFlag.relabel π).relabel π.symm).unlabelledSize
        (by unfold FlagType.relabel; congr 1
            change (ext'.extendedType.graph.comap π).comap π.symm = ext'.extendedType.graph
            rw [SimpleGraph.comap_comap,
                show (⇑π ∘ ⇑π.symm) = id from funext π.apply_symm_apply,
                SimpleGraph.comap_id])
        le_rfl (RelIso.refl _)
        (fun i => by
          change ((ext'.extendedFlag.relabel π).relabel π.symm).embedding i =
            ext'.extendedFlag.embedding (Fin.cast _ i)
          simp only [Flag.relabel_embedding_apply]
          congr 1; ext; exact congrArg Fin.val (π.apply_symm_apply i))
        (@IsLocalFlag_relabel _ (ext'.extendedType.relabel π)
          (ext'.extendedFlag.relabel π) 𝒢 Δ π.symm le_rfl h_rel_local)

theorem augmented_local_flag
    (σ : FlagType) (F' : Flag σ) (𝒢 : GraphClass) (Δ : GraphParam)
    (hF' : IsLocalFlag σ F' 𝒢 Δ)
    (σ' : FlagType) (B : Flag σ')
    (hσ' : σ'.size = σ.size + 1) (hB : B.size = F'.size + 1)
    -- B restricted to first F'.size vertices recovers F'.graph
    (hadj : ∀ i j : Fin F'.size,
      F'.graph.Adj i j ↔
        B.graph.Adj (Fin.cast hB.symm (Fin.castSucc i))
                    (Fin.cast hB.symm (Fin.castSucc j)))
    -- B's first σ.size labels correspond to F'.embedding
    (hcompat : ∀ k : Fin σ.size,
      (B.embedding (Fin.cast hσ'.symm (Fin.castSucc k))).val = (F'.embedding k).val)
    -- The new σ'-label points to the new vertex (index F'.size)
    (hNewLabelled : (B.embedding (Fin.cast hσ'.symm (Fin.last σ.size))).val = F'.size) :
    IsLocalFlag σ' B 𝒢 Δ :=
  augmented_local_flag_aux F'.unlabelledSize σ F' 𝒢 Δ hF' le_rfl σ' B hσ' hB
    hadj hcompat hNewLabelled

/-- **Decomposition of label extensions** (thesis p.27, lines 344-356).
    The combinatorial core of the label extension argument. Given `p(F,F';H) > 0`
    at the σ-level and a label extension of H at unlabelled vertex v, the thesis
    shows that the decomposition V(H) = U ∪ U' (with U ∩ U' = im(θ_H)) can be
    lifted to the extended type σ' = ext.extendedType.

    WLOG v ∈ U \ im(θ_H). Define:
    - A = F^v: the label extension of F at v's preimage in U, a σ'-flag of size |F|
    - B = H[U' ∪ {v}]: F' augmented by vertex v (now labelled), a σ'-flag of size |F'|+1

    Then:
    1. `p_{σ'}(A, B; H^v) > 0`: the covering U ∪ U' = V(H) lifts to
       V(H^v), and the overlap U ∩ U' = im(θ_H) lifts to
       U ∩ (U' ∪ {v}) = im(θ_H) ∪ {v} = im(θ_{σ'}). The witness embeddings
       e₁ (restricted/transported for A) and bMap e₂ v (for B) satisfy
       the jointCount conditions at the σ'-level.
    2. A is local: from `hF.extensions` applied to the label extension of F at
       e₁⁻¹(v), transported via the type equality extF.extendedType = ext.extendedType
       (proved from e₁ being an induced embedding).
    3. B is local: copies of B in a σ'-flag G' project to copies of F' in G'_σ
       (forgetting the extra label v), giving bounded density from hF'. Extensions
       of B have strictly fewer unlabelled vertices and the argument recurses.

    The WLOG is justified by the symmetry `p(F,F';H) = p(F',F;H)`.

    **Core construction** (`decomposition_at_extension_core`): when
    `ext.vertex ∈ range e₁.toFun \ range H.embedding`, we construct A (label extension of F)
    and B (augmentation of F') at the extended type. -/
private theorem decomposition_at_extension_core (σ : FlagType)
    (F F' H : Flag σ) (𝒢 : GraphClass) (Δ : GraphParam)
    (hF : IsLocalFlag σ F 𝒢 Δ) (hF' : IsLocalFlag σ F' 𝒢 Δ)
    (hp : jointInducedDensity σ F F' H > 0)
    (ext : LabelExtension σ H)
    (e₁ : InducedEmbedding σ F H) (e₂ : InducedEmbedding σ F' H)
    (hoverlap : ∀ i : Fin H.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range H.embedding)
    (hcovering : ∀ i : Fin H.size,
      i ∈ Set.range e₁.toFun ∨ i ∈ Set.range e₂.toFun)
    (hv_in_e1 : ext.vertex ∈ Set.range e₁.toFun)
    (hv_not_e2 : ext.vertex ∉ Set.range e₂.toFun) :
    ∃ (A B : Flag ext.extendedType),
      jointInducedDensity ext.extendedType A B ext.extendedFlag > 0 ∧
      IsLocalFlag ext.extendedType A 𝒢 Δ ∧
      IsLocalFlag ext.extendedType B 𝒢 Δ := by
  -- Step 1: u = e₁⁻¹(ext.vertex), which is unlabelled in F
  obtain ⟨u, hu⟩ := hv_in_e1
  have hu_unlab : u ∉ Set.range F.embedding := fun ⟨i, hi⟩ =>
    ext.unlabelled ⟨i, by rw [← e₁.compat i, hi, hu]⟩
  let extF : LabelExtension σ F := ⟨u, hu_unlab⟩
  -- Step 2: e₁ ∘ extF.vertexMap = ext.vertexMap
  have hcomp : ∀ i : Fin (σ.size + 1),
      e₁.toFun (extF.vertexMap i) = ext.vertexMap i := by
    intro i; obtain (⟨j, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
    · simp only [LabelExtension.vertexMap, Fin.lastCases_castSucc]; exact e₁.compat j
    · simp only [LabelExtension.vertexMap, Fin.lastCases_last]; exact hu
  -- Step 3: Type equality extF.extendedType = ext.extendedType
  have htype_eq : extF.extendedType = ext.extendedType := by
    simp only [LabelExtension.extendedType]; congr 1; ext a b
    change F.graph.Adj (extF.vertexMap a) (extF.vertexMap b) ↔
      H.graph.Adj (ext.vertexMap a) (ext.vertexMap b)
    constructor
    · intro h; have := e₁.map_adj _ _ h; rwa [hcomp a, hcomp b] at this
    · intro h
      by_contra hna
      exact e₁.map_non_adj _ _
        (fun heq => h.ne (by have := congrArg e₁.toFun heq; rwa [hcomp a, hcomp b] at this))
        hna (by rwa [hcomp a, hcomp b])
  -- == Step 4: Construct A and prove locality ==
  -- We work at extF.extendedType level. A = extF.extendedFlag, transported to ext.extendedType.
  -- Since the goal is existential, we use `suffices` to work at extF.extendedType.
  -- Step 4: Construct A (label extension of F, transported to ext.extendedType)
  have aEmb_iff : ∀ a b : Fin (σ.size + 1),
      ext.extendedType.graph.Adj a b ↔ F.graph.Adj (extF.vertexMap a) (extF.vertexMap b) := by
    intro a b
    change H.graph.Adj (ext.vertexMap a) (ext.vertexMap b) ↔ _
    rw [← hcomp a, ← hcomp b]
    exact ⟨fun h => by_contra fun hna =>
      e₁.map_non_adj _ _ (fun heq => h.ne (congrArg e₁.toFun heq)) hna h,
      e₁.map_adj _ _⟩
  let aEmb : ext.extendedType.graph ↪g F.graph :=
    { toEmbedding := extF.vertexMapEmb
      map_rel_iff' := fun {a b} => (aEmb_iff a b).symm }
  let A : Flag ext.extendedType :=
    ⟨F.size, F.graph, aEmb, by change σ.size + 1 ≤ F.size; exact extF.size_le⟩
  -- A is local: identity iso transport from extF.extendedFlag
  have hA_local : IsLocalFlag ext.extendedType A 𝒢 Δ :=
    IsLocalFlag_flagIso_gen A.unlabelledSize htype_eq le_rfl
      { toEquiv := Equiv.refl _, map_rel_iff' := Iff.rfl }
      (fun i => by
        change (Equiv.refl _) (extF.vertexMap i) =
          extF.vertexMap (Fin.cast (congrArg FlagType.size htype_eq) i)
        simp only [Equiv.refl_apply]; congr 1)
      (hF.extensions extF)
  -- Step 5: Construct B = H[im(e₂) ∪ {ext.vertex}]
  let bMap : Fin (F'.size + 1) → Fin H.size :=
    Fin.lastCases ext.vertex (fun j => e₂.toFun j)
  have bMap_inj : Function.Injective bMap := by
    intro a b hab
    obtain (⟨i, rfl⟩ | rfl) := a.eq_castSucc_or_eq_last
    · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
      · simp only [bMap, Fin.lastCases_castSucc] at hab
        exact congr_arg Fin.castSucc (e₂.injective hab)
      · simp only [bMap, Fin.lastCases_castSucc, Fin.lastCases_last] at hab
        exact absurd ⟨i, hab⟩ hv_not_e2
    · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
      · simp only [bMap, Fin.lastCases_castSucc, Fin.lastCases_last] at hab
        exact absurd ⟨j, hab.symm⟩ hv_not_e2
      · rfl
  let bEmbMap : Fin (σ.size + 1) → Fin (F'.size + 1) :=
    Fin.lastCases (Fin.last F'.size) (fun j => Fin.castSucc (F'.embedding j))
  have bEmbMap_inj : Function.Injective bEmbMap := by
    intro a b hab
    obtain (⟨i, rfl⟩ | rfl) := a.eq_castSucc_or_eq_last
    · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
      · simp only [bEmbMap, Fin.lastCases_castSucc, Fin.castSucc_inj] at hab
        exact congr_arg Fin.castSucc (F'.embedding.injective hab)
      · simp only [bEmbMap, Fin.lastCases_castSucc, Fin.lastCases_last] at hab
        exact absurd hab (Fin.castSucc_lt_last _).ne
    · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
      · simp only [bEmbMap, Fin.lastCases_castSucc, Fin.lastCases_last] at hab
        exact absurd hab.symm (Fin.castSucc_lt_last _).ne
      · rfl
  have bMap_bEmb_eq : ∀ i : Fin (σ.size + 1),
      bMap (bEmbMap i) = ext.vertexMap i := by
    intro i; obtain (⟨j, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
    · simp only [bEmbMap, bMap, LabelExtension.vertexMap, Fin.lastCases_castSucc]; exact e₂.compat j
    · simp only [bEmbMap, bMap, LabelExtension.vertexMap, Fin.lastCases_last]
  let bEmb : ext.extendedType.graph ↪g (H.graph.comap bMap) :=
    { toEmbedding := ⟨bEmbMap, bEmbMap_inj⟩
      map_rel_iff' := fun {a b} => by
        simp only [LabelExtension.extendedType, SimpleGraph.comap_adj, Function.Embedding.coeFn_mk]
        rw [bMap_bEmb_eq a, bMap_bEmb_eq b] }
  let B : Flag ext.extendedType :=
    ⟨F'.size + 1, H.graph.comap bMap, bEmb,
     by change σ.size + 1 ≤ F'.size + 1; exact Nat.add_le_add_right F'.hsize 1⟩
  -- Step 6: B is local (augmentation of F' by one vertex)
  have hB_local : IsLocalFlag ext.extendedType B 𝒢 Δ :=
    augmented_local_flag σ F' 𝒢 Δ hF' ext.extendedType B rfl rfl
      (fun i j => by
        change F'.graph.Adj i j ↔
          (H.graph.comap bMap).Adj (Fin.castSucc i) (Fin.castSucc j)
        simp only [SimpleGraph.comap_adj, bMap, Fin.lastCases_castSucc]
        exact ⟨e₂.map_adj i j, fun h => by_contra fun hna =>
          e₂.map_non_adj i j (fun heq => h.ne (congrArg e₂.toFun heq)) hna h⟩)
      (fun k => by
        change (bEmbMap (Fin.castSucc k)).val = (F'.embedding k).val
        simp only [bEmbMap, Fin.lastCases_castSucc, Fin.val_castSucc])
      (by change (bEmbMap (Fin.last σ.size)).val = F'.size
          simp only [bEmbMap, Fin.lastCases_last, Fin.val_last])
  -- Step 7: Joint density p(A, B; ext.extendedFlag) > 0
  -- Witness embeddings eA (via e₁) and eB (via bMap)
  let eA : InducedEmbedding ext.extendedType A ext.extendedFlag :=
    { toFun := e₁.toFun, injective := e₁.injective
      map_adj := fun u v h => e₁.map_adj u v h
      map_non_adj := fun u v hne hnadj => e₁.map_non_adj u v hne hnadj
      compat := fun i => by change e₁.toFun (extF.vertexMap i) = ext.vertexMap i; exact hcomp i }
  let eB : InducedEmbedding ext.extendedType B ext.extendedFlag :=
    { toFun := bMap, injective := bMap_inj
      map_adj := fun _ _ h => h
      map_non_adj := fun _ _ _ hnadj => hnadj
      compat := fun i => by change bMap (bEmbMap i) = ext.vertexMap i; exact bMap_bEmb_eq i }
  -- Range characterizations for overlap/covering
  have h_bMap_range : Set.range bMap = Set.range e₂.toFun ∪ {ext.vertex} := by
    ext x; simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj⟩; obtain (⟨k, rfl⟩ | rfl) := j.eq_castSucc_or_eq_last
      · left; exact ⟨k, by simp only [bMap, Fin.lastCases_castSucc] at hj; exact hj⟩
      · right; simp only [bMap, Fin.lastCases_last] at hj; exact hj.symm
    · rintro (⟨k, rfl⟩ | rfl)
      · exact ⟨Fin.castSucc k, by simp only [bMap, Fin.lastCases_castSucc]⟩
      · exact ⟨Fin.last _, by simp only [bMap, Fin.lastCases_last]⟩
  have hoverlap' : ∀ i : Fin ext.extendedFlag.size,
      (i ∈ Set.range eA.toFun ∧ i ∈ Set.range eB.toFun) ↔
        i ∈ Set.range ext.extendedFlag.embedding := by
    intro i
    rw [show Set.range eA.toFun = Set.range e₁.toFun from rfl,
        show Set.range eB.toFun = Set.range bMap from rfl,
        ext.range_extendedFlag_embedding, h_bMap_range]
    constructor
    · rintro ⟨hi_e1, hi_e2 | rfl⟩
      · left; exact (hoverlap i).mp ⟨hi_e1, hi_e2⟩
      · right; rfl
    · rintro (hi_emb | rfl)
      · exact ⟨((hoverlap i).mpr hi_emb).1, Or.inl ((hoverlap i).mpr hi_emb).2⟩
      · exact ⟨⟨u, hu⟩, Or.inr rfl⟩
  have hcovering' : ∀ i : Fin ext.extendedFlag.size,
      i ∈ Set.range eA.toFun ∨ i ∈ Set.range eB.toFun := by
    intro i
    rw [show Set.range eA.toFun = Set.range e₁.toFun from rfl,
        show Set.range eB.toFun = Set.range bMap from rfl, h_bMap_range]
    rcases hcovering i with h1 | h2
    · left; exact h1
    · right; left; exact h2
  -- jointCount > 0 from witness embeddings
  have hjc_pos : 0 < jointCount ext.extendedType A B ext.extendedFlag := by
    unfold jointCount; rw [Fintype.card_pos_iff]; exact ⟨⟨⟨eA, eB⟩, hoverlap', hcovering'⟩⟩
  -- Size bounds from injectivity
  have hF_le_H : F.size ≤ H.size := by
    have := Fintype.card_le_of_injective e₁.toFun e₁.injective
    rwa [Fintype.card_fin, Fintype.card_fin] at this
  -- Inclusion-exclusion: H.size + σ.size = F.size + F'.size
  have hsize_sum : H.size + σ.size = F.size + F'.size := by
    have := jointCount_pos_of_jointInducedDensity_pos σ F F' H hp
    unfold jointCount at this; rw [Fintype.card_pos_iff] at this
    obtain ⟨⟨⟨e₁', e₂'⟩, hoverlap', hcovering'⟩⟩ := this
    set S₁ := Finset.univ.image e₁'.toFun; set S₂ := Finset.univ.image e₂'.toFun
    set Sσ := Finset.univ.image H.embedding
    have hS₁ : S₁.card = F.size := (Finset.card_image_of_injective _ e₁'.injective).trans
      (Finset.card_univ.trans (Fintype.card_fin F.size))
    have hS₂ : S₂.card = F'.size := (Finset.card_image_of_injective _ e₂'.injective).trans
      (Finset.card_univ.trans (Fintype.card_fin F'.size))
    have hSσ : Sσ.card = σ.size := (Finset.card_image_of_injective _ H.embedding.injective).trans
      (Finset.card_univ.trans (Fintype.card_fin σ.size))
    have hinter : S₁ ∩ S₂ = Sσ := by
      ext i; simp only [Finset.mem_inter, S₁, S₂, Sσ, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩⟩
        exact (hoverlap' i).mp ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩⟩
      · rintro ⟨k, rfl⟩
        have := (hoverlap' (H.embedding k)).mpr ⟨k, rfl⟩
        exact ⟨⟨this.1.choose, this.1.choose_spec⟩, ⟨this.2.choose, this.2.choose_spec⟩⟩
    have hunion : S₁ ∪ S₂ = Finset.univ := by
      ext i; simp only [Finset.mem_union, S₁, S₂, Finset.mem_image, Finset.mem_univ, true_and,
        iff_true]
      rcases hcovering' i with ⟨j, hj⟩ | ⟨j, hj⟩
      · left; exact ⟨j, hj⟩
      · right; exact ⟨j, hj⟩
    have hcard := Finset.card_union_add_card_inter S₁ S₂
    rw [hunion, hinter, Finset.card_univ, Fintype.card_fin, hS₁, hS₂, hSσ] at hcard; linarith
  -- Convert to jointInducedDensity > 0
  have hp_ext : jointInducedDensity ext.extendedType A B ext.extendedFlag > 0 := by
    unfold jointInducedDensity; apply div_pos (Nat.cast_pos.mpr hjc_pos)
    apply mul_pos
    · exact Nat.cast_pos.mpr (Nat.choose_pos (by change F.size - (σ.size + 1) ≤ H.size - (σ.size + 1); omega))
    · have : B.size - ext.extendedType.size ≤
          ext.extendedFlag.size - ext.extendedType.size - (A.size - ext.extendedType.size) := by
        -- Unfold opaque struct fields for omega
        change F'.size + 1 - (σ.size + 1) ≤ H.size - (σ.size + 1) - (F.size - (σ.size + 1))
        have := hsize_sum; have := extF.size_le; have := hF_le_H; omega
      exact Nat.cast_pos.mpr (Nat.choose_pos this)
  exact ⟨A, B, hp_ext, hA_local, hB_local⟩

theorem decomposition_at_extension (σ : FlagType)
    (F F' H : Flag σ) (𝒢 : GraphClass) (Δ : GraphParam)
    (hF : IsLocalFlag σ F 𝒢 Δ) (hF' : IsLocalFlag σ F' 𝒢 Δ)
    (hp : jointInducedDensity σ F F' H > 0)
    (ext : LabelExtension σ H) :
    ∃ (A B : Flag ext.extendedType),
      jointInducedDensity ext.extendedType A B ext.extendedFlag > 0 ∧
      IsLocalFlag ext.extendedType A 𝒢 Δ ∧
      IsLocalFlag ext.extendedType B 𝒢 Δ := by
  obtain ⟨e₁, e₂, hoverlap, hcovering⟩ := joint_pos_witness σ F F' H hp
  rcases vertex_in_exactly_one_side σ F F' H e₁ e₂
    hoverlap hcovering ext.vertex ext.unlabelled with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
  · exact decomposition_at_extension_core σ F F' H 𝒢 Δ hF hF' hp ext
      e₁ e₂ hoverlap hcovering hv1 hv2
  · exact decomposition_at_extension_core σ F' F H 𝒢 Δ hF' hF
      (jointInducedDensity_pos_comm σ F F' H hp) ext e₂ e₁
      (fun i => (and_comm ..).trans (hoverlap i))
      (fun i => (hcovering i).elim .inr .inl) hv2 hv1

/-- **Product closure by well-founded induction** (thesis p.27, lines 305-356):
    Combined proof of product closure and the label extension property by
    well-founded induction on the number of unlabelled vertices of H.

    At each step:
    - Bounded density follows from `bounded_density_of_joint_pos`.
    - For label extensions: `decomposition_at_extension` provides local σ'-flags
      A, B with `p(A,B;H^v) > 0`. Since `H^v.unlabelledSize < H.unlabelledSize`,
      the induction hypothesis (applied at the σ'-level) gives that H^v is local.

    This breaks the mutual dependency between `product_closure` and the label
    extension lemma by handling both simultaneously via the IH. -/
private theorem product_closure_aux (n : ℕ) :
    ∀ (σ : FlagType) (F F' H : Flag σ) (𝒢 : GraphClass) (Δ : GraphParam),
      H.unlabelledSize ≤ n →
      IsLocalFlag σ F 𝒢 Δ →
      IsLocalFlag σ F' 𝒢 Δ →
      jointInducedDensity σ F F' H > 0 →
      IsLocalFlag σ H 𝒢 Δ := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro σ F F' H 𝒢 Δ hle hF hF' hp
  refine IsLocalFlag.intro σ H 𝒢 Δ
    (bounded_density_of_joint_pos σ F F' H 𝒢 Δ hF.bounded hF'.bounded hp)
    fun ext => ?_
  -- Goal: IsLocalFlag ext.extendedType ext.extendedFlag 𝒢 Δ
  -- Step 1: Get local σ'-flags A, B with p(A,B;H^v) > 0 from the decomposition.
  obtain ⟨A, B, hp_ext, hA_local, hB_local⟩ :=
    decomposition_at_extension σ F F' H 𝒢 Δ hF hF' hp ext
  -- Step 2: H^v has strictly fewer unlabelled vertices than H.
  have hlt : ext.extendedFlag.unlabelledSize < H.unlabelledSize := by
    have hσ_lt : σ.size < H.size := by
      by_contra h; push_neg at h
      have hsz : H.size = σ.size := Nat.le_antisymm h H.hsize
      exact ext.unlabelled
        (H.embedding.injective.surjective_of_finite (finCongr hsz.symm) ext.vertex)
    exact ext.unlabelledSize_lt hσ_lt
  -- Step 3: Apply the IH at the σ'-level.
  exact ih ext.extendedFlag.unlabelledSize (lt_of_lt_of_le hlt hle)
    ext.extendedType A B ext.extendedFlag 𝒢 Δ le_rfl hA_local hB_local hp_ext

/-- **Label extension decomposition** (thesis p.27, lines 335-356):
    If `p(F,F';H) > 0` and `ext` is a label extension of H at an unlabelled vertex v,
    then v belongs to U \ im(θ) or U' \ im(θ) in the decomposition of H.
    WLOG v ∈ U \ im(θ). Then any copy of H^v decomposes into a copy of F^v and F'.
    Since F is local, F^v is local (by the extension condition), and we can apply
    the product closure theorem recursively.

    This lemma encapsulates the WLOG + inductive step: the label extension of H
    is itself a local flag, given that F and F' are local. -/
private theorem label_extension_local_of_joint_pos (σ : FlagType)
    (F F' H : Flag σ) (𝒢 : GraphClass) (Δ : GraphParam)
    (hF : IsLocalFlag σ F 𝒢 Δ) (hF' : IsLocalFlag σ F' 𝒢 Δ)
    (hp : jointInducedDensity σ F F' H > 0)
    (ext : LabelExtension σ H) :
    IsLocalFlag ext.extendedType ext.extendedFlag 𝒢 Δ := by
  -- Delegate to the WF-induction proof.
  exact (product_closure_aux H.unlabelledSize σ F F' H 𝒢 Δ le_rfl hF hF' hp).extensions ext

/-- **Theorem** (thesis p.27): If F, F' are local σ-flags and p(F,F';H) > 0 then
    H is also a local σ-flag. This means the product stays in 𝓛^σ.

    The hypothesis uses the *joint* induced density p(F,F';H) > 0, meaning H
    can be decomposed into overlapping copies of F and F' meeting exactly on
    im(η). The proof shows c(H;G) ≤ c(F;G)·c(F';G), and for label extensions
    uses that F and F' are local so their extensions are bounded. -/
theorem product_closure (σ : FlagType) (F F' H : Flag σ)
    (𝒢 : GraphClass) (Δ : GraphParam)
    (hF : IsLocalFlag σ F 𝒢 Δ)
    (hF' : IsLocalFlag σ F' 𝒢 Δ)
    (hp : jointInducedDensity σ F F' H > 0) :
    IsLocalFlag σ H 𝒢 Δ :=
  product_closure_aux H.unlabelledSize σ F F' H 𝒢 Δ le_rfl hF hF' hp

/-- **Corollary** (thesis Cor after product closure): For local flags F, F',
    every σ-flag H ∈ 𝒢̄^σ with p(F,F';H) > 0 is automatically a local σ-flag.
    This means the product F · F' = Σ_H p(F,F';H)·H can equivalently sum over
    all σ-flags of size n = |F|+|F'|-|σ| (not just local ones), since the
    non-local terms have zero coefficient.

    **Status**: Intentional standalone — Thesis Cor 2.8; no consumer
    expected (the local product uses `localFlagProduct` directly). -/
theorem product_sum_all_flags (σ : FlagType) (F F' H : Flag σ)
    (𝒢 : GraphClass) (Δ : GraphParam)
    (hF : IsLocalFlag σ F 𝒢 Δ) (hF' : IsLocalFlag σ F' 𝒢 Δ)
    (hp : jointInducedDensity σ F F' H > 0) :
    IsLocalFlag σ H 𝒢 Δ :=
  product_closure σ F F' H 𝒢 Δ hF hF' hp

/-! ## §2.2: Product Limit Theorem (Theorem 2.3)

The fundamental theorem of the local flag algebra: the product captures
density multiplication up to O(1/Δ) error.

### Unlabelled (thesis) density

The thesis defines ρ(F; G) = c(F; G) / C(Δ, f), where c counts **subsets** U with
F ≅ G[U]. Our `localDensity` counts **embeddings** (injective maps), overcounting
each subset by |Aut_σ(F)| = `flagAutCount σ F`. The **unlabelled density** corrects
for this: `unlabelledDensity σ F G Δ = localDensity σ F G Δ / flagAutCount σ F`.
This matches the thesis ρ exactly and enables clean bilinear extension of the
product limit theorem. -/

/-- The thesis density ρ(F; G) = c(F;G) / C(Δ, |F|-|σ|), where c counts subsets (not
    embeddings). Equals `localDensity / flagAutCount`. -/
noncomputable def unlabelledDensity (σ : FlagType) (F : Flag σ) (G : Flag σ)
    (Δ : GraphParam) : ℝ :=
  localDensity σ F G Δ / (flagAutCount σ F : ℝ)

/-- `unlabelledDensity` respects flag isomorphism. -/
theorem unlabelledDensity_flagIso {σ : FlagType} {F₁ F₂ G : Flag σ} {Δ : GraphParam}
    (h : FlagIso σ F₁ F₂) : unlabelledDensity σ F₁ G Δ = unlabelledDensity σ F₂ G Δ := by
  unfold unlabelledDensity
  rw [localDensity_flagIso h, flagAutCount_flagIso h]

/-- Unlabelled density is nonneg: dividing a nonneg quantity by a positive natural. -/
theorem unlabelledDensity_nonneg (σ : FlagType) (F G : Flag σ) (Δ : GraphParam) :
    0 ≤ unlabelledDensity σ F G Δ := by
  unfold unlabelledDensity localDensity
  exact div_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

/-- Unlabelled density ≤ local density (since flagAutCount ≥ 1). -/
theorem unlabelledDensity_le_localDensity (σ : FlagType) (F G : Flag σ) (Δ : GraphParam) :
    unlabelledDensity σ F G Δ ≤ localDensity σ F G Δ := by
  unfold unlabelledDensity
  exact div_le_self (by unfold localDensity; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Nat.one_le_cast.mpr (flagAutCount_pos σ F))

/-- Lift `unlabelledDensity` to isomorphism classes. -/
noncomputable def classUnlabelledDensity (σ : FlagType) (G : Flag σ) (Δ : GraphParam)
    (cls : FlagClass σ) : ℝ :=
  Quotient.lift (fun F => unlabelledDensity σ F G Δ)
    (fun _ _ h => unlabelledDensity_flagIso h) cls

/-- Unlabelled density of a basis element equals the underlying flag's
    unlabelled density.

    **Status**: Intentional standalone — `@[simp]`-tagged def-equivalence;
    consumed by `simp` reduction. -/
@[simp]
theorem classUnlabelledDensity_mk (σ : FlagType) (F G : Flag σ) (Δ : GraphParam) :
    classUnlabelledDensity σ G Δ (FlagClass.mk F) = unlabelledDensity σ F G Δ := by
  simp [classUnlabelledDensity, FlagClass.mk]

/-- Evaluate a vector v ∈ 𝓛^σ using the thesis (unlabelled) density:
    ρ̃(v; G) = Σ_F coeff(F) · ρ_thesis(F; G). -/
noncomputable def FlagAlg.unlabelledEvalDensity (v : FlagAlg σ) (G : Flag σ)
    (Δ : GraphParam) : ℝ :=
  v.sum (fun cls c => c * classUnlabelledDensity σ G Δ cls)

theorem FlagAlg.unlabelledEvalDensity_zero (σ : FlagType) (G : Flag σ) (Δ : GraphParam) :
    (0 : FlagAlg σ).unlabelledEvalDensity G Δ = 0 := by
  unfold FlagAlg.unlabelledEvalDensity; rw [Finsupp.sum_zero_index]

theorem FlagAlg.unlabelledEvalDensity_pointwise_smul (c : ℝ) (v : FlagAlg σ)
    (G : Flag σ) (Δ : GraphParam) :
    FlagAlg.unlabelledEvalDensity (c • v) G Δ = c * v.unlabelledEvalDensity G Δ := by
  simp only [FlagAlg.unlabelledEvalDensity]
  rw [Finsupp.sum_smul_index (by simp)]
  simp only [Finsupp.sum, mul_assoc]
  rw [← Finset.mul_sum]

theorem FlagAlg.unlabelledEvalDensity_add (v w : FlagAlg σ)
    (G : Flag σ) (Δ : GraphParam) :
    FlagAlg.unlabelledEvalDensity (v + w) G Δ =
      v.unlabelledEvalDensity G Δ + w.unlabelledEvalDensity G Δ := by
  simp only [FlagAlg.unlabelledEvalDensity]
  rw [Finsupp.sum_add_index (by simp) (by intros; ring)]

theorem FlagAlg.unlabelledEvalDensity_single (σ : FlagType) (F G : Flag σ)
    (Δ : GraphParam) :
    (FlagAlg.single σ F).unlabelledEvalDensity G Δ = unlabelledDensity σ F G Δ := by
  simp [FlagAlg.single, FlagAlg.unlabelledEvalDensity, Finsupp.sum_single_index]

/-- The `localFlagProduct_class` of two classes equals the `localFlagProduct`
    of their canonical representatives. -/
theorem localFlagProduct_class_out (σ : FlagType) (cls₁ cls₂ : FlagClass σ) :
    localFlagProduct_class σ cls₁ cls₂ = localFlagProduct σ cls₁.out cls₂.out := by
  conv_lhs => rw [← Quotient.out_eq cls₁, ← Quotient.out_eq cls₂]
  exact localFlagProduct_class_mk σ cls₁.out cls₂.out

/-! #### Counting and density lemmas for the type flag σ.toFlag -/

/-- The unique σ-compatible induced embedding of σ.toFlag into any σ-flag G
    is the embedding G.embedding itself. -/
theorem inducedCount_type_eq_one' (σ : FlagType) (G : Flag σ) :
    inducedCount σ σ.toFlag G = 1 := by
  unfold inducedCount
  rw [Fintype.card_eq_one_iff]
  have hcanon_inj : Function.Injective (fun i : Fin σ.size => G.embedding i) :=
    fun _ _ h => G.embedding.injective h
  refine ⟨⟨fun i => G.embedding i, hcanon_inj,
    fun u v hadj => ?_, fun u v _ hnadj => ?_,
    fun i => ?_⟩, fun b => ?_⟩
  · exact G.embedding.map_rel_iff'.mpr hadj
  · exact fun hadj' => hnadj (G.embedding.map_rel_iff'.mp hadj')
  · simp [FlagType.toFlag, SimpleGraph.Embedding.refl]
  · have heq : b.toFun = fun i => G.embedding i := by
      funext v
      have hv : σ.toFlag.embedding v = v := by
        simp [FlagType.toFlag, SimpleGraph.Embedding.refl]
      rw [← hv]
      exact b.compat v
    cases b; simp only at heq; subst heq; rfl

/-- The local density of the type σ viewed as a σ-flag is always 1:
    ρ(σ; G) = c(σ;G)/C(Δ,0) = 1/1 = 1. -/
theorem localDensity_type_eq_one' (σ : FlagType) (G : Flag σ) (Δ : GraphParam) :
    localDensity σ σ.toFlag G Δ = 1 := by
  unfold localDensity
  have hsub : σ.toFlag.size - σ.size = 0 := Nat.sub_self σ.size
  rw [hsub, Nat.choose_zero_right, inducedCount_type_eq_one']
  simp

/-- The unlabelled density of σ.toFlag is always 1:
    ρ̃(σ; G) = ρ(σ;G) / |Aut_σ(σ)| = 1/1 = 1. -/
theorem unlabelledDensity_type_eq_one (σ : FlagType) (G : Flag σ) (Δ : GraphParam) :
    unlabelledDensity σ σ.toFlag G Δ = 1 := by
  unfold unlabelledDensity
  rw [localDensity_type_eq_one', flagAutCount_toFlag, Nat.cast_one, div_one]

/-! #### Unit product helpers (moved early for use in product_limit_basis) -/

/-- When one factor is `σ.toFlag`, the `e₂` component of a joint pair is uniquely
    determined (as in `inducedCount_type_eq_one`), and the covering condition forces
    `e₁` to be surjective. For same-size flags this is automatic, so
    `jointCount σ F σ.toFlag H = inducedCount σ F H` when `H.size = F.size`. -/
private theorem jointCount_toFlag_eq_inducedCount (σ : FlagType) (F H : Flag σ)
    (hsize : H.size = F.size) :
    jointCount σ F σ.toFlag H = inducedCount σ F H := by
  unfold jointCount inducedCount
  -- Build an equiv between the joint pairs and InducedEmbedding σ F H
  apply Fintype.card_congr
  -- The unique e₂ : InducedEmbedding σ σ.toFlag H sends i to H.embedding i
  have e₂_unique : ∀ (e : InducedEmbedding σ σ.toFlag H),
      e.toFun = fun i => H.embedding i := by
    intro e; funext v
    have hv : σ.toFlag.embedding v = v := by
      simp [FlagType.toFlag, SimpleGraph.Embedding.refl]
    rw [← hv]; exact e.compat v
  -- The canonical e₂
  let e₂_canon : InducedEmbedding σ σ.toFlag H :=
    ⟨fun i => H.embedding i,
     fun _ _ h => H.embedding.injective h,
     fun _ _ hadj => H.embedding.map_rel_iff'.mpr hadj,
     fun _ _ _ hnadj => fun hadj' => hnadj (H.embedding.map_rel_iff'.mp hadj'),
     fun i => by simp [FlagType.toFlag, SimpleGraph.Embedding.refl]⟩
  -- For any injective e₁ : Fin F.size → Fin H.size with |F| = |H|, e₁ is surjective
  have inj_surj : ∀ (f : Fin F.size → Fin H.size), Function.Injective f →
      Function.Surjective f := by
    intro f hf
    exact hf.surjective_of_finite (Fin.castOrderIso hsize.symm).toEquiv
  -- The overlap condition is automatic when e₂ = e₂_canon and e₁ is surjective
  have overlap_auto : ∀ (e₁ : InducedEmbedding σ F H),
      ∀ i : Fin H.size,
        (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂_canon.toFun) ↔
          i ∈ Set.range H.embedding := by
    intro e₁ i
    constructor
    · rintro ⟨_, hi₂⟩; exact hi₂
    · intro hi
      constructor
      · exact (inj_surj e₁.toFun e₁.injective) i
      · exact hi
  have covering_auto : ∀ (e₁ : InducedEmbedding σ F H),
      ∀ i : Fin H.size,
        i ∈ Set.range e₁.toFun ∨ i ∈ Set.range e₂_canon.toFun := by
    intro e₁ i
    exact Or.inl ((inj_surj e₁.toFun e₁.injective) i)
  -- Build the equivalence: joint count subtype ≃ InducedEmbedding σ F H
  -- (jointCount is Fintype.card of the subtype, inducedCount is Fintype.card of InducedEmbedding)
  exact {
    toFun := fun p => p.1.1
    invFun := fun e₁ => ⟨(e₁, e₂_canon), overlap_auto e₁, covering_auto e₁⟩
    left_inv := fun ⟨⟨e₁, e₂⟩, hcond⟩ => by
      -- Need: ⟨(e₁, e₂_canon), ...⟩ = ⟨(e₁, e₂), hcond⟩
      -- e₂ = e₂_canon since e₂.toFun is uniquely determined
      have hf : e₂.toFun = e₂_canon.toFun := e₂_unique e₂
      have he₂ : e₂ = e₂_canon := by cases e₂; subst hf; rfl
      subst he₂; rfl
    right_inv := fun _ => rfl
  }

/-- The joint induced density `p(F, σ.toFlag; H) = inducedCount σ F H` when
    `H.size = F.size` (the multinomial denominator is 1). -/
private theorem jointInducedDensity_toFlag (σ : FlagType) (F H : Flag σ)
    (hsize : H.size = F.size) :
    jointInducedDensity σ F σ.toFlag H = (inducedCount σ F H : ℝ) := by
  unfold jointInducedDensity
  rw [jointCount_toFlag_eq_inducedCount σ F H hsize]
  -- Denominator: choose (H.size - σ.size) (F.size - σ.size) * choose 0 0 = 1
  have h1 : σ.toFlag.size = σ.size := rfl
  have h2 : H.size - σ.size - (F.size - σ.size) = 0 := by omega
  have h3 : Nat.choose (H.size - σ.size) (F.size - σ.size) = 1 := by
    rw [hsize]; exact Nat.choose_self _
  rw [h1, Nat.sub_self, Nat.choose_zero_right, h3]
  simp

/-- An `InducedEmbedding σ F H` with `F.size = H.size` yields a `FlagIso σ F H`. -/
private theorem flagIso_of_inducedEmbedding_same_size (σ : FlagType) (F H : Flag σ)
    (hsize : F.size = H.size) (e : InducedEmbedding σ F H) : FlagIso σ F H := by
  have hsurj : Function.Surjective e.toFun :=
    e.injective.surjective_of_finite (Fin.castOrderIso hsize).toEquiv
  have hbij : Function.Bijective e.toFun := ⟨e.injective, hsurj⟩
  -- Build the graph isomorphism from the bijection
  let φequiv := Equiv.ofBijective e.toFun hbij
  have hadj : ∀ {a b}, F.graph.Adj a b ↔ H.graph.Adj (φequiv a) (φequiv b) := by
    intro a b
    constructor
    · exact e.map_adj a b
    · intro hadj'
      by_contra hnadj
      by_cases hab : a = b
      · subst hab; exact (H.graph.irrefl hadj').elim
      · exact e.map_non_adj a b hab hnadj hadj'
  exact ⟨{ toEquiv := φequiv, map_rel_iff' := hadj.symm }, fun i => e.compat i⟩

/-- `inducedCount σ F H = 0` when `F.size = H.size` and `¬ FlagIso σ F H`. -/
private theorem inducedCount_eq_zero_of_not_iso (σ : FlagType) (F H : Flag σ)
    (hsize : F.size = H.size) (hnotiso : ¬ FlagIso σ F H) :
    inducedCount σ F H = 0 := by
  unfold inducedCount
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun e => hnotiso (flagIso_of_inducedEmbedding_same_size σ F H hsize e)⟩

/-- `FlagClass.mk F` is in `classesOfSize σ F.size F.hsize`. -/
private theorem mk_mem_classesOfSize (σ : FlagType) (F : Flag σ) :
    FlagClass.mk F ∈ classesOfSize σ F.size F.hsize := by
  rw [classesOfSize, Finset.mem_image]
  exact ⟨⟨F.graph, F.embedding⟩, Finset.mem_univ _, rfl⟩

/-- `FlagClass.mk F` is in `classesOfSize` for the product size parameter. -/
private theorem mk_F_mem_classesOfSize' (σ : FlagType) (F : Flag σ)
    (hn : σ.size ≤ F.size + σ.toFlag.size - σ.size) :
    FlagClass.mk F ∈ classesOfSize σ (F.size + σ.toFlag.size - σ.size) hn := by
  have hneq : F.size + σ.toFlag.size - σ.size = F.size := by
    change F.size + σ.size - σ.size = F.size; have := F.hsize; omega
  -- Transport F to a flag of size n = F.size + σ.toFlag.size - σ.size via Fin.cast
  set n := F.size + σ.toFlag.size - σ.size
  -- Build the transported graph and embedding
  let castFin : Fin F.size → Fin n := Fin.cast hneq.symm
  let castBack : Fin n → Fin F.size := Fin.cast hneq
  have hcast_inv : ∀ x, castBack (castFin x) = x := by intro x; simp [castFin, castBack]
  have hcast_inv' : ∀ x, castFin (castBack x) = x := by intro x; simp [castFin, castBack]
  let g : SimpleGraph (Fin n) := ⟨fun a b => F.graph.Adj (castBack a) (castBack b),
    fun {a} {b} h => F.graph.symm h, ⟨fun a h => F.graph.loopless.irrefl _ h⟩⟩
  let emb : σ.graph ↪g g := ⟨⟨fun i => castFin (F.embedding i),
    fun {a} {b} (h : castFin (F.embedding a) = castFin (F.embedding b)) =>
      F.embedding.injective (by
        have := congr_arg Fin.val h
        simp only [castFin, Fin.val_cast] at this
        exact Fin.ext this)⟩,
    fun {a} {b} => by
      -- The goal is: σ.graph.Adj a b ↔ g.Adj (castFin (F.embedding a)) (castFin (F.embedding b))
      -- g.Adj x y = F.graph.Adj (castBack x) (castBack y) by definition
      -- castBack (castFin x) = x by hcast_inv
      -- So this reduces to: σ.graph.Adj a b ↔ F.graph.Adj (F.embedding a) (F.embedding b)
      -- which is F.embedding.map_rel_iff'
      have h1 : castBack (castFin (F.embedding a)) = F.embedding a := hcast_inv _
      have h2 : castBack (castFin (F.embedding b)) = F.embedding b := hcast_inv _
      simp only [g]
      exact F.embedding.map_rel_iff'⟩
  rw [classesOfSize, Finset.mem_image]
  refine ⟨⟨g, emb⟩, Finset.mem_univ _, ?_⟩
  rw [FlagClass.mk_eq, flagOfSigma]
  -- FlagIso σ ⟨n, g, emb, hn⟩ F: via castBack
  refine ⟨⟨⟨castBack, castFin, hcast_inv', hcast_inv⟩,
    fun {a} {b} => Iff.rfl⟩,
    fun i => rfl⟩

set_option maxHeartbeats 400000 in
-- Needs extra heartbeats for Finsupp.ext + Finset.sum_ite_eq' + FlagIso construction
/-- **Lemma 2.4 (Unit)**: σ is the multiplicative unit of 𝓛^σ.
    For any F ∈ 𝓛^σ: F · σ = F. (Thesis lines 497-503)
    Proof: The only flag of size |F| containing copies of both F and σ (with
    im(θ_F) ∩ im(θ_σ) = im(θ_H)) is F itself, so p(F,σ;H) = δ_{H,F}.
    Now consistent with the concrete `localFlagProduct` (automorphism normalization). -/
theorem product_unit (σ : FlagType) (F : Flag σ) :
    localFlagProduct σ F σ.toFlag = FlagAlg.single σ F := by
  -- Rewrite localFlagProduct to use F.size directly
  -- Key: σ.toFlag.size = σ.size (definitional), so n = F.size + σ.size - σ.size
  unfold localFlagProduct
  -- The let-bound n = F.size + σ.toFlag.size - σ.size
  -- σ.toFlag.size = σ.size definitionally
  -- σ.size ≤ n: show σ.size ≤ F.size + σ.size - σ.size
  have hn : σ.size ≤ F.size + σ.toFlag.size - σ.size := by
    change σ.size ≤ F.size + σ.size - σ.size
    have := F.hsize; omega
  rw [dif_pos hn, flagAutCount_toFlag, Nat.cast_one, mul_one]
  -- Goal: (flagAutCount σ F)⁻¹ • Σ_{cls} single cls (jid σ F σ.toFlag cls.out) = single [F] 1
  -- Suffices to show the sum = flagAutCount σ F • single [F] 1
  rw [FlagAlg.single]
  -- Goal: (↑(flagAutCount σ F))⁻¹ • sum = single [F] 1
  -- Equivalently: sum = ↑(flagAutCount σ F) • single [F] 1 = single [F] (flagAutCount σ F)
  rw [inv_smul_eq_iff₀ (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (flagAutCount_pos σ F)))]
  simp only [Finsupp.smul_single', mul_one]
  -- Goal: sum = single [F] (↑(flagAutCount σ F))
  -- Use Finsupp.ext: show coefficients agree at every class
  ext cls
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply]
  -- LHS is: Σ_{c ∈ classesOfSize} (if c = cls then jid σ F σ.toFlag c.out else 0)
  -- RHS is: if FlagClass.mk F = cls then ↑(flagAutCount σ F) else 0
  -- Use Finset.sum_ite_eq' to collapse the sum (sum has `if x = cls`)
  rw [Finset.sum_ite_eq']
  -- Goal: (if cls ∈ classesOfSize ... then jid ... else 0) = (if [F] = cls then ... else 0)
  -- Now case split
  by_cases hmem : cls ∈ classesOfSize σ _ hn
  · rw [if_pos hmem]
    have hout_size : (Quotient.out cls).size = F.size := by
      have hneq : F.size + σ.toFlag.size - σ.size = F.size := by
        change F.size + σ.size - σ.size = F.size; omega
      rw [← hneq]; exact classesOfSize_out_size hmem
    rw [jointInducedDensity_toFlag σ F _ hout_size]
    by_cases heq : FlagClass.mk F = cls
    · rw [if_pos heq]
      -- cls = [F], so inducedCount σ F cls.out = flagAutCount σ F
      have hiso : FlagIso σ (Quotient.out cls) F := by
        rw [← FlagClass.mk_eq, ← heq]; exact Quotient.out_eq _
      congr 1
      obtain ⟨φ, hφ⟩ := hiso
      unfold flagAutCount inducedCount
      apply Fintype.card_congr
      exact {
        toFun := fun e => ⟨fun v => φ (e.toFun v), fun a b h => e.injective (φ.injective h),
          fun u v h => φ.map_rel_iff'.mpr (e.map_adj u v h),
          fun u v huv hna hadj => e.map_non_adj u v huv hna (φ.map_rel_iff'.mp hadj),
          fun i => by change φ (e.toFun (F.embedding i)) = F.embedding i; rw [e.compat, hφ]⟩
        invFun := fun e => ⟨fun v => φ.symm (e.toFun v),
          fun a b h => e.injective (φ.symm.injective h),
          fun u v h => φ.symm.map_rel_iff'.mpr (e.map_adj u v h),
          fun u v huv hna hadj => e.map_non_adj u v huv hna (φ.symm.map_rel_iff'.mp hadj),
          fun i => by
            change φ.symm (e.toFun (F.embedding i)) = (Quotient.out cls).embedding i
            rw [e.compat, ← hφ]; simp⟩
        left_inv := fun e => by cases e; simp
        right_inv := fun e => by cases e; simp
      }
    · rw [if_neg heq]
      -- cls ≠ [F], so inducedCount σ F cls.out = 0
      have hnotiso : ¬ FlagIso σ F (Quotient.out cls) := by
        intro hiso; apply heq
        rw [← FlagClass.mk_eq] at hiso
        rw [← Quotient.out_eq cls]; exact hiso
      rw [inducedCount_eq_zero_of_not_iso σ F _ hout_size.symm hnotiso]; simp
  · rw [if_neg hmem]
    split_ifs with heq
    · -- cls = [F] but cls ∉ classesOfSize: contradiction
      exfalso; apply hmem; rw [← heq]
      exact mk_F_mem_classesOfSize' σ F hn
    · rfl

/-! #### Binomial asymptotics for the product limit theorem -/

/-- **Binomial ratio asymptotics**: C(n, k) / C(n - m, k) → 1 as n → ∞
    for fixed k, m : ℕ.
    Proof: Both C(n,k) and C(n-m,k) are asymptotic to n^k/k! by
    `isEquivalent_choose`, so their ratio tends to 1. -/
theorem choose_ratio_tendsto_one' (k m : ℕ) :
    Filter.Tendsto (fun n : ℕ => (Nat.choose n k : ℝ) / (Nat.choose (n - m) k : ℝ))
      Filter.atTop (nhds 1) := by
  open Asymptotics Filter Nat in
  suffices h : IsEquivalent atTop
      (fun n : ℕ => (n.choose k : ℝ)) (fun n : ℕ => ((n - m).choose k : ℝ)) by
    exact (isEquivalent_iff_tendsto_one (eventually_atTop.mpr ⟨m + k, fun n hn => by
      exact_mod_cast (Nat.choose_pos (show k ≤ n - m by omega)).ne'⟩)).mp h
  have h1 := isEquivalent_choose k
  have h_sub : Tendsto (fun n : ℕ => n - m) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun _ _ h => Nat.sub_le_sub_right h m)
      (fun b => ⟨b + m, by omega⟩)
  have h2 : IsEquivalent atTop
      (fun n : ℕ => ((n - m).choose k : ℝ))
      (fun n : ℕ => ((n - m : ℕ) : ℝ) ^ k / ↑k.factorial) := by
    have := h1.comp_tendsto h_sub
    simpa only [Function.comp_def] using this
  have h_nm : IsEquivalent atTop
      (fun n : ℕ => (n : ℝ)) (fun n : ℕ => ((n - m : ℕ) : ℝ)) := by
    rw [IsEquivalent]
    have hf : (fun n : ℕ => (n : ℝ) - ((n - m : ℕ) : ℝ)) =ᶠ[atTop]
        (fun (_ : ℕ) => (m : ℝ)) :=
      eventually_atTop.mpr ⟨m, fun n hn => by
        simp only [Nat.cast_sub hn, sub_sub_cancel]⟩
    have key : (fun (_ : ℕ) => (m : ℝ)) =o[atTop] (fun n : ℕ => ((n - m : ℕ) : ℝ)) :=
      isLittleO_const_left.mpr (.inr ((tendsto_natCast_atTop_atTop.comp h_sub).congr
        (fun n => (Real.norm_of_nonneg (Nat.cast_nonneg (n - m))).symm)))
    exact (isLittleO_congr hf EventuallyEq.rfl).mpr key
  have h3 : IsEquivalent atTop
      (fun n : ℕ => (n : ℝ) ^ k / ↑k.factorial)
      (fun n : ℕ => ((n - m : ℕ) : ℝ) ^ k / ↑k.factorial) := by
    exact (h_nm.pow k).div IsEquivalent.refl
  exact h1.trans (h3.trans h2.symm)

/-! #### Helper lemmas for the product limit theorem (Theorem 2.3) -/

/-- A flag with the same size as σ is isomorphic to σ.toFlag.
    When F.size = σ.size, the embedding F.embedding : Fin σ.size → Fin F.size
    is a bijection, giving a canonical graph isomorphism φ = emb⁻¹. -/
private theorem flagIso_toFlag_of_size_eq {σ : FlagType} (F : Flag σ) (hsz : F.size = σ.size) :
    FlagIso σ F σ.toFlag := by
  -- Compose F.embedding with Fin.cast to get a self-map on Fin σ.size
  let ψ : Fin σ.size → Fin σ.size := (finCongr hsz) ∘ F.embedding
  have hψ_inj : Function.Injective ψ := (Equiv.injective _).comp F.embedding.injective
  have hψ_bij : Function.Bijective ψ := (Finite.injective_iff_bijective).mp hψ_inj
  let ψ_equiv := Equiv.ofBijective ψ hψ_bij
  -- The graph iso φ : F.graph ≃g σ.graph has φ(x) = emb⁻¹(x)
  let φ_equiv : Fin F.size ≃ Fin σ.size := (finCongr hsz).trans ψ_equiv.symm
  -- Key: F.embedding (φ_equiv x) = x (φ is the inverse of the embedding)
  have hemb_inv : ∀ x : Fin F.size, F.embedding.toEmbedding (φ_equiv x) = x := by
    intro x
    apply (finCongr hsz).injective
    show (finCongr hsz) (F.embedding.toEmbedding (φ_equiv x)) = (finCongr hsz) x
    change ψ (ψ_equiv.symm ((finCongr hsz) x)) = (finCongr hsz) x
    exact Equiv.ofBijective_apply_symm_apply ψ hψ_bij ((finCongr hsz) x)
  refine ⟨⟨φ_equiv, fun {x y} => ?_⟩, fun i => ?_⟩
  · -- Graph iso condition: σ.graph.Adj (φ x) (φ y) ↔ F.graph.Adj x y
    constructor
    · intro h
      have := F.embedding.map_rel_iff'.mpr h
      convert this using 2 <;> exact (hemb_inv _).symm
    · intro h
      apply F.embedding.map_rel_iff'.mp
      convert h using 2 <;> exact hemb_inv _
  · -- Compatibility: φ (F.embedding i) = i = σ.toFlag.embedding i
    change φ_equiv (F.embedding i) = i
    simp only [φ_equiv, Equiv.trans_apply]
    show ψ_equiv.symm (finCongr hsz (F.embedding i)) = i
    change ψ_equiv.symm (ψ_equiv i) = i
    exact ψ_equiv.symm_apply_apply i

/-- The unlabelled density of a flag with size = σ.size is either 0 or 1/Aut. -/
private theorem unlabelledDensity_of_size_eq {σ : FlagType} (F : Flag σ) (G : Flag σ)
    (Δ : GraphParam) (hsz : F.size = σ.size) :
    unlabelledDensity σ F G Δ = unlabelledDensity σ σ.toFlag G Δ :=
  unlabelledDensity_flagIso (flagIso_toFlag_of_size_eq F hsz)

/-- **Vandermonde convolution identity**: C(Δ, f+f') · C(f+f', f) = C(Δ, f) · C(Δ-f, f').
    Standard combinatorial identity: both sides count the number of ways to choose
    f elements then f' elements from [Δ] without replacement. -/
private theorem choose_vandermonde (Δ f f' : ℕ) (_hf : f ≤ Δ) (_hff : f + f' ≤ Δ) :
    Nat.choose Δ (f + f') * Nat.choose (f + f') f =
      Nat.choose Δ f * Nat.choose (Δ - f) f' := by
  -- From Nat.choose_mul: C(Δ, f+f') · C(f+f', f) = C(Δ, f) · C(Δ-f, (f+f')-f)
  have h : f ≤ f + f' := Nat.le_add_right f f'
  rw [Nat.choose_mul h, Nat.add_sub_cancel_left]

-- ═══════════════════════════════════════════════════════════════════════════
-- 2-flag orbit counting infrastructure (duplicated from 3-flag version with
-- "nop" prefix to avoid forward references).
-- ═══════════════════════════════════════════════════════════════════════════

-- Two InducedEmbeddings with the same toFun are equal (proof irrelevance).
private theorem nopExt' {σ : FlagType} {F G : Flag σ}
    {e₁ e₂ : InducedEmbedding σ F G} (h : e₁.toFun = e₂.toFun) : e₁ = e₂ := by
  cases e₁; cases e₂; simp only [InducedEmbedding.mk.injEq]; exact h

-- Union of two embedding ranges as a Finset.
private noncomputable def nopFinset {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G) :
    Finset (Fin G.size) :=
  Finset.univ.filter (fun v => v ∈ Set.range e₁.toFun ∨ v ∈ Set.range e₂.toFun)

private theorem nopFinset_contains_sigma {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (i : Fin σ.size) :
    G.embedding i ∈ nopFinset e₁ e₂ := by
  simp only [nopFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  left; exact ⟨F₁.embedding i, e₁.compat i⟩

-- Card of the union finset = F₁.size + F₂.size - σ.size (only needs overlap).
private theorem nopFinset_card {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding) :
    (nopFinset e₁ e₂).card = F₁.size + F₂.size - σ.size := by
  let A := Finset.univ.filter (fun v => v ∈ Set.range e₁.toFun)
  let B := Finset.univ.filter (fun v => v ∈ Set.range e₂.toFun)
  have hAB : nopFinset e₁ e₂ = A ∪ B := by
    ext v; simp only [nopFinset, A, B, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_union]
  rw [hAB]
  have hA : A.card = F₁.size := by
    have : A = Finset.univ.image e₁.toFun := by
      ext v; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image]; rfl
    rw [this, Finset.card_image_of_injective _ e₁.injective, Finset.card_fin]
  have hB : B.card = F₂.size := by
    have : B = Finset.univ.image e₂.toFun := by
      ext v; simp only [B, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image]; rfl
    rw [this, Finset.card_image_of_injective _ e₂.injective, Finset.card_fin]
  have hAinterB : (A ∩ B).card = σ.size := by
    have hAB_eq : A ∩ B = Finset.univ.image G.embedding := by
      ext v; simp only [A, B, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_image]
      exact hoverlap v
    rw [hAB_eq, Finset.card_image_of_injective _ G.embedding.injective, Finset.card_fin]
  have h := Finset.card_union_add_card_inter A B
  omega

-- Intermediate subflag (only needs overlap, not covering).
private noncomputable def nopSubflag {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    Flag σ :=
  G.inducedSubflag (nopFinset e₁ e₂) (nopFinset_contains_sigma e₁ e₂)
    ((nopFinset_card e₁ e₂ hoverlap).symm ▸ hn)

private theorem nopSubflag_size {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    (nopSubflag e₁ e₂ hoverlap hn).size = F₁.size + F₂.size - σ.size :=
  nopFinset_card e₁ e₂ hoverlap

private noncomputable def nopSubflag_incl {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    InducedEmbedding σ (nopSubflag e₁ e₂ hoverlap hn) G :=
  G.inducedSubflag_incl _ _ _

private theorem nopSubflag_incl_range {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    Set.range (nopSubflag_incl e₁ e₂ hoverlap hn).toFun =
      ↑(nopFinset e₁ e₂) :=
  Flag.inducedSubflag_incl_range G _ _ _

-- Restrict e₁ to the intermediate subflag.
private noncomputable def nop_restrict_e₁ {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    InducedEmbedding σ F₁ (nopSubflag e₁ e₂ hoverlap hn) :=
  e₁.restrictToSubflag _ _ _ (fun x => by
    simp only [nopFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    left; exact Set.mem_range_self x)

private noncomputable def nop_restrict_e₂ {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    InducedEmbedding σ F₂ (nopSubflag e₁ e₂ hoverlap hn) :=
  e₂.restrictToSubflag _ _ _ (fun x => by
    simp only [nopFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    right; exact Set.mem_range_self x)

private theorem nop_restrict_comp_incl_e₁ {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    ∀ x, (nopSubflag_incl e₁ e₂ hoverlap hn).toFun
      ((nop_restrict_e₁ e₁ e₂ hoverlap hn).toFun x) = e₁.toFun x :=
  InducedEmbedding.restrictToSubflag_comp_incl e₁ _ _ _ _

private theorem nop_restrict_comp_incl_e₂ {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    ∀ x, (nopSubflag_incl e₁ e₂ hoverlap hn).toFun
      ((nop_restrict_e₂ e₁ e₂ hoverlap hn).toFun x) = e₂.toFun x :=
  InducedEmbedding.restrictToSubflag_comp_incl e₂ _ _ _ _

-- The restricted embeddings form a JC pair in the intermediate subflag.
private theorem nop_restrict_jc {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    let H := nopSubflag e₁ e₂ hoverlap hn
    let a₁ := nop_restrict_e₁ e₁ e₂ hoverlap hn
    let a₂ := nop_restrict_e₂ e₁ e₂ hoverlap hn
    (∀ i : Fin H.size,
      (i ∈ Set.range a₁.toFun ∧ i ∈ Set.range a₂.toFun) ↔
        i ∈ Set.range H.embedding) ∧
    (∀ i : Fin H.size,
      i ∈ Set.range a₁.toFun ∨ i ∈ Set.range a₂.toFun) := by
  intro H a₁ a₂
  set incl := nopSubflag_incl e₁ e₂ hoverlap hn
  have hcomp₁ := nop_restrict_comp_incl_e₁ e₁ e₂ hoverlap hn
  have hcomp₂ := nop_restrict_comp_incl_e₂ e₁ e₂ hoverlap hn
  have hrange := nopSubflag_incl_range e₁ e₂ hoverlap hn
  constructor
  · intro i; constructor
    · intro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
      have h1 : incl.toFun i ∈ Set.range e₁.toFun := by
        have : incl.toFun i = incl.toFun (a₁.toFun x₁) := by congr 1; exact hx₁.symm
        rw [this, hcomp₁ x₁]; exact Set.mem_range_self x₁
      have h2 : incl.toFun i ∈ Set.range e₂.toFun := by
        have : incl.toFun i = incl.toFun (a₂.toFun x₂) := by congr 1; exact hx₂.symm
        rw [this, hcomp₂ x₂]; exact Set.mem_range_self x₂
      obtain ⟨j, hj⟩ := (hoverlap _).mp ⟨h1, h2⟩
      exact ⟨j, incl.injective ((incl.compat j).trans hj)⟩
    · intro ⟨j, hj⟩
      have hincl_i : incl.toFun i = G.embedding j := by
        rw [show i = H.embedding j from hj.symm]; exact incl.compat j
      constructor
      · refine ⟨F₁.embedding j, incl.injective ?_⟩
        rw [hcomp₁, e₁.compat, hincl_i]
      · refine ⟨F₂.embedding j, incl.injective ?_⟩
        rw [hcomp₂, e₂.compat, hincl_i]
  · intro i
    have hi : incl.toFun i ∈ (nopFinset e₁ e₂ : Set (Fin G.size)) := by
      rw [← hrange]; exact Set.mem_range_self i
    simp only [nopFinset, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
      true_and] at hi
    rcases hi with ⟨x₁, hx₁⟩ | ⟨x₂, hx₂⟩
    · left; exact ⟨x₁, incl.injective ((hcomp₁ x₁).trans hx₁)⟩
    · right; exact ⟨x₂, incl.injective ((hcomp₂ x₂).trans hx₂)⟩

-- Preimage map restricted to range.
private noncomputable def nopInvOnRange {σ : FlagType} {H G : Flag σ}
    (b : InducedEmbedding σ H G) :
    { v : Fin G.size // v ∈ Set.range b.toFun } → Fin H.size :=
  fun ⟨_v, hv⟩ => hv.choose

private theorem nopInvOnRange_spec {σ : FlagType} {H G : Flag σ}
    (b : InducedEmbedding σ H G)
    (v : Fin G.size) (hv : v ∈ Set.range b.toFun) :
    b.toFun (nopInvOnRange b ⟨v, hv⟩) = v :=
  hv.choose_spec

private theorem nopInvOnRange_left_inv {σ : FlagType} {H G : Flag σ}
    (b : InducedEmbedding σ H G) (x : Fin H.size) :
    nopInvOnRange b ⟨b.toFun x, Set.mem_range_self x⟩ = x :=
  b.injective (nopInvOnRange_spec b (b.toFun x) (Set.mem_range_self x))

-- Construct automorphism α = b⁻¹ ∘ b' when range(b) = range(b').
private noncomputable def nopSameRangeAut {σ : FlagType} {H G : Flag σ}
    (b b' : InducedEmbedding σ H G)
    (hrange : Set.range b.toFun = Set.range b'.toFun) :
    InducedEmbedding σ H H where
  toFun v := nopInvOnRange b ⟨b'.toFun v, hrange ▸ Set.mem_range_self v⟩
  injective x y h := by
    have := congr_arg b.toFun h
    rw [nopInvOnRange_spec, nopInvOnRange_spec] at this
    exact b'.injective this
  map_adj u v hadj := by
    have hu := hrange.symm ▸ Set.mem_range_self (f := b'.toFun) u
    have hv := hrange.symm ▸ Set.mem_range_self (f := b'.toFun) v
    have hne : nopInvOnRange b ⟨b'.toFun u, hu⟩ ≠ nopInvOnRange b ⟨b'.toFun v, hv⟩ := by
      intro h; have := congr_arg b.toFun h
      rw [nopInvOnRange_spec, nopInvOnRange_spec] at this
      exact hadj.ne (b'.injective this)
    have hG : G.graph.Adj (b.toFun (nopInvOnRange b ⟨b'.toFun u, hu⟩))
                          (b.toFun (nopInvOnRange b ⟨b'.toFun v, hv⟩)) := by
      rw [nopInvOnRange_spec, nopInvOnRange_spec]; exact b'.map_adj _ _ hadj
    by_contra hnadj; exact absurd hG (b.map_non_adj _ _ hne hnadj)
  map_non_adj u v hne hnadj := by
    have hu := hrange.symm ▸ Set.mem_range_self (f := b'.toFun) u
    have hv := hrange.symm ▸ Set.mem_range_self (f := b'.toFun) v
    have hne' : nopInvOnRange b ⟨b'.toFun u, hu⟩ ≠ nopInvOnRange b ⟨b'.toFun v, hv⟩ := by
      intro h; have := congr_arg b.toFun h
      rw [nopInvOnRange_spec, nopInvOnRange_spec] at this
      exact hne (b'.injective this)
    intro hadj; exact absurd (b.map_adj _ _ hadj) (by
      rw [nopInvOnRange_spec, nopInvOnRange_spec]; exact b'.map_non_adj _ _ hne hnadj)
  compat i := by
    apply b.injective; rw [nopInvOnRange_spec, b'.compat, ← b.compat]

private theorem nopSameRangeAut_spec {σ : FlagType} {H G : Flag σ}
    (b b' : InducedEmbedding σ H G)
    (hrange : Set.range b.toFun = Set.range b'.toFun)
    (v : Fin H.size) :
    b.toFun ((nopSameRangeAut b b' hrange).toFun v) = b'.toFun v := by
  have hmem : b'.toFun v ∈ Set.range b.toFun :=
    hrange.symm ▸ Set.mem_range_self v
  change b.toFun (nopInvOnRange b ⟨b'.toFun v, hmem⟩) = b'.toFun v
  exact nopInvOnRange_spec _ _ _

-- Pullback embedding through an injective map.
private noncomputable def nopPullback {σ : FlagType} {F H G : Flag σ}
    (b : InducedEmbedding σ H G) (e : InducedEmbedding σ F G)
    (hrange : ∀ x, e.toFun x ∈ Set.range b.toFun) :
    InducedEmbedding σ F H where
  toFun x := nopInvOnRange b ⟨e.toFun x, hrange x⟩
  injective x y h := by
    have := congr_arg b.toFun h
    rw [nopInvOnRange_spec, nopInvOnRange_spec] at this
    exact e.injective this
  map_adj u v hadj := by
    have hne : nopInvOnRange b ⟨e.toFun u, hrange u⟩ ≠
        nopInvOnRange b ⟨e.toFun v, hrange v⟩ := by
      intro h; have := congr_arg b.toFun h
      rw [nopInvOnRange_spec, nopInvOnRange_spec] at this
      exact (SimpleGraph.Adj.ne hadj) (e.injective this)
    have hG : G.graph.Adj (b.toFun (nopInvOnRange b ⟨e.toFun u, hrange u⟩))
                          (b.toFun (nopInvOnRange b ⟨e.toFun v, hrange v⟩)) := by
      rw [nopInvOnRange_spec, nopInvOnRange_spec]; exact e.map_adj _ _ hadj
    by_contra hnadj; exact absurd hG (b.map_non_adj _ _ hne hnadj)
  map_non_adj u v hne hnadj := by
    have hne' : nopInvOnRange b ⟨e.toFun u, hrange u⟩ ≠
        nopInvOnRange b ⟨e.toFun v, hrange v⟩ := by
      intro h; have hh := congr_arg b.toFun h
      rw [nopInvOnRange_spec, nopInvOnRange_spec] at hh
      exact hne (e.injective hh)
    have hG : ¬G.graph.Adj (b.toFun (nopInvOnRange b ⟨e.toFun u, hrange u⟩))
                           (b.toFun (nopInvOnRange b ⟨e.toFun v, hrange v⟩)) := by
      rw [nopInvOnRange_spec, nopInvOnRange_spec]; exact e.map_non_adj _ _ hne hnadj
    intro hadj; exact hG (b.map_adj _ _ hadj)
  compat i := by
    apply b.injective; rw [nopInvOnRange_spec, e.compat, ← b.compat]

private theorem nopPullback_spec {σ : FlagType} {F H G : Flag σ}
    (b : InducedEmbedding σ H G) (e : InducedEmbedding σ F G)
    (hrange : ∀ x, e.toFun x ∈ Set.range b.toFun) :
    ∀ x, b.toFun ((nopPullback b e hrange).toFun x) = e.toFun x := by
  intro x; exact nopInvOnRange_spec b (e.toFun x) (hrange x)

private theorem nop_comp_pullback_eq {σ : FlagType} {F H G : Flag σ}
    (b : InducedEmbedding σ H G) (e : InducedEmbedding σ F G)
    (hrange : ∀ x, e.toFun x ∈ Set.range b.toFun) :
    b.comp (nopPullback b e hrange) = e := by
  apply nopExt'; ext x
  simp only [InducedEmbedding.comp, Function.comp_apply]
  exact congr_arg Fin.val (nopPullback_spec b e hrange x)

-- Equiv IE(H,H) ≃ {b : IE(H,G) // range(b) = range(b₀)}.
private noncomputable def nopSameRangeEquiv {σ : FlagType} {H G : Flag σ}
    (b₀ : InducedEmbedding σ H G) :
    InducedEmbedding σ H H ≃
      { b : InducedEmbedding σ H G // Set.range b.toFun = Set.range b₀.toFun } where
  toFun α := ⟨b₀.comp α, by
    ext x; simp only [InducedEmbedding.comp, Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨α.toFun y, rfl⟩
    · rintro ⟨y, hy⟩
      have hsurj : Function.Surjective α.toFun :=
        (Finite.injective_iff_surjective.mp α.injective)
      obtain ⟨z, rfl⟩ := hsurj y
      exact ⟨z, hy⟩⟩
  invFun bpair := nopSameRangeAut b₀ bpair.val bpair.property.symm
  left_inv α := by
    have hrange : Set.range b₀.toFun = Set.range (b₀.comp α).toFun := by
      ext x; simp only [InducedEmbedding.comp, Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨y, rfl⟩
        have hsurj := (Finite.injective_iff_surjective.mp α.injective)
        obtain ⟨z, rfl⟩ := hsurj y; exact ⟨z, rfl⟩
      · rintro ⟨y, rfl⟩; exact ⟨α.toFun y, rfl⟩
    change nopSameRangeAut b₀ (b₀.comp α) hrange = α
    have hfun : ∀ x, (nopSameRangeAut b₀ (b₀.comp α) hrange).toFun x = α.toFun x := by
      intro x; apply b₀.injective
      exact nopSameRangeAut_spec b₀ (b₀.comp α) hrange x
    exact nopExt' (funext hfun)
  right_inv bpair := by
    apply Subtype.ext
    have hfun : ∀ x,
        (b₀.comp (nopSameRangeAut b₀ bpair.val bpair.property.symm)).toFun x =
        bpair.val.toFun x := by
      intro x; change b₀.toFun ((nopSameRangeAut b₀ bpair.val bpair.property.symm).toFun x) =
        bpair.val.toFun x
      exact nopSameRangeAut_spec b₀ bpair.val bpair.property.symm x
    exact nopExt' (funext hfun)

-- Non-overlapping pair subtype: pairs (e₁,e₂) where overlap = σ-image (no covering).
private abbrev NOPSub (σ : FlagType) (F₁ F₂ G : Flag σ) :=
  { p : InducedEmbedding σ F₁ G × InducedEmbedding σ F₂ G //
    ∀ i : Fin G.size,
      (i ∈ Set.range p.1.toFun ∧ i ∈ Set.range p.2.toFun) ↔
        i ∈ Set.range G.embedding }

-- Joint count subtype: pairs with overlap = σ-image AND coverage of G.
-- (Duplicated from later in the file to avoid forward reference.)
private abbrev JCSub₂ (σ : FlagType) (F₁ F₂ G : Flag σ) :=
  { p : InducedEmbedding σ F₁ G × InducedEmbedding σ F₂ G //
    (∀ i : Fin G.size,
      (i ∈ Set.range p.1.toFun ∧ i ∈ Set.range p.2.toFun) ↔
        i ∈ Set.range G.embedding) ∧
    (∀ i : Fin G.size,
      i ∈ Set.range p.1.toFun ∨ i ∈ Set.range p.2.toFun) }

-- Classify an NOPSub pair by the intermediate iso class.
private noncomputable def nopIntermediateClass {σ : FlagType} {F₁ F₂ G : Flag σ}
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size)
    (t : NOPSub σ F₁ F₂ G) : FlagClass σ :=
  FlagClass.mk (nopSubflag t.val.1 t.val.2 t.property hn)

private theorem nopIntermediateClass_mem {σ : FlagType} {F₁ F₂ G : Flag σ}
    {n : ℕ} (hn : σ.size ≤ n) (hn_eq : n = F₁.size + F₂.size - σ.size)
    (t : NOPSub σ F₁ F₂ G) :
    nopIntermediateClass (hn_eq ▸ hn) t ∈ classesOfSize σ n hn := by
  set H := nopSubflag t.val.1 t.val.2 t.property (hn_eq ▸ hn)
  have hsize : H.size = n := by
    rw [hn_eq]; exact nopSubflag_size t.val.1 t.val.2 t.property _
  have hmem : FlagClass.mk H ∈ classesOfSize σ H.size H.hsize := by
    rw [classesOfSize, Finset.mem_image]
    exact ⟨⟨H.graph, H.embedding⟩, Finset.mem_univ _, rfl⟩
  convert hmem using 2; exact hsize.symm

-- Compose a JCSub pair with an IE to produce a NOPSub pair.
private theorem nop_compose_overlap {σ : FlagType} {F₁ F₂ H G : Flag σ}
    (a₁ : InducedEmbedding σ F₁ H) (a₂ : InducedEmbedding σ F₂ H)
    (b : InducedEmbedding σ H G)
    (hjc_overlap : ∀ i : Fin H.size,
      (i ∈ Set.range a₁.toFun ∧ i ∈ Set.range a₂.toFun) ↔
        i ∈ Set.range H.embedding) :
    ∀ i : Fin G.size,
      (i ∈ Set.range (b.comp a₁).toFun ∧ i ∈ Set.range (b.comp a₂).toFun) ↔
        i ∈ Set.range G.embedding := by
  intro i
  have hr1 : Set.range (b.comp a₁).toFun = b.toFun '' Set.range a₁.toFun :=
    InducedEmbedding.range_comp b a₁
  have hr2 : Set.range (b.comp a₂).toFun = b.toFun '' Set.range a₂.toFun :=
    InducedEmbedding.range_comp b a₂
  rw [hr1, hr2]; constructor
  · intro ⟨h1, h2⟩
    obtain ⟨x₁, hx₁, hx₁_eq⟩ := h1
    obtain ⟨x₂, hx₂, hx₂_eq⟩ := h2
    have h_eq : x₁ = x₂ := b.injective (hx₁_eq.trans hx₂_eq.symm)
    subst h_eq
    obtain ⟨j, rfl⟩ := (hjc_overlap x₁).mp ⟨hx₁, hx₂⟩
    exact ⟨j, (b.compat j).symm.trans hx₁_eq⟩
  · intro ⟨j, hj⟩
    have hemb := (hjc_overlap (H.embedding j)).mpr ⟨j, rfl⟩
    constructor
    · exact ⟨H.embedding j, hemb.1, (b.compat j).trans hj⟩
    · exact ⟨H.embedding j, hemb.2, (b.compat j).trans hj⟩

-- The composition map: JCSub(F₁,F₂;H) × IE(H,G) → NOPSub(F₁,F₂;G).
private noncomputable def nopComposeMap {σ : FlagType} {F₁ F₂ H G : Flag σ}
    (pair : JCSub₂ σ F₁ F₂ H × InducedEmbedding σ H G) :
    NOPSub σ F₁ F₂ G :=
  ⟨(pair.2.comp pair.1.val.1, pair.2.comp pair.1.val.2),
    nop_compose_overlap pair.1.val.1 pair.1.val.2 pair.2 pair.1.property.1⟩

-- The intermediate class of a composed pair equals [H].
private theorem nopComposeMap_class {σ : FlagType} {F₁ F₂ H G : Flag σ}
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size)
    (pair : JCSub₂ σ F₁ F₂ H × InducedEmbedding σ H G) :
    nopIntermediateClass hn (nopComposeMap pair) = FlagClass.mk H := by
  unfold nopIntermediateClass nopComposeMap; simp only; rw [FlagClass.mk_eq]
  set a₁ := pair.1.val.1; set a₂ := pair.1.val.2; set b := pair.2
  set hoverlap := nop_compose_overlap a₁ a₂ b pair.1.property.1
  set Sub := nopSubflag (b.comp a₁) (b.comp a₂) hoverlap hn
  set incl := nopSubflag_incl (b.comp a₁) (b.comp a₂) hoverlap hn
  have hincl_sub_b : ∀ x : Fin Sub.size,
      incl.toFun x ∈ Set.range b.toFun := by
    intro x
    have hi : incl.toFun x ∈ (nopFinset (b.comp a₁) (b.comp a₂) : Set (Fin G.size)) :=
      (nopSubflag_incl_range (b.comp a₁) (b.comp a₂) hoverlap hn).symm ▸ Set.mem_range_self x
    simp only [nopFinset, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
      true_and] at hi
    rcases hi with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨a₁.toFun y, hy⟩
    · exact ⟨a₂.toFun y, hy⟩
  set pb := nopPullback b incl hincl_sub_b
  have hsize_eq : Sub.size = H.size := by
    rw [nopSubflag_size (b.comp a₁) (b.comp a₂) hoverlap hn]
    let A := Finset.univ.filter (fun v : Fin H.size => v ∈ Set.range a₁.toFun)
    let B := Finset.univ.filter (fun v : Fin H.size => v ∈ Set.range a₂.toFun)
    have hA : A.card = F₁.size := by
      have : A = Finset.univ.image a₁.toFun := by
        ext v; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_image]; rfl
      rw [this, Finset.card_image_of_injective _ a₁.injective, Finset.card_fin]
    have hB : B.card = F₂.size := by
      have : B = Finset.univ.image a₂.toFun := by
        ext v; simp only [B, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_image]; rfl
      rw [this, Finset.card_image_of_injective _ a₂.injective, Finset.card_fin]
    have hAB : (A ∪ B).card = H.size := by
      have : A ∪ B = Finset.univ := by
        ext v; simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
          true_and]; exact iff_true_intro (pair.1.property.2 v)
      rw [this, Finset.card_univ, Fintype.card_fin]
    have hAinterB : (A ∩ B).card = σ.size := by
      have : A ∩ B = Finset.univ.image H.embedding := by
        ext v; simp only [A, B, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_image]; exact pair.1.property.1 v
      rw [this, Finset.card_image_of_injective _ H.embedding.injective, Finset.card_fin]
    have := Finset.card_union_add_card_inter A B; omega
  have pb_surj : Function.Surjective pb.toFun := by
    have := Finite.surjective_of_injective (f := pb.toFun ∘ Fin.cast hsize_eq.symm)
      (pb.injective.comp (Fin.cast_injective _))
    intro y; obtain ⟨x, hx⟩ := this y; exact ⟨Fin.cast hsize_eq.symm x, hx⟩
  set φ := Equiv.ofBijective pb.toFun ⟨pb.injective, pb_surj⟩
  have hmap : ∀ {u v}, H.graph.Adj (φ u) (φ v) ↔ Sub.graph.Adj u v := by
    intro u v; constructor
    · intro h; by_contra hnadj
      have hne : u ≠ v := fun heq => by subst heq; exact SimpleGraph.irrefl _ h
      exact absurd h (pb.map_non_adj u v hne hnadj)
    · exact pb.map_adj u v
  exact ⟨⟨φ, hmap⟩, fun i => pb.compat i⟩

-- Decompose a NOPSub pair: given t and b : IE(H,G) with range(b) = nopFinset,
-- produce a JCSub pair.
private noncomputable def nopDecompose {σ : FlagType} {F₁ F₂ H G : Flag σ}
    (t : NOPSub σ F₁ F₂ G) (b : InducedEmbedding σ H G)
    (hb_range : Set.range b.toFun = ↑(nopFinset t.val.1 t.val.2)) :
    JCSub₂ σ F₁ F₂ H × InducedEmbedding σ H G :=
  have h₁ : ∀ x, t.val.1.toFun x ∈ Set.range b.toFun := by
    intro x; rw [hb_range]
    simp only [nopFinset, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    left; exact Set.mem_range_self x
  have h₂ : ∀ x, t.val.2.toFun x ∈ Set.range b.toFun := by
    intro x; rw [hb_range]
    simp only [nopFinset, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    right; exact Set.mem_range_self x
  let a₁ := nopPullback b t.val.1 h₁
  let a₂ := nopPullback b t.val.2 h₂
  have jc_overlap : ∀ i : Fin H.size,
      (i ∈ Set.range a₁.toFun ∧ i ∈ Set.range a₂.toFun) ↔
        i ∈ Set.range H.embedding := by
    intro i; constructor
    · intro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
      have hbi : b.toFun i ∈ Set.range t.val.1.toFun :=
        ⟨x₁, by rw [← nopPullback_spec b t.val.1 h₁, ← congr_arg b.toFun hx₁]⟩
      have hbi' : b.toFun i ∈ Set.range t.val.2.toFun :=
        ⟨x₂, by rw [← nopPullback_spec b t.val.2 h₂, ← congr_arg b.toFun hx₂]⟩
      obtain ⟨j, hj⟩ := (t.property (b.toFun i)).mp ⟨hbi, hbi'⟩
      exact ⟨j, b.injective ((b.compat j).trans hj)⟩
    · intro ⟨j, hj⟩
      have hemb := (t.property (G.embedding j)).mpr ⟨j, rfl⟩
      constructor <;> [obtain ⟨x, hx⟩ := (b.compat j ▸ hemb.1 : b.toFun (H.embedding j) ∈ _);
                        obtain ⟨x, hx⟩ := (b.compat j ▸ hemb.2 : b.toFun (H.embedding j) ∈ _)]
      all_goals exact ⟨x, b.injective (by rw [nopPullback_spec, hx, congr_arg b.toFun hj])⟩
  have jc_cover : ∀ i : Fin H.size,
      i ∈ Set.range a₁.toFun ∨ i ∈ Set.range a₂.toFun := by
    intro i
    have hbi : b.toFun i ∈ (nopFinset t.val.1 t.val.2 : Set (Fin G.size)) := by
      rw [← hb_range]; exact Set.mem_range_self i
    simp only [nopFinset, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
      true_and] at hbi
    rcases hbi with ⟨x₁, hx₁⟩ | ⟨x₂, hx₂⟩
    · left; exact ⟨x₁, b.injective ((nopPullback_spec b t.val.1 h₁ x₁).trans hx₁)⟩
    · right; exact ⟨x₂, b.injective ((nopPullback_spec b t.val.2 h₂ x₂).trans hx₂)⟩
  (⟨(a₁, a₂), jc_overlap, jc_cover⟩, b)

-- Decompose then compose = identity (the b component is preserved).
private theorem nopDecompose_b {σ : FlagType} {F₁ F₂ H G : Flag σ}
    (t : NOPSub σ F₁ F₂ G) (b : InducedEmbedding σ H G)
    (hb_range : Set.range b.toFun = ↑(nopFinset t.val.1 t.val.2)) :
    (nopDecompose t b hb_range).2 = b := rfl

-- compose(decompose(t, b)) = t.
private theorem nopDecompose_compose {σ : FlagType} {F₁ F₂ H G : Flag σ}
    (t : NOPSub σ F₁ F₂ G) (b : InducedEmbedding σ H G)
    (hb_range : Set.range b.toFun = ↑(nopFinset t.val.1 t.val.2)) :
    nopComposeMap (nopDecompose t b hb_range) = t := by
  apply Subtype.ext; apply Prod.ext
  · -- First component: b.comp a₁ = t.val.1
    exact nop_comp_pullback_eq b t.val.1 _
  · -- Second component: b.comp a₂ = t.val.2
    exact nop_comp_pullback_eq b t.val.2 _

set_option maxHeartbeats 3200000 in
-- Per-class orbit counting (ℕ level): JC(F₁,F₂;H) * IC(H;G) = Aut(H) * |{NOP pairs with class [H]}|.
private theorem nop_per_class_counting {σ : FlagType} {F₁ F₂ G : Flag σ}
    {n : ℕ} (hn : σ.size ≤ n) (hn_eq : n = F₁.size + F₂.size - σ.size)
    (cls : FlagClass σ) (_hcls : cls ∈ classesOfSize σ n hn) :
    jointCount σ F₁ F₂ cls.out * inducedCount σ cls.out G =
    flagAutCount σ cls.out *
      (Finset.univ.filter (fun t : NOPSub σ F₁ F₂ G =>
        nopIntermediateClass (hn_eq ▸ hn) t = cls)).card := by
  set H := cls.out
  set fiber := Finset.univ.filter (fun t : NOPSub σ F₁ F₂ G =>
    nopIntermediateClass (hn_eq ▸ hn) t = cls)
  have hmap : ∀ pair : JCSub₂ σ F₁ F₂ H × InducedEmbedding σ H G,
      nopComposeMap pair ∈ fiber := fun pair => by
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [nopComposeMap_class (hn_eq ▸ hn) pair, FlagClass.mk, Quotient.out_eq]
  rw [show jointCount σ F₁ F₂ H = Fintype.card (JCSub₂ σ F₁ F₂ H) from rfl,
      show inducedCount σ H G = Fintype.card (InducedEmbedding σ H G) from rfl,
      show flagAutCount σ H = Fintype.card (InducedEmbedding σ H H) from rfl,
      ← Fintype.card_prod]
  have hfib_count :
      Fintype.card (JCSub₂ σ F₁ F₂ H × InducedEmbedding σ H G) =
      fiber.sum (fun t =>
        (Finset.univ.filter (fun pair : JCSub₂ σ F₁ F₂ H × InducedEmbedding σ H G =>
          nopComposeMap pair = t)).card) :=
    Finset.card_eq_sum_card_fiberwise (fun pair _ => hmap pair)
  rw [hfib_count]
  suffices hconst : ∀ t ∈ fiber,
      (Finset.univ.filter (fun pair : JCSub₂ σ F₁ F₂ H × InducedEmbedding σ H G =>
        nopComposeMap pair = t)).card =
      Fintype.card (InducedEmbedding σ H H) by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
  intro t ht
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  set Sub_t := nopSubflag t.val.1 t.val.2 t.property (hn_eq ▸ hn)
  have hiso_class : nopIntermediateClass (hn_eq ▸ hn) t = FlagClass.mk Sub_t := rfl
  have hH_cls : FlagClass.mk H = cls := Quotient.out_eq cls
  have hcls_eq : FlagClass.mk Sub_t = FlagClass.mk H := by rw [← hiso_class, ht, hH_cls]
  have ⟨iso, hiso_compat⟩ := (FlagClass.mk_eq _ _).mp hcls_eq
  set incl_t := nopSubflag_incl t.val.1 t.val.2 t.property (hn_eq ▸ hn)
  set b₀ := InducedEmbedding.mapIsoInv iso hiso_compat incl_t with hb₀_def
  have hb₀_range : Set.range b₀.toFun = ↑(nopFinset t.val.1 t.val.2) := by
    rw [hb₀_def, InducedEmbedding.range_mapIsoInv]
    exact nopSubflag_incl_range t.val.1 t.val.2 t.property (hn_eq ▸ hn)
  have hpreimage_range :
      ∀ pair : JCSub₂ σ F₁ F₂ H × InducedEmbedding σ H G,
      nopComposeMap pair = t →
      Set.range pair.2.toFun = Set.range b₀.toFun := by
    intro pair hpair
    have hval := congr_arg Subtype.val hpair
    have hfun1 : ∀ x, pair.2.toFun (pair.1.val.1.toFun x) = t.val.1.toFun x := fun x =>
      congr_fun (congr_arg InducedEmbedding.toFun (congr_arg (·.1) hval)) x
    have hfun2 : ∀ x, pair.2.toFun (pair.1.val.2.toFun x) = t.val.2.toFun x := fun x =>
      congr_fun (congr_arg InducedEmbedding.toFun (congr_arg (·.2) hval)) x
    rw [hb₀_range]; ext v; constructor
    · rintro ⟨w, rfl⟩
      simp only [nopFinset, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases pair.1.property.2 w with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · left; exact ⟨z, (hfun1 z).symm⟩
      · right; exact ⟨z, (hfun2 z).symm⟩
    · intro hv
      simp only [nopFinset, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      rcases hv with ⟨x, hx⟩ | ⟨x, hx⟩
      · exact ⟨pair.1.val.1.toFun x, (hfun1 x).trans hx⟩
      · exact ⟨pair.1.val.2.toFun x, (hfun2 x).trans hx⟩
  have hinj : ∀ pair₁ pair₂ : JCSub₂ σ F₁ F₂ H × InducedEmbedding σ H G,
      nopComposeMap pair₁ = t → nopComposeMap pair₂ = t →
      pair₁.2 = pair₂.2 → pair₁ = pair₂ := by
    intro p₁ p₂ hp₁ hp₂ hb_eq
    have hval₁ := congr_arg Subtype.val hp₁
    have hval₂ := congr_arg Subtype.val hp₂
    have heq₁ : p₁.2.comp p₁.1.val.1 = t.val.1 :=
      nopExt' (congr_arg InducedEmbedding.toFun (congr_arg (·.1) hval₁))
    have heq₂ : p₂.2.comp p₂.1.val.1 = t.val.1 :=
      nopExt' (congr_arg InducedEmbedding.toFun (congr_arg (·.1) hval₂))
    have heq₃ : p₁.2.comp p₁.1.val.2 = t.val.2 :=
      nopExt' (congr_arg InducedEmbedding.toFun (congr_arg (·.2) hval₁))
    have heq₄ : p₂.2.comp p₂.1.val.2 = t.val.2 :=
      nopExt' (congr_arg InducedEmbedding.toFun (congr_arg (·.2) hval₂))
    have ha₁ : p₁.1.val.1 = p₂.1.val.1 := by
      apply nopExt'; funext x; apply p₂.2.injective
      have : (p₁.2.comp p₁.1.val.1).toFun x = (p₂.2.comp p₂.1.val.1).toFun x := by
        rw [heq₁, heq₂]
      simp only [InducedEmbedding.comp, Function.comp_apply] at this
      rwa [hb_eq] at this
    have ha₂ : p₁.1.val.2 = p₂.1.val.2 := by
      apply nopExt'; funext x; apply p₂.2.injective
      have : (p₁.2.comp p₁.1.val.2).toFun x = (p₂.2.comp p₂.1.val.2).toFun x := by
        rw [heq₃, heq₄]
      simp only [InducedEmbedding.comp, Function.comp_apply] at this
      rwa [hb_eq] at this
    exact Prod.ext (Subtype.ext (Prod.ext ha₁ ha₂)) hb_eq
  apply Nat.le_antisymm
  · rw [← Fintype.card_coe, ← Fintype.card_congr (nopSameRangeEquiv b₀).symm]
    apply Fintype.card_le_of_injective
      (fun ⟨pair, hmem⟩ =>
        ⟨pair.2,
          hpreimage_range pair (by simpa only [Finset.mem_filter, Finset.mem_univ,
            true_and] using hmem)⟩)
    intro ⟨p₁, hm₁⟩ ⟨p₂, hm₂⟩ heq
    simp only [Subtype.mk.injEq] at heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hm₂
    exact Subtype.ext (hinj p₁ p₂ hm₁ hm₂ heq)
  · rw [← Fintype.card_coe]
    have hcomp_range : ∀ α : InducedEmbedding σ H H,
        Set.range (b₀.comp α).toFun = Set.range b₀.toFun := by
      intro α; ext v
      simp only [InducedEmbedding.comp, Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨α.toFun y, rfl⟩
      · rintro ⟨y, rfl⟩
        obtain ⟨z, rfl⟩ := (Finite.injective_iff_surjective.mp α.injective) y
        exact ⟨z, rfl⟩
    apply Fintype.card_le_of_injective (fun α => by
      exact ⟨nopDecompose t (b₀.comp α) (by rw [hcomp_range, hb₀_range]),
             by simp [Finset.mem_filter, nopDecompose_compose]⟩)
    intro α₁ α₂ heq
    simp only [Subtype.mk.injEq] at heq
    have hb_eq : b₀.comp α₁ = b₀.comp α₂ := by
      rw [← nopDecompose_b t (b₀.comp α₁) (by rw [hcomp_range, hb₀_range]),
          ← nopDecompose_b t (b₀.comp α₂) (by rw [hcomp_range, hb₀_range])]
      exact congr_arg (fun p =>
        (p : JCSub₂ σ F₁ F₂ H × InducedEmbedding σ H G).2) heq
    apply nopExt'; funext x
    have := congr_fun (congr_arg InducedEmbedding.toFun hb_eq) x
    simp only [InducedEmbedding.comp, Function.comp_apply] at this
    exact b₀.injective this

/-- **2-flag orbit counting** (thesis p.31): the orbit sum Σ_[H] JC(F,F';H) · IC(H;G) / Aut(H)
    counts non-overlapping embedding pairs, hence is ≤ IC(F;G) · IC(F';G).

    Each non-overlapping pair (e₁,e₂) determines an intermediate H = G[im(e₁)∪im(e₂)]
    of size n = |F|+|F'|-|σ|. The orbit sum counts such pairs grouped by iso class [H],
    with Aut(H) correcting for the choice of representative. This is the 2-flag analogue
    of `orbit_counting_factoring` (which handles 3 flags via ~1100 lines of fiber counting). -/
private theorem orbit_sum_le_product (σ : FlagType) (F F' G : Flag σ)
    (hn : σ.size ≤ F.size + F'.size - σ.size) :
    (classesOfSize σ (F.size + F'.size - σ.size) hn).sum (fun cls =>
        (jointCount σ F F' cls.out : ℝ) * (inducedCount σ cls.out G : ℝ) /
          (flagAutCount σ cls.out : ℝ)) ≤
      (inducedCount σ F G : ℝ) * (inducedCount σ F' G : ℝ) := by
  set n := F.size + F'.size - σ.size
  have hper : ∀ cls ∈ classesOfSize σ n hn,
      ((jointCount σ F F' cls.out : ℝ) * (inducedCount σ cls.out G : ℝ)) /
        (flagAutCount σ cls.out : ℝ) =
      ((Finset.univ.filter (fun t : NOPSub σ F F' G =>
        nopIntermediateClass hn t = cls)).card : ℝ) := by
    intro cls hcls
    have h := @nop_per_class_counting σ F F' G n hn rfl cls hcls
    rw [div_eq_iff (ne_of_gt (Nat.cast_pos.mpr (flagAutCount_pos σ cls.out))),
      show (jointCount σ F F' cls.out : ℝ) * (inducedCount σ cls.out G : ℝ) =
        (flagAutCount σ cls.out : ℝ) * ((Finset.univ.filter (fun t : NOPSub σ F F' G =>
          nopIntermediateClass hn t = cls)).card : ℝ) from by exact_mod_cast h, mul_comm]
  rw [Finset.sum_congr rfl hper]
  have hfib : (Finset.univ : Finset (NOPSub σ F F' G)).card =
      (classesOfSize σ n hn).sum (fun cls =>
        (Finset.univ.filter (fun t : NOPSub σ F F' G =>
          nopIntermediateClass hn t = cls)).card) :=
    Finset.card_eq_sum_card_fiberwise (fun t _ => nopIntermediateClass_mem hn rfl t)
  simp only [inducedCount]; rw [Finset.card_univ] at hfib
  calc ∑ cls ∈ classesOfSize σ n hn,
      ((Finset.univ.filter (fun t : NOPSub σ F F' G =>
        nopIntermediateClass hn t = cls)).card : ℝ)
      = (Fintype.card (NOPSub σ F F' G) : ℝ) := by exact_mod_cast hfib.symm
    _ ≤ (Fintype.card (InducedEmbedding σ F G) : ℝ) *
          (Fintype.card (InducedEmbedding σ F' G) : ℝ) := by
        have : Fintype.card (NOPSub σ F F' G) ≤
            Fintype.card (InducedEmbedding σ F G) * Fintype.card (InducedEmbedding σ F' G) := by
          rw [← Fintype.card_prod]
          exact Fintype.card_le_of_injective (fun t => t.val) Subtype.val_injective
        exact_mod_cast this

/-- **Overlap count bound** (thesis p.31): overlapping σ-embedding pairs of local flags F, F'
    are O(C(Δ, f) · C(Δ, f'-1)). Each overlapping pair shares at least one unlabelled
    vertex, so the overlap count is bounded by a constant (depending on F, F' and their
    bounded density constants) times C(Δ(G), f) · C(Δ(G), f'-1).

    The proof uses a counting argument: for each overlapping pair (e₁,e₂), pick a vertex
    v in the overlap im(e₁)∩im(e₂)∖σ. Overcounting by triples (e₁,e₂,v) and decomposing
    by v, we get overlap ≤ Σ_v A(v)·B(v) where A(v) = |{e₁:v∈im(e₁)}| and
    B(v) = |{e₂:v∈im(e₂)}|. Then Σ A(v) = f·IC(F;G) and max B(v) ≤ f'·C_ext·C(Δ,f'-1),
    giving the bound. Requires f+f' ≤ Δ(G) for the bounded density to yield count bounds. -/
private theorem overlap_count_le (σ : FlagType) (F F' : Flag σ)
    (𝒢 : GraphClass) (Δ : GraphParam)
    (hF : IsLocalFlag σ F 𝒢 Δ) (hF' : IsLocalFlag σ F' 𝒢 Δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : Flag σ, 𝒢 G.forget →
      F.size - σ.size + (F'.size - σ.size) ≤ Δ G.forget →
      (inducedCount σ F G : ℝ) * (inducedCount σ F' G : ℝ) -
        (classesOfSize σ (F.size + F'.size - σ.size)
          (by have := F.hsize; have := F'.hsize; omega)).sum (fun cls =>
            (jointCount σ F F' cls.out : ℝ) * (inducedCount σ cls.out G : ℝ) /
              (flagAutCount σ cls.out : ℝ)) ≤
        K * ((Nat.choose (Δ G.forget) (F.size - σ.size) : ℝ) *
             (Nat.choose (Δ G.forget) (F'.size - σ.size - 1) : ℝ)) := by
  set f := F.size - σ.size with hf_def
  set f' := F'.size - σ.size with hf'_def
  set hn_le : σ.size ≤ F.size + F'.size - σ.size :=
    (by have := F.hsize; have := F'.hsize; omega)
  have h_orbit_nn : ∀ G : Flag σ,
      0 ≤ (classesOfSize σ (F.size + F'.size - σ.size) hn_le).sum (fun cls =>
        (jointCount σ F F' cls.out : ℝ) * (inducedCount σ cls.out G : ℝ) /
          (flagAutCount σ cls.out : ℝ)) :=
    fun G => Finset.sum_nonneg (fun cls _ =>
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  obtain ⟨C_F, hCF_nn, hCF⟩ := hF.bounded
  by_cases hf'_zero : f' = 0
  · refine ⟨C_F, hCF_nn, fun G hG hΔ => ?_⟩
    have hsz : F'.size = σ.size := by have := F'.hsize; omega
    have hIC_F'_le : (inducedCount σ F' G : ℝ) ≤ 1 := by
      unfold inducedCount; rw [Nat.cast_le_one, Fintype.card_le_one_iff]
      intro a b
      have : a.toFun = b.toFun := by
        funext v; obtain ⟨i, rfl⟩ :=
          F'.embedding.injective.surjective_of_finite (finCongr hsz.symm) v
        exact a.compat i |>.trans (b.compat i).symm
      cases a; cases b; subst this; rfl
    rw [show F'.size - σ.size - 1 = 0 from by omega, Nat.choose_zero_right,
      Nat.cast_one, mul_one]
    calc (inducedCount σ F G : ℝ) * (inducedCount σ F' G : ℝ) -
          (classesOfSize σ _ hn_le).sum _ ≤
        (inducedCount σ F G : ℝ) * (inducedCount σ F' G : ℝ) := by linarith [h_orbit_nn G]
      _ ≤ (inducedCount σ F G : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hIC_F'_le (Nat.cast_nonneg _)
      _ = (inducedCount σ F G : ℝ) := mul_one _
      _ ≤ C_F * (Nat.choose (Δ G.forget) f : ℝ) := by
          have hld := hCF G hG; unfold localDensity at hld
          rwa [div_le_iff₀ (Nat.cast_pos.mpr (Nat.choose_pos (by omega)))] at hld
  have hf'_pos : 1 ≤ f' := Nat.one_le_iff_ne_zero.mpr hf'_zero
  have h_Cmax : ∃ C_max : ℝ, 0 ≤ C_max ∧
      ∀ (w : Fin F'.size) (hw : w ∉ Set.range F'.embedding),
        ∀ G' : Flag (LabelExtension.extendedType ⟨w, hw⟩), 𝒢 G'.forget →
          localDensity (LabelExtension.extendedType ⟨w, hw⟩)
            (LabelExtension.extendedFlag ⟨w, hw⟩) G' Δ ≤ C_max := by
    set S := (Finset.univ : Finset (Fin F'.size)).filter (· ∉ Set.range F'.embedding)
    suffices h : ∀ (T : Finset (Fin F'.size)), T ⊆ S →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ T, ∀ (hw : w ∉ Set.range F'.embedding),
          ∀ G' : Flag (LabelExtension.extendedType ⟨w, hw⟩), 𝒢 G'.forget →
            localDensity (LabelExtension.extendedType ⟨w, hw⟩)
              (LabelExtension.extendedFlag ⟨w, hw⟩) G' Δ ≤ C by
      obtain ⟨C, hC_nn, hC⟩ := h S Finset.Subset.rfl
      exact ⟨C, hC_nn, fun w hw =>
        hC w (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩) hw⟩
    intro T hTS
    induction T using Finset.induction with
    | empty => exact ⟨0, le_refl _, fun w hw => absurd hw (by simp)⟩
    | @insert a T' ha ih =>
      obtain ⟨C_prev, hCp_nn, hCp⟩ := ih ((Finset.subset_insert a T').trans hTS)
      have ha_unlab : a ∉ Set.range F'.embedding :=
        (Finset.mem_filter.mp (hTS (Finset.mem_insert_self a T'))).2
      obtain ⟨C_a, hCa_nn, hCa⟩ := (hF'.extensions ⟨a, ha_unlab⟩).bounded
      refine ⟨max C_prev C_a, le_max_of_le_left hCp_nn, fun w hw_mem hw G' hG' => ?_⟩
      rcases Finset.mem_insert.mp hw_mem with rfl | hw_mem
      · exact le_trans (hCa G' hG') (le_max_right _ _)
      · exact le_trans (hCp w hw_mem hw G' hG') (le_max_left _ _)
  obtain ⟨C_max, hCmax_nn, hCmax⟩ := h_Cmax
  set K := (f : ℝ) * f' * C_F * C_max with hK_def
  have hK_nn : 0 ≤ K := mul_nonneg (mul_nonneg (mul_nonneg
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hCF_nn) hCmax_nn
  refine ⟨K, hK_nn, fun G hG hΔ => ?_⟩
  have hfΔ : f ≤ Δ G.forget := by omega
  have hf'1Δ : f' - 1 ≤ Δ G.forget := by omega
  have hCDf_pos : (0 : ℝ) < (Nat.choose (Δ G.forget) f : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hfΔ)
  have hICF_bound : (inducedCount σ F G : ℝ) ≤
      C_F * (Nat.choose (Δ G.forget) f : ℝ) := by
    have hld := hCF G hG; unfold localDensity at hld
    rwa [div_le_iff₀ hCDf_pos] at hld
  have h_fiber_bound : ∀ (w : Fin F'.size) (hw : w ∉ Set.range F'.embedding)
      (v : Fin G.size) (_ : v ∉ Set.range G.embedding),
      ((Finset.univ.filter (fun e : InducedEmbedding σ F' G =>
        e.toFun w = v)).card : ℝ) ≤
      C_max * (Nat.choose (Δ G.forget) (f' - 1) : ℝ) := by
    intro w hw v hv
    by_cases h_empty :
        (Finset.univ.filter (fun e : InducedEmbedding σ F' G =>
          e.toFun w = v)) = ∅
    · simp [h_empty]; exact mul_nonneg hCmax_nn (Nat.cast_nonneg _)
    obtain ⟨e₀, he₀⟩ := Finset.nonempty_of_ne_empty h_empty
    rw [Finset.mem_filter] at he₀
    let ext : LabelExtension σ F' := ⟨w, hw⟩
    let extG : LabelExtension σ G := ⟨v, hv⟩
    have hcomp₀ : ∀ i, e₀.toFun (ext.vertexMap i) = extG.vertexMap i := by
      intro i
      obtain (⟨m, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
      · simp only [LabelExtension.vertexMap, Fin.lastCases_castSucc]; exact e₀.compat m
      · simp only [LabelExtension.vertexMap, Fin.lastCases_last]; exact he₀.2
    let extG_emb : ext.extendedType.graph ↪g G.graph :=
      ⟨⟨extG.vertexMap, extG.vertexMap_injective⟩, fun {a b} => by
        simp only [LabelExtension.extendedType, SimpleGraph.comap_adj]
        constructor
        · intro h; by_contra hna
          have hab : a ≠ b := fun heq => h.ne (congrArg extG.vertexMap heq)
          have hab' : ext.vertexMap a ≠ ext.vertexMap b :=
            fun heq => hab (ext.vertexMap_injective heq)
          have := e₀.map_non_adj _ _ hab' hna
          rw [hcomp₀ a, hcomp₀ b] at this; exact this h
        · intro h; have := e₀.map_adj _ _ h
          rwa [hcomp₀ a, hcomp₀ b] at this⟩
    let extGFlag : Flag ext.extendedType :=
      ⟨G.size, G.graph, extG_emb, extG.size_le⟩
    -- Fiber injects into IE(ext.type, ext.flag, extGFlag).
    have h_compat : ∀ (e : InducedEmbedding σ F' G), e.toFun w = v →
        ∀ i, e.toFun (ext.vertexMap i) = extG.vertexMap i := by
      intro e hev i
      obtain (⟨m, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
      · simp only [LabelExtension.vertexMap, Fin.lastCases_castSucc]; exact e.compat m
      · simp only [LabelExtension.vertexMap, Fin.lastCases_last]; exact hev
    have h_card_fiber :
        (Finset.univ.filter (fun e : InducedEmbedding σ F' G =>
          e.toFun w = v)).card ≤
        Fintype.card (InducedEmbedding ext.extendedType ext.extendedFlag extGFlag) := by
      have : Fintype.card {e : InducedEmbedding σ F' G // e.toFun w = v} ≤
          Fintype.card (InducedEmbedding ext.extendedType ext.extendedFlag extGFlag) := by
        apply Fintype.card_le_of_injective
          (fun (p : {e : InducedEmbedding σ F' G // e.toFun w = v}) =>
            (⟨p.val.toFun, p.val.injective, p.val.map_adj, p.val.map_non_adj,
              h_compat p.val p.prop⟩ :
              InducedEmbedding ext.extendedType ext.extendedFlag extGFlag))
        intro ⟨e₁, _⟩ ⟨e₂, _⟩ h_eq
        simp only [Subtype.mk.injEq]; dsimp only at h_eq
        have htf := congr_arg InducedEmbedding.toFun h_eq
        cases e₁; cases e₂; simp only [InducedEmbedding.mk.injEq] at htf ⊢; exact htf
      convert this using 1; rw [← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun e => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]))
    have hld := hCmax w hw extGFlag hG; unfold localDensity at hld
    rw [show ext.extendedFlag.size - ext.extendedType.size = f' - 1 from by
      simp only [LabelExtension.extendedFlag, LabelExtension.extendedType]; omega] at hld
    rw [div_le_iff₀ (Nat.cast_pos.mpr (Nat.choose_pos hf'1Δ))] at hld
    exact_mod_cast (Nat.cast_le (α := ℝ)).mpr h_card_fiber |>.trans hld
  suffices h_key : (inducedCount σ F G : ℝ) * (inducedCount σ F' G : ℝ) -
      (classesOfSize σ _ hn_le).sum (fun cls =>
        (jointCount σ F F' cls.out : ℝ) * (inducedCount σ cls.out G : ℝ) /
          (flagAutCount σ cls.out : ℝ)) ≤
      (inducedCount σ F G : ℝ) * ((f : ℝ) * f' * C_max *
        (Nat.choose (Δ G.forget) (f' - 1) : ℝ)) by
    calc (inducedCount σ F G : ℝ) * (inducedCount σ F' G : ℝ) -
          (classesOfSize σ _ hn_le).sum _ ≤
        (inducedCount σ F G : ℝ) * ((f : ℝ) * f' * C_max *
          (Nat.choose (Δ G.forget) (f' - 1) : ℝ)) := h_key
      _ ≤ (C_F * (Nat.choose (Δ G.forget) f : ℝ)) * ((f : ℝ) * f' * C_max *
            (Nat.choose (Δ G.forget) (f' - 1) : ℝ)) :=
        mul_le_mul_of_nonneg_right hICF_bound (mul_nonneg (mul_nonneg (mul_nonneg
          (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hCmax_nn) (Nat.cast_nonneg _))
      _ = K * ((Nat.choose (Δ G.forget) f : ℝ) *
              (Nat.choose (Δ G.forget) (f' - 1) : ℝ)) := by ring
  have haut_pos : ∀ cls ∈ classesOfSize σ _ hn_le,
      (0 : ℝ) < (flagAutCount σ cls.out : ℝ) := by
    intro cls _; exact Nat.cast_pos.mpr (flagAutCount_pos σ cls.out)
  have hper : ∀ cls ∈ classesOfSize σ _ hn_le,
      ((jointCount σ F F' cls.out : ℝ) * (inducedCount σ cls.out G : ℝ)) /
        (flagAutCount σ cls.out : ℝ) =
      ((Finset.univ.filter (fun t : NOPSub σ F F' G =>
        nopIntermediateClass hn_le t = cls)).card : ℝ) := by
    intro cls hcls
    have h := @nop_per_class_counting σ F F' G _ hn_le rfl cls hcls
    have hR : (jointCount σ F F' cls.out : ℝ) * (inducedCount σ cls.out G : ℝ) =
        (flagAutCount σ cls.out : ℝ) *
        ((Finset.univ.filter (fun t : NOPSub σ F F' G =>
          nopIntermediateClass hn_le t = cls)).card : ℝ) := by exact_mod_cast h
    rw [div_eq_iff (ne_of_gt (haut_pos cls hcls)), hR, mul_comm]
  rw [Finset.sum_congr rfl hper]
  have hfib : (Finset.univ : Finset (NOPSub σ F F' G)).card =
      (classesOfSize σ _ hn_le).sum (fun cls =>
        (Finset.univ.filter (fun t : NOPSub σ F F' G =>
          nopIntermediateClass hn_le t = cls)).card) :=
    Finset.card_eq_sum_card_fiberwise
      (fun t _ => nopIntermediateClass_mem hn_le rfl t)
  rw [Finset.card_univ] at hfib
  have h_orbit_nat : (Fintype.card (NOPSub σ F F' G) : ℝ) =
      ∑ cls ∈ classesOfSize σ _ hn_le,
        ((Finset.univ.filter (fun t : NOPSub σ F F' G =>
          nopIntermediateClass hn_le t = cls)).card : ℝ) := by
    exact_mod_cast hfib
  have h_nop_le_prod : Fintype.card (NOPSub σ F F' G) ≤
      Fintype.card (InducedEmbedding σ F G) *
        Fintype.card (InducedEmbedding σ F' G) := by
    rw [← Fintype.card_prod]
    exact Fintype.card_le_of_injective (fun t => t.val) Subtype.val_injective
  by_cases hIC_zero : inducedCount σ F G = 0
  · calc _ ≤ (0 : ℝ) := by
          simp only [show (inducedCount σ F G : ℝ) = 0 from by exact_mod_cast hIC_zero,
            zero_mul]; linarith [h_orbit_nn G]
      _ ≤ _ := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg
        (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hCmax_nn) (Nat.cast_nonneg _))
  have hIC_pos : 0 < inducedCount σ F G := Nat.pos_of_ne_zero hIC_zero
  set bad := fun (e₁ : InducedEmbedding σ F G) =>
    Finset.univ.filter (fun (e₂ : InducedEmbedding σ F' G) =>
      ∃ v : Fin G.size, v ∈ Set.range e₁.toFun ∧ v ∈ Set.range e₂.toFun ∧
        v ∉ Set.range G.embedding)
  set good := fun (e₁ : InducedEmbedding σ F G) =>
    Finset.univ.filter (fun (e₂ : InducedEmbedding σ F' G) =>
      ∀ i : Fin G.size,
        (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
          i ∈ Set.range G.embedding)
  set W := Finset.univ.filter
    (fun w : Fin F'.size => w ∉ Set.range F'.embedding)
  have hW_card : W.card = f' := by
    rw [show W = Finset.univ \ Finset.univ.image F'.embedding from by
      ext w; simp only [W, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_sdiff, Finset.mem_image, Set.mem_range],
      Finset.card_sdiff_of_subset (fun _ _ => Finset.mem_univ _), Finset.card_fin,
      Finset.card_image_of_injective _ F'.embedding.injective, Finset.card_fin]
  have h_per_e1 : ∀ e₁ : InducedEmbedding σ F G,
      ((bad e₁).card : ℝ) ≤
      (f : ℝ) * f' * C_max * (Nat.choose (Δ G.forget) (f' - 1) : ℝ) := by
    intro e₁
    set unlabImg := Finset.univ.filter (fun v : Fin G.size =>
      v ∈ Set.range e₁.toFun ∧ v ∉ Set.range G.embedding)
    have h_unlabImg_card : unlabImg.card = f := by
      have h_eq : unlabImg = (Finset.univ.filter
          (fun w : Fin F.size => w ∉ Set.range F.embedding)).image e₁.toFun := by
        ext v; constructor
        · intro hv
          simp only [unlabImg, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          obtain ⟨⟨w, rfl⟩, hv_ns⟩ := hv
          apply Finset.mem_image.mpr
          refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
          intro ⟨i, hi⟩
          exact hv_ns ⟨i, (hi ▸ e₁.compat i).symm⟩
        · intro hv
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
          simp only [unlabImg, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨⟨w, rfl⟩, fun ⟨i, hi⟩ => hw ⟨i, e₁.injective
            ((e₁.compat i).trans hi)⟩⟩
      rw [h_eq, Finset.card_image_of_injective _ e₁.injective]
      have : (Finset.univ.filter
          (fun w : Fin F.size => w ∉ Set.range F.embedding)) =
          Finset.univ \ Finset.univ.image F.embedding := by
        ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_sdiff, Finset.mem_image, Set.mem_range]
      rw [this, Finset.card_sdiff_of_subset (fun _ _ => Finset.mem_univ _),
        Finset.card_fin,
        Finset.card_image_of_injective _ F.embedding.injective,
        Finset.card_fin]
    have h_bad_sub : bad e₁ ⊆ unlabImg.biUnion (fun v =>
        Finset.univ.filter (fun e₂ : InducedEmbedding σ F' G =>
          v ∈ Set.range e₂.toFun)) := by
      intro e₂ he₂
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at he₂
      obtain ⟨v, hv₁, hv₂, hvσ⟩ := he₂
      exact Finset.mem_biUnion.mpr ⟨v,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv₁, hvσ⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv₂⟩⟩
    have h_per_v : ∀ v ∈ unlabImg,
        ((Finset.univ.filter (fun e₂ : InducedEmbedding σ F' G =>
          v ∈ Set.range e₂.toFun)).card : ℝ) ≤
        (f' : ℝ) * C_max * (Nat.choose (Δ G.forget) (f' - 1) : ℝ) := by
      intro v hv
      have hv_not_sigma : v ∉ Set.range G.embedding :=
        (Finset.mem_filter.mp hv).2.2
      have h_v_sub : Finset.univ.filter (fun e₂ : InducedEmbedding σ F' G =>
          v ∈ Set.range e₂.toFun) ⊆
        W.biUnion (fun w => Finset.univ.filter (fun e₂ : InducedEmbedding σ F' G =>
          e₂.toFun w = v)) := by
        intro e₂ he₂
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_range] at he₂
        obtain ⟨w, hw⟩ := he₂
        apply Finset.mem_biUnion.mpr
        refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩
        intro ⟨i, hi⟩
        exact hv_not_sigma ⟨i, by rw [← hw, ← hi, e₂.compat]⟩
      calc ((Finset.univ.filter (fun e₂ : InducedEmbedding σ F' G =>
            v ∈ Set.range e₂.toFun)).card : ℝ)
          ≤ (W.sum (fun w => (Finset.univ.filter
              (fun e₂ : InducedEmbedding σ F' G =>
              e₂.toFun w = v)).card) : ℝ) := by
            exact_mod_cast (Finset.card_le_card h_v_sub).trans Finset.card_biUnion_le
        _ ≤ W.sum (fun _ =>
              C_max * (Nat.choose (Δ G.forget) (f' - 1) : ℝ)) := by
            exact Finset.sum_le_sum fun w hw =>
              h_fiber_bound w ((Finset.mem_filter.mp hw).2) v hv_not_sigma
        _ = (f' : ℝ) * C_max * (Nat.choose (Δ G.forget) (f' - 1) : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, hW_card]; ring
    calc ((bad e₁).card : ℝ)
        ≤ (unlabImg.sum (fun v => (Finset.univ.filter
            (fun e₂ : InducedEmbedding σ F' G =>
            v ∈ Set.range e₂.toFun)).card) : ℝ) := by
          exact_mod_cast (Finset.card_le_card h_bad_sub).trans Finset.card_biUnion_le
      _ ≤ unlabImg.sum (fun _ =>
            (f' : ℝ) * C_max *
            (Nat.choose (Δ G.forget) (f' - 1) : ℝ)) := by
          exact Finset.sum_le_sum h_per_v
      _ = (f : ℝ) * f' * C_max *
            (Nat.choose (Δ G.forget) (f' - 1) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, h_unlabImg_card]; ring
  have h_bad_eq_compl : ∀ e₁ : InducedEmbedding σ F G,
      (bad e₁).card + (good e₁).card =
      Fintype.card (InducedEmbedding σ F' G) := by
    intro e₁
    suffices h_eq : bad e₁ = Finset.univ.filter
        (fun e₂ : InducedEmbedding σ F' G =>
          ¬∀ i : Fin G.size,
            (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
              i ∈ Set.range G.embedding) by
      have := @Finset.card_filter_add_card_filter_not _
        (Finset.univ : Finset (InducedEmbedding σ F' G))
        (fun e₂ : InducedEmbedding σ F' G =>
          ∀ i : Fin G.size,
            (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
              i ∈ Set.range G.embedding) _ _
      simp only [Finset.card_univ] at this
      rw [h_eq]; linarith
    ext e₂
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv₁, hv₂, hvσ⟩
      intro hh; exact hvσ ((hh v).mp ⟨hv₁, hv₂⟩)
    · intro hh
      by_contra h_all_good
      push_neg at h_all_good
      apply hh; intro v; constructor
      · intro ⟨hv₁, hv₂⟩; exact h_all_good v hv₁ hv₂
      · intro hvσ; obtain ⟨i, rfl⟩ := hvσ
        exact ⟨⟨F.embedding i, e₁.compat i⟩, ⟨F'.embedding i, e₂.compat i⟩⟩
  have h_nop_eq_good : Fintype.card (NOPSub σ F F' G) =
      Finset.univ.sum (fun e₁ : InducedEmbedding σ F G => (good e₁).card) := by
    rw [show Fintype.card (NOPSub σ F F' G) =
        Fintype.card (Σ (e₁ : InducedEmbedding σ F G),
          {e₂ : InducedEmbedding σ F' G //
            ∀ i : Fin G.size,
              (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
                i ∈ Set.range G.embedding}) from Fintype.card_congr {
      toFun := fun ⟨⟨e₁, e₂⟩, h⟩ => ⟨e₁, e₂, h⟩
      invFun := fun ⟨e₁, ⟨e₂, h⟩⟩ => ⟨⟨e₁, e₂⟩, h⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }, Fintype.card_sigma]
    congr 1; ext e₁; simp only [good, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun e₂ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]))
  have h_sum_add :
      Finset.univ.sum (fun e₁ : InducedEmbedding σ F G => (bad e₁).card) +
      Fintype.card (NOPSub σ F F' G) =
      Fintype.card (InducedEmbedding σ F G) * Fintype.card (InducedEmbedding σ F' G) := by
    rw [h_nop_eq_good, ← Finset.sum_add_distrib]; simp only [h_bad_eq_compl]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h_sum_le : (Finset.univ.sum (fun e₁ : InducedEmbedding σ F G =>
      (bad e₁).card) : ℝ) ≤
    (Fintype.card (InducedEmbedding σ F G) : ℝ) *
      ((f : ℝ) * f' * C_max * (Nat.choose (Δ G.forget) (f' - 1) : ℝ)) := by
    calc (∑ e₁ : InducedEmbedding σ F G, ((bad e₁).card : ℝ))
        ≤ ∑ _ : InducedEmbedding σ F G,
          ((f : ℝ) * f' * C_max * (Nat.choose (Δ G.forget) (f' - 1) : ℝ)) :=
        Finset.sum_le_sum (fun e₁ _ => h_per_e1 e₁)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← (by exact_mod_cast hfib : (Fintype.card (NOPSub σ F F' G) : ℝ) =
    ∑ cls ∈ classesOfSize σ _ hn_le, ((Finset.univ.filter (fun t : NOPSub σ F F' G =>
      nopIntermediateClass hn_le t = cls)).card : ℝ))]
  simp only [inducedCount]
  linarith [show (Finset.univ.sum (fun e₁ : InducedEmbedding σ F G =>
    (bad e₁).card) : ℝ) + (Fintype.card (NOPSub σ F F' G) : ℝ) =
    (Fintype.card (InducedEmbedding σ F G) : ℝ) *
    (Fintype.card (InducedEmbedding σ F' G) : ℝ) from by exact_mod_cast h_sum_add]

/-- **Embedding pair overlap bound** (thesis p.31, lines 431-453):
    For local flags F, F', the number of "overlapping" sigma-embedding pairs
    (those where unlabelled vertices share an image) is O(Delta^{f+f'-1}).
    Proved from `orbit_sum_le_product` (non-negativity) and `overlap_count_le` (upper bound). -/
private theorem overlap_embedding_bound (σ : FlagType) (F F' : Flag σ)
    (𝒢 : GraphClass) (Δ : GraphParam)
    (hF : IsLocalFlag σ F 𝒢 Δ) (hF' : IsLocalFlag σ F' 𝒢 Δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : Flag σ, 𝒢 G.forget →
      F.size - σ.size + (F'.size - σ.size) ≤ Δ G.forget →
      let n := F.size + F'.size - σ.size
      let f := F.size - σ.size
      let f' := F'.size - σ.size
      (0 : ℝ) ≤ (inducedCount σ F G : ℝ) * (inducedCount σ F' G : ℝ) -
        (if hn : σ.size ≤ n then
          (classesOfSize σ n hn).sum (fun cls =>
            (jointCount σ F F' cls.out : ℝ) * (inducedCount σ cls.out G : ℝ) /
              (flagAutCount σ cls.out : ℝ))
        else 0) ∧
      (inducedCount σ F G : ℝ) * (inducedCount σ F' G : ℝ) -
        (if hn : σ.size ≤ n then
          (classesOfSize σ n hn).sum (fun cls =>
            (jointCount σ F F' cls.out : ℝ) * (inducedCount σ cls.out G : ℝ) /
              (flagAutCount σ cls.out : ℝ))
        else 0) ≤
        K * ((Nat.choose (Δ G.forget) f : ℝ) *
             (Nat.choose (Δ G.forget) (f' - 1) : ℝ)) := by
  have hn_le : σ.size ≤ F.size + F'.size - σ.size := by
    have := F.hsize; have := F'.hsize; omega
  obtain ⟨K, hK_nn, hK_bound⟩ := overlap_count_le σ F F' 𝒢 Δ hF hF'
  refine ⟨K, hK_nn, fun G hG hΔ => ?_⟩
  constructor
  · -- Non-negativity: orbit sum ≤ IC_F * IC_F' from 2-flag orbit counting
    rw [dif_pos hn_le]
    linarith [orbit_sum_le_product σ F F' G hn_le]
  · -- Upper bound: overlap ≤ K * C(Δ,f) * C(Δ,f'-1) from overlap_count_le
    rw [dif_pos hn_le]
    exact hK_bound G hG hΔ

/-- C(Δ, k-1) / C(Δ, k) = k / (Δ - k + 1) for k ≤ Δ, k ≥ 1. -/
private theorem choose_ratio_pred (Δ k : ℕ) (hk : 1 ≤ k) (hkΔ : k ≤ Δ) :
    (Nat.choose Δ (k - 1) : ℝ) / (Nat.choose Δ k : ℝ) =
      (k : ℝ) / ((Δ : ℝ) - k + 1) := by
  -- From Nat.choose_succ_right_eq: C(Δ, k) * k = C(Δ, k-1) * (Δ - k + 1)
  -- So C(Δ, k-1) / C(Δ, k) = k / (Δ - k + 1)
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have hDk : 0 < Δ - k + 1 := by omega
  have hDk_r : (0 : ℝ) < (Δ - k + 1 : ℕ) := Nat.cast_pos.mpr hDk
  have hchoose_pos : (0 : ℝ) < (Nat.choose Δ k : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hkΔ)
  -- Key identity: C(Δ, k-1) * (Δ - (k-1)) = C(Δ, k) * k
  -- From choose_succ_right_eq: C(Δ, (k-1)+1) * ((k-1)+1) = C(Δ, k-1) * (Δ - (k-1))
  have key : Nat.choose Δ (k - 1) * (Δ - k + 1) = Nat.choose Δ k * k := by
    have hk1 := Nat.choose_succ_right_eq Δ (k - 1)
    have hkk : k - 1 + 1 = k := by omega
    rw [hkk] at hk1
    -- hk1 : C(Δ, k) * k = C(Δ, k-1) * (Δ - (k-1))
    have hsub : Δ - (k - 1) = Δ - k + 1 := by omega
    rw [hsub] at hk1; omega
  -- Rewrite as multiplication: C(Δ,k-1) * (Δ-k+1) = C(Δ,k) * k
  -- Both in ℝ: this gives the division identity
  have key_r : (Nat.choose Δ (k - 1) : ℝ) * (Δ - k + 1 : ℕ) =
      (Nat.choose Δ k : ℝ) * k := by exact_mod_cast key
  rw [show ((Δ : ℝ) - k + 1) = ((Δ - k + 1 : ℕ) : ℝ) from by
    rw [Nat.cast_add, Nat.cast_sub hkΔ, Nat.cast_one]]
  rw [div_eq_div_iff hchoose_pos.ne' hDk_r.ne']
  linarith

/-- The unlabelled evaluation of `localFlagProduct σ F F'` equals the orbit sum
    divided by (Aut_F · Aut_F'). -/
private theorem localFlagProduct_unlabelledEvalDensity (σ : FlagType) (F F' G : Flag σ)
    (Δ : GraphParam) :
    (localFlagProduct σ F F').unlabelledEvalDensity G Δ =
      ((flagAutCount σ F : ℝ) * (flagAutCount σ F' : ℝ))⁻¹ *
        (classesOfSize σ (F.size + F'.size - σ.size)
          (by have := F.hsize; have := F'.hsize; omega)).sum
          (fun cls => jointInducedDensity σ F F' cls.out *
            unlabelledDensity σ cls.out G Δ) := by
  set n := F.size + F'.size - σ.size
  have hn : σ.size ≤ n := by have := F.hsize; have := F'.hsize; omega
  -- Unfold localFlagProduct and eliminate the `if`
  have hprod : localFlagProduct σ F F' =
      ((flagAutCount σ F : ℝ) * (flagAutCount σ F' : ℝ))⁻¹ •
        (classesOfSize σ n hn).sum (fun cls =>
          Finsupp.single cls (jointInducedDensity σ F F' cls.out)) := by
    unfold localFlagProduct
    rw [dif_pos hn]
  rw [hprod, FlagAlg.unlabelledEvalDensity_pointwise_smul]
  congr 1
  -- Prove: ueD of a Finset.sum of Finsupp.singles = sum of coeff * classUnlabelledDensity
  -- First, a helper for single elements
  have hsingle : ∀ cls : FlagClass σ, ∀ c : ℝ,
      FlagAlg.unlabelledEvalDensity (Finsupp.single cls c) G Δ =
        c * classUnlabelledDensity σ G Δ cls := by
    intro cls c
    unfold FlagAlg.unlabelledEvalDensity
    exact Finsupp.sum_single_index (zero_mul _)
  -- Now prove ueD of the sum by Finset induction
  have ueval_sum : ∀ (T : Finset (FlagClass σ)) (h : FlagClass σ → ℝ),
      FlagAlg.unlabelledEvalDensity (T.sum (fun cls => Finsupp.single cls (h cls))) G Δ =
        T.sum (fun cls => h cls * classUnlabelledDensity σ G Δ cls) := by
    intro T h
    induction T using Finset.induction with
    | empty => simp [FlagAlg.unlabelledEvalDensity_zero]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, FlagAlg.unlabelledEvalDensity_add, ih,
        Finset.sum_insert ha, hsingle]
  rw [ueval_sum]
  apply Finset.sum_congr rfl
  intro cls _
  have : classUnlabelledDensity σ G Δ cls = unlabelledDensity σ cls.out G Δ := by
    unfold classUnlabelledDensity
    conv_lhs => rw [← Quotient.out_eq cls]
    exact Quotient.lift_mk _ _ _
  rw [this]

/-- **Theorem 2.3 (Basis case)**: For local basis flags F, F' ∈ 𝒢^σ_loc:
    ρ̃(F;G) · ρ̃(F';G) = ρ̃(F·F';G) + O(1/Δ(G)).

    The proof (thesis p.30, lines 374–463) decomposes the error into:
    1. A denominator ratio correction: C(Δ,f')/C(Δ-f,f') → 1 as Δ→∞.
    2. An overlap bound: pairs of embeddings that share unlabelled vertices
       number at most O(Δ^{f+f'-1}), using the IsLocalFlag extension property.
    Both terms are O(1/Δ), giving the result. -/
theorem product_limit_basis (σ : FlagType) (F F' : Flag σ)
    (𝒢 : GraphClass) (Δ : GraphParam)
    (hF : IsLocalFlag σ F 𝒢 Δ) (hF' : IsLocalFlag σ F' 𝒢 Δ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ Δ₀ : ℕ, ∀ G : Flag σ, 𝒢 G.forget → Δ₀ ≤ Δ G.forget →
        |unlabelledDensity σ F G Δ * unlabelledDensity σ F' G Δ -
         (localFlagProduct σ F F').unlabelledEvalDensity G Δ| ≤ ε := by
  intro ε hε
  set f := F.size - σ.size with hf_def
  set f' := F'.size - σ.size with hf'_def
  set n := F.size + F'.size - σ.size with hn_def
  obtain ⟨C_F, hCF_nn, hCF⟩ := hF.bounded
  obtain ⟨C_F', hCF'_nn, hCF'⟩ := hF'.bounded
  obtain ⟨K, hK_nn, hK_bound⟩ := overlap_embedding_bound σ F F' 𝒢 Δ hF hF'
  by_cases hf'_pos : f' = 0
  · exact ⟨0, fun G _ _ => by
      have hsz : F'.size = σ.size := by have := F'.hsize; omega
      rw [unlabelledDensity_of_size_eq F' G Δ hsz, unlabelledDensity_type_eq_one, mul_one,
        localFlagProduct_flagIso_right (flagIso_toFlag_of_size_eq F' hsz), product_unit,
        FlagAlg.unlabelledEvalDensity_single]
      simp [le_of_lt hε]⟩
  have hf'_ge : 1 ≤ f' := Nat.one_le_iff_ne_zero.mpr hf'_pos
  set M₁ := C_F * C_F' with hM₁_def
  have hM₁_nn : 0 ≤ M₁ := mul_nonneg hCF_nn hCF'_nn
  have hε₁ : 0 < ε / (2 * (M₁ + 1)) :=
    div_pos hε (mul_pos two_pos (by linarith))
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n →
      |(Nat.choose n f' : ℝ) / (Nat.choose (n - f) f' : ℝ) - 1| <
        ε / (2 * (M₁ + 1)) := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (choose_ratio_tendsto_one' f' f))
      _ hε₁
    exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩
  set N₂ := Nat.ceil (2 * K * (↑f' : ℝ) / ε) with hN₂_def
  refine ⟨max N₁ (N₂ + f + f'), fun G hG hΔ => ?_⟩
  set D := Δ G.forget with hD_def
  have hD_ge_N₁ : N₁ ≤ D := le_trans (le_max_left _ _) hΔ
  have hD_ge_N₂f' : N₂ + f' ≤ D := by
    have := le_trans (le_max_right N₁ (N₂ + f + f')) hΔ; omega
  have hf_le_D : f ≤ D := by
    have := le_trans (le_max_right N₁ (N₂ + f + f')) hΔ; omega
  have hff_le_D : f + f' ≤ D := by
    have := le_trans (le_max_right N₁ (N₂ + f + f')) hΔ; omega
  have density_decomposition :
      |unlabelledDensity σ F G Δ * unlabelledDensity σ F' G Δ -
        (localFlagProduct σ F F').unlabelledEvalDensity G Δ| ≤
      K * (Nat.choose D (f' - 1) : ℝ) / (Nat.choose D f' : ℝ) +
      M₁ * |(Nat.choose D f' : ℝ) / (Nat.choose (D - f) f' : ℝ) - 1| := by
    set IC_F := (inducedCount σ F G : ℝ) with hIC_F_def
    set IC_F' := (inducedCount σ F' G : ℝ) with hIC_F'_def
    set Aut_F := (flagAutCount σ F : ℝ) with hAut_F_def
    set Aut_F' := (flagAutCount σ F' : ℝ) with hAut_F'_def
    set CDF := (Nat.choose D f : ℝ) with hCDF_def
    set CDF' := (Nat.choose D f' : ℝ) with hCDF'_def
    set CDmfF' := (Nat.choose (D - f) f' : ℝ) with hCDmfF'_def
    set CDF'_1 := (Nat.choose D (f' - 1) : ℝ) with hCDF'_1_def
    have hAut_F_pos : 0 < Aut_F := Nat.cast_pos.mpr (flagAutCount_pos σ F)
    have hAut_F'_pos : 0 < Aut_F' := Nat.cast_pos.mpr (flagAutCount_pos σ F')
    have hCDF_pos : 0 < CDF := Nat.cast_pos.mpr (Nat.choose_pos hf_le_D)
    have hCDF'_pos : 0 < CDF' := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    have hCDmfF'_pos : 0 < CDmfF' := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    have hIC_F'_nn : 0 ≤ IC_F' := Nat.cast_nonneg _
    have hα_pos : 0 < (Aut_F * Aut_F')⁻¹ := inv_pos.mpr (mul_pos hAut_F_pos hAut_F'_pos)
    have hα_le_one : (Aut_F * Aut_F')⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_mul_of_one_le_of_one_le
        (Nat.one_le_cast.mpr (flagAutCount_pos σ F))
        (Nat.one_le_cast.mpr (flagAutCount_pos σ F')))
    have lhs_eq : unlabelledDensity σ F G Δ * unlabelledDensity σ F' G Δ =
        (Aut_F * Aut_F')⁻¹ * (IC_F * IC_F' / (CDF * CDF')) := by
      simp only [unlabelledDensity, localDensity, hD_def, hIC_F_def, hIC_F'_def,
        hAut_F_def, hAut_F'_def, hCDF_def, hCDF'_def]
      field_simp; ring
    set hn_le : σ.size ≤ F.size + F'.size - σ.size :=
      (by have := F.hsize; have := F'.hsize; omega) with hn_le_def
    set S := (classesOfSize σ n hn_le).sum (fun cls =>
        (jointCount σ F F' cls.out : ℝ) * (inducedCount σ cls.out G : ℝ) /
          (flagAutCount σ cls.out : ℝ)) with hS_def
    have hK_nonneg : 0 ≤ IC_F * IC_F' - S := by
      have h := (hK_bound G hG hff_le_D).1; rwa [dif_pos hn_le] at h
    have hK_upper : IC_F * IC_F' - S ≤ K * (CDF * CDF'_1) := by
      have h := (hK_bound G hG hff_le_D).2; rwa [dif_pos hn_le] at h
    have hS_nn' : 0 ≤ S := Finset.sum_nonneg fun cls _ =>
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    set Cff := (Nat.choose (f + f') f : ℝ) with hCff_def
    set CDff := (Nat.choose D (f + f') : ℝ) with hCDff_def
    have hCff_pos : 0 < Cff := Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_right f f'))
    have orbit_sum_eq :
        (classesOfSize σ n hn_le).sum (fun cls =>
          jointInducedDensity σ F F' cls.out * unlabelledDensity σ cls.out G Δ) =
        S / (Cff * CDff) := by
      have h_term : ∀ cls ∈ classesOfSize σ n hn_le,
          jointInducedDensity σ F F' cls.out * unlabelledDensity σ cls.out G Δ =
          (jointCount σ F F' cls.out : ℝ) * (inducedCount σ cls.out G : ℝ) /
            (flagAutCount σ cls.out : ℝ) / (Cff * CDff) := by
        intro cls hmem
        have hff_eq : cls.out.size - σ.size = f + f' := by
          have := classesOfSize_out_size hmem; have := F.hsize; have := F'.hsize; omega
        rw [show jointInducedDensity σ F F' cls.out =
            (jointCount σ F F' cls.out : ℝ) / Cff from by
          unfold jointInducedDensity
          rw [hff_eq, Nat.add_sub_cancel_left, Nat.choose_self, Nat.cast_one, mul_one],
          show unlabelledDensity σ cls.out G Δ =
            (inducedCount σ cls.out G : ℝ) / ((flagAutCount σ cls.out : ℝ) *
              (Nat.choose (Δ G.forget) (cls.out.size - σ.size) : ℝ)) from by
          unfold unlabelledDensity localDensity; rw [div_div, mul_comm],
          hff_eq, div_mul_div_comm, div_div]
        congr 1; ring
      rw [Finset.sum_congr rfl h_term, ← Finset.sum_div]
    have rhs_eq : (localFlagProduct σ F F').unlabelledEvalDensity G Δ =
        (Aut_F * Aut_F')⁻¹ * (S / (Cff * CDff)) := by
      rw [localFlagProduct_unlabelledEvalDensity, orbit_sum_eq]
    have hvand' : Cff * CDff = CDF * CDmfF' := by
      rw [mul_comm]; simp only [hCDff_def, hCff_def, hCDF_def, hCDmfF'_def]
      exact_mod_cast choose_vandermonde D f f' hf_le_D hff_le_D
    have diff_factored : unlabelledDensity σ F G Δ * unlabelledDensity σ F' G Δ -
        (localFlagProduct σ F F').unlabelledEvalDensity G Δ =
        (Aut_F * Aut_F')⁻¹ / CDF *
          ((IC_F * IC_F' - S) / CDF' +
           S * (1 / CDF' - 1 / CDmfF')) := by
      rw [lhs_eq, rhs_eq, hvand', mul_sub]; field_simp; ring
    have term1_bound : (Aut_F * Aut_F')⁻¹ / CDF * ((IC_F * IC_F' - S) / CDF') ≤
        K * CDF'_1 / CDF' := by
      calc (Aut_F * Aut_F')⁻¹ / CDF * ((IC_F * IC_F' - S) / CDF')
          ≤ (IC_F * IC_F' - S) / (CDF * CDF') := by
            rw [div_mul_div_comm]
            exact div_le_div_of_nonneg_right
              (by linarith [mul_le_mul_of_nonneg_right hα_le_one hK_nonneg])
              (mul_pos hCDF_pos hCDF'_pos).le
        _ ≤ K * CDF'_1 / CDF' := by
            rw [div_le_div_iff₀ (mul_pos hCDF_pos hCDF'_pos) hCDF'_pos]
            linarith [mul_le_mul_of_nonneg_right hK_upper hCDF'_pos.le,
              show K * (CDF * CDF'_1) * CDF' = K * CDF'_1 * (CDF * CDF') by ring]
    have hαS_bound : (Aut_F * Aut_F')⁻¹ * S / (CDF * CDF') ≤ M₁ := by
      calc (Aut_F * Aut_F')⁻¹ * S / (CDF * CDF')
          ≤ IC_F * IC_F' / (CDF * CDF') :=
            div_le_div_of_nonneg_right
              (by linarith [mul_le_mul_of_nonneg_right hα_le_one hS_nn'])
              (mul_pos hCDF_pos hCDF'_pos).le
        _ ≤ M₁ := by
            rw [div_le_iff₀ (mul_pos hCDF_pos hCDF'_pos)]
            calc IC_F * IC_F'
                ≤ (C_F * CDF) * (C_F' * CDF') :=
                  mul_le_mul
                    (by have := hCF G hG; simp only [localDensity] at this;
                        rwa [div_le_iff₀ hCDF_pos] at this)
                    (by have := hCF' G hG; simp only [localDensity] at this;
                        rwa [div_le_iff₀ hCDF'_pos] at this)
                    hIC_F'_nn (mul_nonneg hCF_nn hCDF_pos.le)
              _ = M₁ * (CDF * CDF') := by ring
    have term2_bound :
        |(Aut_F * Aut_F')⁻¹ / CDF * (S * (1 / CDF' - 1 / CDmfF'))| ≤
        M₁ * |CDF' / CDmfF' - 1| := by
      rw [abs_mul, abs_of_nonneg (div_nonneg hα_pos.le hCDF_pos.le),
        abs_mul, abs_of_nonneg hS_nn']
      rw [show |1 / CDF' - 1 / CDmfF'| = |CDF' / CDmfF' - 1| / CDF' from by
        rw [show (1 / CDF' - 1 / CDmfF') = (CDmfF' - CDF') / (CDF' * CDmfF') from by
              field_simp,
          show (CDF' / CDmfF' - 1) = (CDF' - CDmfF') / CDmfF' from by field_simp,
          abs_div, abs_div, abs_of_pos (mul_pos hCDF'_pos hCDmfF'_pos),
          abs_of_pos hCDmfF'_pos, div_div, abs_sub_comm, mul_comm CDmfF' CDF'],
        show (Aut_F * Aut_F')⁻¹ / CDF * (S * (|CDF' / CDmfF' - 1| / CDF')) =
          (Aut_F * Aut_F')⁻¹ * S / (CDF * CDF') * |CDF' / CDmfF' - 1| from by field_simp]
      exact mul_le_mul_of_nonneg_right hαS_bound (abs_nonneg _)
    rw [diff_factored]
    calc |(Aut_F * Aut_F')⁻¹ / CDF * ((IC_F * IC_F' - S) / CDF' + S * (1 / CDF' - 1 / CDmfF'))|
        ≤ |(Aut_F * Aut_F')⁻¹ / CDF * ((IC_F * IC_F' - S) / CDF')| +
          |(Aut_F * Aut_F')⁻¹ / CDF * (S * (1 / CDF' - 1 / CDmfF'))| := by
          rw [mul_add]; exact abs_add_le _ _
      _ ≤ K * CDF'_1 / CDF' + M₁ * |CDF' / CDmfF' - 1| := by
          apply add_le_add _ term2_bound
          rw [abs_of_nonneg]
          · exact term1_bound
          · exact mul_nonneg (div_nonneg hα_pos.le hCDF_pos.le)
              (div_nonneg (by linarith) hCDF'_pos.le)
  calc |unlabelledDensity σ F G Δ * unlabelledDensity σ F' G Δ -
        (localFlagProduct σ F F').unlabelledEvalDensity G Δ|
    ≤ K * (Nat.choose D (f' - 1) : ℝ) / (Nat.choose D f' : ℝ) +
      M₁ * |(Nat.choose D f' : ℝ) / (Nat.choose (D - f) f' : ℝ) - 1| :=
      density_decomposition
    _ ≤ K * (↑f' : ℝ) / ((D : ℝ) - ↑f' + 1) + M₁ * |(Nat.choose D f' : ℝ) /
        (Nat.choose (D - f) f' : ℝ) - 1| := by
      rw [mul_div_assoc, choose_ratio_pred D f' hf'_ge (by omega : f' ≤ D), ← mul_div_assoc]
    _ ≤ ε / 2 + ε / 2 := by
      apply add_le_add
      · -- overlap bound: K * f' / (D - f' + 1) ≤ ε / 2
        have hKf'_nn : 0 ≤ K * (↑f' : ℝ) := mul_nonneg hK_nn (Nat.cast_nonneg _)
        have hDmf'_pos : (0 : ℝ) < (D : ℝ) - ↑f' + 1 := by
          have : (↑f' : ℝ) ≤ (D : ℝ) := Nat.cast_le.mpr (by omega : f' ≤ D); linarith
        rcases eq_or_lt_of_le hKf'_nn with hKf'_zero | _
        · rw [← hKf'_zero, zero_div]; exact le_of_lt (half_pos hε)
        · rw [div_le_div_iff₀ hDmf'_pos two_pos]
          have hN₂_le_D : (N₂ : ℝ) ≤ (D : ℝ) - ↑f' := by
            have : (↑(N₂ + f') : ℝ) ≤ (D : ℝ) := Nat.cast_le.mpr hD_ge_N₂f'
            push_cast at this ⊢; linarith
          nlinarith [(div_le_iff₀ hε).mp (le_trans (Nat.le_ceil _) hN₂_le_D)]
      · -- ratio bound: M₁ * |C(D,f')/C(D-f,f') - 1| ≤ ε / 2
        calc M₁ * |(Nat.choose D f' : ℝ) / (Nat.choose (D - f) f' : ℝ) - 1|
          ≤ M₁ * (ε / (2 * (M₁ + 1))) :=
            mul_le_mul_of_nonneg_left (le_of_lt (hN₁ D hD_ge_N₁)) hM₁_nn
          _ = ε * (M₁ / (2 * (M₁ + 1))) := by ring
          _ ≤ ε * (1 / 2) := mul_le_mul_of_nonneg_left
              (by rw [div_le_div_iff₀ (mul_pos two_pos (by linarith : (0:ℝ) < M₁ + 1)) two_pos]
                  nlinarith) hε.le
          _ = ε / 2 := by ring
    _ = ε := by ring

/-! ### Linear extension of product limit -/

set_option maxHeartbeats 800000 in
/-- **Theorem 2.3 (Full)**: The product limit theorem for arbitrary elements of 𝓛^σ.
    Proved from `product_limit_basis` by bilinearity: the difference decomposes as
    a finite sum of basis-level differences, each bounded by ε/W for large Δ,
    where W = (Σ|cᵢ|)·(Σ|dⱼ|) is the total coefficient weight. -/
theorem product_limit (σ : FlagType)
    (f g : FlagAlg σ)
    (𝒢 : GraphClass) (Δ : GraphParam)
    (hf_local : ∀ cls ∈ f.support, IsLocalFlag σ cls.out 𝒢 Δ)
    (hg_local : ∀ cls ∈ g.support, IsLocalFlag σ cls.out 𝒢 Δ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ Δ₀ : ℕ, ∀ G : Flag σ, 𝒢 G.forget → Δ₀ ≤ Δ G.forget →
        |f.unlabelledEvalDensity G Δ * g.unlabelledEvalDensity G Δ -
         (f.mul g).unlabelledEvalDensity G Δ| ≤ ε := by
  intro ε hε
  by_cases hf : f = 0
  · exact ⟨0, fun G _ _ => by
      simp only [hf, FlagAlg.unlabelledEvalDensity_zero, zero_mul, FlagAlg.mul,
        Finsupp.sum_zero_index, sub_self, abs_zero]; exact hε.le⟩
  by_cases hg : g = 0
  · exact ⟨0, fun G _ _ => by
      subst hg; simp only [FlagAlg.unlabelledEvalDensity_zero, mul_zero, FlagAlg.mul]
      have : (f.sum fun cls₁ c₁ => (0 : FlagAlg σ).sum fun cls₂ c₂ =>
          (c₁ * c₂) • localFlagProduct_class σ cls₁ cls₂) = 0 :=
        Finset.sum_eq_zero (fun cls _ => Finsupp.sum_zero_index)
      rw [this, FlagAlg.unlabelledEvalDensity_zero, sub_self, abs_zero]; exact hε.le⟩
  set Sf := f.support; set Sg := g.support
  set Wf := Sf.sum (fun cls => |f cls|); set Wg := Sg.sum (fun cls => |g cls|)
  have hWf_pos : 0 < Wf := Finset.sum_pos (fun cls hcls =>
    abs_pos.mpr (Finsupp.mem_support_iff.mp hcls)) (Finsupp.support_nonempty_iff.mpr hf)
  have hWg_pos : 0 < Wg := Finset.sum_pos (fun cls hcls =>
    abs_pos.mpr (Finsupp.mem_support_iff.mp hcls)) (Finsupp.support_nonempty_iff.mpr hg)
  have hW_pos : 0 < Wf * Wg := mul_pos hWf_pos hWg_pos
  set ε' := ε / (Wf * Wg)
  choose Δ₀_fn hΔ₀_fn using fun (x : {cls // cls ∈ Sf}) (y : {cls // cls ∈ Sg}) =>
    product_limit_basis σ x.1.out y.1.out 𝒢 Δ
      (hf_local x.1 x.2) (hg_local y.1 y.2) ε' (div_pos hε hW_pos)
  refine ⟨(Sf.attach ×ˢ Sg.attach).sup (fun p => Δ₀_fn p.1 p.2), fun G hG hΔ => ?_⟩
  have hpair : ∀ cls₁ ∈ Sf, ∀ cls₂ ∈ Sg,
      |unlabelledDensity σ cls₁.out G Δ * unlabelledDensity σ cls₂.out G Δ -
       (localFlagProduct σ cls₁.out cls₂.out).unlabelledEvalDensity G Δ| ≤ ε' := by
    intro cls₁ h₁ cls₂ h₂
    exact hΔ₀_fn ⟨cls₁, h₁⟩ ⟨cls₂, h₂⟩ G hG
      (le_trans (Finset.le_sup (f := fun p => Δ₀_fn p.1 p.2)
        (show (⟨cls₁, h₁⟩, ⟨cls₂, h₂⟩) ∈ Sf.attach ×ˢ Sg.attach from
          Finset.mem_product.mpr ⟨Finset.mem_attach _ _, Finset.mem_attach _ _⟩)) hΔ)
  have hρ : ∀ cls, classUnlabelledDensity σ G Δ cls = unlabelledDensity σ cls.out G Δ := by
    intro cls; unfold classUnlabelledDensity; conv_lhs => rw [← Quotient.out_eq cls]
    exact Quotient.lift_mk _ _ _
  set ρ := fun cls => unlabelledDensity σ (Quotient.out cls) G Δ
  have ueval_sum : ∀ (S : Finset (FlagClass σ)) (h : FlagClass σ → FlagAlg σ),
      (S.sum h).unlabelledEvalDensity G Δ =
        S.sum (fun cls => (h cls).unlabelledEvalDensity G Δ) := by
    intro S h; induction S using Finset.induction with
    | empty => simp [FlagAlg.unlabelledEvalDensity_zero]
    | @insert a s ha ih => rw [Finset.sum_insert ha,
        FlagAlg.unlabelledEvalDensity_add, ih, Finset.sum_insert ha]
  have heval_mul : (f.mul g).unlabelledEvalDensity G Δ =
      Sf.sum (fun cls₁ => Sg.sum (fun cls₂ => f cls₁ * g cls₂ *
          (localFlagProduct σ cls₁.out cls₂.out).unlabelledEvalDensity G Δ)) := by
    simp only [FlagAlg.mul, Finsupp.sum]; rw [ueval_sum]; congr 1; ext cls₁; rw [ueval_sum]
    congr 1; ext cls₂; rw [FlagAlg.unlabelledEvalDensity_pointwise_smul,
      congrArg (·.unlabelledEvalDensity G Δ) (localFlagProduct_class_out σ cls₁ cls₂)]
  have heval_fg : ∀ (v : FlagAlg σ), v.unlabelledEvalDensity G Δ =
      v.support.sum (fun cls => v cls * ρ cls) := fun v => by
    simp only [FlagAlg.unlabelledEvalDensity, Finsupp.sum]; congr 1; ext cls; rw [hρ]
  rw [show f.unlabelledEvalDensity G Δ * g.unlabelledEvalDensity G Δ -
      (f.mul g).unlabelledEvalDensity G Δ =
      Sf.sum (fun cls₁ => Sg.sum (fun cls₂ => f cls₁ * g cls₂ *
        (ρ cls₁ * ρ cls₂ -
          (localFlagProduct σ cls₁.out cls₂.out).unlabelledEvalDensity G Δ))) from by
    rw [heval_fg f, heval_fg g, Finset.sum_mul, heval_mul, ← Finset.sum_sub_distrib]
    congr 1; ext cls₁; rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1; ext cls₂; ring]
  calc |Sf.sum (fun cls₁ => Sg.sum (fun cls₂ => f cls₁ * g cls₂ *
          (ρ cls₁ * ρ cls₂ -
            (localFlagProduct σ cls₁.out cls₂.out).unlabelledEvalDensity G Δ)))|
      ≤ Sf.sum (fun cls₁ => |Sg.sum (fun cls₂ => f cls₁ * g cls₂ *
          (ρ cls₁ * ρ cls₂ -
            (localFlagProduct σ cls₁.out cls₂.out).unlabelledEvalDensity G Δ))|) :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ Sf.sum (fun cls₁ => Sg.sum (fun cls₂ => |f cls₁ * g cls₂ *
          (ρ cls₁ * ρ cls₂ -
            (localFlagProduct σ cls₁.out cls₂.out).unlabelledEvalDensity G Δ)|)) := by
        gcongr with cls₁ _; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ Sf.sum (fun cls₁ => Sg.sum (fun cls₂ => |f cls₁| * |g cls₂| * ε')) := by
        gcongr with cls₁ h₁ cls₂ h₂; rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hpair cls₁ h₁ cls₂ h₂)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = Wf * Wg * ε' := by simp only [← Finset.sum_mul, ← Finset.mul_sum]; ring
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hW_pos)

/-! ## §2.2: Algebra Properties (Lemma 2.4)

We need the chain rule for induced densities from the classic flag algebra
(Thesis Lemma 1.3, Razborov Thm 2.5). This does NOT hold for local densities
but it holds for the induced density p, which is what the product definition uses. -/

-- **Chain Rule for induced densities** (Thesis Lemma 1.3, Razborov Thm 2.5):
-- Σ_{H ∈ 𝒢^σ_ℓ} p(F₁, F₂; H) · p(H, F₃; G) = p(F₁, F₂, F₃; G)
-- where p(F₁,F₂,F₃;G) is the multi-flag joint density.
-- This reduces the product of two sums into a single symmetric sum.
-- Used implicitly in the associativity proof below.


/-- The multinomial denominator is symmetric: C(n,a)·C(n-a,b) = C(n,b)·C(n-b,a).
    Both sides equal n!/(a!·b!·(n-a-b)!). -/
theorem choose_mul_choose_comm (n a b : ℕ) (hab : a + b ≤ n) :
    (Nat.choose n a : ℝ) * (Nat.choose (n - a) b : ℝ) =
    (Nat.choose n b : ℝ) * (Nat.choose (n - b) a : ℝ) := by
  have ha : a ≤ n := le_trans (Nat.le_add_right a b) hab
  have hb : b ≤ n := le_trans (Nat.le_add_left b a) hab
  have hba : b ≤ n - a := by omega
  have hab' : a ≤ n - b := by omega
  suffices h : Nat.choose n a * Nat.choose (n - a) b =
      Nat.choose n b * Nat.choose (n - b) a by exact_mod_cast h
  -- Both sides times a!·b!·(n-a-b)! equal n!
  set c := a.factorial * b.factorial * (n - a - b).factorial
  have hc : 0 < c :=
    Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) (Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_right hc
  have lhs : Nat.choose n a * Nat.choose (n - a) b * c = n.factorial := by
    calc Nat.choose n a * Nat.choose (n - a) b * c
        = Nat.choose n a * (Nat.choose (n - a) b * b.factorial * (n - a - b).factorial) *
          a.factorial := by ring
      _ = Nat.choose n a * (n - a).factorial * a.factorial := by
          rw [Nat.choose_mul_factorial_mul_factorial hba]
      _ = Nat.choose n a * a.factorial * (n - a).factorial := by ring
      _ = n.factorial := Nat.choose_mul_factorial_mul_factorial ha
  have rhs : Nat.choose n b * Nat.choose (n - b) a * c = n.factorial := by
    have hsub : n - a - b = n - b - a := by omega
    calc Nat.choose n b * Nat.choose (n - b) a * c
        = Nat.choose n b * (Nat.choose (n - b) a * a.factorial * (n - a - b).factorial) *
          b.factorial := by ring
      _ = Nat.choose n b * (Nat.choose (n - b) a * a.factorial * (n - b - a).factorial) *
          b.factorial := by rw [hsub]
      _ = Nat.choose n b * (n - b).factorial * b.factorial := by
          rw [Nat.choose_mul_factorial_mul_factorial hab']
      _ = Nat.choose n b * b.factorial * (n - b).factorial := by ring
      _ = n.factorial := Nat.choose_mul_factorial_mul_factorial hb
  linarith

/-- The **trinomial identity**: C(n,k)·C(k,j) = C(n,j)·C(n-j,k-j).
    Both sides equal n!/(j!·(k-j)!·(n-k)!). This is the Vandermonde-type identity
    that relates factoring a triple partition in two different orders.
    (Used in the density chain rule proof.) -/
private theorem choose_mul_choose_trinomial (n k j : ℕ) (hj : j ≤ k) (hk : k ≤ n) :
    (Nat.choose n k : ℝ) * (Nat.choose k j : ℝ) =
    (Nat.choose n j : ℝ) * (Nat.choose (n - j) (k - j) : ℝ) := by
  have hj_n : j ≤ n := le_trans hj hk
  have hkj : k - j ≤ n - j := Nat.sub_le_sub_right hk j
  suffices h : Nat.choose n k * Nat.choose k j =
      Nat.choose n j * Nat.choose (n - j) (k - j) by exact_mod_cast h
  -- Both sides times j!·(k-j)!·(n-k)! equal n!
  set c := j.factorial * (k - j).factorial * (n - k).factorial
  have hc : 0 < c :=
    Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)) (Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_right hc
  have lhs : Nat.choose n k * Nat.choose k j * c = n.factorial := by
    have hnjk : n - k = n - j - (k - j) := by omega
    calc Nat.choose n k * Nat.choose k j * c
        = Nat.choose n k * (Nat.choose k j * j.factorial * (k - j).factorial) *
          (n - k).factorial := by ring
      _ = Nat.choose n k * k.factorial * (n - k).factorial := by
          rw [Nat.choose_mul_factorial_mul_factorial hj]
      _ = n.factorial := Nat.choose_mul_factorial_mul_factorial hk
  have rhs : Nat.choose n j * Nat.choose (n - j) (k - j) * c = n.factorial := by
    have hnjk' : n - k = n - j - (k - j) := by omega
    calc Nat.choose n j * Nat.choose (n - j) (k - j) * c
        = Nat.choose n j * (Nat.choose (n - j) (k - j) * (k - j).factorial *
          (n - k).factorial) * j.factorial := by ring
      _ = Nat.choose n j * (Nat.choose (n - j) (k - j) * (k - j).factorial *
          (n - j - (k - j)).factorial) * j.factorial := by rw [hnjk']
      _ = Nat.choose n j * (n - j).factorial * j.factorial := by
          rw [Nat.choose_mul_factorial_mul_factorial hkj]
      _ = Nat.choose n j * j.factorial * (n - j).factorial := by ring
      _ = n.factorial := Nat.choose_mul_factorial_mul_factorial hj_n
  linarith

/-- The joint induced density is symmetric: p(F,F';H) = p(F',F;H).
    Uses `jointCount_comm` and multinomial symmetry. -/
theorem jointInducedDensity_comm (σ : FlagType) (F F' H : Flag σ) :
    jointInducedDensity σ F F' H = jointInducedDensity σ F' F H := by
  unfold jointInducedDensity
  rw [jointCount_comm]
  congr 1
  -- The multinomial denominators are symmetric
  set g := H.size - σ.size
  set f := F.size - σ.size
  set f' := F'.size - σ.size
  by_cases hab : f + f' ≤ g
  · exact choose_mul_choose_comm g f f' hab
  · -- If f + f' > g, both products are 0
    push_neg at hab
    have h1 : Nat.choose g f * Nat.choose (g - f) f' = 0 := by
      rw [Nat.mul_eq_zero]
      by_contra h; push_neg at h
      have := Nat.choose_ne_zero_iff.mp h.1
      have := Nat.choose_ne_zero_iff.mp h.2
      omega
    have h2 : Nat.choose g f' * Nat.choose (g - f') f = 0 := by
      rw [Nat.mul_eq_zero]
      by_contra h; push_neg at h
      have := Nat.choose_ne_zero_iff.mp h.1
      have := Nat.choose_ne_zero_iff.mp h.2
      omega
    have h1' : (Nat.choose g f : ℝ) * (Nat.choose (g - f) f' : ℝ) = 0 := by exact_mod_cast h1
    have h2' : (Nat.choose g f' : ℝ) * (Nat.choose (g - f') f : ℝ) = 0 := by exact_mod_cast h2
    linarith

/-- **Lemma 2.4 (Commutativity)**: F · F' = F' · F.
    Follows from p(F,F';H) = p(F',F;H) (the joint density is symmetric). -/
theorem product_comm (σ : FlagType) (F F' : Flag σ) :
    localFlagProduct σ F F' = localFlagProduct σ F' F := by
  unfold localFlagProduct
  rw [show F.size + F'.size = F'.size + F.size from Nat.add_comm _ _]
  dsimp only []
  split
  · congr 1
    · rw [mul_comm]
    · exact Finset.sum_congr rfl fun cls _ => by rw [jointInducedDensity_comm]
  · rfl

/-! ### Linearity of FlagAlg.mul

Helper lemmas showing `FlagAlg.mul` distributes over addition and scalar multiplication.
Used in the inductive proof of associativity (Lemma 2.4). -/

private theorem FlagAlg.mul_zero_left (σ : FlagType) (v : FlagAlg σ) :
    FlagAlg.mul (0 : FlagAlg σ) v = 0 :=
  Finsupp.sum_zero_index

private theorem FlagAlg.mul_zero_right (σ : FlagType) (v : FlagAlg σ) :
    FlagAlg.mul v (0 : FlagAlg σ) = 0 := by
  unfold FlagAlg.mul
  simp [Finsupp.sum_zero_index]

private theorem FlagAlg.add_mul (σ : FlagType) (v w u : FlagAlg σ) :
    (v + w).mul u = v.mul u + w.mul u :=
  Finsupp.sum_add_index'
    (fun a => by simp [zero_mul, zero_smul, Finsupp.sum])
    (fun a b₁ b₂ => by
      simp_rw [_root_.add_mul, _root_.add_smul]
      simp only [Finsupp.sum, Finset.sum_add_distrib])

private theorem FlagAlg.mul_add (σ : FlagType) (v w u : FlagAlg σ) :
    v.mul (w + u) = v.mul w + v.mul u := by
  unfold FlagAlg.mul
  conv_lhs =>
    arg 2; ext cls₁ c₁
    rw [Finsupp.sum_add_index'
      (fun a => by simp [mul_zero, zero_smul])
      (fun a b₁ b₂ => by rw [_root_.mul_add, _root_.add_smul])]
  simp only [Finsupp.sum, Finset.sum_add_distrib]

private theorem FlagAlg.smul_mul (σ : FlagType) (c : ℝ) (v w : FlagAlg σ) :
    (c • v).mul w = c • (v.mul w) := by
  unfold FlagAlg.mul
  rw [Finsupp.sum_smul_index
    (fun _ => by simp [zero_mul, zero_smul, Finsupp.sum])]
  simp only [Finsupp.sum, Finset.smul_sum, smul_smul]
  congr 1; ext cls; congr 1; ext cls'
  ring

private theorem FlagAlg.mul_smul (σ : FlagType) (c : ℝ) (v w : FlagAlg σ) :
    v.mul (c • w) = c • (v.mul w) := by
  unfold FlagAlg.mul
  conv_lhs =>
    arg 2; ext cls₁ c₁
    rw [Finsupp.sum_smul_index (fun _ => by simp [mul_zero, zero_smul])]
  simp only [Finsupp.sum, Finset.smul_sum, smul_smul]
  congr 1; ext cls; congr 1; ext cls'
  ring

/-! ### Basis associativity (Chain rule)

The key lemma: `(F₁ · F₂) · F₃ = F₁ · (F₂ · F₃)` for basis flags.
Follows from the chain rule for induced densities (Thesis Lemma 1.3):
  Σ_H p(F₁,F₂;H)·p(H,F₃;G) = p(F₁,F₂,F₃;G) = Σ_{H'} p(F₂,F₃;H')·p(F₁,H';G)
Both sides equal the triple joint density, making the product associative. -/

/-- Helper: `FlagAlg.mul` distributes a `Finset.sum` of `Finsupp.single`s over
    multiplication by `FlagAlg.single` on the right. -/
private theorem finset_sum_single_mul_right (σ : FlagType)
    (S : Finset (FlagClass σ)) (coeff : FlagClass σ → ℝ) (F : Flag σ) :
    FlagAlg.mul (S.sum (fun cls => Finsupp.single cls (coeff cls))) (FlagAlg.single σ F) =
    S.sum (fun cls => coeff cls • localFlagProduct σ cls.out F) := by
  induction S using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact FlagAlg.mul_zero_left σ _
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, FlagAlg.add_mul, ih, Finset.sum_insert ha]
    congr 1
    have hsingle : Finsupp.single a (coeff a) = coeff a • Finsupp.single a (1 : ℝ) := by
      rw [Finsupp.smul_single', mul_one]
    rw [hsingle, FlagAlg.smul_mul]
    have : Finsupp.single a (1 : ℝ) = FlagAlg.single σ a.out := by
      unfold FlagAlg.single FlagClass.mk; congr 1; exact (Quotient.out_eq a).symm
    rw [this, FlagAlg.mul_single]

/-- Helper: `FlagAlg.mul` distributes `FlagAlg.single` on the left over a
    `Finset.sum` of `Finsupp.single`s. -/
private theorem single_mul_finset_sum_single (σ : FlagType)
    (F : Flag σ) (S : Finset (FlagClass σ)) (coeff : FlagClass σ → ℝ) :
    FlagAlg.mul (FlagAlg.single σ F) (S.sum (fun cls => Finsupp.single cls (coeff cls))) =
    S.sum (fun cls => coeff cls • localFlagProduct σ F cls.out) := by
  induction S using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact FlagAlg.mul_zero_right σ _
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, FlagAlg.mul_add, ih, Finset.sum_insert ha]
    congr 1
    have hsingle : Finsupp.single a (coeff a) = coeff a • Finsupp.single a (1 : ℝ) := by
      rw [Finsupp.smul_single', mul_one]
    rw [hsingle, FlagAlg.mul_smul]
    have : Finsupp.single a (1 : ℝ) = FlagAlg.single σ a.out := by
      unfold FlagAlg.single FlagClass.mk; congr 1; exact (Quotient.out_eq a).symm
    rw [this, FlagAlg.mul_single]

/-- The triple joint induced density is invariant under cyclic permutation
    (F₁,F₂,F₃) → (F₂,F₃,F₁). Follows from `tripleJointCount_perm_231` and
    multinomial coefficient symmetry via two applications of `choose_mul_choose_comm`. -/
private theorem tripleJointInducedDensity_perm_231 (σ : FlagType) (F₁ F₂ F₃ G : Flag σ) :
    tripleJointInducedDensity σ F₁ F₂ F₃ G =
    tripleJointInducedDensity σ F₂ F₃ F₁ G := by
  unfold tripleJointInducedDensity
  rw [tripleJointCount_perm_231]
  congr 1
  -- Show the multinomial denominators are equal:
  -- C(g,f₁)·C(g-f₁,f₂)·C(g-f₁-f₂,f₃) = C(g,f₂)·C(g-f₂,f₃)·C(g-f₂-f₃,f₁)
  set g := G.size - σ.size
  set f₁ := F₁.size - σ.size
  set f₂ := F₂.size - σ.size
  set f₃ := F₃.size - σ.size
  by_cases h12 : f₁ + f₂ ≤ g
  · by_cases h123 : f₁ + f₂ + f₃ ≤ g
    · -- Main case: all sizes fit
      have h23 : f₂ + f₃ ≤ g := by omega
      have h1_le : f₁ ≤ g := by omega
      have h2_le : f₂ ≤ g := by omega
      have hf2_gf1 : f₂ ≤ g - f₁ := by omega
      have hf3_gf1f2 : f₃ ≤ g - f₁ - f₂ := by omega
      have hf3_gf2 : f₃ ≤ g - f₂ := by omega
      have hf1_gf2f3 : f₁ ≤ g - f₂ - f₃ := by omega
      -- Step 1: C(g,f₁)·C(g-f₁,f₂) = C(g,f₂)·C(g-f₂,f₁)
      have step1 := choose_mul_choose_comm g f₁ f₂ h12
      -- Step 2: C(g-f₂,f₁)·C((g-f₂)-f₁,f₃) = C(g-f₂,f₃)·C((g-f₂)-f₃,f₁)
      have h12' : f₁ + f₃ ≤ g - f₂ := by omega
      have step2 := choose_mul_choose_comm (g - f₂) f₁ f₃ h12'
      -- Note: g - f₁ - f₂ = (g - f₂) - f₁ and g - f₂ - f₃ = (g - f₂) - f₃
      have hsub1 : g - f₁ - f₂ = (g - f₂) - f₁ := by omega
      -- Combine: multiply step1 by C(g-f₁-f₂,f₃), use step2
      -- LHS product: C(g,f₁) * C(g-f₁,f₂) * C(g-f₁-f₂,f₃)
      -- = C(g,f₂) * C(g-f₂,f₁) * C(g-f₁-f₂,f₃)          [step1]
      -- = C(g,f₂) * C(g-f₂,f₁) * C((g-f₂)-f₁,f₃)         [hsub1]
      -- = C(g,f₂) * C(g-f₂,f₃) * C((g-f₂)-f₃,f₁)         [step2]
      -- = C(g,f₂) * C(g-f₂,f₃) * C(g-f₂-f₃,f₁)
      calc (Nat.choose g f₁ : ℝ) * (Nat.choose (g - f₁) f₂ : ℝ) *
              (Nat.choose (g - f₁ - f₂) f₃ : ℝ)
          = (Nat.choose g f₂ : ℝ) * (Nat.choose (g - f₂) f₁ : ℝ) *
              (Nat.choose (g - f₁ - f₂) f₃ : ℝ) := by rw [step1]
        _ = (Nat.choose g f₂ : ℝ) * ((Nat.choose (g - f₂) f₁ : ℝ) *
              (Nat.choose ((g - f₂) - f₁) f₃ : ℝ)) := by
            rw [show (g - f₁ - f₂) = (g - f₂) - f₁ from by omega]; ring
        _ = (Nat.choose g f₂ : ℝ) * ((Nat.choose (g - f₂) f₃ : ℝ) *
              (Nat.choose ((g - f₂) - f₃) f₁ : ℝ)) := by rw [step2]
        _ = (Nat.choose g f₂ : ℝ) * (Nat.choose (g - f₂) f₃ : ℝ) *
              (Nat.choose (g - f₂ - f₃) f₁ : ℝ) := by ring
    · -- f₁+f₂+f₃ > g: both products are 0
      -- A helper to show the RHS product vanishes
      have rhs_zero : (Nat.choose g f₂ : ℝ) * (Nat.choose (g - f₂) f₃ : ℝ) *
          (Nat.choose (g - f₂ - f₃) f₁ : ℝ) = 0 := by
        by_cases h23 : f₂ + f₃ ≤ g
        · have : Nat.choose (g - f₂ - f₃) f₁ = 0 := by
            rw [Nat.choose_eq_zero_iff]; omega
          simp [this]
        · push_neg at h23
          have : Nat.choose (g - f₂) f₃ = 0 := by
            rw [Nat.choose_eq_zero_iff]; omega
          simp [this]
      have lhs_zero : (Nat.choose g f₁ : ℝ) * (Nat.choose (g - f₁) f₂ : ℝ) *
          (Nat.choose (g - f₁ - f₂) f₃ : ℝ) = 0 := by
        have : Nat.choose (g - f₁ - f₂) f₃ = 0 := by
          rw [Nat.choose_eq_zero_iff]; omega
        simp [this]
      linarith
  · -- f₁+f₂ > g: both products are 0
    push_neg at h12
    have lhs_zero : (Nat.choose g f₁ : ℝ) * (Nat.choose (g - f₁) f₂ : ℝ) *
        (Nat.choose (g - f₁ - f₂) f₃ : ℝ) = 0 := by
      -- Either C(g,f₁)=0 (if f₁>g) or C(g-f₁,f₂)=0 (if f₁≤g)
      rcases le_or_gt f₁ g with hf1 | hf1
      · have : Nat.choose (g - f₁) f₂ = 0 := by
          rw [Nat.choose_eq_zero_iff]; omega
        simp [this]
      · have : Nat.choose g f₁ = 0 := by
          rw [Nat.choose_eq_zero_iff]; exact hf1
        simp [this]
    have rhs_zero : (Nat.choose g f₂ : ℝ) * (Nat.choose (g - f₂) f₃ : ℝ) *
        (Nat.choose (g - f₂ - f₃) f₁ : ℝ) = 0 := by
      by_cases h23 : f₂ + f₃ ≤ g
      · have : Nat.choose (g - f₂ - f₃) f₁ = 0 := by
          rw [Nat.choose_eq_zero_iff]; omega
        simp [this]
      · push_neg at h23
        rcases le_or_gt f₂ g with hf2 | hf2
        · have : Nat.choose (g - f₂) f₃ = 0 := by
            rw [Nat.choose_eq_zero_iff]; omega
          simp [this]
        · have : Nat.choose g f₂ = 0 := by
            rw [Nat.choose_eq_zero_iff]; exact hf2
          simp [this]
    linarith

/-- The multinomial M₁₂ · M_H₃ = M₁₂₃: factoring a trinomial through an intermediate
    size is the same as the direct trinomial. Uses `choose_mul_choose_trinomial`.
    M₁₂ = C(f₁+f₂, f₁) (after simplification), M_H₃ = C(g, f₁+f₂)·C(g-f₁-f₂, f₃),
    M₁₂₃ = C(g, f₁)·C(g-f₁, f₂)·C(g-f₁-f₂, f₃). -/
private theorem multinomial_factoring (g f₁ f₂ f₃ : ℕ)
    (hf₁₂ : f₁ + f₂ ≤ g) :
    (Nat.choose (f₁ + f₂) f₁ : ℝ) *
      ((Nat.choose g (f₁ + f₂) : ℝ) * (Nat.choose (g - (f₁ + f₂)) f₃ : ℝ)) =
    (Nat.choose g f₁ : ℝ) * (Nat.choose (g - f₁) f₂ : ℝ) *
      (Nat.choose (g - f₁ - f₂) f₃ : ℝ) := by
  have hf₁ : f₁ ≤ f₁ + f₂ := Nat.le_add_right _ _
  have := choose_mul_choose_trinomial g (f₁ + f₂) f₁ hf₁ hf₁₂
  -- trinomial: C(g, f₁+f₂) · C(f₁+f₂, f₁) = C(g, f₁) · C(g-f₁, f₂)
  have hsub : (f₁ + f₂) - f₁ = f₂ := Nat.add_sub_cancel_left _ _
  rw [hsub] at this
  -- Now: C(g, f₁+f₂) · C(f₁+f₂, f₁) = C(g, f₁) · C(g-f₁, f₂)
  -- and g - (f₁ + f₂) = g - f₁ - f₂
  have hsub2 : g - (f₁ + f₂) = g - f₁ - f₂ := by omega
  rw [hsub2]; nlinarith

/-! ### Orbit-counting infrastructure

Helper definitions and lemmas for the orbit-counting identity (Theorem 2.5). -/

/-- The intermediate finset for a pair of embeddings: the union of their ranges,
    as a `Finset (Fin G.size)`. -/
private noncomputable def intermediateFinset {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G) :
    Finset (Fin G.size) :=
  Finset.univ.filter (fun v => v ∈ Set.range e₁.toFun ∨ v ∈ Set.range e₂.toFun)

/-- The σ-image of G is contained in the intermediate finset (both embeddings
    are σ-compatible, so each maps the σ-image to `G.embedding`). -/
private theorem intermediateFinset_contains_sigma {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (i : Fin σ.size) :
    G.embedding i ∈ intermediateFinset e₁ e₂ := by
  simp only [intermediateFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  left; exact ⟨F₁.embedding i, e₁.compat i⟩

/-- The cardinality of the intermediate finset equals `F₁.size + F₂.size - σ.size`
    when the overlap condition holds (overlap ↔ σ-image) and the covering condition
    holds (union = all of G). -/
private theorem intermediateFinset_card {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (_hcovering : ∀ i : Fin G.size,
      i ∈ Set.range e₁.toFun ∨ i ∈ Set.range e₂.toFun) :
    (intermediateFinset e₁ e₂).card = F₁.size + F₂.size - σ.size := by
  -- The intermediate finset = range e₁ ∪ range e₂ (as finsets).
  -- Since covering holds, this is all of Fin G.size.
  -- We use inclusion-exclusion: |A ∪ B| = |A| + |B| - |A ∩ B|.
  -- |A| = F₁.size, |B| = F₂.size, |A ∩ B| = σ.size.
  let A := Finset.univ.filter (fun v => v ∈ Set.range e₁.toFun)
  let B := Finset.univ.filter (fun v => v ∈ Set.range e₂.toFun)
  have hAB : intermediateFinset e₁ e₂ = A ∪ B := by
    ext v; simp only [intermediateFinset, A, B, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_union]
  rw [hAB]
  have hA : A.card = F₁.size := by
    have : A = Finset.univ.image e₁.toFun := by
      ext v; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image]; rfl
    rw [this, Finset.card_image_of_injective _ e₁.injective, Finset.card_fin]
  have hB : B.card = F₂.size := by
    have : B = Finset.univ.image e₂.toFun := by
      ext v; simp only [B, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image]; rfl
    rw [this, Finset.card_image_of_injective _ e₂.injective, Finset.card_fin]
  have hAinterB : (A ∩ B).card = σ.size := by
    have hAB_eq : A ∩ B = Finset.univ.image G.embedding := by
      ext v; simp only [A, B, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_image]
      exact hoverlap v
    rw [hAB_eq, Finset.card_image_of_injective _ G.embedding.injective, Finset.card_fin]
  have h := Finset.card_union_add_card_inter A B
  omega

/-- Composition of embeddings produces a TJC triple: given `(a₁,a₂)` witnessing
    `JC(F₁,F₂;H)` and `(b,e₃)` witnessing `JC(H,F₃;G)`, the composed triple
    `(b∘a₁, b∘a₂, e₃)` satisfies the TJC conditions. -/
private theorem compose_produces_tjc {σ : FlagType} {F₁ F₂ F₃ H G : Flag σ}
    (a₁ : InducedEmbedding σ F₁ H) (a₂ : InducedEmbedding σ F₂ H)
    (b : InducedEmbedding σ H G) (e₃ : InducedEmbedding σ F₃ G)
    (hjc12_overlap : ∀ i : Fin H.size,
      (i ∈ Set.range a₁.toFun ∧ i ∈ Set.range a₂.toFun) ↔
        i ∈ Set.range H.embedding)
    (hjc12_cover : ∀ i : Fin H.size,
      i ∈ Set.range a₁.toFun ∨ i ∈ Set.range a₂.toFun)
    (hjcH3_overlap : ∀ i : Fin G.size,
      (i ∈ Set.range b.toFun ∧ i ∈ Set.range e₃.toFun) ↔
        i ∈ Set.range G.embedding)
    (hjcH3_cover : ∀ i : Fin G.size,
      i ∈ Set.range b.toFun ∨ i ∈ Set.range e₃.toFun) :
    -- Overlap (b∘a₁, b∘a₂) ↔ σ-image
    (∀ i : Fin G.size,
      (i ∈ Set.range (b.comp a₁).toFun ∧ i ∈ Set.range (b.comp a₂).toFun) ↔
        i ∈ Set.range G.embedding) ∧
    -- Overlap (b∘a₁, e₃) ↔ σ-image
    (∀ i : Fin G.size,
      (i ∈ Set.range (b.comp a₁).toFun ∧ i ∈ Set.range e₃.toFun) ↔
        i ∈ Set.range G.embedding) ∧
    -- Overlap (b∘a₂, e₃) ↔ σ-image
    (∀ i : Fin G.size,
      (i ∈ Set.range (b.comp a₂).toFun ∧ i ∈ Set.range e₃.toFun) ↔
        i ∈ Set.range G.embedding) ∧
    -- Triple coverage
    (∀ i : Fin G.size,
      i ∈ Set.range (b.comp a₁).toFun ∨ i ∈ Set.range (b.comp a₂).toFun ∨
        i ∈ Set.range e₃.toFun) := by
  have hr1 := InducedEmbedding.range_comp b a₁
  have hr2 := InducedEmbedding.range_comp b a₂
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [hr1, hr2]; constructor
    · rintro ⟨⟨x₁, hx₁, hx₁_eq⟩, x₂, hx₂, hx₂_eq⟩
      obtain rfl : x₁ = x₂ := b.injective (hx₁_eq.trans hx₂_eq.symm)
      obtain ⟨j, rfl⟩ := (hjc12_overlap x₁).mp ⟨hx₁, hx₂⟩
      exact ⟨j, (b.compat j).symm.trans hx₁_eq⟩
    · rintro ⟨j, hj⟩
      exact ⟨⟨H.embedding j, ((hjc12_overlap _).mpr ⟨j, rfl⟩).1, (b.compat j).trans hj⟩,
             H.embedding j, ((hjc12_overlap _).mpr ⟨j, rfl⟩).2, (b.compat j).trans hj⟩
  · rw [hr1]; constructor
    · rintro ⟨⟨x₁, _, rfl⟩, h₃⟩; exact (hjcH3_overlap _).mp ⟨⟨x₁, rfl⟩, h₃⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨H.embedding j, ((hjc12_overlap _).mpr ⟨j, rfl⟩).1, b.compat j⟩,
             ((hjcH3_overlap _).mpr ⟨j, rfl⟩).2⟩
  · rw [hr2]; constructor
    · rintro ⟨⟨x₂, _, rfl⟩, h₃⟩; exact (hjcH3_overlap _).mp ⟨⟨x₂, rfl⟩, h₃⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨H.embedding j, ((hjc12_overlap _).mpr ⟨j, rfl⟩).2, b.compat j⟩,
             ((hjcH3_overlap _).mpr ⟨j, rfl⟩).2⟩
  · rw [hr1, hr2]
    rcases hjcH3_cover i with ⟨x, rfl⟩ | he₃
    · rcases hjc12_cover x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · left; exact Set.mem_image_of_mem b.toFun (Set.mem_range_self y)
      · right; left; exact Set.mem_image_of_mem b.toFun (Set.mem_range_self y)
    · right; right; exact he₃

/-- Given an injective induced embedding b : H ↪ G, the preimage map restricted to range b
    gives a left inverse. -/
private noncomputable def InducedEmbedding.invOnRange {σ : FlagType} {H G : Flag σ}
    (b : InducedEmbedding σ H G) :
    { v : Fin G.size // v ∈ Set.range b.toFun } → Fin H.size :=
  fun ⟨_v, hv⟩ => hv.choose

private theorem InducedEmbedding.invOnRange_spec {σ : FlagType} {H G : Flag σ}
    (b : InducedEmbedding σ H G)
    (v : Fin G.size) (hv : v ∈ Set.range b.toFun) :
    b.toFun (b.invOnRange ⟨v, hv⟩) = v :=
  hv.choose_spec

private theorem InducedEmbedding.invOnRange_left_inv {σ : FlagType} {H G : Flag σ}
    (b : InducedEmbedding σ H G) (x : Fin H.size) :
    b.invOnRange ⟨b.toFun x, Set.mem_range_self x⟩ = x :=
  b.injective (b.invOnRange_spec (b.toFun x) (Set.mem_range_self x))

/-- Construct the automorphism α = b⁻¹ ∘ b' when range(b) = range(b'). -/
private noncomputable def sameRangeAut {σ : FlagType} {H G : Flag σ}
    (b b' : InducedEmbedding σ H G)
    (hrange : Set.range b.toFun = Set.range b'.toFun) :
    InducedEmbedding σ H H where
  toFun v := b.invOnRange ⟨b'.toFun v, hrange ▸ Set.mem_range_self v⟩
  injective x y h := by
    have := congr_arg b.toFun h
    rw [b.invOnRange_spec, b.invOnRange_spec] at this
    exact b'.injective this
  map_adj u v hadj := by
    have hu : b'.toFun u ∈ Set.range b.toFun :=
      hrange.symm ▸ Set.mem_range_self u
    have hv : b'.toFun v ∈ Set.range b.toFun :=
      hrange.symm ▸ Set.mem_range_self v
    have hne : b.invOnRange ⟨b'.toFun u, hu⟩ ≠ b.invOnRange ⟨b'.toFun v, hv⟩ := by
      intro h
      have := congr_arg b.toFun h
      rw [b.invOnRange_spec, b.invOnRange_spec] at this
      exact (SimpleGraph.Adj.ne hadj) (b'.injective this)
    have hG : G.graph.Adj (b.toFun (b.invOnRange ⟨b'.toFun u, hu⟩))
                          (b.toFun (b.invOnRange ⟨b'.toFun v, hv⟩)) := by
      rw [b.invOnRange_spec, b.invOnRange_spec]; exact b'.map_adj _ _ hadj
    by_contra hnadj
    exact absurd hG (b.map_non_adj _ _ hne hnadj)
  map_non_adj u v hne hnadj := by
    have hu : b'.toFun u ∈ Set.range b.toFun :=
      hrange.symm ▸ Set.mem_range_self u
    have hv : b'.toFun v ∈ Set.range b.toFun :=
      hrange.symm ▸ Set.mem_range_self v
    have hne' : b.invOnRange ⟨b'.toFun u, hu⟩ ≠ b.invOnRange ⟨b'.toFun v, hv⟩ := by
      intro h; exact hne (b'.injective (by rw [← b.invOnRange_spec (b'.toFun u) hu,
        ← b.invOnRange_spec (b'.toFun v) hv]; congr 1))
    have hG : ¬G.graph.Adj (b.toFun (b.invOnRange ⟨b'.toFun u, hu⟩))
                           (b.toFun (b.invOnRange ⟨b'.toFun v, hv⟩)) := by
      rw [b.invOnRange_spec, b.invOnRange_spec]; exact b'.map_non_adj _ _ hne hnadj
    intro hadj; exact hG (b.map_adj _ _ hadj)
  compat i := by
    have hmem : b'.toFun (H.embedding i) ∈ Set.range b.toFun :=
      hrange.symm ▸ Set.mem_range_self (H.embedding i)
    change b.invOnRange ⟨b'.toFun (H.embedding i), hmem⟩ = H.embedding i
    apply b.injective
    rw [b.invOnRange_spec, b'.compat, ← b.compat]

/-- The automorphism α = b⁻¹ ∘ b' satisfies b ∘ α = b' (pointwise). -/
private theorem sameRangeAut_spec {σ : FlagType} {H G : Flag σ}
    (b b' : InducedEmbedding σ H G)
    (hrange : Set.range b.toFun = Set.range b'.toFun)
    (v : Fin H.size) :
    b.toFun ((sameRangeAut b b' hrange).toFun v) = b'.toFun v :=
  b.invOnRange_spec _ _

/-- Two JC-pair embeddings b, b' : H ↪ G from a joint count pair with the same e₃
    must have the same range (since range = complement of range(e₃) ∪ σ-image). -/
private theorem jc_pair_same_e3_same_range {σ : FlagType} {H F₃ G : Flag σ}
    (b b' : InducedEmbedding σ H G) (e₃ : InducedEmbedding σ F₃ G)
    (hjc : (∀ i, (i ∈ Set.range b.toFun ∧ i ∈ Set.range e₃.toFun) ↔
      i ∈ Set.range G.embedding) ∧
      (∀ i, i ∈ Set.range b.toFun ∨ i ∈ Set.range e₃.toFun))
    (hjc' : (∀ i, (i ∈ Set.range b'.toFun ∧ i ∈ Set.range e₃.toFun) ↔
      i ∈ Set.range G.embedding) ∧
      (∀ i, i ∈ Set.range b'.toFun ∨ i ∈ Set.range e₃.toFun)) :
    Set.range b.toFun = Set.range b'.toFun := by
  ext v; constructor
  · rintro ⟨x, rfl⟩
    rcases hjc'.2 (b.toFun x) with h | h
    · exact h
    · exact ((hjc'.1 _).mpr ((hjc.1 _).mp ⟨Set.mem_range_self x, h⟩)).1
  · rintro ⟨x, rfl⟩
    rcases hjc.2 (b'.toFun x) with h | h
    · exact h
    · exact ((hjc.1 _).mpr ((hjc'.1 _).mp ⟨Set.mem_range_self x, h⟩)).1

/-- The intermediate subflag for a JC₁₂ pair (e₁,e₂). Returns the induced subflag on
    the union of ranges, together with proofs of the relevant properties. -/
private noncomputable def jcIntermediateSubflag {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hcov : ∀ i : Fin G.size,
      i ∈ Set.range e₁.toFun ∨ i ∈ Set.range e₂.toFun)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    Flag σ :=
  G.inducedSubflag (intermediateFinset e₁ e₂) (intermediateFinset_contains_sigma e₁ e₂)
    ((intermediateFinset_card e₁ e₂ hoverlap hcov).symm ▸ hn)

/-- The intermediate subflag has size n = F₁.size + F₂.size - σ.size. -/
private theorem jcIntermediateSubflag_size {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hcov : ∀ i : Fin G.size,
      i ∈ Set.range e₁.toFun ∨ i ∈ Set.range e₂.toFun)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    (jcIntermediateSubflag e₁ e₂ hoverlap hcov hn).size = F₁.size + F₂.size - σ.size :=
  intermediateFinset_card e₁ e₂ hoverlap hcov

/-- FlagClass.mk of the intermediate subflag is in classesOfSize. -/
private theorem jcIntermediateSubflag_mem_classesOfSize {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hcov : ∀ i : Fin G.size,
      i ∈ Set.range e₁.toFun ∨ i ∈ Set.range e₂.toFun)
    {n : ℕ} (hn : σ.size ≤ n) (hn_eq : n = F₁.size + F₂.size - σ.size) :
    FlagClass.mk (jcIntermediateSubflag e₁ e₂ hoverlap hcov (hn_eq ▸ hn)) ∈
      classesOfSize σ n hn := by
  set H := jcIntermediateSubflag e₁ e₂ hoverlap hcov (hn_eq ▸ hn)
  have hsize : H.size = n := by
    rw [hn_eq]; exact jcIntermediateSubflag_size e₁ e₂ hoverlap hcov _
  have hmem : FlagClass.mk H ∈ classesOfSize σ H.size H.hsize := by
    rw [classesOfSize, Finset.mem_image]
    exact ⟨⟨H.graph, H.embedding⟩, Finset.mem_univ _, rfl⟩
  convert hmem using 2; exact hsize.symm




/-- **Per-class orbit-counting**: for a fixed flag H, the composition map
    `JC₁₂(H) × JC_H₃(H,G) → TJC` has each fiber of size `Aut(H)`.
    Equivalently: `JC₁₂(H) * JC_H₃(H,G) = Aut(H) * |{TJC triples factoring through H}|`.

    This is expressed as a real-valued identity: the sum over ALL classes [H'] in
    classesOfSize of `(JC₁₂(H') * JC_H₃(H',G)) / Aut(H')` equals TJC.

    The proof constructs, for each TJC triple (e₁,e₂,e₃):
    1. The intermediate subflag H_mid = G|_{range(e₁) ∪ range(e₂)}
    2. The canonical inclusion b₀ : H_mid ↪ G
    3. For any b : H ↪ G with range = range(b₀), define α = b₀⁻¹ ∘ b via `sameRangeAut`
    4. Show b determines (a₁,a₂) uniquely: a₁ = b⁻¹ ∘ e₁, a₂ = b⁻¹ ∘ e₂
    5. The number of valid b equals |IE(H, H_mid)| = Aut(H) (when H ≅ H_mid)

    The fiber-counting gives JC₁₂ * JC_H₃ / Aut = |{triples with intermediate class [H]}|.
    Summing over classes and using Finset.card_eq_sum_card_fiberwise gives TJC. -/
-- Inclusion-exclusion for intermediate finset card: only needs overlap, not covering.
private theorem intermediateFinset_card' {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding) :
    (intermediateFinset e₁ e₂).card = F₁.size + F₂.size - σ.size := by
  let A := Finset.univ.filter (fun v => v ∈ Set.range e₁.toFun)
  let B := Finset.univ.filter (fun v => v ∈ Set.range e₂.toFun)
  have hAB : intermediateFinset e₁ e₂ = A ∪ B := by
    ext v; simp only [intermediateFinset, A, B, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_union]
  rw [hAB]
  have hA : A.card = F₁.size := by
    have : A = Finset.univ.image e₁.toFun := by
      ext v; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image]; rfl
    rw [this, Finset.card_image_of_injective _ e₁.injective, Finset.card_fin]
  have hB : B.card = F₂.size := by
    have : B = Finset.univ.image e₂.toFun := by
      ext v; simp only [B, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image]; rfl
    rw [this, Finset.card_image_of_injective _ e₂.injective, Finset.card_fin]
  have hAinterB : (A ∩ B).card = σ.size := by
    have : A ∩ B = Finset.univ.image G.embedding := by
      ext v; simp only [A, B, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_image]; exact hoverlap v
    rw [this, Finset.card_image_of_injective _ G.embedding.injective, Finset.card_fin]
  have := Finset.card_union_add_card_inter A B; omega

-- The intermediate subflag for a pair (e₁,e₂) where only the overlap condition holds
-- (no full coverage needed).
private noncomputable def intermediateSubflag' {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    Flag σ :=
  G.inducedSubflag (intermediateFinset e₁ e₂) (intermediateFinset_contains_sigma e₁ e₂)
    ((intermediateFinset_card' e₁ e₂ hoverlap).symm ▸ hn)

private theorem intermediateSubflag'_size {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    (intermediateSubflag' e₁ e₂ hoverlap hn).size = F₁.size + F₂.size - σ.size :=
  intermediateFinset_card' e₁ e₂ hoverlap

-- The canonical inclusion of the intermediate subflag into G.
private noncomputable def intermediateSubflag'_incl {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    InducedEmbedding σ (intermediateSubflag' e₁ e₂ hoverlap hn) G :=
  G.inducedSubflag_incl _ _ _

-- Range of the inclusion = the intermediate finset (as a set).
private theorem intermediateSubflag'_incl_range {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    Set.range (intermediateSubflag'_incl e₁ e₂ hoverlap hn).toFun =
      ↑(intermediateFinset e₁ e₂) :=
  Flag.inducedSubflag_incl_range G _ _ _

-- e₁ restricts to the intermediate subflag.
private noncomputable def restrict_e₁_to_intermediate {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    InducedEmbedding σ F₁ (intermediateSubflag' e₁ e₂ hoverlap hn) :=
  e₁.restrictToSubflag _ _ _ (fun x => by
    simp only [intermediateFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    left; exact Set.mem_range_self x)

-- e₂ restricts to the intermediate subflag.
private noncomputable def restrict_e₂_to_intermediate {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    InducedEmbedding σ F₂ (intermediateSubflag' e₁ e₂ hoverlap hn) :=
  e₂.restrictToSubflag _ _ _ (fun x => by
    simp only [intermediateFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    right; exact Set.mem_range_self x)

-- The restricted embeddings compose with inclusion to give the originals.
private theorem restrict_comp_incl_e₁ {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    ∀ x, (intermediateSubflag'_incl e₁ e₂ hoverlap hn).toFun
      ((restrict_e₁_to_intermediate e₁ e₂ hoverlap hn).toFun x) = e₁.toFun x :=
  InducedEmbedding.restrictToSubflag_comp_incl e₁ _ _ _ _

private theorem restrict_comp_incl_e₂ {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    ∀ x, (intermediateSubflag'_incl e₁ e₂ hoverlap hn).toFun
      ((restrict_e₂_to_intermediate e₁ e₂ hoverlap hn).toFun x) = e₂.toFun x :=
  InducedEmbedding.restrictToSubflag_comp_incl e₂ _ _ _ _

-- The restricted embeddings form a JC pair in the intermediate subflag:
-- overlap ↔ σ-image and covering holds.
private theorem restrict_jc_overlap {σ : FlagType} {F₁ F₂ G : Flag σ}
    (e₁ : InducedEmbedding σ F₁ G) (e₂ : InducedEmbedding σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    let H := intermediateSubflag' e₁ e₂ hoverlap hn
    let a₁ := restrict_e₁_to_intermediate e₁ e₂ hoverlap hn
    let a₂ := restrict_e₂_to_intermediate e₁ e₂ hoverlap hn
    (∀ i : Fin H.size,
      (i ∈ Set.range a₁.toFun ∧ i ∈ Set.range a₂.toFun) ↔
        i ∈ Set.range H.embedding) ∧
    (∀ i : Fin H.size,
      i ∈ Set.range a₁.toFun ∨ i ∈ Set.range a₂.toFun) := by
  intro H a₁ a₂
  set incl := intermediateSubflag'_incl e₁ e₂ hoverlap hn
  have hcomp₁ := restrict_comp_incl_e₁ e₁ e₂ hoverlap hn
  have hcomp₂ := restrict_comp_incl_e₂ e₁ e₂ hoverlap hn
  have hrange := intermediateSubflag'_incl_range e₁ e₂ hoverlap hn
  constructor
  · intro i; constructor
    · intro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
      -- hx₁ : a₁.toFun x₁ = i, so incl i = incl (a₁ x₁) = e₁ x₁
      have h1 : incl.toFun i ∈ Set.range e₁.toFun := by
        have : incl.toFun i = incl.toFun (a₁.toFun x₁) := by congr 1; exact hx₁.symm
        rw [this, hcomp₁ x₁]; exact Set.mem_range_self x₁
      have h2 : incl.toFun i ∈ Set.range e₂.toFun := by
        have : incl.toFun i = incl.toFun (a₂.toFun x₂) := by congr 1; exact hx₂.symm
        rw [this, hcomp₂ x₂]; exact Set.mem_range_self x₂
      obtain ⟨j, hj⟩ := (hoverlap _).mp ⟨h1, h2⟩
      exact ⟨j, incl.injective ((incl.compat j).trans hj)⟩
    · intro ⟨j, hj⟩
      -- H.embedding j = i, so incl i = incl (H.embedding j) = G.embedding j
      have hincl_i : incl.toFun i = G.embedding j := by
        rw [show i = H.embedding j from hj.symm]; exact incl.compat j
      constructor
      · -- Need: i ∈ range(a₁). We know G.embedding j ∈ range(e₁), and e₁ maps into H.
        -- e₁ (F₁.embedding j) = G.embedding j; F₁.embedding j maps via a₁ into H.
        -- a₁ (F₁.embedding j) : its image under incl = e₁ (F₁.embedding j) = G.embedding j = incl i
        -- So a₁ (F₁.embedding j) = i by injectivity.
        refine ⟨F₁.embedding j, incl.injective ?_⟩
        rw [hcomp₁, e₁.compat, hincl_i]
      · refine ⟨F₂.embedding j, incl.injective ?_⟩
        rw [hcomp₂, e₂.compat, hincl_i]
  · intro i
    -- incl i ∈ intermediateFinset = {v | v ∈ range(e₁) ∨ v ∈ range(e₂)}
    have hi : incl.toFun i ∈ (intermediateFinset e₁ e₂ : Set (Fin G.size)) := by
      rw [← hrange]; exact Set.mem_range_self i
    simp only [intermediateFinset, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
      true_and] at hi
    rcases hi with ⟨x₁, hx₁⟩ | ⟨x₂, hx₂⟩
    · -- hx₁ : e₁.toFun x₁ = incl.toFun i, so incl (a₁ x₁) = e₁ x₁ = incl i
      left; exact ⟨x₁, incl.injective ((hcomp₁ x₁).trans hx₁)⟩
    · right; exact ⟨x₂, incl.injective ((hcomp₂ x₂).trans hx₂)⟩

-- Abbreviation for the TJC subtype.
private abbrev TJCSub (σ : FlagType) (F₁ F₂ F₃ G : Flag σ) :=
  { t : InducedEmbedding σ F₁ G × InducedEmbedding σ F₂ G ×
        InducedEmbedding σ F₃ G //
    (∀ i, (i ∈ Set.range t.1.toFun ∧ i ∈ Set.range t.2.1.toFun) ↔
      i ∈ Set.range G.embedding) ∧
    (∀ i, (i ∈ Set.range t.1.toFun ∧ i ∈ Set.range t.2.2.toFun) ↔
      i ∈ Set.range G.embedding) ∧
    (∀ i, (i ∈ Set.range t.2.1.toFun ∧ i ∈ Set.range t.2.2.toFun) ↔
      i ∈ Set.range G.embedding) ∧
    (∀ i, i ∈ Set.range t.1.toFun ∨ i ∈ Set.range t.2.1.toFun ∨
      i ∈ Set.range t.2.2.toFun) }

-- Abbreviation for JC subtype (joint count pairs).
private abbrev JCSub (σ : FlagType) (F₁ F₂ G : Flag σ) :=
  { p : InducedEmbedding σ F₁ G × InducedEmbedding σ F₂ G //
    (∀ i : Fin G.size,
      (i ∈ Set.range p.1.toFun ∧ i ∈ Set.range p.2.toFun) ↔
        i ∈ Set.range G.embedding) ∧
    (∀ i : Fin G.size,
      i ∈ Set.range p.1.toFun ∨ i ∈ Set.range p.2.toFun) }

-- The intermediate class of a TJC triple: FlagClass.mk of the intermediate subflag.
-- The intermediate subflag is G restricted to range(e₁) ∪ range(e₂).
private noncomputable def tjcIntermediateClass {σ : FlagType} {F₁ F₂ F₃ G : Flag σ}
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size)
    (t : TJCSub σ F₁ F₂ F₃ G) :
    FlagClass σ :=
  FlagClass.mk (intermediateSubflag' t.val.1 t.val.2.1 t.property.1 hn)

-- The intermediate class is in classesOfSize.
private theorem tjcIntermediateClass_mem {σ : FlagType} {F₁ F₂ F₃ G : Flag σ}
    {n : ℕ} (hn : σ.size ≤ n) (hn_eq : n = F₁.size + F₂.size - σ.size)
    (t : TJCSub σ F₁ F₂ F₃ G) :
    tjcIntermediateClass (hn_eq ▸ hn) t ∈ classesOfSize σ n hn := by
  unfold tjcIntermediateClass
  set H := intermediateSubflag' t.val.1 t.val.2.1 t.property.1 (hn_eq ▸ hn)
  have hsize : H.size = n := by
    rw [hn_eq]; exact intermediateSubflag'_size t.val.1 t.val.2.1 t.property.1 _
  have hmem : FlagClass.mk H ∈ classesOfSize σ H.size H.hsize := by
    rw [classesOfSize, Finset.mem_image]
    exact ⟨⟨H.graph, H.embedding⟩, Finset.mem_univ _, rfl⟩
  convert hmem using 2; exact hsize.symm

-- The composition map: JC12(H) × JCH3(H,G) → TJC.
private noncomputable def composeMap_val {σ : FlagType} {F₁ F₂ F₃ H G : Flag σ}
    (pair : JCSub σ F₁ F₂ H × JCSub σ H F₃ G) :
    InducedEmbedding σ F₁ G × InducedEmbedding σ F₂ G × InducedEmbedding σ F₃ G :=
  (pair.2.val.1.comp pair.1.val.1, pair.2.val.1.comp pair.1.val.2, pair.2.val.2)

private noncomputable def composeMap {σ : FlagType} {F₁ F₂ F₃ H G : Flag σ}
    (pair : JCSub σ F₁ F₂ H × JCSub σ H F₃ G) :
    TJCSub σ F₁ F₂ F₃ G :=
  let pf := compose_produces_tjc pair.1.val.1 pair.1.val.2 pair.2.val.1 pair.2.val.2
    pair.1.property.1 pair.1.property.2 pair.2.property.1 pair.2.property.2
  ⟨composeMap_val pair, pf.1, pf.2.1, pf.2.2.1, pf.2.2.2⟩

@[simp] private theorem composeMap_val_eq {σ : FlagType} {F₁ F₂ F₃ H G : Flag σ}
    (pair : JCSub σ F₁ F₂ H × JCSub σ H F₃ G) :
    (composeMap pair).val = composeMap_val pair := rfl

set_option maxHeartbeats 800000 in
private theorem composeMap_class {σ : FlagType} {F₁ F₂ F₃ H G : Flag σ}
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size)
    (pair : JCSub σ F₁ F₂ H × JCSub σ H F₃ G) :
    tjcIntermediateClass hn (composeMap pair) = FlagClass.mk H := by
  set a₁ := pair.1.val.1 with ha₁
  set a₂ := pair.1.val.2 with ha₂
  set b := pair.2.val.1 with hb
  set e₃ := pair.2.val.2 with he₃
  have hcov₁₂ := pair.1.property.2
  unfold tjcIntermediateClass; rw [FlagClass.mk_eq]
  set S := intermediateFinset (composeMap pair).val.1 (composeMap pair).val.2.1
  have hS_eq : S = Finset.univ.image b.toFun := by
    change intermediateFinset (b.comp a₁) (b.comp a₂) = _
    ext v; simp only [intermediateFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, InducedEmbedding.comp]
    constructor
    · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> simp only [Function.comp_apply] <;> exact ⟨_, rfl⟩
    · rintro ⟨y, -, rfl⟩
      rcases hcov₁₂ y with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · left; exact ⟨z, rfl⟩
      · right; exact ⟨z, rfl⟩
  set ι := S.orderEmbOfFin rfl
  have hι_mem : ∀ v : Fin S.card, (ι v : Fin G.size) ∈ Set.range b.toFun := by
    intro v
    have : (ι v : Fin G.size) ∈ (Finset.univ.image b.toFun : Finset _) :=
      hS_eq ▸ Finset.orderEmbOfFin_mem S rfl v
    exact (Finset.mem_image.mp this).elim fun w hw => ⟨w, hw.2⟩
  let φfun : Fin S.card → Fin H.size := fun v => b.invOnRange ⟨ι v, hι_mem v⟩
  let ψfun : Fin H.size → Fin S.card := fun w =>
    (S.orderIsoOfFin rfl).symm ⟨b.toFun w, by
      rw [hS_eq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ w)⟩
  have hφψ : ∀ w, φfun (ψfun w) = w := by
    intro w; simp only [φfun, ψfun]
    apply b.injective; rw [b.invOnRange_spec]
    change ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨b.toFun w, _⟩)) = b.toFun w
    simp [OrderIso.apply_symm_apply]
  have hψφ : ∀ v, ψfun (φfun v) = v := by
    intro v; simp only [φfun, ψfun, b.invOnRange_spec (ι v) (hι_mem v)]
    exact (S.orderIsoOfFin rfl).symm_apply_apply v
  have hadj_iff : ∀ {u v : Fin S.card},
      G.graph.Adj (ι u) (ι v) ↔ H.graph.Adj (φfun u) (φfun v) := by
    intro u v; constructor
    · intro hadj
      have hne : φfun u ≠ φfun v := fun h => (SimpleGraph.Adj.ne hadj) (by
        rw [← b.invOnRange_spec (ι u) (hι_mem u),
            ← b.invOnRange_spec (ι v) (hι_mem v)]; congr 1)
      by_contra hnadj
      exact absurd (by rwa [← b.invOnRange_spec (ι u) (hι_mem u),
        ← b.invOnRange_spec (ι v) (hι_mem v)] at hadj) (b.map_non_adj _ _ hne hnadj)
    · intro hadj; have := b.map_adj _ _ hadj
      rwa [b.invOnRange_spec, b.invOnRange_spec] at this
  refine ⟨⟨⟨φfun, ψfun, hψφ, hφψ⟩, fun {u v} => hadj_iff.symm⟩, ?_⟩
  intro i; change φfun _ = H.embedding i
  change b.invOnRange ⟨ι _, hι_mem _⟩ = H.embedding i
  apply b.injective; rw [b.invOnRange_spec, b.compat i]
  exact (G.inducedSubflag_incl S _ _).compat i

-- Two InducedEmbeddings with the same toFun are equal (proof irrelevance).
private theorem InducedEmbedding.ext' {σ : FlagType} {F G : Flag σ}
    {e₁ e₂ : InducedEmbedding σ F G} (h : e₁.toFun = e₂.toFun) : e₁ = e₂ := by
  cases e₁; cases e₂; simp only [InducedEmbedding.mk.injEq]; exact h

private noncomputable def pullbackEmbedding {σ : FlagType} {F H G : Flag σ}
    (b : InducedEmbedding σ H G) (e : InducedEmbedding σ F G)
    (hrange : ∀ x, e.toFun x ∈ Set.range b.toFun) :
    InducedEmbedding σ F H where
  toFun x := b.invOnRange ⟨e.toFun x, hrange x⟩
  injective x y h := e.injective (by
    have := congr_arg b.toFun h; rwa [b.invOnRange_spec, b.invOnRange_spec] at this)
  map_adj u v hadj := by
    have hne : b.invOnRange ⟨e.toFun u, hrange u⟩ ≠ b.invOnRange ⟨e.toFun v, hrange v⟩ := fun h =>
      hadj.ne (e.injective (by
        have := congr_arg b.toFun h; rwa [b.invOnRange_spec, b.invOnRange_spec] at this))
    by_contra hnadj
    exact absurd (by rw [b.invOnRange_spec, b.invOnRange_spec]; exact e.map_adj _ _ hadj :
        G.graph.Adj _ _) (b.map_non_adj _ _ hne hnadj)
  map_non_adj u v hne hnadj := by
    have hne' : b.invOnRange ⟨e.toFun u, hrange u⟩ ≠ b.invOnRange ⟨e.toFun v, hrange v⟩ := fun h =>
      hne (e.injective (by
        have := congr_arg b.toFun h; rwa [b.invOnRange_spec, b.invOnRange_spec] at this))
    intro hadj
    exact (by rw [b.invOnRange_spec, b.invOnRange_spec]; exact e.map_non_adj _ _ hne hnadj :
        ¬G.graph.Adj _ _) (b.map_adj _ _ hadj)
  compat i := b.injective (by rw [b.invOnRange_spec, e.compat, ← b.compat])

private theorem pullbackEmbedding_spec {σ : FlagType} {F H G : Flag σ}
    (b : InducedEmbedding σ H G) (e : InducedEmbedding σ F G)
    (hrange : ∀ x, e.toFun x ∈ Set.range b.toFun) (x) :
    b.toFun ((pullbackEmbedding b e hrange).toFun x) = e.toFun x :=
  b.invOnRange_spec (e.toFun x) (hrange x)

private theorem comp_pullback_eq {σ : FlagType} {F H G : Flag σ}
    (b : InducedEmbedding σ H G) (e : InducedEmbedding σ F G)
    (hrange : ∀ x, e.toFun x ∈ Set.range b.toFun) :
    b.comp (pullbackEmbedding b e hrange) = e := by
  apply InducedEmbedding.ext'; ext x
  simp only [InducedEmbedding.comp, Function.comp_apply]
  exact congr_arg Fin.val (pullbackEmbedding_spec b e hrange x)

private noncomputable def sameRangeEquiv {σ : FlagType} {H G : Flag σ}
    (b₀ : InducedEmbedding σ H G) :
    InducedEmbedding σ H H ≃
      { b : InducedEmbedding σ H G // Set.range b.toFun = Set.range b₀.toFun } where
  toFun α := ⟨b₀.comp α, by
    ext x; simp only [InducedEmbedding.comp, Set.mem_range, Function.comp_apply]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨α.toFun y, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨z, rfl⟩ := Finite.injective_iff_surjective.mp α.injective y
      exact ⟨z, hy⟩⟩
  invFun bpair := sameRangeAut b₀ bpair.val bpair.property.symm
  left_inv α := by
    have hrange : Set.range b₀.toFun = Set.range (b₀.comp α).toFun := by
      ext x; simp only [InducedEmbedding.comp, Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨y, rfl⟩
        obtain ⟨z, rfl⟩ := Finite.injective_iff_surjective.mp α.injective y; exact ⟨z, rfl⟩
      · rintro ⟨y, rfl⟩; exact ⟨α.toFun y, rfl⟩
    exact InducedEmbedding.ext' (funext fun x => b₀.injective
      (sameRangeAut_spec b₀ (b₀.comp α) hrange x))
  right_inv bpair := by
    apply Subtype.ext; apply InducedEmbedding.ext'; funext x
    exact sameRangeAut_spec b₀ bpair.val bpair.property.symm x

-- Per-class orbit-counting (ℕ level): for a fixed flag H,
-- JC(F₁,F₂;H) * JC(H,F₃;G) = Aut(H) * |{TJC triples with intermediate class [H]}|.
private noncomputable def decomposeTriple {σ : FlagType} {F₁ F₂ F₃ H G : Flag σ}
    (t : TJCSub σ F₁ F₂ F₃ G) (b : InducedEmbedding σ H G)
    (hrange : Set.range b.toFun = ↑(intermediateFinset t.val.1 t.val.2.1)) :
    JCSub σ F₁ F₂ H × JCSub σ H F₃ G := by
  have h1 : ∀ x, t.val.1.toFun x ∈ Set.range b.toFun := fun x => by
    rw [hrange]; simp only [intermediateFinset, Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_univ, true_and]; exact .inl ⟨x, rfl⟩
  have h2 : ∀ x, t.val.2.1.toFun x ∈ Set.range b.toFun := fun x => by
    rw [hrange]; simp only [intermediateFinset, Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_univ, true_and]; exact .inr ⟨x, rfl⟩
  set a₁ := pullbackEmbedding b t.val.1 h1; set a₂ := pullbackEmbedding b t.val.2.1 h2
  have hjc_overlap : ∀ i : Fin H.size,
      (i ∈ Set.range a₁.toFun ∧ i ∈ Set.range a₂.toFun) ↔ i ∈ Set.range H.embedding := by
    intro i; constructor
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      have hbi := congr_arg b.toFun (hx.trans hy.symm)
      rw [pullbackEmbedding_spec, pullbackEmbedding_spec] at hbi
      obtain ⟨j, hj⟩ := (t.property.1 (t.val.1.toFun x)).mp ⟨⟨x, rfl⟩, ⟨y, hbi.symm⟩⟩
      exact ⟨j, b.injective (by rw [← hx, pullbackEmbedding_spec, ← hj, b.compat])⟩
    · rintro ⟨j, hj⟩
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := (t.property.1 (G.embedding j)).mpr ⟨j, rfl⟩
      have hbi : b.toFun i = G.embedding j := by subst hj; exact b.compat j
      exact ⟨⟨x, b.injective (by rw [pullbackEmbedding_spec, hbi, hx])⟩,
             ⟨y, b.injective (by rw [pullbackEmbedding_spec, hbi, hy])⟩⟩
  have hjc_covering : ∀ i : Fin H.size,
      i ∈ Set.range a₁.toFun ∨ i ∈ Set.range a₂.toFun := by
    intro i
    have hmem := Set.mem_range_self (f := b.toFun) i; rw [hrange] at hmem
    simp only [intermediateFinset, Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_univ, true_and] at hmem
    rcases hmem with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact .inl ⟨x, b.injective (by rw [pullbackEmbedding_spec, hx])⟩
    · exact .inr ⟨y, b.injective (by rw [pullbackEmbedding_spec, hy])⟩
  have hjc_overlap_G : ∀ i : Fin G.size,
      (i ∈ Set.range b.toFun ∧ i ∈ Set.range t.val.2.2.toFun) ↔
        i ∈ Set.range G.embedding := by
    intro i; constructor
    · rintro ⟨hb_mem, he₃_mem⟩
      have : i ∈ Set.range t.val.1.toFun ∨ i ∈ Set.range t.val.2.1.toFun := by
        rw [hrange] at hb_mem; simp only [intermediateFinset, Finset.coe_filter,
          Set.mem_setOf_eq, Finset.mem_univ, true_and] at hb_mem; exact hb_mem
      rcases this with ⟨x, hx⟩ | ⟨y, hy⟩
      · exact (t.property.2.1 i).mp ⟨⟨x, hx⟩, he₃_mem⟩
      · exact (t.property.2.2.1 i).mp ⟨⟨y, hy⟩, he₃_mem⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨H.embedding j, b.compat j⟩,
             ((t.property.2.1 (G.embedding j)).mpr ⟨j, rfl⟩).2⟩
  have hjc_covering_G : ∀ i : Fin G.size,
      i ∈ Set.range b.toFun ∨ i ∈ Set.range t.val.2.2.toFun := by
    intro i; rcases t.property.2.2.2 i with h1' | h2' | h3'
    · exact .inl (hrange ▸ by simp only [intermediateFinset, Finset.coe_filter,
        Set.mem_setOf_eq, Finset.mem_univ, true_and]; exact .inl h1')
    · exact .inl (hrange ▸ by simp only [intermediateFinset, Finset.coe_filter,
        Set.mem_setOf_eq, Finset.mem_univ, true_and]; exact .inr h2')
    · exact .inr h3'
  exact (⟨⟨a₁, a₂⟩, hjc_overlap, hjc_covering⟩, ⟨⟨b, t.val.2.2⟩, hjc_overlap_G, hjc_covering_G⟩)

private theorem decomposeTriple_composeMap {σ : FlagType} {F₁ F₂ F₃ H G : Flag σ}
    (t : TJCSub σ F₁ F₂ F₃ G) (b : InducedEmbedding σ H G)
    (hrange : Set.range b.toFun = ↑(intermediateFinset t.val.1 t.val.2.1)) :
    composeMap (decomposeTriple t b hrange) = t := by
  apply Subtype.ext
  simp only [composeMap_val_eq, composeMap_val, decomposeTriple]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · exact comp_pullback_eq b t.val.1 _
  · exact comp_pullback_eq b t.val.2.1 _

private theorem decomposeTriple_b {σ : FlagType} {F₁ F₂ F₃ H G : Flag σ}
    (t : TJCSub σ F₁ F₂ F₃ G) (b : InducedEmbedding σ H G)
    (hrange : Set.range b.toFun = ↑(intermediateFinset t.val.1 t.val.2.1)) :
    (decomposeTriple t b hrange).2.val.1 = b := rfl

set_option maxHeartbeats 3200000 in
private theorem per_class_orbit_counting {σ : FlagType} {F₁ F₂ F₃ G : Flag σ}
    {n : ℕ} (hn : σ.size ≤ n) (hn_eq : n = F₁.size + F₂.size - σ.size)
    (cls : FlagClass σ) (_hcls : cls ∈ classesOfSize σ n hn) :
    jointCount σ F₁ F₂ cls.out * jointCount σ cls.out F₃ G =
    flagAutCount σ cls.out *
      (Finset.univ.filter (fun t : TJCSub σ F₁ F₂ F₃ G =>
        tjcIntermediateClass (hn_eq ▸ hn) t = cls)).card := by
  set H := cls.out
  suffices h : Fintype.card (JCSub σ F₁ F₂ H × JCSub σ H F₃ G) =
      Fintype.card (InducedEmbedding σ H H) *
        (Finset.univ.filter (fun t : TJCSub σ F₁ F₂ F₃ G =>
          tjcIntermediateClass (hn_eq ▸ hn) t = cls)).card by
    rw [show jointCount σ F₁ F₂ H = Fintype.card (JCSub σ F₁ F₂ H) from rfl,
        show jointCount σ H F₃ G = Fintype.card (JCSub σ H F₃ G) from rfl,
        show flagAutCount σ H = Fintype.card (InducedEmbedding σ H H) from rfl,
        ← Fintype.card_prod]
    exact h
  set fiber := Finset.univ.filter (fun t : TJCSub σ F₁ F₂ F₃ G =>
    tjcIntermediateClass (hn_eq ▸ hn) t = cls)
  have hmap : ∀ pair : JCSub σ F₁ F₂ H × JCSub σ H F₃ G,
      composeMap pair ∈ fiber := by
    intro pair
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [composeMap_class (hn_eq ▸ hn) pair, FlagClass.mk, Quotient.out_eq]
  rw [show Fintype.card (JCSub σ F₁ F₂ H × JCSub σ H F₃ G) =
      fiber.sum (fun t => (Finset.univ.filter (fun pair : JCSub σ F₁ F₂ H × JCSub σ H F₃ G =>
        composeMap pair = t)).card) from
    Finset.card_eq_sum_card_fiberwise (fun pair _ => hmap pair)]
  suffices hconst : ∀ t ∈ fiber,
      (Finset.univ.filter (fun pair : JCSub σ F₁ F₂ H × JCSub σ H F₃ G =>
        composeMap pair = t)).card =
      Fintype.card (InducedEmbedding σ H H) by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
  intro t ht
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  set Sub_t := intermediateSubflag' t.val.1 t.val.2.1 t.property.1 (hn_eq ▸ hn)
  have hiso_class : tjcIntermediateClass (hn_eq ▸ hn) t = FlagClass.mk Sub_t := rfl
  have hH_cls : FlagClass.mk H = cls := Quotient.out_eq cls
  have hcls_eq : FlagClass.mk Sub_t = FlagClass.mk H := by rw [← hiso_class, ht, hH_cls]
  have ⟨iso, hiso_compat⟩ := (FlagClass.mk_eq _ _).mp hcls_eq
  set incl_t := intermediateSubflag'_incl t.val.1 t.val.2.1 t.property.1 (hn_eq ▸ hn)
  set b₀ := InducedEmbedding.mapIsoInv iso hiso_compat incl_t with hb₀_def
  have hb₀_range : Set.range b₀.toFun =
      ↑(intermediateFinset t.val.1 t.val.2.1) := by
    rw [hb₀_def, InducedEmbedding.range_mapIsoInv]
    exact intermediateSubflag'_incl_range t.val.1 t.val.2.1 t.property.1 (hn_eq ▸ hn)
  have hpreimage_range :
      ∀ pair : JCSub σ F₁ F₂ H × JCSub σ H F₃ G,
      composeMap pair = t →
      Set.range pair.2.val.1.toFun = Set.range b₀.toFun := by
    intro pair hpair
    have hval := congr_arg Subtype.val hpair
    have hfun1 : ∀ x, pair.2.val.1.toFun (pair.1.val.1.toFun x) = t.val.1.toFun x := by
      intro x
      exact congr_fun (congr_arg InducedEmbedding.toFun
        ((by simp only [composeMap_val_eq, composeMap_val] :
          (composeMap pair).val.1 = pair.2.val.1.comp pair.1.val.1).symm.trans
          (congr_arg (·.1) hval))) x
    have hfun2 : ∀ x, pair.2.val.1.toFun (pair.1.val.2.toFun x) = t.val.2.1.toFun x := by
      intro x
      exact congr_fun (congr_arg InducedEmbedding.toFun
        ((by simp only [composeMap_val_eq, composeMap_val] :
          (composeMap pair).val.2.1 = pair.2.val.1.comp pair.1.val.2).symm.trans
          (congr_arg (·.2.1) hval))) x
    rw [hb₀_range]; ext v
    constructor
    · rintro ⟨w, rfl⟩
      simp only [intermediateFinset, Finset.coe_filter, Set.mem_setOf_eq,
        Finset.mem_univ, true_and]
      rcases pair.1.property.2 w with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · left; exact ⟨z, (hfun1 z).symm⟩
      · right; exact ⟨z, (hfun2 z).symm⟩
    · intro hv
      simp only [intermediateFinset, Finset.coe_filter, Set.mem_setOf_eq,
        Finset.mem_univ, true_and] at hv
      rcases hv with ⟨x, hx⟩ | ⟨x, hx⟩
      · exact ⟨pair.1.val.1.toFun x, (hfun1 x).trans hx⟩
      · exact ⟨pair.1.val.2.toFun x, (hfun2 x).trans hx⟩
  have hinj : ∀ pair₁ pair₂ : JCSub σ F₁ F₂ H × JCSub σ H F₃ G,
      composeMap pair₁ = t → composeMap pair₂ = t →
      pair₁.2.val.1 = pair₂.2.val.1 → pair₁ = pair₂ := by
    intro p₁ p₂ hp₁ hp₂ hb_eq
    have hval₁ := congr_arg Subtype.val hp₁
    have hval₂ := congr_arg Subtype.val hp₂
    have cm := fun p => (by simp only [composeMap_val_eq, composeMap_val] :
      (composeMap p).val.1 = (p : JCSub σ F₁ F₂ H × JCSub σ H F₃ G).2.val.1.comp p.1.val.1)
    have cm2 := fun p => (by simp only [composeMap_val_eq, composeMap_val] :
      (composeMap p).val.2.1 = (p : JCSub σ F₁ F₂ H × JCSub σ H F₃ G).2.val.1.comp p.1.val.2)
    have heq₁ : p₁.2.val.1.comp p₁.1.val.1 = t.val.1 := (cm p₁).symm.trans (congr_arg (·.1) hval₁)
    have heq₂ : p₂.2.val.1.comp p₂.1.val.1 = t.val.1 := (cm p₂).symm.trans (congr_arg (·.1) hval₂)
    have heq₃ : p₁.2.val.1.comp p₁.1.val.2 = t.val.2.1 :=
      (cm2 p₁).symm.trans (congr_arg (·.2.1) hval₁)
    have heq₄ : p₂.2.val.1.comp p₂.1.val.2 = t.val.2.1 :=
      (cm2 p₂).symm.trans (congr_arg (·.2.1) hval₂)
    have ha₁ : p₁.1.val.1 = p₂.1.val.1 := by
      apply InducedEmbedding.ext'; funext x; apply p₂.2.val.1.injective
      have : (p₁.2.val.1.comp p₁.1.val.1).toFun x = (p₂.2.val.1.comp p₂.1.val.1).toFun x := by
        rw [heq₁, heq₂]
      simp only [InducedEmbedding.comp, Function.comp_apply] at this; rwa [hb_eq] at this
    have ha₂ : p₁.1.val.2 = p₂.1.val.2 := by
      apply InducedEmbedding.ext'; funext x; apply p₂.2.val.1.injective
      have : (p₁.2.val.1.comp p₁.1.val.2).toFun x = (p₂.2.val.1.comp p₂.1.val.2).toFun x := by
        rw [heq₃, heq₄]
      simp only [InducedEmbedding.comp, Function.comp_apply] at this; rwa [hb_eq] at this
    have he₃ : p₁.2.val.2 = p₂.2.val.2 := by
      have := fun p => (by simp only [composeMap_val_eq, composeMap_val] :
        (composeMap p).val.2.2 = (p : JCSub σ F₁ F₂ H × JCSub σ H F₃ G).2.val.2)
      rw [← this p₁, ← this p₂]
      exact (congr_arg (·.2.2) hval₁).trans (congr_arg (·.2.2) hval₂).symm
    exact Prod.ext (Subtype.ext (Prod.ext ha₁ ha₂)) (Subtype.ext (Prod.ext hb_eq he₃))
  apply Nat.le_antisymm
  · rw [← Fintype.card_coe, ← Fintype.card_congr (sameRangeEquiv b₀).symm]
    apply Fintype.card_le_of_injective
      (fun ⟨pair, hmem⟩ =>
        ⟨pair.2.val.1,
          hpreimage_range pair (by simpa only [Finset.mem_filter, Finset.mem_univ,
            true_and] using hmem)⟩)
    intro ⟨p₁, hm₁⟩ ⟨p₂, hm₂⟩ heq
    simp only [Subtype.mk.injEq] at heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hm₂
    exact Subtype.ext (hinj p₁ p₂ hm₁ hm₂ heq)
  · rw [← Fintype.card_coe]
    have hcomp_range : ∀ α : InducedEmbedding σ H H,
        Set.range (b₀.comp α).toFun = Set.range b₀.toFun := by
      intro α; ext v
      simp only [InducedEmbedding.comp, Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨α.toFun y, rfl⟩
      · rintro ⟨y, rfl⟩
        obtain ⟨z, rfl⟩ := (Finite.injective_iff_surjective.mp α.injective) y
        exact ⟨z, rfl⟩
    apply Fintype.card_le_of_injective (fun α => by
      have hb_range_eq : Set.range (b₀.comp α).toFun =
          ↑(intermediateFinset t.val.1 t.val.2.1) := by
        rw [hcomp_range α, hb₀_range]
      exact ⟨decomposeTriple t (b₀.comp α) hb_range_eq,
        by simp [Finset.mem_filter, decomposeTriple_composeMap t (b₀.comp α) hb_range_eq]⟩)
    intro α₁ α₂ heq
    simp only [Subtype.mk.injEq] at heq
    have hb_eq : b₀.comp α₁ = b₀.comp α₂ := by
      rw [← decomposeTriple_b t (b₀.comp α₁) (by rw [hcomp_range, hb₀_range]),
          ← decomposeTriple_b t (b₀.comp α₂) (by rw [hcomp_range, hb₀_range])]
      exact congr_arg (fun p => (p : JCSub σ F₁ F₂ H × JCSub σ H F₃ G).2.val.1) heq
    apply InducedEmbedding.ext'; funext x
    exact b₀.injective (by
      have := congr_fun (congr_arg InducedEmbedding.toFun hb_eq) x
      simpa only [InducedEmbedding.comp, Function.comp_apply] using this)

set_option maxHeartbeats 800000 in
-- Orbit-counting identity (Razborov 2007, Theorem 2.5)
theorem orbit_counting_factoring (σ : FlagType) (F₁ F₂ F₃ G : Flag σ)
    (n : ℕ) (hn : σ.size ≤ n) (hn_eq : n = F₁.size + F₂.size - σ.size) :
    (classesOfSize σ n hn).sum (fun H =>
        ((jointCount σ F₁ F₂ H.out : ℝ) * (jointCount σ H.out F₃ G : ℝ)) /
        (flagAutCount σ H.out : ℝ)) =
    (tripleJointCount σ F₁ F₂ F₃ G : ℝ) := by
  rw [Finset.sum_congr rfl (fun cls hcls => by
    rw [div_eq_iff (ne_of_gt (Nat.cast_pos.mpr (flagAutCount_pos σ cls.out))),
      show (jointCount σ F₁ F₂ cls.out : ℝ) * (jointCount σ cls.out F₃ G : ℝ) =
        (flagAutCount σ cls.out : ℝ) * ((Finset.univ.filter (fun t : TJCSub σ F₁ F₂ F₃ G =>
          tjcIntermediateClass (hn_eq ▸ hn) t = cls)).card : ℝ) from by
        exact_mod_cast @per_class_orbit_counting σ F₁ F₂ F₃ G n hn hn_eq cls hcls, mul_comm])]
  change _ = ((Finset.univ : Finset (TJCSub σ F₁ F₂ F₃ G)).card : ℝ)
  exact_mod_cast (Finset.card_eq_sum_card_fiberwise
    (fun t _ => tjcIntermediateClass_mem hn hn_eq t)).symm

/-- **Counting-level triple joint factoring**: the sum over iso classes of
    JC(F₁,F₂;H.out)·JC(H.out,F₃;G)/Aut(H.out) equals TJC(F₁,F₂,F₃;G).
    This is the orbit-counting identity (Razborov 2007, Thm 2.5). -/
private theorem triple_joint_count_factoring (σ : FlagType) (F₁ F₂ F₃ G : Flag σ)
    (hℓ : σ.size ≤ F₁.size + F₂.size - σ.size) :
    (classesOfSize σ (F₁.size + F₂.size - σ.size) hℓ).sum (fun H =>
        ((jointCount σ F₁ F₂ H.out : ℝ) * (jointCount σ H.out F₃ G : ℝ)) /
        (flagAutCount σ H.out : ℝ)) =
    (tripleJointCount σ F₁ F₂ F₃ G : ℝ) :=
  orbit_counting_factoring σ F₁ F₂ F₃ G _ hℓ rfl

/-- **Triple joint factoring** (orbit-counting identity): the triple joint induced
    density factors through any intermediate iso class sum. The sum over classes [H]
    of size |F₁|+|F₂|-|σ| of JID(F₁,F₂;H)·JID(H,F₃;G)/Aut(H) equals TJD(F₁,F₂,F₃;G).

    Proved from `triple_joint_count_factoring` (counting level) and
    `multinomial_factoring` (density-to-counting reduction). -/
theorem triple_joint_factoring (σ : FlagType) (F₁ F₂ F₃ G : Flag σ)
    (hℓ : σ.size ≤ F₁.size + F₂.size - σ.size) :
    (classesOfSize σ (F₁.size + F₂.size - σ.size) hℓ).sum (fun H =>
        jointInducedDensity σ F₁ F₂ H.out *
          jointInducedDensity σ H.out F₃ G /
          (flagAutCount σ H.out : ℝ)) =
    tripleJointInducedDensity σ F₁ F₂ F₃ G := by
  -- Abbreviations
  set n := F₁.size + F₂.size - σ.size
  -- Key size fact: n - σ.size = (F₁.size - σ.size) + (F₂.size - σ.size)
  have h_ns : n - σ.size = (F₁.size - σ.size) + (F₂.size - σ.size) := by
    have := F₁.hsize; have := F₂.hsize; omega
  -- Expand JID and TJD to JC / multinomial
  unfold jointInducedDensity tripleJointInducedDensity
  -- All H.out have size n, so H.out.size - σ.size = n - σ.size
  -- Rewrite each summand: JID₁₂·JID_H₃/Aut = JC₁₂·JC_H₃/(M₁₂·M_H₃·Aut)
  -- where M₁₂ and M_H₃ are constant across H (depend only on sizes)
  have h_rw : ∀ H ∈ classesOfSize σ n hℓ,
      (jointCount σ F₁ F₂ H.out : ℝ) /
        ((Nat.choose (H.out.size - σ.size) (F₁.size - σ.size) : ℝ) *
          (Nat.choose (H.out.size - σ.size - (F₁.size - σ.size))
            (F₂.size - σ.size) : ℝ)) *
        ((jointCount σ H.out F₃ G : ℝ) /
          ((Nat.choose (G.size - σ.size) (H.out.size - σ.size) : ℝ) *
            (Nat.choose (G.size - σ.size - (H.out.size - σ.size))
              (F₃.size - σ.size) : ℝ))) /
        (flagAutCount σ H.out : ℝ) =
      ((jointCount σ F₁ F₂ H.out : ℝ) * (jointCount σ H.out F₃ G : ℝ)) /
        ((flagAutCount σ H.out : ℝ) *
          ((Nat.choose (n - σ.size) (F₁.size - σ.size) : ℝ) *
            (Nat.choose (n - σ.size - (F₁.size - σ.size))
              (F₂.size - σ.size) : ℝ) *
            ((Nat.choose (G.size - σ.size) (n - σ.size) : ℝ) *
              (Nat.choose (G.size - σ.size - (n - σ.size))
                (F₃.size - σ.size) : ℝ)))) := fun H hH => by
    have hsize := classesOfSize_out_size hH
    rw [hsize]; ring
  rw [Finset.sum_congr rfl h_rw]
  -- Factor out the constant multinomial denominator
  set M := (Nat.choose (n - σ.size) (F₁.size - σ.size) : ℝ) *
            (Nat.choose (n - σ.size - (F₁.size - σ.size))
              (F₂.size - σ.size) : ℝ) *
            ((Nat.choose (G.size - σ.size) (n - σ.size) : ℝ) *
              (Nat.choose (G.size - σ.size - (n - σ.size))
                (F₃.size - σ.size) : ℝ))
  -- Each summand is (JC₁₂ · JC_H₃) / (Aut · M) = (JC₁₂ · JC_H₃ / Aut) / M
  have h_factor : ∀ H ∈ classesOfSize σ n hℓ,
      ((jointCount σ F₁ F₂ H.out : ℝ) * (jointCount σ H.out F₃ G : ℝ)) /
        ((flagAutCount σ H.out : ℝ) * M) =
      ((jointCount σ F₁ F₂ H.out : ℝ) * (jointCount σ H.out F₃ G : ℝ) /
        (flagAutCount σ H.out : ℝ)) / M := fun H _ => by ring
  rw [Finset.sum_congr rfl h_factor, ← Finset.sum_div,
      triple_joint_count_factoring σ F₁ F₂ F₃ G hℓ]
  -- Goal: TJC / M = TJC / M₁₂₃ where M₁₂₃ is the TJD denominator
  -- Need M = M₁₂₃ by the trinomial identity
  suffices hM : M =
      (Nat.choose (G.size - σ.size) (F₁.size - σ.size) : ℝ) *
        (Nat.choose (G.size - σ.size - (F₁.size - σ.size))
          (F₂.size - σ.size) : ℝ) *
        (Nat.choose (G.size - σ.size - (F₁.size - σ.size) -
          (F₂.size - σ.size)) (F₃.size - σ.size) : ℝ) by
    rw [hM]
  -- Expand M and use multinomial_factoring
  change (Nat.choose (n - σ.size) (F₁.size - σ.size) : ℝ) *
        (Nat.choose (n - σ.size - (F₁.size - σ.size))
          (F₂.size - σ.size) : ℝ) *
        ((Nat.choose (G.size - σ.size) (n - σ.size) : ℝ) *
          (Nat.choose (G.size - σ.size - (n - σ.size))
            (F₃.size - σ.size) : ℝ)) = _
  rw [h_ns]
  set f₁ := F₁.size - σ.size
  set f₂ := F₂.size - σ.size
  set f₃ := F₃.size - σ.size
  set g := G.size - σ.size
  -- LHS: C(f₁+f₂, f₁) · C(f₂, f₂) · C(g, f₁+f₂) · C(g-(f₁+f₂), f₃)
  -- RHS: C(g, f₁) · C(g-f₁, f₂) · C(g-f₁-f₂, f₃)
  have hf₂f₂ : (Nat.choose f₂ f₂ : ℝ) = 1 := by simp [Nat.choose_self]
  rw [show f₁ + f₂ - f₁ = f₂ from by omega, hf₂f₂]
  by_cases hf₁₂ : f₁ + f₂ ≤ g
  · simp only [mul_one]
    have hsub : g - (f₁ + f₂) = g - f₁ - f₂ := by omega
    have hM := multinomial_factoring g f₁ f₂ f₃ hf₁₂
    rw [hsub] at hM ⊢; exact hM
  · push_neg at hf₁₂
    have h1 : (Nat.choose g (f₁ + f₂) : ℝ) = 0 := by
      exact_mod_cast Nat.choose_eq_zero_of_lt hf₁₂
    have h2 : (Nat.choose g f₁ : ℝ) * (Nat.choose (g - f₁) f₂ : ℝ) = 0 := by
      rcases le_or_gt f₁ g with hf₁ | hf₁
      · simp [show Nat.choose (g - f₁) f₂ = 0 from by rw [Nat.choose_eq_zero_iff]; omega]
      · simp [show Nat.choose g f₁ = 0 from Nat.choose_eq_zero_of_lt hf₁]
    have : (0 : ℝ) ≤ (Nat.choose (g - f₁ - f₂) f₃ : ℝ) := Nat.cast_nonneg _
    simp only [h1, h2, zero_mul, mul_zero, mul_one]

/-- **Coefficient-level chain rule** (Razborov 2007, Thm 2.5): for any flags F₁,F₂,F₃,G,
    factoring the triple product through F₁·F₂ gives the same coefficient as factoring
    through F₂·F₃. Both sides equal the triple joint density.

    Proved from `triple_joint_factoring` and `tripleJointInducedDensity_perm_231`. -/
theorem coeff_chain_rule (σ : FlagType) (F₁ F₂ F₃ G : Flag σ)
    (hℓ : σ.size ≤ F₁.size + F₂.size - σ.size)
    (hm : σ.size ≤ F₂.size + F₃.size - σ.size) :
    ((flagAutCount σ F₁ : ℝ) * (flagAutCount σ F₂ : ℝ))⁻¹ *
      (classesOfSize σ (F₁.size + F₂.size - σ.size) hℓ).sum (fun H =>
        jointInducedDensity σ F₁ F₂ H.out *
          ((flagAutCount σ H.out : ℝ) * (flagAutCount σ F₃ : ℝ))⁻¹ *
          jointInducedDensity σ H.out F₃ G) =
    ((flagAutCount σ F₂ : ℝ) * (flagAutCount σ F₃ : ℝ))⁻¹ *
      (classesOfSize σ (F₂.size + F₃.size - σ.size) hm).sum (fun H' =>
        jointInducedDensity σ F₂ F₃ H'.out *
          ((flagAutCount σ F₁ : ℝ) * (flagAutCount σ H'.out : ℝ))⁻¹ *
          jointInducedDensity σ F₁ H'.out G) := by
  set T := tripleJointInducedDensity σ F₁ F₂ F₃ G
  have sum_lhs : (classesOfSize σ (F₁.size + F₂.size - σ.size) hℓ).sum (fun H =>
      jointInducedDensity σ F₁ F₂ H.out *
        ((flagAutCount σ H.out : ℝ) * (flagAutCount σ F₃ : ℝ))⁻¹ *
        jointInducedDensity σ H.out F₃ G) = (flagAutCount σ F₃ : ℝ)⁻¹ * T := by
    have h_rw : ∀ H ∈ classesOfSize σ (F₁.size + F₂.size - σ.size) hℓ,
        jointInducedDensity σ F₁ F₂ H.out *
          ((flagAutCount σ H.out : ℝ) * (flagAutCount σ F₃ : ℝ))⁻¹ *
          jointInducedDensity σ H.out F₃ G = (flagAutCount σ F₃ : ℝ)⁻¹ *
          (jointInducedDensity σ F₁ F₂ H.out * jointInducedDensity σ H.out F₃ G /
            (flagAutCount σ H.out : ℝ)) := fun H _ => by rw [mul_inv]; ring
    rw [Finset.sum_congr rfl h_rw, ← Finset.mul_sum,
        triple_joint_factoring σ F₁ F₂ F₃ G hℓ]
  have sum_rhs : (classesOfSize σ (F₂.size + F₃.size - σ.size) hm).sum (fun H' =>
      jointInducedDensity σ F₂ F₃ H'.out *
        ((flagAutCount σ F₁ : ℝ) * (flagAutCount σ H'.out : ℝ))⁻¹ *
        jointInducedDensity σ F₁ H'.out G) = (flagAutCount σ F₁ : ℝ)⁻¹ * T := by
    have h_rw : ∀ H' ∈ classesOfSize σ (F₂.size + F₃.size - σ.size) hm,
        jointInducedDensity σ F₂ F₃ H'.out *
          ((flagAutCount σ F₁ : ℝ) * (flagAutCount σ H'.out : ℝ))⁻¹ *
          jointInducedDensity σ F₁ H'.out G = (flagAutCount σ F₁ : ℝ)⁻¹ *
          (jointInducedDensity σ F₂ F₃ H'.out * jointInducedDensity σ H'.out F₁ G /
            (flagAutCount σ H'.out : ℝ)) :=
      fun H' _ => by rw [mul_inv, jointInducedDensity_comm σ F₁ H'.out G]; ring
    rw [Finset.sum_congr rfl h_rw, ← Finset.mul_sum,
        triple_joint_factoring σ F₂ F₃ F₁ G hm,
        ← tripleJointInducedDensity_perm_231 σ F₁ F₂ F₃ G]
  rw [sum_lhs, sum_rhs]; ring

/-- **Chain rule for the local flag product** (Thesis Lemma 1.3, Razborov Thm 2.5):
    Factoring a triple product through two different intermediate sizes yields the same
    result. Both sides equal the triple joint density sum Σ_G p(F₁,F₂,F₃;G)·[G].

    Proved from `coeff_chain_rule` by extracting Finsupp coefficients. -/
private theorem localFlagProduct_apply (σ : FlagType) (A B : Flag σ)
    (hAB : σ.size ≤ A.size + B.size - σ.size) (cls : FlagClass σ) :
    (localFlagProduct σ A B) cls =
      ((flagAutCount σ A : ℝ) * (flagAutCount σ B : ℝ))⁻¹ *
        (classesOfSize σ (A.size + B.size - σ.size) hAB).sum (fun G =>
          if G = cls then jointInducedDensity σ A B G.out else 0) := by
  simp only [localFlagProduct, dif_pos hAB, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.finset_sum_apply, Finsupp.single_apply]

set_option maxHeartbeats 1600000 in
theorem density_chain_rule (σ : FlagType) (F₁ F₂ F₃ : Flag σ)
    (hℓ : σ.size ≤ F₁.size + F₂.size - σ.size)
    (hm : σ.size ≤ F₂.size + F₃.size - σ.size) :
    ((flagAutCount σ F₁ : ℝ) * (flagAutCount σ F₂ : ℝ))⁻¹ •
      (classesOfSize σ (F₁.size + F₂.size - σ.size) hℓ).sum (fun H =>
        jointInducedDensity σ F₁ F₂ H.out • localFlagProduct σ H.out F₃) =
    ((flagAutCount σ F₂ : ℝ) * (flagAutCount σ F₃ : ℝ))⁻¹ •
      (classesOfSize σ (F₂.size + F₃.size - σ.size) hm).sum (fun H' =>
        jointInducedDensity σ F₂ F₃ H'.out • localFlagProduct σ F₁ H'.out) := by
  have hHF₃ : ∀ H : FlagClass σ, H ∈ classesOfSize σ (F₁.size + F₂.size - σ.size) hℓ →
      σ.size ≤ H.out.size + F₃.size - σ.size := by
    intro H hmem; have := classesOfSize_out_size hmem; have := F₃.hsize; omega
  have hF₁H' : ∀ H' : FlagClass σ, H' ∈ classesOfSize σ (F₂.size + F₃.size - σ.size) hm →
      σ.size ≤ F₁.size + H'.out.size - σ.size := by
    intro H' hmem; have := classesOfSize_out_size hmem; have := F₁.hsize; omega
  ext cls
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.finset_sum_apply]
  set n₃ := F₁.size + F₂.size + F₃.size - 2 * σ.size with hn₃_def
  have hn₃ : σ.size ≤ n₃ := by
    have := F₁.hsize; have := F₂.hsize; have := F₃.hsize; omega
  have lhs_eq : (∑ H ∈ classesOfSize σ (F₁.size + F₂.size - σ.size) hℓ,
      jointInducedDensity σ F₁ F₂ H.out * (localFlagProduct σ H.out F₃) cls) =
    (∑ H ∈ classesOfSize σ (F₁.size + F₂.size - σ.size) hℓ,
      jointInducedDensity σ F₁ F₂ H.out *
        ((flagAutCount σ H.out : ℝ) * (flagAutCount σ F₃ : ℝ))⁻¹ *
        (if cls ∈ classesOfSize σ n₃ hn₃
         then jointInducedDensity σ H.out F₃ cls.out else 0)) := by
    apply Finset.sum_congr rfl; intro H hmem
    rw [localFlagProduct_apply σ H.out F₃ (hHF₃ H hmem) cls, Finset.sum_ite_eq', mul_assoc]
    rw [show classesOfSize σ (H.out.size + F₃.size - σ.size) (hHF₃ H hmem) =
      classesOfSize σ n₃ hn₃ from by
        congr 1; have := classesOfSize_out_size hmem; have := F₃.hsize; omega]
  have rhs_eq : (∑ H' ∈ classesOfSize σ (F₂.size + F₃.size - σ.size) hm,
      jointInducedDensity σ F₂ F₃ H'.out * (localFlagProduct σ F₁ H'.out) cls) =
    (∑ H' ∈ classesOfSize σ (F₂.size + F₃.size - σ.size) hm,
      jointInducedDensity σ F₂ F₃ H'.out *
        ((flagAutCount σ F₁ : ℝ) * (flagAutCount σ H'.out : ℝ))⁻¹ *
        (if cls ∈ classesOfSize σ n₃ hn₃
         then jointInducedDensity σ F₁ H'.out cls.out else 0)) := by
    apply Finset.sum_congr rfl; intro H' hmem
    rw [localFlagProduct_apply σ F₁ H'.out (hF₁H' H' hmem) cls, Finset.sum_ite_eq', mul_assoc]
    rw [show classesOfSize σ (F₁.size + H'.out.size - σ.size) (hF₁H' H' hmem) =
      classesOfSize σ n₃ hn₃ from by
        congr 1; have := classesOfSize_out_size hmem; have := F₁.hsize; omega]
  rw [lhs_eq, rhs_eq]
  by_cases hmem : cls ∈ classesOfSize σ n₃ hn₃
  · simp only [if_pos hmem]; exact coeff_chain_rule σ F₁ F₂ F₃ cls.out hℓ hm
  · simp only [if_neg hmem, mul_zero, Finset.sum_const_zero, mul_zero]

private theorem product_assoc_basis (σ : FlagType) (F₁ F₂ F₃ : Flag σ) :
    (localFlagProduct σ F₁ F₂).mul (FlagAlg.single σ F₃) =
      (FlagAlg.single σ F₁).mul (localFlagProduct σ F₂ F₃) := by
  show FlagAlg.mul (localFlagProduct σ F₁ F₂) (FlagAlg.single σ F₃) =
    FlagAlg.mul (FlagAlg.single σ F₁) (localFlagProduct σ F₂ F₃)
  have hℓ : σ.size ≤ F₁.size + F₂.size - σ.size := by
    have := F₁.hsize; have := F₂.hsize; omega
  have hm : σ.size ≤ F₂.size + F₃.size - σ.size := by
    have := F₂.hsize; have := F₃.hsize; omega
  have h12 : localFlagProduct σ F₁ F₂ =
      ((flagAutCount σ F₁ : ℝ) * (flagAutCount σ F₂ : ℝ))⁻¹ •
        (classesOfSize σ (F₁.size + F₂.size - σ.size) hℓ).sum (fun cls =>
          Finsupp.single cls (jointInducedDensity σ F₁ F₂ cls.out)) := by
    unfold localFlagProduct; simp only [dif_pos hℓ]
  have h23 : localFlagProduct σ F₂ F₃ =
      ((flagAutCount σ F₂ : ℝ) * (flagAutCount σ F₃ : ℝ))⁻¹ •
        (classesOfSize σ (F₂.size + F₃.size - σ.size) hm).sum (fun cls =>
          Finsupp.single cls (jointInducedDensity σ F₂ F₃ cls.out)) := by
    unfold localFlagProduct; simp only [dif_pos hm]
  rw [h12, FlagAlg.smul_mul, finset_sum_single_mul_right,
      h23, FlagAlg.mul_smul, single_mul_finset_sum_single]
  exact density_chain_rule σ F₁ F₂ F₃ hℓ hm

private theorem Finsupp.single_eq_smul_one (a : FlagClass σ) (b : ℝ) :
    Finsupp.single a b = b • Finsupp.single a (1 : ℝ) := by
  rw [Finsupp.smul_single', mul_one]

private theorem Finsupp.single_one_eq_FlagAlg_single (σ : FlagType) (a : FlagClass σ) :
    Finsupp.single a (1 : ℝ) = FlagAlg.single σ a.out := by
  unfold FlagAlg.single FlagClass.mk
  congr 1
  exact (Quotient.out_eq a).symm

/-- Associativity for two basis flags and an arbitrary element.
    Reduces to `product_assoc_basis` by Finsupp induction on the third factor. -/
private theorem product_assoc_left_basis (σ : FlagType) (F₁ F₂ : Flag σ) (v₃ : FlagAlg σ) :
    (localFlagProduct σ F₁ F₂).mul v₃ =
      (FlagAlg.single σ F₁).mul ((FlagAlg.single σ F₂).mul v₃) := by
  induction v₃ using Finsupp.induction with
  | zero => simp only [FlagAlg.mul_zero_right]
  | single_add a₃ b₃ f₃ ha₃ hb₃ ih₃ =>
    rw [FlagAlg.mul_add, FlagAlg.mul_add, FlagAlg.mul_add]
    congr 1
    rw [Finsupp.single_eq_smul_one a₃ b₃,
        FlagAlg.mul_smul, FlagAlg.mul_smul, FlagAlg.mul_smul]
    congr 1
    rw [Finsupp.single_one_eq_FlagAlg_single σ a₃]
    conv_rhs => rw [FlagAlg.mul_single]
    exact product_assoc_basis σ F₁ F₂ a₃.out

/-- Associativity for one basis flag and two arbitrary elements.
    Reduces to `product_assoc_left_basis` by Finsupp induction on the second factor. -/
private theorem product_assoc_single (σ : FlagType) (F₁ : Flag σ) (v₂ v₃ : FlagAlg σ) :
    ((FlagAlg.single σ F₁).mul v₂).mul v₃ =
      (FlagAlg.single σ F₁).mul (v₂.mul v₃) := by
  induction v₂ using Finsupp.induction with
  | zero => simp only [FlagAlg.mul_zero_right, FlagAlg.mul_zero_left]
  | single_add a₂ b₂ f₂ ha₂ hb₂ ih₂ =>
    rw [FlagAlg.mul_add, FlagAlg.add_mul, FlagAlg.add_mul, FlagAlg.mul_add]
    congr 1
    rw [Finsupp.single_eq_smul_one a₂ b₂,
        FlagAlg.mul_smul, FlagAlg.smul_mul, FlagAlg.smul_mul, FlagAlg.mul_smul]
    congr 1
    rw [Finsupp.single_one_eq_FlagAlg_single σ a₂, FlagAlg.mul_single]
    exact product_assoc_left_basis σ F₁ a₂.out v₃

/-- **Lemma 2.4 (Associativity)**: (v₁ · v₂) · v₃ = v₁ · (v₂ · v₃).
    Proof: Reduce to basis elements by triple Finsupp induction using linearity
    of `FlagAlg.mul`, then apply the chain rule (thesis Lemma 1.3). -/
theorem product_assoc (σ : FlagType) (v₁ v₂ v₃ : FlagAlg σ) :
    (v₁.mul v₂).mul v₃ = v₁.mul (v₂.mul v₃) := by
  induction v₁ using Finsupp.induction with
  | zero => simp only [FlagAlg.mul_zero_left]
  | single_add a b f ha hb ih =>
    rw [FlagAlg.add_mul, FlagAlg.add_mul, FlagAlg.add_mul]
    congr 1
    rw [Finsupp.single_eq_smul_one a b,
        FlagAlg.smul_mul, FlagAlg.smul_mul, FlagAlg.smul_mul]
    congr 1
    rw [Finsupp.single_one_eq_FlagAlg_single σ a]
    exact product_assoc_single σ a.out v₂ v₃

/-! ## §2.2: Limit Functionals

Limits of ρ along Δ-increasing convergent subsequences.
Any Δ-increasing sequence has a convergent subsequence by Tychonoff
(since local densities are bounded, the image is compact). -/

/-- A sequence of σ-flags is **Δ-increasing** if Δ(G_k) is strictly increasing.
    (Thesis §2.2 Definition) -/
structure DeltaIncreasingSeq (σ : FlagType) (Δ : GraphParam) where
  seq : ℕ → Flag σ
  increasing : StrictMono (fun k => Δ (seq k).forget)

/-- Standalone linear evaluation of a `FlagAlg` element given an eval function
    on flags. Used in the `LimitFunctional` structure definition to avoid
    a forward reference to `LimitFunctional.evalAlg`. -/
noncomputable def evalAlgOf (eval : Flag σ → ℝ) (v : FlagAlg σ) : ℝ :=
  v.sum (fun cls c => c * eval cls.out)

/-- A **limit functional** φ ∈ Φ^σ: φ(F) = lim_{k→∞} ρ(F; G_k)
    for a Δ-increasing convergent subsequence (G_k).
    (Thesis §2.2)

    The key properties are:
    * φ is nonneg on flags (densities are nonneg)
    * φ(σ) = 1 (the type has density 1)
    * φ respects isomorphism
    * φ is an algebra homomorphism (immediate corollary of Theorem 2.3) -/
structure LimitFunctional (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam) where
  eval : Flag σ → ℝ
  nonneg_on_flags : ∀ F, 0 ≤ eval F
  eval_type : eval σ.toFlag = 1
  eval_iso : ∀ F₁ F₂ : Flag σ, FlagIso σ F₁ F₂ → eval F₁ = eval F₂
  eval_nonlocal : ∀ F : Flag σ, ¬IsLocalFlag σ F 𝒢 Δ → eval F = 0
  is_homomorphism : ∀ v w : FlagAlg σ,
    (∀ cls ∈ v.support, IsLocalFlag σ cls.out 𝒢 Δ) →
    (∀ cls ∈ w.support, IsLocalFlag σ cls.out 𝒢 Δ) →
    evalAlgOf eval (v.mul w) = evalAlgOf eval v * evalAlgOf eval w
  /-- The Δ-increasing sequence from which this functional was constructed. -/
  seq : DeltaIncreasingSeq σ Δ
  /-- Every flag in the sequence belongs to 𝒢. -/
  seq_in_class : ∀ k, 𝒢 (seq.seq k).forget
  /-- The convergent subsequence extracted by Tychonoff/Bolzano–Weierstrass. -/
  sub : ℕ → ℕ
  /-- The subsequence is strictly monotone. -/
  sub_strictMono : StrictMono sub
  /-- For each local flag F, the unlabelled density along the subsequence
      converges to eval F. -/
  convergence : ∀ F : Flag σ, IsLocalFlag σ F 𝒢 Δ →
    Filter.Tendsto (fun k => unlabelledDensity σ F (seq.seq (sub k)) Δ)
      Filter.atTop (nhds (eval F))

/-- Local density is always nonneg: ρ(F; G) = c(F;G) / C(Δ,n) ≥ 0.

    **Status**: Intentional standalone — foundational positivity fact;
    no consumer expected. -/
theorem localDensity_nonneg (σ : FlagType) (F G : Flag σ) (Δ : GraphParam) :
    0 ≤ localDensity σ F G Δ :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The unique σ-compatible induced embedding of σ.toFlag into any σ-flag G
    is the embedding G.embedding itself. -/
theorem inducedCount_type_eq_one (σ : FlagType) (G : Flag σ) :
    inducedCount σ σ.toFlag G = 1 := by
  unfold inducedCount
  rw [Fintype.card_eq_one_iff]
  -- The canonical embedding sends each labelled vertex i to G.embedding i
  have hcanon_inj : Function.Injective (fun i : Fin σ.size => G.embedding i) :=
    fun _ _ h => G.embedding.injective h
  refine ⟨⟨fun i => G.embedding i, hcanon_inj,
    fun u v hadj => ?_, fun u v _ hnadj => ?_,
    fun i => ?_⟩, fun b => ?_⟩
  · -- map_adj: σ.toFlag.graph.Adj u v → G.graph.Adj (G.embedding u) (G.embedding v)
    -- σ.toFlag.graph = σ.graph, and G.embedding preserves adjacency
    exact G.embedding.map_rel_iff'.mpr hadj
  · -- map_non_adj: ¬σ.graph.Adj u v → ¬G.graph.Adj (G.embedding u) (G.embedding v)
    exact fun hadj' => hnadj (G.embedding.map_rel_iff'.mp hadj')
  · -- compat: (fun i => G.embedding i) (σ.toFlag.embedding i) = G.embedding i
    -- σ.toFlag.embedding = SimpleGraph.Embedding.refl, so σ.toFlag.embedding i = i
    simp [FlagType.toFlag, SimpleGraph.Embedding.refl]
  · -- Uniqueness: any InducedEmbedding σ σ.toFlag G equals the canonical one
    have heq : b.toFun = fun i => G.embedding i := by
      funext v
      -- b.compat v : b.toFun (σ.toFlag.embedding v) = G.embedding v
      -- σ.toFlag.embedding v = v (since embedding = refl)
      have hv : σ.toFlag.embedding v = v := by
        simp [FlagType.toFlag, SimpleGraph.Embedding.refl]
      rw [← hv]
      exact b.compat v
    cases b; simp only at heq; subst heq; rfl

/-- The local density of the type σ viewed as a σ-flag is always 1:
    ρ(σ; G) = c(σ;G)/C(Δ,0) = 1/1 = 1.

    **Status**: Intentional standalone — foundational fact about type
    density; no consumer expected. -/
theorem localDensity_type_eq_one (σ : FlagType) (G : Flag σ) (Δ : GraphParam) :
    localDensity σ σ.toFlag G Δ = 1 := by
  unfold localDensity
  have hsub : σ.toFlag.size - σ.size = 0 := Nat.sub_self σ.size
  rw [hsub, Nat.choose_zero_right, inducedCount_type_eq_one]
  simp

/-! ### Bolzano–Weierstrass for densities

Each local flag F has bounded density ρ(F; ·), so the sequence of densities
along any Δ-increasing sequence lies in a compact interval [0, C].
By Bolzano–Weierstrass (sequential compactness of [0, C] ⊂ ℝ), there
exists a convergent subsequence. This is the per-flag step of the
Tychonoff argument from thesis §2.2. -/

/-- **Bolzano–Weierstrass for local densities**: If F is a local σ-flag,
    the sequence of densities ρ(F; G_k) has a convergent subsequence.
    (Thesis §2.2, per-flag step of the Tychonoff argument.) -/
private theorem density_convergent_subseq
    (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam)
    (seq : DeltaIncreasingSeq σ Δ)
    (hlocal : ∀ k, 𝒢 (seq.seq k).forget)
    (F : Flag σ) (hF : IsLocalFlag σ F 𝒢 Δ) :
    ∃ (sub : ℕ → ℕ) (L : ℝ), StrictMono sub ∧ 0 ≤ L ∧
      Filter.Tendsto (fun k => unlabelledDensity σ F (seq.seq (sub k)) Δ)
        Filter.atTop (nhds L) := by
  obtain ⟨C, hC, hbound⟩ := hF.bounded
  have hmem : ∀ k, unlabelledDensity σ F (seq.seq k) Δ ∈ Set.Icc 0 C :=
    fun k => ⟨unlabelledDensity_nonneg σ F (seq.seq k) Δ,
      le_trans (unlabelledDensity_le_localDensity σ F (seq.seq k) Δ)
        (hbound (seq.seq k) (hlocal k))⟩
  obtain ⟨a, ha_mem, φ, hφ_mono, hφ_tend⟩ := isCompact_Icc.tendsto_subseq hmem
  exact ⟨φ, a, hφ_mono, ha_mem.1, hφ_tend⟩

/-- `Flag σ` is countable: a countable union (over size n ∈ ℕ) of finite types. -/
noncomputable instance Flag.instCountable : Countable (Flag σ) := by
  -- Inject into Σ (n : ℕ) (g : SimpleGraph (Fin n)), σ.graph ↪g g
  -- which is countable (ℕ-indexed union of finite types).
  let T := Σ (n : ℕ) (g : SimpleGraph (Fin n)), σ.graph ↪g g
  have hT : Countable T := inferInstance
  exact @Function.Injective.countable (Flag σ) T hT
    (fun F => ⟨F.size, F.graph, F.embedding⟩)
    (fun F₁ F₂ h => by
      obtain ⟨s₁, g₁, e₁, h₁⟩ := F₁
      obtain ⟨s₂, g₂, e₂, h₂⟩ := F₂
      simp only [T, Sigma.mk.inj_iff] at h
      obtain ⟨hs, hrest⟩ := h; subst hs
      simp only [heq_eq_eq, Sigma.mk.inj_iff] at hrest
      obtain ⟨hg, he⟩ := hrest; subst hg
      simp only [heq_eq_eq] at he; subst he
      rfl)

/-- `FlagClass σ` is countable since it's a quotient of `Flag σ`. -/
noncomputable instance FlagClass.instCountable : Countable (FlagClass σ) := by
  unfold FlagClass; infer_instance

/-- `jointInducedDensity` is nonneg (ratio of Nat casts). -/
private theorem jointInducedDensity_nonneg (σ : FlagType) (F₁ F₂ G : Flag σ) :
    0 ≤ jointInducedDensity σ F₁ F₂ G := by
  unfold jointInducedDensity
  exact div_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Every class in the support of `localFlagProduct σ F F'` is a local flag,
    provided F and F' are local. This follows from `product_closure`. -/
private theorem localFlagProduct_local_support (σ : FlagType) (F F' : Flag σ)
    (𝒢 : GraphClass) (Δ : GraphParam)
    (hF : IsLocalFlag σ F 𝒢 Δ) (hF' : IsLocalFlag σ F' 𝒢 Δ)
    (cls : FlagClass σ) (hcls : cls ∈ (localFlagProduct σ F F').support) :
    IsLocalFlag σ cls.out 𝒢 Δ := by
  simp only [localFlagProduct] at hcls
  by_cases hn : σ.size ≤ F.size + F'.size - σ.size
  · rw [dif_pos hn] at hcls
    simp only [Finsupp.mem_support_iff] at hcls
    rw [Finsupp.smul_apply] at hcls
    -- The scalar is nonzero, so the sum term is nonzero
    have hscalar_ne : ((↑(flagAutCount σ F) * ↑(flagAutCount σ F'))⁻¹ : ℝ) ≠ 0 :=
      inv_ne_zero (mul_ne_zero
        (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (flagAutCount_pos σ F)))
        (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (flagAutCount_pos σ F'))))
    have hsum_ne := right_ne_zero_of_mul (by rwa [smul_eq_mul] at hcls)
    rw [Finsupp.finset_sum_apply] at hsum_ne
    by_contra h_not_local
    apply hsum_ne
    apply Finset.sum_eq_zero
    intro cls' _
    simp only [Finsupp.single_apply]
    split_ifs with heq
    · -- heq : cls' = cls, after subst cls is replaced by cls'
      subst heq
      by_contra h_jid_ne
      exact h_not_local (product_closure σ F F' cls'.out 𝒢 Δ hF hF'
        (lt_of_le_of_ne (jointInducedDensity_nonneg σ F F' cls'.out) (Ne.symm h_jid_ne)))
    · rfl
  · rw [dif_neg hn] at hcls
    exact absurd hcls (by simp [Finsupp.support_zero])

/-- Every class in the support of `v.mul w` is local, provided v and w have
    local support. -/
private theorem mul_local_support (σ : FlagType) (v w : FlagAlg σ)
    (𝒢 : GraphClass) (Δ : GraphParam)
    (hv : ∀ cls ∈ v.support, IsLocalFlag σ cls.out 𝒢 Δ)
    (hw : ∀ cls ∈ w.support, IsLocalFlag σ cls.out 𝒢 Δ)
    (cls : FlagClass σ) (hcls : cls ∈ (v.mul w).support) :
    IsLocalFlag σ cls.out 𝒢 Δ := by
  -- If every LFP(cls₁,cls₂) has zero coefficient at cls for all cls₁ ∈ v, cls₂ ∈ w,
  -- then (v.mul w)(cls) = 0, contradicting cls ∈ support. So some is nonzero → local.
  by_contra h_not_local
  -- Show v.mul w at cls is 0 (contradiction with hcls)
  have hzero : (v.mul w) cls = 0 := by
    simp only [FlagAlg.mul, Finsupp.sum]
    -- Distribute evaluation at cls through the double sum
    rw [Finsupp.finset_sum_apply]
    apply Finset.sum_eq_zero
    intro cls₁ hcls₁
    rw [Finsupp.finset_sum_apply]
    apply Finset.sum_eq_zero
    intro cls₂ hcls₂
    simp only [Finsupp.smul_apply, smul_eq_mul]
    by_cases h : (localFlagProduct_class σ cls₁ cls₂) cls = 0
    · rw [h, mul_zero]
    · exfalso; apply h_not_local
      rw [localFlagProduct_class_out] at h
      exact localFlagProduct_local_support σ cls₁.out cls₂.out 𝒢 Δ
        (hv cls₁ hcls₁) (hw cls₂ hcls₂) cls (Finsupp.mem_support_iff.mpr h)
  exact Finsupp.mem_support_iff.mp hcls hzero

/-- Swapping a finite Finsupp sum with a limit: if each coordinate converges,
    the finite linear combination converges to the linear combination of limits. -/
theorem evalAlgOf_eq_limit
    (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam)
    (seq : DeltaIncreasingSeq σ Δ)
    (sub : ℕ → ℕ)
    (eval : Flag σ → ℝ)
    (hconv : ∀ F : Flag σ, IsLocalFlag σ F 𝒢 Δ →
      Filter.Tendsto (fun k => unlabelledDensity σ F (seq.seq (sub k)) Δ)
        Filter.atTop (nhds (eval F)))
    (_hnonlocal : ∀ F : Flag σ, ¬IsLocalFlag σ F 𝒢 Δ → eval F = 0)
    (v : FlagAlg σ)
    (hv : ∀ cls ∈ v.support, IsLocalFlag σ cls.out 𝒢 Δ) :
    Filter.Tendsto (fun k => v.unlabelledEvalDensity (seq.seq (sub k)) Δ)
      Filter.atTop (nhds (evalAlgOf eval v)) := by
  -- Both sides are finite sums (Finsupp.sum = Finset.sum over support).
  -- Tendsto of finite sum follows from Tendsto of each term.
  -- First, rewrite classUnlabelledDensity in terms of unlabelledDensity
  have hcls_eq : ∀ (cls : FlagClass σ) (G : Flag σ),
      classUnlabelledDensity σ G Δ cls = unlabelledDensity σ cls.out G Δ := by
    intro cls G
    unfold classUnlabelledDensity
    conv_lhs => rw [← Quotient.out_eq cls]
    simp only [Quotient.lift_mk]
  -- Show uED = sum of v(cls) * density(cls.out, G, Δ)
  have huED_eq : ∀ k, v.unlabelledEvalDensity (seq.seq (sub k)) Δ =
      ∑ cls ∈ v.support, v cls * unlabelledDensity σ cls.out (seq.seq (sub k)) Δ := by
    intro k
    simp only [FlagAlg.unlabelledEvalDensity, Finsupp.sum, hcls_eq]
  have heval_eq : evalAlgOf eval v =
      ∑ cls ∈ v.support, v cls * eval cls.out := by
    simp only [evalAlgOf, Finsupp.sum]
  rw [heval_eq]
  simp_rw [huED_eq]
  apply tendsto_finset_sum
  intro cls hcls
  exact (hconv cls.out (hv cls hcls)).const_mul _

/-- A strict monotone sequence of naturals eventually exceeds any bound. -/
theorem strictMono_nat_eventually_ge {f : ℕ → ℕ} (hf : StrictMono f) (N : ℕ) :
    ∃ k, N ≤ f k := by
  have hle : ∀ k, k ≤ f k := by
    intro k; induction k with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hf (Nat.lt_succ_of_le le_rfl)))
  exact ⟨N, hle N⟩

set_option maxHeartbeats 1600000 in
-- Tychonoff + product_limit argument for limit functional construction
/-- Limit functional construction via Tychonoff and product limit (existential version). -/
private theorem limit_functional_construction_aux (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam)
    (seq : DeltaIncreasingSeq σ Δ)
    (hlocal : ∀ k, 𝒢 (seq.seq k).forget) :
    ∃ (φ : LimitFunctional σ 𝒢 Δ), φ.seq = seq := by
  classical
  let u : ℕ → (FlagClass σ → ℝ) := fun k cls =>
    if IsLocalFlag σ cls.out 𝒢 Δ then unlabelledDensity σ cls.out (seq.seq k) Δ else 0
  have hbound_u : ∀ cls : FlagClass σ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k, u k cls ≤ C := by
    intro cls; by_cases hloc : IsLocalFlag σ cls.out 𝒢 Δ
    · obtain ⟨C, hC0, hCbound⟩ := hloc.bounded
      exact ⟨C, hC0, fun k => by
        simp only [u, if_pos hloc]
        exact (unlabelledDensity_le_localDensity σ cls.out (seq.seq k) Δ).trans
          (hCbound (seq.seq k) (hlocal k))⟩
    · exact ⟨0, le_rfl, fun k => by simp only [u, if_neg hloc]; exact le_refl 0⟩
  let B : FlagClass σ → ℝ := fun cls => (hbound_u cls).choose
  have hB_bound : ∀ cls k, u k cls ≤ B cls := fun cls => (hbound_u cls).choose_spec.2
  have hu_mem : ∀ k, u k ∈ Set.pi Set.univ (fun cls => Set.Icc 0 (B cls)) := by
    intro k cls _; refine ⟨?_, hB_bound cls k⟩
    simp only [u]; split_ifs
    · exact unlabelledDensity_nonneg σ cls.out (seq.seq k) Δ
    · exact le_refl 0
  obtain ⟨a, ha_mem, φ, hφ_mono, hφ_tend⟩ :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).tendsto_subseq hu_mem
  rw [tendsto_pi_nhds] at hφ_tend
  let eval : Flag σ → ℝ := fun F =>
    if IsLocalFlag σ F 𝒢 Δ then a (FlagClass.mk F) else 0
  have heval_local : ∀ F : Flag σ, IsLocalFlag σ F 𝒢 Δ →
      eval F = a (FlagClass.mk F) := fun F hF => by simp only [eval, if_pos hF]
  have heval_nonlocal : ∀ F : Flag σ, ¬IsLocalFlag σ F 𝒢 Δ →
      eval F = 0 := fun F hF => by simp only [eval, if_neg hF]
  have hconv_local : ∀ F : Flag σ, IsLocalFlag σ F 𝒢 Δ →
      Filter.Tendsto (fun k => unlabelledDensity σ F (seq.seq (φ k)) Δ)
        Filter.atTop (nhds (eval F)) := by
    intro F hF; rw [heval_local F hF]
    have htend_class := hφ_tend (FlagClass.mk F)
    simp only [Function.comp_def] at htend_class
    have hiso := Quotient.exact (Quotient.out_eq (FlagClass.mk F))
    simp_rw [show ∀ k, u (φ k) (FlagClass.mk F) =
        unlabelledDensity σ (FlagClass.mk F).out (seq.seq (φ k)) Δ from
      fun k => by simp only [u, if_pos (IsLocalFlag_flagIso (FlagIso.symm hiso) hF)]]
      at htend_class
    convert htend_class using 1; ext k
    exact (unlabelledDensity_flagIso hiso).symm
  have heval_type : eval σ.toFlag = 1 := by
    have htype_local : IsLocalFlag σ σ.toFlag 𝒢 Δ :=
      IsLocalFlag.intro σ σ.toFlag 𝒢 Δ
        ⟨1, le_of_lt one_pos, fun G _ => by rw [localDensity_type_eq_one']⟩
        (fun ext => absurd (Set.mem_range.mpr ⟨ext.vertex, by
          simp [FlagType.toFlag, SimpleGraph.Embedding.refl]⟩) ext.unlabelled)
    rw [heval_local σ.toFlag htype_local]
    have hout_local : IsLocalFlag σ (FlagClass.mk σ.toFlag).out 𝒢 Δ :=
      IsLocalFlag_flagIso
        (FlagIso.symm (Quotient.exact (Quotient.out_eq (FlagClass.mk σ.toFlag))))
        htype_local
    have htend := hφ_tend (FlagClass.mk σ.toFlag)
    simp only [Function.comp_def] at htend
    have hu_eq : ∀ k, u (φ k) (FlagClass.mk σ.toFlag) = 1 := fun k => by
      simp only [u, if_pos hout_local]
      rw [unlabelledDensity_flagIso
        (Quotient.exact (Quotient.out_eq (FlagClass.mk σ.toFlag)))]
      exact unlabelledDensity_type_eq_one σ (seq.seq (φ k)) Δ
    exact tendsto_nhds_unique
      (show Filter.Tendsto (fun _ => (1 : ℝ)) _ _ from
        (funext hu_eq ▸ htend)) tendsto_const_nhds
  exact ⟨⟨eval,
    fun F => by
      by_cases hF : IsLocalFlag σ F 𝒢 Δ
      · rw [heval_local F hF]; exact (ha_mem (FlagClass.mk F) (Set.mem_univ _)).1
      · rw [heval_nonlocal F hF],
    heval_type,
    fun F₁ F₂ hiso => by
      by_cases hF₁ : IsLocalFlag σ F₁ 𝒢 Δ
      · rw [heval_local F₁ hF₁, heval_local F₂ (IsLocalFlag_flagIso hiso hF₁),
          show FlagClass.mk F₁ = FlagClass.mk F₂ from (FlagClass.mk_eq F₁ F₂).mpr hiso]
      · rw [heval_nonlocal F₁ hF₁, heval_nonlocal F₂
          (fun h => hF₁ (IsLocalFlag_flagIso (FlagIso.symm hiso) h))],
    heval_nonlocal,
    fun v w hv hw => by
      have htend_vw := evalAlgOf_eq_limit σ 𝒢 Δ seq φ eval
        hconv_local heval_nonlocal (v.mul w) (mul_local_support σ v w 𝒢 Δ hv hw)
      have htend_prod := (evalAlgOf_eq_limit σ 𝒢 Δ seq φ eval
        hconv_local heval_nonlocal v hv).mul (evalAlgOf_eq_limit σ 𝒢 Δ seq φ eval
        hconv_local heval_nonlocal w hw)
      have hdiff_zero : Filter.Tendsto
          (fun k => v.unlabelledEvalDensity (seq.seq (φ k)) Δ *
                    w.unlabelledEvalDensity (seq.seq (φ k)) Δ -
                    (v.mul w).unlabelledEvalDensity (seq.seq (φ k)) Δ)
          Filter.atTop (nhds 0) := by
        rw [Metric.tendsto_atTop]; intro ε hε
        obtain ⟨Δ₀, hΔ₀⟩ := product_limit σ v w 𝒢 Δ hv hw (ε / 2) (half_pos hε)
        have hmono : StrictMono (fun k => Δ (seq.seq (φ k)).forget) :=
          seq.increasing.comp hφ_mono
        obtain ⟨N, hN⟩ := strictMono_nat_eventually_ge hmono Δ₀
        exact ⟨N, fun k hk => by
          simp only [Real.dist_eq, sub_zero]
          exact (hΔ₀ _ (hlocal (φ k)) (hN.trans (hmono.monotone hk))).trans_lt
            (half_lt_self hε)⟩
      have h := htend_prod.sub hdiff_zero; simp only [sub_zero] at h
      exact tendsto_nhds_unique htend_vw (h.congr (fun k => by ring)),
    seq, hlocal, φ, hφ_mono, hconv_local⟩, rfl⟩

/-- Limit functional construction via Tychonoff and product limit.
    Packages the sequence, subsequence, and convergence data into the
    `LimitFunctional` structure. -/
noncomputable def limit_functional_construction (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam)
    (seq : DeltaIncreasingSeq σ Δ)
    (hlocal : ∀ k, 𝒢 (seq.seq k).forget) :
    LimitFunctional σ 𝒢 Δ :=
  (limit_functional_construction_aux σ 𝒢 Δ seq hlocal).choose

/-- The constructed limit functional uses the input sequence. -/
theorem limit_functional_construction_seq (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam)
    (seq : DeltaIncreasingSeq σ Δ)
    (hlocal : ∀ k, 𝒢 (seq.seq k).forget) :
    (limit_functional_construction σ 𝒢 Δ seq hlocal).seq = seq :=
  (limit_functional_construction_aux σ 𝒢 Δ seq hlocal).choose_spec

/-- Any Δ-increasing sequence of σ-flags in 𝒢^σ gives rise to a limit
    functional φ. The functional carries its own convergent subsequence.
    (Thesis §2.2. The limit functional and common convergent subsequence are
    provided by `limit_functional_construction`.)

    **Status**: Intentional standalone — existence corollary of the
    Tychonoff construction; no consumer expected (consumers use the
    `LimitFunctional` structure directly). -/
theorem limit_functional_exists (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam)
    (seq : DeltaIncreasingSeq σ Δ)
    (hlocal : ∀ k, 𝒢 (seq.seq k).forget) :
    ∃ _ : LimitFunctional σ 𝒢 Δ, True :=
  ⟨limit_functional_construction σ 𝒢 Δ seq hlocal, trivial⟩

/-- Evaluate a limit functional on an isomorphism class via any representative.
    Well-defined by `eval_iso`. -/
noncomputable def LimitFunctional.evalClass {𝒢 : GraphClass} {Δ : GraphParam}
    (φ : LimitFunctional σ 𝒢 Δ) (cls : FlagClass σ) : ℝ :=
  φ.eval cls.out

@[simp]
theorem LimitFunctional.evalClass_mk {𝒢 : GraphClass} {Δ : GraphParam}
    (φ : LimitFunctional σ 𝒢 Δ) (F : Flag σ) :
    φ.evalClass (FlagClass.mk F) = φ.eval F := by
  simp only [evalClass]
  exact φ.eval_iso _ _ (Quotient.exact (Quotient.out_eq (FlagClass.mk F)))

/-- Linearly extend a limit functional to 𝓛^σ.
    φ(Σ cᵢ · [Fᵢ]) = Σ cᵢ · φ(Fᵢ). -/
noncomputable def LimitFunctional.evalAlg {𝒢 : GraphClass} {Δ : GraphParam}
    (φ : LimitFunctional σ 𝒢 Δ) (v : FlagAlg σ) : ℝ :=
  v.sum (fun cls c => c * φ.evalClass cls)

/-- φ on a basis element is eval. -/
theorem LimitFunctional.evalAlg_single {𝒢 : GraphClass} {Δ : GraphParam}
    (φ : LimitFunctional σ 𝒢 Δ) (F : Flag σ) :
    φ.evalAlg (FlagAlg.single σ F) = φ.eval F := by
  simp [evalAlg, FlagAlg.single, Finsupp.sum_single_index]

/-- φ is linear: scalar multiplication. -/
theorem LimitFunctional.evalAlg_smul {𝒢 : GraphClass} {Δ : GraphParam}
    (φ : LimitFunctional σ 𝒢 Δ) (c : ℝ) (v : FlagAlg σ) :
    φ.evalAlg (FlagAlg.smul c v) = c * φ.evalAlg v := by
  simp only [evalAlg, FlagAlg.smul]
  rw [Finsupp.sum_mapRange_index (by simp)]
  simp only [Finsupp.sum, mul_assoc]
  rw [← Finset.mul_sum]

/-- φ is linear: addition. -/
theorem LimitFunctional.evalAlg_add {𝒢 : GraphClass} {Δ : GraphParam}
    (φ : LimitFunctional σ 𝒢 Δ) (v w : FlagAlg σ) :
    φ.evalAlg (FlagAlg.add v w) = φ.evalAlg v + φ.evalAlg w := by
  simp only [evalAlg, FlagAlg.add]
  rw [Finsupp.sum_add_index (by simp) (by intros; ring)]

/-- `evalAlg` equals `evalAlgOf eval` (the standalone version). -/
theorem LimitFunctional.evalAlg_eq_evalAlgOf {𝒢 : GraphClass} {Δ : GraphParam}
    (φ : LimitFunctional σ 𝒢 Δ) (v : FlagAlg σ) :
    φ.evalAlg v = evalAlgOf φ.eval v := by
  simp only [evalAlg, evalAlgOf, evalClass]

/-- **Theorem 2.3 (Corollary)**: Any limit functional φ ∈ Φ^σ is an algebra
    homomorphism 𝓛^σ → ℝ. That is, φ(f · g) = φ(f) · φ(g).
    (Thesis §2.2, immediate from the `is_homomorphism` field which is proved
    at construction time using the product limit theorem.) -/
theorem limit_is_homomorphism (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam)
    (φ : LimitFunctional σ 𝒢 Δ) (v w : FlagAlg σ)
    (hv : ∀ cls ∈ v.support, IsLocalFlag σ cls.out 𝒢 Δ)
    (hw : ∀ cls ∈ w.support, IsLocalFlag σ cls.out 𝒢 Δ) :
    φ.evalAlg (v.mul w) = φ.evalAlg v * φ.evalAlg w := by
  simp only [φ.evalAlg_eq_evalAlgOf]
  exact φ.is_homomorphism v w hv hw

/-! ## §2.3: Positivity and the Semantic Cone -/

/-- An element f ∈ 𝓛^σ is **positive** (f ≥_{𝓛^σ} 0) if φ(f) ≥ 0 for all
    limit functionals φ ∈ Φ^σ. (Thesis §2.3 Definition) -/
def FlagAlg.isPositive (v : FlagAlg σ) (𝒢 : GraphClass) (Δ : GraphParam) : Prop :=
  ∀ φ : LimitFunctional σ 𝒢 Δ, 0 ≤ φ.evalAlg v

/-- The **semantic cone** C^σ_sem: the convex cone of positive elements of 𝓛^σ.
    (Thesis §2.3) -/
def SemanticCone (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam) : Set (FlagAlg σ) :=
  {v | v.isPositive 𝒢 Δ}

/-- **Squares are positive**: φ(f²) = φ(f)² ≥ 0 for all φ, when f has local support.
    (Thesis §2.3, follows from limit_is_homomorphism) -/
theorem square_in_cone (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam)
    (v : FlagAlg σ) (hv : ∀ cls ∈ v.support, IsLocalFlag σ cls.out 𝒢 Δ) :
    (v.mul v).isPositive 𝒢 Δ := by
  intro φ
  rw [limit_is_homomorphism σ 𝒢 Δ φ v v hv hv]
  exact mul_self_nonneg _

/-! ## §2.4: Averaging Operator

The averaging operator ⟦·⟧ : 𝓛^σ → 𝓛^∅ connects σ-flag densities to ∅-flag
densities. It is well-defined when σ is a local type. -/

/-- The **normalisation factor** q_σ(F): the probability that a uniformly random
    injection θ : Fin σ.size ↪ Fin F.size gives a σ-flag isomorphic to F.
    (Thesis Definition 1.19)

    Concretely: q_σ(F) = |{e : σ.graph ↪g F.graph | flagOfEmbedding F e ≅_σ F}| /
                          P(F.size, σ.size)
    where P(n,k) = Nat.descFactorial n k is the number of injections Fin k → Fin n.
    The numerator uses graph embeddings, but every compatible injection is automatically
    a graph embedding (the isomorphism condition forces adjacency preservation). -/
noncomputable def normalisationFactor (σ : FlagType) (F : Flag σ) : ℝ :=
  let compat := (Finset.univ (α := σ.graph ↪g F.graph)).filter fun e =>
    FlagIso σ (flagOfEmbedding F e) F
  (compat.card : ℝ) / (Nat.descFactorial F.size σ.size : ℝ)

/-- The normalisation factor is nonneg. -/
theorem normalisationFactor_nonneg (σ : FlagType) (F : Flag σ) :
    0 ≤ normalisationFactor σ F :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The normalisation factor is at most 1 (it's a probability).
    Proof: compat ⊆ graph embeddings ⊆ all injections, and
    |all injections| = Nat.descFactorial F.size σ.size.

    **Status**: Intentional standalone — foundational upper bound;
    no consumer expected. -/
theorem normalisationFactor_le_one (σ : FlagType) (F : Flag σ) :
    normalisationFactor σ F ≤ 1 := by
  unfold normalisationFactor
  rcases Nat.eq_zero_or_pos (Nat.descFactorial F.size σ.size) with h | h
  · simp [h]
  · rw [div_le_one (Nat.cast_pos.mpr h)]
    -- compat.card ≤ |σ.graph ↪g F.graph| ≤ descFactorial F.size σ.size
    -- Graph embeddings inject into plain injections via toFun
    have hle : Fintype.card (σ.graph ↪g F.graph) ≤ Nat.descFactorial F.size σ.size := by
      have hemb : Fintype.card (Fin σ.size ↪ Fin F.size) =
          Nat.descFactorial F.size σ.size := by
        rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
      rw [← hemb]
      exact Fintype.card_le_of_injective
        (fun (e : σ.graph ↪g F.graph) => (⟨e.toFun, e.injective⟩ : Fin σ.size ↪ Fin F.size))
        (fun e₁ e₂ h => by
          ext x
          exact congr_arg (fun f : Fin σ.size ↪ Fin F.size => (f x : ℕ)) h)
    calc ((Finset.univ.filter fun e : σ.graph ↪g F.graph =>
          FlagIso σ (flagOfEmbedding F e) F).card : ℝ)
        ≤ (Fintype.card (σ.graph ↪g F.graph) : ℝ) := by
          exact_mod_cast Finset.card_filter_le _ _
      _ ≤ (Nat.descFactorial F.size σ.size : ℝ) := by
          exact_mod_cast hle

/-- q_σ(σ) = |Aut(σ.graph)| / σ.size!: For the type σ viewed as a σ-flag,
    every embedding σ.graph ↪g σ.graph is compatible (it's a bijection on a finite
    set of the same size, so its inverse is the isomorphism witness). The denominator
    is descFactorial σ.size σ.size = σ.size!. -/
theorem normalisationFactor_type (σ : FlagType) :
    normalisationFactor σ σ.toFlag =
      (Fintype.card (σ.graph ↪g σ.graph) : ℝ) / (Nat.factorial σ.size : ℝ) := by
  -- Every embedding σ.graph ↪g σ.graph is compatible with σ.toFlag,
  -- because any such embedding is bijective (injective on finite set of same size),
  -- so its inverse is the isomorphism witness.
  have hcompat : ∀ e : σ.graph ↪g σ.toFlag.graph,
      FlagIso σ (flagOfEmbedding σ.toFlag e) σ.toFlag := by
    intro e
    have hsurj : Function.Surjective e :=
      (Finite.injective_iff_bijective.mp e.injective).2
    let φ := RelIso.ofSurjective e hsurj
    refine ⟨φ.symm, fun i => ?_⟩
    change φ.symm (e i) = σ.toFlag.embedding i
    simp [FlagType.toFlag, SimpleGraph.Embedding.refl, φ, RelIso.ofSurjective]
  unfold normalisationFactor
  -- All embeddings are compatible, so compat = univ
  have hfilt : (Finset.univ.filter fun e : σ.graph ↪g σ.toFlag.graph =>
      FlagIso σ (flagOfEmbedding σ.toFlag e) σ.toFlag) = Finset.univ :=
    Finset.filter_true_of_mem (fun e _ => hcompat e)
  simp only [hfilt, Finset.card_univ]
  -- σ.toFlag.size = σ.size definitionally, and descFactorial n n = n!
  -- σ.toFlag.graph = σ.graph definitionally
  simp only [FlagType.toFlag, Nat.descFactorial_self]

/-- The normalisation factor respects flag isomorphism. -/
theorem normalisationFactor_flagIso {σ : FlagType} {F₁ F₂ : Flag σ}
    (h : FlagIso σ F₁ F₂) : normalisationFactor σ F₁ = normalisationFactor σ F₂ := by
  obtain ⟨φ, hφ⟩ := h
  unfold normalisationFactor
  -- φ induces a bijection σ.graph ↪g F₁.graph ≃ σ.graph ↪g F₂.graph
  -- that preserves the FlagIso predicate
  let f : (σ.graph ↪g F₁.graph) → (σ.graph ↪g F₂.graph) :=
    fun e => e.trans φ.toEmbedding
  have hf_inj : Function.Injective f := fun e₁ e₂ h => by
    have eq : e₁.trans φ.toEmbedding = e₂.trans φ.toEmbedding := by simp only [f] at h; exact h
    ext x
    congr 1
    have : (e₁.trans φ.toEmbedding) x = (e₂.trans φ.toEmbedding) x := by rw [eq]
    simp only [RelEmbedding.trans_apply] at this
    exact φ.injective this
  have hf_surj : Function.Surjective f := fun e => by
    exact ⟨e.trans φ.symm.toEmbedding, by ext x; simp [f, RelEmbedding.trans]⟩
  -- f preserves the FlagIso predicate
  have hf_iso : ∀ e, FlagIso σ (flagOfEmbedding F₁ e) F₁ ↔
      FlagIso σ (flagOfEmbedding F₂ (f e)) F₂ := by
    intro e
    constructor
    · rintro ⟨ψ, hψ⟩
      -- Witness: φ ∘ ψ ∘ φ⁻¹
      refine ⟨(φ.symm.trans ψ).trans φ, fun i => ?_⟩
      change φ (ψ (φ.symm (φ (e i)))) = F₂.embedding i
      have : φ.symm (φ (e i)) = e i := by simp
      rw [this]
      have hψe : ψ (e i) = F₁.embedding i := by simpa [flagOfEmbedding] using hψ i
      rw [hψe]
      exact hφ i
    · rintro ⟨ψ', hψ'⟩
      -- Witness: φ⁻¹ ∘ ψ' ∘ φ
      refine ⟨(φ.trans ψ').trans φ.symm, fun i => ?_⟩
      change φ.symm (ψ' (φ (e i))) = F₁.embedding i
      have hψ'φe : ψ' (φ (e i)) = F₂.embedding i := hψ' i
      rw [hψ'φe]
      have : φ.symm (F₂.embedding i) = F₁.embedding i := by
        have hφi : φ (F₁.embedding i) = F₂.embedding i := hφ i
        exact (RelIso.symm_apply_eq φ).mpr hφi.symm
      exact this
  -- The bijection preserves cardinalities
  have hcompat : (Finset.univ.filter fun e => FlagIso σ (flagOfEmbedding F₁ e) F₁).card =
      (Finset.univ.filter fun e => FlagIso σ (flagOfEmbedding F₂ e) F₂).card := by
    apply Finset.card_nbij f
    · intro e he
      have ⟨_, he_iso⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf_iso e).mp he_iso⟩
    · exact fun _ _ _ _ h => hf_inj h
    · intro e he
      have ⟨_, he_iso⟩ := Finset.mem_filter.mp he
      obtain ⟨e', he'⟩ := hf_surj e
      exact ⟨e', Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf_iso e').mpr (he' ▸ he_iso)⟩, he'⟩
  -- F₁.size = F₂.size since φ is a bijection
  have hsize : F₁.size = F₂.size := by
    simpa only [Fintype.card_fin] using Fintype.card_congr φ.toEquiv
  simp only [hcompat, hsize]

/-- The **averaging operator** ⟦F⟧ = q_σ(F) · ↓F for a σ-flag F.
    Extended linearly to 𝓛^σ → 𝓛^∅.
    (Thesis Definition, §2.4) -/
noncomputable def averaging (σ : FlagType) (F : Flag σ) : FlagAlg emptyType :=
  FlagAlg.smul (normalisationFactor σ F) (FlagAlg.single emptyType F.forget)

/-- Averaging respects flag isomorphism. -/
theorem averaging_flagIso {σ : FlagType} {F₁ F₂ : Flag σ}
    (h : FlagIso σ F₁ F₂) : averaging σ F₁ = averaging σ F₂ := by
  simp only [averaging, FlagAlg.smul, FlagAlg.single,
    normalisationFactor_flagIso h, FlagClass.mk_forget_eq h]

/-- Evaluate averaging on an isomorphism class via any representative. -/
noncomputable def classAveraging (σ : FlagType) (cls : FlagClass σ) : FlagAlg emptyType :=
  averaging σ cls.out

@[simp]
theorem classAveraging_mk (σ : FlagType) (F : Flag σ) :
    classAveraging σ (FlagClass.mk F) = averaging σ F := by
  simp only [classAveraging]
  exact averaging_flagIso ((FlagClass.mk_eq _ _).mp (Quotient.out_eq (FlagClass.mk F)))

/-- Linear extension of the averaging operator to 𝓛^σ → 𝓛^∅. -/
noncomputable def averagingAlg (σ : FlagType) (v : FlagAlg σ) : FlagAlg emptyType :=
  v.sum (fun cls c => FlagAlg.smul c (classAveraging σ cls))

/-! ### Averaging identity and asymptotics (Lemma 2.7)

The thesis (Lemma 2.7, lines 634–700) proves that
  E_θ[ρ(F; (G,θ))] ~ ρ(⟦F⟧; G) / ρ(⟦σ⟧; G)  as Δ(G) → ∞.

The proof has two parts:
1. **Exact counting identity** (proved): c(↓F; G) = Σ_θ c(F; (G,θ)),
   the bijection between ∅-embeddings and (θ, σ-embedding) pairs
   (`forget_count_eq_sigma_sum`).
2. **Binomial asymptotics** (proved): C(n,k)/C(n-m,k) → 1 as n → ∞. -/

/-- **Exact averaging identity** (Thesis Lemma 2.7, lines 634–700):
    The number of ∅-embeddings of ↓F into G equals the sum over σ-embeddings θ
    of the number of σ-compatible embeddings of F into (G, θ).

    This is the injection-level counting identity underlying the thesis's
    double-counting argument. With Lean's injection-based `inducedCount`,
    the identity holds exactly at the natural number level, with no
    correction factors needed.

    The asymptotic consequence (E_θ[ρ(F;(G,θ))] ~ ρ(↓F;G)/ρ(↓σ;G)) follows
    from this + `choose_ratio_tendsto_one`. -/
theorem averaging_exact_identity (σ : FlagType) (F : Flag σ)
    (G : Flag emptyType) :
    inducedCount emptyType F.forget G =
      Finset.univ.sum (fun θ : SigmaEmbIntoGraph σ G =>
        inducedCount σ F (sigmaFlagOfEmb θ)) :=
  forget_count_eq_sigma_sum σ F G

/-- **Binomial ratio asymptotics**: C(n, k) / C(n - m, k) → 1 as n → ∞
    for fixed k, m : ℕ.
    Proof: Both C(n,k) and C(n-m,k) are asymptotic to n^k/k! by
    `isEquivalent_choose`, so their ratio tends to 1. -/
theorem choose_ratio_tendsto_one (k m : ℕ) :
    Filter.Tendsto (fun n : ℕ => (Nat.choose n k : ℝ) / (Nat.choose (n - m) k : ℝ))
      Filter.atTop (nhds 1) := by
  open Asymptotics Filter Nat in
  -- C(n, k) ~ C(n-m, k) via common asymptotic n^k / k!
  suffices h : IsEquivalent atTop
      (fun n : ℕ => (n.choose k : ℝ)) (fun n : ℕ => ((n - m).choose k : ℝ)) by
    exact (isEquivalent_iff_tendsto_one (eventually_atTop.mpr ⟨m + k, fun n hn => by
      exact_mod_cast (Nat.choose_pos (show k ≤ n - m by omega)).ne'⟩)).mp h
  have h1 := isEquivalent_choose k
  have h_sub : Tendsto (fun n : ℕ => n - m) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun _ _ h => Nat.sub_le_sub_right h m)
      (fun b => ⟨b + m, by omega⟩)
  have h2 : IsEquivalent atTop
      (fun n : ℕ => ((n - m).choose k : ℝ))
      (fun n : ℕ => ((n - m : ℕ) : ℝ) ^ k / ↑k.factorial) := by
    have := h1.comp_tendsto h_sub
    simpa only [Function.comp_def] using this
  -- (n : ℝ) ~[atTop] ((n - m : ℕ) : ℝ) via isLittleO of constant
  have h_nm : IsEquivalent atTop
      (fun n : ℕ => (n : ℝ)) (fun n : ℕ => ((n - m : ℕ) : ℝ)) := by
    rw [IsEquivalent]
    have hf : (fun n : ℕ => (n : ℝ) - ((n - m : ℕ) : ℝ)) =ᶠ[atTop]
        (fun (_ : ℕ) => (m : ℝ)) :=
      eventually_atTop.mpr ⟨m, fun n hn => by
        simp only [Nat.cast_sub hn, sub_sub_cancel]⟩
    have key : (fun (_ : ℕ) => (m : ℝ)) =o[atTop] (fun n : ℕ => ((n - m : ℕ) : ℝ)) :=
      isLittleO_const_left.mpr (.inr ((tendsto_natCast_atTop_atTop.comp h_sub).congr
        (fun n => (Real.norm_of_nonneg (Nat.cast_nonneg (n - m))).symm)))
    exact (isLittleO_congr hf EventuallyEq.rfl).mpr key
  have h3 : IsEquivalent atTop
      (fun n : ℕ => (n : ℝ) ^ k / ↑k.factorial)
      (fun n : ℕ => ((n - m : ℕ) : ℝ) ^ k / ↑k.factorial) := by
    exact (h_nm.pow k).div IsEquivalent.refl
  exact h1.trans (h3.trans h2.symm)

/-- **Lemma 2.7** (Thesis, restated): The averaging ratio equals the expected
    local density times a correction factor C(Δ,k)/C(Δ-|σ|,k) that tends to 1.
    Equivalently, ρ(⟦F⟧;G)/ρ(⟦σ⟧;G) ~ E_θ[ρ(F;(G,θ))] as Δ(G) → ∞.

    The counting identity is `averaging_exact_identity`.
    The correction factor → 1 is `choose_ratio_tendsto_one`.

    **Status**: Intentional standalone — Thesis Lemma 2.10 averaging
    limit (the per-functional version `genAveraging_eventually_neg'`
    is the actually-used variant); no consumer expected. -/
theorem averaging_limit (σ : FlagType) (F : Flag σ) (_Δ : GraphParam) :
    ∀ ε : ℝ, 0 < ε →
      ∃ Δ₀ : ℕ, ∀ n : ℕ, Δ₀ ≤ n →
        |(Nat.choose n (F.size - σ.size) : ℝ) /
         (Nat.choose (n - σ.size) (F.size - σ.size) : ℝ) - 1| ≤ ε := by
  intro ε hε
  have htend := choose_ratio_tendsto_one (F.size - σ.size) σ.size
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend ε hε
  exact ⟨N, fun n hn => by
    have := hN n hn
    rw [Real.dist_eq] at this
    exact le_of_lt this⟩

/-! ## §2.4: Positivity Preservation (Lemma 2.8)

### Orbit-stabilizer and averaging infrastructure -/

/-- An `InducedEmbedding emptyType F.forget F.forget` (self-embedding of F.graph) yields
    a graph isomorphism, since an injective self-map on a finite set is bijective. -/
private noncomputable def selfEmbToIso {σ : FlagType} {F : Flag σ}
    (α : InducedEmbedding emptyType F.forget F.forget) : F.graph ≃g F.graph :=
  let surj := (Finite.injective_iff_bijective.mp α.injective).2
  { toEquiv := Equiv.ofBijective α.toFun ⟨α.injective, surj⟩,
    map_rel_iff' := by
      intro a b
      constructor
      · intro h
        by_contra hnadj
        exact α.map_non_adj a b
          (fun hab => by subst hab; exact SimpleGraph.irrefl _ h) hnadj h
      · exact α.map_adj a b }

@[simp]
private theorem selfEmbToIso_apply {σ : FlagType} {F : Flag σ}
    (α : InducedEmbedding emptyType F.forget F.forget) (x : Fin F.size) :
    (selfEmbToIso α).toFun x = α.toFun x := rfl

/-- For a compatible embedding e (with witness φ such that φ ∘ e = F.emb),
    extract the graph isomorphism φ from the FlagIso proof. -/
private noncomputable def compatIso {σ : FlagType} {F : Flag σ}
    {e : σ.graph ↪g F.graph} (h : FlagIso σ (flagOfEmbedding F e) F) :
    F.graph ≃g F.graph :=
  Classical.choose h

private theorem compatIso_spec {σ : FlagType} {F : Flag σ}
    {e : σ.graph ↪g F.graph} (h : FlagIso σ (flagOfEmbedding F e) F)
    (i : Fin σ.size) : (compatIso h) (e i) = F.embedding i :=
  Classical.choose_spec h i

set_option maxHeartbeats 1600000 in
/-- **Orbit-stabilizer counting identity**: the number of compatible embeddings
    times the flag automorphism count equals the graph automorphism count. -/
private theorem orbit_stabilizer_card (σ : FlagType) (F : Flag σ) :
    ((Finset.univ (α := σ.graph ↪g F.graph)).filter fun e =>
        FlagIso σ (flagOfEmbedding F e) F).card *
      flagAutCount σ F = flagAutCount emptyType F.forget := by
  unfold flagAutCount inducedCount
  let compat := (Finset.univ (α := σ.graph ↪g F.graph)).filter fun e =>
    FlagIso σ (flagOfEmbedding F e) F
  change compat.card * _ = _
  rw [show compat.card = Fintype.card { e // e ∈ compat } from
    (Fintype.card_coe compat).symm, ← Fintype.card_prod]
  -- We prove |C × A| = |B| by showing the map (e,ψ) ↦ φ_e⁻¹ ∘ ψ is a bijection.
  -- We establish injectivity directly, then surjectivity by constructing preimages.
  -- Define the forward map
  let fwd : { e // e ∈ compat } × InducedEmbedding σ F F →
      InducedEmbedding emptyType F.forget F.forget :=
    fun ⟨⟨e, he⟩, ψ⟩ =>
      let φ := compatIso (Finset.mem_filter.mp he).2
      { toFun := fun x => φ.symm (ψ.toFun x),
        injective := φ.symm.injective.comp ψ.injective,
        map_adj := fun u v (hadj : F.graph.Adj u v) => by
          exact (φ.symm.map_rel_iff' (a := ψ.toFun u) (b := ψ.toFun v)).mpr
            (ψ.map_adj u v hadj),
        map_non_adj := fun u v hne (hnadj : ¬F.graph.Adj u v)
            (hadj : F.graph.Adj (φ.symm (ψ.toFun u)) (φ.symm (ψ.toFun v))) => by
          exact hnadj ((φ.symm.map_rel_iff' (a := ψ.toFun u) (b := ψ.toFun v)).mp
            hadj |> fun h => by
              by_contra hnadj'
              exact ψ.map_non_adj u v hne hnadj' h),
        compat := fun i => Fin.elim0 i }
  -- Show fwd is injective
  have fwd_inj : Function.Injective fwd := by
    intro ⟨⟨e₁, he₁⟩, ψ₁⟩ ⟨⟨e₂, he₂⟩, ψ₂⟩ hfun
    have hfun' : ∀ x, (compatIso (Finset.mem_filter.mp he₁).2).symm (ψ₁.toFun x) =
        (compatIso (Finset.mem_filter.mp he₂).2).symm (ψ₂.toFun x) :=
      fun x => congrFun (congrArg InducedEmbedding.toFun hfun) x
    have he_eq : e₁ = e₂ := by
      ext j
      have h := hfun' (F.embedding j)
      rw [ψ₁.compat j, ψ₂.compat j] at h
      -- h : φ₁.symm (F.embedding j) = φ₂.symm (F.embedding j)
      -- Need: e₁ j = e₂ j
      -- From compatIso_spec: φ₁(e₁ j) = F.embedding j, so e₁ j = φ₁⁻¹(F.embedding j)
      have h₁ : e₁ j = (compatIso (Finset.mem_filter.mp he₁).2).symm (F.embedding j) :=
        ((compatIso _).symm_apply_eq.mpr (compatIso_spec _ j).symm).symm
      have h₂ : e₂ j = (compatIso (Finset.mem_filter.mp he₂).2).symm (F.embedding j) :=
        ((compatIso _).symm_apply_eq.mpr (compatIso_spec _ j).symm).symm
      rw [h₁, h₂, h]
    have hsub : (⟨e₁, he₁⟩ : { e // e ∈ compat }) = ⟨e₂, he₂⟩ := Subtype.ext he_eq
    refine Prod.ext hsub ?_
    have hφeq : compatIso (Finset.mem_filter.mp he₁).2 =
        compatIso (Finset.mem_filter.mp he₂).2 := by
      subst he_eq; rfl
    cases ψ₁; cases ψ₂
    simp only [InducedEmbedding.mk.injEq]
    funext x
    exact (compatIso _).symm.injective (hφeq ▸ hfun' x)
  -- Show fwd is surjective
  have fwd_surj : Function.Surjective fwd := by
    intro α
    -- Preimage: e₀ = α ∘ F.emb, ψ₀ = compatIso(e₀) ∘ α
    let αIso := selfEmbToIso α
    let e₀ : σ.graph ↪g F.graph := αIso.toEmbedding.comp F.embedding
    have he₀ : FlagIso σ (flagOfEmbedding F e₀) F :=
      ⟨αIso.symm, fun i => by
        change αIso.symm (αIso (F.embedding i)) = F.embedding i; simp⟩
    let he₀_mem : e₀ ∈ compat := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he₀⟩
    let φ₀ := compatIso (Finset.mem_filter.mp he₀_mem).2
    -- φ₀ has the spec: φ₀(e₀ i) = F.embedding i
    let ψ₀ : InducedEmbedding σ F F :=
      { toFun := fun x => φ₀ (α.toFun x),
        injective := φ₀.injective.comp α.injective,
        map_adj := fun u v (hadj : F.graph.Adj u v) => by
          have h1 : F.graph.Adj (α.toFun u) (α.toFun v) := α.map_adj u v hadj
          exact φ₀.map_rel_iff'.mpr h1,
        map_non_adj := fun u v hne (hnadj : ¬F.graph.Adj u v)
            (hadj : F.graph.Adj (φ₀ (α.toFun u)) (φ₀ (α.toFun v))) => by
          have h1 : F.graph.Adj (α.toFun u) (α.toFun v) := φ₀.map_rel_iff'.mp hadj
          exact hnadj (by
            by_contra hnadj'
            exact α.map_non_adj u v hne hnadj' h1),
        compat := fun i => compatIso_spec (Finset.mem_filter.mp he₀_mem).2 i }
    refine ⟨(⟨e₀, he₀_mem⟩, ψ₀), ?_⟩
    -- fwd(e₀, ψ₀).toFun = α.toFun, which determines InducedEmbedding equality
    have hfun : (fwd (⟨e₀, he₀_mem⟩, ψ₀)).toFun = α.toFun := by
      funext x
      change (compatIso (Finset.mem_filter.mp he₀_mem).2).symm (φ₀ (α.toFun x)) = α.toFun x
      exact φ₀.symm_apply_apply (α.toFun x)
    -- InducedEmbedding is injected by toFun
    exact (show Function.Injective (fun (e : InducedEmbedding emptyType F.forget F.forget) =>
        e.toFun) from fun a b h => by cases a; cases b; subst h; rfl) hfun
  -- Bijection from injectivity + surjectivity on finite types
  exact Fintype.card_congr
    (Equiv.ofBijective fwd ⟨fwd_inj, fwd_surj⟩)

/-- **Orbit-stabilizer for normalisationFactor**: expresses normalisationFactor
    in terms of flagAutCount via the orbit-stabilizer theorem. -/
private theorem normalisationFactor_eq_aut_ratio (σ : FlagType) (F : Flag σ) :
    normalisationFactor σ F =
      (flagAutCount emptyType F.forget : ℝ) /
        ((flagAutCount σ F : ℝ) * (Nat.descFactorial F.size σ.size : ℝ)) := by
  unfold normalisationFactor
  -- orbit_stabilizer_card gives: compat.card * flagAutCount σ F = flagAutCount ∅ F.forget
  have hos := orbit_stabilizer_card σ F
  have haut_pos : (0 : ℝ) < (flagAutCount σ F : ℝ) :=
    Nat.cast_pos.mpr (flagAutCount_pos σ F)
  -- Goal: compat.card / descFact = Aut_∅ / (Aut_σ * descFact)
  -- Since Aut_∅ = compat.card * Aut_σ, RHS = compat.card * Aut_σ / (Aut_σ * descFact) = compat.card / descFact
  have : (flagAutCount emptyType F.forget : ℝ) =
      ((Finset.univ.filter fun e : σ.graph ↪g F.graph =>
        FlagIso σ (flagOfEmbedding F e) F).card : ℝ) * (flagAutCount σ F : ℝ) := by
    exact_mod_cast hos.symm
  rw [this]
  rw [mul_comm ((Finset.univ.filter _).card : ℝ), mul_div_mul_left _ _ (ne_of_gt haut_pos)]

/-- `(sigmaFlagOfEmb θ).forget = G.forget`. -/
private theorem sigmaFlagOfEmb_forget_eq {σ : FlagType} {G : Flag emptyType}
    (θ : SigmaEmbIntoGraph σ G) :
    (sigmaFlagOfEmb θ).forget = G.forget := rfl

/-- `inducedCount ∅ σ.toFlag.forget G = Fintype.card (SigmaEmbIntoGraph σ G)`. -/
private theorem inducedCount_forget_type_eq_sigma (σ : FlagType) (G : Flag emptyType) :
    inducedCount emptyType σ.toFlag.forget G =
      Fintype.card (SigmaEmbIntoGraph σ G) := by
  -- Both count induced embeddings of σ.graph into G.graph.
  -- σ.toFlag.forget has graph = σ.graph, size = σ.size (all definitional)
  -- So InducedEmbedding emptyType σ.toFlag.forget G ≅ SigmaEmbIntoGraph σ G
  unfold inducedCount
  apply Fintype.card_congr
  exact {
    toFun := fun e =>
      { emb := ⟨⟨e.toFun, e.injective⟩, fun {a b} =>
          ⟨fun h => by
            by_contra hnadj
            exact e.map_non_adj a b
              (fun hab => by subst hab; exact SimpleGraph.irrefl _ h) hnadj h,
           e.map_adj a b⟩⟩,
        hsize := by
          have := Fintype.card_le_of_injective e.toFun e.injective
          simp only [Fintype.card_fin] at this; exact this }
    invFun := fun θ =>
      { toFun := θ.emb,
        injective := θ.emb.injective,
        map_adj := fun u v h => (θ.emb.map_rel_iff'.mpr h : _),
        map_non_adj := fun u v _ hnadj h => hnadj (θ.emb.map_rel_iff'.mp h : _),
        compat := fun i => Fin.elim0 i }
    left_inv := fun e => by cases e; rfl
    right_inv := fun θ => by
      cases θ; simp only [SigmaEmbIntoGraph.mk.injEq]; ext x; rfl
  }

/-- `flagAutCount ∅ σ.toFlag.forget = Fintype.card (σ.graph ↪g σ.graph)`. -/
private theorem flagAutCount_forget_type_eq (σ : FlagType) :
    flagAutCount emptyType σ.toFlag.forget =
      Fintype.card (σ.graph ↪g σ.graph) := by
  -- Both count self-embeddings of σ.graph (with trivial labelling).
  unfold flagAutCount inducedCount
  apply Fintype.card_congr
  exact {
    toFun := fun e => ⟨⟨e.toFun, e.injective⟩, fun {a b} =>
      ⟨fun h => by
        by_contra hnadj
        exact e.map_non_adj a b
          (fun hab => by subst hab; exact SimpleGraph.irrefl _ h) hnadj h,
       e.map_adj a b⟩⟩
    invFun := fun emb => ⟨emb, emb.injective,
      fun u v h => (emb.map_rel_iff'.mpr h : _),
      fun u v _ hnadj h => hnadj (emb.map_rel_iff'.mp h : _),
      fun i => Fin.elim0 i⟩
    left_inv := fun e => by cases e; rfl
    right_inv := fun emb => by ext x; rfl
  }


/-- **Averaging density identity** (Thesis Lemma 2.7, algebraic part):
    For any σ-flag F and graph G, the normalised ∅-level density of ↓F equals
    the normalised ∅-level density of ↓σ times the average σ-level density of F
    times a binomial correction C(Δ,f)/C(Δ-s,f) that tends to 1.

    Concretely:
      q(F) · uD(∅, ↓F, G, Δ) =
        q(σ) · uD(∅, ↓σ, G, Δ) · E_θ[uD(σ,F,(G,θ),Δ)] · C(Δ,f)/C(Δ-s,f)

    This follows from:
    1. `averaging_exact_identity`: IC(∅,↓F,G) = Σ_θ IC(σ,F,(G,θ))
    2. Vandermonde: C(n,s)·C(n-s,f) = C(n,f+s)·C(f+s,s) (`Nat.choose_mul`)
    3. s!·C(k,s) = descFactorial(k,s) (`Nat.descFactorial_eq_factorial_mul_choose`)

    Both sides equal IC(∅,↓F,G) / (Aut_σ(F)·s!·C(Δ,s)·C(Δ-s,f)) after
    substitution and simplification. -/
theorem averaging_density_identity (σ : FlagType) (F : Flag σ)
    (G : Flag emptyType) (Δ : GraphParam) :
    normalisationFactor σ F * unlabelledDensity emptyType F.forget G Δ =
      normalisationFactor σ σ.toFlag *
        unlabelledDensity emptyType σ.toFlag.forget G Δ *
        ((∑ θ : SigmaEmbIntoGraph σ G,
            unlabelledDensity σ F (sigmaFlagOfEmb θ) Δ) /
          (Fintype.card (SigmaEmbIntoGraph σ G) : ℝ)) *
        ((Nat.choose (Δ G.forget) (F.size - σ.size) : ℝ) /
          (Nat.choose (Δ G.forget - σ.size) (F.size - σ.size) : ℝ)) := by
  set s := σ.size
  set f := F.size - σ.size
  set n := Δ G.forget
  set IC := (inducedCount emptyType F.forget G : ℝ)
  set Aσ := (flagAutCount σ F : ℝ)
  set Ae := (flagAutCount emptyType F.forget : ℝ)
  set Aes := (flagAutCount emptyType σ.toFlag.forget : ℝ)
  set Θ := (Fintype.card (SigmaEmbIntoGraph σ G) : ℝ)
  rw [normalisationFactor_eq_aut_ratio σ F, normalisationFactor_type σ]
  unfold unlabelledDensity localDensity
  rw [inducedCount_forget_type_eq_sigma σ G, flagAutCount_forget_type_eq σ]
  have hsum : (∑ θ : SigmaEmbIntoGraph σ G,
      (inducedCount σ F (sigmaFlagOfEmb θ) : ℝ) /
        (Nat.choose (Δ (sigmaFlagOfEmb θ).forget) (F.size - σ.size) : ℝ) /
        (flagAutCount σ F : ℝ)) =
      (∑ θ : SigmaEmbIntoGraph σ G, (inducedCount σ F (sigmaFlagOfEmb θ) : ℝ)) /
        ((Nat.choose n f : ℝ) * Aσ) := by
    rw [Finset.sum_div]; congr 1; ext θ; rw [sigmaFlagOfEmb_forget_eq]; ring
  have havg := averaging_exact_identity σ F G
  rw [show σ.toFlag.forget.size - emptyType.size = s from by
      simp only [Flag.forget, FlagType.toFlag, emptyType]; rfl,
    show F.forget.size - emptyType.size = F.size from by
      simp only [Flag.forget, emptyType]; rfl,
    hsum,
    show (∑ θ : SigmaEmbIntoGraph σ G,
        (inducedCount σ F (sigmaFlagOfEmb θ) : ℝ)) = IC from by
      rw [← Nat.cast_sum]; exact congrArg Nat.cast havg.symm]
  have hdesc : (Nat.descFactorial F.size s : ℝ) =
      (s.factorial : ℝ) * (Nat.choose F.size s : ℝ) :=
    mod_cast Nat.descFactorial_eq_factorial_mul_choose F.size s
  have hvand : (Nat.choose n F.size : ℝ) * (Nat.choose F.size s : ℝ) =
      (Nat.choose n s : ℝ) * (Nat.choose (n - s) f : ℝ) :=
    mod_cast Nat.choose_mul F.hsize
  have hAσ_pos : (0 : ℝ) < Aσ := Nat.cast_pos.mpr (flagAutCount_pos σ F)
  have hAe_pos : (0 : ℝ) < Ae := Nat.cast_pos.mpr (flagAutCount_pos emptyType F.forget)
  have hAes_pos : (0 : ℝ) < Aes :=
    Nat.cast_pos.mpr (flagAutCount_pos emptyType σ.toFlag.forget)
  rw [show (Fintype.card (σ.graph ↪g σ.graph) : ℝ) = Aes from
    congrArg Nat.cast (flagAutCount_forget_type_eq σ).symm]
  -- Both sides equal IC / (Aσ * s! * C(n,s) * C(n-s,f)); prove via algebraic lemma.
  suffices algebraic_identity :
      ∀ (ae aσ aes ic θ desc sf cnF cns cnf cnsf cFs : ℝ),
      0 < ae → 0 < aσ → 0 < aes →
      desc = sf * cFs →
      cnF * cFs = cns * cnsf →
      (cnf = 0 → cnF = 0) →
      (θ = 0 → ic = 0) →
      ae / (aσ * desc) * (ic / cnF / ae) =
        aes / sf * (θ / cns / aes) * (ic / (cnf * aσ) / θ) * (cnf / cnsf) by
    apply algebraic_identity
    · exact hAe_pos
    · exact hAσ_pos
    · exact hAes_pos
    · exact hdesc
    · exact hvand
    · intro hcnf
      have hlt := Nat.choose_eq_zero_iff.mp (Nat.cast_eq_zero.mp hcnf)
      exact Nat.cast_eq_zero.mpr
        (Nat.choose_eq_zero_iff.mpr (lt_of_lt_of_le hlt (Nat.sub_le F.size s)))
    · intro hθ
      have hcard := Fintype.card_eq_zero_iff.mp (Nat.cast_eq_zero.mp hθ)
      exact Nat.cast_eq_zero.mpr
        (havg ▸ Finset.sum_eq_zero (fun θ _ => IsEmpty.elim hcard θ))
  intro ae aσ aes ic θ desc sf cnF cns cnf cnsf cFs hae haσ haes hdesc' hvand' hcnf_imp hθ_imp
  subst hdesc'
  by_cases hcFs : cFs = 0
  · simp only [hcFs, mul_zero] at hvand' ⊢
    rcases mul_eq_zero.mp hvand'.symm with hcns | hcnsf
    · simp [hcns]
    · simp [hcnsf]
  · by_cases hsf : sf = 0
    · simp [hsf]
    · by_cases hcnF : cnF = 0
      · have : cns * cnsf = 0 := by rw [← hvand']; simp [hcnF]
        rcases mul_eq_zero.mp this with hcns | hcnsf <;> simp [*]
      · by_cases hcns : cns = 0
        · exact absurd ((mul_eq_zero.mp (hvand' ▸ mul_eq_zero_of_left hcns _)).resolve_left hcnF) hcFs
        · by_cases hcnsf : cnsf = 0
          · exact absurd ((mul_eq_zero.mp (hvand' ▸ mul_eq_zero_of_right _ hcnsf)).resolve_left hcnF) hcFs
          · by_cases hcnf : cnf = 0
            · simp [hcnf, hcnf_imp hcnf]
            · by_cases hθ : θ = 0
              · simp [hθ, hθ_imp hθ]
              · field_simp [ne_of_gt hae, ne_of_gt haσ, ne_of_gt haes,
                  hsf, hcFs, hcnF, hcns, hcnsf, hcnf, hθ]
                linear_combination -ic * hvand'

/-- **Density-level averaging** (Thesis Lemma 2.7 + Lemma 2.8 consequence):
    If ψ.evalAlg(averagingAlg σ v) < 0, then for large k along ψ's subsequence,
    the average of v.uED over σ-embeddings into G_k is negative.

    **Proof sketch:** By `averaging_density_identity`, for each cls in v.support:
      `q(cls) · uD(∅,↓cls,G_k) = q(σ) · uD(∅,↓σ,G_k) · E_θ[uD(σ,cls,(G_k,θ))] · corr(cls,k)`
    where `corr(cls,k) = C(Δ_k,f)/C(Δ_k-s,f) → 1` by `choose_ratio_tendsto_one`.
    Summing: `(averagingAlg σ v).uED(G_k) = q(σ)·uD(∅,↓σ,G_k)·(E_θ[v.uED_σ]+error)`.
    Since the LHS → L < 0, and `q(σ)·uD(∅,↓σ)` is bounded/non-negative (eventually > 0),
    the σ-level average `E_θ[v.uED_σ]` is eventually ≤ L/(2Q) < 0 where
    Q = q(σ)·ψ.eval(↓σ) > 0.

    **Status: partially proved.** Two remaining sorries:
    1. Counting squeeze: `normFactor(F) · ψ.eval(↓F) = 0` when `ψ.eval(↓σ) = 0`
       (via `averaging_exact_identity` + `IsBoundedDensity` + squeeze theorem, ~60 lines).
    2. Main convergence: `E_θ ≤ L/(2Q)` eventually
       (via `averaging_density_identity` + `choose_ratio_tendsto_one`, ~100 lines). -/
private theorem averaging_eventually_neg (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam)
    (hσ : IsLocalType σ 𝒢 Δ)
    (v : FlagAlg σ) (hv_local : ∀ cls ∈ v.support, IsLocalFlag σ cls.out 𝒢 Δ)
    (ψ : LimitFunctional emptyType 𝒢 Δ)
    (hψ : ψ.evalAlg (averagingAlg σ v) < 0) :
    -- For large k, E_θ[v.uED(G_k,θ)] < 0, and bounded away from 0:
    ∃ (c : ℝ) (_ : c < 0) (N₀ : ℕ), ∀ k, N₀ ≤ k →
      (∑ θ : SigmaEmbIntoGraph σ (ψ.seq.seq (ψ.sub k)),
          v.unlabelledEvalDensity (sigmaFlagOfEmb θ) Δ) /
        (Fintype.card (SigmaEmbIntoGraph σ (ψ.seq.seq (ψ.sub k))) : ℝ) ≤ c := by
  let G : ℕ → Flag emptyType := fun k => ψ.seq.seq (ψ.sub k)
  set L := ψ.evalAlg (averagingAlg σ v) with hL_def
  have hforget_local : ∀ cls ∈ v.support, IsLocalFlag emptyType cls.out.forget 𝒢 Δ :=
    fun cls hcls => hσ cls.out (hv_local cls hcls)
  have hσ_forget_local : IsLocalFlag emptyType σ.toFlag.forget 𝒢 Δ :=
    hσ σ.toFlag (type_is_local σ 𝒢 Δ)
  set Qlim := normalisationFactor σ σ.toFlag * ψ.eval σ.toFlag.forget with hQlim_def
  have hQlim_nonneg : 0 ≤ Qlim :=
    mul_nonneg (normalisationFactor_nonneg σ σ.toFlag) (ψ.nonneg_on_flags σ.toFlag.forget)
  -- evalAlg distributes over Finset.sum
  have evalAlg_sum : ∀ (S : Finset (FlagClass σ)) (f : FlagClass σ → FlagAlg emptyType),
      ψ.evalAlg (∑ x ∈ S, f x) = ∑ x ∈ S, ψ.evalAlg (f x) := by
    intro S f; induction S using Finset.induction with
    | empty => simp [Finset.sum_empty, LimitFunctional.evalAlg, Finsupp.sum_zero_index]
    | insert _ _ hna ih =>
      simp only [Finset.sum_insert hna]; change ψ.evalAlg (FlagAlg.add _ _) = _
      rw [ψ.evalAlg_add, ih]
  have hnf_σ_pos : 0 < normalisationFactor σ σ.toFlag := by
    rw [normalisationFactor_type σ]
    exact div_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr (Nat.factorial_pos _))
  -- Qlim > 0 (otherwise L = 0, contradicting hψ)
  have hQlim_pos : 0 < Qlim := by
    by_contra h; push_neg at h
    have hQlim_zero : Qlim = 0 := le_antisymm h hQlim_nonneg
    have heval_σ_zero : ψ.eval σ.toFlag.forget = 0 :=
      (mul_eq_zero.mp (hQlim_def ▸ hQlim_zero)).resolve_left (ne_of_gt hnf_σ_pos)
    -- Squeeze: normFactor(F) · uD(∅,↓F,G_k) = Q_k · avg · corr → 0 since Q_k → 0
    have heval_forget_zero : ∀ cls ∈ v.support,
        normalisationFactor σ cls.out * ψ.eval cls.out.forget = 0 := by
      intro cls hcls
      have hid := fun k => averaging_density_identity σ cls.out (G k) Δ
      have htend_lhs : Filter.Tendsto
          (fun k => normalisationFactor σ cls.out *
            unlabelledDensity emptyType cls.out.forget (G k) Δ)
          Filter.atTop (nhds (normalisationFactor σ cls.out * ψ.eval cls.out.forget)) :=
        (ψ.convergence cls.out.forget (hforget_local cls hcls)).const_mul _
      have htend_σ : Filter.Tendsto
          (fun k => unlabelledDensity emptyType σ.toFlag.forget (G k) Δ)
          Filter.atTop (nhds 0) := by
        rw [← heval_σ_zero]; exact ψ.convergence σ.toFlag.forget hσ_forget_local
      obtain ⟨C_F, hC_F_nonneg, hC_F_bound⟩ := (hv_local cls hcls).bounded
      have havg_le : ∀ k, (∑ θ : SigmaEmbIntoGraph σ (G k),
          unlabelledDensity σ cls.out (sigmaFlagOfEmb θ) Δ) /
          (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ) ≤ C_F := by
        intro k
        by_cases hΘ : (Fintype.card (SigmaEmbIntoGraph σ (G k))) = 0
        · simp [hΘ]; exact hC_F_nonneg
        · have hΘ_pos : (0 : ℝ) < (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ) :=
            Nat.cast_pos.mpr (Nat.pos_of_ne_zero hΘ)
          rw [div_le_iff₀ hΘ_pos]
          calc ∑ θ : SigmaEmbIntoGraph σ (G k),
                unlabelledDensity σ cls.out (sigmaFlagOfEmb θ) Δ
              ≤ ∑ _ : SigmaEmbIntoGraph σ (G k), C_F := by
                apply Finset.sum_le_sum; intro θ _
                exact le_trans (unlabelledDensity_le_localDensity σ cls.out
                  (sigmaFlagOfEmb θ) Δ) (hC_F_bound (sigmaFlagOfEmb θ) (ψ.seq_in_class (ψ.sub k)))
            _ = C_F * (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ) := by
                simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
      set f_size := cls.out.size - σ.size
      have htend_corr : Filter.Tendsto
          (fun k => (Nat.choose (Δ (G k).forget) f_size : ℝ) /
            (Nat.choose (Δ (G k).forget - σ.size) f_size : ℝ))
          Filter.atTop (nhds 1) :=
        (choose_ratio_tendsto_one f_size σ.size).comp
          (ψ.seq.increasing.comp ψ.sub_strictMono).tendsto_atTop
      -- Squeeze: f(k) ≤ normFactor(σ) * uD_σ(k) * C_F * corr(k) → 0
      have hle : ∀ k, normalisationFactor σ cls.out *
          unlabelledDensity emptyType cls.out.forget (G k) Δ ≤
          normalisationFactor σ σ.toFlag *
          unlabelledDensity emptyType σ.toFlag.forget (G k) Δ *
          C_F *
          ((Nat.choose (Δ (G k).forget) f_size : ℝ) /
            (Nat.choose (Δ (G k).forget - σ.size) f_size : ℝ)) := by
        intro k
        rw [hid k]
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left (havg_le k)
          exact mul_nonneg (normalisationFactor_nonneg σ σ.toFlag)
            (unlabelledDensity_nonneg emptyType σ.toFlag.forget (G k) Δ)
        · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have htend_g : Filter.Tendsto
          (fun k => normalisationFactor σ σ.toFlag *
            unlabelledDensity emptyType σ.toFlag.forget (G k) Δ *
            C_F *
            ((Nat.choose (Δ (G k).forget) f_size : ℝ) /
              (Nat.choose (Δ (G k).forget - σ.size) f_size : ℝ)))
          Filter.atTop (nhds 0) := by
        rw [show (0 : ℝ) = normalisationFactor σ σ.toFlag * 0 * C_F * 1 from by ring]
        exact ((htend_σ.const_mul _).mul tendsto_const_nhds).mul htend_corr
      exact tendsto_nhds_unique htend_lhs
        (squeeze_zero (fun k => mul_nonneg (normalisationFactor_nonneg σ cls.out)
          (unlabelledDensity_nonneg emptyType cls.out.forget (G k) Δ)) hle htend_g)
    -- L = Σ v(cls) · normFactor · ψ.eval(↓F) = Σ v(cls) · 0 = 0, contradicting hψ
    linarith [show L = 0 from by
      rw [hL_def]; show ψ.evalAlg (averagingAlg σ v) = 0
      simp only [averagingAlg, Finsupp.sum]; rw [evalAlg_sum]
      exact Finset.sum_eq_zero fun cls hcls => by
        rw [ψ.evalAlg_smul]; simp only [classAveraging, averaging]
        rw [ψ.evalAlg_smul, ψ.evalAlg_single, heval_forget_zero cls hcls, mul_zero]]
  refine ⟨L / (2 * Qlim), div_neg_of_neg_of_pos hψ (mul_pos two_pos hQlim_pos), ?_⟩
  -- Main convergence: show E_θ[v.uED] → L/Qlim < L/(2·Qlim) eventually
  have htend_Q : Filter.Tendsto
      (fun k => normalisationFactor σ σ.toFlag *
        unlabelledDensity emptyType σ.toFlag.forget (G k) Δ)
      Filter.atTop (nhds Qlim) :=
    (ψ.convergence σ.toFlag.forget hσ_forget_local).const_mul _
  -- S_k = Σ v(cls) * normFactor * uD_forget → L
  have htend_S_L : Filter.Tendsto
      (fun k => ∑ cls ∈ v.support, v cls * (normalisationFactor σ cls.out *
        unlabelledDensity emptyType cls.out.forget (G k) Δ))
      Filter.atTop (nhds L) := by
    have hS_limit_eq_L :
        ∑ cls ∈ v.support, v cls *
          (normalisationFactor σ cls.out * ψ.eval cls.out.forget) = L := by
      rw [hL_def]; simp only [averagingAlg, Finsupp.sum]; rw [evalAlg_sum]
      congr 1; ext cls; rw [ψ.evalAlg_smul]; congr 1
      simp only [classAveraging, averaging]; rw [ψ.evalAlg_smul, ψ.evalAlg_single]
    rw [← hS_limit_eq_L]
    exact tendsto_finset_sum _ fun cls hcls =>
      ((ψ.convergence cls.out.forget (hforget_local cls hcls)).const_mul _).const_mul _
  -- Summed averaging identity at each k
  have hid_sum : ∀ k,
      ∑ cls ∈ v.support, v cls * (normalisationFactor σ cls.out *
        unlabelledDensity emptyType cls.out.forget (G k) Δ) =
      (normalisationFactor σ σ.toFlag *
        unlabelledDensity emptyType σ.toFlag.forget (G k) Δ) *
      ∑ cls ∈ v.support, v cls *
        ((∑ θ : SigmaEmbIntoGraph σ (G k),
            unlabelledDensity σ cls.out (sigmaFlagOfEmb θ) Δ) /
          (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ)) *
        ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ)) := by
    intro k; rw [Finset.mul_sum]; congr 1; ext cls
    rw [averaging_density_identity σ cls.out (G k) Δ]; ring
  have huED_expand : ∀ k,
      ∑ θ : SigmaEmbIntoGraph σ (G k),
        v.unlabelledEvalDensity (sigmaFlagOfEmb θ) Δ =
      ∑ cls ∈ v.support, v cls * ∑ θ : SigmaEmbIntoGraph σ (G k),
        unlabelledDensity σ cls.out (sigmaFlagOfEmb θ) Δ := by
    intro k
    have hcuD : ∀ (cls : FlagClass σ) (G' : Flag σ),
        classUnlabelledDensity σ G' Δ cls = unlabelledDensity σ cls.out G' Δ := by
      intro cls G'; unfold classUnlabelledDensity
      conv_lhs => rw [← Quotient.out_eq cls]
      exact Quotient.lift_mk _ _ _
    simp only [FlagAlg.unlabelledEvalDensity, Finsupp.sum, hcuD]
    rw [Finset.sum_comm]
    congr 1; ext cls; rw [Finset.mul_sum]
  have hEθ_eq : ∀ k,
      (∑ θ : SigmaEmbIntoGraph σ (G k),
        v.unlabelledEvalDensity (sigmaFlagOfEmb θ) Δ) /
        (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ) =
      ∑ cls ∈ v.support, v cls *
        ((∑ θ : SigmaEmbIntoGraph σ (G k),
            unlabelledDensity σ cls.out (sigmaFlagOfEmb θ) Δ) /
          (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ)) := by
    intro k; rw [huED_expand k, Finset.sum_div]
    congr 1; ext cls; ring
  have htend_Δ : Filter.Tendsto (fun k => Δ (G k).forget) Filter.atTop Filter.atTop :=
    (ψ.seq.increasing.comp ψ.sub_strictMono).tendsto_atTop
  have htend_corr_cls : ∀ cls ∈ v.support, Filter.Tendsto
      (fun k => (Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
        (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ))
      Filter.atTop (nhds 1) :=
    fun cls _ => (choose_ratio_tendsto_one (cls.out.size - σ.size) σ.size).comp htend_Δ
  have havg_bound : ∀ cls ∈ v.support, ∃ C_cls : ℝ, ∀ k,
      ‖v cls *
        ((∑ θ : SigmaEmbIntoGraph σ (G k),
            unlabelledDensity σ cls.out (sigmaFlagOfEmb θ) Δ) /
          (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ))‖ ≤ C_cls := by
    intro cls hcls
    obtain ⟨C_F, hC_F_nonneg, hC_F_bound⟩ := (hv_local cls hcls).bounded
    refine ⟨|v cls| * C_F, fun k => ?_⟩
    rw [Real.norm_eq_abs, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [abs_of_nonneg (div_nonneg (Finset.sum_nonneg (fun θ _ =>
        unlabelledDensity_nonneg σ cls.out (sigmaFlagOfEmb θ) Δ)) (Nat.cast_nonneg _))]
    by_cases hΘ : (Fintype.card (SigmaEmbIntoGraph σ (G k))) = 0
    · simp [hΘ]; exact hC_F_nonneg
    · have hΘ_pos : (0 : ℝ) < ↑(Fintype.card (SigmaEmbIntoGraph σ (G k))) :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero hΘ)
      rw [div_le_iff₀ hΘ_pos]
      calc ∑ θ : SigmaEmbIntoGraph σ (G k),
              unlabelledDensity σ cls.out (sigmaFlagOfEmb θ) Δ
            ≤ ∑ _ : SigmaEmbIntoGraph σ (G k), C_F := by
              apply Finset.sum_le_sum; intro θ _
              exact le_trans (unlabelledDensity_le_localDensity σ cls.out
                (sigmaFlagOfEmb θ) Δ) (hC_F_bound (sigmaFlagOfEmb θ) (ψ.seq_in_class (ψ.sub k)))
          _ = C_F * ↑(Fintype.card (SigmaEmbIntoGraph σ (G k))) := by
              simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  -- Each diff term v(cls) * avg * (corr - 1) → 0
  have hdiff_term_tendsto : ∀ cls ∈ v.support, Filter.Tendsto
      (fun k => v cls *
        ((∑ θ : SigmaEmbIntoGraph σ (G k),
            unlabelledDensity σ cls.out (sigmaFlagOfEmb θ) Δ) /
          (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ)) *
        ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1))
      Filter.atTop (nhds 0) := by
    intro cls hcls
    obtain ⟨C_cls, hC_cls⟩ := havg_bound cls hcls
    have hcorr_sub : Filter.Tendsto
        (fun k => (Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1)
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ) = 1 - 1 from by ring]
      exact (htend_corr_cls cls hcls).sub tendsto_const_nhds
    apply squeeze_zero_norm'
      (Filter.Eventually.of_forall (fun (k : ℕ) => show
        ‖v cls *
          ((∑ θ : SigmaEmbIntoGraph σ (G k),
              unlabelledDensity σ cls.out (sigmaFlagOfEmb θ) Δ) /
            (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ)) *
          ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
            (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1)‖ ≤
        C_cls * ‖(Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
            (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1‖ from by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC_cls k) (norm_nonneg _)))
    rw [show (0:ℝ) = C_cls * 0 from by ring]
    have htend_norm : Filter.Tendsto
        (fun k => ‖(Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
            (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1‖)
        Filter.atTop (nhds (0 : ℝ)) := by
      rw [show (0 : ℝ) = ‖(0 : ℝ)‖ from by simp]; exact hcorr_sub.norm
    exact htend_norm.const_mul _
  have hdiff_sum_tendsto : Filter.Tendsto
      (fun k => ∑ cls ∈ v.support, v cls *
        ((∑ θ : SigmaEmbIntoGraph σ (G k),
            unlabelledDensity σ cls.out (sigmaFlagOfEmb θ) Δ) /
          (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ)) *
        ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1))
      Filter.atTop (nhds 0) := by
    rw [show (0 : ℝ) = ∑ _ ∈ v.support, (0 : ℝ) from by simp]
    exact tendsto_finset_sum _ hdiff_term_tendsto
  have hsum_split : ∀ k,
      ∑ cls ∈ v.support, v cls *
        ((∑ θ : SigmaEmbIntoGraph σ (G k),
            unlabelledDensity σ cls.out (sigmaFlagOfEmb θ) Δ) /
          (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ)) *
        ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ)) =
      (∑ θ : SigmaEmbIntoGraph σ (G k),
          v.unlabelledEvalDensity (sigmaFlagOfEmb θ) Δ) /
        (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ) +
      ∑ cls ∈ v.support, v cls *
        ((∑ θ : SigmaEmbIntoGraph σ (G k),
            unlabelledDensity σ cls.out (sigmaFlagOfEmb θ) Δ) /
          (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ)) *
        ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1) := by
    intro k; rw [hEθ_eq k, ← Finset.sum_add_distrib]; congr 1; ext cls; ring
  -- E_θ = S_k/Q_k - diff eventually (when Q_k > 0)
  have hEθ_eventually : ∀ᶠ k in Filter.atTop,
      (∑ θ : SigmaEmbIntoGraph σ (G k),
        v.unlabelledEvalDensity (sigmaFlagOfEmb θ) Δ) /
        (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ) =
      (∑ cls ∈ v.support, v cls * (normalisationFactor σ cls.out *
        unlabelledDensity emptyType cls.out.forget (G k) Δ)) /
        (normalisationFactor σ σ.toFlag *
          unlabelledDensity emptyType σ.toFlag.forget (G k) Δ) -
      ∑ cls ∈ v.support, v cls *
        ((∑ θ : SigmaEmbIntoGraph σ (G k),
            unlabelledDensity σ cls.out (sigmaFlagOfEmb θ) Δ) /
          (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ)) *
        ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1) := by
    filter_upwards [htend_Q.eventually (Ioi_mem_nhds (half_lt_self_iff.mpr hQlim_pos))] with k hk_pos
    have hQ_ne : normalisationFactor σ σ.toFlag *
        unlabelledDensity emptyType σ.toFlag.forget (G k) Δ ≠ 0 :=
      ne_of_gt (lt_trans (div_pos hQlim_pos two_pos) hk_pos)
    have h_id := hid_sum k; rw [hsum_split k] at h_id
    have h_div : (∑ θ : SigmaEmbIntoGraph σ (G k),
          v.unlabelledEvalDensity (sigmaFlagOfEmb θ) Δ) /
        (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ) +
      ∑ cls ∈ v.support, v cls *
        ((∑ θ : SigmaEmbIntoGraph σ (G k),
            unlabelledDensity σ cls.out (sigmaFlagOfEmb θ) Δ) /
          (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ)) *
        ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1) =
      (∑ cls ∈ v.support, v cls * (normalisationFactor σ cls.out *
        unlabelledDensity emptyType cls.out.forget (G k) Δ)) /
        (normalisationFactor σ σ.toFlag *
          unlabelledDensity emptyType σ.toFlag.forget (G k) Δ) :=
      (div_eq_of_eq_mul hQ_ne (by rw [mul_comm]; exact h_id)).symm
    linarith
  -- E_θ → L/Qlim → eventually ≤ L/(2·Qlim)
  have htend_Eθ : Filter.Tendsto
      (fun k => (∑ θ : SigmaEmbIntoGraph σ (G k),
        v.unlabelledEvalDensity (sigmaFlagOfEmb θ) Δ) /
        (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ))
      Filter.atTop (nhds (L / Qlim)) := by
    have htend_sub : Filter.Tendsto
        (fun k => (∑ cls ∈ v.support, v cls * (normalisationFactor σ cls.out *
          unlabelledDensity emptyType cls.out.forget (G k) Δ)) /
          (normalisationFactor σ σ.toFlag *
            unlabelledDensity emptyType σ.toFlag.forget (G k) Δ) -
        ∑ cls ∈ v.support, v cls *
          ((∑ θ : SigmaEmbIntoGraph σ (G k),
              unlabelledDensity σ cls.out (sigmaFlagOfEmb θ) Δ) /
            (Fintype.card (SigmaEmbIntoGraph σ (G k)) : ℝ)) *
          ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
            (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1))
        Filter.atTop (nhds (L / Qlim)) := by
      rw [show L / Qlim = L / Qlim - 0 from by ring]
      exact (htend_S_L.div htend_Q (ne_of_gt hQlim_pos)).sub hdiff_sum_tendsto
    exact htend_sub.congr' (Filter.EventuallyEq.symm hEθ_eventually)
  exact Filter.eventually_atTop.mp
    ((htend_Eθ.eventually (gt_mem_nhds (by
      rw [div_lt_div_iff₀ hQlim_pos (mul_pos two_pos hQlim_pos)]; nlinarith))).mono
      fun k hk => le_of_lt hk)


set_option maxHeartbeats 3200000 in
-- Lemma 2.8 (averaging preserves positivity): multi-step density + pigeonhole argument
/-- **Contrapositive of Lemma 2.8** (Thesis p.41, lines 715-757):
    If ψ(⟦v⟧) < 0 for some ψ ∈ Φ^∅ and σ is a local type, then ∃ φ ∈ Φ^σ
    with φ(v) < 0. Requires v to have local support (matching the thesis's
    restriction to 𝓛^σ = span of local σ-flags). -/
theorem averaging_neg_gives_neg_functional (σ : FlagType)
    (𝒢 : GraphClass) (Δ : GraphParam)
    (hσ : IsLocalType σ 𝒢 Δ)
    (v : FlagAlg σ)
    (hv_local : ∀ cls ∈ v.support, IsLocalFlag σ cls.out 𝒢 Δ)
    (ψ : LimitFunctional emptyType 𝒢 Δ)
    (hψ : ψ.evalAlg (averagingAlg σ v) < 0) :
    ∃ φ : LimitFunctional σ 𝒢 Δ, φ.evalAlg v < 0 := by
  -- Thesis Lemma 2.8: construct σ-level sequence with v.uED ≤ c < 0,
  -- then any limit functional from it witnesses φ.evalAlg v < 0.
  suffices hsuff : ∃ (seq : DeltaIncreasingSeq σ Δ)
      (hclass : ∀ k, 𝒢 (seq.seq k).forget)
      (c : ℝ) (_ : c < 0),
      ∀ k, v.unlabelledEvalDensity (seq.seq k) Δ ≤ c by
    obtain ⟨seq, hclass, c, hc_neg, hbound⟩ := hsuff
    let φ := limit_functional_construction σ 𝒢 Δ seq hclass
    have hseq_eq := limit_functional_construction_seq σ 𝒢 Δ seq hclass
    refine ⟨φ, ?_⟩
    rw [φ.evalAlg_eq_evalAlgOf v]
    have hconv_cls : ∀ (F : Flag σ), IsLocalFlag σ F 𝒢 Δ →
        Filter.Tendsto (fun k => unlabelledDensity σ F (seq.seq (φ.sub k)) Δ)
          Filter.atTop (nhds (φ.eval F)) :=
      fun F hF => hseq_eq ▸ φ.convergence F hF
    have hcls_eq : ∀ (cls : FlagClass σ) (G : Flag σ),
        classUnlabelledDensity σ G Δ cls = unlabelledDensity σ cls.out G Δ := by
      intro cls G; unfold classUnlabelledDensity
      conv_lhs => rw [← Quotient.out_eq cls]; simp only [Quotient.lift_mk]
    have htend : Filter.Tendsto
        (fun k => v.unlabelledEvalDensity (seq.seq (φ.sub k)) Δ)
        Filter.atTop (nhds (evalAlgOf φ.eval v)) := by
      simp only [evalAlgOf, Finsupp.sum]
      simp_rw [show ∀ k, v.unlabelledEvalDensity (seq.seq (φ.sub k)) Δ =
        ∑ cls ∈ v.support, v cls * unlabelledDensity σ cls.out (seq.seq (φ.sub k)) Δ from
        fun k => by simp only [FlagAlg.unlabelledEvalDensity, Finsupp.sum, hcls_eq]]
      exact tendsto_finset_sum _ fun cls hcls =>
        (hconv_cls cls.out (hv_local cls hcls)).const_mul _
    exact lt_of_le_of_lt
      (le_of_tendsto htend (Filter.Eventually.of_forall (fun k => hbound (φ.sub k)))) hc_neg
  -- By averaging_eventually_neg, for large k, E_θ[v.uED(G_k,θ)] ≤ c < 0.
  obtain ⟨c, hc_neg, N₀, hN₀⟩ := averaging_eventually_neg σ 𝒢 Δ hσ v hv_local ψ hψ
  -- For k ≥ N₀, pigeonhole gives θ_k with v.uED(G_k, θ_k) ≤ c.
  have hexists_neg : ∀ k, N₀ ≤ k →
      ∃ θ : SigmaEmbIntoGraph σ (ψ.seq.seq (ψ.sub k)),
        v.unlabelledEvalDensity (sigmaFlagOfEmb θ) Δ ≤ c := by
    intro k hk
    have havg_le_c := hN₀ k hk
    by_cases hN : (Fintype.card (SigmaEmbIntoGraph σ (ψ.seq.seq (ψ.sub k)))) = 0
    · simp [hN] at havg_le_c; linarith
    · have hN_pos : (0 : ℝ) < (Fintype.card
          (SigmaEmbIntoGraph σ (ψ.seq.seq (ψ.sub k))) : ℝ) :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
      have hsum_le : ∑ θ : SigmaEmbIntoGraph σ (ψ.seq.seq (ψ.sub k)),
          v.unlabelledEvalDensity (sigmaFlagOfEmb θ) Δ ≤
          c * (Fintype.card (SigmaEmbIntoGraph σ (ψ.seq.seq (ψ.sub k))) : ℝ) := by
        rwa [div_le_iff₀ hN_pos] at havg_le_c
      rw [mul_comm] at hsum_le
      rw [← show ∑ _ : SigmaEmbIntoGraph σ (ψ.seq.seq (ψ.sub k)), c =
          (Fintype.card (SigmaEmbIntoGraph σ (ψ.seq.seq (ψ.sub k))) : ℝ) * c from
        by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]] at hsum_le
      obtain ⟨θ, _, hθ⟩ := Finset.exists_le_of_sum_le
        (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hN)))
        hsum_le
      exact ⟨θ, hθ⟩
  -- Build shifted sequence: for each k, choose θ_{k+N₀} via pigeonhole.
  classical
  let θ_seq : (k : ℕ) → SigmaEmbIntoGraph σ (ψ.seq.seq (ψ.sub (k + N₀))) :=
    fun k => (hexists_neg (k + N₀) (Nat.le_add_left N₀ k)).choose
  have hθ_bound : ∀ k,
      v.unlabelledEvalDensity (sigmaFlagOfEmb (θ_seq k)) Δ ≤ c :=
    fun k => (hexists_neg (k + N₀) (Nat.le_add_left N₀ k)).choose_spec
  let seq : DeltaIncreasingSeq σ Δ := {
    seq := fun k => sigmaFlagOfEmb (θ_seq k)
    increasing := by
      intro a b hab
      simp only [show ∀ k, (sigmaFlagOfEmb (θ_seq k)).forget =
        (ψ.seq.seq (ψ.sub (k + N₀))).forget from fun k => rfl]
      exact ψ.seq.increasing (ψ.sub_strictMono (by omega))
  }
  refine ⟨seq, ?_, c, hc_neg, hθ_bound⟩
  intro k
  simp only [seq, show (sigmaFlagOfEmb (θ_seq k)).forget =
    (ψ.seq.seq (ψ.sub (k + N₀))).forget from rfl]
  exact ψ.seq_in_class (ψ.sub (k + N₀))

/-- **Lemma 2.8** (Thesis p.41): For a local type σ, the averaging operator
    preserves positivity: ⟦C^σ_sem⟧ ⊆ C^∅_sem.

    Proof: By contradiction. If ⟦v⟧ ∉ C^∅_sem, then ∃ ψ with ψ(⟦v⟧) < 0.
    By `averaging_neg_gives_neg_functional`, ∃ φ ∈ Φ^σ with φ(v) < 0.
    But v ∈ C^σ_sem means φ(v) ≥ 0 for all φ ∈ Φ^σ. Contradiction. -/
theorem averaging_preserves_positivity (σ : FlagType)
    (𝒢 : GraphClass) (Δ : GraphParam)
    (hσ : IsLocalType σ 𝒢 Δ)
    (v : FlagAlg σ) (hv : v ∈ SemanticCone σ 𝒢 Δ)
    (hv_local : ∀ cls ∈ v.support, IsLocalFlag σ cls.out 𝒢 Δ) :
    averagingAlg σ v ∈ SemanticCone emptyType 𝒢 Δ := by
  intro ψ
  by_contra h
  push_neg at h
  obtain ⟨φ, hφ⟩ := averaging_neg_gives_neg_functional σ 𝒢 Δ hσ v hv_local ψ h
  exact absurd (hv φ) (not_le.mpr hφ)

/-! ## §2.5: The Semidefinite Method

Adapts the semidefinite method to the local flag algebra. The key constraint
is that ⟦f²⟧ ≥ 0 is only available for local types σ. -/

/-- **SDP Bound Certificate**: A bound φ(f) ≤ c can be certified by exhibiting
    c · σ - f ∈ C^σ_sem, i.e. the vector c · (unit) - f is positive.
    (Thesis §2.5) -/
theorem sdp_bound (σ : FlagType) (𝒢 : GraphClass) (Δ : GraphParam)
    (φ : LimitFunctional σ 𝒢 Δ)
    (f : FlagAlg σ) (bound : ℝ)
    (hcone : (FlagAlg.add (FlagAlg.smul bound (FlagAlg.single σ σ.toFlag))
      (FlagAlg.smul (-1) f)).isPositive 𝒢 Δ) :
    φ.evalAlg f ≤ bound := by
  have h := hcone φ
  rw [LimitFunctional.evalAlg_add, LimitFunctional.evalAlg_smul,
      LimitFunctional.evalAlg_smul, LimitFunctional.evalAlg_single] at h
  rw [φ.eval_type, mul_one] at h
  linarith

/-- **Corollary of Lemma 2.8**: For a local type σ, ⟦f²⟧ ≥ 0 for all f ∈ 𝓛^σ.
    This is the key SDP constraint: squares average to positive elements.
    (Thesis §2.5, immediate from averaging_preserves_positivity + square_in_cone) -/
theorem square_averaging_positive (σ : FlagType)
    (𝒢 : GraphClass) (Δ : GraphParam)
    (hσ : IsLocalType σ 𝒢 Δ)
    (f : FlagAlg σ)
    (hf : ∀ cls ∈ f.support, IsLocalFlag σ cls.out 𝒢 Δ) :
    averagingAlg σ (f.mul f) ∈ SemanticCone emptyType 𝒢 Δ :=
  averaging_preserves_positivity σ 𝒢 Δ hσ (f.mul f) (square_in_cone σ 𝒢 Δ f hf)
    (mul_local_support σ f f 𝒢 Δ hf hf)

/-- **SDP Method** (Thesis §2.5): To prove φ(f) ≤ bound for all φ ∈ Φ^∅,
    it suffices to find:
    1. Local types σ₁, ..., σ_m
    2. Vectors g_i ∈ 𝓛^{σ_i}
    3. Nonneg coefficients a_i
    such that bound · ∅ - f = Σ_i a_i · ⟦g_i²⟧ (modulo elements known to be positive).

    This is the local flag algebra analogue of the classic SDP method.
    The key limitation: we can only use types σ_i that are local types. -/
theorem sdp_method (𝒢 : GraphClass) (Δ : GraphParam) (φ : LimitFunctional emptyType 𝒢 Δ)
    (f : FlagAlg emptyType) (bound : ℝ)
    (σ : FlagType)
    (hσ : IsLocalType σ 𝒢 Δ)
    (g : FlagAlg σ) (a : ℝ) (ha : 0 ≤ a)
    (hg : ∀ cls ∈ g.support, IsLocalFlag σ cls.out 𝒢 Δ)
    (hcert : FlagAlg.add (FlagAlg.smul bound (FlagAlg.single emptyType emptyType.toFlag))
      (FlagAlg.smul (-1) f) =
      FlagAlg.smul a (averagingAlg σ (g.mul g))) :
    φ.evalAlg f ≤ bound := by
  apply sdp_bound emptyType 𝒢 Δ
  intro ψ
  rw [hcert]
  rw [LimitFunctional.evalAlg_smul]
  exact mul_nonneg ha (square_averaging_positive σ 𝒢 Δ hσ g hg ψ)

/-! ## Generic Flag Algebra Types

Generic versions of the flag algebra types parameterized by `RelUniverse`.
These generalize the `SimpleGraph`-specific types defined above. -/

/-- Generic flag algebra: formal ℝ-linear combinations of generic flag classes. -/
noncomputable abbrev GenFlagAlg (R : RelUniverse) (σ : GenFlagType R) :=
  GenFlagClass R σ →₀ ℝ

/-- Basis element: the indicator of a single flag class. -/
noncomputable def GenFlagAlg.single {R : RelUniverse} {σ : GenFlagType R}
    (F : GenFlag R σ) : GenFlagAlg R σ :=
  Finsupp.single (GenFlagClass.mk F) 1

/-- Generic flag automorphism count. -/
noncomputable def genFlagAutCount (R : RelUniverse) (σ : GenFlagType R)
    (F : GenFlag R σ) : ℕ :=
  genInducedCount R σ F F

/-- Generic unlabelled density: IC / (C(Δ, f) · Aut). -/
noncomputable def genUnlabelledDensity (R : RelUniverse) (σ : GenFlagType R)
    (F G : GenFlag R σ) (Δ : GenFlag R (GenFlagType.empty R) → ℕ) : ℝ :=
  (genInducedCount R σ F G : ℝ) /
    ((Nat.choose (Δ G.forget) (F.size - σ.size) : ℝ) *
     (genFlagAutCount R σ F : ℝ))

/-- All generic flag classes of a given size n. -/
noncomputable def genClassesOfSize (R : RelUniverse) (σ : GenFlagType R)
    (n : ℕ) (hn : σ.size ≤ n) : Finset (GenFlagClass R σ) := by
  haveI : Fintype (R.Str n) := R.instFintype n
  haveI : DecidableEq (R.Str n) := R.instDecEq n
  haveI : DecidableEq (R.Str σ.size) := R.instDecEq σ.size
  exact (Finset.univ : Finset (Σ (s : R.Str n),
    { f : Fin σ.size ↪ Fin n // R.comap f s = σ.str })).image
    (fun p => GenFlagClass.mk ⟨n, p.1, p.2.1, p.2.2, hn⟩)

/-- Lift unlabelled density to generic flag classes. -/
noncomputable def genClassUnlabelledDensity (R : RelUniverse) (σ : GenFlagType R)
    (G : GenFlag R σ) (Δ : GenFlag R (GenFlagType.empty R) → ℕ)
    (cls : GenFlagClass R σ) : ℝ :=
  genUnlabelledDensity R σ cls.out G Δ

/-- Evaluate a generic FlagAlg element as a density at graph G. -/
noncomputable def genUnlabelledEvalDensity {R : RelUniverse} {σ : GenFlagType R}
    (v : GenFlagAlg R σ) (G : GenFlag R σ)
    (Δ : GenFlag R (GenFlagType.empty R) → ℕ) : ℝ :=
  v.sum (fun cls c => c * genClassUnlabelledDensity R σ G Δ cls)

theorem genUnlabelledEvalDensity_zero {R : RelUniverse} {σ : GenFlagType R}
    (G : GenFlag R σ) (Δ : GenFlag R (GenFlagType.empty R) → ℕ) :
    genUnlabelledEvalDensity (0 : GenFlagAlg R σ) G Δ = 0 :=
  Finsupp.sum_zero_index

theorem genUnlabelledEvalDensity_add {R : RelUniverse} {σ : GenFlagType R}
    (v w : GenFlagAlg R σ) (G : GenFlag R σ) (Δ : GenFlag R (GenFlagType.empty R) → ℕ) :
    genUnlabelledEvalDensity (v + w) G Δ =
      genUnlabelledEvalDensity v G Δ + genUnlabelledEvalDensity w G Δ :=
  Finsupp.sum_add_index (by simp) (by intros; ring)

theorem genUnlabelledEvalDensity_pointwise_smul {R : RelUniverse} {σ : GenFlagType R}
    (c : ℝ) (v : GenFlagAlg R σ) (G : GenFlag R σ) (Δ : GenFlag R (GenFlagType.empty R) → ℕ) :
    genUnlabelledEvalDensity (c • v) G Δ = c * genUnlabelledEvalDensity v G Δ := by
  simp only [genUnlabelledEvalDensity]
  rw [Finsupp.sum_smul_index (by simp)]
  simp only [Finsupp.sum, Finset.mul_sum]; congr 1; ext cls; ring

/-- Standalone linear evaluation of a generic FlagAlg element. -/
noncomputable def genEvalAlgOf {R : RelUniverse} {σ : GenFlagType R}
    (eval : GenFlag R σ → ℝ) (v : GenFlagAlg R σ) : ℝ :=
  v.sum (fun cls c => c * eval cls.out)

/-! ## Phase 4b: Generic Local Flag Product -/

/-- Generic joint count: pairs of embeddings with overlap = σ-image and covering G. -/
noncomputable def genJointCount (R : RelUniverse) (σ : GenFlagType R)
    (F₁ F₂ G : GenFlag R σ) : ℕ :=
  Fintype.card
    { p : GenInducedEmbedding R σ F₁ G × GenInducedEmbedding R σ F₂ G //
      (∀ i : Fin G.size,
        (i ∈ Set.range p.1.toFun ∧ i ∈ Set.range p.2.toFun) ↔
          i ∈ Set.range G.embedding) ∧
      (∀ i : Fin G.size,
        i ∈ Set.range p.1.toFun ∨ i ∈ Set.range p.2.toFun) }

/-- Generic joint induced density. -/
noncomputable def genJointInducedDensity (R : RelUniverse) (σ : GenFlagType R)
    (F₁ F₂ G : GenFlag R σ) : ℝ :=
  (genJointCount R σ F₁ F₂ G : ℝ) /
    ((Nat.choose (G.size - σ.size) (F₁.size - σ.size) : ℝ) *
     (Nat.choose (G.size - σ.size - (F₁.size - σ.size)) (F₂.size - σ.size) : ℝ))

/-- Generic local flag product on basis elements. -/
noncomputable def genLocalFlagProduct (R : RelUniverse) (σ : GenFlagType R)
    (F F' : GenFlag R σ) : GenFlagAlg R σ :=
  let n := F.size + F'.size - σ.size
  if hn : σ.size ≤ n then
    ((genFlagAutCount R σ F : ℝ) * (genFlagAutCount R σ F' : ℝ))⁻¹ •
      (genClassesOfSize R σ n hn).sum (fun cls =>
        Finsupp.single cls (genJointInducedDensity R σ F F' cls.out))
  else 0

/-- The range of `GenInducedEmbedding.mapIso φ ... e` equals the range of `e`:
    `range(e.toFun ∘ φ) = range(e.toFun)` since `φ` is a bijection. -/
theorem GenInducedEmbedding.range_mapIso {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₂ G : GenFlag R σ}
    (φ : Fin F₁.size ≃ Fin F₂.size)
    (hstr : R.comap φ F₂.str = F₁.str)
    (hcompat : ∀ i : Fin σ.size, φ (F₁.embedding i) = F₂.embedding i)
    (e : GenInducedEmbedding R σ F₂ G) :
    Set.range (GenInducedEmbedding.mapIso φ hstr hcompat e).toFun = Set.range e.toFun := by
  simp only [GenInducedEmbedding.mapIso]
  ext x
  simp only [Set.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨φ y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨φ.symm y, by simp⟩

/-- Generic joint count is invariant under flag isomorphism on the left argument. -/
theorem genJointCount_flagIso_left {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₁' F₂ G : GenFlag R σ}
    (h : GenFlagIso σ F₁ F₁') :
    genJointCount R σ F₁ F₂ G = genJointCount R σ F₁' F₂ G := by
  obtain ⟨φ, hstr, hcompat⟩ := h
  unfold genJointCount
  apply Fintype.card_congr
  -- We need mapIso in both directions.
  -- Forward: φ maps F₁ → F₁', so mapIso φ.symm sends F₁-embeddings to F₁'-embeddings
  have hsymm : R.comap (⇑φ.symm) F₁.str = F₁'.str := by
    rw [← hstr, ← R.comap_comp]
    have : (⇑φ ∘ ⇑φ.symm : Fin F₁'.size → Fin F₁'.size) = id := by ext x; simp
    rw [this, R.comap_id]
  have hcompat_inv : ∀ i, φ.symm (F₁'.embedding i) = F₁.embedding i := by
    intro i; simp [← hcompat i]
  have hfwd : ∀ (e : GenInducedEmbedding R σ F₁ G),
      Set.range (GenInducedEmbedding.mapIso φ.symm hsymm hcompat_inv e).toFun =
        Set.range e.toFun :=
    GenInducedEmbedding.range_mapIso φ.symm hsymm hcompat_inv
  have hbwd : ∀ (e : GenInducedEmbedding R σ F₁' G),
      Set.range (GenInducedEmbedding.mapIso φ hstr hcompat e).toFun =
        Set.range e.toFun :=
    GenInducedEmbedding.range_mapIso φ hstr hcompat
  refine {
    toFun := fun x =>
      let e₁ := x.val.1; let e₂ := x.val.2
      let hoverlap := x.property.1; let hcovering := x.property.2
      ⟨⟨GenInducedEmbedding.mapIso φ.symm hsymm hcompat_inv e₁, e₂⟩,
        fun i => by rw [show (GenInducedEmbedding.mapIso φ.symm hsymm hcompat_inv e₁, e₂).1 =
          GenInducedEmbedding.mapIso φ.symm hsymm hcompat_inv e₁ from rfl, hfwd]; exact hoverlap i,
        fun i => by rw [show (GenInducedEmbedding.mapIso φ.symm hsymm hcompat_inv e₁, e₂).1 =
          GenInducedEmbedding.mapIso φ.symm hsymm hcompat_inv e₁ from rfl, hfwd]; exact hcovering i⟩
    invFun := fun x =>
      let e₁' := x.val.1; let e₂ := x.val.2
      let hoverlap := x.property.1; let hcovering := x.property.2
      ⟨⟨GenInducedEmbedding.mapIso φ hstr hcompat e₁', e₂⟩,
        fun i => by rw [show (GenInducedEmbedding.mapIso φ hstr hcompat e₁', e₂).1 =
          GenInducedEmbedding.mapIso φ hstr hcompat e₁' from rfl, hbwd]; exact hoverlap i,
        fun i => by rw [show (GenInducedEmbedding.mapIso φ hstr hcompat e₁', e₂).1 =
          GenInducedEmbedding.mapIso φ hstr hcompat e₁' from rfl, hbwd]; exact hcovering i⟩
    left_inv := fun ⟨⟨e₁, e₂⟩, _, _⟩ => by
      apply Subtype.ext
      simp only [Prod.mk.injEq]
      refine ⟨?_, trivial⟩
      cases e₁ with | mk f _ _ _ =>
      simp only [GenInducedEmbedding.mapIso, GenInducedEmbedding.mk.injEq]
      ext y; simp [Function.comp]
    right_inv := fun ⟨⟨e₁', e₂⟩, _, _⟩ => by
      apply Subtype.ext
      simp only [Prod.mk.injEq]
      refine ⟨?_, trivial⟩
      cases e₁' with | mk f _ _ _ =>
      simp only [GenInducedEmbedding.mapIso, GenInducedEmbedding.mk.injEq]
      ext y; simp [Function.comp]
  }

/-- Generic joint count is symmetric: swap (e₁, e₂) ↦ (e₂, e₁). -/
theorem genJointCount_comm (R : RelUniverse) (σ : GenFlagType R)
    (F₁ F₂ G : GenFlag R σ) :
    genJointCount R σ F₁ F₂ G = genJointCount R σ F₂ F₁ G := by
  unfold genJointCount
  apply Fintype.card_congr
  refine Equiv.subtypeEquiv (Equiv.prodComm _ _) (fun ⟨e₁, e₂⟩ => ?_)
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  constructor
  · rintro ⟨hoverlap, hcovering⟩
    exact ⟨fun i => by rw [and_comm]; exact hoverlap i,
           fun i => by rw [or_comm]; exact hcovering i⟩
  · rintro ⟨hoverlap, hcovering⟩
    exact ⟨fun i => by rw [and_comm]; exact hoverlap i,
           fun i => by rw [or_comm]; exact hcovering i⟩

/-- Generic joint count is invariant under flag isomorphism on the right argument. -/
theorem genJointCount_flagIso_right {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₂ F₂' G : GenFlag R σ}
    (h : GenFlagIso σ F₂ F₂') :
    genJointCount R σ F₁ F₂ G = genJointCount R σ F₁ F₂' G := by
  rw [genJointCount_comm, genJointCount_flagIso_left h, genJointCount_comm]

/-- Generic joint induced density is invariant under flag isomorphism on the left. -/
theorem genJointInducedDensity_flagIso_left {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₁' F₂ G : GenFlag R σ}
    (h : GenFlagIso σ F₁ F₁') :
    genJointInducedDensity R σ F₁ F₂ G = genJointInducedDensity R σ F₁' F₂ G := by
  unfold genJointInducedDensity
  rw [genJointCount_flagIso_left h, genFlagIso_size_eq h]

/-- Generic joint induced density is invariant under flag isomorphism on the right. -/
theorem genJointInducedDensity_flagIso_right {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₂ F₂' G : GenFlag R σ}
    (h : GenFlagIso σ F₂ F₂') :
    genJointInducedDensity R σ F₁ F₂ G = genJointInducedDensity R σ F₁ F₂' G := by
  unfold genJointInducedDensity
  rw [genJointCount_flagIso_right h, genFlagIso_size_eq h]

/-- Generic joint induced density is symmetric: p(F,F';H) = p(F',F;H). -/
theorem genJointInducedDensity_comm (R : RelUniverse) (σ : GenFlagType R)
    (F F' H : GenFlag R σ) :
    genJointInducedDensity R σ F F' H = genJointInducedDensity R σ F' F H := by
  unfold genJointInducedDensity
  rw [genJointCount_comm]
  congr 1
  set g := H.size - σ.size
  set f := F.size - σ.size
  set f' := F'.size - σ.size
  by_cases hab : f + f' ≤ g
  · exact choose_mul_choose_comm g f f' hab
  · push_neg at hab
    have h1 : Nat.choose g f * Nat.choose (g - f) f' = 0 := by
      rw [Nat.mul_eq_zero]
      by_contra h; push_neg at h
      have := Nat.choose_ne_zero_iff.mp h.1
      have := Nat.choose_ne_zero_iff.mp h.2
      omega
    have h2 : Nat.choose g f' * Nat.choose (g - f') f = 0 := by
      rw [Nat.mul_eq_zero]
      by_contra h; push_neg at h
      have := Nat.choose_ne_zero_iff.mp h.1
      have := Nat.choose_ne_zero_iff.mp h.2
      omega
    have h1' : (Nat.choose g f : ℝ) * (Nat.choose (g - f) f' : ℝ) = 0 := by exact_mod_cast h1
    have h2' : (Nat.choose g f' : ℝ) * (Nat.choose (g - f') f : ℝ) = 0 := by exact_mod_cast h2
    linarith

/-- Generic flag automorphism count is invariant under flag isomorphism.
    The bijection `GIE σ F₁ F₁ ≃ GIE σ F₂ F₂` is by conjugation: `e ↦ φ ∘ e ∘ φ⁻¹`. -/
theorem genFlagAutCount_flagIso {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₂ : GenFlag R σ} (h : GenFlagIso σ F₁ F₂) :
    genFlagAutCount R σ F₁ = genFlagAutCount R σ F₂ := by
  obtain ⟨φ, hstr, hcompat⟩ := h
  unfold genFlagAutCount genInducedCount
  apply Fintype.card_congr
  have hsymm : R.comap (⇑φ.symm) F₁.str = F₂.str := by
    rw [← hstr, ← R.comap_comp]
    have : (⇑φ ∘ ⇑φ.symm : Fin F₂.size → Fin F₂.size) = id := by ext x; simp
    rw [this, R.comap_id]
  have hcompat_symm : ∀ i, φ.symm (F₂.embedding i) = F₁.embedding i := by
    intro i; simp [← hcompat i]
  refine {
    toFun := fun e =>
      { toFun := φ ∘ e.toFun ∘ φ.symm
        injective := φ.injective.comp (e.injective.comp φ.symm.injective)
        isInduced := by
          change R.comap ((⇑φ ∘ e.toFun) ∘ ⇑φ.symm) F₂.str = F₂.str
          rw [R.comap_comp, R.comap_comp e.toFun ⇑φ, hstr, e.isInduced, hsymm]
        compat := fun i => by simp [Function.comp, hcompat_symm, e.compat, hcompat] }
    invFun := fun e =>
      { toFun := φ.symm ∘ e.toFun ∘ φ
        injective := φ.symm.injective.comp (e.injective.comp φ.injective)
        isInduced := by
          change R.comap ((⇑φ.symm ∘ e.toFun) ∘ ⇑φ) F₁.str = F₁.str
          rw [R.comap_comp, R.comap_comp e.toFun ⇑φ.symm, hsymm, e.isInduced, hstr]
        compat := fun i => by simp [Function.comp, hcompat, e.compat, hcompat_symm] }
    left_inv := fun e => by
      cases e; simp only [GenInducedEmbedding.mk.injEq]
      ext x; simp [Function.comp]
    right_inv := fun e => by
      cases e; simp only [GenInducedEmbedding.mk.injEq]
      ext x; simp [Function.comp]
  }

/-- Generic local flag product is invariant under flag isomorphism on the left. -/
theorem genLocalFlagProduct_flagIso_left {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₁' F₂ : GenFlag R σ}
    (h : GenFlagIso σ F₁ F₁') :
    genLocalFlagProduct R σ F₁ F₂ = genLocalFlagProduct R σ F₁' F₂ := by
  unfold genLocalFlagProduct
  have hsz := genFlagIso_size_eq h
  have haut := genFlagAutCount_flagIso h
  simp only [hsz, haut]
  split_ifs with hn
  · congr 1
    apply Finset.sum_congr rfl
    intro cls _
    rw [genJointInducedDensity_flagIso_left h]
  · rfl

/-- Generic local flag product is invariant under flag isomorphism on the right. -/
theorem genLocalFlagProduct_flagIso_right {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₂ F₂' : GenFlag R σ}
    (h : GenFlagIso σ F₂ F₂') :
    genLocalFlagProduct R σ F₁ F₂ = genLocalFlagProduct R σ F₁ F₂' := by
  unfold genLocalFlagProduct
  have hsz := genFlagIso_size_eq h
  have haut := genFlagAutCount_flagIso h
  simp only [hsz, haut]
  split_ifs with hn
  · congr 1
    apply Finset.sum_congr rfl
    intro cls _
    rw [genJointInducedDensity_flagIso_right h]
  · rfl

/-- Generic local flag product respects isomorphism. -/
theorem genLocalFlagProduct_flagIso {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₁' F₂ F₂' : GenFlag R σ}
    (h₁ : GenFlagIso σ F₁ F₁') (h₂ : GenFlagIso σ F₂ F₂') :
    genLocalFlagProduct R σ F₁ F₂ = genLocalFlagProduct R σ F₁' F₂' :=
  (genLocalFlagProduct_flagIso_left h₁).trans (genLocalFlagProduct_flagIso_right h₂)

/-- Generic local flag product lifted to isomorphism classes. -/
noncomputable def genLocalFlagProduct_class (R : RelUniverse) (σ : GenFlagType R)
    (cls₁ cls₂ : GenFlagClass R σ) : GenFlagAlg R σ :=
  Quotient.lift₂ (fun F₁ F₂ => genLocalFlagProduct R σ F₁ F₂)
    (fun _ _ _ _ h₁ h₂ => genLocalFlagProduct_flagIso h₁ h₂) cls₁ cls₂

/-- Generic flag algebra multiplication (bilinear extension). -/
noncomputable def GenFlagAlg.mul {R : RelUniverse} {σ : GenFlagType R}
    (v w : GenFlagAlg R σ) : GenFlagAlg R σ :=
  v.sum (fun cls₁ c₁ =>
    w.sum (fun cls₂ c₂ =>
      (c₁ * c₂) • genLocalFlagProduct_class R σ cls₁ cls₂))

/-! ## Phase 4c: Generic Product Properties

Generic commutativity, unit, associativity, and bilinearity helpers for
`GenFlagAlg.mul`.  Commutativity, unit, and associativity are axiomatized
(proved for `simpleGraphUniverse`; the proofs transfer but the translation
is deferred).  The bilinearity helpers are proved from the Finsupp definitions. -/

/-- Generic product commutativity.
    Follows from `genJointInducedDensity_comm` (symmetric joint density)
    and multinomial symmetry. -/
theorem genProduct_comm {R : RelUniverse} (σ : GenFlagType R) (F F' : GenFlag R σ) :
    genLocalFlagProduct R σ F F' = genLocalFlagProduct R σ F' F := by
  unfold genLocalFlagProduct
  rw [show F.size + F'.size = F'.size + F.size from Nat.add_comm _ _]
  dsimp only []
  split
  · congr 1
    · rw [mul_comm]
    · exact Finset.sum_congr rfl fun cls _ => by rw [genJointInducedDensity_comm]
  · rfl

/-- `GenFlagClass.mk F₁ = GenFlagClass.mk F₂` iff `GenFlagIso σ F₁ F₂`. -/
theorem GenFlagClass.mk_eq {R : RelUniverse} {σ : GenFlagType R} (F F' : GenFlag R σ) :
    GenFlagClass.mk F = GenFlagClass.mk F' ↔ GenFlagIso σ F F' :=
  Quotient.eq (r := genFlagSetoid σ)

/-- The type flag `σ.toFlag` has exactly one automorphism (the identity). -/
theorem genFlagAutCount_toFlag {R : RelUniverse} (σ : GenFlagType R) :
    genFlagAutCount R σ σ.toFlag = 1 := by
  unfold genFlagAutCount genInducedCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨id, Function.injective_id, R.comap_id _, fun _ => rfl⟩, fun e => ?_⟩
  have hfun : e.toFun = id := funext fun x => by
    have hx : x.val < σ.size := x.isLt
    have : x = (Function.Embedding.refl _) ⟨x.val, hx⟩ := by simp
    rw [this]; exact e.compat ⟨x.val, hx⟩
  cases e; simp only [GenInducedEmbedding.mk.injEq]; exact hfun

/-- The identity is always a `GenInducedEmbedding`, witnessing `genFlagAutCount ≥ 1`. -/
theorem genFlagAutCount_pos {R : RelUniverse} (σ : GenFlagType R) (F : GenFlag R σ) :
    0 < genFlagAutCount R σ F := by
  unfold genFlagAutCount genInducedCount
  rw [Fintype.card_pos_iff]
  exact ⟨⟨id, Function.injective_id, R.comap_id _, fun _ => rfl⟩⟩

/-- A `GenInducedEmbedding R σ F H` with `F.size = H.size` yields a `GenFlagIso σ F H`. -/
private theorem genFlagIso_of_inducedEmbedding_same_size {R : RelUniverse} {σ : GenFlagType R}
    (F H : GenFlag R σ) (hsize : F.size = H.size) (e : GenInducedEmbedding R σ F H) :
    GenFlagIso σ F H := by
  have hsurj : Function.Surjective e.toFun :=
    e.injective.surjective_of_finite (Fin.castOrderIso hsize).toEquiv
  let φequiv := Equiv.ofBijective e.toFun ⟨e.injective, hsurj⟩
  refine ⟨φequiv, ?_, fun i => e.compat i⟩
  rw [show (⇑φequiv : Fin F.size → Fin H.size) = e.toFun from rfl]
  exact e.isInduced

/-- `genInducedCount R σ F H = 0` when `F.size = H.size` and `¬ GenFlagIso σ F H`. -/
private theorem genInducedCount_eq_zero_of_not_iso {R : RelUniverse} {σ : GenFlagType R}
    (F H : GenFlag R σ) (hsize : F.size = H.size) (hnotiso : ¬ GenFlagIso σ F H) :
    genInducedCount R σ F H = 0 := by
  unfold genInducedCount
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun e => hnotiso (genFlagIso_of_inducedEmbedding_same_size F H hsize e)⟩

/-- The representative of a class in `genClassesOfSize` has size `n`. -/
theorem genClassesOfSize_out_size {R : RelUniverse} {σ : GenFlagType R} {n : ℕ}
    {hn : σ.size ≤ n} {cls : GenFlagClass R σ} (hcls : cls ∈ genClassesOfSize R σ n hn) :
    cls.out.size = n := by
  rw [genClassesOfSize, Finset.mem_image] at hcls
  obtain ⟨p, _, rfl⟩ := hcls
  have hiso := Quotient.exact (Quotient.out_eq (GenFlagClass.mk ⟨n, p.1, p.2.1, p.2.2, hn⟩))
  exact (genFlagIso_size_eq hiso).symm ▸ rfl

/-- `GenFlagClass.mk F` is in `genClassesOfSize` for the appropriate size. -/
theorem mk_F_mem_genClassesOfSize {R : RelUniverse} {σ : GenFlagType R}
    (F : GenFlag R σ) (hn : σ.size ≤ F.size) :
    GenFlagClass.mk F ∈ genClassesOfSize R σ F.size hn := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨F.str, F.embedding, F.isInduced⟩, rfl⟩

/-- The unique `GenInducedEmbedding R σ σ.toFlag G` is `G.embedding`. -/
private theorem genInducedCount_toFlag_eq_one {R : RelUniverse} (σ : GenFlagType R)
    (G : GenFlag R σ) : genInducedCount R σ σ.toFlag G = 1 := by
  unfold genInducedCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨fun i => G.embedding i, fun _ _ h => G.embedding.injective h, ?_,
    fun i => ?_⟩, fun b => ?_⟩
  · -- isInduced: R.comap G.embedding G.str = σ.str
    -- σ.toFlag.str = σ.str, σ.toFlag.embedding = refl
    -- G.isInduced says R.comap G.embedding G.str = σ.str
    exact G.isInduced
  · -- compat: toFun (σ.toFlag.embedding i) = G.embedding i
    -- σ.toFlag.embedding = Function.Embedding.refl, so σ.toFlag.embedding i = i
    change G.embedding ((Function.Embedding.refl _) i) = G.embedding i; rfl
  · -- uniqueness
    have heq : b.toFun = fun i => G.embedding i := by
      funext v
      have hv : σ.toFlag.embedding v = v := rfl
      rw [← hv]; exact b.compat v
    cases b; simp only [GenInducedEmbedding.mk.injEq]; exact heq

/-- `genJointCount R σ F σ.toFlag H = genInducedCount R σ F H` when `H.size = F.size`. -/
private theorem genJointCount_toFlag_eq_inducedCount {R : RelUniverse} {σ : GenFlagType R}
    (F H : GenFlag R σ) (hsize : H.size = F.size) :
    genJointCount R σ F σ.toFlag H = genInducedCount R σ F H := by
  unfold genJointCount genInducedCount
  apply Fintype.card_congr
  have e₂_unique : ∀ (e : GenInducedEmbedding R σ σ.toFlag H),
      e.toFun = fun i => H.embedding i := by
    intro e; funext v
    have hv : σ.toFlag.embedding v = v := rfl
    rw [← hv]; exact e.compat v
  let e₂_canon : GenInducedEmbedding R σ σ.toFlag H :=
    ⟨fun i => H.embedding i, fun _ _ h => H.embedding.injective h,
     H.isInduced,
     fun i => by change H.embedding ((Function.Embedding.refl _) i) = H.embedding i; rfl⟩
  have inj_surj : ∀ (f : Fin F.size → Fin H.size), Function.Injective f →
      Function.Surjective f := by
    intro f hf; exact hf.surjective_of_finite (Fin.castOrderIso hsize.symm).toEquiv
  have overlap_auto : ∀ (e₁ : GenInducedEmbedding R σ F H),
      ∀ i : Fin H.size,
        (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂_canon.toFun) ↔
          i ∈ Set.range H.embedding := by
    intro e₁ i; constructor
    · rintro ⟨_, hi₂⟩; exact hi₂
    · intro hi; exact ⟨(inj_surj e₁.toFun e₁.injective) i, hi⟩
  have covering_auto : ∀ (e₁ : GenInducedEmbedding R σ F H),
      ∀ i : Fin H.size,
        i ∈ Set.range e₁.toFun ∨ i ∈ Set.range e₂_canon.toFun := by
    intro e₁ i; exact Or.inl ((inj_surj e₁.toFun e₁.injective) i)
  exact {
    toFun := fun p => p.1.1
    invFun := fun e₁ => ⟨(e₁, e₂_canon), overlap_auto e₁, covering_auto e₁⟩
    left_inv := fun ⟨⟨e₁, e₂⟩, hcond⟩ => by
      have hf : e₂.toFun = e₂_canon.toFun := e₂_unique e₂
      have he₂ : e₂ = e₂_canon := by cases e₂; subst hf; rfl
      subst he₂; rfl
    right_inv := fun _ => rfl
  }

/-- `genJointInducedDensity R σ F σ.toFlag H = genInducedCount R σ F H`
    when `H.size = F.size`. -/
private theorem genJointInducedDensity_toFlag {R : RelUniverse} {σ : GenFlagType R}
    (F H : GenFlag R σ) (hsize : H.size = F.size) :
    genJointInducedDensity R σ F σ.toFlag H = (genInducedCount R σ F H : ℝ) := by
  unfold genJointInducedDensity
  rw [genJointCount_toFlag_eq_inducedCount F H hsize]
  have h1 : σ.toFlag.size = σ.size := rfl
  have h2 : H.size - σ.size - (F.size - σ.size) = 0 := by omega
  have h3 : Nat.choose (H.size - σ.size) (F.size - σ.size) = 1 := by
    rw [hsize]; exact Nat.choose_self _
  rw [h1, Nat.sub_self, Nat.choose_zero_right, h3]; simp

set_option maxHeartbeats 400000 in
-- Needs extra heartbeats for Finsupp.ext + Finset.sum_ite_eq' + GenFlagIso construction
/-- **Generic product unit**: σ.toFlag is the multiplicative unit of GenFlagAlg.
    For any F: F · σ = single F. -/
theorem genProduct_unit {R : RelUniverse} (σ : GenFlagType R) (F : GenFlag R σ) :
    genLocalFlagProduct R σ F σ.toFlag = GenFlagAlg.single F := by
  unfold genLocalFlagProduct
  have hn : σ.size ≤ F.size + σ.toFlag.size - σ.size := by
    change σ.size ≤ F.size + σ.size - σ.size; have := F.hsize; omega
  rw [dif_pos hn, genFlagAutCount_toFlag, Nat.cast_one, mul_one]
  rw [GenFlagAlg.single]
  rw [inv_smul_eq_iff₀ (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (genFlagAutCount_pos σ F)))]
  simp only [Finsupp.smul_single', mul_one]
  ext cls
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  by_cases hmem : cls ∈ genClassesOfSize R σ _ hn
  · rw [if_pos hmem]
    have hout_size : (Quotient.out cls).size = F.size := by
      have hneq : F.size + σ.toFlag.size - σ.size = F.size := by
        change F.size + σ.size - σ.size = F.size; have := F.hsize; omega
      rw [← hneq]; exact genClassesOfSize_out_size hmem
    rw [genJointInducedDensity_toFlag F _ hout_size]
    by_cases heq : GenFlagClass.mk F = cls
    · rw [if_pos heq]
      congr 1
      have hiso : GenFlagIso σ (Quotient.out cls) F := by
        rw [← GenFlagClass.mk_eq, ← heq]; exact Quotient.out_eq _
      obtain ⟨φ, hstr, hcompat⟩ := hiso
      unfold genFlagAutCount genInducedCount
      apply Fintype.card_congr
      have hsymm : R.comap (⇑φ.symm) (Quotient.out cls).str = F.str := by
        have h1 : R.comap (⇑φ.symm) (Quotient.out cls).str =
            R.comap (⇑φ.symm) (R.comap (⇑φ) F.str) := by rw [hstr]
        rw [h1, ← R.comap_comp]
        have : (⇑φ ∘ ⇑φ.symm : Fin F.size → Fin F.size) = id := by ext x; simp
        rw [this, R.comap_id]
      have hcompat_symm : ∀ i, φ.symm (F.embedding i) = (Quotient.out cls).embedding i := by
        intro i; simp [← hcompat i]
      exact {
        toFun := fun e =>
          ⟨⇑φ ∘ e.toFun,
          fun a b h => e.injective (φ.injective h),
          by rw [R.comap_comp, hstr, e.isInduced],
          fun i => by change φ (e.toFun (F.embedding i)) = F.embedding i
                      rw [e.compat, hcompat]⟩
        invFun := fun e =>
          ⟨⇑φ.symm ∘ e.toFun,
          fun a b h => e.injective (φ.symm.injective h),
          by rw [R.comap_comp, hsymm, e.isInduced],
          fun i => by change φ.symm (e.toFun (F.embedding i)) = (Quotient.out cls).embedding i
                      rw [e.compat, ← hcompat]; simp⟩
        left_inv := fun e => by
          cases e; simp only [GenInducedEmbedding.mk.injEq]; ext x; simp [Function.comp]
        right_inv := fun e => by
          cases e; simp only [GenInducedEmbedding.mk.injEq]; ext x; simp [Function.comp]
      }
    · rw [if_neg heq]
      have hnotiso : ¬ GenFlagIso σ F (Quotient.out cls) := by
        intro hiso; apply heq
        rw [← GenFlagClass.mk_eq] at hiso
        rw [← Quotient.out_eq cls]; exact hiso
      rw [genInducedCount_eq_zero_of_not_iso F _ hout_size.symm hnotiso]; simp
  · rw [if_neg hmem]
    split_ifs with heq
    · exfalso; apply hmem; rw [← heq]
      have hneq : F.size + σ.toFlag.size - σ.size = F.size := by
        change F.size + σ.size - σ.size = F.size; have := F.hsize; omega
      have hmem' := mk_F_mem_genClassesOfSize F F.hsize
      rwa [show genClassesOfSize R σ F.size F.hsize =
        genClassesOfSize R σ (F.size + σ.toFlag.size - σ.size) hn from by
        congr 1; exact hneq.symm] at hmem'
    · rfl

theorem GenFlagAlg.mul_zero_left {R : RelUniverse} {σ : GenFlagType R}
    (v : GenFlagAlg R σ) : (0 : GenFlagAlg R σ).mul v = 0 := by
  simp [GenFlagAlg.mul, Finsupp.sum_zero_index]

theorem GenFlagAlg.mul_zero_right {R : RelUniverse} {σ : GenFlagType R}
    (v : GenFlagAlg R σ) : v.mul (0 : GenFlagAlg R σ) = 0 := by
  simp [GenFlagAlg.mul, Finsupp.sum_zero_index]

/-- Left-distributivity of generic multiplication over addition. -/
theorem GenFlagAlg.add_mul {R : RelUniverse} {σ : GenFlagType R}
    (v w u : GenFlagAlg R σ) : (v + w).mul u = v.mul u + w.mul u :=
  Finsupp.sum_add_index'
    (fun a => by simp [zero_mul, zero_smul, Finsupp.sum])
    (fun a b₁ b₂ => by
      simp_rw [_root_.add_mul, _root_.add_smul]
      simp only [Finsupp.sum, Finset.sum_add_distrib])

/-- Right-distributivity of generic multiplication over addition. -/
theorem GenFlagAlg.mul_add {R : RelUniverse} {σ : GenFlagType R}
    (v w u : GenFlagAlg R σ) : v.mul (w + u) = v.mul w + v.mul u := by
  unfold GenFlagAlg.mul
  conv_lhs => arg 2; ext cls₁ c₁
              rw [Finsupp.sum_add_index' (fun a => by simp [mul_zero, zero_smul])
                (fun a b₁ b₂ => by rw [_root_.mul_add, _root_.add_smul])]
  simp only [Finsupp.sum, Finset.sum_add_distrib]

/-- Left scalar multiplication commutes with generic multiplication. -/
theorem GenFlagAlg.smul_mul {R : RelUniverse} {σ : GenFlagType R}
    (c : ℝ) (v w : GenFlagAlg R σ) : (c • v).mul w = c • (v.mul w) := by
  unfold GenFlagAlg.mul
  rw [Finsupp.sum_smul_index (fun _ => by simp [zero_mul, zero_smul, Finsupp.sum])]
  simp only [Finsupp.sum, Finset.smul_sum, smul_smul]
  congr 1; ext cls; congr 1; ext cls'; ring

/-- Right scalar multiplication commutes with generic multiplication. -/
theorem GenFlagAlg.mul_smul {R : RelUniverse} {σ : GenFlagType R}
    (c : ℝ) (v w : GenFlagAlg R σ) : v.mul (c • w) = c • (v.mul w) := by
  unfold GenFlagAlg.mul
  conv_lhs => arg 2; ext cls₁ c₁
              rw [Finsupp.sum_smul_index (fun _ => by simp [mul_zero, zero_smul])]
  simp only [Finsupp.sum, Finset.smul_sum, smul_smul]
  congr 1; ext cls; congr 1; ext cls'; ring

theorem genLocalFlagProduct_class_mk {R : RelUniverse} (σ : GenFlagType R)
    (F₁ F₂ : GenFlag R σ) :
    genLocalFlagProduct_class R σ (GenFlagClass.mk F₁) (GenFlagClass.mk F₂) =
      genLocalFlagProduct R σ F₁ F₂ := by
  simp [genLocalFlagProduct_class, GenFlagClass.mk, Quotient.lift₂]

/-- Product on generic basis elements. -/
theorem GenFlagAlg.mul_single {R : RelUniverse} {σ : GenFlagType R}
    (F F' : GenFlag R σ) :
    (GenFlagAlg.single F).mul (GenFlagAlg.single F') =
      genLocalFlagProduct R σ F F' := by
  simp only [GenFlagAlg.mul, GenFlagAlg.single]
  rw [Finsupp.sum_single_index (by simp)]
  rw [Finsupp.sum_single_index (by simp)]
  rw [genLocalFlagProduct_class_mk]
  simp

/-- Generic triple joint count. -/
private noncomputable def genTripleJointCount {R : RelUniverse} (σ : GenFlagType R)
    (F₁ F₂ F₃ G : GenFlag R σ) : ℕ :=
  Fintype.card
    { t : GenInducedEmbedding R σ F₁ G × GenInducedEmbedding R σ F₂ G ×
          GenInducedEmbedding R σ F₃ G //
      (∀ i : Fin G.size,
        (i ∈ Set.range t.1.toFun ∧ i ∈ Set.range t.2.1.toFun) ↔ i ∈ Set.range G.embedding) ∧
      (∀ i : Fin G.size,
        (i ∈ Set.range t.1.toFun ∧ i ∈ Set.range t.2.2.toFun) ↔ i ∈ Set.range G.embedding) ∧
      (∀ i : Fin G.size,
        (i ∈ Set.range t.2.1.toFun ∧ i ∈ Set.range t.2.2.toFun) ↔ i ∈ Set.range G.embedding) ∧
      (∀ i : Fin G.size,
        i ∈ Set.range t.1.toFun ∨ i ∈ Set.range t.2.1.toFun ∨ i ∈ Set.range t.2.2.toFun) }

/-- Generic triple joint induced density. -/
private noncomputable def genTripleJointInducedDensity {R : RelUniverse} (σ : GenFlagType R)
    (F₁ F₂ F₃ G : GenFlag R σ) : ℝ :=
  (genTripleJointCount σ F₁ F₂ F₃ G : ℝ) /
    ((Nat.choose (G.size - σ.size) (F₁.size - σ.size) : ℝ) *
     (Nat.choose (G.size - σ.size - (F₁.size - σ.size)) (F₂.size - σ.size) : ℝ) *
     (Nat.choose (G.size - σ.size - (F₁.size - σ.size) - (F₂.size - σ.size))
       (F₃.size - σ.size) : ℝ))

private theorem genTripleJointCount_perm_231 {R : RelUniverse} (σ : GenFlagType R)
    (F₁ F₂ F₃ G : GenFlag R σ) :
    genTripleJointCount σ F₁ F₂ F₃ G = genTripleJointCount σ F₂ F₃ F₁ G := by
  unfold genTripleJointCount; apply Fintype.card_congr
  exact Equiv.subtypeEquiv
    { toFun := fun ⟨e₁, e₂, e₃⟩ => ⟨e₂, e₃, e₁⟩
      invFun := fun ⟨e₂, e₃, e₁⟩ => ⟨e₁, e₂, e₃⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    (fun ⟨e₁, e₂, e₃⟩ => by
      simp only [Equiv.coe_fn_mk]; constructor
      · rintro ⟨h12, h13, h23, hcov⟩
        exact ⟨h23, fun i => and_comm.trans (h12 i), fun i => and_comm.trans (h13 i),
               fun i => by rcases hcov i with h|h|h; exact .inr (.inr h); exact .inl h; exact .inr (.inl h)⟩
      · rintro ⟨h23, h21, h31, hcov⟩
        exact ⟨fun i => and_comm.trans (h21 i), fun i => and_comm.trans (h31 i), h23,
               fun i => by rcases hcov i with h|h|h; exact .inr (.inl h); exact .inr (.inr h); exact .inl h⟩)

private theorem genTripleJointInducedDensity_perm_231 {R : RelUniverse} (σ : GenFlagType R)
    (F₁ F₂ F₃ G : GenFlag R σ) :
    genTripleJointInducedDensity σ F₁ F₂ F₃ G =
    genTripleJointInducedDensity σ F₂ F₃ F₁ G := by
  -- The multinomial denominators are equal: proven by the same argument as in the
  -- SimpleGraph version (tripleJointInducedDensity_perm_231, line 3415).
  unfold genTripleJointInducedDensity; rw [genTripleJointCount_perm_231]; congr 1
  set g := G.size - σ.size; set f₁ := F₁.size - σ.size
  set f₂ := F₂.size - σ.size; set f₃ := F₃.size - σ.size
  by_cases h12 : f₁ + f₂ ≤ g
  · by_cases h123 : f₁ + f₂ + f₃ ≤ g
    · have h23 : f₂ + f₃ ≤ g := by omega
      have step1 := choose_mul_choose_comm g f₁ f₂ h12
      have step2 := choose_mul_choose_comm (g - f₂) f₁ f₃ (show f₁ + f₃ ≤ g - f₂ from by omega)
      calc (Nat.choose g f₁ : ℝ) * (Nat.choose (g - f₁) f₂ : ℝ) *
              (Nat.choose (g - f₁ - f₂) f₃ : ℝ)
          = (Nat.choose g f₂ : ℝ) * (Nat.choose (g - f₂) f₁ : ℝ) *
              (Nat.choose (g - f₁ - f₂) f₃ : ℝ) := by rw [step1]
        _ = (Nat.choose g f₂ : ℝ) * ((Nat.choose (g - f₂) f₁ : ℝ) *
              (Nat.choose ((g - f₂) - f₁) f₃ : ℝ)) := by
            rw [show g - f₁ - f₂ = (g - f₂) - f₁ from by omega]; ring
        _ = (Nat.choose g f₂ : ℝ) * ((Nat.choose (g - f₂) f₃ : ℝ) *
              (Nat.choose ((g - f₂) - f₃) f₁ : ℝ)) := by rw [step2]
        _ = (Nat.choose g f₂ : ℝ) * (Nat.choose (g - f₂) f₃ : ℝ) *
              (Nat.choose (g - f₂ - f₃) f₁ : ℝ) := by ring
    · push_neg at h123
      have rhs_zero : (Nat.choose g f₂ : ℝ) * (Nat.choose (g - f₂) f₃ : ℝ) *
          (Nat.choose (g - f₂ - f₃) f₁ : ℝ) = 0 := by
        by_cases h23 : f₂ + f₃ ≤ g
        · simp [show Nat.choose (g - f₂ - f₃) f₁ = 0 from by rw [Nat.choose_eq_zero_iff]; omega]
        · push_neg at h23
          simp [show Nat.choose (g - f₂) f₃ = 0 from by rw [Nat.choose_eq_zero_iff]; omega]
      have lhs_zero : (Nat.choose g f₁ : ℝ) * (Nat.choose (g - f₁) f₂ : ℝ) *
          (Nat.choose (g - f₁ - f₂) f₃ : ℝ) = 0 := by
        simp [show Nat.choose (g - f₁ - f₂) f₃ = 0 from by rw [Nat.choose_eq_zero_iff]; omega]
      rw [lhs_zero, rhs_zero]
  · push_neg at h12
    -- Both products are 0 because one factor vanishes
    -- LHS: C(g,f₁)*C(g-f₁,f₂) = 0 since f₁+f₂ > g
    -- RHS: need to find a zero factor
    have lhs_zero : (Nat.choose g f₁ : ℝ) * (Nat.choose (g - f₁) f₂ : ℝ) *
        (Nat.choose (g - f₁ - f₂) f₃ : ℝ) = 0 := by
      rcases le_or_gt f₁ g with hf₁ | hf₁
      · have : Nat.choose (g - f₁) f₂ = 0 := by rw [Nat.choose_eq_zero_iff]; omega
        simp [this]
      · have : Nat.choose g f₁ = 0 := by rw [Nat.choose_eq_zero_iff]; omega
        simp [this]
    have rhs_zero : (Nat.choose g f₂ : ℝ) * (Nat.choose (g - f₂) f₃ : ℝ) *
        (Nat.choose (g - f₂ - f₃) f₁ : ℝ) = 0 := by
      -- We need f₁ + f₂ > g. We know f₁ + f₂ > g.
      -- If f₂ > g, C(g,f₂) = 0.
      -- If f₂ ≤ g and f₂+f₃ > g, C(g-f₂,f₃) = 0.
      -- If f₂ ≤ g and f₂+f₃ ≤ g, then g-f₂-f₃ < f₁ so C(g-f₂-f₃,f₁) = 0.
      rcases le_or_gt f₂ g with hf₂ | hf₂
      · rcases le_or_gt (f₂ + f₃) g with h23 | h23
        · have : Nat.choose (g - f₂ - f₃) f₁ = 0 := by rw [Nat.choose_eq_zero_iff]; omega
          simp [this]
        · have : Nat.choose (g - f₂) f₃ = 0 := by rw [Nat.choose_eq_zero_iff]; omega
          simp [this]
      · have : Nat.choose g f₂ = 0 := by rw [Nat.choose_eq_zero_iff]; omega
        simp [this]
    rw [lhs_zero, rhs_zero]

set_option maxHeartbeats 12800000 in
/-- **Generic orbit counting factoring for TJC**: Σ JC₁₂·JC_H₃/Aut = TJC. -/
private theorem genOrbit_counting_factoring {R : RelUniverse} (σ : GenFlagType R)
    (F₁ F₂ F₃ G : GenFlag R σ) (hℓ : σ.size ≤ F₁.size + F₂.size - σ.size) :
    (genClassesOfSize R σ (F₁.size + F₂.size - σ.size) hℓ).sum (fun H =>
        ((genJointCount R σ F₁ F₂ H.out : ℝ) * (genJointCount R σ H.out F₃ G : ℝ)) /
        (genFlagAutCount R σ H.out : ℝ)) =
    (genTripleJointCount σ F₁ F₂ F₃ G : ℝ) := by
  -- Abbreviations
  set n := F₁.size + F₂.size - σ.size with hn_def
  -- GenTJCSub abbreviation
  let GenTJCSub := { t : GenInducedEmbedding R σ F₁ G × GenInducedEmbedding R σ F₂ G ×
        GenInducedEmbedding R σ F₃ G //
    (∀ i : Fin G.size,
      (i ∈ Set.range t.1.toFun ∧ i ∈ Set.range t.2.1.toFun) ↔ i ∈ Set.range G.embedding) ∧
    (∀ i : Fin G.size,
      (i ∈ Set.range t.1.toFun ∧ i ∈ Set.range t.2.2.toFun) ↔ i ∈ Set.range G.embedding) ∧
    (∀ i : Fin G.size,
      (i ∈ Set.range t.2.1.toFun ∧ i ∈ Set.range t.2.2.toFun) ↔ i ∈ Set.range G.embedding) ∧
    (∀ i : Fin G.size,
      i ∈ Set.range t.1.toFun ∨ i ∈ Set.range t.2.1.toFun ∨ i ∈ Set.range t.2.2.toFun) }
  -- GenJCSub abbreviations
  let GenJC12 (H : GenFlag R σ) := { p : GenInducedEmbedding R σ F₁ H × GenInducedEmbedding R σ F₂ H //
    (∀ i : Fin H.size,
      (i ∈ Set.range p.1.toFun ∧ i ∈ Set.range p.2.toFun) ↔
        i ∈ Set.range H.embedding) ∧
    (∀ i : Fin H.size,
      i ∈ Set.range p.1.toFun ∨ i ∈ Set.range p.2.toFun) }
  let GenJCH3 (H : GenFlag R σ) := { p : GenInducedEmbedding R σ H G × GenInducedEmbedding R σ F₃ G //
    (∀ i : Fin G.size,
      (i ∈ Set.range p.1.toFun ∧ i ∈ Set.range p.2.toFun) ↔
        i ∈ Set.range G.embedding) ∧
    (∀ i : Fin G.size,
      i ∈ Set.range p.1.toFun ∨ i ∈ Set.range p.2.toFun) }
  -- Intermediate finset: union of ranges of e₁ and e₂
  let gnf : GenTJCSub → Finset (Fin G.size) :=
    fun t => Finset.univ.filter (fun v => v ∈ Set.range t.val.1.toFun ∨ v ∈ Set.range t.val.2.1.toFun)
  have gnf_sigma : ∀ t : GenTJCSub, ∀ i : Fin σ.size, G.embedding i ∈ gnf t := by
    intro t i; simp only [gnf, Finset.mem_filter, Finset.mem_univ, true_and]
    left; exact ⟨F₁.embedding i, t.val.1.compat i⟩
  have gnf_card : ∀ t : GenTJCSub, (gnf t).card = n := by
    intro t
    let A := Finset.univ.filter (fun v => v ∈ Set.range t.val.1.toFun)
    let B := Finset.univ.filter (fun v => v ∈ Set.range t.val.2.1.toFun)
    have hAB : gnf t = A ∪ B := by
      ext v; simp only [gnf, A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [hAB]
    have hA : A.card = F₁.size := by
      have : A = Finset.univ.image t.val.1.toFun := by
        ext v; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]; rfl
      rw [this, Finset.card_image_of_injective _ t.val.1.injective, Finset.card_fin]
    have hB : B.card = F₂.size := by
      have : B = Finset.univ.image t.val.2.1.toFun := by
        ext v; simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]; rfl
      rw [this, Finset.card_image_of_injective _ t.val.2.1.injective, Finset.card_fin]
    have hAinterB : (A ∩ B).card = σ.size := by
      have hAB_eq : A ∩ B = Finset.univ.image G.embedding := by
        ext v; simp only [A, B, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_image]
        exact t.property.1 v
      rw [hAB_eq, Finset.card_image_of_injective _ G.embedding.injective, Finset.card_fin]
    have hunion := Finset.card_union_add_card_inter A B
    omega
  -- Intermediate class
  let gnic : GenTJCSub → GenFlagClass R σ :=
    fun t => GenFlagClass.mk (G.genInducedSubflag (gnf t) (gnf_sigma t) ((gnf_card t).symm ▸ hℓ))
  have gnic_mem : ∀ t : GenTJCSub,
      gnic t ∈ genClassesOfSize R σ n hℓ := by
    intro t
    let H := G.genInducedSubflag (gnf t) (gnf_sigma t) ((gnf_card t).symm ▸ hℓ)
    have hsize : H.size = n := gnf_card t
    have hmem := mk_F_mem_genClassesOfSize H H.hsize
    convert hmem using 2; exact hsize.symm
  -- Generic pullback
  let pb : {F₀ : GenFlag R σ} → {H : GenFlag R σ} →
      (b : GenInducedEmbedding R σ H G) →
      (e : GenInducedEmbedding R σ F₀ G) →
      (∀ x, e.toFun x ∈ Set.range b.toFun) →
      GenInducedEmbedding R σ F₀ H :=
    fun {F₀} {H} b e hr =>
    { toFun := fun x => Classical.choose (hr x)
      injective := fun x y h => e.injective (by
        have := congr_arg b.toFun h
        rwa [Classical.choose_spec (hr x), Classical.choose_spec (hr y)] at this)
      isInduced := by
        have h1 : R.comap (fun x => Classical.choose (hr x)) H.str =
            R.comap (fun x => Classical.choose (hr x)) (R.comap b.toFun G.str) := by
          congr 1; exact b.isInduced.symm
        rw [h1, ← R.comap_comp]
        have h2 : b.toFun ∘ (fun x => Classical.choose (hr x)) = e.toFun :=
          funext (fun x => Classical.choose_spec (hr x))
        rw [h2]; exact e.isInduced
      compat := fun i => b.injective (by
        rw [Classical.choose_spec (hr (F₀.embedding i)), e.compat]
        exact (b.compat i).symm) }
  have pb_spec : ∀ {F₀ H : GenFlag R σ} (b : GenInducedEmbedding R σ H G)
      (e : GenInducedEmbedding R σ F₀ G) (hr : ∀ x, e.toFun x ∈ Set.range b.toFun),
      ∀ x, b.toFun ((pb b e hr).toFun x) = e.toFun x :=
    fun b e hr x => Classical.choose_spec (hr x)
  -- GenIE equality helper
  have gie_ext : ∀ {F₀ G₀ : GenFlag R σ} (e₁ e₂ : GenInducedEmbedding R σ F₀ G₀),
      e₁.toFun = e₂.toFun → e₁ = e₂ := by
    intro F₀ G₀ e₁ e₂ h; cases e₁; cases e₂
    simp only [GenInducedEmbedding.mk.injEq]; exact h
  -- incl range = Finset as Set
  have incl_range : ∀ (S : Finset (Fin G.size))
      (hS : ∀ i : Fin σ.size, G.embedding i ∈ S) (hσ : σ.size ≤ S.card),
      Set.range (G.genInducedSubflag_incl S hS hσ).toFun = ↑S := by
    intro S hS hσ; ext v; simp only [Set.mem_range, Finset.mem_coe]; constructor
    · rintro ⟨z, rfl⟩; exact Finset.orderEmbOfFin_mem _ rfl z
    · intro hv; exact ⟨(S.orderIsoOfFin rfl).symm ⟨v, hv⟩, by
        change ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨v, hv⟩)) = v
        simp [OrderIso.apply_symm_apply]⟩
  -- Compose overlap: b ∘ a₁, b ∘ a₂ have overlap = σ-image in G
  have comp_overlap_12 : ∀ {H : GenFlag R σ}
      (a₁ : GenInducedEmbedding R σ F₁ H) (a₂ : GenInducedEmbedding R σ F₂ H)
      (b : GenInducedEmbedding R σ H G)
      (ho : ∀ i : Fin H.size, (i ∈ Set.range a₁.toFun ∧ i ∈ Set.range a₂.toFun) ↔ i ∈ Set.range H.embedding),
      ∀ i : Fin G.size,
        (i ∈ Set.range (b.comp a₁).toFun ∧ i ∈ Set.range (b.comp a₂).toFun) ↔
          i ∈ Set.range G.embedding := by
    intro H a₁ a₂ b ho i
    simp only [GenInducedEmbedding.comp, Set.range_comp]; constructor
    · intro ⟨⟨x₁, hx₁, hx₁_eq⟩, ⟨x₂, hx₂, hx₂_eq⟩⟩
      have h_eq : x₁ = x₂ := b.injective (hx₁_eq.trans hx₂_eq.symm)
      subst h_eq
      obtain ⟨j, rfl⟩ := (ho x₁).mp ⟨hx₁, hx₂⟩
      exact ⟨j, (b.compat j).symm.trans hx₁_eq⟩
    · intro ⟨j, hj⟩
      have hemb := (ho (H.embedding j)).mpr ⟨j, rfl⟩
      exact ⟨⟨_, hemb.1, (b.compat j).trans hj⟩, ⟨_, hemb.2, (b.compat j).trans hj⟩⟩
  -- Compose overlap for (b∘a₁, e₃): uses the H-F₃ overlap in G and JC12 overlap
  have comp_overlap_13 : ∀ {H : GenFlag R σ}
      (a₁ : GenInducedEmbedding R σ F₁ H) (a₂ : GenInducedEmbedding R σ F₂ H)
      (b : GenInducedEmbedding R σ H G) (e₃ : GenInducedEmbedding R σ F₃ G)
      (ho12 : ∀ i : Fin H.size, (i ∈ Set.range a₁.toFun ∧ i ∈ Set.range a₂.toFun) ↔ i ∈ Set.range H.embedding)
      (ho_b_e3 : ∀ i : Fin G.size,
        (i ∈ Set.range b.toFun ∧ i ∈ Set.range e₃.toFun) ↔ i ∈ Set.range G.embedding),
      ∀ i : Fin G.size,
        (i ∈ Set.range (b.comp a₁).toFun ∧ i ∈ Set.range e₃.toFun) ↔
          i ∈ Set.range G.embedding := by
    intro H a₁ a₂ b e₃ ho12 ho_b_e3 i; constructor
    · intro ⟨hba₁, he₃⟩
      exact (ho_b_e3 i).mp ⟨by
        obtain ⟨x, rfl⟩ := hba₁
        exact ⟨a₁.toFun x, by simp [GenInducedEmbedding.comp]⟩, he₃⟩
    · intro ⟨j, hj⟩
      obtain ⟨⟨w, hw⟩, he₃⟩ := (ho_b_e3 i).mpr ⟨j, hj⟩
      have hw_eq : w = H.embedding j := b.injective (hw.trans (hj.symm.trans (b.compat j).symm))
      obtain ⟨x, hx⟩ := ((ho12 (H.embedding j)).mpr ⟨j, rfl⟩).1
      exact ⟨⟨x, by simp only [GenInducedEmbedding.comp, Function.comp_apply]; rw [hx, hw_eq.symm]; exact hw⟩, he₃⟩
  -- Compose overlap for (b∘a₂, e₃)
  have comp_overlap_23 : ∀ {H : GenFlag R σ}
      (a₁ : GenInducedEmbedding R σ F₁ H) (a₂ : GenInducedEmbedding R σ F₂ H)
      (b : GenInducedEmbedding R σ H G) (e₃ : GenInducedEmbedding R σ F₃ G)
      (ho12 : ∀ i : Fin H.size, (i ∈ Set.range a₁.toFun ∧ i ∈ Set.range a₂.toFun) ↔ i ∈ Set.range H.embedding)
      (ho_b_e3 : ∀ i : Fin G.size,
        (i ∈ Set.range b.toFun ∧ i ∈ Set.range e₃.toFun) ↔ i ∈ Set.range G.embedding),
      ∀ i : Fin G.size,
        (i ∈ Set.range (b.comp a₂).toFun ∧ i ∈ Set.range e₃.toFun) ↔
          i ∈ Set.range G.embedding := by
    intro H a₁ a₂ b e₃ ho12 ho_b_e3 i; constructor
    · intro ⟨hba₂, he₃⟩
      exact (ho_b_e3 i).mp ⟨by
        obtain ⟨x, rfl⟩ := hba₂
        exact ⟨a₂.toFun x, by simp [GenInducedEmbedding.comp]⟩, he₃⟩
    · intro ⟨j, hj⟩
      obtain ⟨⟨w, hw⟩, he₃⟩ := (ho_b_e3 i).mpr ⟨j, hj⟩
      have hw_eq : w = H.embedding j := b.injective (hw.trans (hj.symm.trans (b.compat j).symm))
      obtain ⟨y, hy⟩ := ((ho12 (H.embedding j)).mpr ⟨j, rfl⟩).2
      exact ⟨⟨y, by simp only [GenInducedEmbedding.comp, Function.comp_apply]; rw [hy, hw_eq.symm]; exact hw⟩, he₃⟩
  -- Compose covering
  have comp_covering : ∀ {H : GenFlag R σ}
      (a₁ : GenInducedEmbedding R σ F₁ H) (a₂ : GenInducedEmbedding R σ F₂ H)
      (b : GenInducedEmbedding R σ H G) (e₃ : GenInducedEmbedding R σ F₃ G)
      (hcov_jc : ∀ i : Fin H.size, i ∈ Set.range a₁.toFun ∨ i ∈ Set.range a₂.toFun)
      (hcov_bH : ∀ i : Fin G.size, i ∈ Set.range b.toFun ∨ i ∈ Set.range e₃.toFun),
      ∀ i : Fin G.size,
        i ∈ Set.range (b.comp a₁).toFun ∨ i ∈ Set.range (b.comp a₂).toFun ∨ i ∈ Set.range e₃.toFun := by
    intro H a₁ a₂ b e₃ hcov_jc hcov_bH i
    rcases hcov_bH i with ⟨w, hw⟩ | he₃
    · rcases hcov_jc w with ⟨x, rfl⟩ | ⟨y, rfl⟩
      · left; exact ⟨x, by simp only [GenInducedEmbedding.comp, Function.comp_apply]; exact hw⟩
      · right; left; exact ⟨y, by simp only [GenInducedEmbedding.comp, Function.comp_apply]; exact hw⟩
    · right; right; exact he₃
  -- Compose map: GenJC12 H × GenJCH3 H → GenTJCSub
  let cmap : {H : GenFlag R σ} → GenJC12 H × GenJCH3 H → GenTJCSub :=
    fun {H} ⟨jc12, jcH3⟩ =>
      ⟨(jcH3.val.1.comp jc12.val.1, jcH3.val.1.comp jc12.val.2, jcH3.val.2),
        comp_overlap_12 jc12.val.1 jc12.val.2 jcH3.val.1 jc12.property.1,
        comp_overlap_13 jc12.val.1 jc12.val.2 jcH3.val.1 jcH3.val.2 jc12.property.1 jcH3.property.1,
        comp_overlap_23 jc12.val.1 jc12.val.2 jcH3.val.1 jcH3.val.2 jc12.property.1 jcH3.property.1,
        comp_covering jc12.val.1 jc12.val.2 jcH3.val.1 jcH3.val.2 jc12.property.2 jcH3.property.2⟩
  -- Per-class counting
  have hper : ∀ cls ∈ genClassesOfSize R σ n hℓ,
      ((genJointCount R σ F₁ F₂ cls.out : ℝ) * (genJointCount R σ cls.out F₃ G : ℝ)) /
        (genFlagAutCount R σ cls.out : ℝ) =
      ((Finset.univ.filter (fun t : GenTJCSub => gnic t = cls)).card : ℝ) := by
    intro cls hcls
    set H := cls.out
    set fiber := Finset.univ.filter (fun t : GenTJCSub => gnic t = cls)
    have hH_size : H.size = n := genClassesOfSize_out_size hcls
    -- cmap lands in fiber for H
    have hmap : ∀ pair : GenJC12 H × GenJCH3 H, cmap pair ∈ fiber := by
      intro ⟨jc12, jcH3⟩
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
      change gnic (cmap (jc12, jcH3)) = cls
      change GenFlagClass.mk _ = cls
      rw [show cls = GenFlagClass.mk H from (Quotient.out_eq cls).symm, GenFlagClass.mk_eq]
      -- range(b) = gnf(cmap(jc12, jcH3)) by covering of jc12
      have hb_range : Set.range jcH3.val.1.toFun = ↑(gnf (cmap (jc12, jcH3))) := by
        ext v; simp only [gnf, cmap, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
          true_and, GenInducedEmbedding.comp, Set.range_comp]; constructor
        · rintro ⟨w, rfl⟩
          rcases jc12.property.2 w with ⟨x, rfl⟩ | ⟨x, rfl⟩
          · left; exact ⟨_, Set.mem_range_self x, rfl⟩
          · right; exact ⟨_, Set.mem_range_self x, rfl⟩
        · intro h; rcases h with ⟨_, ⟨x, rfl⟩, rfl⟩ | ⟨_, ⟨x, rfl⟩, rfl⟩
          · exact ⟨jc12.val.1.toFun x, rfl⟩
          · exact ⟨jc12.val.2.toFun x, rfl⟩
      -- Pullback incl through b to get GenIE from Sub to H
      let Sub := G.genInducedSubflag (gnf (cmap (jc12, jcH3))) (gnf_sigma _) ((gnf_card _).symm ▸ hℓ)
      let incl := G.genInducedSubflag_incl (gnf (cmap (jc12, jcH3))) (gnf_sigma _) ((gnf_card _).symm ▸ hℓ)
      have hincl_in_b : ∀ x : Fin Sub.size, incl.toFun x ∈ Set.range jcH3.val.1.toFun := by
        intro x; rw [hb_range]
        exact (incl_range _ _ _).symm ▸ Set.mem_range_self x
      let φ := pb jcH3.val.1 incl hincl_in_b
      have hsize_eq : Sub.size = H.size := by
        change (gnf (cmap (jc12, jcH3))).card = H.size
        rw [gnf_card]; exact hH_size.symm
      have φ_surj : Function.Surjective φ.toFun := by
        have := Finite.surjective_of_injective
          (f := φ.toFun ∘ Fin.cast hsize_eq.symm)
          (φ.injective.comp (Fin.cast_injective _))
        intro y; obtain ⟨x, hx⟩ := this y; exact ⟨Fin.cast hsize_eq.symm x, hx⟩
      exact ⟨Equiv.ofBijective φ.toFun ⟨φ.injective, φ_surj⟩, φ.isInduced, φ.compat⟩
    -- Fiber counting
    have hfib_count :
        Fintype.card (GenJC12 H × GenJCH3 H) =
        fiber.sum (fun t =>
          (Finset.univ.filter (fun pair : GenJC12 H × GenJCH3 H =>
            cmap pair = t)).card) :=
      Finset.card_eq_sum_card_fiberwise (fun pair _ => hmap pair)
    have hJC_prod : Fintype.card (GenJC12 H × GenJCH3 H) =
        genJointCount R σ F₁ F₂ H * genJointCount R σ H F₃ G := by
      rw [Fintype.card_prod]; rfl
    -- Each preimage has constant size = Aut(H)
    suffices hconst : ∀ t ∈ fiber,
        (Finset.univ.filter (fun pair : GenJC12 H × GenJCH3 H =>
          cmap pair = t)).card = genFlagAutCount R σ H by
      rw [div_eq_iff (ne_of_gt (Nat.cast_pos.mpr (genFlagAutCount_pos σ H)))]
      calc (genJointCount R σ F₁ F₂ H : ℝ) * (genJointCount R σ H F₃ G : ℝ)
          = ↑(Fintype.card (GenJC12 H × GenJCH3 H)) := by rw [hJC_prod]; push_cast; ring
        _ = ↑(fiber.sum (fun t => (Finset.univ.filter (fun pair : GenJC12 H × GenJCH3 H => cmap pair = t)).card)) := by
            exact_mod_cast hfib_count
        _ = (fiber.sum (fun t => (genFlagAutCount R σ H : ℝ))) := by
            push_cast; exact Finset.sum_congr rfl (fun t ht => by rw [hconst t ht])
        _ = ↑(genFlagAutCount R σ H) * ↑fiber.card := by
            rw [Finset.sum_const]; simp [nsmul_eq_mul, mul_comm]
        _ = (Finset.univ.filter fun t => gnic t = cls).card * ↑(genFlagAutCount R σ H) := by ring
    -- Prove each preimage has size Aut(H) by antisymmetric injections
    intro t ht
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    -- gnic t = cls means [G[gnf t]] ≅ H
    have hiso : GenFlagIso σ (G.genInducedSubflag (gnf t) (gnf_sigma t) ((gnf_card t).symm ▸ hℓ)) H :=
      (GenFlagClass.mk_eq _ _).mp (show gnic t = GenFlagClass.mk H from ht.trans (Quotient.out_eq cls).symm)
    obtain ⟨φ_iso, hstr_iso, hcompat_iso⟩ := hiso
    -- b₀ : GenIE H G via mapIso with φ_iso.symm + incl
    let incl_t := G.genInducedSubflag_incl (gnf t) (gnf_sigma t) ((gnf_card t).symm ▸ hℓ)
    have hstr_inv : R.comap (⇑φ_iso.symm) (G.genInducedSubflag (gnf t) (gnf_sigma t) ((gnf_card t).symm ▸ hℓ)).str = H.str := by
      rw [← hstr_iso, ← R.comap_comp]
      have : (⇑φ_iso ∘ ⇑φ_iso.symm) = id := funext (fun x => φ_iso.apply_symm_apply x)
      rw [this, R.comap_id]
    have hcompat_inv : ∀ i, φ_iso.symm (H.embedding i) = (G.genInducedSubflag (gnf t) (gnf_sigma t) ((gnf_card t).symm ▸ hℓ)).embedding i := by
      intro i; exact φ_iso.symm_apply_eq.mpr (hcompat_iso i).symm
    let b₀ : GenInducedEmbedding R σ H G := GenInducedEmbedding.mapIso φ_iso.symm hstr_inv hcompat_inv incl_t
    have hb₀_range : Set.range b₀.toFun = ↑(gnf t) := by
      change Set.range (GenInducedEmbedding.mapIso φ_iso.symm hstr_inv hcompat_inv incl_t).toFun = ↑(gnf t)
      rw [GenInducedEmbedding.range_mapIso]; exact incl_range _ _ _
    -- For any pair mapping to t, the b-component has range = range(b₀)
    have pair_b_range : ∀ pair : GenJC12 H × GenJCH3 H,
        cmap pair = t → Set.range pair.2.val.1.toFun = Set.range b₀.toFun := by
      intro ⟨jc12, jcH3⟩ hpair; rw [hb₀_range]
      ext v; simp only [gnf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      -- hpair says cmap(jc12,jcH3) = t, so the components match
      have h_e1 : ∀ x, jcH3.val.1.toFun (jc12.val.1.toFun x) = t.val.1.toFun x := by
        intro x; have := congr_arg Subtype.val hpair
        exact congr_fun (congr_arg GenInducedEmbedding.toFun (congr_arg Prod.fst this)) x
      have h_e2 : ∀ x, jcH3.val.1.toFun (jc12.val.2.toFun x) = t.val.2.1.toFun x := by
        intro x; have := congr_arg Subtype.val hpair
        exact congr_fun (congr_arg GenInducedEmbedding.toFun (congr_arg (Prod.fst ∘ Prod.snd) this)) x
      constructor
      · rintro ⟨w, rfl⟩
        rcases jc12.property.2 w with ⟨z, rfl⟩ | ⟨z, rfl⟩
        · left; exact ⟨z, (h_e1 z).symm⟩
        · right; exact ⟨z, (h_e2 z).symm⟩
      · intro h; rcases h with ⟨x, hx⟩ | ⟨x, hx⟩
        · exact ⟨jc12.val.1.toFun x, (h_e1 x).trans hx⟩
        · exact ⟨jc12.val.2.toFun x, (h_e2 x).trans hx⟩
    -- Pairs mapping to t are determined by their b-component (jcH3.1)
    have pair_det : ∀ p₁ p₂ : GenJC12 H × GenJCH3 H,
        cmap p₁ = t → cmap p₂ = t → p₁.2.val.1 = p₂.2.val.1 → p₁ = p₂ := by
      intro p₁ p₂ hp₁ hp₂ hb_eq
      -- Extract component equalities from cmap p = t
      have hp₁_1 : ∀ x, p₁.2.val.1.toFun (p₁.1.val.1.toFun x) = t.val.1.toFun x :=
        fun x => congr_fun (congr_arg GenInducedEmbedding.toFun
          (congr_arg Prod.fst (congr_arg Subtype.val hp₁))) x
      have hp₂_1 : ∀ x, p₂.2.val.1.toFun (p₂.1.val.1.toFun x) = t.val.1.toFun x :=
        fun x => congr_fun (congr_arg GenInducedEmbedding.toFun
          (congr_arg Prod.fst (congr_arg Subtype.val hp₂))) x
      have hp₁_2 : ∀ x, p₁.2.val.1.toFun (p₁.1.val.2.toFun x) = t.val.2.1.toFun x :=
        fun x => congr_fun (congr_arg GenInducedEmbedding.toFun
          (congr_arg (Prod.fst ∘ Prod.snd) (congr_arg Subtype.val hp₁))) x
      have hp₂_2 : ∀ x, p₂.2.val.1.toFun (p₂.1.val.2.toFun x) = t.val.2.1.toFun x :=
        fun x => congr_fun (congr_arg GenInducedEmbedding.toFun
          (congr_arg (Prod.fst ∘ Prod.snd) (congr_arg Subtype.val hp₂))) x
      have ha₁_fun : p₁.1.val.1.toFun = p₂.1.val.1.toFun := by
        funext x; apply p₂.2.val.1.injective
        calc p₂.2.val.1.toFun (p₁.1.val.1.toFun x)
            = p₁.2.val.1.toFun (p₁.1.val.1.toFun x) := by rw [hb_eq]
          _ = t.val.1.toFun x := hp₁_1 x
          _ = p₂.2.val.1.toFun (p₂.1.val.1.toFun x) := (hp₂_1 x).symm
      have ha₂_fun : p₁.1.val.2.toFun = p₂.1.val.2.toFun := by
        funext x; apply p₂.2.val.1.injective
        calc p₂.2.val.1.toFun (p₁.1.val.2.toFun x)
            = p₁.2.val.1.toFun (p₁.1.val.2.toFun x) := by rw [hb_eq]
          _ = t.val.2.1.toFun x := hp₁_2 x
          _ = p₂.2.val.1.toFun (p₂.1.val.2.toFun x) := (hp₂_2 x).symm
      have heq1 : p₁.1.val.1 = p₂.1.val.1 := gie_ext _ _ ha₁_fun
      have heq2 : p₁.1.val.2 = p₂.1.val.2 := gie_ext _ _ ha₂_fun
      have he₃ : p₁.2.val.2 = p₂.2.val.2 := by
        have h1 : (cmap p₁).val.2.2 = p₁.2.val.2 := rfl
        have h2 : (cmap p₂).val.2.2 = p₂.2.val.2 := rfl
        rw [← h1, ← h2]
        exact (congr_arg (Prod.snd ∘ Prod.snd) (congr_arg Subtype.val hp₁)).trans
          (congr_arg (Prod.snd ∘ Prod.snd) (congr_arg Subtype.val hp₂)).symm
      exact Prod.ext (Subtype.ext (Prod.ext heq1 heq2)) (Subtype.ext (Prod.ext hb_eq he₃))
    -- Helper: range(b₀∘α) = range(b₀) for any automorphism α
    have hcomp_range : ∀ α : GenInducedEmbedding R σ H H,
        Set.range (b₀.comp α).toFun = Set.range b₀.toFun := by
      intro α; ext v
      simp only [GenInducedEmbedding.comp, Set.mem_range, Function.comp_apply]; constructor
      · rintro ⟨y, rfl⟩; exact ⟨α.toFun y, rfl⟩
      · rintro ⟨y, rfl⟩
        obtain ⟨z, rfl⟩ := (Finite.injective_iff_surjective.mp α.injective) y
        exact ⟨z, rfl⟩
    -- t.val.1 and t.val.2.1 images are in range(b₀)
    have ht1_in_b₀ : ∀ x, t.val.1.toFun x ∈ Set.range b₀.toFun := by
      intro x; rw [hb₀_range]
      simp only [gnf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      left; exact Set.mem_range_self x
    have ht2_in_b₀ : ∀ x, t.val.2.1.toFun x ∈ Set.range b₀.toFun := by
      intro x; rw [hb₀_range]
      simp only [gnf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      right; exact Set.mem_range_self x
    -- comp ∘ pb = id
    have comp_pb_toFun : ∀ {F₀ : GenFlag R σ} (b : GenInducedEmbedding R σ H G)
        (e : GenInducedEmbedding R σ F₀ G) (hr : ∀ x, e.toFun x ∈ Set.range b.toFun),
        (b.comp (pb b e hr)).toFun = e.toFun :=
      fun b e hr => funext (fun x => pb_spec b e hr x)
    -- Antisymmetric injections: fiber_size = Aut(H)
    apply Nat.le_antisymm
    -- Upper bound: fiber ≤ Aut(H)
    · rw [← Fintype.card_coe]
      apply Fintype.card_le_of_injective
        (fun ⟨pair, hmem⟩ =>
          pb b₀ pair.2.val.1 (fun x => by
            have hcmap_t : cmap pair = t := by
              simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem
            have hrange_eq := pair_b_range pair hcmap_t
            exact hrange_eq ▸ Set.mem_range_self x))
      intro ⟨p₁, hm₁⟩ ⟨p₂, hm₂⟩ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hm₂
      simp only [Subtype.mk.injEq]
      -- From pb(b₀,p₁.2.1) = pb(b₀,p₂.2.1), deduce p₁.2.1 = p₂.2.1
      have hr₁ : ∀ x, p₁.2.val.1.toFun x ∈ Set.range b₀.toFun :=
        fun x => (pair_b_range p₁ hm₁) ▸ Set.mem_range_self x
      have hr₂ : ∀ x, p₂.2.val.1.toFun x ∈ Set.range b₀.toFun :=
        fun x => (pair_b_range p₂ hm₂) ▸ Set.mem_range_self x
      have hb_eq : p₁.2.val.1 = p₂.2.val.1 := by
        have hfun_eq : p₁.2.val.1.toFun = p₂.2.val.1.toFun := by
          funext x
          have h := pb_spec b₀ p₁.2.val.1 hr₁ x
          have h' := pb_spec b₀ p₂.2.val.1 hr₂ x
          have hpb_eq : ∀ y, (pb b₀ p₁.2.val.1 hr₁).toFun y = (pb b₀ p₂.2.val.1 hr₂).toFun y :=
            fun y => congr_fun (congr_arg GenInducedEmbedding.toFun heq) y
          rw [hpb_eq] at h; exact h.symm.trans h'
        exact gie_ext _ _ hfun_eq
      exact pair_det p₁ p₂ hm₁ hm₂ hb_eq
    -- Lower bound: Aut(H) ≤ fiber
    · rw [← Fintype.card_coe]
      -- For each α, pull back t's components through b₀ ∘ α
      have ht1_in_comp : ∀ (α : GenInducedEmbedding R σ H H),
          ∀ x, t.val.1.toFun x ∈ Set.range (b₀.comp α).toFun :=
        fun α x => by rw [hcomp_range]; exact ht1_in_b₀ x
      have ht2_in_comp : ∀ (α : GenInducedEmbedding R σ H H),
          ∀ x, t.val.2.1.toFun x ∈ Set.range (b₀.comp α).toFun :=
        fun α x => by rw [hcomp_range]; exact ht2_in_b₀ x
      -- Overlap condition for decomposed pair (F₁, F₂ in H)
      have decompose_overlap : ∀ α : GenInducedEmbedding R σ H H,
          ∀ i : Fin H.size,
          (i ∈ Set.range (pb (b₀.comp α) t.val.1 (ht1_in_comp α)).toFun ∧
           i ∈ Set.range (pb (b₀.comp α) t.val.2.1 (ht2_in_comp α)).toFun) ↔
            i ∈ Set.range H.embedding := by
        intro α i; set bα := b₀.comp α; constructor
        · intro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
          have hbi₁ : bα.toFun i ∈ Set.range t.val.1.toFun :=
            ⟨x₁, (pb_spec bα t.val.1 (ht1_in_comp α) x₁).symm.trans (congr_arg bα.toFun hx₁)⟩
          have hbi₂ : bα.toFun i ∈ Set.range t.val.2.1.toFun :=
            ⟨x₂, (pb_spec bα t.val.2.1 (ht2_in_comp α) x₂).symm.trans (congr_arg bα.toFun hx₂)⟩
          obtain ⟨j, hj⟩ := (t.property.1 (bα.toFun i)).mp ⟨hbi₁, hbi₂⟩
          exact ⟨j, bα.injective ((bα.compat j).trans hj)⟩
        · intro ⟨j, hj⟩
          have hemb := (t.property.1 (G.embedding j)).mpr ⟨j, rfl⟩
          constructor
          · obtain ⟨x, hx⟩ := hemb.1
            exact ⟨x, bα.injective (by rw [pb_spec, ← hj, hx]; exact (bα.compat j).symm)⟩
          · obtain ⟨x, hx⟩ := hemb.2
            exact ⟨x, bα.injective (by rw [pb_spec, ← hj, hx]; exact (bα.compat j).symm)⟩
      -- Cover condition for decomposed pair (F₁, F₂ cover H)
      have decompose_cover : ∀ α : GenInducedEmbedding R σ H H,
          ∀ i : Fin H.size,
          i ∈ Set.range (pb (b₀.comp α) t.val.1 (ht1_in_comp α)).toFun ∨
          i ∈ Set.range (pb (b₀.comp α) t.val.2.1 (ht2_in_comp α)).toFun := by
        intro α i; set bα := b₀.comp α
        have hbi_in_range : bα.toFun i ∈ Set.range b₀.toFun := by
          rw [← hcomp_range]; exact Set.mem_range_self i
        rw [hb₀_range] at hbi_in_range
        simp only [gnf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hbi_in_range
        rcases hbi_in_range with ⟨x₁, hx₁⟩ | ⟨x₂, hx₂⟩
        · left; exact ⟨x₁, bα.injective ((pb_spec bα t.val.1 (ht1_in_comp α) x₁).trans hx₁)⟩
        · right; exact ⟨x₂, bα.injective ((pb_spec bα t.val.2.1 (ht2_in_comp α) x₂).trans hx₂)⟩
      -- Overlap condition for (b₀∘α, e₃) in G
      have decompose_overlap_bH3 : ∀ α : GenInducedEmbedding R σ H H,
          (∀ i : Fin G.size,
            (i ∈ Set.range (b₀.comp α).toFun ∧ i ∈ Set.range t.val.2.2.toFun) ↔
              i ∈ Set.range G.embedding) := by
        intro α i
        rw [hcomp_range]; constructor
        · intro ⟨hb, he₃⟩
          rw [hb₀_range] at hb
          simp only [gnf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb
          rcases hb with ⟨x, hx⟩ | ⟨x, hx⟩
          · exact (t.property.2.1 i).mp ⟨⟨x, hx⟩, he₃⟩
          · exact (t.property.2.2.1 i).mp ⟨⟨x, hx⟩, he₃⟩
        · intro ⟨j, hj⟩
          rw [hb₀_range]
          refine ⟨?_, ?_⟩
          · simp only [gnf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
            left; exact ⟨F₁.embedding j, (t.val.1.compat j).trans hj⟩
          · exact ((t.property.2.1 i).mpr ⟨j, hj⟩).2
      -- Cover condition for (b₀∘α, e₃) in G
      have decompose_cover_bH3 : ∀ α : GenInducedEmbedding R σ H H,
          ∀ i : Fin G.size,
          i ∈ Set.range (b₀.comp α).toFun ∨ i ∈ Set.range t.val.2.2.toFun := by
        intro α i; rw [hcomp_range, hb₀_range]
        rcases t.property.2.2.2 i with h1 | h2 | h3
        · left; simp only [gnf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
          left; exact h1
        · left; simp only [gnf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
          right; exact h2
        · right; exact h3
      -- cmap ∘ decompose = id
      have decompose_compose : ∀ α : GenInducedEmbedding R σ H H,
          cmap (⟨(pb (b₀.comp α) t.val.1 (ht1_in_comp α),
                  pb (b₀.comp α) t.val.2.1 (ht2_in_comp α)),
                 decompose_overlap α, decompose_cover α⟩,
                ⟨(b₀.comp α, t.val.2.2),
                 decompose_overlap_bH3 α, decompose_cover_bH3 α⟩) = t := by
        intro α; apply Subtype.ext; apply Prod.ext
        · exact gie_ext _ _ (comp_pb_toFun (b₀.comp α) t.val.1 (ht1_in_comp α))
        · apply Prod.ext
          · exact gie_ext _ _ (comp_pb_toFun (b₀.comp α) t.val.2.1 (ht2_in_comp α))
          · rfl
      -- Injection from Aut(H) into fiber
      apply Fintype.card_le_of_injective (fun α =>
        ⟨(⟨(pb (b₀.comp α) t.val.1 (ht1_in_comp α),
            pb (b₀.comp α) t.val.2.1 (ht2_in_comp α)),
           decompose_overlap α, decompose_cover α⟩,
          ⟨(b₀.comp α, t.val.2.2),
           decompose_overlap_bH3 α, decompose_cover_bH3 α⟩),
         by simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact decompose_compose α⟩)
      intro α₁ α₂ heq
      simp only [Subtype.mk.injEq] at heq
      have hb_eq : b₀.comp α₁ = b₀.comp α₂ :=
        congr_arg (fun p => (p : GenJC12 H × GenJCH3 H).2.val.1) heq
      cases h₁ : α₁; cases h₂ : α₂
      simp only [GenInducedEmbedding.mk.injEq]; funext x
      have := congr_fun (congr_arg GenInducedEmbedding.toFun hb_eq) x
      simp only [GenInducedEmbedding.comp, Function.comp_apply, h₁, h₂] at this
      exact b₀.injective this
  -- Sum fibers = total
  rw [Finset.sum_congr rfl (fun cls hcls => hper cls hcls)]
  change _ = ((Finset.univ : Finset GenTJCSub).card : ℝ)
  exact_mod_cast (Finset.card_eq_sum_card_fiberwise
    (fun t _ => gnic_mem t)).symm

set_option maxHeartbeats 12800000 in
/-- **Generic basis associativity**: the two bracketings of a triple product on
    basis elements give the same Finsupp element.  Proved from the generic density
    chain rule (which chains through orbit counting factoring). -/
private theorem genProduct_assoc_basis (R : RelUniverse) (σ : GenFlagType R) :
    ∀ (F₁ F₂ F₃ : GenFlag R σ),
      (genLocalFlagProduct R σ F₁ F₂).mul (GenFlagAlg.single F₃) =
        (GenFlagAlg.single F₁).mul (genLocalFlagProduct R σ F₂ F₃) := by
  -- The proof mirrors product_assoc_basis for simpleGraphUniverse (line 4625).
  -- Key chain: orbit_counting → triple_joint_factoring → coeff_chain_rule →
  --            density_chain_rule → product_assoc_basis
  -- We inline the entire chain here.
  intro F₁ F₂ F₃
  have hℓ : σ.size ≤ F₁.size + F₂.size - σ.size := by have := F₁.hsize; have := F₂.hsize; omega
  have hm : σ.size ≤ F₂.size + F₃.size - σ.size := by have := F₂.hsize; have := F₃.hsize; omega
  -- Bilinearity helpers
  have gen_add_mul : ∀ v w u : GenFlagAlg R σ, (v + w).mul u = v.mul u + w.mul u :=
    fun v w u => Finsupp.sum_add_index'
      (fun a => by simp [zero_mul, zero_smul, Finsupp.sum])
      (fun a b₁ b₂ => by simp_rw [_root_.add_mul, _root_.add_smul]; simp only [Finsupp.sum, Finset.sum_add_distrib])
  have gen_mul_add : ∀ v w u : GenFlagAlg R σ, v.mul (w + u) = v.mul w + v.mul u := by
    intro v w u; unfold GenFlagAlg.mul
    conv_lhs => arg 2; ext cls₁ c₁
                rw [Finsupp.sum_add_index' (fun a => by simp [mul_zero, zero_smul])
                  (fun a b₁ b₂ => by rw [_root_.mul_add, _root_.add_smul])]
    simp only [Finsupp.sum, Finset.sum_add_distrib]
  have gen_smul_mul : ∀ (c : ℝ) (v w : GenFlagAlg R σ), (c • v).mul w = c • (v.mul w) := by
    intro c v w; unfold GenFlagAlg.mul
    rw [Finsupp.sum_smul_index (fun _ => by simp [zero_mul, zero_smul, Finsupp.sum])]
    simp only [Finsupp.sum, Finset.smul_sum, smul_smul]
    congr 1; ext cls; congr 1; ext cls'; ring
  have gen_mul_smul : ∀ (c : ℝ) (v w : GenFlagAlg R σ), v.mul (c • w) = c • (v.mul w) := by
    intro c v w; unfold GenFlagAlg.mul
    conv_lhs => arg 2; ext cls₁ c₁
                rw [Finsupp.sum_smul_index (fun _ => by simp [mul_zero, zero_smul])]
    simp only [Finsupp.sum, Finset.smul_sum, smul_smul]
    congr 1; ext cls; congr 1; ext cls'; ring
  -- finset_sum_single helpers
  have finset_sum_single_mul : ∀ (S : Finset (GenFlagClass R σ))
      (coeff : GenFlagClass R σ → ℝ) (F : GenFlag R σ),
      GenFlagAlg.mul (S.sum (fun cls => Finsupp.single cls (coeff cls))) (GenFlagAlg.single F) =
      S.sum (fun cls => coeff cls • genLocalFlagProduct R σ cls.out F) := by
    intro S coeff F
    induction S using Finset.induction with
    | empty => simp only [Finset.sum_empty]; exact GenFlagAlg.mul_zero_left _
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, gen_add_mul, ih, Finset.sum_insert ha]; congr 1
      rw [show Finsupp.single a (coeff a) = coeff a • Finsupp.single a (1 : ℝ) from by
            rw [Finsupp.smul_single', mul_one], gen_smul_mul]; congr 1
      rw [show Finsupp.single a (1 : ℝ) = GenFlagAlg.single a.out from by
            unfold GenFlagAlg.single GenFlagClass.mk; congr 1; exact (Quotient.out_eq a).symm,
          GenFlagAlg.mul_single]
  have single_mul_finset_sum : ∀ (F : GenFlag R σ) (S : Finset (GenFlagClass R σ))
      (coeff : GenFlagClass R σ → ℝ),
      GenFlagAlg.mul (GenFlagAlg.single F) (S.sum (fun cls => Finsupp.single cls (coeff cls))) =
      S.sum (fun cls => coeff cls • genLocalFlagProduct R σ F cls.out) := by
    intro F S coeff
    induction S using Finset.induction with
    | empty => simp only [Finset.sum_empty]; exact GenFlagAlg.mul_zero_right _
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, gen_mul_add, ih, Finset.sum_insert ha]; congr 1
      rw [show Finsupp.single a (coeff a) = coeff a • Finsupp.single a (1 : ℝ) from by
            rw [Finsupp.smul_single', mul_one], gen_mul_smul]; congr 1
      rw [show Finsupp.single a (1 : ℝ) = GenFlagAlg.single a.out from by
            unfold GenFlagAlg.single GenFlagClass.mk; congr 1; exact (Quotient.out_eq a).symm,
          GenFlagAlg.mul_single]
  -- Unfold LFP as smul of sum and reduce
  rw [show genLocalFlagProduct R σ F₁ F₂ =
      ((genFlagAutCount R σ F₁ : ℝ) * (genFlagAutCount R σ F₂ : ℝ))⁻¹ •
        (genClassesOfSize R σ (F₁.size + F₂.size - σ.size) hℓ).sum (fun cls =>
          Finsupp.single cls (genJointInducedDensity R σ F₁ F₂ cls.out)) from by
      unfold genLocalFlagProduct; simp only [dif_pos hℓ],
      gen_smul_mul, show GenFlagAlg.mul _ _ = _ from finset_sum_single_mul _ _ _,
      show genLocalFlagProduct R σ F₂ F₃ =
      ((genFlagAutCount R σ F₂ : ℝ) * (genFlagAutCount R σ F₃ : ℝ))⁻¹ •
        (genClassesOfSize R σ (F₂.size + F₃.size - σ.size) hm).sum (fun cls =>
          Finsupp.single cls (genJointInducedDensity R σ F₂ F₃ cls.out)) from by
      unfold genLocalFlagProduct; simp only [dif_pos hm],
      gen_mul_smul, show GenFlagAlg.mul _ _ = _ from single_mul_finset_sum _ _ _]
  -- Now goal is the density chain rule
  -- We prove it via the coefficient chain rule → orbit counting factoring
  -- genLocalFlagProduct_apply (extract Finsupp coefficient)
  have lfp_apply : ∀ (A B : GenFlag R σ) (hAB : σ.size ≤ A.size + B.size - σ.size)
      (cls : GenFlagClass R σ),
      (genLocalFlagProduct R σ A B) cls =
        ((genFlagAutCount R σ A : ℝ) * (genFlagAutCount R σ B : ℝ))⁻¹ *
          (genClassesOfSize R σ (A.size + B.size - σ.size) hAB).sum (fun G =>
            if G = cls then genJointInducedDensity R σ A B G.out else 0) := by
    intro A B hAB cls
    simp only [genLocalFlagProduct, dif_pos hAB, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.finset_sum_apply, Finsupp.single_apply]
  -- The density chain rule (Finsupp level)
  ext cls
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.finset_sum_apply]
  set n₃ := F₁.size + F₂.size + F₃.size - 2 * σ.size
  have hn₃ : σ.size ≤ n₃ := by have := F₁.hsize; have := F₂.hsize; have := F₃.hsize; omega
  have hHF₃ : ∀ H ∈ genClassesOfSize R σ (F₁.size + F₂.size - σ.size) hℓ,
      σ.size ≤ H.out.size + F₃.size - σ.size :=
    fun H hm => by have := genClassesOfSize_out_size hm; have := F₃.hsize; omega
  have hF₁H' : ∀ H' ∈ genClassesOfSize R σ (F₂.size + F₃.size - σ.size) hm,
      σ.size ≤ F₁.size + H'.out.size - σ.size :=
    fun H' hm => by have := genClassesOfSize_out_size hm; have := F₁.hsize; omega
  -- Rewrite LHS and RHS using lfp_apply
  have lhs_eq : (∑ H ∈ genClassesOfSize R σ (F₁.size + F₂.size - σ.size) hℓ,
      genJointInducedDensity R σ F₁ F₂ H.out * (genLocalFlagProduct R σ H.out F₃) cls) =
    (∑ H ∈ genClassesOfSize R σ (F₁.size + F₂.size - σ.size) hℓ,
      genJointInducedDensity R σ F₁ F₂ H.out *
        ((genFlagAutCount R σ H.out : ℝ) * (genFlagAutCount R σ F₃ : ℝ))⁻¹ *
        (if cls ∈ genClassesOfSize R σ n₃ hn₃
         then genJointInducedDensity R σ H.out F₃ cls.out else 0)) := by
    apply Finset.sum_congr rfl; intro H hmem
    rw [lfp_apply H.out F₃ (hHF₃ H hmem) cls, Finset.sum_ite_eq', mul_assoc]
    rw [show genClassesOfSize R σ (H.out.size + F₃.size - σ.size) (hHF₃ H hmem) =
      genClassesOfSize R σ n₃ hn₃ from by
        congr 1; have := genClassesOfSize_out_size hmem; have := F₃.hsize; omega]
  have rhs_eq : (∑ H' ∈ genClassesOfSize R σ (F₂.size + F₃.size - σ.size) hm,
      genJointInducedDensity R σ F₂ F₃ H'.out * (genLocalFlagProduct R σ F₁ H'.out) cls) =
    (∑ H' ∈ genClassesOfSize R σ (F₂.size + F₃.size - σ.size) hm,
      genJointInducedDensity R σ F₂ F₃ H'.out *
        ((genFlagAutCount R σ F₁ : ℝ) * (genFlagAutCount R σ H'.out : ℝ))⁻¹ *
        (if cls ∈ genClassesOfSize R σ n₃ hn₃
         then genJointInducedDensity R σ F₁ H'.out cls.out else 0)) := by
    apply Finset.sum_congr rfl; intro H' hmem
    rw [lfp_apply F₁ H'.out (hF₁H' H' hmem) cls, Finset.sum_ite_eq', mul_assoc]
    rw [show genClassesOfSize R σ (F₁.size + H'.out.size - σ.size) (hF₁H' H' hmem) =
      genClassesOfSize R σ n₃ hn₃ from by
        congr 1; have := genClassesOfSize_out_size hmem; have := F₁.hsize; omega]
  rw [lhs_eq, rhs_eq]
  by_cases hmem : cls ∈ genClassesOfSize R σ n₃ hn₃
  · simp only [if_pos hmem]
    -- Coefficient chain rule: both sides = (aut₁·aut₂·aut₃)⁻¹ · TJD
    -- Step 1: triple_joint_factoring (density level)
    set G := cls.out
    have tjf : ∀ (A B C : GenFlag R σ) (hAB : σ.size ≤ A.size + B.size - σ.size),
        (genClassesOfSize R σ (A.size + B.size - σ.size) hAB).sum (fun H =>
          genJointInducedDensity R σ A B H.out * genJointInducedDensity R σ H.out C G /
            (genFlagAutCount R σ H.out : ℝ)) =
        genTripleJointInducedDensity σ A B C G := by
      intro A B C hAB
      set nAB := A.size + B.size - σ.size
      have h_ns : nAB - σ.size = (A.size - σ.size) + (B.size - σ.size) := by
        have := A.hsize; have := B.hsize; omega
      unfold genJointInducedDensity genTripleJointInducedDensity
      have h_rw : ∀ H ∈ genClassesOfSize R σ nAB hAB,
          (genJointCount R σ A B H.out : ℝ) /
            ((Nat.choose (H.out.size - σ.size) (A.size - σ.size) : ℝ) *
              (Nat.choose (H.out.size - σ.size - (A.size - σ.size)) (B.size - σ.size) : ℝ)) *
            ((genJointCount R σ H.out C G : ℝ) /
              ((Nat.choose (G.size - σ.size) (H.out.size - σ.size) : ℝ) *
                (Nat.choose (G.size - σ.size - (H.out.size - σ.size)) (C.size - σ.size) : ℝ))) /
            (genFlagAutCount R σ H.out : ℝ) =
          ((genJointCount R σ A B H.out : ℝ) * (genJointCount R σ H.out C G : ℝ)) /
            ((genFlagAutCount R σ H.out : ℝ) *
              ((Nat.choose (nAB - σ.size) (A.size - σ.size) : ℝ) *
                (Nat.choose (nAB - σ.size - (A.size - σ.size)) (B.size - σ.size) : ℝ) *
                ((Nat.choose (G.size - σ.size) (nAB - σ.size) : ℝ) *
                  (Nat.choose (G.size - σ.size - (nAB - σ.size)) (C.size - σ.size) : ℝ)))) :=
        fun H hH => by have hsz := genClassesOfSize_out_size hH; rw [hsz]; ring
      rw [Finset.sum_congr rfl h_rw]
      set M := (Nat.choose (nAB - σ.size) (A.size - σ.size) : ℝ) *
                (Nat.choose (nAB - σ.size - (A.size - σ.size)) (B.size - σ.size) : ℝ) *
                ((Nat.choose (G.size - σ.size) (nAB - σ.size) : ℝ) *
                  (Nat.choose (G.size - σ.size - (nAB - σ.size)) (C.size - σ.size) : ℝ))
      have h_factor : ∀ H ∈ genClassesOfSize R σ nAB hAB,
          ((genJointCount R σ A B H.out : ℝ) * (genJointCount R σ H.out C G : ℝ)) /
            ((genFlagAutCount R σ H.out : ℝ) * M) =
          ((genJointCount R σ A B H.out : ℝ) * (genJointCount R σ H.out C G : ℝ) /
            (genFlagAutCount R σ H.out : ℝ)) / M := fun H _ => by ring
      rw [Finset.sum_congr rfl h_factor, ← Finset.sum_div,
          genOrbit_counting_factoring σ A B C G hAB]
      suffices hM : M = (Nat.choose (G.size - σ.size) (A.size - σ.size) : ℝ) *
          (Nat.choose (G.size - σ.size - (A.size - σ.size)) (B.size - σ.size) : ℝ) *
          (Nat.choose (G.size - σ.size - (A.size - σ.size) - (B.size - σ.size))
            (C.size - σ.size) : ℝ) by rw [hM]
      change (Nat.choose (nAB - σ.size) (A.size - σ.size) : ℝ) *
            (Nat.choose (nAB - σ.size - (A.size - σ.size)) (B.size - σ.size) : ℝ) *
            ((Nat.choose (G.size - σ.size) (nAB - σ.size) : ℝ) *
              (Nat.choose (G.size - σ.size - (nAB - σ.size)) (C.size - σ.size) : ℝ)) = _
      rw [h_ns]; set f₁ := A.size - σ.size; set f₂ := B.size - σ.size
      set f₃ := C.size - σ.size; set g := G.size - σ.size
      rw [show f₁ + f₂ - f₁ = f₂ from by omega, show (Nat.choose f₂ f₂ : ℝ) = 1 from by simp]
      by_cases hf₁₂ : f₁ + f₂ ≤ g
      · simp only [mul_one]
        have hsub : g - (f₁ + f₂) = g - f₁ - f₂ := by omega
        have hM := multinomial_factoring g f₁ f₂ f₃ hf₁₂
        rw [hsub] at hM ⊢; exact hM
      · push_neg at hf₁₂
        simp [show (Nat.choose g (f₁ + f₂) : ℝ) = 0 from by exact_mod_cast Nat.choose_eq_zero_of_lt hf₁₂,
              show (Nat.choose g f₁ : ℝ) * (Nat.choose (g - f₁) f₂ : ℝ) = 0 from by
                rcases le_or_gt f₁ g with h | h
                · simp [show Nat.choose (g - f₁) f₂ = 0 from by rw [Nat.choose_eq_zero_iff]; omega]
                · simp [show Nat.choose g f₁ = 0 from Nat.choose_eq_zero_of_lt h]]
    -- Step 2: coeff chain rule -- each side = aut⁻¹ · T
    set T := genTripleJointInducedDensity σ F₁ F₂ F₃ G
    have sum_lhs : (∑ H ∈ genClassesOfSize R σ (F₁.size + F₂.size - σ.size) hℓ,
        genJointInducedDensity R σ F₁ F₂ H.out *
          ((genFlagAutCount R σ H.out : ℝ) * (genFlagAutCount R σ F₃ : ℝ))⁻¹ *
          genJointInducedDensity R σ H.out F₃ G) = (genFlagAutCount R σ F₃ : ℝ)⁻¹ * T := by
      have h_rw_lhs : ∀ H ∈ genClassesOfSize R σ (F₁.size + F₂.size - σ.size) hℓ,
          genJointInducedDensity R σ F₁ F₂ H.out *
            ((genFlagAutCount R σ H.out : ℝ) * (genFlagAutCount R σ F₃ : ℝ))⁻¹ *
            genJointInducedDensity R σ H.out F₃ G = (genFlagAutCount R σ F₃ : ℝ)⁻¹ *
            (genJointInducedDensity R σ F₁ F₂ H.out * genJointInducedDensity R σ H.out F₃ G /
              (genFlagAutCount R σ H.out : ℝ)) := fun H _ => by rw [mul_inv]; ring
      rw [Finset.sum_congr rfl h_rw_lhs, ← Finset.mul_sum, tjf F₁ F₂ F₃ hℓ]
    have sum_rhs : (∑ H' ∈ genClassesOfSize R σ (F₂.size + F₃.size - σ.size) hm,
        genJointInducedDensity R σ F₂ F₃ H'.out *
          ((genFlagAutCount R σ F₁ : ℝ) * (genFlagAutCount R σ H'.out : ℝ))⁻¹ *
          genJointInducedDensity R σ F₁ H'.out G) = (genFlagAutCount R σ F₁ : ℝ)⁻¹ * T := by
      have h_rw_rhs : ∀ H' ∈ genClassesOfSize R σ (F₂.size + F₃.size - σ.size) hm,
          genJointInducedDensity R σ F₂ F₃ H'.out *
            ((genFlagAutCount R σ F₁ : ℝ) * (genFlagAutCount R σ H'.out : ℝ))⁻¹ *
            genJointInducedDensity R σ F₁ H'.out G = (genFlagAutCount R σ F₁ : ℝ)⁻¹ *
            (genJointInducedDensity R σ F₂ F₃ H'.out *
              genJointInducedDensity R σ H'.out F₁ G /
              (genFlagAutCount R σ H'.out : ℝ)) :=
        fun H' _ => by rw [mul_inv, genJointInducedDensity_comm R σ F₁ H'.out G]; ring
      rw [Finset.sum_congr rfl h_rw_rhs, ← Finset.mul_sum, tjf F₂ F₃ F₁ hm,
          ← genTripleJointInducedDensity_perm_231 σ F₁ F₂ F₃ G]
    rw [sum_lhs, sum_rhs]; ring
  · simp only [if_neg hmem, mul_zero, Finset.sum_const_zero, mul_zero]

/-- A predicate on unlabelled graphs in a generic `RelUniverse`. -/
abbrev GenGraphClass (R : RelUniverse) := GenFlag R (GenFlagType.empty R) → Prop

/-- A graph parameter (ℕ-valued) in a generic `RelUniverse`. -/
abbrev GenGraphParam (R : RelUniverse) := GenFlag R (GenFlagType.empty R) → ℕ

/-! ## Phase 4e: Generic Product Closure

Product closure says that if F and F' are local flags and H appears in their
product with positive joint density, then H is also a local flag.  This ensures
the product of two local-support elements has local support.

`genProduct_closure` is proved by well-founded induction on `H.unlabelledSize`,
mirroring `product_closure_aux` for `simpleGraphUniverse`.  The two counting
sub-lemmas (`genBounded_density_of_joint_pos`, `genDecomposition_at_extension`)
are sorry'd pending translation of the ~600-line embedding construction.
The two support lemmas follow from `genProduct_closure` by Finsupp analysis. -/

/-- Counting inequality: if `genJointInducedDensity > 0`, then
    `genInducedCount H G ≤ genInducedCount F G * genInducedCount F' G` via
    the injection φ ↦ (φ ∘ e₁, φ ∘ e₂) using the witness covering. -/
private theorem genInducedCount_le_product_of_joint_pos {R : RelUniverse}
    {σ : GenFlagType R} (F F' H G : GenFlag R σ)
    (hp : genJointInducedDensity R σ F F' H > 0) :
    (genInducedCount R σ H G : ℝ) ≤
      (genInducedCount R σ F G : ℝ) * (genInducedCount R σ F' G : ℝ) := by
  -- Extract a witness pair from genJointCount > 0.
  have hjc_pos : (0 : ℝ) < (genJointCount R σ F F' H : ℝ) := by
    unfold genJointInducedDensity at hp
    by_contra h; push_neg at h
    have h0 := le_antisymm h (Nat.cast_nonneg _)
    rw [h0] at hp; simp at hp
  have hjc_nat : 0 < genJointCount R σ F F' H := Nat.cast_pos.mp hjc_pos
  unfold genJointCount at hjc_nat
  rw [Fintype.card_pos_iff] at hjc_nat
  obtain ⟨⟨⟨e₁, e₂⟩, _, hcovering⟩⟩ := hjc_nat
  suffices h : genInducedCount R σ H G ≤ genInducedCount R σ F G * genInducedCount R σ F' G by
    exact_mod_cast h
  unfold genInducedCount
  rw [← Fintype.card_prod]
  apply Fintype.card_le_of_injective
    (fun (φ : GenInducedEmbedding R σ H G) =>
      (φ.comp e₁, φ.comp e₂))
  intro φ₁ φ₂ heq
  have h1 : φ₁.toFun ∘ e₁.toFun = φ₂.toFun ∘ e₁.toFun :=
    congr_arg GenInducedEmbedding.toFun (congr_arg Prod.fst heq)
  have h2 : φ₁.toFun ∘ e₂.toFun = φ₂.toFun ∘ e₂.toFun :=
    congr_arg GenInducedEmbedding.toFun (congr_arg Prod.snd heq)
  have hfun : φ₁.toFun = φ₂.toFun := by
    funext i
    rcases hcovering i with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [← hj]; exact congr_fun h1 j
    · rw [← hj]; exact congr_fun h2 j
  cases φ₁; cases φ₂; simp only at hfun; subst hfun; rfl

/-- Size identity from positive joint density:
    `H.size - σ.size = (F.size - σ.size) + (F'.size - σ.size)`. -/
private theorem genSize_eq_of_joint_pos {R : RelUniverse} {σ : GenFlagType R}
    (F F' H : GenFlag R σ)
    (hp : genJointInducedDensity R σ F F' H > 0) :
    H.size - σ.size = (F.size - σ.size) + (F'.size - σ.size) := by
  have hjc_pos : (0 : ℝ) < (genJointCount R σ F F' H : ℝ) := by
    unfold genJointInducedDensity at hp
    by_contra h; push_neg at h
    have h0 := le_antisymm h (Nat.cast_nonneg _)
    rw [h0] at hp; simp at hp
  have hjc_nat : 0 < genJointCount R σ F F' H := Nat.cast_pos.mp hjc_pos
  unfold genJointCount at hjc_nat
  rw [Fintype.card_pos_iff] at hjc_nat
  obtain ⟨⟨⟨e₁, e₂⟩, hoverlap, hcovering⟩⟩ := hjc_nat
  -- Use Finset.image for cardinality.
  have hS₁_card : (Finset.univ.image e₁.toFun).card = F.size := by
    rw [Finset.card_image_of_injective _ e₁.injective, Finset.card_univ, Fintype.card_fin]
  have hS₂_card : (Finset.univ.image e₂.toFun).card = F'.size := by
    rw [Finset.card_image_of_injective _ e₂.injective, Finset.card_univ, Fintype.card_fin]
  have hSσ_card : (Finset.univ.image H.embedding).card = σ.size := by
    rw [Finset.card_image_of_injective _ H.embedding.injective, Finset.card_univ,
        Fintype.card_fin]
  -- S₁ ∩ S₂ = Sσ (overlap exactly on sigma-image)
  have hinter : Finset.univ.image e₁.toFun ∩ Finset.univ.image e₂.toFun =
      Finset.univ.image H.embedding := by
    ext i; simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩⟩
      have hi₁ : i ∈ Set.range e₁.toFun := ⟨j₁, hj₁⟩
      have hi₂ : i ∈ Set.range e₂.toFun := ⟨j₂, hj₂⟩
      obtain ⟨k, hk⟩ := (hoverlap i).mp ⟨hi₁, hi₂⟩
      exact ⟨k, hk⟩
    · rintro ⟨j, hj⟩
      have himσ : i ∈ Set.range H.embedding := ⟨j, hj⟩
      have hmem := (hoverlap i).mpr himσ
      obtain ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩ := hmem
      exact ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩
  -- S₁ ∪ S₂ = univ (covering)
  have hunion : Finset.univ.image e₁.toFun ∪ Finset.univ.image e₂.toFun = Finset.univ := by
    ext i; constructor
    · intro; exact Finset.mem_univ _
    · intro _
      rw [Finset.mem_union]
      rcases hcovering i with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · left; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      · right; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hcard := Finset.card_union_add_card_inter
    (Finset.univ.image e₁.toFun) (Finset.univ.image e₂.toFun)
  rw [hunion, hinter, Finset.card_univ, Fintype.card_fin,
      hS₁_card, hS₂_card, hSσ_card] at hcard
  have hFσ := F.hsize; have hF'σ := F'.hsize; have hHσ := H.hsize
  omega

private theorem genBounded_density_of_joint_pos {R : RelUniverse}
    (σ : GenFlagType R) (F F' H : GenFlag R σ)
    (𝒢 : GenGraphClass R) (Δ : GenGraphParam R)
    (hbF : GenIsBoundedDensity σ F 𝒢 Δ) (hbF' : GenIsBoundedDensity σ F' 𝒢 Δ)
    (hp : genJointInducedDensity R σ F F' H > 0) :
    GenIsBoundedDensity σ H 𝒢 Δ := by
  obtain ⟨C_F, hCF_nn, hCF⟩ := hbF
  obtain ⟨C_F', hCF'_nn, hCF'⟩ := hbF'
  set f := F.size - σ.size
  set f' := F'.size - σ.size
  set h := H.size - σ.size
  set R_val := (Nat.choose h f : ℝ) with hR_def
  have hR_nn : (0 : ℝ) ≤ R_val := Nat.cast_nonneg _
  have hR2_nn : (0 : ℝ) ≤ R_val ^ 2 := pow_nonneg hR_nn 2
  refine ⟨C_F * C_F' * R_val ^ 2,
    mul_nonneg (mul_nonneg hCF_nn hCF'_nn) hR2_nn, fun G hG => ?_⟩
  have hsize : h = f + f' := genSize_eq_of_joint_pos F F' H hp
  have hcount := genInducedCount_le_product_of_joint_pos F F' H G hp
  -- Prove the density product bound: genLocalDensity H ≤ genLocalDensity F * genLocalDensity F' * R_val^2
  set n := Δ G.forget
  have hld_bound : genLocalDensity σ H G Δ ≤
      genLocalDensity σ F G Δ * genLocalDensity σ F' G Δ * R_val ^ 2 := by
    unfold genLocalDensity
    by_cases hdenom : Nat.choose n h = 0
    · rw [hdenom, Nat.cast_zero, div_zero]
      apply mul_nonneg
      · apply mul_nonneg
        · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · exact pow_nonneg (Nat.cast_nonneg _) 2
    · have hh_le_n : h ≤ n := Nat.choose_ne_zero_iff.mp hdenom
      have hvander : Nat.choose n f * Nat.choose n f' ≤
          Nat.choose h f ^ 2 * Nat.choose n h := by
        rw [hsize]; exact choose_mul_choose_le f f' n (hsize ▸ hh_le_n)
      have hcount_nat : genInducedCount R σ H G ≤
          genInducedCount R σ F G * genInducedCount R σ F' G := by
        exact_mod_cast hcount
      have hcombined :
          genInducedCount R σ H G * (Nat.choose n f * Nat.choose n f') ≤
          genInducedCount R σ F G * genInducedCount R σ F' G *
            (Nat.choose h f ^ 2 * Nat.choose n h) :=
        Nat.mul_le_mul hcount_nat hvander
      have hcombined_real : (genInducedCount R σ H G : ℝ) *
          ((Nat.choose n f : ℝ) * (Nat.choose n f' : ℝ)) ≤
          (genInducedCount R σ F G : ℝ) * (genInducedCount R σ F' G : ℝ) *
            (((Nat.choose h f : ℝ) ^ 2) * (Nat.choose n h : ℝ)) := by
        exact_mod_cast hcombined
      have hprod_pos : (0 : ℝ) < (Nat.choose n f : ℝ) * (Nat.choose n f' : ℝ) := by
        apply mul_pos <;> exact_mod_cast Nat.choose_pos (by omega)
      have hCnh_pos : (0 : ℝ) < (Nat.choose n h : ℝ) :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero hdenom)
      rw [div_mul_div_comm, div_mul_eq_mul_div]
      rw [div_le_div_iff₀ hCnh_pos hprod_pos]
      linarith
  have hprod : genLocalDensity σ F G Δ * genLocalDensity σ F' G Δ ≤ C_F * C_F' :=
    mul_le_mul (hCF G hG) (hCF' G hG)
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (le_trans (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hCF G hG))
  calc genLocalDensity σ H G Δ
      ≤ genLocalDensity σ F G Δ * genLocalDensity σ F' G Δ * R_val ^ 2 := hld_bound
    _ ≤ C_F * C_F' * R_val ^ 2 := mul_le_mul_of_nonneg_right hprod hR2_nn

/-- If `genJointInducedDensity > 0` then there exists a witness pair of
    embeddings satisfying the overlap and covering conditions. -/
theorem gen_joint_pos_witness {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₂ G : GenFlag R σ}
    (hp : genJointInducedDensity R σ F₁ F₂ G > 0) :
    ∃ (e₁ : GenInducedEmbedding R σ F₁ G) (e₂ : GenInducedEmbedding R σ F₂ G),
      (∀ i : Fin G.size,
        (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
          i ∈ Set.range G.embedding) ∧
      (∀ i : Fin G.size,
        i ∈ Set.range e₁.toFun ∨ i ∈ Set.range e₂.toFun) := by
  have hjc_pos : (0 : ℝ) < (genJointCount R σ F₁ F₂ G : ℝ) := by
    unfold genJointInducedDensity at hp
    by_contra h; push_neg at h
    have h0 := le_antisymm h (Nat.cast_nonneg _)
    rw [h0] at hp; simp at hp
  have hjc_nat : 0 < genJointCount R σ F₁ F₂ G := Nat.cast_pos.mp hjc_pos
  unfold genJointCount at hjc_nat
  rw [Fintype.card_pos_iff] at hjc_nat
  obtain ⟨⟨⟨e₁, e₂⟩, hoverlap, hcovering⟩⟩ := hjc_nat
  exact ⟨e₁, e₂, hoverlap, hcovering⟩

/-- In a joint count witness, an unlabelled vertex is in exactly one side. -/
theorem gen_vertex_in_exactly_one_side {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₂ G : GenFlag R σ}
    (e₁ : GenInducedEmbedding R σ F₁ G) (e₂ : GenInducedEmbedding R σ F₂ G)
    (hoverlap : ∀ i : Fin G.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
        i ∈ Set.range G.embedding)
    (hcovering : ∀ i : Fin G.size,
      i ∈ Set.range e₁.toFun ∨ i ∈ Set.range e₂.toFun)
    (v : Fin G.size) (hv : v ∉ Set.range G.embedding) :
    (v ∈ Set.range e₁.toFun ∧ v ∉ Set.range e₂.toFun) ∨
    (v ∉ Set.range e₁.toFun ∧ v ∈ Set.range e₂.toFun) := by
  have hnot_both : ¬(v ∈ Set.range e₁.toFun ∧ v ∈ Set.range e₂.toFun) := by
    intro hboth; exact hv ((hoverlap v).mp hboth)
  rcases hcovering v with h1 | h2
  · left; exact ⟨h1, fun h2 => hnot_both ⟨h1, h2⟩⟩
  · right; exact ⟨fun h1 => hnot_both ⟨h1, h2⟩, h2⟩

/-- Transport GenIsBoundedDensity through a GenFlagIso. -/
private theorem GenIsBoundedDensity_flagIso {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₂ : GenFlag R σ} {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    (hiso : GenFlagIso σ F₁ F₂) (hbd : GenIsBoundedDensity σ F₁ 𝒢 Δ) :
    GenIsBoundedDensity σ F₂ 𝒢 Δ := by
  obtain ⟨C, hC0, hC⟩ := hbd
  refine ⟨C, hC0, fun G hG => ?_⟩
  have heq : genLocalDensity σ F₂ G Δ = genLocalDensity σ F₁ G Δ := by
    unfold genLocalDensity
    rw [genInducedCount_flagIso hiso.symm,
      show F₂.size = F₁.size from (genFlagIso_size_eq hiso).symm]
  rw [heq]; exact hC G hG

/-- Transport a GenLabelExtension backward through a GenFlagIso.
    Given φ : F₁ ≃ F₂ and ext₂ : GenLabelExtension F₂,
    construct ext₁ : GenLabelExtension F₁ using φ⁻¹. -/
private noncomputable def GenLabelExtension.ofGenFlagIso
    {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₂ : GenFlag R σ}
    (φ : Fin F₁.size ≃ Fin F₂.size)
    (hcompat : ∀ i : Fin σ.size,
      φ (F₁.embedding i) = F₂.embedding i)
    (ext₂ : GenLabelExtension F₂) : GenLabelExtension F₁ where
  vertex := φ.symm ext₂.vertex
  unlabelled := by
    intro ⟨i, hi⟩
    apply ext₂.unlabelled
    exact ⟨i, by rw [← hcompat i]; simp [hi]⟩

/-- Generic IsLocalFlag is preserved by flag isomorphism.
    By ℕ-induction on unlabelled size (with cross-type generalization
    to handle the type change at each extension step).
    Mirrors `IsLocalFlag_flagIso_gen` from FlagIso.lean. -/
private theorem GenIsLocalFlag_flagIso_gen {R : RelUniverse} (n : ℕ) :
    ∀ {σ₁ σ₂ : GenFlagType R} (hσ : σ₁ = σ₂)
      {F₁ : GenFlag R σ₁} {F₂ : GenFlag R σ₂}
      {𝒢 : GenGraphClass R} {Δ : GenGraphParam R},
    F₁.unlabelledSize ≤ n →
    (φ : Fin F₁.size ≃ Fin F₂.size) →
    (R.comap φ F₂.str = F₁.str) →
    (∀ i : Fin σ₁.size, φ (F₁.embedding i) =
      F₂.embedding (Fin.cast (congrArg GenFlagType.size hσ) i)) →
    GenIsLocalFlag σ₁ F₁ 𝒢 Δ → GenIsLocalFlag σ₂ F₂ 𝒢 Δ := by
  induction n with
  | zero =>
    intro σ₁ σ₂ hσ F₁ F₂ 𝒢 Δ hn φ hstr hφ h
    subst hσ; simp only [Fin.cast_eq_self] at hφ
    cases h with | intro _ _ _ _ hbd hext =>
    apply GenIsLocalFlag.intro _ _ _ _
      (GenIsBoundedDensity_flagIso ⟨φ, hstr, hφ⟩ hbd)
    intro ext₂; exfalso
    unfold GenFlag.unlabelledSize at hn
    have hsz : F₁.size = F₂.size := genFlagIso_size_eq ⟨φ, hstr, hφ⟩
    have hge : F₂.size ≤ σ₁.size := by omega
    exact ext₂.unlabelled
      (F₂.embedding.injective.surjective_of_finite
        (finCongr (Nat.le_antisymm hge F₂.hsize).symm) ext₂.vertex)
  | succ m ih_m =>
    intro σ₁ σ₂ hσ F₁ F₂ 𝒢 Δ hn φ hstr hφ h
    subst hσ; simp only [Fin.cast_eq_self] at hφ
    cases h with | intro _ _ _ _ hbd hext =>
    apply GenIsLocalFlag.intro _ _ _ _
      (GenIsBoundedDensity_flagIso ⟨φ, hstr, hφ⟩ hbd)
    intro ext₂
    let ext₁ := GenLabelExtension.ofGenFlagIso φ hφ ext₂
    -- The extended types are equal
    have hteq : ext₁.extendedType = ext₂.extendedType := by
      unfold GenLabelExtension.extendedType
      congr 1
      -- Goal: R.comap ext₁.vertexMap F₁.str = R.comap ext₂.vertexMap F₂.str
      -- Rewrite F₁.str = R.comap φ F₂.str (from hstr), then compose
      conv_lhs => rw [← hstr]
      rw [← R.comap_comp]
      congr 1; ext i
      obtain (⟨j, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
      · simp only [Function.comp, GenLabelExtension.vertexMap,
          Fin.lastCases_castSucc]
        exact congrArg Fin.val (hφ j)
      · simp only [Function.comp, GenLabelExtension.vertexMap,
          Fin.lastCases_last]
        exact congrArg Fin.val (φ.apply_symm_apply ext₂.vertex)
    -- The vertex map compatibility at the extended type
    have hvm_compat : ∀ i : Fin ext₁.extendedType.size,
        φ (ext₁.vertexMap i) =
          ext₂.vertexMap (Fin.cast (congrArg GenFlagType.size hteq) i) := by
      intro i
      have : Fin.cast (congrArg GenFlagType.size hteq) i = i :=
        Fin.ext rfl
      rw [this]
      obtain (⟨j, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
      · simp only [GenLabelExtension.vertexMap, Fin.lastCases_castSucc]
        exact hφ j
      · simp only [GenLabelExtension.vertexMap, Fin.lastCases_last]
        exact φ.apply_symm_apply ext₂.vertex
    apply ih_m hteq ?_ φ ?_ ?_ (hext ext₁)
    · -- unlabelledSize decreases
      simp only [GenFlag.unlabelledSize, GenLabelExtension.extendedFlag,
        GenLabelExtension.extendedType]
      unfold GenFlag.unlabelledSize at hn; omega
    · -- R.comap φ ext₂.extendedFlag.str = ext₁.extendedFlag.str
      change R.comap φ F₂.str = F₁.str
      exact hstr
    · -- Compatibility: φ maps ext₁ embeddings to ext₂ embeddings
      change ∀ i, φ (ext₁.vertexMap i) =
        ext₂.vertexMap (Fin.cast _ i)
      exact hvm_compat

/-- Generic IsLocalFlag is preserved by flag isomorphism. -/
theorem GenIsLocalFlag_flagIso {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₂ : GenFlag R σ} {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    (hiso : GenFlagIso σ F₁ F₂) (h : GenIsLocalFlag σ F₁ 𝒢 Δ) :
    GenIsLocalFlag σ F₂ 𝒢 Δ := by
  obtain ⟨φ, hstr, hcompat⟩ := hiso
  have : ∀ i : Fin σ.size, φ (F₁.embedding i) =
      F₂.embedding (Fin.cast rfl i) := by
    simp only [Fin.cast_eq_self]; exact hcompat
  exact GenIsLocalFlag_flagIso_gen F₁.unlabelledSize rfl le_rfl φ hstr this h

/-- **Generic augmented local flag**: augmenting a local flag F' by one vertex
    preserves locality. Generalizes `augmented_local_flag` to arbitrary `RelUniverse`.

    Given: F' local at σ, B at σ' (|σ'|=|σ|+1, |B|=|F'|+1) whose structure
    restricts to F' on the first F'.size vertices, with compatible embedding.

    The structural condition `R.comap castMap B.str = F'.str` replaces the
    SimpleGraph pointwise adjacency condition, making the proof simpler. -/
private theorem genAugmented_local_flag {R : RelUniverse}
    (σ : GenFlagType R) (F' : GenFlag R σ)
    (𝒢 : GenGraphClass R) (Δ : GenGraphParam R)
    (hF' : GenIsLocalFlag σ F' 𝒢 Δ)
    (σ' : GenFlagType R) (B : GenFlag R σ')
    (hσ' : σ'.size = σ.size + 1) (hB : B.size = F'.size + 1)
    (hstr : R.comap (fun i : Fin F'.size => (⟨i.val, by omega⟩ : Fin B.size)) B.str = F'.str)
    (hcompat : ∀ k : Fin σ.size,
      (B.embedding (Fin.cast hσ'.symm (Fin.castSucc k))).val = (F'.embedding k).val)
    (hNewLabelled : (B.embedding (Fin.cast hσ'.symm (Fin.last σ.size))).val = F'.size) :
    GenIsLocalFlag σ' B 𝒢 Δ := by
  -- Step 1: Prove GenIsLocalFlag_relabel (permuting labels preserves locality)
  -- by induction on unlabelledSize, as a standalone helper.
  have gen_relabel : ∀ (m : ℕ) {σ₂ : GenFlagType R} {F₂ : GenFlag R σ₂}
      {𝒢₂ : GenGraphClass R} {Δ₂ : GenGraphParam R}
      (π₂ : Equiv.Perm (Fin σ₂.size)),
      GenIsLocalFlag σ₂ F₂ 𝒢₂ Δ₂ → F₂.unlabelledSize ≤ m →
      GenIsLocalFlag
        ⟨σ₂.size, R.comap π₂ σ₂.str⟩
        ⟨F₂.size, F₂.str,
          ⟨fun i => F₂.embedding (π₂ i),
            fun {a b} hab => π₂.injective (F₂.embedding.injective hab)⟩,
          by change R.comap (F₂.embedding ∘ π₂) F₂.str = R.comap π₂ σ₂.str
             rw [R.comap_comp, F₂.isInduced],
          F₂.hsize⟩
        𝒢₂ Δ₂ := by
    -- GenIsLocalFlag_relabel: permuting labels preserves locality.
    -- Proof by induction on unlabelledSize m: bounded density via injection
    -- (construct G with permuted σ-embedding), extensions via IH with extended
    -- permutation + GenIsLocalFlag_flagIso_gen transport.
    intro m; induction m with
    | zero =>
      intro σ₂ F₂ 𝒢₂ Δ₂ π₂ hF₂ hm
      let σ_π : GenFlagType R := ⟨σ₂.size, R.comap π₂ σ₂.str⟩
      let F_π : GenFlag R σ_π :=
        ⟨F₂.size, F₂.str,
          ⟨fun i => F₂.embedding (π₂ i),
            fun {a b} hab => π₂.injective (F₂.embedding.injective hab)⟩,
          by change R.comap (F₂.embedding ∘ π₂) F₂.str = R.comap π₂ σ₂.str
             rw [R.comap_comp, F₂.isInduced],
          F₂.hsize⟩
      cases hF₂ with | intro _ _ _ _ hbd hext =>
      change GenIsLocalFlag σ_π F_π 𝒢₂ Δ₂
      apply GenIsLocalFlag.intro
      · obtain ⟨C, hC0, hCbound⟩ := hbd
        refine ⟨C, hC0, fun G hG => ?_⟩
        let G_orig : GenFlag R σ₂ :=
          { size := G.size
            str := G.str
            embedding := ⟨fun i => G.embedding (π₂.symm i),
              fun {a b} hab => π₂.symm.injective (G.embedding.injective hab)⟩
            isInduced := by
              change R.comap (G.embedding ∘ π₂.symm) G.str = σ₂.str
              rw [R.comap_comp, G.isInduced, ← R.comap_comp,
                  show (⇑π₂ ∘ ⇑π₂.symm : Fin σ₂.size → Fin σ₂.size) = id from
                    funext π₂.apply_symm_apply, R.comap_id]
            hsize := G.hsize }
        have h_inj : genInducedCount R σ_π F_π G ≤ genInducedCount R σ₂ F₂ G_orig := by
          unfold genInducedCount
          apply Fintype.card_le_of_injective
            (fun (e : GenInducedEmbedding R σ_π F_π G) =>
              (⟨e.toFun, e.injective, e.isInduced,
                fun i => by
                  have h := e.compat (π₂.symm i)
                  change e.toFun (F₂.embedding (π₂ (π₂.symm i))) =
                    G.embedding (π₂.symm i) at h
                  rwa [π₂.apply_symm_apply] at h⟩
                : GenInducedEmbedding R σ₂ F₂ G_orig))
          intro e₁ e₂ h; cases e₁; cases e₂
          simpa [GenInducedEmbedding.mk.injEq] using h
        calc genLocalDensity σ_π F_π G Δ₂
            = (genInducedCount R σ_π F_π G : ℝ) /
              (Nat.choose (Δ₂ G.forget) (F_π.size - σ_π.size) : ℝ) := rfl
          _ ≤ (genInducedCount R σ₂ F₂ G_orig : ℝ) /
              (Nat.choose (Δ₂ G.forget) (F_π.size - σ_π.size) : ℝ) :=
              div_le_div_of_nonneg_right (Nat.cast_le.mpr h_inj) (Nat.cast_nonneg _)
          _ = genLocalDensity σ₂ F₂ G_orig Δ₂ := rfl
          _ ≤ C := hCbound G_orig (by change 𝒢₂ G.forget at hG; exact hG)
      · intro ext₀; exfalso
        unfold GenFlag.unlabelledSize at hm
        have hge : F₂.size ≤ σ₂.size := by omega
        have hsurj := F₂.embedding.injective.surjective_of_finite
          (finCongr (Nat.le_antisymm hge F₂.hsize).symm)
        exact ext₀.unlabelled (by
          obtain ⟨j, hj⟩ := hsurj ext₀.vertex
          change ext₀.vertex ∈ Set.range (fun i => F₂.embedding (π₂ i))
          exact ⟨π₂.symm j, by simp only [π₂.apply_symm_apply, hj]⟩)
    | succ m ih_rel =>
      intro σ₂ F₂ 𝒢₂ Δ₂ π₂ hF₂ hm
      let σ_π : GenFlagType R := ⟨σ₂.size, R.comap π₂ σ₂.str⟩
      let F_π : GenFlag R σ_π :=
        ⟨F₂.size, F₂.str,
          ⟨fun i => F₂.embedding (π₂ i),
            fun {a b} hab => π₂.injective (F₂.embedding.injective hab)⟩,
          by change R.comap (F₂.embedding ∘ π₂) F₂.str = R.comap π₂ σ₂.str
             rw [R.comap_comp, F₂.isInduced],
          F₂.hsize⟩
      cases hF₂ with | intro _ _ _ _ hbd hext =>
      change GenIsLocalFlag σ_π F_π 𝒢₂ Δ₂
      apply GenIsLocalFlag.intro
      · -- Bounded density (same as base)
        obtain ⟨C, hC0, hCbound⟩ := hbd
        refine ⟨C, hC0, fun G hG => ?_⟩
        let G_orig : GenFlag R σ₂ :=
          { size := G.size
            str := G.str
            embedding := ⟨fun i => G.embedding (π₂.symm i),
              fun {a b} hab => π₂.symm.injective (G.embedding.injective hab)⟩
            isInduced := by
              change R.comap (G.embedding ∘ π₂.symm) G.str = σ₂.str
              rw [R.comap_comp, G.isInduced, ← R.comap_comp,
                  show (⇑π₂ ∘ ⇑π₂.symm : Fin σ₂.size → Fin σ₂.size) = id from
                    funext π₂.apply_symm_apply, R.comap_id]
            hsize := G.hsize }
        have h_inj : genInducedCount R σ_π F_π G ≤ genInducedCount R σ₂ F₂ G_orig := by
          unfold genInducedCount
          apply Fintype.card_le_of_injective
            (fun (e : GenInducedEmbedding R σ_π F_π G) =>
              (⟨e.toFun, e.injective, e.isInduced,
                fun i => by
                  have h := e.compat (π₂.symm i)
                  change e.toFun (F₂.embedding (π₂ (π₂.symm i))) =
                    G.embedding (π₂.symm i) at h
                  rwa [π₂.apply_symm_apply] at h⟩
                : GenInducedEmbedding R σ₂ F₂ G_orig))
          intro e₁ e₂ h; cases e₁; cases e₂
          simpa [GenInducedEmbedding.mk.injEq] using h
        calc genLocalDensity σ_π F_π G Δ₂
            = (genInducedCount R σ_π F_π G : ℝ) /
              (Nat.choose (Δ₂ G.forget) (F_π.size - σ_π.size) : ℝ) := rfl
          _ ≤ (genInducedCount R σ₂ F₂ G_orig : ℝ) /
              (Nat.choose (Δ₂ G.forget) (F_π.size - σ_π.size) : ℝ) :=
              div_le_div_of_nonneg_right (Nat.cast_le.mpr h_inj) (Nat.cast_nonneg _)
          _ = genLocalDensity σ₂ F₂ G_orig Δ₂ := rfl
          _ ≤ C := hCbound G_orig (by change 𝒢₂ G.forget at hG; exact hG)
      · -- Extensions
        intro ext₂
        have hv_unlab : ext₂.vertex ∉ Set.range F₂.embedding := by
          intro ⟨j, hj⟩; apply ext₂.unlabelled
          change ext₂.vertex ∈ Set.range (fun i => F₂.embedding (π₂ i))
          exact ⟨π₂.symm j, by simp only [π₂.apply_symm_apply, hj]⟩
        let ext_orig : GenLabelExtension F₂ := ⟨ext₂.vertex, hv_unlab⟩
        -- Extended permutation: π₂ on first σ₂.size positions, id on last
        let π₂_ext : Equiv.Perm (Fin ext_orig.extendedType.size) :=
          { toFun := fun i =>
              if h : i.val < σ₂.size then Fin.castSucc (π₂ ⟨i.val, h⟩) else i
            invFun := fun i =>
              if h : i.val < σ₂.size then Fin.castSucc (π₂.symm ⟨i.val, h⟩) else i
            left_inv := fun i => by
              dsimp only
              split
              next h =>
                have h2 : (Fin.castSucc (π₂ ⟨i.val, h⟩)).val < σ₂.size := by
                  simp only [Fin.val_castSucc]; exact (π₂ ⟨i.val, h⟩).isLt
                simp only [dif_pos h2]
                refine Fin.ext ?_
                simp only [Fin.val_castSucc]
                have heq : (⟨(π₂ ⟨i.val, h⟩).val, h2⟩ : Fin σ₂.size) =
                    π₂ ⟨i.val, h⟩ := Fin.ext rfl
                rw [heq, π₂.symm_apply_apply]
              next h => rfl
            right_inv := fun i => by
              dsimp only
              split
              next h =>
                have h2 : (Fin.castSucc (π₂.symm ⟨i.val, h⟩)).val < σ₂.size := by
                  simp only [Fin.val_castSucc]; exact (π₂.symm ⟨i.val, h⟩).isLt
                simp only [dif_pos h2]
                refine Fin.ext ?_
                simp only [Fin.val_castSucc]
                have heq : (⟨(π₂.symm ⟨i.val, h⟩).val, h2⟩ : Fin σ₂.size) =
                    π₂.symm ⟨i.val, h⟩ := Fin.ext rfl
                rw [heq, π₂.apply_symm_apply]
              next h => rfl }
        have h_unl_ext : ext_orig.extendedFlag.unlabelledSize ≤ m := by
          unfold GenFlag.unlabelledSize at hm ⊢
          simp only [GenLabelExtension.extendedFlag, GenLabelExtension.extendedType]; omega
        have h_ext_local := hext ext_orig
        have h_rel_ext := ih_rel (σ₂ := ext_orig.extendedType) (F₂ := ext_orig.extendedFlag)
          π₂_ext h_ext_local h_unl_ext
        -- ext₂.extendedType = relabelled ext_orig.extendedType
        have hπ₂_ext_castSucc : ∀ (j : Fin σ₂.size),
            π₂_ext (Fin.castSucc j) = Fin.castSucc (π₂ j) := by
          intro j
          change (if h : (Fin.castSucc j).val < σ₂.size
            then Fin.castSucc (π₂ ⟨(Fin.castSucc j).val, h⟩)
            else Fin.castSucc j) = Fin.castSucc (π₂ j)
          simp only [Fin.val_castSucc, j.isLt, dite_true, Fin.eta]
        have hπ₂_ext_last : π₂_ext (Fin.last σ₂.size) = Fin.last σ₂.size := by
          change (if h : (Fin.last σ₂.size).val < σ₂.size
            then Fin.castSucc (π₂ ⟨(Fin.last σ₂.size).val, h⟩)
            else Fin.last σ₂.size) = Fin.last σ₂.size
          simp only [Fin.val_last, lt_irrefl, dite_false]
        have hvertex_map_eq : ∀ i, ext₂.vertexMap i =
            ext_orig.vertexMap (π₂_ext i) := by
          intro i
          obtain ⟨j, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
          · simp only [GenLabelExtension.vertexMap, Fin.lastCases_castSucc, hπ₂_ext_castSucc]
            rfl
          · rw [GenLabelExtension.vertexMap, Fin.lastCases_last, GenLabelExtension.vertexMap,
              hπ₂_ext_last, Fin.lastCases_last]
        have htype_eq : ext₂.extendedType =
            ⟨ext_orig.extendedType.size, R.comap π₂_ext ext_orig.extendedType.str⟩ := by
          simp only [GenLabelExtension.extendedType]; congr 1
          rw [← R.comap_comp]; congr 1; funext i
          exact hvertex_map_eq i
        -- h_rel_ext gives locality of the relabelled flag at the relabelled type.
        -- htype_eq says ext₂.extendedType = relabelled type.
        -- Transport via GenIsLocalFlag_flagIso_gen.
        let σ_rel : GenFlagType R :=
          ⟨ext_orig.extendedType.size, R.comap π₂_ext ext_orig.extendedType.str⟩
        let F_rel : GenFlag R σ_rel :=
          ⟨ext_orig.extendedFlag.size, ext_orig.extendedFlag.str,
            ⟨fun i => ext_orig.extendedFlag.embedding (π₂_ext i),
              fun {a b} hab => π₂_ext.injective
                (ext_orig.extendedFlag.embedding.injective hab)⟩,
            by change R.comap (ext_orig.extendedFlag.embedding ∘ ⇑π₂_ext)
                  ext_orig.extendedFlag.str =
                R.comap π₂_ext ext_orig.extendedType.str
               rw [R.comap_comp, ext_orig.extendedFlag.isInduced],
            ext_orig.extendedFlag.hsize⟩
        -- h_rel_ext : GenIsLocalFlag σ_rel F_rel 𝒢₂ Δ₂
        change GenIsLocalFlag σ_rel F_rel 𝒢₂ Δ₂ at h_rel_ext
        exact GenIsLocalFlag_flagIso_gen F_rel.unlabelledSize
          htype_eq.symm le_rfl (Equiv.refl _)
          (by change R.comap id ext₂.extendedFlag.str = F_rel.str
              rw [R.comap_id]; rfl)
          (fun i => by
            change F_rel.embedding i =
              ext₂.extendedFlag.embedding (Fin.cast _ i)
            have hcast : Fin.cast (congrArg GenFlagType.size htype_eq.symm) i = i := Fin.ext rfl
            rw [hcast]
            -- F_rel.embedding i = ext_orig.extendedFlag.embedding (π₂_ext i)
            -- ext₂.extendedFlag.embedding i = ext₂.vertexMap i
            -- Need: ext_orig.vertexMap (π₂_ext i) = ext₂.vertexMap i
            change ext_orig.extendedFlag.embedding (π₂_ext i) = ext₂.extendedFlag.embedding i
            obtain ⟨j, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
            · -- castSucc case: use hvertex_map_eq
              exact (hvertex_map_eq (Fin.castSucc j)).symm
            · -- last case: use hvertex_map_eq
              exact (hvertex_map_eq (Fin.last _)).symm)
          h_rel_ext
  -- Step 2: Prove augmented_local_flag by induction on F'.unlabelledSize.
  suffices h_aux : ∀ (n : ℕ) (σ₁ : GenFlagType R) (F₁ : GenFlag R σ₁)
      (𝒢₁ : GenGraphClass R) (Δ₁ : GenGraphParam R),
      GenIsLocalFlag σ₁ F₁ 𝒢₁ Δ₁ → F₁.unlabelledSize ≤ n →
      ∀ (σ₁' : GenFlagType R) (B₁ : GenFlag R σ₁')
        (hσ₁ : σ₁'.size = σ₁.size + 1) (hB₁ : B₁.size = F₁.size + 1),
      R.comap (fun i : Fin F₁.size => (⟨i.val, by omega⟩ : Fin B₁.size)) B₁.str = F₁.str →
      (∀ k : Fin σ₁.size,
        (B₁.embedding (Fin.cast hσ₁.symm (Fin.castSucc k))).val = (F₁.embedding k).val) →
      (B₁.embedding (Fin.cast hσ₁.symm (Fin.last σ₁.size))).val = F₁.size →
      GenIsLocalFlag σ₁' B₁ 𝒢₁ Δ₁ from
    h_aux F'.unlabelledSize σ F' 𝒢 Δ hF' le_rfl σ' B hσ' hB hstr hcompat hNewLabelled
  intro n; induction n with
  | zero =>
    intro σ₁ F₁ 𝒢₁ Δ₁ hF₁ hn σ₁' B₁ hσ₁ hB₁ hstr₁ hcompat₁ hNewLabelled₁
    have hBs : B₁.size = σ₁'.size := by
      have := Nat.le_antisymm (by unfold GenFlag.unlabelledSize at hn; omega) F₁.hsize; omega
    have hsurj := B₁.embedding.injective.surjective_of_finite (finCongr hBs.symm)
    apply GenIsLocalFlag.intro
    · refine ⟨1, le_of_lt one_pos, fun G hG => ?_⟩
      unfold genLocalDensity
      rw [show B₁.size - σ₁'.size = 0 from by omega, Nat.choose_zero_right,
          Nat.cast_one, div_one]
      suffices h : Fintype.card (GenInducedEmbedding R σ₁' B₁ G) ≤ 1 by exact_mod_cast h
      rw [Fintype.card_le_one_iff_subsingleton]; constructor; intro e₁ e₂
      have : e₁.toFun = e₂.toFun := by
        funext x; obtain ⟨i, hi⟩ := hsurj x; rw [← hi, e₁.compat, e₂.compat]
      cases e₁; cases e₂; simpa [GenInducedEmbedding.mk.injEq] using this
    · intro ext'; exact absurd (hsurj ext'.vertex) ext'.unlabelled
  | succ n ih =>
    intro σ₁ F₁ 𝒢₁ Δ₁ hF₁ hn σ₁' B₁ hσ₁ hB₁ hstr₁ hcompat₁ hNewLabelled₁
    let castMap₁ : Fin F₁.size → Fin B₁.size := fun i => ⟨i.val, by omega⟩
    apply GenIsLocalFlag.intro
    · -- Bounded density: inject B₁-embeddings into F₁-embeddings
      obtain ⟨C, hC0, hCbound⟩ := hF₁.bounded
      refine ⟨C, hC0, fun G hG => ?_⟩
      let G_σ_emb_fun : Fin σ₁.size → Fin G.size :=
        fun k => G.embedding (Fin.cast hσ₁.symm (Fin.castSucc k))
      have G_σ_isInduced : R.comap G_σ_emb_fun G.str = σ₁.str := by
        -- G_σ_emb_fun = G.embedding ∘ (cast ∘ castSucc)
        -- comap (G.emb ∘ adj) G.str = comap adj (comap G.emb G.str) = comap adj σ₁'.str
        have h1 : R.comap G_σ_emb_fun G.str = R.comap (fun k : Fin σ₁.size =>
            Fin.cast hσ₁.symm (Fin.castSucc k)) σ₁'.str := by
          change R.comap (G.embedding ∘ (fun k => Fin.cast hσ₁.symm (Fin.castSucc k))) G.str =
            R.comap (fun k => Fin.cast hσ₁.symm (Fin.castSucc k)) σ₁'.str
          rw [R.comap_comp, G.isInduced]
        -- comap adj σ₁'.str = comap adj (comap B₁.emb B₁.str)
        --   = comap (B₁.emb ∘ adj) B₁.str
        -- Also: σ₁.str = comap F₁.emb F₁.str = comap F₁.emb (comap castMap₁ B₁.str)
        --   = comap (castMap₁ ∘ F₁.emb) B₁.str
        -- Need: B₁.emb(adj k) = castMap₁(F₁.emb k), i.e., same val, which is hcompat₁
        rw [h1, ← B₁.isInduced, ← R.comap_comp, ← F₁.isInduced, ← hstr₁, ← R.comap_comp]
        congr 1; funext k; exact Fin.ext (hcompat₁ k)
      let G_σ : GenFlag R σ₁ :=
        { size := G.size
          str := G.str
          embedding := ⟨G_σ_emb_fun, fun {a b} hab =>
            (Fin.castSucc_injective _) ((Fin.cast_injective _)
              (G.embedding.injective hab))⟩
          isInduced := G_σ_isInduced
          hsize := by have := G.hsize; omega }
      have hG_σ_forget : G_σ.forget = G.forget := rfl
      have h_inj_count : genInducedCount R σ₁' B₁ G ≤ genInducedCount R σ₁ F₁ G_σ := by
        unfold genInducedCount
        apply Fintype.card_le_of_injective
          (fun (e : GenInducedEmbedding R σ₁' B₁ G) =>
            (⟨fun i => e.toFun (castMap₁ i),
              fun {a b} hab => by
                have h1 : castMap₁ a = castMap₁ b := e.injective hab
                exact Fin.ext (by simp only [Fin.ext_iff, castMap₁] at h1; exact h1),
              by change R.comap (e.toFun ∘ castMap₁) G.str = F₁.str
                 rw [R.comap_comp, e.isInduced, hstr₁],
              fun k => by
                change e.toFun (castMap₁ (F₁.embedding k)) =
                  G.embedding (Fin.cast hσ₁.symm (Fin.castSucc k))
                rw [show castMap₁ (F₁.embedding k) =
                    B₁.embedding (Fin.cast hσ₁.symm (Fin.castSucc k)) from
                  Fin.ext (by simp only [castMap₁]
                              exact (hcompat₁ k).symm)]
                exact e.compat _⟩
              : GenInducedEmbedding R σ₁ F₁ G_σ))
        intro e₁ e₂ h
        have h_eq : e₁.toFun = e₂.toFun := by
          funext x; by_cases hx : x.val < F₁.size
          · rw [show x = castMap₁ ⟨x.val, hx⟩ from Fin.ext (by simp [castMap₁])]
            exact congr_fun (congr_arg GenInducedEmbedding.toFun h) ⟨x.val, hx⟩
          · rw [show x = B₁.embedding (Fin.cast hσ₁.symm (Fin.last σ₁.size)) from
              Fin.ext (by rw [hNewLabelled₁]; have := x.isLt; simp only [hB₁] at this; omega),
              e₁.compat, e₂.compat]
        cases e₁; cases e₂; simpa [GenInducedEmbedding.mk.injEq] using h_eq
      calc genLocalDensity σ₁' B₁ G Δ₁
            = (genInducedCount R σ₁' B₁ G : ℝ) /
              (Nat.choose (Δ₁ G.forget) (B₁.size - σ₁'.size) : ℝ) := rfl
          _ ≤ (genInducedCount R σ₁ F₁ G_σ : ℝ) /
              (Nat.choose (Δ₁ G.forget) (B₁.size - σ₁'.size) : ℝ) :=
              div_le_div_of_nonneg_right (Nat.cast_le.mpr h_inj_count) (Nat.cast_nonneg _)
          _ = (genInducedCount R σ₁ F₁ G_σ : ℝ) /
              (Nat.choose (Δ₁ G_σ.forget) (F₁.size - σ₁.size) : ℝ) := by
              rw [hG_σ_forget, show B₁.size - σ₁'.size = F₁.size - σ₁.size from by omega]
          _ = genLocalDensity σ₁ F₁ G_σ Δ₁ := rfl
          _ ≤ C := hCbound G_σ (hG_σ_forget ▸ hG)
    · -- Extensions
      intro ext'₁
      have hv_lt : ext'₁.vertex.val < F₁.size := by
        have : ext'₁.vertex.val ≠ F₁.size := fun heq =>
          ext'₁.unlabelled ⟨Fin.cast hσ₁.symm (Fin.last σ₁.size),
            Fin.ext (by simp [hNewLabelled₁, heq])⟩
        have := ext'₁.vertex.isLt; simp only [hB₁] at this; omega
      let ext_F₁ : GenLabelExtension F₁ :=
        ⟨⟨ext'₁.vertex.val, hv_lt⟩, fun ⟨k, hk⟩ => ext'₁.unlabelled
          ⟨Fin.cast hσ₁.symm (Fin.castSucc k), Fin.ext (by
            rw [hcompat₁ k]; exact congr_arg Fin.val hk)⟩⟩
      have h_unl_le : ext_F₁.extendedFlag.unlabelledSize ≤ n := by
        unfold GenFlag.unlabelledSize at hn ⊢
        simp only [GenLabelExtension.extendedFlag, GenLabelExtension.extendedType]; omega
      -- Define π: swap last two label positions of ext'₁.extendedType
      let π₁ : Equiv.Perm (Fin ext'₁.extendedType.size) :=
        Equiv.swap (⟨σ₁.size, by
          simp only [GenLabelExtension.extendedType, hσ₁]; omega⟩)
          (⟨σ₁.size + 1, by
            simp only [GenLabelExtension.extendedType, hσ₁]; omega⟩)
      -- Construct the relabelled type and flag
      let σ_rel : GenFlagType R :=
        ⟨ext'₁.extendedType.size, R.comap π₁ ext'₁.extendedType.str⟩
      let B_rel : GenFlag R σ_rel :=
        { size := ext'₁.extendedFlag.size
          str := ext'₁.extendedFlag.str
          embedding := ⟨fun i => ext'₁.extendedFlag.embedding (π₁ i),
            fun {a b} hab => π₁.injective (ext'₁.extendedFlag.embedding.injective hab)⟩
          isInduced := by
            change R.comap (ext'₁.extendedFlag.embedding ∘ π₁) ext'₁.extendedFlag.str =
              R.comap π₁ (R.comap ext'₁.extendedFlag.embedding ext'₁.extendedFlag.str)
            rw [R.comap_comp]
          hsize := ext'₁.extendedFlag.hsize }
      -- Apply IH: show B_rel is local
      have ih_hσ' : σ_rel.size = ext_F₁.extendedType.size + 1 := by
        change ext'₁.extendedType.size = (σ₁.size + 1) + 1
        simp only [GenLabelExtension.extendedType, hσ₁]
      have ih_hB : B_rel.size = ext_F₁.extendedFlag.size + 1 := by
        change ext'₁.extendedFlag.size = F₁.size + 1
        simp only [GenLabelExtension.extendedFlag]; exact hB₁
      have ih_hstr : R.comap (fun i : Fin ext_F₁.extendedFlag.size =>
          (⟨i.val, by omega⟩ : Fin B_rel.size)) B_rel.str = ext_F₁.extendedFlag.str := by
        change R.comap (fun i : Fin F₁.size => (⟨i.val, by omega⟩ : Fin B₁.size)) B₁.str = F₁.str
        exact hstr₁
      have ih_hcompat : ∀ k : Fin ext_F₁.extendedType.size,
          (B_rel.embedding (Fin.cast ih_hσ'.symm (Fin.castSucc k))).val =
          (ext_F₁.extendedFlag.embedding k).val := by
        intro k
        change (ext'₁.extendedFlag.embedding
          (π₁ (Fin.cast ih_hσ'.symm (Fin.castSucc k)))).val =
          (ext_F₁.extendedFlag.embedding k).val
        obtain ⟨m, rfl⟩ | rfl := k.eq_castSucc_or_eq_last
        · have hne1 : (Fin.cast ih_hσ'.symm (Fin.castSucc (Fin.castSucc m)) :
              Fin ext'₁.extendedType.size) ≠ ⟨σ₁.size, by
              simp only [GenLabelExtension.extendedType, hσ₁]; omega⟩ := by
            intro h; have := congrArg Fin.val h; simp at this; omega
          have hne2 : (Fin.cast ih_hσ'.symm (Fin.castSucc (Fin.castSucc m)) :
              Fin ext'₁.extendedType.size) ≠ ⟨σ₁.size + 1, by
              simp only [GenLabelExtension.extendedType, hσ₁]; omega⟩ := by
            intro h; have := congrArg Fin.val h; simp at this; omega
          rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
          change (ext'₁.vertexMap (Fin.castSucc
            (⟨m.val, by omega⟩ : Fin σ₁'.size))).val =
            (ext_F₁.vertexMap (Fin.castSucc m)).val
          rw [show (⟨m.val, (by omega : m.val < σ₁'.size)⟩ : Fin σ₁'.size) =
              Fin.cast hσ₁.symm (Fin.castSucc m) from Fin.ext (by simp)]
          simp only [GenLabelExtension.vertexMap, Fin.lastCases_castSucc]
          exact hcompat₁ m
        · rw [show π₁ (Fin.cast ih_hσ'.symm (Fin.castSucc (Fin.last σ₁.size))) =
              (⟨σ₁.size + 1, by simp only [GenLabelExtension.extendedType, hσ₁]; omega⟩ :
                Fin ext'₁.extendedType.size) from by
            rw [show (Fin.cast ih_hσ'.symm (Fin.castSucc (Fin.last σ₁.size)) :
                Fin ext'₁.extendedType.size) = ⟨σ₁.size, by
                  simp only [GenLabelExtension.extendedType, hσ₁]; omega⟩ from
              Fin.ext (by simp)]
            exact Equiv.swap_apply_left _ _]
          change (ext'₁.vertexMap (⟨σ₁.size + 1, by omega⟩ : Fin (σ₁'.size + 1))).val =
            (ext_F₁.vertexMap (Fin.last σ₁.size)).val
          rw [show (⟨σ₁.size + 1, (by omega : σ₁.size + 1 < σ₁'.size + 1)⟩ :
              Fin (σ₁'.size + 1)) = Fin.last σ₁'.size from Fin.ext (by simp [hσ₁]),
              GenLabelExtension.vertexMap, Fin.lastCases_last,
              GenLabelExtension.vertexMap, Fin.lastCases_last]
      have ih_hNewLabelled :
          (B_rel.embedding (Fin.cast ih_hσ'.symm
            (Fin.last ext_F₁.extendedType.size))).val =
          ext_F₁.extendedFlag.size := by
        change (ext'₁.extendedFlag.embedding
          (π₁ (Fin.cast ih_hσ'.symm (Fin.last ext_F₁.extendedType.size)))).val = F₁.size
        rw [show π₁ (Fin.cast ih_hσ'.symm (Fin.last ext_F₁.extendedType.size)) =
            (⟨σ₁.size, by simp only [GenLabelExtension.extendedType, hσ₁]; omega⟩ :
              Fin ext'₁.extendedType.size) from by
          rw [show (Fin.cast ih_hσ'.symm (Fin.last ext_F₁.extendedType.size) :
              Fin ext'₁.extendedType.size) = ⟨σ₁.size + 1, by
                simp only [GenLabelExtension.extendedType, hσ₁]; omega⟩ from by
            simp [Fin.ext_iff, GenLabelExtension.extendedType]]
          exact Equiv.swap_apply_right _ _]
        change (ext'₁.vertexMap (⟨σ₁.size, by omega⟩ : Fin (σ₁'.size + 1))).val = F₁.size
        rw [show (⟨σ₁.size, (by omega : σ₁.size < σ₁'.size + 1)⟩ : Fin (σ₁'.size + 1)) =
            Fin.castSucc (⟨σ₁.size, by omega⟩ : Fin σ₁'.size) from Fin.ext (by simp),
            GenLabelExtension.vertexMap, Fin.lastCases_castSucc,
            show (⟨σ₁.size, (by omega : σ₁.size < σ₁'.size)⟩ : Fin σ₁'.size) =
            Fin.cast hσ₁.symm (Fin.last σ₁.size) from Fin.ext (by simp)]
        exact hNewLabelled₁
      have h_rel_local : GenIsLocalFlag σ_rel B_rel 𝒢₁ Δ₁ :=
        ih ext_F₁.extendedType ext_F₁.extendedFlag 𝒢₁ Δ₁
          (hF₁.extensions ext_F₁) h_unl_le
          σ_rel B_rel ih_hσ' ih_hB ih_hstr ih_hcompat ih_hNewLabelled
      -- Transport: apply gen_relabel with π₁ to get locality at the double-relabelled
      -- type, then use GenIsLocalFlag_flagIso_gen to go to ext'₁.extendedType.
      have h_unl_B_rel : B_rel.unlabelledSize ≤ n + 1 := by
        unfold GenFlag.unlabelledSize
        -- B_rel.size = ext'₁.extendedFlag.size = B₁.size = F₁.size + 1
        -- σ_rel.size = ext'₁.extendedType.size = σ₁'.size + 1 = σ₁.size + 2
        -- So unlabelledSize = (F₁.size + 1) - (σ₁.size + 2)
        -- And hn : F₁.size - σ₁.size ≤ n + 1
        change ext'₁.extendedFlag.size - ext'₁.extendedType.size ≤ n + 1
        simp only [GenLabelExtension.extendedFlag, GenLabelExtension.extendedType]
        -- Now: B₁.size - (σ₁'.size + 1) ≤ n + 1
        unfold GenFlag.unlabelledSize at hn
        omega
      have h_dbl_local := gen_relabel (n + 1) (σ₂ := σ_rel) (F₂ := B_rel) π₁ h_rel_local h_unl_B_rel
      -- The double-relabelled type = ext'₁.extendedType
      have htype_dbl_eq : (⟨σ_rel.size, R.comap π₁ σ_rel.str⟩ : GenFlagType R) =
          ext'₁.extendedType := by
        change (⟨ext'₁.extendedType.size,
          R.comap π₁ (R.comap π₁ ext'₁.extendedType.str)⟩ : GenFlagType R) = ext'₁.extendedType
        have hstr_eq : R.comap π₁ (R.comap π₁ ext'₁.extendedType.str) =
            ext'₁.extendedType.str := by
          rw [← R.comap_comp,
              show (⇑π₁ ∘ ⇑π₁ : Fin ext'₁.extendedType.size → Fin ext'₁.extendedType.size) =
                id from funext (fun i => by simp [π₁, Equiv.swap_apply_self]),
              R.comap_id]
        exact show (⟨ext'₁.extendedType.size,
          R.comap π₁ (R.comap π₁ ext'₁.extendedType.str)⟩ : GenFlagType R) =
          ⟨ext'₁.extendedType.size, ext'₁.extendedType.str⟩ from
          congrArg _ hstr_eq
      -- Use GenIsLocalFlag_flagIso_gen to transport from double-relabelled to ext'₁
      exact GenIsLocalFlag_flagIso_gen B_rel.unlabelledSize htype_dbl_eq le_rfl
        (Equiv.refl _)
        (by change R.comap id ext'₁.extendedFlag.str = B_rel.str
            rw [R.comap_id])
        (fun i => by
          change B_rel.embedding (π₁ i) =
            ext'₁.extendedFlag.embedding (Fin.cast (congrArg GenFlagType.size htype_dbl_eq) i)
          have : Fin.cast (congrArg GenFlagType.size htype_dbl_eq) i = i := Fin.ext rfl
          rw [this]
          change ext'₁.extendedFlag.embedding (π₁ (π₁ i)) = ext'₁.extendedFlag.embedding i
          congr 1; simp [π₁, Equiv.swap_apply_self])
        h_dbl_local

/-- Size sum from overlap/covering: `H.size + σ.size = F.size + F'.size`. -/
private theorem gen_size_sum_of_overlap_covering {R : RelUniverse} {σ : GenFlagType R}
    {F F' H : GenFlag R σ}
    (e₁ : GenInducedEmbedding R σ F H) (e₂ : GenInducedEmbedding R σ F' H)
    (hoverlap : ∀ i : Fin H.size,
      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔ i ∈ Set.range H.embedding)
    (hcovering : ∀ i : Fin H.size,
      i ∈ Set.range e₁.toFun ∨ i ∈ Set.range e₂.toFun) :
    H.size + σ.size = F.size + F'.size := by
  set S₁ := Finset.univ.image e₁.toFun; set S₂ := Finset.univ.image e₂.toFun
  set Sσ := Finset.univ.image H.embedding
  have hS₁ : S₁.card = F.size := (Finset.card_image_of_injective _ e₁.injective).trans
    (Finset.card_univ.trans (Fintype.card_fin F.size))
  have hS₂ : S₂.card = F'.size := (Finset.card_image_of_injective _ e₂.injective).trans
    (Finset.card_univ.trans (Fintype.card_fin F'.size))
  have hSσ : Sσ.card = σ.size := (Finset.card_image_of_injective _ H.embedding.injective).trans
    (Finset.card_univ.trans (Fintype.card_fin σ.size))
  have hinter : S₁ ∩ S₂ = Sσ := by
    ext i; simp only [Finset.mem_inter, S₁, S₂, Sσ, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩⟩; exact (hoverlap i).mp ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩⟩
    · rintro ⟨k, rfl⟩
      have := (hoverlap (H.embedding k)).mpr ⟨k, rfl⟩
      exact ⟨⟨this.1.choose, this.1.choose_spec⟩, ⟨this.2.choose, this.2.choose_spec⟩⟩
  have hunion : S₁ ∪ S₂ = Finset.univ := by
    ext i; simp only [Finset.mem_union, S₁, S₂, Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    rcases hcovering i with ⟨j, hj⟩ | ⟨j, hj⟩
    · left; exact ⟨j, hj⟩
    · right; exact ⟨j, hj⟩
  have hcard := Finset.card_union_add_card_inter S₁ S₂
  rw [hunion, hinter, Finset.card_univ, Fintype.card_fin, hS₁, hS₂, hSσ] at hcard; linarith

/-- Generic decomposition at label extension: if `p(F,F';H) > 0` and `ext` is
    a label extension of H, then there exist local flags A, B at the extended
    type with `p(A,B;H^v) > 0`.
    Mirrors `decomposition_at_extension` for `simpleGraphUniverse`. -/
private theorem genDecomposition_at_extension {R : RelUniverse}
    (σ : GenFlagType R) (F F' H : GenFlag R σ)
    (𝒢 : GenGraphClass R) (Δ : GenGraphParam R)
    (hF : GenIsLocalFlag σ F 𝒢 Δ) (hF' : GenIsLocalFlag σ F' 𝒢 Δ)
    (hp : genJointInducedDensity R σ F F' H > 0)
    (ext : GenLabelExtension H) :
    ∃ (A B : GenFlag R ext.extendedType),
      genJointInducedDensity R ext.extendedType A B ext.extendedFlag > 0 ∧
      GenIsLocalFlag ext.extendedType A 𝒢 Δ ∧
      GenIsLocalFlag ext.extendedType B 𝒢 Δ := by
  -- Step 1: Extract witness decomposition
  obtain ⟨e₁, e₂, hoverlap, hcovering⟩ := gen_joint_pos_witness hp
  -- Step 2: Determine which side contains ext.vertex
  have hv_side := gen_vertex_in_exactly_one_side e₁ e₂
    hoverlap hcovering ext.vertex ext.unlabelled
  rcases hv_side with ⟨hv_in_e1, hv_not_e2⟩ | ⟨hv_not_e1, hv_in_e2⟩
  · -- Case 1: ext.vertex ∈ range e₁ (the F-side)
    -- Step 1a: u = e₁⁻¹(ext.vertex)
    obtain ⟨u, hu⟩ := hv_in_e1
    -- u is unlabelled in F
    have hu_unlab : u ∉ Set.range F.embedding := by
      intro ⟨i, hi⟩
      have : H.embedding i = ext.vertex := by
        have := e₁.compat i; rw [hi] at this; rw [← this, hu]
      exact ext.unlabelled ⟨i, this⟩
    -- Step 2: Define the label extension of F at u
    let extF : GenLabelExtension F := ⟨u, hu_unlab⟩
    -- Step 3: Type equality extF.extendedType = ext.extendedType
    -- Both have size σ.size + 1. For the structure:
    -- e₁ ∘ extF.vertexMap = ext.vertexMap
    have hcomp : ∀ i : Fin (σ.size + 1),
        e₁.toFun (extF.vertexMap i) = ext.vertexMap i := by
      intro i
      obtain (⟨j, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
      · simp only [GenLabelExtension.vertexMap, Fin.lastCases_castSucc]; exact e₁.compat j
      · simp only [GenLabelExtension.vertexMap, Fin.lastCases_last]; exact hu
    have htype_eq : extF.extendedType = ext.extendedType := by
      simp only [GenLabelExtension.extendedType]
      congr 1
      -- Goal: R.comap extF.vertexMap F.str = R.comap ext.vertexMap H.str
      -- From e₁.isInduced: R.comap e₁.toFun H.str = F.str
      -- So R.comap extF.vertexMap F.str
      --  = R.comap extF.vertexMap (R.comap e₁.toFun H.str)  [by e₁.isInduced]
      --  = R.comap (e₁.toFun ∘ extF.vertexMap) H.str        [by comap_comp]
      --  = R.comap ext.vertexMap H.str                       [since e₁ ∘ extF.vMap = ext.vMap]
      rw [← e₁.isInduced, ← R.comap_comp]
      congr 1; funext i; exact hcomp i
    -- A: constructed directly at ext.extendedType with str = F.str
    have aIsInduced : R.comap extF.vertexMap F.str = ext.extendedType.str := by
      change R.comap extF.vertexMap F.str = R.comap ext.vertexMap H.str
      rw [← e₁.isInduced, ← R.comap_comp]; congr 1; funext i; exact hcomp i
    let A : GenFlag R ext.extendedType :=
      ⟨F.size, F.str, ⟨extF.vertexMap, extF.vertexMap_injective⟩, aIsInduced,
       by have := Fintype.card_le_of_injective extF.vertexMap extF.vertexMap_injective
          simp [Fintype.card_fin] at this; exact this⟩
    -- A locality via GenIsLocalFlag_flagIso_gen (identity iso, cross-type)
    have hA_local : GenIsLocalFlag ext.extendedType A 𝒢 Δ :=
      GenIsLocalFlag_flagIso_gen A.unlabelledSize htype_eq le_rfl
        (Equiv.refl _)
        (by change R.comap id F.str = F.str; rw [R.comap_id])
        (fun i => by change extF.vertexMap i = extF.vertexMap (Fin.cast (congrArg GenFlagType.size htype_eq) i)
                     congr 1)
        (hF.extensions extF)
    -- B = H restricted to range(e₂) ∪ {ext.vertex}, built at ext.extendedType
    let bMap : Fin (F'.size + 1) → Fin H.size :=
      Fin.lastCases ext.vertex (fun j => e₂.toFun j)
    have bMap_inj : Function.Injective bMap := by
      intro a b hab
      obtain (⟨i, rfl⟩ | rfl) := a.eq_castSucc_or_eq_last
      · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
        · simp only [bMap, Fin.lastCases_castSucc] at hab
          exact congr_arg Fin.castSucc (e₂.injective hab)
        · exact absurd ⟨i, by simp only [bMap, Fin.lastCases_castSucc, Fin.lastCases_last] at hab; exact hab⟩ hv_not_e2
      · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
        · exact absurd ⟨j, by simp only [bMap, Fin.lastCases_castSucc, Fin.lastCases_last] at hab; exact hab.symm⟩ hv_not_e2
        · rfl
    let bEmbMap : Fin (σ.size + 1) → Fin (F'.size + 1) :=
      Fin.lastCases (Fin.last F'.size) (fun j => Fin.castSucc (F'.embedding j))
    have bEmbMap_inj : Function.Injective bEmbMap := by
      intro a b hab
      obtain (⟨i, rfl⟩ | rfl) := a.eq_castSucc_or_eq_last
      · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
        · simp only [bEmbMap, Fin.lastCases_castSucc, Fin.castSucc_inj] at hab
          exact congr_arg Fin.castSucc (F'.embedding.injective hab)
        · exact absurd (by simp only [bEmbMap, Fin.lastCases_castSucc, Fin.lastCases_last] at hab; exact hab) (Fin.castSucc_lt_last _).ne
      · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
        · exact absurd (by simp only [bEmbMap, Fin.lastCases_castSucc, Fin.lastCases_last] at hab; exact hab.symm) (Fin.castSucc_lt_last _).ne
        · rfl
    have bMap_bEmb_eq : ∀ i : Fin (σ.size + 1), bMap (bEmbMap i) = ext.vertexMap i := by
      intro i; obtain (⟨j, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
      · simp only [bEmbMap, bMap, GenLabelExtension.vertexMap, Fin.lastCases_castSucc]; exact e₂.compat j
      · simp only [bEmbMap, bMap, GenLabelExtension.vertexMap, Fin.lastCases_last]
    -- B's isInduced: R.comap bEmbMap (R.comap bMap H.str) = ext.extendedType.str
    have bIsInduced : R.comap bEmbMap (R.comap bMap H.str) = ext.extendedType.str := by
      rw [← R.comap_comp]; change R.comap (bMap ∘ bEmbMap) H.str = R.comap ext.vertexMap H.str
      congr 1; funext i; exact bMap_bEmb_eq i
    let B : GenFlag R ext.extendedType :=
      ⟨F'.size + 1, R.comap bMap H.str, ⟨bEmbMap, bEmbMap_inj⟩, bIsInduced,
       by change σ.size + 1 ≤ F'.size + 1; exact Nat.add_le_add_right F'.hsize 1⟩
    -- B locality via genAugmented_local_flag
    -- The structural condition R.comap castSucc B.str = F'.str follows from
    -- B.str = R.comap bMap H.str and bMap ∘ castSucc = e₂ and e₂.isInduced.
    have hB_local : GenIsLocalFlag ext.extendedType B 𝒢 Δ := by
      apply genAugmented_local_flag σ F' 𝒢 Δ hF' ext.extendedType B rfl rfl
      · -- R.comap castSuccMap B.str = F'.str
        -- B.str = R.comap bMap H.str, so R.comap cast (R.comap bMap H.str)
        -- = R.comap (bMap ∘ cast) H.str = R.comap e₂.toFun H.str = F'.str
        have : (fun i : Fin F'.size => (⟨i.val, by omega⟩ : Fin (F'.size + 1))) = Fin.castSucc :=
          funext fun i => Fin.ext (by simp [Fin.val_castSucc])
        rw [← R.comap_comp, this]
        have : bMap ∘ Fin.castSucc = e₂.toFun :=
          funext fun i => by simp only [Function.comp, bMap, Fin.lastCases_castSucc]
        rw [this]; exact e₂.isInduced
      · -- embedding compat
        intro k; change (bEmbMap (Fin.cast rfl (Fin.castSucc k))).val = (F'.embedding k).val
        simp [bEmbMap, Fin.cast_eq_self, Fin.lastCases_castSucc, Fin.val_castSucc]
      · -- new label position
        change (bEmbMap (Fin.cast rfl (Fin.last σ.size))).val = F'.size
        simp [bEmbMap, Fin.cast_eq_self, Fin.lastCases_last, Fin.val_last]
    -- JID > 0: transport from extF.extendedType
    -- At extF.extendedType, we can construct eA from e₁ and eB' from bMap,
    -- then transport the whole genJointCount > 0 via htype_eq ▸.
    -- eA: A → ext.extendedFlag via e₁
    let eA : GenInducedEmbedding R ext.extendedType A ext.extendedFlag :=
      { toFun := e₁.toFun, injective := e₁.injective
        isInduced := e₁.isInduced  -- R.comap e₁ H.str = F.str = A.str
        compat := fun i => hcomp i }
    -- eB: B → ext.extendedFlag via bMap
    let eB : GenInducedEmbedding R ext.extendedType B ext.extendedFlag :=
      { toFun := bMap, injective := bMap_inj, isInduced := rfl, compat := bMap_bEmb_eq }
    -- Overlap/covering
    have h_bMap_range : Set.range bMap = Set.range e₂.toFun ∪ {ext.vertex} := by
      ext x; simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]; constructor
      · rintro ⟨j, hj⟩; obtain (⟨k, rfl⟩ | rfl) := j.eq_castSucc_or_eq_last
        · left; exact ⟨k, by simp only [bMap, Fin.lastCases_castSucc] at hj; exact hj⟩
        · right; simp only [bMap, Fin.lastCases_last] at hj; exact hj.symm
      · rintro (⟨k, rfl⟩ | rfl)
        · exact ⟨Fin.castSucc k, by simp only [bMap, Fin.lastCases_castSucc]⟩
        · exact ⟨Fin.last _, by simp only [bMap, Fin.lastCases_last]⟩
    have hoverlap' : ∀ i : Fin ext.extendedFlag.size,
        (i ∈ Set.range eA.toFun ∧ i ∈ Set.range eB.toFun) ↔
          i ∈ Set.range ext.extendedFlag.embedding := by
      intro i
      rw [show Set.range eA.toFun = Set.range e₁.toFun from rfl,
          show Set.range eB.toFun = Set.range bMap from rfl,
          ext.range_extendedFlag_embedding, h_bMap_range]
      constructor
      · rintro ⟨hi_e1, hi_e2 | rfl⟩
        · left; exact (hoverlap i).mp ⟨hi_e1, hi_e2⟩
        · right; rfl
      · rintro (hi_emb | rfl)
        · exact ⟨((hoverlap i).mpr hi_emb).1, Or.inl ((hoverlap i).mpr hi_emb).2⟩
        · exact ⟨⟨u, hu⟩, Or.inr rfl⟩
    have hcovering' : ∀ i : Fin ext.extendedFlag.size,
        i ∈ Set.range eA.toFun ∨ i ∈ Set.range eB.toFun := by
      intro i
      rw [show Set.range eA.toFun = Set.range e₁.toFun from rfl,
          show Set.range eB.toFun = Set.range bMap from rfl, h_bMap_range]
      rcases hcovering i with h1 | h2
      · left; exact h1
      · right; left; exact h2
    -- genJointCount > 0
    have hjc_pos : 0 < genJointCount R ext.extendedType A B ext.extendedFlag := by
      unfold genJointCount; rw [Fintype.card_pos_iff]; exact ⟨⟨⟨eA, eB⟩, hoverlap', hcovering'⟩⟩
    -- genJointInducedDensity > 0
    have hF_le_H : F.size ≤ H.size := by
      simpa [Fintype.card_fin] using Fintype.card_le_of_injective e₁.toFun e₁.injective
    have hF'_le_H : F'.size ≤ H.size := by
      simpa [Fintype.card_fin] using Fintype.card_le_of_injective e₂.toFun e₂.injective
    have hjid_pos : genJointInducedDensity R ext.extendedType A B ext.extendedFlag > 0 := by
      unfold genJointInducedDensity; apply div_pos (Nat.cast_pos.mpr hjc_pos)
      apply mul_pos
      · exact Nat.cast_pos.mpr (Nat.choose_pos (by change F.size - (σ.size + 1) ≤ H.size - (σ.size + 1); omega))
      · -- Need: F'.size - σ.size ≤ H.size - σ.size - 1 - (F.size - σ.size - 1)
        -- From size sum: H.size + σ.size = F.size + F'.size (inclusion-exclusion)
        have hsize_sum : H.size + σ.size = F.size + F'.size := by
          exact gen_size_sum_of_overlap_covering e₁ e₂ hoverlap hcovering
        exact Nat.cast_pos.mpr (Nat.choose_pos (by
          change F'.size + 1 - (σ.size + 1) ≤ H.size - (σ.size + 1) - (F.size - (σ.size + 1))
          have h1 : σ.size + 1 ≤ F.size := by
            simpa [Fintype.card_fin] using Fintype.card_le_of_injective extF.vertexMap extF.vertexMap_injective
          omega))
    exact ⟨A, B, hjid_pos, hA_local, hB_local⟩
  · -- Case 2: ext.vertex ∈ range e₂ (the F'-side) — swap F and F'
    have hp' : genJointInducedDensity R σ F' F H > 0 := by
      rwa [genJointInducedDensity_comm]
    obtain ⟨e₁', e₂', hoverlap', hcovering'⟩ := gen_joint_pos_witness hp'
    -- Determine which side contains ext.vertex for the swapped version
    have hv_side' := gen_vertex_in_exactly_one_side e₁' e₂'
      hoverlap' hcovering' ext.vertex ext.unlabelled
    rcases hv_side' with ⟨hv_in_e1', hv_not_e2'⟩ | ⟨hv_not_e1', hv_in_e2'⟩
    · -- ext.vertex ∈ range e₁' (now the F'-side): proceed as Case 1 with F' and F swapped
      obtain ⟨u', hu'⟩ := hv_in_e1'
      have hu'_unlab : u' ∉ Set.range F'.embedding := by
        intro ⟨i, hi⟩
        have : H.embedding i = ext.vertex := by
          have := e₁'.compat i; rw [hi] at this; rw [← this, hu']
        exact ext.unlabelled ⟨i, this⟩
      let extF' : GenLabelExtension F' := ⟨u', hu'_unlab⟩
      have hcomp' : ∀ i : Fin (σ.size + 1),
          e₁'.toFun (extF'.vertexMap i) = ext.vertexMap i := by
        intro i
        obtain (⟨j, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
        · simp only [GenLabelExtension.vertexMap, Fin.lastCases_castSucc]; exact e₁'.compat j
        · simp only [GenLabelExtension.vertexMap, Fin.lastCases_last]; exact hu'
      have htype_eq' : extF'.extendedType = ext.extendedType := by
        simp only [GenLabelExtension.extendedType]
        congr 1
        rw [← e₁'.isInduced, ← R.comap_comp]
        congr 1; funext i; exact hcomp' i
      -- A: direct construction at ext.extendedType with str = F'.str
      have aIsInduced' : R.comap extF'.vertexMap F'.str = ext.extendedType.str := by
        change R.comap extF'.vertexMap F'.str = R.comap ext.vertexMap H.str
        rw [← e₁'.isInduced, ← R.comap_comp]; congr 1; funext i; exact hcomp' i
      let A : GenFlag R ext.extendedType :=
        ⟨F'.size, F'.str, ⟨extF'.vertexMap, extF'.vertexMap_injective⟩, aIsInduced',
         by have := Fintype.card_le_of_injective extF'.vertexMap extF'.vertexMap_injective
            simp [Fintype.card_fin] at this; exact this⟩
      have hA_local : GenIsLocalFlag ext.extendedType A 𝒢 Δ :=
        GenIsLocalFlag_flagIso_gen A.unlabelledSize htype_eq' le_rfl (Equiv.refl _)
          (by change R.comap id F'.str = F'.str; rw [R.comap_id])
          (fun i => by change extF'.vertexMap i = extF'.vertexMap (Fin.cast _ i); congr 1)
          (hF'.extensions extF')
      -- B from range(e₂') ∪ {vertex}, swapped roles: F is the B-side
      let bMap' : Fin (F.size + 1) → Fin H.size :=
        Fin.lastCases ext.vertex (fun j => e₂'.toFun j)
      let bEmbMap' : Fin (σ.size + 1) → Fin (F.size + 1) :=
        Fin.lastCases (Fin.last F.size) (fun j => Fin.castSucc (F.embedding j))
      have bMap'_bEmb'_eq : ∀ i : Fin (σ.size + 1), bMap' (bEmbMap' i) = ext.vertexMap i := by
        intro i; obtain (⟨j, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
        · simp only [bEmbMap', bMap', GenLabelExtension.vertexMap, Fin.lastCases_castSucc]; exact e₂'.compat j
        · simp only [bEmbMap', bMap', GenLabelExtension.vertexMap, Fin.lastCases_last]
      have bEmbMap'_inj : Function.Injective bEmbMap' := by
        intro a b hab
        obtain (⟨i, rfl⟩ | rfl) := a.eq_castSucc_or_eq_last
        · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
          · simp only [bEmbMap', Fin.lastCases_castSucc, Fin.castSucc_inj] at hab
            exact congr_arg Fin.castSucc (F.embedding.injective hab)
          · exact absurd (by simp only [bEmbMap', Fin.lastCases_castSucc, Fin.lastCases_last] at hab; exact hab) (Fin.castSucc_lt_last _).ne
        · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
          · exact absurd (by simp only [bEmbMap', Fin.lastCases_castSucc, Fin.lastCases_last] at hab; exact hab.symm) (Fin.castSucc_lt_last _).ne
          · rfl
      let B : GenFlag R ext.extendedType :=
        ⟨F.size + 1, R.comap bMap' H.str, ⟨bEmbMap', bEmbMap'_inj⟩,
         by rw [← R.comap_comp]; congr 1; funext i; exact bMap'_bEmb'_eq i,
         by change σ.size + 1 ≤ F.size + 1; exact Nat.add_le_add_right F.hsize 1⟩
      have hB_local : GenIsLocalFlag ext.extendedType B 𝒢 Δ := by
        apply genAugmented_local_flag σ F 𝒢 Δ hF ext.extendedType B rfl rfl
        · have : (fun i : Fin F.size => (⟨i.val, by omega⟩ : Fin (F.size + 1))) = Fin.castSucc :=
            funext fun i => Fin.ext (by simp [Fin.val_castSucc])
          rw [← R.comap_comp, this]
          have : bMap' ∘ Fin.castSucc = e₂'.toFun :=
            funext fun i => by simp only [Function.comp, bMap', Fin.lastCases_castSucc]
          rw [this]; exact e₂'.isInduced
        · intro k; change (bEmbMap' (Fin.cast rfl (Fin.castSucc k))).val = (F.embedding k).val
          simp [bEmbMap', Fin.cast_eq_self, Fin.lastCases_castSucc, Fin.val_castSucc]
        · change (bEmbMap' (Fin.cast rfl (Fin.last σ.size))).val = F.size
          simp [bEmbMap', Fin.cast_eq_self, Fin.lastCases_last, Fin.val_last]
      -- eA/eB + JID > 0
      let eA : GenInducedEmbedding R ext.extendedType A ext.extendedFlag :=
        { toFun := e₁'.toFun, injective := e₁'.injective, isInduced := e₁'.isInduced, compat := hcomp' }
      let eB : GenInducedEmbedding R ext.extendedType B ext.extendedFlag :=
        { toFun := bMap', injective := by
            intro a b hab; obtain (⟨i, rfl⟩ | rfl) := a.eq_castSucc_or_eq_last
            · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
              · simp only [bMap', Fin.lastCases_castSucc] at hab; exact congr_arg Fin.castSucc (e₂'.injective hab)
              · exact absurd ⟨i, by simp only [bMap', Fin.lastCases_castSucc, Fin.lastCases_last] at hab; exact hab⟩ hv_not_e2'
            · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
              · exact absurd ⟨j, by simp only [bMap', Fin.lastCases_castSucc, Fin.lastCases_last] at hab; exact hab.symm⟩ hv_not_e2'
              · rfl
          isInduced := rfl, compat := bMap'_bEmb'_eq }
      have hjc_pos : 0 < genJointCount R ext.extendedType A B ext.extendedFlag := by
        unfold genJointCount; rw [Fintype.card_pos_iff]
        have h_bMap'_range : Set.range bMap' = Set.range e₂'.toFun ∪ {ext.vertex} := by
          ext x; simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]; constructor
          · rintro ⟨j, hj⟩; obtain (⟨k, rfl⟩ | rfl) := j.eq_castSucc_or_eq_last
            · left; exact ⟨k, by simp only [bMap', Fin.lastCases_castSucc] at hj; exact hj⟩
            · right; simp only [bMap', Fin.lastCases_last] at hj; exact hj.symm
          · rintro (⟨k, rfl⟩ | rfl)
            · exact ⟨Fin.castSucc k, by simp only [bMap', Fin.lastCases_castSucc]⟩
            · exact ⟨Fin.last _, by simp only [bMap', Fin.lastCases_last]⟩
        exact ⟨⟨⟨eA, eB⟩, fun i => by
          rw [show Set.range eA.toFun = Set.range e₁'.toFun from rfl,
              show Set.range eB.toFun = Set.range bMap' from rfl,
              ext.range_extendedFlag_embedding, h_bMap'_range]
          constructor
          · rintro ⟨hi1, hi2 | rfl⟩
            · left; exact (hoverlap' i).mp ⟨hi1, hi2⟩
            · right; rfl
          · rintro (hi | rfl)
            · exact ⟨((hoverlap' i).mpr hi).1, Or.inl ((hoverlap' i).mpr hi).2⟩
            · exact ⟨⟨u', hu'⟩, Or.inr rfl⟩,
          fun i => by
          rw [show Set.range eA.toFun = Set.range e₁'.toFun from rfl,
              show Set.range eB.toFun = Set.range bMap' from rfl, h_bMap'_range]
          rcases hcovering' i with h1 | h2
          · left; exact h1
          · right; left; exact h2⟩⟩
      have hjid_pos : genJointInducedDensity R ext.extendedType A B ext.extendedFlag > 0 := by
        unfold genJointInducedDensity; apply div_pos (Nat.cast_pos.mpr hjc_pos); apply mul_pos
        · exact Nat.cast_pos.mpr (Nat.choose_pos (by
            have := Fintype.card_le_of_injective e₁'.toFun e₁'.injective
            simp [Fintype.card_fin] at this; change F'.size - (σ.size + 1) ≤ H.size - (σ.size + 1); omega))
        · have hsize_sum : H.size + σ.size = F'.size + F.size :=
            gen_size_sum_of_overlap_covering e₁' e₂' hoverlap' hcovering'
          exact Nat.cast_pos.mpr (Nat.choose_pos (by
            have h1 : σ.size + 1 ≤ F'.size := by
              simpa [Fintype.card_fin] using Fintype.card_le_of_injective extF'.vertexMap extF'.vertexMap_injective
            change F.size + 1 - (σ.size + 1) ≤ H.size - (σ.size + 1) - (F'.size - (σ.size + 1)); omega))
      exact ⟨A, B, hjid_pos, hA_local, hB_local⟩
    · -- ext.vertex ∈ range e₂' (the F-side in the swapped version): same as Case 1
      -- We can use the original e₂ (F-side) and e₁ (F'-side) with swapped overlap
      have hoverlap_swap : ∀ i : Fin H.size,
          (i ∈ Set.range e₂.toFun ∧ i ∈ Set.range e₁.toFun) ↔
            i ∈ Set.range H.embedding := by
        intro i; rw [and_comm]; exact hoverlap i
      obtain ⟨u', hu'⟩ := hv_in_e2'
      have hu'_unlab : u' ∉ Set.range F.embedding := by
        intro ⟨i, hi⟩
        have : H.embedding i = ext.vertex := by
          have := e₂'.compat i; rw [hi] at this; rw [← this, hu']
        exact ext.unlabelled ⟨i, this⟩
      let extF'' : GenLabelExtension F := ⟨u', hu'_unlab⟩
      have hcomp'' : ∀ i : Fin (σ.size + 1),
          e₂'.toFun (extF''.vertexMap i) = ext.vertexMap i := by
        intro i; obtain (⟨j, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
        · simp only [GenLabelExtension.vertexMap, Fin.lastCases_castSucc]; exact e₂'.compat j
        · simp only [GenLabelExtension.vertexMap, Fin.lastCases_last]; exact hu'
      have htype_eq'' : extF''.extendedType = ext.extendedType := by
        simp only [GenLabelExtension.extendedType]; congr 1
        rw [← e₂'.isInduced, ← R.comap_comp]; congr 1; funext i; exact hcomp'' i
      -- A: direct construction at ext.extendedType with str = F.str
      have aIsInduced'' : R.comap extF''.vertexMap F.str = ext.extendedType.str := by
        change R.comap extF''.vertexMap F.str = R.comap ext.vertexMap H.str
        rw [← e₂'.isInduced, ← R.comap_comp]; congr 1; funext i; exact hcomp'' i
      let A : GenFlag R ext.extendedType :=
        ⟨F.size, F.str, ⟨extF''.vertexMap, extF''.vertexMap_injective⟩, aIsInduced'',
         by have := Fintype.card_le_of_injective extF''.vertexMap extF''.vertexMap_injective
            simp [Fintype.card_fin] at this; exact this⟩
      have hA_local : GenIsLocalFlag ext.extendedType A 𝒢 Δ :=
        GenIsLocalFlag_flagIso_gen A.unlabelledSize htype_eq'' le_rfl (Equiv.refl _)
          (by change R.comap id F.str = F.str; rw [R.comap_id])
          (fun i => by change extF''.vertexMap i = extF''.vertexMap (Fin.cast _ i); congr 1)
          (hF.extensions extF'')
      -- B from range(e₁') ∪ {vertex}: F' is the B-side
      let bMap'' : Fin (F'.size + 1) → Fin H.size :=
        Fin.lastCases ext.vertex (fun j => e₁'.toFun j)
      let bEmbMap'' : Fin (σ.size + 1) → Fin (F'.size + 1) :=
        Fin.lastCases (Fin.last F'.size) (fun j => Fin.castSucc (F'.embedding j))
      have bMap''_bEmb''_eq : ∀ i : Fin (σ.size + 1), bMap'' (bEmbMap'' i) = ext.vertexMap i := by
        intro i; obtain (⟨j, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
        · simp only [bEmbMap'', bMap'', GenLabelExtension.vertexMap, Fin.lastCases_castSucc]; exact e₁'.compat j
        · simp only [bEmbMap'', bMap'', GenLabelExtension.vertexMap, Fin.lastCases_last]
      have bEmbMap''_inj : Function.Injective bEmbMap'' := by
        intro a b hab
        obtain (⟨i, rfl⟩ | rfl) := a.eq_castSucc_or_eq_last
        · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
          · simp only [bEmbMap'', Fin.lastCases_castSucc, Fin.castSucc_inj] at hab
            exact congr_arg Fin.castSucc (F'.embedding.injective hab)
          · exact absurd (by simp only [bEmbMap'', Fin.lastCases_castSucc, Fin.lastCases_last] at hab; exact hab) (Fin.castSucc_lt_last _).ne
        · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
          · exact absurd (by simp only [bEmbMap'', Fin.lastCases_castSucc, Fin.lastCases_last] at hab; exact hab.symm) (Fin.castSucc_lt_last _).ne
          · rfl
      let B : GenFlag R ext.extendedType :=
        ⟨F'.size + 1, R.comap bMap'' H.str, ⟨bEmbMap'', bEmbMap''_inj⟩,
         by rw [← R.comap_comp]; congr 1; funext i; exact bMap''_bEmb''_eq i,
         by change σ.size + 1 ≤ F'.size + 1; exact Nat.add_le_add_right F'.hsize 1⟩
      have hB_local : GenIsLocalFlag ext.extendedType B 𝒢 Δ := by
        apply genAugmented_local_flag σ F' 𝒢 Δ hF' ext.extendedType B rfl rfl
        · have : (fun i : Fin F'.size => (⟨i.val, by omega⟩ : Fin (F'.size + 1))) = Fin.castSucc :=
            funext fun i => Fin.ext (by simp [Fin.val_castSucc])
          rw [← R.comap_comp, this]
          have : bMap'' ∘ Fin.castSucc = e₁'.toFun :=
            funext fun i => by simp only [Function.comp, bMap'', Fin.lastCases_castSucc]
          rw [this]; exact e₁'.isInduced
        · intro k; change (bEmbMap'' (Fin.cast rfl (Fin.castSucc k))).val = (F'.embedding k).val
          simp [bEmbMap'', Fin.cast_eq_self, Fin.lastCases_castSucc, Fin.val_castSucc]
        · change (bEmbMap'' (Fin.cast rfl (Fin.last σ.size))).val = F'.size
          simp [bEmbMap'', Fin.cast_eq_self, Fin.lastCases_last, Fin.val_last]
      -- eA/eB + JID > 0 (same pattern as Case 1 with e₂'/e₁' swapped)
      let eA : GenInducedEmbedding R ext.extendedType A ext.extendedFlag :=
        { toFun := e₂'.toFun, injective := e₂'.injective, isInduced := e₂'.isInduced, compat := hcomp'' }
      let eB : GenInducedEmbedding R ext.extendedType B ext.extendedFlag :=
        { toFun := bMap'', injective := by
            intro a b hab; obtain (⟨i, rfl⟩ | rfl) := a.eq_castSucc_or_eq_last
            · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
              · simp only [bMap'', Fin.lastCases_castSucc] at hab; exact congr_arg Fin.castSucc (e₁'.injective hab)
              · exact absurd ⟨i, by simp only [bMap'', Fin.lastCases_castSucc, Fin.lastCases_last] at hab; exact hab⟩ hv_not_e1'
            · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
              · exact absurd ⟨j, by simp only [bMap'', Fin.lastCases_castSucc, Fin.lastCases_last] at hab; exact hab.symm⟩ hv_not_e1'
              · rfl
          isInduced := rfl, compat := bMap''_bEmb''_eq }
      have hjc_pos : 0 < genJointCount R ext.extendedType A B ext.extendedFlag := by
        unfold genJointCount; rw [Fintype.card_pos_iff]
        have h_bMap''_range : Set.range bMap'' = Set.range e₁'.toFun ∪ {ext.vertex} := by
          ext x; simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]; constructor
          · rintro ⟨j, hj⟩; obtain (⟨k, rfl⟩ | rfl) := j.eq_castSucc_or_eq_last
            · left; exact ⟨k, by simp only [bMap'', Fin.lastCases_castSucc] at hj; exact hj⟩
            · right; simp only [bMap'', Fin.lastCases_last] at hj; exact hj.symm
          · rintro (⟨k, rfl⟩ | rfl)
            · exact ⟨Fin.castSucc k, by simp only [bMap'', Fin.lastCases_castSucc]⟩
            · exact ⟨Fin.last _, by simp only [bMap'', Fin.lastCases_last]⟩
        exact ⟨⟨⟨eA, eB⟩, fun i => by
          rw [show Set.range eA.toFun = Set.range e₂'.toFun from rfl,
              show Set.range eB.toFun = Set.range bMap'' from rfl,
              ext.range_extendedFlag_embedding, h_bMap''_range]
          constructor
          · rintro ⟨hi1, hi2 | rfl⟩
            · left; exact (hoverlap' i).mp ⟨hi2, hi1⟩
            · right; rfl
          · rintro (hi | rfl)
            · exact ⟨((hoverlap' i).mpr hi).2, Or.inl ((hoverlap' i).mpr hi).1⟩
            · exact ⟨⟨u', hu'⟩, Or.inr rfl⟩,
          fun i => by
          rw [show Set.range eA.toFun = Set.range e₂'.toFun from rfl,
              show Set.range eB.toFun = Set.range bMap'' from rfl, h_bMap''_range]
          rcases hcovering' i with h_e1' | h_e2'
          · right; left; exact h_e1'
          · left; exact h_e2'⟩⟩
      have hjid_pos : genJointInducedDensity R ext.extendedType A B ext.extendedFlag > 0 := by
        unfold genJointInducedDensity; apply div_pos (Nat.cast_pos.mpr hjc_pos); apply mul_pos
        · exact Nat.cast_pos.mpr (Nat.choose_pos (by
            have := Fintype.card_le_of_injective e₂'.toFun e₂'.injective
            simp [Fintype.card_fin] at this; change F.size - (σ.size + 1) ≤ H.size - (σ.size + 1); omega))
        · have hsize_sum : H.size + σ.size = F.size + F'.size := by
            have := gen_size_sum_of_overlap_covering e₁' e₂' hoverlap' hcovering'; omega
          exact Nat.cast_pos.mpr (Nat.choose_pos (by
            have h1 : σ.size + 1 ≤ F.size := by
              simpa [Fintype.card_fin] using Fintype.card_le_of_injective extF''.vertexMap extF''.vertexMap_injective
            change F'.size + 1 - (σ.size + 1) ≤ H.size - (σ.size + 1) - (F.size - (σ.size + 1)); omega))
      exact ⟨A, B, hjid_pos, hA_local, hB_local⟩

/-- **Generic product closure** by well-founded induction on `H.unlabelledSize`.
    At each step bounded density follows from `genBounded_density_of_joint_pos`,
    and the label extension property from `genDecomposition_at_extension` + the IH.

    Proved for `simpleGraphUniverse` as `product_closure`. -/
private theorem genProduct_closure_aux {R : RelUniverse} (n : ℕ) :
    ∀ (σ : GenFlagType R) (F F' H : GenFlag R σ)
      (𝒢 : GenGraphClass R) (Δ : GenGraphParam R),
      H.unlabelledSize ≤ n →
      GenIsLocalFlag σ F 𝒢 Δ →
      GenIsLocalFlag σ F' 𝒢 Δ →
      genJointInducedDensity R σ F F' H > 0 →
      GenIsLocalFlag σ H 𝒢 Δ := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro σ F F' H 𝒢 Δ hle hF hF' hp
  refine GenIsLocalFlag.intro σ H 𝒢 Δ
    (genBounded_density_of_joint_pos σ F F' H 𝒢 Δ hF.bounded hF'.bounded hp)
    fun ext => ?_
  -- Goal: GenIsLocalFlag ext.extendedType ext.extendedFlag 𝒢 Δ
  -- Step 1: Get local σ'-flags A, B with p(A,B;H^v) > 0.
  obtain ⟨A, B, hp_ext, hA_local, hB_local⟩ :=
    genDecomposition_at_extension σ F F' H 𝒢 Δ hF hF' hp ext
  -- Step 2: H^v has strictly fewer unlabelled vertices than H.
  have hlt : ext.extendedFlag.unlabelledSize < H.unlabelledSize := by
    have hσ_lt : σ.size < H.size := by
      by_contra h; push_neg at h
      have hsz : H.size = σ.size := Nat.le_antisymm h H.hsize
      exact ext.unlabelled
        (H.embedding.injective.surjective_of_finite (finCongr hsz.symm) ext.vertex)
    simp only [GenFlag.unlabelledSize, GenLabelExtension.extendedFlag,
      GenLabelExtension.extendedType]
    omega
  -- Step 3: Apply the IH at the σ'-level.
  exact ih ext.extendedFlag.unlabelledSize (lt_of_lt_of_le hlt hle)
    ext.extendedType A B ext.extendedFlag 𝒢 Δ le_rfl hA_local hB_local hp_ext

/-- **Generic product closure**: if F and F' are local flags and H appears in
    their product with positive joint density, then H is also local.

    Proved by well-founded induction mirroring `product_closure`. -/
theorem genProduct_closure {R : RelUniverse} (σ : GenFlagType R)
    (F F' H : GenFlag R σ) (𝒢 : GenGraphClass R) (Δ : GenGraphParam R)
    (hF : GenIsLocalFlag σ F 𝒢 Δ) (hF' : GenIsLocalFlag σ F' 𝒢 Δ)
    (hp : genJointInducedDensity R σ F F' H > 0) :
    GenIsLocalFlag σ H 𝒢 Δ :=
  genProduct_closure_aux H.unlabelledSize σ F F' H 𝒢 Δ le_rfl hF hF' hp

/-- Every class in the support of `genLocalFlagProduct` is a local flag,
    provided F and F' are local.  Follows from `genProduct_closure`. -/
theorem genLocalFlagProduct_local_support {R : RelUniverse} {σ : GenFlagType R}
    (F F' : GenFlag R σ) (𝒢 : GenGraphClass R) (Δ : GenGraphParam R)
    (hF : GenIsLocalFlag σ F 𝒢 Δ) (hF' : GenIsLocalFlag σ F' 𝒢 Δ)
    (cls : GenFlagClass R σ) (hcls : cls ∈ (genLocalFlagProduct R σ F F').support) :
    GenIsLocalFlag σ cls.out 𝒢 Δ := by
  simp only [genLocalFlagProduct] at hcls
  by_cases hn : σ.size ≤ F.size + F'.size - σ.size
  · rw [dif_pos hn] at hcls
    simp only [Finsupp.mem_support_iff] at hcls
    rw [Finsupp.smul_apply] at hcls
    have hscalar_ne : ((↑(genFlagAutCount R σ F) * ↑(genFlagAutCount R σ F'))⁻¹ : ℝ) ≠ 0 :=
      inv_ne_zero (mul_ne_zero
        (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (genFlagAutCount_pos σ F)))
        (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (genFlagAutCount_pos σ F'))))
    have hsum_ne := right_ne_zero_of_mul (by rwa [smul_eq_mul] at hcls)
    rw [Finsupp.finset_sum_apply] at hsum_ne
    by_contra h_not_local
    apply hsum_ne
    apply Finset.sum_eq_zero
    intro cls' _
    simp only [Finsupp.single_apply]
    split_ifs with heq
    · subst heq
      by_contra h_jid_ne
      have h_jid_nn : 0 ≤ genJointInducedDensity R σ F F' cls'.out := by
        unfold genJointInducedDensity
        exact div_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      exact h_not_local (genProduct_closure σ F F' cls'.out 𝒢 Δ hF hF'
        (lt_of_le_of_ne h_jid_nn (Ne.symm h_jid_ne)))
    · rfl
  · rw [dif_neg hn] at hcls
    exact absurd hcls (by simp [Finsupp.support_zero])

/-- `genLocalFlagProduct_class` evaluated on representatives equals `genLocalFlagProduct`. -/
theorem genLocalFlagProduct_class_out {R : RelUniverse} (σ : GenFlagType R)
    (cls₁ cls₂ : GenFlagClass R σ) :
    genLocalFlagProduct_class R σ cls₁ cls₂ = genLocalFlagProduct R σ cls₁.out cls₂.out := by
  conv_lhs => rw [← Quotient.out_eq cls₁, ← Quotient.out_eq cls₂]
  exact genLocalFlagProduct_class_mk σ cls₁.out cls₂.out

/-- Every class in the support of `v.mul w` is local, provided v and w have
    local support.  Follows from `genLocalFlagProduct_local_support`. -/
theorem genMul_local_support {R : RelUniverse} {σ : GenFlagType R}
    (v w : GenFlagAlg R σ) (𝒢 : GenGraphClass R) (Δ : GenGraphParam R)
    (hv : ∀ cls ∈ v.support, GenIsLocalFlag σ cls.out 𝒢 Δ)
    (hw : ∀ cls ∈ w.support, GenIsLocalFlag σ cls.out 𝒢 Δ)
    (cls : GenFlagClass R σ) (hcls : cls ∈ (v.mul w).support) :
    GenIsLocalFlag σ cls.out 𝒢 Δ := by
  by_contra h_not_local
  have hzero : (v.mul w) cls = 0 := by
    simp only [GenFlagAlg.mul, Finsupp.sum]
    rw [Finsupp.finset_sum_apply]
    apply Finset.sum_eq_zero
    intro cls₁ hcls₁
    rw [Finsupp.finset_sum_apply]
    apply Finset.sum_eq_zero
    intro cls₂ hcls₂
    simp only [Finsupp.smul_apply, smul_eq_mul]
    by_cases h : (genLocalFlagProduct_class R σ cls₁ cls₂) cls = 0
    · rw [h, mul_zero]
    · exfalso; apply h_not_local
      rw [genLocalFlagProduct_class_out] at h
      exact genLocalFlagProduct_local_support cls₁.out cls₂.out 𝒢 Δ
        (hv cls₁ hcls₁) (hw cls₂ hcls₂) cls (Finsupp.mem_support_iff.mpr h)
  exact Finsupp.mem_support_iff.mp hcls hzero

/-! ## Phase 4g: Generic Limit Functionals and SDP Method

Generic versions of the limit functional infrastructure and SDP method
for arbitrary `RelUniverse`. These generalise the concrete constructions
for `simpleGraphUniverse` proved above. -/

set_option maxHeartbeats 1600000 in
/-- **Generic product limit** (Theorem 2.3) for arbitrary `RelUniverse`:
    The product of unlabelled evaluation densities converges to the product's density.

    Proved for `simpleGraphUniverse` as `product_limit` from `product_limit_basis`
    (orbit counting + overlap bounds + Vandermonde asymptotics, ~3000 lines).
    The generic version holds by the same argument; translation is deferred. -/
theorem genProduct_limit (R : RelUniverse) (σ : GenFlagType R)
    (f g : GenFlagAlg R σ)
    (𝒢 : GenGraphClass R) (Δ : GenGraphParam R)
    (hf_local : ∀ cls ∈ f.support, GenIsLocalFlag σ cls.out 𝒢 Δ)
    (hg_local : ∀ cls ∈ g.support, GenIsLocalFlag σ cls.out 𝒢 Δ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ Δ₀ : ℕ, ∀ G : GenFlag R σ, 𝒢 G.forget → Δ₀ ≤ Δ G.forget →
        |genUnlabelledEvalDensity f G Δ * genUnlabelledEvalDensity g G Δ -
         genUnlabelledEvalDensity (f.mul g) G Δ| ≤ ε := by
  -- Bilinear extension from genProduct_limit_basis (sorry'd).
  have genProduct_limit_basis : ∀ (F F' : GenFlag R σ),
      GenIsLocalFlag σ F 𝒢 Δ → GenIsLocalFlag σ F' 𝒢 Δ →
      ∀ ε : ℝ, 0 < ε → ∃ Δ₀ : ℕ, ∀ G : GenFlag R σ, 𝒢 G.forget → Δ₀ ≤ Δ G.forget →
        |genUnlabelledDensity R σ F G Δ * genUnlabelledDensity R σ F' G Δ -
         genUnlabelledEvalDensity (genLocalFlagProduct R σ F F') G Δ| ≤ ε := by
    -- Generic translation of `product_limit_basis` for `simpleGraphUniverse`.
    -- Sub-lemmas for orbit counting + overlap bounds are sorry'd
    -- (pending translation from the ~600-line SimpleGraph embedding constructions).
    intro F F' hF hF' ε hε
    -- Helper: genFlagIso_toFlag_of_size_eq (inline, mirrors flagIso_toFlag_of_size_eq)
    have genFlagIso_toFlag_of_size_eq : ∀ (H : GenFlag R σ), H.size = σ.size →
        GenFlagIso σ H σ.toFlag := by
      intro H hsz
      let ψ : Fin σ.size → Fin σ.size := (finCongr hsz) ∘ H.embedding
      have hψ_inj : Function.Injective ψ := (Equiv.injective _).comp H.embedding.injective
      have hψ_bij : Function.Bijective ψ := (Finite.injective_iff_bijective).mp hψ_inj
      let ψ_equiv := Equiv.ofBijective ψ hψ_bij
      let φ_equiv : Fin H.size ≃ Fin σ.size := (finCongr hsz).trans ψ_equiv.symm
      -- φ_equiv is the inverse of H.embedding (cast through finCongr)
      have hemb_comp_φ : ∀ x : Fin H.size,
          H.embedding (φ_equiv x) = x := by
        intro x; apply (finCongr hsz).injective
        change ψ (ψ_equiv.symm ((finCongr hsz) x)) = (finCongr hsz) x
        exact Equiv.ofBijective_apply_symm_apply ψ hψ_bij ((finCongr hsz) x)
      refine ⟨φ_equiv, ?_, fun i => ?_⟩
      · -- R.comap φ σ.str = H.str
        -- Use: R.comap φ σ.str = R.comap φ (R.comap emb H.str)  [by H.isInduced]
        --    = R.comap (emb ∘ φ) H.str  [by comap_comp]
        --    = R.comap id H.str  [since emb ∘ φ = id by hemb_comp_φ]
        --    = H.str  [by comap_id]
        have hemb_comp_eq : (H.embedding : Fin σ.size → Fin H.size) ∘ (⇑φ_equiv) = id :=
          funext (fun x => hemb_comp_φ x)
        calc R.comap (⇑φ_equiv) σ.toFlag.str
            = R.comap (⇑φ_equiv) σ.str := rfl
          _ = R.comap (⇑φ_equiv) (R.comap H.embedding H.str) := by rw [H.isInduced]
          _ = R.comap (H.embedding ∘ ⇑φ_equiv) H.str := by rw [R.comap_comp]
          _ = R.comap id H.str := by rw [hemb_comp_eq]
          _ = H.str := R.comap_id H.str
      · -- φ (H.embedding i) = i (compatibility)
        change φ_equiv (H.embedding i) = (Function.Embedding.refl (Fin σ.size)) i
        simp only [Function.Embedding.refl, φ_equiv, Equiv.trans_apply]
        change ψ_equiv.symm (finCongr hsz (H.embedding i)) = i
        change ψ_equiv.symm (ψ_equiv i) = i
        exact ψ_equiv.symm_apply_apply i
    -- Inline: genUnlabelledDensity_flagIso
    have genUD_flagIso : ∀ {H₁ H₂ G' : GenFlag R σ},
        GenFlagIso σ H₁ H₂ → genUnlabelledDensity R σ H₁ G' Δ =
          genUnlabelledDensity R σ H₂ G' Δ := by
      intro H₁ H₂ G' hiso
      unfold genUnlabelledDensity
      rw [genInducedCount_flagIso hiso, genFlagAutCount_flagIso hiso,
        show H₁.size = H₂.size from genFlagIso_size_eq hiso]
    -- Inline: genUnlabelledDensity_type_eq_one
    have genUD_type_eq_one : ∀ (G' : GenFlag R σ),
        genUnlabelledDensity R σ σ.toFlag G' Δ = 1 := by
      intro G'
      unfold genUnlabelledDensity
      rw [genInducedCount_toFlag_eq_one]
      have hsub : σ.toFlag.size - σ.size = 0 := Nat.sub_self σ.size
      rw [hsub, Nat.choose_zero_right, genFlagAutCount_toFlag]; simp
    -- Inline: genUnlabelledEvalDensity_single
    have genUED_single : ∀ (H G' : GenFlag R σ),
        genUnlabelledEvalDensity (GenFlagAlg.single H) G' Δ =
          genUnlabelledDensity R σ H G' Δ := by
      intro H G'; unfold genUnlabelledEvalDensity GenFlagAlg.single
      rw [Finsupp.sum_single_index (by simp [genClassUnlabelledDensity])]
      simp only [one_mul, genClassUnlabelledDensity]
      exact genUD_flagIso (Quotient.exact (Quotient.out_eq (GenFlagClass.mk H)))
    -- Sorry'd: generic overlap embedding bound
    have genOverlap_embedding_bound :
        ∃ K : ℝ, 0 ≤ K ∧ ∀ G' : GenFlag R σ, 𝒢 G'.forget →
          F.size - σ.size + (F'.size - σ.size) ≤ Δ G'.forget →
          let nn := F.size + F'.size - σ.size
          let ff := F.size - σ.size
          let ff' := F'.size - σ.size
          (0 : ℝ) ≤ (genInducedCount R σ F G' : ℝ) * (genInducedCount R σ F' G' : ℝ) -
            (if hn : σ.size ≤ nn then
              (genClassesOfSize R σ nn hn).sum (fun cls =>
                (genJointCount R σ F F' cls.out : ℝ) * (genInducedCount R σ cls.out G' : ℝ) /
                  (genFlagAutCount R σ cls.out : ℝ))
            else 0) ∧
          (genInducedCount R σ F G' : ℝ) * (genInducedCount R σ F' G' : ℝ) -
            (if hn : σ.size ≤ nn then
              (genClassesOfSize R σ nn hn).sum (fun cls =>
                (genJointCount R σ F F' cls.out : ℝ) * (genInducedCount R σ cls.out G' : ℝ) /
                  (genFlagAutCount R σ cls.out : ℝ))
            else 0) ≤
            K * ((Nat.choose (Δ G'.forget) ff : ℝ) *
                 (Nat.choose (Δ G'.forget) (ff' - 1) : ℝ)) :=
      by
      -- Split into two sub-lemmas mirroring the SimpleGraph proofs:
      -- (1) orbit_sum_le_product: non-negativity (orbit sum counts disjoint pairs ≤ all pairs)
      -- (2) overlap_count_le: upper bound (overlap bounded by K * C(Δ,f) * C(Δ,f'-1))
      have hn_le : σ.size ≤ F.size + F'.size - σ.size := by
        have := F.hsize; have := F'.hsize; omega
      -- Sub-lemma 1: Orbit sum ≤ IC(F;G) * IC(F';G)
      -- The orbit sum counts non-overlapping embedding pairs grouped by iso class.
      -- Since NOPs inject into all pairs, the sum is ≤ IC_F * IC_F'.
      -- (Mirrors `orbit_sum_le_product` at lines 2342-2377)
      have genOrbit_sum_eq_and_le : ∀ G' : GenFlag R σ,
          (genClassesOfSize R σ (F.size + F'.size - σ.size) hn_le).sum (fun cls =>
              (genJointCount R σ F F' cls.out : ℝ) * (genInducedCount R σ cls.out G' : ℝ) /
                (genFlagAutCount R σ cls.out : ℝ)) =
            (Fintype.card { p : GenInducedEmbedding R σ F G' × GenInducedEmbedding R σ F' G' //
              ∀ i : Fin G'.size,
                (i ∈ Set.range p.1.toFun ∧ i ∈ Set.range p.2.toFun) ↔
                  i ∈ Set.range G'.embedding } : ℝ) ∧
          (Fintype.card { p : GenInducedEmbedding R σ F G' × GenInducedEmbedding R σ F' G' //
              ∀ i : Fin G'.size,
                (i ∈ Set.range p.1.toFun ∧ i ∈ Set.range p.2.toFun) ↔
                  i ∈ Set.range G'.embedding } : ℕ) ≤
            Fintype.card (GenInducedEmbedding R σ F G') *
              Fintype.card (GenInducedEmbedding R σ F' G') :=
        fun G' => by
        -- Define GenNOPSub: pairs of embeddings whose images overlap exactly on σ-image
        set GenNOPSub := { p : GenInducedEmbedding R σ F G' × GenInducedEmbedding R σ F' G' //
          ∀ i : Fin G'.size,
            (i ∈ Set.range p.1.toFun ∧ i ∈ Set.range p.2.toFun) ↔
              i ∈ Set.range G'.embedding } with hGenNOPSub_def
        -- Orbit sum = |GenNOPSub| (per-class fiber counting, mirrors nop_per_class_counting)
        have h_orbit_eq :
            (genClassesOfSize R σ (F.size + F'.size - σ.size) hn_le).sum (fun cls =>
              (genJointCount R σ F F' cls.out : ℝ) * (genInducedCount R σ cls.out G' : ℝ) /
                (genFlagAutCount R σ cls.out : ℝ)) =
            (Fintype.card GenNOPSub : ℝ) :=
          by
          -- Define intermediate class map: each NOP pair determines a flag class
          -- via the induced subflag on the union of the two embedding ranges
          -- genNopFinset: union of ranges as Finset
          let gnf : GenNOPSub → Finset (Fin G'.size) :=
            fun t => Finset.univ.filter (fun v => v ∈ Set.range t.val.1.toFun ∨ v ∈ Set.range t.val.2.toFun)
          have gnf_sigma : ∀ (t : GenNOPSub) (i : Fin σ.size), G'.embedding i ∈ gnf t := by
            intro t i; simp only [gnf, Finset.mem_filter, Finset.mem_univ, true_and]
            left; exact ⟨F.embedding i, t.val.1.compat i⟩
          have gnf_card : ∀ (t : GenNOPSub), (gnf t).card = F.size + F'.size - σ.size := by
            intro t
            let A := Finset.univ.filter (fun v : Fin G'.size => v ∈ Set.range t.val.1.toFun)
            let B := Finset.univ.filter (fun v : Fin G'.size => v ∈ Set.range t.val.2.toFun)
            have hAB : gnf t = A ∪ B := by
              ext v; simp only [gnf, A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
            rw [hAB]
            have hA : A.card = F.size := by
              have : A = Finset.univ.image t.val.1.toFun := by
                ext v; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]; rfl
              rw [this, Finset.card_image_of_injective _ t.val.1.injective, Finset.card_fin]
            have hB : B.card = F'.size := by
              have : B = Finset.univ.image t.val.2.toFun := by
                ext v; simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]; rfl
              rw [this, Finset.card_image_of_injective _ t.val.2.injective, Finset.card_fin]
            have hAB_card : (A ∩ B).card = σ.size := by
              have : A ∩ B = Finset.univ.image G'.embedding := by
                ext v; simp only [A, B, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
                exact t.property v
              rw [this, Finset.card_image_of_injective _ G'.embedding.injective, Finset.card_fin]
            have hunion := Finset.card_union_add_card_inter A B
            omega
          -- Intermediate class for each NOP pair
          let gnic : GenNOPSub → GenFlagClass R σ :=
            fun t => GenFlagClass.mk (G'.genInducedSubflag (gnf t) (gnf_sigma t) ((gnf_card t).symm ▸ hn_le))
          have gnic_mem : ∀ t : GenNOPSub,
              gnic t ∈ genClassesOfSize R σ (F.size + F'.size - σ.size) hn_le := by
            intro t
            let H := G'.genInducedSubflag (gnf t) (gnf_sigma t) ((gnf_card t).symm ▸ hn_le)
            have hsize : H.size = F.size + F'.size - σ.size := gnf_card t
            have hmem := mk_F_mem_genClassesOfSize H H.hsize
            convert hmem using 2; exact hsize.symm
          -- Per-class counting: JC * IC / Aut = |fiber| for each class cls
          -- This follows by the same compose/decompose/antisymmetric injection argument
          -- as in the SimpleGraph case (nop_per_class_counting).
          -- The generic version uses genNopPullback (inverse through injective map via Classical.choose),
          -- genInducedSubflag_incl, and GenInducedEmbedding.mapIso for the class representative bijection.
          have hper : ∀ cls ∈ genClassesOfSize R σ (F.size + F'.size - σ.size) hn_le,
              ((genJointCount R σ F F' cls.out : ℝ) * (genInducedCount R σ cls.out G' : ℝ)) /
                (genFlagAutCount R σ cls.out : ℝ) =
              ((Finset.univ.filter (fun t : GenNOPSub => gnic t = cls)).card : ℝ) := by
            intro cls hcls
            set H := cls.out
            set fiber := Finset.univ.filter (fun t : GenNOPSub => gnic t = cls)
            have hH_size : H.size = F.size + F'.size - σ.size := genClassesOfSize_out_size hcls
            -- Abbreviation for GenJCSub type
            let JC := { p : GenInducedEmbedding R σ F H × GenInducedEmbedding R σ F' H //
              (∀ i : Fin H.size,
                (i ∈ Set.range p.1.toFun ∧ i ∈ Set.range p.2.toFun) ↔
                  i ∈ Set.range H.embedding) ∧
              (∀ i : Fin H.size,
                i ∈ Set.range p.1.toFun ∨ i ∈ Set.range p.2.toFun) }
            -- Generic pullback: given b : H → G' injective with e : F₀ → G' s.t. im(e) ⊆ im(b),
            -- construct e' : F₀ → H with b ∘ e' = e
            let pb : {F₀ : GenFlag R σ} → (b : GenInducedEmbedding R σ H G') →
                (e : GenInducedEmbedding R σ F₀ G') →
                (∀ x, e.toFun x ∈ Set.range b.toFun) →
                GenInducedEmbedding R σ F₀ H :=
              fun {F₀} b e hr =>
              { toFun := fun x => Classical.choose (hr x)
                injective := fun x y h => e.injective (by
                  have := congr_arg b.toFun h
                  rwa [Classical.choose_spec (hr x), Classical.choose_spec (hr y)] at this)
                isInduced := by
                  have h1 : R.comap (fun x => Classical.choose (hr x)) H.str =
                      R.comap (fun x => Classical.choose (hr x)) (R.comap b.toFun G'.str) := by
                    congr 1; exact b.isInduced.symm
                  rw [h1, ← R.comap_comp]
                  have h2 : b.toFun ∘ (fun x => Classical.choose (hr x)) = e.toFun :=
                    funext (fun x => Classical.choose_spec (hr x))
                  rw [h2]; exact e.isInduced
                compat := fun i => b.injective (by
                  rw [Classical.choose_spec (hr (F₀.embedding i)), e.compat]
                  exact (b.compat i).symm) }
            have pb_spec : ∀ {F₀ : GenFlag R σ} (b : GenInducedEmbedding R σ H G')
                (e : GenInducedEmbedding R σ F₀ G') (hr : ∀ x, e.toFun x ∈ Set.range b.toFun),
                ∀ x, b.toFun ((pb b e hr).toFun x) = e.toFun x :=
              fun b e hr x => Classical.choose_spec (hr x)
            -- Compose overlap: b ∘ a₁, b ∘ a₂ have overlap = σ-image in G'
            have comp_overlap : ∀ (a₁ : GenInducedEmbedding R σ F H) (a₂ : GenInducedEmbedding R σ F' H)
                (b : GenInducedEmbedding R σ H G')
                (ho : ∀ i : Fin H.size, (i ∈ Set.range a₁.toFun ∧ i ∈ Set.range a₂.toFun) ↔ i ∈ Set.range H.embedding),
                ∀ i : Fin G'.size,
                  (i ∈ Set.range (b.comp a₁).toFun ∧ i ∈ Set.range (b.comp a₂).toFun) ↔
                    i ∈ Set.range G'.embedding := by
              intro a₁ a₂ b ho i
              simp only [GenInducedEmbedding.comp, Set.range_comp]; constructor
              · intro ⟨⟨x₁, hx₁, hx₁_eq⟩, ⟨x₂, hx₂, hx₂_eq⟩⟩
                have h_eq : x₁ = x₂ := b.injective (hx₁_eq.trans hx₂_eq.symm)
                subst h_eq
                obtain ⟨j, rfl⟩ := (ho x₁).mp ⟨hx₁, hx₂⟩
                exact ⟨j, (b.compat j).symm.trans hx₁_eq⟩
              · intro ⟨j, hj⟩
                have hemb := (ho (H.embedding j)).mpr ⟨j, rfl⟩
                exact ⟨⟨_, hemb.1, (b.compat j).trans hj⟩, ⟨_, hemb.2, (b.compat j).trans hj⟩⟩
            -- Compose map: JC × IE → GenNOPSub
            let cmap : JC × GenInducedEmbedding R σ H G' → GenNOPSub :=
              fun ⟨jc, b⟩ => ⟨(b.comp jc.val.1, b.comp jc.val.2),
                comp_overlap jc.val.1 jc.val.2 b jc.property.1⟩
            -- incl range = Finset as Set
            have incl_range : ∀ (S : Finset (Fin G'.size))
                (hS : ∀ i : Fin σ.size, G'.embedding i ∈ S) (hσ : σ.size ≤ S.card),
                Set.range (G'.genInducedSubflag_incl S hS hσ).toFun = ↑S := by
              intro S hS hσ; ext v; simp only [Set.mem_range, Finset.mem_coe]; constructor
              · rintro ⟨z, rfl⟩; exact Finset.orderEmbOfFin_mem _ rfl z
              · intro hv; exact ⟨(S.orderIsoOfFin rfl).symm ⟨v, hv⟩, by
                  change ↑((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨v, hv⟩)) = v
                  simp [OrderIso.apply_symm_apply]⟩
            -- cmap lands in fiber
            have hmap : ∀ pair : JC × GenInducedEmbedding R σ H G', cmap pair ∈ fiber := by
              intro ⟨jc, b⟩
              simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
              -- Need: gnic (cmap (jc, b)) = cls, i.e., [G'[im(b∘a₁) ∪ im(b∘a₂)]] = [H]
              change gnic (cmap (jc, b)) = cls
              change GenFlagClass.mk _ = cls
              rw [show cls = GenFlagClass.mk H from (Quotient.out_eq cls).symm, GenFlagClass.mk_eq]
              -- range(b) = gnf(cmap(jc,b)) by covering
              have hb_range : Set.range b.toFun = ↑(gnf (cmap (jc, b))) := by
                ext v; simp only [gnf, cmap, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
                  true_and, GenInducedEmbedding.comp, Set.range_comp]; constructor
                · rintro ⟨w, rfl⟩
                  rcases jc.property.2 w with ⟨x, rfl⟩ | ⟨x, rfl⟩
                  · left; exact ⟨_, Set.mem_range_self x, rfl⟩
                  · right; exact ⟨_, Set.mem_range_self x, rfl⟩
                · intro h; rcases h with ⟨_, ⟨x, rfl⟩, rfl⟩ | ⟨_, ⟨x, rfl⟩, rfl⟩
                  · exact ⟨jc.val.1.toFun x, rfl⟩
                  · exact ⟨jc.val.2.toFun x, rfl⟩
              -- Pullback incl through b to get GenIE from Sub to H
              let Sub := G'.genInducedSubflag (gnf (cmap (jc, b))) (gnf_sigma _) ((gnf_card _).symm ▸ hn_le)
              let incl := G'.genInducedSubflag_incl (gnf (cmap (jc, b))) (gnf_sigma _) ((gnf_card _).symm ▸ hn_le)
              have hincl_in_b : ∀ x : Fin Sub.size, incl.toFun x ∈ Set.range b.toFun := by
                intro x; rw [hb_range]
                exact (incl_range _ _ _).symm ▸ Set.mem_range_self x
              let φ := pb b incl hincl_in_b
              have hsize_eq : Sub.size = H.size := by
                change (gnf (cmap (jc, b))).card = H.size
                rw [gnf_card]; exact hH_size.symm
              have φ_surj : Function.Surjective φ.toFun := by
                have := Finite.surjective_of_injective
                  (f := φ.toFun ∘ Fin.cast hsize_eq.symm)
                  (φ.injective.comp (Fin.cast_injective _))
                intro y; obtain ⟨x, hx⟩ := this y; exact ⟨Fin.cast hsize_eq.symm x, hx⟩
              exact ⟨Equiv.ofBijective φ.toFun ⟨φ.injective, φ_surj⟩, φ.isInduced, φ.compat⟩
            -- Fiber counting: card(JC × IE) = Σ |preimage|
            have hfib_count :
                Fintype.card (JC × GenInducedEmbedding R σ H G') =
                fiber.sum (fun t =>
                  (Finset.univ.filter (fun pair : JC × GenInducedEmbedding R σ H G' =>
                    cmap pair = t)).card) :=
              Finset.card_eq_sum_card_fiberwise (fun pair _ => hmap pair)
            have hJC_IC : Fintype.card (JC × GenInducedEmbedding R σ H G') =
                genJointCount R σ F F' H * genInducedCount R σ H G' := by
              rw [Fintype.card_prod]; rfl
            -- Each preimage has constant size = Aut(H)
            suffices hconst : ∀ t ∈ fiber,
                (Finset.univ.filter (fun pair : JC × GenInducedEmbedding R σ H G' =>
                  cmap pair = t)).card = genFlagAutCount R σ H by
              rw [div_eq_iff (ne_of_gt (Nat.cast_pos.mpr (genFlagAutCount_pos σ H)))]
              calc (genJointCount R σ F F' H : ℝ) * (genInducedCount R σ H G' : ℝ)
                  = ↑(Fintype.card (JC × GenInducedEmbedding R σ H G')) := by rw [hJC_IC]; push_cast; ring
                _ = ↑(fiber.sum (fun t => (Finset.univ.filter (fun pair : JC × GenInducedEmbedding R σ H G' => cmap pair = t)).card)) := by
                    exact_mod_cast hfib_count
                _ = (fiber.sum (fun t => (genFlagAutCount R σ H : ℝ))) := by
                    push_cast; exact Finset.sum_congr rfl (fun t ht => by rw [hconst t ht])
                _ = ↑(genFlagAutCount R σ H) * ↑fiber.card := by
                    rw [Finset.sum_const]; simp [nsmul_eq_mul, mul_comm]
                _ = (Finset.univ.filter fun t => gnic t = cls).card * ↑(genFlagAutCount R σ H) := by ring
            -- Prove each preimage has size Aut(H) by antisymmetric injections
            intro t ht
            simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at ht
            -- gnic t = cls means [G'[gnf t]] = [H]
            have hiso : GenFlagIso σ (G'.genInducedSubflag (gnf t) (gnf_sigma t) ((gnf_card t).symm ▸ hn_le)) H :=
              (GenFlagClass.mk_eq _ _).mp (show gnic t = GenFlagClass.mk H from ht.trans (Quotient.out_eq cls).symm)
            obtain ⟨φ_iso, hstr_iso, hcompat_iso⟩ := hiso
            -- b₀ : GenIE H G' via mapIso with φ_iso.symm + incl
            let incl_t := G'.genInducedSubflag_incl (gnf t) (gnf_sigma t) ((gnf_card t).symm ▸ hn_le)
            have hstr_inv : R.comap (⇑φ_iso.symm) (G'.genInducedSubflag (gnf t) (gnf_sigma t) ((gnf_card t).symm ▸ hn_le)).str = H.str := by
              rw [← hstr_iso, ← R.comap_comp]
              have : (⇑φ_iso ∘ ⇑φ_iso.symm) = id := funext (fun x => φ_iso.apply_symm_apply x)
              rw [this, R.comap_id]
            have hcompat_inv : ∀ i, φ_iso.symm (H.embedding i) = (G'.genInducedSubflag (gnf t) (gnf_sigma t) ((gnf_card t).symm ▸ hn_le)).embedding i := by
              intro i; exact φ_iso.symm_apply_eq.mpr (hcompat_iso i).symm
            let b₀ : GenInducedEmbedding R σ H G' := GenInducedEmbedding.mapIso φ_iso.symm hstr_inv hcompat_inv incl_t
            have hb₀_range : Set.range b₀.toFun = ↑(gnf t) := by
              change Set.range (GenInducedEmbedding.mapIso φ_iso.symm hstr_inv hcompat_inv incl_t).toFun = ↑(gnf t)
              rw [GenInducedEmbedding.range_mapIso]; exact incl_range _ _ _
            -- For any pair mapping to t, pair.2 has range ⊆ range(b₀)
            have pair_range : ∀ pair : JC × GenInducedEmbedding R σ H G',
                cmap pair = t → ∀ x, pair.2.toFun x ∈ Set.range b₀.toFun := by
              intro ⟨jc, b⟩ hpair x; rw [hb₀_range]
              simp only [gnf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
              have hval := congr_arg Subtype.val hpair
              rcases jc.property.2 x with ⟨z, rfl⟩ | ⟨z, rfl⟩
              · left; exact ⟨z, (congr_fun (congr_arg GenInducedEmbedding.toFun (congr_arg (·.1) hval)) z).symm⟩
              · right; exact ⟨z, (congr_fun (congr_arg GenInducedEmbedding.toFun (congr_arg (·.2) hval)) z).symm⟩
            -- Pairs mapping to t are determined by their b-component
            have pair_det : ∀ p₁ p₂ : JC × GenInducedEmbedding R σ H G',
                cmap p₁ = t → cmap p₂ = t → p₁.2 = p₂.2 → p₁ = p₂ := by
              intro p₁ p₂ hp₁ hp₂ hb_eq
              have hval₁ := congr_arg Subtype.val hp₁
              have hval₂ := congr_arg Subtype.val hp₂
              have ha₁ : p₁.1.val.1.toFun = p₂.1.val.1.toFun := by
                funext x; apply p₂.2.injective
                calc p₂.2.toFun (p₁.1.val.1.toFun x)
                    = p₁.2.toFun (p₁.1.val.1.toFun x) := by rw [hb_eq]
                  _ = t.val.1.toFun x :=
                      congr_fun (congr_arg GenInducedEmbedding.toFun (congr_arg (·.1) hval₁)) x
                  _ = p₂.2.toFun (p₂.1.val.1.toFun x) :=
                      (congr_fun (congr_arg GenInducedEmbedding.toFun (congr_arg (·.1) hval₂)) x).symm
              have ha₂ : p₁.1.val.2.toFun = p₂.1.val.2.toFun := by
                funext x; apply p₂.2.injective
                calc p₂.2.toFun (p₁.1.val.2.toFun x)
                    = p₁.2.toFun (p₁.1.val.2.toFun x) := by rw [hb_eq]
                  _ = t.val.2.toFun x :=
                      congr_fun (congr_arg GenInducedEmbedding.toFun (congr_arg (·.2) hval₁)) x
                  _ = p₂.2.toFun (p₂.1.val.2.toFun x) :=
                      (congr_fun (congr_arg GenInducedEmbedding.toFun (congr_arg (·.2) hval₂)) x).symm
              have heq1 : p₁.1.val.1 = p₂.1.val.1 := by
                have : p₁.1.val.1.toFun = p₂.1.val.1.toFun := ha₁
                cases h₁ : p₁.1.val.1; cases h₂ : p₂.1.val.1
                simp only [GenInducedEmbedding.mk.injEq]
                rw [h₁, h₂] at this; exact this
              have heq2 : p₁.1.val.2 = p₂.1.val.2 := by
                have : p₁.1.val.2.toFun = p₂.1.val.2.toFun := ha₂
                cases h₁ : p₁.1.val.2; cases h₂ : p₂.1.val.2
                simp only [GenInducedEmbedding.mk.injEq]
                rw [h₁, h₂] at this; exact this
              exact Prod.ext (Subtype.ext (Prod.ext heq1 heq2)) hb_eq
            -- Fiber size = Aut(H) by antisymmetric injections.
            -- Upper bound: (jc,b) ↦ pb(b₀,b) injects fiber into Aut(H)
            -- Lower bound: α ↦ (decompose(t,b₀∘α), b₀∘α) injects Aut(H) into fiber
            -- Helper: range(b₀∘α) = range(b₀) for any automorphism α
            have hcomp_range : ∀ α : GenInducedEmbedding R σ H H,
                Set.range (b₀.comp α).toFun = Set.range b₀.toFun := by
              intro α; ext v
              simp only [GenInducedEmbedding.comp, Set.mem_range, Function.comp_apply]; constructor
              · rintro ⟨y, rfl⟩; exact ⟨α.toFun y, rfl⟩
              · rintro ⟨y, rfl⟩
                obtain ⟨z, rfl⟩ := (Finite.injective_iff_surjective.mp α.injective) y
                exact ⟨z, rfl⟩
            -- Helper: t.val.1 image is in range(b₀)
            have ht1_in_b₀ : ∀ x, t.val.1.toFun x ∈ Set.range b₀.toFun := by
              intro x; rw [hb₀_range]
              simp only [gnf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
              left; exact Set.mem_range_self x
            -- Helper: t.val.2 image is in range(b₀)
            have ht2_in_b₀ : ∀ x, t.val.2.toFun x ∈ Set.range b₀.toFun := by
              intro x; rw [hb₀_range]
              simp only [gnf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
              right; exact Set.mem_range_self x
            -- Helper: b₀.toFun i is in gnf t
            have hb₀_in_gnf : ∀ i, b₀.toFun i ∈ (gnf t : Set (Fin G'.size)) := by
              intro i; rw [← hb₀_range]; exact Set.mem_range_self i
            -- Helper: comp(b,pb(b,e)) = e as functions
            have comp_pb_eq : ∀ {F₀ : GenFlag R σ} (b : GenInducedEmbedding R σ H G')
                (e : GenInducedEmbedding R σ F₀ G') (hr : ∀ x, e.toFun x ∈ Set.range b.toFun),
                (b.comp (pb b e hr)).toFun = e.toFun := by
              intro F₀ b e hr; funext x
              simp only [GenInducedEmbedding.comp, Function.comp_apply]
              exact pb_spec b e hr x
            apply Nat.le_antisymm
            -- Upper bound: fiber ≤ Aut(H)
            · rw [← Fintype.card_coe]
              apply Fintype.card_le_of_injective
                (fun ⟨pair, hmem⟩ =>
                  pb b₀ pair.2 (pair_range pair (by
                    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem)))
              intro ⟨p₁, hm₁⟩ ⟨p₂, hm₂⟩ heq
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm₁ hm₂
              simp only [Subtype.mk.injEq]
              -- From pb(b₀,p₁.2) = pb(b₀,p₂.2), deduce p₁.2 = p₂.2
              have hb_eq : p₁.2 = p₂.2 := by
                have hpb_fun_eq : ∀ x, (pb b₀ p₁.2 (pair_range p₁ hm₁)).toFun x =
                    (pb b₀ p₂.2 (pair_range p₂ hm₂)).toFun x :=
                  fun x => congr_fun (congr_arg GenInducedEmbedding.toFun heq) x
                have hfun_eq : p₁.2.toFun = p₂.2.toFun := by
                  funext x
                  have h1 := pb_spec b₀ p₁.2 (pair_range p₁ hm₁) x
                  have h2 := pb_spec b₀ p₂.2 (pair_range p₂ hm₂) x
                  rw [hpb_fun_eq] at h1; exact h1.symm.trans h2
                cases hp₁ : p₁.2; cases hp₂ : p₂.2
                simp only [GenInducedEmbedding.mk.injEq]
                rw [hp₁, hp₂] at hfun_eq; exact hfun_eq
              exact pair_det p₁ p₂ hm₁ hm₂ hb_eq
            -- Lower bound: Aut(H) ≤ fiber
            · rw [← Fintype.card_coe]
              -- For each α, pull back t's components through b₀ ∘ α
              have ht1_in_comp : ∀ (α : GenInducedEmbedding R σ H H),
                  ∀ x, t.val.1.toFun x ∈ Set.range (b₀.comp α).toFun :=
                fun α x => by rw [hcomp_range]; exact ht1_in_b₀ x
              have ht2_in_comp : ∀ (α : GenInducedEmbedding R σ H H),
                  ∀ x, t.val.2.toFun x ∈ Set.range (b₀.comp α).toFun :=
                fun α x => by rw [hcomp_range]; exact ht2_in_b₀ x
              -- Overlap condition for decomposed pair
              have decompose_overlap : ∀ α : GenInducedEmbedding R σ H H,
                  ∀ i : Fin H.size,
                  (i ∈ Set.range (pb (b₀.comp α) t.val.1 (ht1_in_comp α)).toFun ∧
                   i ∈ Set.range (pb (b₀.comp α) t.val.2 (ht2_in_comp α)).toFun) ↔
                    i ∈ Set.range H.embedding := by
                intro α i; set bα := b₀.comp α; constructor
                · intro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
                  have hbi₁ : bα.toFun i ∈ Set.range t.val.1.toFun := by
                    refine ⟨x₁, ?_⟩
                    have h := pb_spec bα t.val.1 (ht1_in_comp α) x₁
                    rw [hx₁] at h; exact h.symm
                  have hbi₂ : bα.toFun i ∈ Set.range t.val.2.toFun := by
                    refine ⟨x₂, ?_⟩
                    have h := pb_spec bα t.val.2 (ht2_in_comp α) x₂
                    rw [hx₂] at h; exact h.symm
                  obtain ⟨j, hj⟩ := (t.property (bα.toFun i)).mp ⟨hbi₁, hbi₂⟩
                  exact ⟨j, bα.injective ((bα.compat j).trans hj)⟩
                · intro ⟨j, hj⟩
                  have hemb := (t.property (G'.embedding j)).mpr ⟨j, rfl⟩
                  constructor
                  · obtain ⟨x, hx⟩ := hemb.1
                    refine ⟨x, bα.injective ?_⟩
                    rw [pb_spec]; rw [← hj]; rw [hx]; exact (bα.compat j).symm
                  · obtain ⟨x, hx⟩ := hemb.2
                    refine ⟨x, bα.injective ?_⟩
                    rw [pb_spec]; rw [← hj]; rw [hx]; exact (bα.compat j).symm
              -- Cover condition for decomposed pair
              have decompose_cover : ∀ α : GenInducedEmbedding R σ H H,
                  ∀ i : Fin H.size,
                  i ∈ Set.range (pb (b₀.comp α) t.val.1 (ht1_in_comp α)).toFun ∨
                  i ∈ Set.range (pb (b₀.comp α) t.val.2 (ht2_in_comp α)).toFun := by
                intro α i; set bα := b₀.comp α
                have hbi_in_range : bα.toFun i ∈ Set.range b₀.toFun := by
                  rw [← hcomp_range]; exact Set.mem_range_self i
                rw [hb₀_range] at hbi_in_range
                have hbi : bα.toFun i ∈ Set.range t.val.1.toFun ∨
                           bα.toFun i ∈ Set.range t.val.2.toFun := by
                  simp only [gnf, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hbi_in_range
                  exact hbi_in_range
                rcases hbi with ⟨x₁, hx₁⟩ | ⟨x₂, hx₂⟩
                · left; exact ⟨x₁, bα.injective ((pb_spec bα t.val.1 (ht1_in_comp α) x₁).trans hx₁)⟩
                · right; exact ⟨x₂, bα.injective ((pb_spec bα t.val.2 (ht2_in_comp α) x₂).trans hx₂)⟩
              -- cmap ∘ decompose = id (compose recovers t)
              -- Key fact: (b₀∘α) ∘ pb(b₀∘α, e) = e, so cmap gives back t
              -- Helper: b.comp (pb b e hr) has same toFun as e
              have comp_pb_toFun : ∀ {F₀ : GenFlag R σ} (b : GenInducedEmbedding R σ H G')
                  (e : GenInducedEmbedding R σ F₀ G') (hr : ∀ x, e.toFun x ∈ Set.range b.toFun),
                  (b.comp (pb b e hr)).toFun = e.toFun :=
                fun b e hr => funext (fun x => pb_spec b e hr x)
              -- Helper to prove GenInducedEmbedding equality from toFun equality
              have gie_ext : ∀ {F₀ G₀ : GenFlag R σ} (e₁ e₂ : GenInducedEmbedding R σ F₀ G₀),
                  e₁.toFun = e₂.toFun → e₁ = e₂ := by
                intro F₀ G₀ e₁ e₂ h; cases e₁; cases e₂
                simp only [GenInducedEmbedding.mk.injEq]; exact h
              have decompose_compose : ∀ α : GenInducedEmbedding R σ H H,
                  cmap (⟨(pb (b₀.comp α) t.val.1 (ht1_in_comp α),
                          pb (b₀.comp α) t.val.2 (ht2_in_comp α)),
                         decompose_overlap α, decompose_cover α⟩,
                        b₀.comp α) = t := by
                intro α; apply Subtype.ext; apply Prod.ext
                · -- (b₀∘α).comp (pb(b₀∘α, t.1)) = t.1
                  exact gie_ext _ _ (comp_pb_toFun (b₀.comp α) t.val.1 (ht1_in_comp α))
                · -- (b₀∘α).comp (pb(b₀∘α, t.2)) = t.2
                  exact gie_ext _ _ (comp_pb_toFun (b₀.comp α) t.val.2 (ht2_in_comp α))
              -- Injection from Aut(H) into fiber
              apply Fintype.card_le_of_injective (fun α =>
                ⟨(⟨(pb (b₀.comp α) t.val.1 (ht1_in_comp α),
                    pb (b₀.comp α) t.val.2 (ht2_in_comp α)),
                   decompose_overlap α, decompose_cover α⟩,
                  b₀.comp α),
                 by simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                    exact decompose_compose α⟩)
              intro α₁ α₂ heq
              simp only [Subtype.mk.injEq] at heq
              have hb_eq : b₀.comp α₁ = b₀.comp α₂ :=
                congr_arg (fun p => (p : JC × GenInducedEmbedding R σ H G').2) heq
              cases h₁ : α₁; cases h₂ : α₂
              simp only [GenInducedEmbedding.mk.injEq]; funext x
              have := congr_fun (congr_arg GenInducedEmbedding.toFun hb_eq) x
              simp only [GenInducedEmbedding.comp, Function.comp_apply, h₁, h₂] at this
              exact b₀.injective this
          -- Sum fibers = total
          rw [Finset.sum_congr rfl hper]
          have hfib : (Finset.univ : Finset GenNOPSub).card =
              (genClassesOfSize R σ (F.size + F'.size - σ.size) hn_le).sum (fun cls =>
                (Finset.univ.filter (fun t : GenNOPSub => gnic t = cls)).card) :=
            Finset.card_eq_sum_card_fiberwise (fun t _ => gnic_mem t)
          rw [Finset.card_univ] at hfib
          exact_mod_cast hfib.symm
        -- |GenNOPSub| ≤ IC(F;G') * IC(F';G') by injection into product
        have h_nop_le_product :
            (Fintype.card GenNOPSub : ℕ) ≤
            Fintype.card (GenInducedEmbedding R σ F G') *
              Fintype.card (GenInducedEmbedding R σ F' G') := by
          rw [← Fintype.card_prod]
          exact Fintype.card_le_of_injective (fun t => t.val) Subtype.val_injective
        exact ⟨h_orbit_eq, h_nop_le_product⟩
      have genOrbit_sum_le_product : ∀ G' : GenFlag R σ,
          (genClassesOfSize R σ (F.size + F'.size - σ.size) hn_le).sum (fun cls =>
              (genJointCount R σ F F' cls.out : ℝ) * (genInducedCount R σ cls.out G' : ℝ) /
                (genFlagAutCount R σ cls.out : ℝ)) ≤
            (genInducedCount R σ F G' : ℝ) * (genInducedCount R σ F' G' : ℝ) :=
        fun G' => by
        obtain ⟨h_eq, h_le⟩ := genOrbit_sum_eq_and_le G'
        rw [h_eq]; exact_mod_cast h_le
      -- Sub-lemma 2: Overlap count ≤ K * C(Δ,f) * C(Δ,f'-1)
      -- Each overlapping pair shares an unlabelled vertex; decomposing by that vertex
      -- and using bounded density of extensions gives the bound.
      -- (Mirrors `overlap_count_le` at lines 2389-2763)
      have genOverlap_count_le :
          ∃ K : ℝ, 0 ≤ K ∧ ∀ G' : GenFlag R σ, 𝒢 G'.forget →
            F.size - σ.size + (F'.size - σ.size) ≤ Δ G'.forget →
            (genInducedCount R σ F G' : ℝ) * (genInducedCount R σ F' G' : ℝ) -
              (genClassesOfSize R σ (F.size + F'.size - σ.size) hn_le).sum (fun cls =>
                (genJointCount R σ F F' cls.out : ℝ) * (genInducedCount R σ cls.out G' : ℝ) /
                  (genFlagAutCount R σ cls.out : ℝ)) ≤
              K * ((Nat.choose (Δ G'.forget) (F.size - σ.size) : ℝ) *
                   (Nat.choose (Δ G'.forget) (F'.size - σ.size - 1) : ℝ)) :=
        by
        -- Follow the structure of `overlap_count_le` (lines 2389-2763).
        -- K = f * f' * C_F * C_max where C_max bounds local density at every extension of F'.
        set f := F.size - σ.size with hf_def
        set f' := F'.size - σ.size with hf'_def
        have h_orbit_nn : ∀ G0 : GenFlag R σ,
            0 ≤ (genClassesOfSize R σ (F.size + F'.size - σ.size) hn_le).sum (fun cls =>
              (genJointCount R σ F F' cls.out : ℝ) * (genInducedCount R σ cls.out G0 : ℝ) /
                (genFlagAutCount R σ cls.out : ℝ)) :=
          fun G0 => Finset.sum_nonneg (fun cls _ =>
            div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
        obtain ⟨C_F0, hCF0_nn, hCF0⟩ := hF.bounded
        by_cases hf'_zero : f' = 0
        · -- f' = 0: F' has same size as σ, at most one embedding
          refine ⟨C_F0, hCF0_nn, fun G0 hG0 hΔ0 => ?_⟩
          have hsz : F'.size = σ.size := by have := F'.hsize; omega
          have hIC_F'_le : (genInducedCount R σ F' G0 : ℝ) ≤ 1 := by
            unfold genInducedCount; rw [Nat.cast_le_one, Fintype.card_le_one_iff]
            intro a b
            have : a.toFun = b.toFun := by
              funext v; obtain ⟨i, rfl⟩ :=
                F'.embedding.injective.surjective_of_finite (finCongr hsz.symm) v
              exact a.compat i |>.trans (b.compat i).symm
            cases a; cases b; simp only [GenInducedEmbedding.mk.injEq] at this ⊢; exact this
          rw [show F'.size - σ.size - 1 = 0 from by omega, Nat.choose_zero_right,
            Nat.cast_one, mul_one]
          have hfΔ0 : f ≤ Δ G0.forget := by omega
          have hCDf_pos : (0 : ℝ) < (Nat.choose (Δ G0.forget) f : ℝ) :=
            Nat.cast_pos.mpr (Nat.choose_pos hfΔ0)
          calc (genInducedCount R σ F G0 : ℝ) * (genInducedCount R σ F' G0 : ℝ) -
                (genClassesOfSize R σ _ hn_le).sum _ ≤
              (genInducedCount R σ F G0 : ℝ) * (genInducedCount R σ F' G0 : ℝ) :=
                by linarith [h_orbit_nn G0]
            _ ≤ (genInducedCount R σ F G0 : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hIC_F'_le (Nat.cast_nonneg _)
            _ = (genInducedCount R σ F G0 : ℝ) := mul_one _
            _ ≤ C_F0 * (Nat.choose (Δ G0.forget) f : ℝ) := by
                have hld := hCF0 G0 hG0; unfold genLocalDensity at hld
                rwa [div_le_iff₀ hCDf_pos] at hld
        · -- f' ≥ 1: extract bounded density constants from extensions of F'
          -- Sorry the main fiber counting argument (pending GenLabelExtension infrastructure)
          -- The constant K = f * f' * C_F * C_max works, following the SimpleGraph proof.
          have hf'_pos : 1 ≤ f' := Nat.one_le_iff_ne_zero.mpr hf'_zero
          -- Extract C_max bounding local density at all extensions of F'
          -- (mirrors lines 2435-2460 of SimpleGraph overlap_count_le)
          obtain ⟨C_max, hCmax_nn, _hCmax⟩ : ∃ C_max : ℝ, 0 ≤ C_max ∧
              ∀ (ext : GenLabelExtension F'),
                ∀ G0 : GenFlag R ext.extendedType, 𝒢 G0.forget →
                  genLocalDensity ext.extendedType ext.extendedFlag G0 Δ ≤ C_max := by
            -- Each extension has bounded density from GenIsLocalFlag
            have h_all_ext : ∀ ext : GenLabelExtension F',
                GenIsLocalFlag ext.extendedType ext.extendedFlag 𝒢 Δ :=
              fun ext => hF'.extensions ext
            -- Iterate over unlabelled vertices (a finite set) to take max of bounds
            set S := (Finset.univ : Finset (Fin F'.size)).filter
              (fun v => ¬ ∃ i, F'.embedding i = v) with _hS_def
            suffices h : ∀ (T : Finset (Fin F'.size)), T ⊆ S →
                ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ T, ∀ (hv : v ∉ Set.range F'.embedding),
                  ∀ G0 : GenFlag R (GenLabelExtension.extendedType ⟨v, hv⟩), 𝒢 G0.forget →
                    genLocalDensity _ (GenLabelExtension.extendedFlag ⟨v, hv⟩) G0 Δ ≤ C by
              obtain ⟨C, hC_nn, hC⟩ := h S Finset.Subset.rfl
              refine ⟨C, hC_nn, fun ext G0 hG0 => ?_⟩
              have hv_mem : ext.vertex ∈ S := by
                simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
                intro ⟨i, hi⟩; exact ext.unlabelled ⟨i, hi⟩
              exact hC ext.vertex hv_mem ext.unlabelled G0 hG0
            intro T hTS
            induction T using Finset.induction with
            | empty => exact ⟨0, le_refl _, fun v hv => absurd hv (by simp)⟩
            | @insert a T' ha ih =>
              obtain ⟨C_prev, hCp_nn, hCp⟩ := ih (Finset.subset_insert a T' |>.trans hTS)
              have ha_unlab : a ∉ Set.range F'.embedding := by
                have := Finset.mem_filter.mp (hTS (Finset.mem_insert_self a T'))
                simp only [Set.mem_range] at this ⊢; exact this.2
              obtain ⟨C_a, hCa_nn, hCa⟩ := (h_all_ext ⟨a, ha_unlab⟩).bounded
              refine ⟨max C_prev C_a, le_max_of_le_left hCp_nn,
                fun v hv_mem hv G0 hG0 => ?_⟩
              rcases Finset.mem_insert.mp hv_mem with rfl | hv_mem'
              · exact le_trans (hCa G0 hG0) (le_max_right _ _)
              · exact le_trans (hCp v hv_mem' hv G0 hG0) (le_max_left _ _)
          set K := (f : ℝ) * f' * C_F0 * C_max with _hK_def
          have hK_nn : 0 ≤ K := mul_nonneg (mul_nonneg (mul_nonneg
            (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hCF0_nn) hCmax_nn
          refine ⟨K, hK_nn, fun G0 hG0 hΔ0 => ?_⟩
          -- Use the orbit=NOP equality from genOrbit_sum_eq_and_le
          obtain ⟨h_orbit_eq0, _⟩ := genOrbit_sum_eq_and_le G0
          -- Basic bounds
          have hfΔ : f ≤ Δ G0.forget := by omega
          have hf'1Δ : f' - 1 ≤ Δ G0.forget := by omega
          have hCDf_pos : (0 : ℝ) < (Nat.choose (Δ G0.forget) f : ℝ) :=
            Nat.cast_pos.mpr (Nat.choose_pos hfΔ)
          have hICF_bound : (genInducedCount R σ F G0 : ℝ) ≤
              C_F0 * (Nat.choose (Δ G0.forget) f : ℝ) := by
            have hld := hCF0 G0 hG0; unfold genLocalDensity at hld
            rwa [div_le_iff₀ hCDf_pos] at hld
          -- Step 2: Fiber bound — for each w ∉ range(F'.embedding) and v ∉ range(G0.embedding),
          -- the number of embeddings e : F' ↪ G0 with e(w) = v is ≤ C_max * C(Δ, f'-1).
          have h_fiber_bound : ∀ (w : Fin F'.size) (hw : w ∉ Set.range F'.embedding)
              (v : Fin G0.size) (_ : v ∉ Set.range G0.embedding),
              ((Finset.univ.filter (fun e : GenInducedEmbedding R σ F' G0 =>
                e.toFun w = v)).card : ℝ) ≤
              C_max * (Nat.choose (Δ G0.forget) (f' - 1) : ℝ) := by
            intro w hw v hv
            by_cases h_empty :
                (Finset.univ.filter (fun e : GenInducedEmbedding R σ F' G0 =>
                  e.toFun w = v)) = ∅
            · simp [h_empty]; exact mul_nonneg hCmax_nn (Nat.cast_nonneg _)
            obtain ⟨e₀, he₀⟩ := Finset.nonempty_of_ne_empty h_empty
            rw [Finset.mem_filter] at he₀
            let ext : GenLabelExtension F' := ⟨w, hw⟩
            let extG : GenLabelExtension G0 := ⟨v, hv⟩
            -- Compatibility: e₀ maps ext.vertexMap to extG.vertexMap
            have hcomp₀ : ∀ i, e₀.toFun (ext.vertexMap i) = extG.vertexMap i := by
              intro i
              obtain (⟨m, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
              · simp only [GenLabelExtension.vertexMap, Fin.lastCases_castSucc]; exact e₀.compat m
              · simp only [GenLabelExtension.vertexMap, Fin.lastCases_last]; exact he₀.2
            -- Construct the extended G0-flag of type ext.extendedType
            have hcomap_eq : R.comap (e₀.toFun ∘ ext.vertexMap) G0.str = ext.extendedType.str := by
              rw [R.comap_comp]
              rw [e₀.isInduced]; rfl
            let extGFlag : GenFlag R ext.extendedType :=
              ⟨G0.size, G0.str,
               ⟨e₀.toFun ∘ ext.vertexMap, Function.Injective.comp e₀.injective ext.vertexMap_injective⟩,
               hcomap_eq, by
                 change σ.size + 1 ≤ G0.size
                 have : Fintype.card (Fin F'.size) ≤ Fintype.card (Fin G0.size) :=
                   Fintype.card_le_of_injective _ e₀.injective
                 simp only [Fintype.card_fin] at this
                 have := F'.hsize; omega⟩
            -- extGFlag.forget = G0.forget
            have hextG_forget : extGFlag.forget = G0.forget := rfl
            -- Fiber injects into IE(ext.extendedType, ext.extendedFlag, extGFlag)
            have h_compat : ∀ (e : GenInducedEmbedding R σ F' G0), e.toFun w = v →
                ∀ i, e.toFun (ext.vertexMap i) = extGFlag.embedding i := by
              intro e hev i
              obtain (⟨m, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
              · simp only [GenLabelExtension.vertexMap, Fin.lastCases_castSucc]
                change e.toFun (F'.embedding m) = e₀.toFun (ext.vertexMap (Fin.castSucc m))
                simp only [GenLabelExtension.vertexMap, Fin.lastCases_castSucc]
                rw [e.compat m, e₀.compat m]
              · simp only [GenLabelExtension.vertexMap, Fin.lastCases_last]
                change e.toFun w = e₀.toFun (ext.vertexMap (Fin.last _))
                simp only [GenLabelExtension.vertexMap, Fin.lastCases_last]
                exact hev.trans he₀.2.symm
            have h_card_fiber :
                (Finset.univ.filter (fun e : GenInducedEmbedding R σ F' G0 =>
                  e.toFun w = v)).card ≤
                Fintype.card (GenInducedEmbedding R ext.extendedType ext.extendedFlag extGFlag) := by
              have : Fintype.card {e : GenInducedEmbedding R σ F' G0 // e.toFun w = v} ≤
                  Fintype.card (GenInducedEmbedding R ext.extendedType ext.extendedFlag extGFlag) := by
                apply Fintype.card_le_of_injective
                  (fun (p : {e : GenInducedEmbedding R σ F' G0 // e.toFun w = v}) =>
                    (⟨p.val.toFun, p.val.injective,
                      p.val.isInduced,
                      h_compat p.val p.prop⟩ :
                      GenInducedEmbedding R ext.extendedType ext.extendedFlag extGFlag))
                intro ⟨e₁, _⟩ ⟨e₂, _⟩ h_eq
                simp only [Subtype.mk.injEq]; dsimp only at h_eq
                have htf := congr_arg GenInducedEmbedding.toFun h_eq
                cases e₁; cases e₂; simp only [GenInducedEmbedding.mk.injEq] at htf ⊢; exact htf
              convert this using 1; rw [← Fintype.card_coe]
              exact Fintype.card_congr (Equiv.subtypeEquivRight (fun e => by
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]))
            have hld := _hCmax ext extGFlag (hextG_forget ▸ hG0)
            unfold genLocalDensity at hld
            rw [show ext.extendedFlag.size - ext.extendedType.size = f' - 1 from by
              simp only [GenLabelExtension.extendedFlag, GenLabelExtension.extendedType]; omega] at hld
            rw [show Δ extGFlag.forget = Δ G0.forget from by rw [hextG_forget]] at hld
            rw [div_le_iff₀ (Nat.cast_pos.mpr (Nat.choose_pos hf'1Δ))] at hld
            exact_mod_cast (Nat.cast_le (α := ℝ)).mpr h_card_fiber |>.trans hld
          -- Step 3: Per-e₁ bound on bad pairs
          -- W = unlabelled vertices of F'
          set W := Finset.univ.filter
            (fun w : Fin F'.size => w ∉ Set.range F'.embedding) with hW_def
          have hW_card : W.card = f' := by
            rw [show W = Finset.univ \ Finset.univ.image F'.embedding from by
              ext w; simp only [W, Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_sdiff, Finset.mem_image, Set.mem_range],
              Finset.card_sdiff_of_subset (fun _ _ => Finset.mem_univ _), Finset.card_fin,
              Finset.card_image_of_injective _ F'.embedding.injective, Finset.card_fin]
          -- bad(e₁) = embeddings of F' that share an unlabelled vertex with e₁
          set bad := fun (e₁ : GenInducedEmbedding R σ F G0) =>
            Finset.univ.filter (fun (e₂ : GenInducedEmbedding R σ F' G0) =>
              ∃ v : Fin G0.size, v ∈ Set.range e₁.toFun ∧ v ∈ Set.range e₂.toFun ∧
                v ∉ Set.range G0.embedding)
          set good := fun (e₁ : GenInducedEmbedding R σ F G0) =>
            Finset.univ.filter (fun (e₂ : GenInducedEmbedding R σ F' G0) =>
              ∀ i : Fin G0.size,
                (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
                  i ∈ Set.range G0.embedding)
          have h_per_e1 : ∀ e₁ : GenInducedEmbedding R σ F G0,
              ((bad e₁).card : ℝ) ≤
              (f : ℝ) * f' * C_max * (Nat.choose (Δ G0.forget) (f' - 1) : ℝ) := by
            intro e₁
            set unlabImg := Finset.univ.filter (fun v : Fin G0.size =>
              v ∈ Set.range e₁.toFun ∧ v ∉ Set.range G0.embedding)
            have h_unlabImg_card : unlabImg.card = f := by
              have h_eq : unlabImg = (Finset.univ.filter
                  (fun w : Fin F.size => w ∉ Set.range F.embedding)).image e₁.toFun := by
                ext v; constructor
                · intro hv
                  simp only [unlabImg, Finset.mem_filter, Finset.mem_univ, true_and] at hv
                  obtain ⟨⟨w, rfl⟩, hv_ns⟩ := hv
                  apply Finset.mem_image.mpr
                  refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
                  intro ⟨i, hi⟩
                  exact hv_ns ⟨i, (hi ▸ e₁.compat i).symm⟩
                · intro hv
                  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
                  simp only [unlabImg, Finset.mem_filter, Finset.mem_univ, true_and]
                  exact ⟨⟨w, rfl⟩, fun ⟨i, hi⟩ => hw ⟨i, e₁.injective
                    ((e₁.compat i).trans hi)⟩⟩
              rw [h_eq, Finset.card_image_of_injective _ e₁.injective]
              have : (Finset.univ.filter
                  (fun w : Fin F.size => w ∉ Set.range F.embedding)) =
                  Finset.univ \ Finset.univ.image F.embedding := by
                ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                  Finset.mem_sdiff, Finset.mem_image, Set.mem_range]
              rw [this, Finset.card_sdiff_of_subset (fun _ _ => Finset.mem_univ _),
                Finset.card_fin,
                Finset.card_image_of_injective _ F.embedding.injective,
                Finset.card_fin]
            have h_bad_sub : bad e₁ ⊆ unlabImg.biUnion (fun v =>
                Finset.univ.filter (fun e₂ : GenInducedEmbedding R σ F' G0 =>
                  v ∈ Set.range e₂.toFun)) := by
              intro e₂ he₂
              simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at he₂
              obtain ⟨v, hv₁, hv₂, hvσ⟩ := he₂
              exact Finset.mem_biUnion.mpr ⟨v,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv₁, hvσ⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv₂⟩⟩
            have h_per_v : ∀ v ∈ unlabImg,
                ((Finset.univ.filter (fun e₂ : GenInducedEmbedding R σ F' G0 =>
                  v ∈ Set.range e₂.toFun)).card : ℝ) ≤
                (f' : ℝ) * C_max * (Nat.choose (Δ G0.forget) (f' - 1) : ℝ) := by
              intro v hv
              have hv_not_sigma : v ∉ Set.range G0.embedding :=
                (Finset.mem_filter.mp hv).2.2
              have h_v_sub : Finset.univ.filter (fun e₂ : GenInducedEmbedding R σ F' G0 =>
                  v ∈ Set.range e₂.toFun) ⊆
                W.biUnion (fun w => Finset.univ.filter (fun e₂ : GenInducedEmbedding R σ F' G0 =>
                  e₂.toFun w = v)) := by
                intro e₂ he₂
                simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_range] at he₂
                obtain ⟨w, hw⟩ := he₂
                apply Finset.mem_biUnion.mpr
                refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩
                intro ⟨i, hi⟩
                exact hv_not_sigma ⟨i, by rw [← hw, ← hi, e₂.compat]⟩
              calc ((Finset.univ.filter (fun e₂ : GenInducedEmbedding R σ F' G0 =>
                    v ∈ Set.range e₂.toFun)).card : ℝ)
                  ≤ (W.sum (fun w => (Finset.univ.filter
                      (fun e₂ : GenInducedEmbedding R σ F' G0 =>
                      e₂.toFun w = v)).card) : ℝ) := by
                    exact_mod_cast (Finset.card_le_card h_v_sub).trans Finset.card_biUnion_le
                _ ≤ W.sum (fun _ =>
                      C_max * (Nat.choose (Δ G0.forget) (f' - 1) : ℝ)) := by
                    exact Finset.sum_le_sum fun w hw =>
                      h_fiber_bound w ((Finset.mem_filter.mp hw).2) v hv_not_sigma
                _ = (f' : ℝ) * C_max * (Nat.choose (Δ G0.forget) (f' - 1) : ℝ) := by
                    rw [Finset.sum_const, nsmul_eq_mul, hW_card]; ring
            calc ((bad e₁).card : ℝ)
                ≤ (unlabImg.sum (fun v => (Finset.univ.filter
                    (fun e₂ : GenInducedEmbedding R σ F' G0 =>
                    v ∈ Set.range e₂.toFun)).card) : ℝ) := by
                  exact_mod_cast (Finset.card_le_card h_bad_sub).trans Finset.card_biUnion_le
              _ ≤ unlabImg.sum (fun _ =>
                    (f' : ℝ) * C_max *
                    (Nat.choose (Δ G0.forget) (f' - 1) : ℝ)) := by
                  exact Finset.sum_le_sum h_per_v
              _ = (f : ℝ) * f' * C_max *
                    (Nat.choose (Δ G0.forget) (f' - 1) : ℝ) := by
                  rw [Finset.sum_const, nsmul_eq_mul, h_unlabImg_card]; ring
          -- bad + good = total
          have h_bad_eq_compl : ∀ e₁ : GenInducedEmbedding R σ F G0,
              (bad e₁).card + (good e₁).card =
              Fintype.card (GenInducedEmbedding R σ F' G0) := by
            intro e₁
            suffices h_eq : bad e₁ = Finset.univ.filter
                (fun e₂ : GenInducedEmbedding R σ F' G0 =>
                  ¬∀ i : Fin G0.size,
                    (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
                      i ∈ Set.range G0.embedding) by
              have := @Finset.card_filter_add_card_filter_not _
                (Finset.univ : Finset (GenInducedEmbedding R σ F' G0))
                (fun e₂ => ∀ i : Fin G0.size,
                    (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
                      i ∈ Set.range G0.embedding) _ _
              simp only [Finset.card_univ] at this; rw [h_eq]; linarith
            ext e₂; simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨v, hv₁, hv₂, hvσ⟩ hh; exact hvσ ((hh v).mp ⟨hv₁, hv₂⟩)
            · intro hh; by_contra h_all_good; push_neg at h_all_good
              apply hh; intro v; constructor
              · intro ⟨hv₁, hv₂⟩; exact h_all_good v hv₁ hv₂
              · intro hvσ; obtain ⟨i, rfl⟩ := hvσ
                exact ⟨⟨F.embedding i, e₁.compat i⟩, ⟨F'.embedding i, e₂.compat i⟩⟩
          -- NOP = sum of good
          set NOP0 := { p : GenInducedEmbedding R σ F G0 × GenInducedEmbedding R σ F' G0 //
              ∀ i : Fin G0.size,
                (i ∈ Set.range p.1.toFun ∧ i ∈ Set.range p.2.toFun) ↔
                  i ∈ Set.range G0.embedding } with _hNOP0_def
          have h_nop_eq_good : Fintype.card NOP0 =
              Finset.univ.sum (fun e₁ : GenInducedEmbedding R σ F G0 => (good e₁).card) := by
            rw [show Fintype.card NOP0 = Fintype.card (Σ (e₁ : GenInducedEmbedding R σ F G0),
                  {e₂ : GenInducedEmbedding R σ F' G0 //
                    ∀ i : Fin G0.size,
                      (i ∈ Set.range e₁.toFun ∧ i ∈ Set.range e₂.toFun) ↔
                        i ∈ Set.range G0.embedding}) from Fintype.card_congr {
              toFun := fun ⟨⟨e₁, e₂⟩, h⟩ => ⟨e₁, e₂, h⟩
              invFun := fun ⟨e₁, ⟨e₂, h⟩⟩ => ⟨⟨e₁, e₂⟩, h⟩
              left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
              right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }, Fintype.card_sigma]
            congr 1; ext e₁; simp only [good, ← Fintype.card_coe]
            exact Fintype.card_congr (Equiv.subtypeEquivRight (fun e₂ => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]))
          -- sum|bad| + |NOP| = IC * IC
          have h_sum_add :
              Finset.univ.sum (fun e₁ : GenInducedEmbedding R σ F G0 => (bad e₁).card) +
              Fintype.card NOP0 =
              Fintype.card (GenInducedEmbedding R σ F G0) *
                Fintype.card (GenInducedEmbedding R σ F' G0) := by
            rw [h_nop_eq_good, ← Finset.sum_add_distrib]; simp only [h_bad_eq_compl]
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          -- Combine: IC*IC - orbit = IC*IC - |NOP| = sum|bad| ≤ IC * bound ≤ K * C(Δ,f) * C(Δ,f'-1)
          suffices h_key : (genInducedCount R σ F G0 : ℝ) * (genInducedCount R σ F' G0 : ℝ) -
              (genClassesOfSize R σ _ hn_le).sum (fun cls =>
                (genJointCount R σ F F' cls.out : ℝ) * (genInducedCount R σ cls.out G0 : ℝ) /
                  (genFlagAutCount R σ cls.out : ℝ)) ≤
              (genInducedCount R σ F G0 : ℝ) * ((f : ℝ) * f' * C_max *
                (Nat.choose (Δ G0.forget) (f' - 1) : ℝ)) by
            calc (genInducedCount R σ F G0 : ℝ) * (genInducedCount R σ F' G0 : ℝ) -
                  (genClassesOfSize R σ _ hn_le).sum _ ≤
                (genInducedCount R σ F G0 : ℝ) * ((f : ℝ) * f' * C_max *
                  (Nat.choose (Δ G0.forget) (f' - 1) : ℝ)) := h_key
              _ ≤ (C_F0 * (Nat.choose (Δ G0.forget) f : ℝ)) * ((f : ℝ) * f' * C_max *
                    (Nat.choose (Δ G0.forget) (f' - 1) : ℝ)) :=
                mul_le_mul_of_nonneg_right hICF_bound (mul_nonneg (mul_nonneg (mul_nonneg
                  (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hCmax_nn) (Nat.cast_nonneg _))
              _ = K * ((Nat.choose (Δ G0.forget) f : ℝ) *
                      (Nat.choose (Δ G0.forget) (f' - 1) : ℝ)) := by ring
          -- Use orbit = |NOP| (from h_orbit_eq0), then IC*IC - |NOP| = sum|bad|
          rw [h_orbit_eq0]; simp only [genInducedCount]
          -- IC*IC - |NOP| = sum|bad| (from h_sum_add), then sum|bad| ≤ IC * bound
          have h_sum_add_r : (Finset.univ.sum (fun e₁ : GenInducedEmbedding R σ F G0 =>
              (bad e₁).card) : ℝ) + (Fintype.card NOP0 : ℝ) =
            (Fintype.card (GenInducedEmbedding R σ F G0) : ℝ) *
              (Fintype.card (GenInducedEmbedding R σ F' G0) : ℝ) := by
            exact_mod_cast h_sum_add
          have h_sum_bad_le : (Finset.univ.sum (fun e₁ : GenInducedEmbedding R σ F G0 =>
              (bad e₁).card) : ℝ) ≤
            (Fintype.card (GenInducedEmbedding R σ F G0) : ℝ) *
              ((f : ℝ) * f' * C_max * (Nat.choose (Δ G0.forget) (f' - 1) : ℝ)) := by
            calc (∑ e₁ : GenInducedEmbedding R σ F G0, ((bad e₁).card : ℝ))
                ≤ ∑ _ : GenInducedEmbedding R σ F G0,
                  ((f : ℝ) * f' * C_max * (Nat.choose (Δ G0.forget) (f' - 1) : ℝ)) :=
                Finset.sum_le_sum (fun e₁ _ => h_per_e1 e₁)
              _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          linarith [h_sum_add_r, h_sum_bad_le]
      -- Combine: mirrors `overlap_embedding_bound` (lines 2769-2801)
      obtain ⟨K, hK_nn, hK_bound⟩ := genOverlap_count_le
      refine ⟨K, hK_nn, fun G' hG hΔ => ?_⟩
      constructor
      · -- Non-negativity from orbit sum ≤ product
        rw [dif_pos hn_le]
        linarith [genOrbit_sum_le_product G']
      · -- Upper bound from overlap_count_le
        rw [dif_pos hn_le]
        exact hK_bound G' hG hΔ
    -- Sorry'd: genLocalFlagProduct_unlabelledEvalDensity
    have genLFP_unlabelledEvalDensity :
        ∀ G' : GenFlag R σ,
        genUnlabelledEvalDensity (genLocalFlagProduct R σ F F') G' Δ =
          ((genFlagAutCount R σ F : ℝ) * (genFlagAutCount R σ F' : ℝ))⁻¹ *
            (genClassesOfSize R σ (F.size + F'.size - σ.size)
              (by have := F.hsize; have := F'.hsize; omega)).sum
              (fun cls => genJointInducedDensity R σ F F' cls.out *
                genUnlabelledDensity R σ cls.out G' Δ) :=
      by
      intro G'
      set n := F.size + F'.size - σ.size
      have hn : σ.size ≤ n := by have := F.hsize; have := F'.hsize; omega
      have hprod : genLocalFlagProduct R σ F F' =
          ((genFlagAutCount R σ F : ℝ) * (genFlagAutCount R σ F' : ℝ))⁻¹ •
            (genClassesOfSize R σ n hn).sum (fun cls =>
              Finsupp.single cls (genJointInducedDensity R σ F F' cls.out)) := by
        unfold genLocalFlagProduct; rw [dif_pos hn]
      rw [hprod, genUnlabelledEvalDensity_pointwise_smul]; congr 1
      have hsingle : ∀ cls : GenFlagClass R σ, ∀ c : ℝ,
          genUnlabelledEvalDensity (Finsupp.single cls c) G' Δ =
            c * genClassUnlabelledDensity R σ G' Δ cls :=
        fun cls c => Finsupp.sum_single_index (zero_mul _)
      have ueval_sum : ∀ (T : Finset (GenFlagClass R σ)) (h : GenFlagClass R σ → ℝ),
          genUnlabelledEvalDensity (T.sum (fun cls => Finsupp.single cls (h cls))) G' Δ =
            T.sum (fun cls => h cls * genClassUnlabelledDensity R σ G' Δ cls) := by
        intro T h; induction T using Finset.induction with
        | empty => simp [genUnlabelledEvalDensity_zero]
        | @insert a s ha ih =>
          rw [Finset.sum_insert ha, genUnlabelledEvalDensity_add, ih, Finset.sum_insert ha, hsingle]
      rw [ueval_sum]; rfl
    -- Main proof structure
    set f := F.size - σ.size with hf_def
    set f' := F'.size - σ.size with hf'_def
    set n := F.size + F'.size - σ.size with hn_def
    obtain ⟨C_F, hCF_nn, hCF⟩ := hF.bounded
    obtain ⟨C_F', hCF'_nn, hCF'⟩ := hF'.bounded
    obtain ⟨K, hK_nn, hK_bound⟩ := genOverlap_embedding_bound
    by_cases hf'_pos : f' = 0
    · -- f' = 0 case: F' has same size as σ, product is identity
      exact ⟨0, fun G' _ _ => by
        have hsz : F'.size = σ.size := by have := F'.hsize; omega
        rw [genUD_flagIso (genFlagIso_toFlag_of_size_eq F' hsz),
          genUD_type_eq_one, mul_one,
          genLocalFlagProduct_flagIso_right (genFlagIso_toFlag_of_size_eq F' hsz),
          genProduct_unit, genUED_single]
        simp [le_of_lt hε]⟩
    have hf'_ge : 1 ≤ f' := Nat.one_le_iff_ne_zero.mpr hf'_pos
    set M₁ := C_F * C_F' with hM₁_def
    have hM₁_nn : 0 ≤ M₁ := mul_nonneg hCF_nn hCF'_nn
    have hε₁ : 0 < ε / (2 * (M₁ + 1)) :=
      div_pos hε (mul_pos two_pos (by linarith))
    obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ m : ℕ, N₁ ≤ m →
        |(Nat.choose m f' : ℝ) / (Nat.choose (m - f) f' : ℝ) - 1| <
          ε / (2 * (M₁ + 1)) := by
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (choose_ratio_tendsto_one' f' f))
        _ hε₁
      exact ⟨N, fun m hm => by simpa [Real.dist_eq] using hN m hm⟩
    set N₂ := Nat.ceil (2 * K * (↑f' : ℝ) / ε) with hN₂_def
    refine ⟨max N₁ (N₂ + f + f'), fun G' hG hΔ => ?_⟩
    set D := Δ G'.forget with hD_def
    have hD_ge_N₁ : N₁ ≤ D := le_trans (le_max_left _ _) hΔ
    have hD_ge_N₂f' : N₂ + f' ≤ D := by
      have := le_trans (le_max_right N₁ (N₂ + f + f')) hΔ; omega
    have hf_le_D : f ≤ D := by
      have := le_trans (le_max_right N₁ (N₂ + f + f')) hΔ; omega
    have hff_le_D : f + f' ≤ D := by
      have := le_trans (le_max_right N₁ (N₂ + f + f')) hΔ; omega
    -- Set up named quantities for the density decomposition
    set IC_F := (genInducedCount R σ F G' : ℝ) with hIC_F_def
    set IC_F' := (genInducedCount R σ F' G' : ℝ) with hIC_F'_def
    set Aut_F := (genFlagAutCount R σ F : ℝ) with hAut_F_def
    set Aut_F' := (genFlagAutCount R σ F' : ℝ) with hAut_F'_def
    set CDF := (Nat.choose D f : ℝ) with hCDF_def
    set CDF' := (Nat.choose D f' : ℝ) with hCDF'_def
    set CDmfF' := (Nat.choose (D - f) f' : ℝ) with hCDmfF'_def
    set CDF'_1 := (Nat.choose D (f' - 1) : ℝ) with hCDF'_1_def
    have hAut_F_pos : 0 < Aut_F := Nat.cast_pos.mpr (genFlagAutCount_pos σ F)
    have hAut_F'_pos : 0 < Aut_F' := Nat.cast_pos.mpr (genFlagAutCount_pos σ F')
    have hCDF_pos : 0 < CDF := Nat.cast_pos.mpr (Nat.choose_pos hf_le_D)
    have hCDF'_pos : 0 < CDF' := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    have hCDmfF'_pos : 0 < CDmfF' := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
    have hIC_F'_nn : 0 ≤ IC_F' := Nat.cast_nonneg _
    have hα_pos : 0 < (Aut_F * Aut_F')⁻¹ := inv_pos.mpr (mul_pos hAut_F_pos hAut_F'_pos)
    have hα_le_one : (Aut_F * Aut_F')⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_mul_of_one_le_of_one_le
        (Nat.one_le_cast.mpr (genFlagAutCount_pos σ F))
        (Nat.one_le_cast.mpr (genFlagAutCount_pos σ F')))
    have lhs_eq : genUnlabelledDensity R σ F G' Δ * genUnlabelledDensity R σ F' G' Δ =
        (Aut_F * Aut_F')⁻¹ * (IC_F * IC_F' / (CDF * CDF')) := by
      simp only [genUnlabelledDensity, hD_def, hIC_F_def, hIC_F'_def,
        hAut_F_def, hAut_F'_def, hCDF_def, hCDF'_def]
      field_simp; ring
    have hn_le : σ.size ≤ n := by have := F.hsize; have := F'.hsize; omega
    set S := (genClassesOfSize R σ n hn_le).sum (fun cls =>
        (genJointCount R σ F F' cls.out : ℝ) * (genInducedCount R σ cls.out G' : ℝ) /
          (genFlagAutCount R σ cls.out : ℝ)) with hS_def
    have hK_nonneg : 0 ≤ IC_F * IC_F' - S := by
      have h := (hK_bound G' hG hff_le_D).1; rwa [dif_pos hn_le] at h
    have hK_upper : IC_F * IC_F' - S ≤ K * (CDF * CDF'_1) := by
      have h := (hK_bound G' hG hff_le_D).2; rwa [dif_pos hn_le] at h
    have hS_nn' : 0 ≤ S := Finset.sum_nonneg fun cls _ =>
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    set Cff := (Nat.choose (f + f') f : ℝ) with hCff_def
    set CDff := (Nat.choose D (f + f') : ℝ) with hCDff_def
    have hCff_pos : 0 < Cff := Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_right f f'))
    have orbit_sum_eq :
        (genClassesOfSize R σ n hn_le).sum (fun cls =>
          genJointInducedDensity R σ F F' cls.out * genUnlabelledDensity R σ cls.out G' Δ) =
        S / (Cff * CDff) := by
      have h_term : ∀ cls ∈ genClassesOfSize R σ n hn_le,
          genJointInducedDensity R σ F F' cls.out * genUnlabelledDensity R σ cls.out G' Δ =
          (genJointCount R σ F F' cls.out : ℝ) * (genInducedCount R σ cls.out G' : ℝ) /
            (genFlagAutCount R σ cls.out : ℝ) / (Cff * CDff) := by
        intro cls hmem
        have hff_eq : cls.out.size - σ.size = f + f' := by
          have := genClassesOfSize_out_size hmem; have := F.hsize; have := F'.hsize; omega
        rw [show genJointInducedDensity R σ F F' cls.out =
            (genJointCount R σ F F' cls.out : ℝ) / Cff from by
          unfold genJointInducedDensity
          rw [hff_eq, Nat.add_sub_cancel_left, Nat.choose_self, Nat.cast_one, mul_one],
          show genUnlabelledDensity R σ cls.out G' Δ =
            (genInducedCount R σ cls.out G' : ℝ) / ((genFlagAutCount R σ cls.out : ℝ) *
              (Nat.choose (Δ G'.forget) (cls.out.size - σ.size) : ℝ)) from by
          unfold genUnlabelledDensity; congr 1; ring,
          hff_eq, div_mul_div_comm, div_div]
        congr 1; ring
      rw [Finset.sum_congr rfl h_term, ← Finset.sum_div]
    have rhs_eq : genUnlabelledEvalDensity (genLocalFlagProduct R σ F F') G' Δ =
        (Aut_F * Aut_F')⁻¹ * (S / (Cff * CDff)) := by
      rw [genLFP_unlabelledEvalDensity, orbit_sum_eq]
    have hvand' : Cff * CDff = CDF * CDmfF' := by
      rw [mul_comm]; simp only [hCDff_def, hCff_def, hCDF_def, hCDmfF'_def]
      exact_mod_cast choose_vandermonde D f f' hf_le_D hff_le_D
    have diff_factored : genUnlabelledDensity R σ F G' Δ * genUnlabelledDensity R σ F' G' Δ -
        genUnlabelledEvalDensity (genLocalFlagProduct R σ F F') G' Δ =
        (Aut_F * Aut_F')⁻¹ / CDF *
          ((IC_F * IC_F' - S) / CDF' +
           S * (1 / CDF' - 1 / CDmfF')) := by
      rw [lhs_eq, rhs_eq, hvand', mul_sub]; field_simp; ring
    have term1_bound : (Aut_F * Aut_F')⁻¹ / CDF * ((IC_F * IC_F' - S) / CDF') ≤
        K * CDF'_1 / CDF' := by
      calc (Aut_F * Aut_F')⁻¹ / CDF * ((IC_F * IC_F' - S) / CDF')
          ≤ (IC_F * IC_F' - S) / (CDF * CDF') := by
            rw [div_mul_div_comm]
            exact div_le_div_of_nonneg_right
              (by linarith [mul_le_mul_of_nonneg_right hα_le_one hK_nonneg])
              (mul_pos hCDF_pos hCDF'_pos).le
        _ ≤ K * CDF'_1 / CDF' := by
            rw [div_le_div_iff₀ (mul_pos hCDF_pos hCDF'_pos) hCDF'_pos]
            linarith [mul_le_mul_of_nonneg_right hK_upper hCDF'_pos.le,
              show K * (CDF * CDF'_1) * CDF' = K * CDF'_1 * (CDF * CDF') by ring]
    have hαS_bound : (Aut_F * Aut_F')⁻¹ * S / (CDF * CDF') ≤ M₁ := by
      calc (Aut_F * Aut_F')⁻¹ * S / (CDF * CDF')
          ≤ IC_F * IC_F' / (CDF * CDF') :=
            div_le_div_of_nonneg_right
              (by linarith [mul_le_mul_of_nonneg_right hα_le_one hS_nn'])
              (mul_pos hCDF_pos hCDF'_pos).le
        _ ≤ M₁ := by
            rw [div_le_iff₀ (mul_pos hCDF_pos hCDF'_pos)]
            calc IC_F * IC_F'
                ≤ (C_F * CDF) * (C_F' * CDF') :=
                  mul_le_mul
                    (by have := hCF G' hG; simp only [genLocalDensity] at this;
                        rwa [div_le_iff₀ hCDF_pos] at this)
                    (by have := hCF' G' hG; simp only [genLocalDensity] at this;
                        rwa [div_le_iff₀ hCDF'_pos] at this)
                    hIC_F'_nn (mul_nonneg hCF_nn hCDF_pos.le)
              _ = M₁ * (CDF * CDF') := by ring
    have term2_bound :
        |(Aut_F * Aut_F')⁻¹ / CDF * (S * (1 / CDF' - 1 / CDmfF'))| ≤
        M₁ * |CDF' / CDmfF' - 1| := by
      rw [abs_mul, abs_of_nonneg (div_nonneg hα_pos.le hCDF_pos.le),
        abs_mul, abs_of_nonneg hS_nn']
      rw [show |1 / CDF' - 1 / CDmfF'| = |CDF' / CDmfF' - 1| / CDF' from by
        rw [show (1 / CDF' - 1 / CDmfF') = (CDmfF' - CDF') / (CDF' * CDmfF') from by
              field_simp,
          show (CDF' / CDmfF' - 1) = (CDF' - CDmfF') / CDmfF' from by field_simp,
          abs_div, abs_div, abs_of_pos (mul_pos hCDF'_pos hCDmfF'_pos),
          abs_of_pos hCDmfF'_pos, div_div, abs_sub_comm, mul_comm CDmfF' CDF'],
        show (Aut_F * Aut_F')⁻¹ / CDF * (S * (|CDF' / CDmfF' - 1| / CDF')) =
          (Aut_F * Aut_F')⁻¹ * S / (CDF * CDF') * |CDF' / CDmfF' - 1| from by field_simp]
      exact mul_le_mul_of_nonneg_right hαS_bound (abs_nonneg _)
    rw [diff_factored]
    calc |(Aut_F * Aut_F')⁻¹ / CDF * ((IC_F * IC_F' - S) / CDF' + S * (1 / CDF' - 1 / CDmfF'))|
        ≤ |(Aut_F * Aut_F')⁻¹ / CDF * ((IC_F * IC_F' - S) / CDF')| +
          |(Aut_F * Aut_F')⁻¹ / CDF * (S * (1 / CDF' - 1 / CDmfF'))| := by
          rw [mul_add]; exact abs_add_le _ _
      _ ≤ K * CDF'_1 / CDF' + M₁ * |CDF' / CDmfF' - 1| := by
          apply add_le_add _ term2_bound
          rw [abs_of_nonneg]
          · exact term1_bound
          · exact mul_nonneg (div_nonneg hα_pos.le hCDF_pos.le)
              (div_nonneg (by linarith) hCDF'_pos.le)
      _ ≤ K * (↑f' : ℝ) / ((D : ℝ) - ↑f' + 1) + M₁ * |(Nat.choose D f' : ℝ) /
          (Nat.choose (D - f) f' : ℝ) - 1| := by
          rw [mul_div_assoc, choose_ratio_pred D f' hf'_ge (by omega : f' ≤ D), ← mul_div_assoc]
      _ ≤ ε / 2 + ε / 2 := by
          apply add_le_add
          · -- overlap bound: K * f' / (D - f' + 1) ≤ ε / 2
            have hKf'_nn : 0 ≤ K * (↑f' : ℝ) := mul_nonneg hK_nn (Nat.cast_nonneg _)
            have hDmf'_pos : (0 : ℝ) < (D : ℝ) - ↑f' + 1 := by
              have : (↑f' : ℝ) ≤ (D : ℝ) := Nat.cast_le.mpr (by omega : f' ≤ D); linarith
            rcases eq_or_lt_of_le hKf'_nn with hKf'_zero | _
            · rw [← hKf'_zero, zero_div]; exact le_of_lt (half_pos hε)
            · rw [div_le_div_iff₀ hDmf'_pos two_pos]
              have hN₂_le_D : (N₂ : ℝ) ≤ (D : ℝ) - ↑f' := by
                have : (↑(N₂ + f') : ℝ) ≤ (D : ℝ) := Nat.cast_le.mpr hD_ge_N₂f'
                push_cast at this ⊢; linarith
              nlinarith [(div_le_iff₀ hε).mp (le_trans (Nat.le_ceil _) hN₂_le_D)]
          · -- ratio bound: M₁ * |C(D,f')/C(D-f,f') - 1| ≤ ε / 2
            calc M₁ * |(Nat.choose D f' : ℝ) / (Nat.choose (D - f) f' : ℝ) - 1|
              ≤ M₁ * (ε / (2 * (M₁ + 1))) :=
                mul_le_mul_of_nonneg_left (le_of_lt (hN₁ D hD_ge_N₁)) hM₁_nn
              _ = ε * (M₁ / (2 * (M₁ + 1))) := by ring
              _ ≤ ε * (1 / 2) := mul_le_mul_of_nonneg_left
                  (by rw [div_le_div_iff₀ (mul_pos two_pos (by linarith : (0:ℝ) < M₁ + 1)) two_pos]
                      nlinarith) hε.le
              _ = ε / 2 := by ring
      _ = ε := by ring
  intro ε hε
  by_cases hf : f = 0
  · exact ⟨0, fun G _ _ => by
      simp [hf, genUnlabelledEvalDensity_zero, GenFlagAlg.mul, Finsupp.sum_zero_index]; exact hε.le⟩
  by_cases hg : g = 0
  · exact ⟨0, fun G _ _ => by
      subst hg; simp only [genUnlabelledEvalDensity_zero, mul_zero]
      have : (f.mul 0 : GenFlagAlg R σ) = 0 := by
        simp only [GenFlagAlg.mul]
        exact Finset.sum_eq_zero (fun _ _ => Finsupp.sum_zero_index)
      rw [this, genUnlabelledEvalDensity_zero, sub_self, abs_zero]; exact hε.le⟩
  set Sf := f.support; set Sg := g.support
  set Wf := Sf.sum (fun cls => |f cls|); set Wg := Sg.sum (fun cls => |g cls|)
  have hWf_pos : 0 < Wf := Finset.sum_pos (fun cls hcls =>
    abs_pos.mpr (Finsupp.mem_support_iff.mp hcls)) (Finsupp.support_nonempty_iff.mpr hf)
  have hWg_pos : 0 < Wg := Finset.sum_pos (fun cls hcls =>
    abs_pos.mpr (Finsupp.mem_support_iff.mp hcls)) (Finsupp.support_nonempty_iff.mpr hg)
  have hW_pos : 0 < Wf * Wg := mul_pos hWf_pos hWg_pos
  set ε' := ε / (Wf * Wg) with hε'_def
  have hε'_pos : 0 < ε' := div_pos hε hW_pos
  -- For each pair (cls₁, cls₂), get a Δ₀ bound
  have hbasis : ∀ cls₁ ∈ Sf, ∀ cls₂ ∈ Sg,
      ∃ Δ₀ : ℕ, ∀ G : GenFlag R σ, 𝒢 G.forget → Δ₀ ≤ Δ G.forget →
        |genUnlabelledDensity R σ cls₁.out G Δ * genUnlabelledDensity R σ cls₂.out G Δ -
         genUnlabelledEvalDensity (genLocalFlagProduct R σ cls₁.out cls₂.out) G Δ| ≤ ε' :=
    fun cls₁ h₁ cls₂ h₂ => genProduct_limit_basis cls₁.out cls₂.out
      (hf_local cls₁ h₁) (hg_local cls₂ h₂) ε' hε'_pos
  -- Take Δ₀ as max over all pairs (using classical choice + Finset.sup)
  classical
  choose Δ₀_fn hΔ₀_fn using fun (cls₁ : GenFlagClass R σ) (h₁ : cls₁ ∈ Sf)
      (cls₂ : GenFlagClass R σ) (h₂ : cls₂ ∈ Sg) => hbasis cls₁ h₁ cls₂ h₂
  set Δ₀ := Sf.sup (fun cls₁ => Sg.sup (fun cls₂ =>
    if h₁ : cls₁ ∈ Sf then if h₂ : cls₂ ∈ Sg then Δ₀_fn cls₁ h₁ cls₂ h₂ else 0 else 0))
  refine ⟨Δ₀, fun G hG hΔ => ?_⟩
  have hpair : ∀ cls₁ ∈ Sf, ∀ cls₂ ∈ Sg,
      |genUnlabelledDensity R σ cls₁.out G Δ * genUnlabelledDensity R σ cls₂.out G Δ -
       genUnlabelledEvalDensity (genLocalFlagProduct R σ cls₁.out cls₂.out) G Δ| ≤ ε' := by
    intro cls₁ h₁ cls₂ h₂
    apply hΔ₀_fn cls₁ h₁ cls₂ h₂ G hG
    calc Δ₀_fn cls₁ h₁ cls₂ h₂
        = (if h₁' : cls₁ ∈ Sf then if h₂' : cls₂ ∈ Sg then Δ₀_fn cls₁ h₁' cls₂ h₂' else 0 else 0) := by
          simp [h₁, h₂]
      _ ≤ Sg.sup (fun cls₂ => if h₁' : cls₁ ∈ Sf then if h₂' : cls₂ ∈ Sg then
            Δ₀_fn cls₁ h₁' cls₂ h₂' else 0 else 0) :=
          Finset.le_sup (f := fun cls₂ => if h₁' : cls₁ ∈ Sf then if h₂' : cls₂ ∈ Sg then
            Δ₀_fn cls₁ h₁' cls₂ h₂' else 0 else 0) h₂
      _ ≤ Δ₀ :=
          Finset.le_sup (f := fun cls₁ => Sg.sup (fun cls₂ =>
            if h₁' : cls₁ ∈ Sf then if h₂' : cls₂ ∈ Sg then
              Δ₀_fn cls₁ h₁' cls₂ h₂' else 0 else 0)) h₁
      _ ≤ Δ G.forget := hΔ
  -- Bilinear decomposition: rewrite difference as double sum of per-pair errors
  set ρ := fun cls => genUnlabelledDensity R σ (Quotient.out cls) G Δ
  have heval_fg : ∀ (v : GenFlagAlg R σ), genUnlabelledEvalDensity v G Δ =
      v.support.sum (fun cls => v cls * ρ cls) := fun v => by
    simp only [genUnlabelledEvalDensity, Finsupp.sum]; rfl
  have ueval_sum : ∀ (S : Finset (GenFlagClass R σ)) (h : GenFlagClass R σ → GenFlagAlg R σ),
      genUnlabelledEvalDensity (S.sum h) G Δ =
        S.sum (fun cls => genUnlabelledEvalDensity (h cls) G Δ) := by
    intro S h; induction S using Finset.induction with
    | empty => simp [genUnlabelledEvalDensity_zero]
    | @insert a s ha ih => rw [Finset.sum_insert ha,
        genUnlabelledEvalDensity_add, ih, Finset.sum_insert ha]
  have heval_mul : genUnlabelledEvalDensity (f.mul g) G Δ =
      Sf.sum (fun cls₁ => Sg.sum (fun cls₂ => f cls₁ * g cls₂ *
          genUnlabelledEvalDensity (genLocalFlagProduct R σ cls₁.out cls₂.out) G Δ)) := by
    simp only [GenFlagAlg.mul, Finsupp.sum]; rw [ueval_sum]; congr 1; ext cls₁; rw [ueval_sum]
    congr 1; ext cls₂; rw [genUnlabelledEvalDensity_pointwise_smul,
      congrArg (genUnlabelledEvalDensity · G Δ) (genLocalFlagProduct_class_out σ cls₁ cls₂)]
  rw [show genUnlabelledEvalDensity f G Δ * genUnlabelledEvalDensity g G Δ -
      genUnlabelledEvalDensity (f.mul g) G Δ =
      Sf.sum (fun cls₁ => Sg.sum (fun cls₂ => f cls₁ * g cls₂ *
        (ρ cls₁ * ρ cls₂ -
          genUnlabelledEvalDensity (genLocalFlagProduct R σ cls₁.out cls₂.out) G Δ))) from by
    rw [heval_fg f, heval_fg g, Finset.sum_mul, heval_mul, ← Finset.sum_sub_distrib]
    congr 1; ext cls₁; rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1; ext cls₂; ring]
  -- Triangle inequality + per-pair bound
  calc |Sf.sum (fun cls₁ => Sg.sum (fun cls₂ => f cls₁ * g cls₂ *
          (ρ cls₁ * ρ cls₂ -
            genUnlabelledEvalDensity (genLocalFlagProduct R σ cls₁.out cls₂.out) G Δ)))|
      ≤ Sf.sum (fun cls₁ => |Sg.sum (fun cls₂ => f cls₁ * g cls₂ *
          (ρ cls₁ * ρ cls₂ -
            genUnlabelledEvalDensity (genLocalFlagProduct R σ cls₁.out cls₂.out) G Δ))|) :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ Sf.sum (fun cls₁ => Sg.sum (fun cls₂ => |f cls₁ * g cls₂ *
          (ρ cls₁ * ρ cls₂ -
            genUnlabelledEvalDensity (genLocalFlagProduct R σ cls₁.out cls₂.out) G Δ)|)) := by
        gcongr with cls₁ _; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ Sf.sum (fun cls₁ => Sg.sum (fun cls₂ => |f cls₁| * |g cls₂| * ε')) := by
        gcongr with cls₁ h₁ cls₂ h₂; rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hpair cls₁ h₁ cls₂ h₂)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = Wf * Wg * ε' := by simp only [← Finset.sum_mul, ← Finset.mul_sum]; ring
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hW_pos)

/-- A generic Δ-increasing sequence. -/
structure GenDeltaIncreasingSeq (R : RelUniverse) (σ : GenFlagType R)
    (Δ : GenGraphParam R) where
  seq : ℕ → GenFlag R σ
  increasing : StrictMono (fun k => Δ (seq k).forget)

/-- A **generic limit functional** φ ∈ Φ^σ for an arbitrary `RelUniverse`.
    Mirrors `LimitFunctional` but works over any `RelUniverse`. -/
structure GenLimitFunctional (R : RelUniverse) (σ : GenFlagType R)
    (𝒢 : GenGraphClass R) (Δ : GenGraphParam R) where
  eval : GenFlag R σ → ℝ
  nonneg_on_flags : ∀ F, 0 ≤ eval F
  eval_type : eval σ.toFlag = 1
  eval_iso : ∀ F₁ F₂, GenFlagIso σ F₁ F₂ → eval F₁ = eval F₂
  eval_nonlocal : ∀ F, ¬GenIsLocalFlag σ F 𝒢 Δ → eval F = 0
  is_homomorphism : ∀ v w : GenFlagAlg R σ,
    (∀ cls ∈ v.support, GenIsLocalFlag σ cls.out 𝒢 Δ) →
    (∀ cls ∈ w.support, GenIsLocalFlag σ cls.out 𝒢 Δ) →
    genEvalAlgOf eval (v.mul w) = genEvalAlgOf eval v * genEvalAlgOf eval w
  /-- The Δ-increasing sequence from which this functional was constructed. -/
  seq : GenDeltaIncreasingSeq R σ Δ
  /-- Every flag in the sequence belongs to 𝒢. -/
  seq_in_class : ∀ k, 𝒢 (seq.seq k).forget
  /-- The convergent subsequence extracted by Tychonoff/Bolzano–Weierstrass. -/
  sub : ℕ → ℕ
  /-- The subsequence is strictly monotone. -/
  sub_strictMono : StrictMono sub
  /-- For each local flag F, the unlabelled density along the subsequence
      converges to eval F. -/
  convergence : ∀ F, GenIsLocalFlag σ F 𝒢 Δ →
    Filter.Tendsto (fun k => genUnlabelledDensity R σ F (seq.seq (sub k)) Δ)
      Filter.atTop (nhds (eval F))

/-! ### Generic helper lemmas for the Tychonoff construction -/

/-- `GenFlag R σ` is countable: a countable union (over size n) of finite types. -/
noncomputable instance GenFlag.instCountable {R : RelUniverse} {σ : GenFlagType R} :
    Countable (GenFlag R σ) := by
  -- Each fiber (fixed n) is finite since R.Str n and Fin σ.size ↪ Fin n are both Fintype
  have : ∀ n, Fintype (Σ (s : R.Str n), { f : Fin σ.size ↪ Fin n // R.comap f s = σ.str }) := by
    intro n
    haveI : Fintype (R.Str n) := R.instFintype n
    haveI : DecidableEq (R.Str n) := R.instDecEq n
    haveI : DecidableEq (R.Str σ.size) := R.instDecEq σ.size
    exact Sigma.instFintype
  let T := Σ (n : ℕ), Σ (s : R.Str n), { f : Fin σ.size ↪ Fin n // R.comap f s = σ.str }
  haveI (n : ℕ) : Countable (Σ (s : R.Str n),
      { f : Fin σ.size ↪ Fin n // R.comap f s = σ.str }) := by
    haveI := this n; infer_instance
  have hT : Countable T := inferInstance
  exact @Function.Injective.countable (GenFlag R σ) T hT
    (fun F => ⟨F.size, F.str, ⟨F.embedding, F.isInduced⟩⟩)
    (fun F₁ F₂ h => by
      obtain ⟨s₁, str₁, emb₁, ind₁, hs₁⟩ := F₁
      obtain ⟨s₂, str₂, emb₂, ind₂, hs₂⟩ := F₂
      simp only [T, Sigma.mk.inj_iff] at h
      obtain ⟨hn, hrest⟩ := h; subst hn
      simp only [heq_eq_eq, Sigma.mk.inj_iff] at hrest
      obtain ⟨hstr, hemb⟩ := hrest; subst hstr
      simp only [heq_eq_eq, Subtype.mk.injEq] at hemb; subst hemb
      rfl)

/-- `GenFlagClass R σ` is countable since it's a quotient of `GenFlag R σ`. -/
noncomputable instance GenFlagClass.instCountable {R : RelUniverse} {σ : GenFlagType R} :
    Countable (GenFlagClass R σ) := by
  unfold GenFlagClass; infer_instance

/-- Generic unlabelled density is nonneg. -/
private theorem genUnlabelledDensity_nonneg {R : RelUniverse} (σ : GenFlagType R)
    (F G : GenFlag R σ) (Δ : GenGraphParam R) :
    0 ≤ genUnlabelledDensity R σ F G Δ := by
  unfold genUnlabelledDensity
  exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Generic unlabelled density ≤ generic local density (since flagAutCount ≥ 1). -/
private theorem genUnlabelledDensity_le_genLocalDensity {R : RelUniverse} (σ : GenFlagType R)
    (F G : GenFlag R σ) (Δ : GenGraphParam R) :
    genUnlabelledDensity R σ F G Δ ≤ genLocalDensity σ F G Δ := by
  unfold genUnlabelledDensity
  -- genUnlabelledDensity = IC / (C * Aut) = (IC / C) / Aut = genLocalDensity / Aut
  rw [show (genInducedCount R σ F G : ℝ) /
      ((Nat.choose (Δ G.forget) (F.size - σ.size) : ℝ) * (genFlagAutCount R σ F : ℝ)) =
      genLocalDensity σ F G Δ / (genFlagAutCount R σ F : ℝ) from by
    unfold genLocalDensity; rw [div_div]]
  have hnn : 0 ≤ genLocalDensity σ F G Δ := by
    unfold genLocalDensity
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact div_le_self hnn (Nat.one_le_cast.mpr (genFlagAutCount_pos σ F))

/-- Generic unlabelled density is iso-invariant. -/
private theorem genUnlabelledDensity_flagIso {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₂ G : GenFlag R σ} {Δ : GenGraphParam R} (h : GenFlagIso σ F₁ F₂) :
    genUnlabelledDensity R σ F₁ G Δ = genUnlabelledDensity R σ F₂ G Δ := by
  unfold genUnlabelledDensity
  rw [genInducedCount_flagIso h, genFlagAutCount_flagIso h,
    show F₁.size = F₂.size from genFlagIso_size_eq h]

/-- Generic local density of the type is 1. -/
private theorem genLocalDensity_type_eq_one {R : RelUniverse} (σ : GenFlagType R)
    (G : GenFlag R σ) (Δ : GenGraphParam R) :
    genLocalDensity σ σ.toFlag G Δ = 1 := by
  unfold genLocalDensity
  have hsub : σ.toFlag.size - σ.size = 0 := Nat.sub_self σ.size
  rw [hsub, Nat.choose_zero_right, genInducedCount_toFlag_eq_one]
  simp

/-- Generic unlabelled density of the type is 1. -/
private theorem genUnlabelledDensity_type_eq_one {R : RelUniverse} (σ : GenFlagType R)
    (G : GenFlag R σ) (Δ : GenGraphParam R) :
    genUnlabelledDensity R σ σ.toFlag G Δ = 1 := by
  unfold genUnlabelledDensity
  rw [genInducedCount_toFlag_eq_one]
  have hsub : σ.toFlag.size - σ.size = 0 := Nat.sub_self σ.size
  rw [hsub, Nat.choose_zero_right, genFlagAutCount_toFlag]
  simp

/-- Swapping a finite generic Finsupp sum with a limit. -/
theorem genEvalAlgOf_eq_limit {R : RelUniverse}
    (σ : GenFlagType R) (𝒢 : GenGraphClass R) (Δ : GenGraphParam R)
    (seq : GenDeltaIncreasingSeq R σ Δ)
    (sub : ℕ → ℕ)
    (eval : GenFlag R σ → ℝ)
    (hconv : ∀ F : GenFlag R σ, GenIsLocalFlag σ F 𝒢 Δ →
      Filter.Tendsto (fun k => genUnlabelledDensity R σ F (seq.seq (sub k)) Δ)
        Filter.atTop (nhds (eval F)))
    (_hnonlocal : ∀ F : GenFlag R σ, ¬GenIsLocalFlag σ F 𝒢 Δ → eval F = 0)
    (v : GenFlagAlg R σ)
    (hv : ∀ cls ∈ v.support, GenIsLocalFlag σ cls.out 𝒢 Δ) :
    Filter.Tendsto (fun k => genUnlabelledEvalDensity v (seq.seq (sub k)) Δ)
      Filter.atTop (nhds (genEvalAlgOf eval v)) := by
  simp only [genEvalAlgOf, genUnlabelledEvalDensity, Finsupp.sum,
    show ∀ (cls : GenFlagClass R σ) (G : GenFlag R σ),
      genClassUnlabelledDensity R σ G Δ cls = genUnlabelledDensity R σ cls.out G Δ from
      fun _ _ => rfl]
  exact tendsto_finset_sum _ fun cls hcls => (hconv cls.out (hv cls hcls)).const_mul _

set_option maxHeartbeats 1600000 in
-- Generic limit functional construction (Tychonoff + product_limit):
-- For any RelUniverse, constructs a limit functional from any Δ-increasing
-- sequence in 𝒢. Mirrors limit_functional_construction for simple graphs.
noncomputable def genLimit_functional_construction (R : RelUniverse)
    (σ : GenFlagType R) (𝒢 : GenGraphClass R) (Δ : GenGraphParam R)
    (seq : GenDeltaIncreasingSeq R σ Δ)
    (hlocal : ∀ k, 𝒢 (seq.seq k).forget) :
    GenLimitFunctional R σ 𝒢 Δ := by
  classical
  -- Step 1: Define the product-space sequence.
  let u : ℕ → (GenFlagClass R σ → ℝ) := fun k cls =>
    if GenIsLocalFlag σ cls.out 𝒢 Δ then
      genUnlabelledDensity R σ cls.out (seq.seq k) Δ
    else 0
  -- Step 2: Uniform bounds on u k cls for each cls.
  have hbound_u : ∀ cls : GenFlagClass R σ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k, u k cls ≤ C := by
    intro cls
    by_cases hloc : GenIsLocalFlag σ cls.out 𝒢 Δ
    · obtain ⟨C, hC0, hCbound⟩ := hloc.bounded
      exact ⟨C, hC0, fun k => by
        simp only [u, if_pos hloc]
        exact le_trans (genUnlabelledDensity_le_genLocalDensity σ cls.out (seq.seq k) Δ)
          (hCbound (seq.seq k) (hlocal k))⟩
    · exact ⟨0, le_rfl, fun k => by simp only [u, if_neg hloc]; exact le_refl 0⟩
  let B : GenFlagClass R σ → ℝ := fun cls => (hbound_u cls).choose
  have hB_nn : ∀ cls, 0 ≤ B cls := fun cls => (hbound_u cls).choose_spec.1
  have hB_bound : ∀ cls k, u k cls ≤ B cls :=
    fun cls => (hbound_u cls).choose_spec.2
  -- u k lies in ∏ cls, Set.Icc 0 (B cls)
  have hu_mem : ∀ k, u k ∈ Set.pi Set.univ (fun cls => Set.Icc 0 (B cls)) := by
    intro k cls _
    refine ⟨?_, hB_bound cls k⟩
    simp only [u]; split_ifs
    · exact genUnlabelledDensity_nonneg σ cls.out (seq.seq k) Δ
    · exact le_refl 0
  -- Tychonoff: the product is compact
  have hcompact : IsCompact (Set.pi Set.univ (fun cls => Set.Icc 0 (B cls))) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  -- Sequential compactness (GenFlagClass is countable, so the product is first-countable)
  have hsub := hcompact.tendsto_subseq hu_mem
  let a := hsub.choose
  have ha_mem : a ∈ Set.pi Set.univ (fun cls => Set.Icc 0 (B cls)) :=
    hsub.choose_spec.1
  let φ := hsub.choose_spec.2.choose
  have hφ_mono : StrictMono φ := hsub.choose_spec.2.choose_spec.1
  have hφ_tend : ∀ x, Filter.Tendsto (fun n => u (φ n) x) Filter.atTop (nhds (a x)) := by
    have := hsub.choose_spec.2.choose_spec.2
    rwa [tendsto_pi_nhds] at this
  -- Step 3: Define eval.
  let eval : GenFlag R σ → ℝ := fun F =>
    if GenIsLocalFlag σ F 𝒢 Δ then a (GenFlagClass.mk F) else 0
  have heval_local : ∀ F : GenFlag R σ, GenIsLocalFlag σ F 𝒢 Δ →
      eval F = a (GenFlagClass.mk F) := by
    intro F hF; simp only [eval, if_pos hF]
  have heval_nonlocal : ∀ F : GenFlag R σ, ¬GenIsLocalFlag σ F 𝒢 Δ →
      eval F = 0 := by
    intro F hF; simp only [eval, if_neg hF]
  -- Step 4: Pointwise convergence for local flags
  have hconv_local : ∀ F : GenFlag R σ, GenIsLocalFlag σ F 𝒢 Δ →
      Filter.Tendsto (fun k => genUnlabelledDensity R σ F (seq.seq (φ k)) Δ)
        Filter.atTop (nhds (eval F)) := by
    intro F hF
    rw [heval_local F hF]
    have htend_class := hφ_tend (GenFlagClass.mk F)
    have hiso := Quotient.exact (Quotient.out_eq (GenFlagClass.mk F))
    have hout_local : GenIsLocalFlag σ (GenFlagClass.mk F).out 𝒢 Δ :=
      GenIsLocalFlag_flagIso hiso.symm hF
    have hu_eq : ∀ k, u (φ k) (GenFlagClass.mk F) =
        genUnlabelledDensity R σ (GenFlagClass.mk F).out (seq.seq (φ k)) Δ := by
      intro k; simp only [u, if_pos hout_local]
    simp_rw [hu_eq] at htend_class
    convert htend_class using 1
    ext k
    exact (genUnlabelledDensity_flagIso hiso).symm
  -- Step 5: Verify eval_type
  have heval_type : eval σ.toFlag = 1 := by
    have htype_local : GenIsLocalFlag σ σ.toFlag 𝒢 Δ := by
      refine GenIsLocalFlag.intro σ σ.toFlag 𝒢 Δ ?_ (fun ext => ?_)
      · exact ⟨1, le_of_lt one_pos, fun G _ => by
          rw [genLocalDensity_type_eq_one]⟩
      · exact absurd (Set.mem_range.mpr ⟨ext.vertex, by
          simp [GenFlagType.toFlag]⟩) ext.unlabelled
    rw [heval_local σ.toFlag htype_local]
    have hout_local : GenIsLocalFlag σ (GenFlagClass.mk σ.toFlag).out 𝒢 Δ :=
      GenIsLocalFlag_flagIso
        ((Quotient.exact (Quotient.out_eq (GenFlagClass.mk σ.toFlag))).symm)
        htype_local
    have htend := hφ_tend (GenFlagClass.mk σ.toFlag)
    have hu_eq : ∀ k, u (φ k) (GenFlagClass.mk σ.toFlag) = 1 := by
      intro k
      simp only [u, if_pos hout_local]
      rw [genUnlabelledDensity_flagIso
        (Quotient.exact (Quotient.out_eq (GenFlagClass.mk σ.toFlag)))]
      exact genUnlabelledDensity_type_eq_one σ (seq.seq (φ k)) Δ
    have htend' : Filter.Tendsto (fun (_ : ℕ) => (1 : ℝ)) Filter.atTop
        (nhds (a (GenFlagClass.mk σ.toFlag))) := by
      have : (fun k => u (φ k) (GenFlagClass.mk σ.toFlag)) = fun (_ : ℕ) => (1 : ℝ) := by
        ext k; exact hu_eq k
      rw [← this]; exact htend
    exact tendsto_nhds_unique htend' tendsto_const_nhds
  -- Step 6: Build the GenLimitFunctional
  exact ⟨eval,
    -- nonneg_on_flags
    fun F => by
      by_cases hF : GenIsLocalFlag σ F 𝒢 Δ
      · rw [heval_local F hF]
        exact (ha_mem (GenFlagClass.mk F) (Set.mem_univ _)).1
      · rw [heval_nonlocal F hF],
    -- eval_type
    heval_type,
    -- eval_iso
    fun F₁ F₂ hiso => by
      by_cases hF₁ : GenIsLocalFlag σ F₁ 𝒢 Δ
      · have hF₂ := GenIsLocalFlag_flagIso hiso hF₁
        rw [heval_local F₁ hF₁, heval_local F₂ hF₂]
        rw [show GenFlagClass.mk F₁ = GenFlagClass.mk F₂ from
          (GenFlagClass.mk_eq F₁ F₂).mpr hiso]
      · have hF₂' : ¬GenIsLocalFlag σ F₂ 𝒢 Δ :=
          fun h => hF₁ (GenIsLocalFlag_flagIso hiso.symm h)
        rw [heval_nonlocal F₁ hF₁, heval_nonlocal F₂ hF₂'],
    -- eval_nonlocal
    heval_nonlocal,
    -- is_homomorphism
    fun v w hv hw => by
      have hvw_local := genMul_local_support v w 𝒢 Δ hv hw
      have htend_v := genEvalAlgOf_eq_limit σ 𝒢 Δ seq φ eval
        hconv_local heval_nonlocal v hv
      have htend_w := genEvalAlgOf_eq_limit σ 𝒢 Δ seq φ eval
        hconv_local heval_nonlocal w hw
      have htend_vw := genEvalAlgOf_eq_limit σ 𝒢 Δ seq φ eval
        hconv_local heval_nonlocal (v.mul w) hvw_local
      have htend_prod := htend_v.mul htend_w
      have hdiff_zero : Filter.Tendsto
          (fun k => genUnlabelledEvalDensity v (seq.seq (φ k)) Δ *
                    genUnlabelledEvalDensity w (seq.seq (φ k)) Δ -
                    genUnlabelledEvalDensity (v.mul w) (seq.seq (φ k)) Δ)
          Filter.atTop (nhds 0) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        obtain ⟨Δ₀, hΔ₀⟩ := genProduct_limit R σ v w 𝒢 Δ hv hw (ε / 2) (half_pos hε)
        have hmono : StrictMono (fun k => Δ (seq.seq (φ k)).forget) :=
          seq.increasing.comp hφ_mono
        obtain ⟨N, hN⟩ := strictMono_nat_eventually_ge hmono Δ₀
        exact ⟨N, fun k hk => by
          simp only [Real.dist_eq, sub_zero]
          exact lt_of_le_of_lt
            (hΔ₀ _ (hlocal (φ k)) (le_trans hN (hmono.monotone hk)))
            (half_lt_self hε)⟩
      have htend_vw_prod : Filter.Tendsto
          (fun k => genUnlabelledEvalDensity (v.mul w) (seq.seq (φ k)) Δ)
          Filter.atTop (nhds (genEvalAlgOf eval v * genEvalAlgOf eval w)) := by
        have h := htend_prod.sub hdiff_zero
        simp only [sub_zero] at h
        convert h using 1
        ext k; ring
      exact tendsto_nhds_unique htend_vw htend_vw_prod,
    -- seq
    seq,
    -- seq_in_class
    hlocal,
    -- sub
    φ,
    -- sub_strictMono
    hφ_mono,
    -- convergence
    hconv_local⟩

/-- Generic evaluation of a limit functional on a `GenFlagAlg` element. -/
noncomputable def GenLimitFunctional.evalAlg {R : RelUniverse} {σ : GenFlagType R}
    {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    (φ : GenLimitFunctional R σ 𝒢 Δ) (v : GenFlagAlg R σ) : ℝ :=
  genEvalAlgOf φ.eval v

/-- `evalAlg` agrees with `genEvalAlgOf`. -/
theorem GenLimitFunctional.evalAlg_eq_genEvalAlgOf {R : RelUniverse} {σ : GenFlagType R}
    {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    (φ : GenLimitFunctional R σ 𝒢 Δ) (v : GenFlagAlg R σ) :
    φ.evalAlg v = genEvalAlgOf φ.eval v := rfl

/-- `evalAlg` on a single flag class. -/
theorem GenLimitFunctional.evalAlg_single {R : RelUniverse} {σ : GenFlagType R}
    {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    (φ : GenLimitFunctional R σ 𝒢 Δ) (F : GenFlag R σ) :
    φ.evalAlg (GenFlagAlg.single F) = φ.eval F := by
  simp only [evalAlg, genEvalAlgOf, GenFlagAlg.single]
  rw [Finsupp.sum_single_index (by simp)]
  rw [one_mul]
  exact φ.eval_iso _ F (Quotient.mk_out (s := genFlagSetoid σ) F)

/-- `evalAlg` distributes over scalar multiplication. -/
theorem GenLimitFunctional.evalAlg_smul {R : RelUniverse} {σ : GenFlagType R}
    {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    (φ : GenLimitFunctional R σ 𝒢 Δ) (c : ℝ) (v : GenFlagAlg R σ) :
    φ.evalAlg (c • v) = c * φ.evalAlg v := by
  simp only [evalAlg, genEvalAlgOf]
  rw [Finsupp.sum_smul_index (by intro; ring)]
  simp only [Finsupp.sum, Finset.mul_sum]
  congr 1
  ext cls
  ring

/-- `evalAlg` distributes over addition. -/
theorem GenLimitFunctional.evalAlg_add {R : RelUniverse} {σ : GenFlagType R}
    {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    (φ : GenLimitFunctional R σ 𝒢 Δ) (v w : GenFlagAlg R σ) :
    φ.evalAlg (v + w) = φ.evalAlg v + φ.evalAlg w := by
  simp only [evalAlg, genEvalAlgOf]
  rw [Finsupp.sum_add_index (by simp) (by intros; ring)]

/-- An element f ∈ 𝓛^σ is **positive** if φ(f) ≥ 0 for all generic limit functionals. -/
def GenFlagAlg.isPositive {R : RelUniverse} {σ : GenFlagType R}
    (v : GenFlagAlg R σ) (𝒢 : GenGraphClass R) (Δ : GenGraphParam R) : Prop :=
  ∀ φ : GenLimitFunctional R σ 𝒢 Δ, 0 ≤ φ.evalAlg v

/-- The **generic semantic cone**: the convex cone of positive elements. -/
def GenSemanticCone (R : RelUniverse) (σ : GenFlagType R)
    (𝒢 : GenGraphClass R) (Δ : GenGraphParam R) : Set (GenFlagAlg R σ) :=
  {v | v.isPositive 𝒢 Δ}

/-- **Squares are positive**: φ(f²) = φ(f)² ≥ 0 for all φ, when f has local support. -/
theorem genSquare_in_cone {R : RelUniverse} {σ : GenFlagType R}
    {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    (v : GenFlagAlg R σ) (hv : ∀ cls ∈ v.support, GenIsLocalFlag σ cls.out 𝒢 Δ) :
    (v.mul v).isPositive 𝒢 Δ := by
  intro φ
  change 0 ≤ genEvalAlgOf φ.eval (v.mul v)
  rw [φ.is_homomorphism v v hv hv]
  exact mul_self_nonneg _

/-- The semantic cone is closed under addition. -/
theorem genIsPositive_add {R : RelUniverse} {σ : GenFlagType R}
    {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    {v w : GenFlagAlg R σ} (hv : v.isPositive 𝒢 Δ) (hw : w.isPositive 𝒢 Δ) :
    (v + w).isPositive 𝒢 Δ := by
  intro φ
  rw [φ.evalAlg_add]
  exact add_nonneg (hv φ) (hw φ)

/-- The semantic cone is closed under nonneg scalar multiplication. -/
theorem genIsPositive_nonneg_smul {R : RelUniverse} {σ : GenFlagType R}
    {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    {v : GenFlagAlg R σ} (c : ℝ) (hc : 0 ≤ c) (hv : v.isPositive 𝒢 Δ) :
    (c • v).isPositive 𝒢 Δ := by
  intro φ
  rw [φ.evalAlg_smul]
  exact mul_nonneg hc (hv φ)

/-! ## Phase 4h: Generic Averaging Operator

Generalizes the SimpleGraph averaging operator (§2.4, lines 6497-7980) to
arbitrary `RelUniverse`. The averaging operator ⟦·⟧ : 𝓛^σ → 𝓛^∅ maps
σ-typed flag algebra elements to ∅-typed elements by summing over all
type embeddings, weighted by the normalisation factor. -/

/-- The **generic normalisation factor** q_σ(F): the proportion of injections
    θ : Fin σ.size ↪ Fin F.size that are structure-preserving (R.comap θ F.str = σ.str).
    Generalizes `normalisationFactor` to arbitrary `RelUniverse`. -/
noncomputable def genNormalisationFactor {R : RelUniverse} (σ : GenFlagType R)
    (F : GenFlag R σ) : ℝ :=
  (genFlagAutCount R (GenFlagType.empty R) F.forget : ℝ) /
    ((genFlagAutCount R σ F : ℝ) * (Nat.descFactorial F.size σ.size : ℝ))

/-- The generic normalisation factor is nonneg. -/
theorem genNormalisationFactor_nonneg {R : RelUniverse} (σ : GenFlagType R)
    (F : GenFlag R σ) : 0 ≤ genNormalisationFactor σ F :=
  div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Orbit-stabilizer bound: the number of structure-preserving permutations of a flag
    (ignoring labels) is at most the number of label-fixing automorphisms times the
    number of injections from the label set. This is the Nat-level inequality underlying
    `genNormalisationFactor_le_one`. -/
private theorem genAutCount_le_mul_descFactorial {R : RelUniverse} (σ : GenFlagType R)
    (F : GenFlag R σ) :
    genFlagAutCount R (GenFlagType.empty R) F.forget ≤
      genFlagAutCount R σ F * Nat.descFactorial F.size σ.size := by
  unfold genFlagAutCount genInducedCount
  -- Rewrite descFactorial as card of embeddings
  rw [show Nat.descFactorial F.size σ.size =
      Fintype.card (Fin σ.size ↪ Fin F.size) by
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]]
  -- Define π : Aut(∅, F.forget) → (Fin σ.size ↪ Fin F.size) by π(φ) = φ ∘ F.embedding
  let π : GenInducedEmbedding R (GenFlagType.empty R) F.forget F.forget →
      (Fin σ.size ↪ Fin F.size) :=
    fun φ => ⟨φ.toFun ∘ F.embedding, φ.injective.comp F.embedding.injective⟩
  -- Use pigeonhole: |source| ≤ (max fiber) × |target|
  rw [← Finset.card_univ (α := GenInducedEmbedding R (GenFlagType.empty R) F.forget F.forget),
      ← Finset.card_univ (α := Fin σ.size ↪ Fin F.size)]
  apply Finset.card_le_mul_card_image_of_maps_to (f := π)
    (fun _ _ => Finset.mem_univ _)
  -- Bound each fiber by |Aut(σ, F)|
  intro b _
  rw [← Finset.card_univ (α := GenInducedEmbedding R σ F F)]
  -- If the fiber is empty, trivial
  by_cases hfib : (Finset.univ.filter (fun a => π a = b)).Nonempty
  · -- Fix φ₀ in the fiber; use φ ↦ φ₀⁻¹ ∘ φ to inject fiber into Aut(σ, F)
    obtain ⟨φ₀, hφ₀mem⟩ := hfib
    have hφ₀fib := (Finset.mem_filter.mp hφ₀mem).2
    -- φ₀.toFun is bijective (injective endo of Fin n)
    have hφ₀_bij : Function.Bijective φ₀.toFun :=
      Finite.injective_iff_bijective.mp φ₀.injective
    let φ₀e : Equiv.Perm (Fin F.size) := Equiv.ofBijective φ₀.toFun hφ₀_bij
    -- The map φ ↦ φ₀⁻¹ ∘ φ sends fiber elements to Aut(σ, F)
    -- φ₀.toFun ∘ φ₀⁻¹ = id
    have hφ₀_right_inv : φ₀.toFun ∘ ⇑φ₀e.symm = id :=
      funext (fun x => Equiv.ofBijective_apply_symm_apply _ _ x)
    -- R.comap φ₀⁻¹ preserves F.forget.str
    have hφ₀inv_str : R.comap (⇑φ₀e.symm) F.forget.str = F.forget.str := by
      have h := φ₀.isInduced  -- R.comap φ₀.toFun F.forget.str = F.forget.str
      calc R.comap (⇑φ₀e.symm) F.forget.str
          = R.comap (⇑φ₀e.symm) (R.comap φ₀.toFun F.forget.str) := by rw [h]
        _ = R.comap (φ₀.toFun ∘ ⇑φ₀e.symm) F.forget.str := (R.comap_comp _ _ _).symm
        _ = R.comap id F.forget.str := by rw [hφ₀_right_inv]
        _ = F.forget.str := R.comap_id _
    have inv_comp_str : ∀ (φ : GenInducedEmbedding R (GenFlagType.empty R) F.forget F.forget),
        R.comap (⇑φ₀e.symm ∘ φ.toFun) F.str = F.str := by
      intro φ
      change R.comap (⇑φ₀e.symm ∘ φ.toFun) F.forget.str = F.forget.str
      have := R.comap_comp φ.toFun (⇑φ₀e.symm) F.forget.str
      rw [this, hφ₀inv_str, φ.isInduced]
    have inv_comp_compat : ∀ (φ : GenInducedEmbedding R (GenFlagType.empty R) F.forget F.forget),
        π φ = π φ₀ →
        ∀ i : Fin σ.size, (φ₀e.symm ∘ φ.toFun) (F.embedding i) = F.embedding i := by
      intro φ hπ i
      -- hπ says φ.toFun ∘ F.embedding = φ₀.toFun ∘ F.embedding (as embeddings)
      have hπ_eq : ∀ j : Fin σ.size, φ.toFun (F.embedding j) = φ₀.toFun (F.embedding j) := by
        intro j
        exact DFunLike.ext_iff.mp hπ j
      change φ₀e.symm (φ.toFun (F.embedding i)) = F.embedding i
      rw [hπ_eq i]
      exact Equiv.ofBijective_symm_apply_apply _ _ _
    -- Build the injection from fiber into Aut(σ, F)
    -- First, use Fintype.card on the filter subtype
    rw [show (Finset.univ.filter (fun a => π a = b)).card =
        Fintype.card (Finset.univ.filter (fun a => π a = b)) from
      (Fintype.card_coe _).symm]
    apply Fintype.card_le_of_injective
      (fun (⟨φ, hφ⟩ : (Finset.univ.filter (fun a => π a = b) : Finset _)) =>
        have hφfib := (Finset.mem_filter.mp hφ).2
        (⟨φ₀e.symm ∘ φ.toFun,
         φ₀e.symm.injective.comp φ.injective,
         inv_comp_str φ,
         inv_comp_compat φ (hφfib.trans hφ₀fib.symm)⟩ :
          GenInducedEmbedding R σ F F))
    -- Injectivity: if φ₀⁻¹ ∘ φ = φ₀⁻¹ ∘ ψ then φ = ψ
    intro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ heq
    simp only [GenInducedEmbedding.mk.injEq] at heq
    apply Subtype.ext
    cases φ; cases ψ
    simp only [GenInducedEmbedding.mk.injEq]
    exact φ₀e.symm.injective.comp_left heq
  · rw [Finset.not_nonempty_iff_eq_empty.mp hfib, Finset.card_empty]
    exact Nat.zero_le _

/-- The generic normalisation factor is at most 1. -/
theorem genNormalisationFactor_le_one {R : RelUniverse} (σ : GenFlagType R)
    (F : GenFlag R σ) : genNormalisationFactor σ F ≤ 1 := by
  unfold genNormalisationFactor
  by_cases h : (genFlagAutCount R σ F : ℝ) * (Nat.descFactorial F.size σ.size : ℝ) = 0
  · simp [h]
  · rw [div_le_one (lt_of_le_of_ne (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Ne.symm h))]
    rw [← Nat.cast_mul, Nat.cast_le]
    exact genAutCount_le_mul_descFactorial σ F

/-- The generic normalisation factor respects flag isomorphism. -/
theorem genNormalisationFactor_flagIso {R : RelUniverse} {σ : GenFlagType R}
    {F₁ F₂ : GenFlag R σ} (hiso : GenFlagIso σ F₁ F₂) :
    genNormalisationFactor σ F₁ = genNormalisationFactor σ F₂ := by
  unfold genNormalisationFactor
  have hsize := genFlagIso_size_eq hiso
  have haut_σ := genFlagAutCount_flagIso hiso
  obtain ⟨φ, hstr, hcompat⟩ := hiso
  have haut_e : genFlagAutCount R (GenFlagType.empty R) F₁.forget =
      genFlagAutCount R (GenFlagType.empty R) F₂.forget :=
    genFlagAutCount_flagIso ⟨φ, hstr, fun i => Fin.elim0 i⟩
  simp only [hsize, haut_σ, haut_e]

/-- The **generic averaging operator** on a single σ-flag: ⟦F⟧ = q_σ(F) · ↓F.
    Maps a σ-flag to an ∅-flag algebra element. -/
noncomputable def genAveraging {R : RelUniverse} (σ : GenFlagType R)
    (F : GenFlag R σ) : GenFlagAlg R (GenFlagType.empty R) :=
  genNormalisationFactor σ F • GenFlagAlg.single F.forget

/-- Class-level generic averaging (well-defined on isomorphism classes). -/
noncomputable def genClassAveraging {R : RelUniverse} (σ : GenFlagType R)
    (cls : GenFlagClass R σ) : GenFlagAlg R (GenFlagType.empty R) :=
  genAveraging σ cls.out

/-- Linear extension of the generic averaging operator: ⟦·⟧ : 𝓛^σ → 𝓛^∅. -/
noncomputable def genAveragingAlg {R : RelUniverse} (σ : GenFlagType R)
    (v : GenFlagAlg R σ) : GenFlagAlg R (GenFlagType.empty R) :=
  v.sum (fun cls c => c • genClassAveraging σ cls)

/-- `genAveragingAlg` distributes over addition. -/
theorem genAveragingAlg_add {R : RelUniverse} {σ : GenFlagType R}
    (v w : GenFlagAlg R σ) :
    genAveragingAlg σ (v + w) = genAveragingAlg σ v + genAveragingAlg σ w := by
  simp only [genAveragingAlg]
  exact Finsupp.sum_add_index
    (by intro cls _; exact zero_smul ℝ (genClassAveraging σ cls))
    (by intro cls _ a b; exact add_smul a b (genClassAveraging σ cls))

/-- `genAveragingAlg` distributes over scalar multiplication. -/
theorem genAveragingAlg_smul {R : RelUniverse} {σ : GenFlagType R}
    (c : ℝ) (v : GenFlagAlg R σ) :
    genAveragingAlg σ (c • v) = c • genAveragingAlg σ v := by
  simp only [genAveragingAlg]
  rw [Finsupp.sum_smul_index (by intro cls; exact zero_smul ℝ (genClassAveraging σ cls))]
  simp only [Finsupp.sum, Finset.smul_sum]
  congr 1; ext cls
  rw [mul_smul]

/-- A type σ is **locally valid** for 𝒢/Δ if every local σ-flag forgets to a
    local ∅-flag. Generalizes `IsLocalType`. -/
def GenIsLocalType {R : RelUniverse} (σ : GenFlagType R)
    (𝒢 : GenGraphClass R) (Δ : GenGraphParam R) : Prop :=
  ∀ F : GenFlag R σ, GenIsLocalFlag σ F 𝒢 Δ →
    GenIsLocalFlag (GenFlagType.empty R) F.forget 𝒢 Δ

/-- Two ∅-type GenFlags with equal size and str are equal (embedding is Fin.elim0). -/
theorem GenFlag.empty_ext {R : RelUniverse}
    (F G : GenFlag R (GenFlagType.empty R))
    (hs : F.size = G.size) (hstr : F.str = hs ▸ G.str) :
    F = G := by
  cases F with | mk s₁ str₁ emb₁ ind₁ hsz₁ =>
  cases G with | mk s₂ str₂ emb₂ ind₂ hsz₂ =>
  dsimp at hs; subst hs; dsimp at hstr; subst hstr
  congr 1; ext i; exact Fin.elim0 i

/-! ## Phase 4i: Generic σ-Embedding Infrastructure -/

/-- A **generic σ-embedding into G**: an injection θ : Fin σ.size ↪ Fin G.size
    that is structure-preserving. Generalizes `SigmaEmbIntoGraph`. -/
structure GenSigmaEmb' {R : RelUniverse} (σ : GenFlagType R)
    (G : GenFlag R (GenFlagType.empty R)) where
  emb : Fin σ.size ↪ Fin G.size
  isCompat : R.comap emb.toFun G.str = σ.str

/-- Construct a σ-flag from a graph G and a generic σ-embedding θ. -/
def genSigmaFlagOfEmb' {R : RelUniverse} {σ : GenFlagType R}
    {G : GenFlag R (GenFlagType.empty R)}
    (θ : GenSigmaEmb' σ G) : GenFlag R σ where
  size := G.size
  str := G.str
  embedding := θ.emb
  isInduced := θ.isCompat
  hsize := by
    have h := Fintype.card_le_of_injective θ.emb.toFun θ.emb.injective
    simp [Fintype.card_fin] at h; exact h

noncomputable instance {R : RelUniverse} {σ : GenFlagType R}
    {G : GenFlag R (GenFlagType.empty R)} :
    Fintype (GenSigmaEmb' σ G) :=
  Fintype.ofInjective (fun e => e.emb) (fun a b h => by cases a; cases b; congr)

/-- `(genSigmaFlagOfEmb' θ).forget = G` for σ-embeddings into G. -/
theorem genSigmaFlagOfEmb'_forget {R : RelUniverse} {σ : GenFlagType R}
    {G : GenFlag R (GenFlagType.empty R)} (θ : GenSigmaEmb' σ G) :
    (genSigmaFlagOfEmb' θ).forget = G :=
  GenFlag.empty_ext _ _ rfl rfl

/-- Extract a σ-embedding from an ∅-embedding of F.forget into G. -/
private def genExtractSigmaEmb {R : RelUniverse} {σ : GenFlagType R}
    {F : GenFlag R σ} {G : GenFlag R (GenFlagType.empty R)}
    (e : GenInducedEmbedding R (GenFlagType.empty R) F.forget G) :
    GenSigmaEmb' σ G where
  emb := F.embedding.trans ⟨e.toFun, e.injective⟩
  isCompat := by
    change R.comap (e.toFun ∘ F.embedding) G.str = σ.str
    rw [R.comap_comp]; exact F.isInduced ▸ e.isInduced ▸ rfl

/-- Lift an ∅-embedding of F.forget to a σ-embedding of F into (G, θ). -/
private def genLiftToSigmaEmb {R : RelUniverse} {σ : GenFlagType R}
    {F : GenFlag R σ} {G : GenFlag R (GenFlagType.empty R)}
    (e : GenInducedEmbedding R (GenFlagType.empty R) F.forget G) :
    GenInducedEmbedding R σ F (genSigmaFlagOfEmb' (genExtractSigmaEmb e)) where
  toFun := e.toFun
  injective := e.injective
  isInduced := e.isInduced
  compat := fun _i => rfl

/-- Forget σ-structure: a σ-embedding of F into (G,θ) gives an ∅-embedding of F.forget into G. -/
private def genReverseSigmaEmb {R : RelUniverse} {σ : GenFlagType R}
    {F : GenFlag R σ} {G : GenFlag R (GenFlagType.empty R)}
    (θ : GenSigmaEmb' σ G) (e : GenInducedEmbedding R σ F (genSigmaFlagOfEmb' θ)) :
    GenInducedEmbedding R (GenFlagType.empty R) F.forget G where
  toFun := e.toFun
  injective := e.injective
  isInduced := e.isInduced
  compat := fun i => Fin.elim0 i

/-- **Generic counting equality**: c(↓F; G) = Σ_θ c(F; (G,θ)).
    The number of ∅-embeddings of F.forget into G equals the sum over σ-embeddings θ
    of the number of σ-embeddings of F into (G,θ). -/
theorem genForget_count_eq_sigma_sum {R : RelUniverse} (σ : GenFlagType R)
    (F : GenFlag R σ) (G : GenFlag R (GenFlagType.empty R)) :
    genInducedCount R (GenFlagType.empty R) F.forget G =
      Finset.univ.sum (fun θ : GenSigmaEmb' σ G =>
        genInducedCount R σ F (genSigmaFlagOfEmb' θ)) := by
  unfold genInducedCount; rw [← Fintype.card_sigma]
  apply le_antisymm
  · -- Forward: each ∅-embedding decomposes into (θ, σ-embedding)
    apply Fintype.card_le_of_injective
      (fun e => ⟨genExtractSigmaEmb e, genLiftToSigmaEmb e⟩)
    intro e₁ e₂ h
    let proj : (Σ θ : GenSigmaEmb' σ G,
        GenInducedEmbedding R σ F (genSigmaFlagOfEmb' θ)) →
        (Fin F.size → Fin G.size) := fun p => p.2.toFun
    have : e₁.toFun = e₂.toFun := congr_arg proj h
    cases e₁; cases e₂; congr
  · -- Reverse: (θ, σ-embedding) gives an ∅-embedding
    apply Fintype.card_le_of_injective
      (fun p => genReverseSigmaEmb p.1 p.2)
    intro ⟨θ₁, e₁⟩ ⟨θ₂, e₂⟩ h
    have h_toFun : e₁.toFun = e₂.toFun := congrArg GenInducedEmbedding.toFun h
    have h_emb : θ₁.emb = θ₂.emb := by
      ext i; have h1 := e₁.compat i; have h2 := e₂.compat i
      simp only [genSigmaFlagOfEmb'] at h1 h2; rw [← h1, ← h2, h_toFun]
    have h_θ : θ₁ = θ₂ := by cases θ₁; cases θ₂; congr
    subst h_θ; congr; cases e₁; cases e₂; congr

/-- IC(∅, σ.toFlag.forget, G) = |GenSigmaEmb' σ G| (same data). -/
private theorem genInducedCount_toFlag_forget_eq_sigmaEmb {R : RelUniverse}
    (σ : GenFlagType R) (G : GenFlag R (GenFlagType.empty R)) :
    genInducedCount R (GenFlagType.empty R) σ.toFlag.forget G =
      Fintype.card (GenSigmaEmb' σ G) := by
  unfold genInducedCount
  apply Fintype.card_congr
  exact {
    toFun := fun e => ⟨⟨e.toFun, e.injective⟩, e.isInduced⟩
    invFun := fun θ => ⟨θ.emb, θ.emb.injective, θ.isCompat, fun i => Fin.elim0 i⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }

/-- **Generic averaging density identity** (thesis Lemma 2.7, generic version):
    Relates ∅-density of F.forget to σ-level expected density with correction factor.
    Uses orbit-stabilizer normalisation: q(F) = Aut(∅,↓F) / (Aut(σ,F) · descFact). -/
theorem genAveraging_density_identity {R : RelUniverse} (σ : GenFlagType R)
    (F : GenFlag R σ) (G : GenFlag R (GenFlagType.empty R))
    (Δ : GenGraphParam R) :
    genNormalisationFactor σ F *
      genUnlabelledDensity R (GenFlagType.empty R) F.forget G Δ =
    genNormalisationFactor σ σ.toFlag *
      genUnlabelledDensity R (GenFlagType.empty R) σ.toFlag.forget G Δ *
      ((∑ θ : GenSigmaEmb' σ G,
          genUnlabelledDensity R σ F (genSigmaFlagOfEmb' θ) Δ) /
        (Fintype.card (GenSigmaEmb' σ G) : ℝ)) *
      ((Nat.choose (Δ G.forget) (F.size - σ.size) : ℝ) /
        (Nat.choose (Δ G.forget - σ.size) (F.size - σ.size) : ℝ)) := by
  set s := σ.size; set f := F.size - σ.size; set n := Δ G.forget
  set IC := (genInducedCount R (GenFlagType.empty R) F.forget G : ℝ)
  set Aσ := (genFlagAutCount R σ F : ℝ)
  set Ae := (genFlagAutCount R (GenFlagType.empty R) F.forget : ℝ)
  set Aes := (genFlagAutCount R (GenFlagType.empty R) σ.toFlag.forget : ℝ)
  set Θ := (Fintype.card (GenSigmaEmb' σ G) : ℝ)
  unfold genUnlabelledDensity
  -- Simplify sum: Δ(G_θ.forget) = n for all θ, then factor out C(n,f)*Aσ
  have hsum : (∑ θ : GenSigmaEmb' σ G,
      (genInducedCount R σ F (genSigmaFlagOfEmb' θ) : ℝ) /
        ((Nat.choose (Δ (genSigmaFlagOfEmb' θ).forget) f : ℝ) *
         (genFlagAutCount R σ F : ℝ))) =
      (∑ θ : GenSigmaEmb' σ G,
        (genInducedCount R σ F (genSigmaFlagOfEmb' θ) : ℝ)) /
        ((Nat.choose n f : ℝ) * Aσ) := by
    have hΔ : ∀ θ : GenSigmaEmb' σ G, Δ (genSigmaFlagOfEmb' θ).forget = n := fun θ => by
      rw [genSigmaFlagOfEmb'_forget, ← GenFlag.empty_ext G.forget G rfl rfl]
    simp_rw [hΔ]; simp only [Finset.sum_div]; rfl
  have havg := genForget_count_eq_sigma_sum σ F G
  rw [hsum, show (∑ θ : GenSigmaEmb' σ G,
      (genInducedCount R σ F (genSigmaFlagOfEmb' θ) : ℝ)) = IC from by
    rw [← Nat.cast_sum]; exact congrArg Nat.cast havg.symm]
  rw [genInducedCount_toFlag_forget_eq_sigmaEmb σ G]
  have hvand : (Nat.choose n F.size : ℝ) * (Nat.choose F.size s : ℝ) =
      (Nat.choose n s : ℝ) * (Nat.choose (n - s) f : ℝ) :=
    mod_cast Nat.choose_mul F.hsize
  have hdesc : (Nat.descFactorial F.size s : ℝ) =
      (s.factorial : ℝ) * (Nat.choose F.size s : ℝ) :=
    mod_cast Nat.descFactorial_eq_factorial_mul_choose F.size s
  have hdesc_σ : (Nat.descFactorial s s : ℝ) = (s.factorial : ℝ) :=
    mod_cast Nat.descFactorial_self s
  have hAσ_pos : (0 : ℝ) < Aσ := Nat.cast_pos.mpr (genFlagAutCount_pos σ F)
  have hAe_pos : (0 : ℝ) < Ae :=
    Nat.cast_pos.mpr (genFlagAutCount_pos (GenFlagType.empty R) F.forget)
  have hAes_pos : (0 : ℝ) < Aes :=
    Nat.cast_pos.mpr (genFlagAutCount_pos (GenFlagType.empty R) σ.toFlag.forget)
  simp only [genNormalisationFactor, genFlagAutCount_toFlag, Nat.cast_one, one_mul]
  change Ae / (Aσ * ↑(F.size.descFactorial s)) * (IC / (↑(n.choose F.size) * Ae)) =
    Aes / ↑(Nat.descFactorial s s) * (Θ / (↑(n.choose s) * Aes)) *
    (IC / (↑(n.choose f) * Aσ) / Θ) * (↑(n.choose f) / ↑((n - s).choose f))
  rw [hdesc_σ, hdesc]
  -- Abstract to pure ℝ algebra and solve by case splitting + field_simp
  suffices ∀ (ae aσ aes ic θ sf cFs cnF cns cnf cnsf : ℝ),
      0 < ae → 0 < aσ → 0 < aes →
      cnF * cFs = cns * cnsf → (cnf = 0 → cnF = 0) → (θ = 0 → ic = 0) →
      ae / (aσ * (sf * cFs)) * (ic / (cnF * ae)) =
        aes / sf * (θ / (cns * aes)) * (ic / (cnf * aσ) / θ) * (cnf / cnsf) by
    exact this Ae Aσ Aes IC Θ _ _ _ _ _ _ hAe_pos hAσ_pos hAes_pos hvand
      (fun hcnf => Nat.cast_eq_zero.mpr (Nat.choose_eq_zero_iff.mpr
        (lt_of_lt_of_le (Nat.choose_eq_zero_iff.mp (Nat.cast_eq_zero.mp hcnf))
          (Nat.sub_le F.size s))))
      (fun hθ => Nat.cast_eq_zero.mpr
        (havg ▸ Finset.sum_eq_zero fun θ _ =>
          IsEmpty.elim (Fintype.card_eq_zero_iff.mp (Nat.cast_eq_zero.mp hθ)) θ))
  intro ae aσ aes ic θ sf cFs cnF cns cnf cnsf hae haσ haes hvand' hcnf_imp hθ_imp
  by_cases hcFs : cFs = 0
  · simp only [hcFs, mul_zero] at hvand' ⊢
    rcases mul_eq_zero.mp hvand'.symm with hcns | hcnsf
    · simp [hcns]
    · simp [hcnsf]
  · by_cases hsf : sf = 0
    · simp [hsf]
    · by_cases hcnF : cnF = 0
      · have : cns * cnsf = 0 := by rw [← hvand']; simp [hcnF]
        rcases mul_eq_zero.mp this with hcns | hcnsf <;> simp [*]
      · by_cases hcns : cns = 0
        · exact absurd
            ((mul_eq_zero.mp (hvand' ▸ mul_eq_zero_of_left hcns _)).resolve_left hcnF) hcFs
        · by_cases hcnsf : cnsf = 0
          · exact absurd
              ((mul_eq_zero.mp (hvand' ▸ mul_eq_zero_of_right _ hcnsf)).resolve_left hcnF) hcFs
          · by_cases hcnf : cnf = 0
            · simp [hcnf, hcnf_imp hcnf]
            · by_cases hθ : θ = 0
              · simp [hθ, hθ_imp hθ]
              · field_simp [ne_of_gt hae, ne_of_gt haσ, ne_of_gt haes,
                  hsf, hcFs, hcnF, hcns, hcnsf, hcnf, hθ]
                linear_combination -ic * hvand'

/-- **Generic bounded density forget** (Thesis Lem 2.6, ∅ case):
    If F has bounded density at σ and σ.toFlag.forget has bounded density at ∅,
    then F.forget has bounded density at ∅.
    Port of `bounded_density_forget` from SimpleGraph to generic RelUniverse. -/
theorem genBounded_density_forget {R : RelUniverse} (σ : GenFlagType R)
    (F : GenFlag R σ) (𝒢 : GenGraphClass R) (Δ : GenGraphParam R)
    (hbd : GenIsBoundedDensity σ F 𝒢 Δ)
    (hσ_bd : GenIsBoundedDensity (GenFlagType.empty R) σ.toFlag.forget 𝒢 Δ) :
    GenIsBoundedDensity (GenFlagType.empty R) F.forget 𝒢 Δ := by
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := hbd
  obtain ⟨C₂, hC₂_nn, hC₂⟩ := hσ_bd
  set K := (Nat.choose F.size σ.size : ℝ) ^ 2
  refine ⟨C₁ * C₂ * K, mul_nonneg (mul_nonneg hC₁_nn hC₂_nn)
    (pow_nonneg (Nat.cast_nonneg _) 2), fun G hG => ?_⟩
  unfold genLocalDensity
  have hFS : F.forget.size - (GenFlagType.empty R).size = F.size := by
    change F.size - 0 = F.size; omega
  rw [hFS]
  set D := Δ G.forget
  set denom := Nat.choose D F.size
  by_cases hdenom_zero : denom = 0
  · rw [hdenom_zero, Nat.cast_zero, div_zero]
    exact mul_nonneg (mul_nonneg hC₁_nn hC₂_nn) (pow_nonneg (Nat.cast_nonneg _) 2)
  · have hdenom_pos : 0 < (denom : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hdenom_zero)
    have hD_ge_F : F.size ≤ D := by
      by_contra h; push_neg at h; exact hdenom_zero (Nat.choose_eq_zero_of_lt h)
    have hD_ge_σ : σ.size ≤ D := le_trans F.hsize hD_ge_F
    set denom_σ := Nat.choose D σ.size
    set denom_F := Nat.choose D (F.size - σ.size)
    have hdenom_σ_pos : 0 < (denom_σ : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hD_ge_σ)
    have hdenom_F_pos : 0 < (denom_F : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos (le_trans (Nat.sub_le F.size σ.size) hD_ge_F))
    -- Step 1: σ-decomposition of ∅-count
    have h_decomp := genForget_count_eq_sigma_sum σ F G
    -- Step 2: bound each σ-level count
    have h_per_theta : ∀ θ : GenSigmaEmb' σ G,
        (genInducedCount R σ F (genSigmaFlagOfEmb' θ) : ℝ) ≤ C₁ * (denom_F : ℝ) := by
      intro θ
      have hGG : 𝒢 G := (GenFlag.empty_ext G.forget G rfl rfl) ▸ hG
      have hG_θ : 𝒢 (genSigmaFlagOfEmb' θ).forget :=
        (genSigmaFlagOfEmb'_forget θ).symm ▸ hGG
      have h_le := hC₁ (genSigmaFlagOfEmb' θ) hG_θ
      unfold genLocalDensity at h_le
      rw [show Δ (genSigmaFlagOfEmb' θ).forget = D from by
        change Δ (genSigmaFlagOfEmb' θ).forget = Δ G.forget; congr 1,
        div_le_iff₀ hdenom_F_pos] at h_le
      exact h_le
    -- Step 3: sum over θ
    have h_sum_bound :
        (Finset.univ.sum (fun θ : GenSigmaEmb' σ G =>
          (genInducedCount R σ F (genSigmaFlagOfEmb' θ) : ℝ))) ≤
        (Fintype.card (GenSigmaEmb' σ G) : ℝ) * C₁ * (denom_F : ℝ) := by
      calc _ ≤ Finset.univ.sum (fun _ : GenSigmaEmb' σ G => C₁ * (denom_F : ℝ)) :=
              Finset.sum_le_sum (fun θ _ => h_per_theta θ)
        _ = _ := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
    -- Step 4: bound σ-embedding count
    have h_sigma_count : (Fintype.card (GenSigmaEmb' σ G) : ℝ) ≤ C₂ * (denom_σ : ℝ) := by
      have h_le := hC₂ G hG
      unfold genLocalDensity at h_le
      rw [show σ.toFlag.forget.size - (GenFlagType.empty R).size = σ.size from by
        change σ.size - 0 = σ.size; omega] at h_le
      rw [show Fintype.card (GenSigmaEmb' σ G) =
        genInducedCount R (GenFlagType.empty R) σ.toFlag.forget G from
        (genInducedCount_toFlag_forget_eq_sigmaEmb σ G).symm]
      exact_mod_cast (div_le_iff₀ hdenom_σ_pos).mp h_le
    -- Step 5: combine + Vandermonde
    have h_count : (genInducedCount R (GenFlagType.empty R) F.forget G : ℝ) ≤
        C₁ * C₂ * (denom_σ : ℝ) * (denom_F : ℝ) := by
      calc (genInducedCount R (GenFlagType.empty R) F.forget G : ℝ)
          ≤ _ := by exact_mod_cast le_of_eq h_decomp
        _ ≤ (Fintype.card (GenSigmaEmb' σ G) : ℝ) * C₁ * (denom_F : ℝ) := h_sum_bound
        _ ≤ C₂ * (denom_σ : ℝ) * C₁ * (denom_F : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right h_sigma_count hC₁_nn) (le_of_lt hdenom_F_pos)
        _ = C₁ * C₂ * (denom_σ : ℝ) * (denom_F : ℝ) := by ring
    rw [div_le_iff₀ hdenom_pos]
    have h_vandermonde : denom_σ * denom_F ≤ Nat.choose F.size σ.size ^ 2 * denom := by
      have hle : σ.size + (F.size - σ.size) ≤ D := by
        have := F.hsize; omega
      have := choose_mul_choose_le σ.size (F.size - σ.size) D hle
      rwa [show σ.size + (F.size - σ.size) = F.size from by have := F.hsize; omega] at this
    calc (genInducedCount R (GenFlagType.empty R) F.forget G : ℝ)
        ≤ C₁ * C₂ * ((denom_σ : ℝ) * (denom_F : ℝ)) := by linarith
      _ ≤ C₁ * C₂ * ((Nat.choose F.size σ.size : ℝ) ^ 2 * (denom : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast h_vandermonde)
            (mul_nonneg hC₁_nn hC₂_nn)
      _ = C₁ * C₂ * K * (denom : ℝ) := by ring

/-- Expected eval density of v over σ-embeddings into G. -/
noncomputable def genExpectedEvalDensity' {R : RelUniverse} (σ : GenFlagType R)
    (v : GenFlagAlg R σ) (G : GenFlag R (GenFlagType.empty R))
    (Δ : GenGraphParam R) : ℝ :=
  let N := Fintype.card (GenSigmaEmb' σ G)
  if N = 0 then 0
  else (∑ θ : GenSigmaEmb' σ G,
    genEvalAlgOf (fun F => genUnlabelledDensity R σ F (genSigmaFlagOfEmb' θ) Δ) v) / N

set_option maxHeartbeats 3200000 in
/-- **Averaging eventually negative**: If ψ.evalAlg(⟦v⟧) < 0, eventually the
    average σ-level eval density of v is ≤ c < 0. Combines density identity
    with correction factor convergence. -/
theorem genAveraging_eventually_neg' {R : RelUniverse} {σ : GenFlagType R}
    {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    (hσ : GenIsLocalType σ 𝒢 Δ)
    (v : GenFlagAlg R σ)
    (hlocal : ∀ cls ∈ v.support, GenIsLocalFlag σ cls.out 𝒢 Δ)
    (ψ : GenLimitFunctional R (GenFlagType.empty R) 𝒢 Δ)
    (hψ : ψ.evalAlg (genAveragingAlg σ v) < 0) :
    ∃ (c : ℝ) (_ : c < 0) (N₀ : ℕ), ∀ k, N₀ ≤ k →
      genExpectedEvalDensity' σ v (ψ.seq.seq (ψ.sub k)) Δ ≤ c := by
  let G : ℕ → GenFlag R (GenFlagType.empty R) := fun k => ψ.seq.seq (ψ.sub k)
  set L := ψ.evalAlg (genAveragingAlg σ v) with hL_def
  have hforget_local : ∀ cls ∈ v.support, GenIsLocalFlag (GenFlagType.empty R) cls.out.forget 𝒢 Δ :=
    fun cls hcls => hσ cls.out (hlocal cls hcls)
  have hσ_forget_local : GenIsLocalFlag (GenFlagType.empty R) σ.toFlag.forget 𝒢 Δ := by
    apply hσ σ.toFlag
    exact GenIsLocalFlag.intro σ σ.toFlag 𝒢 Δ
      ⟨1, le_of_lt one_pos, fun G _ => by rw [genLocalDensity_type_eq_one]⟩
      (fun ext => absurd (Set.mem_range.mpr ⟨ext.vertex, by simp [GenFlagType.toFlag]⟩) ext.unlabelled)
  set Qlim := genNormalisationFactor σ σ.toFlag * ψ.eval σ.toFlag.forget with hQlim_def
  have hQlim_nonneg : 0 ≤ Qlim :=
    mul_nonneg (genNormalisationFactor_nonneg σ σ.toFlag) (ψ.nonneg_on_flags σ.toFlag.forget)
  -- evalAlg distributes over Finset.sum
  have evalAlg_sum : ∀ (S : Finset (GenFlagClass R σ)) (f : GenFlagClass R σ → GenFlagAlg R (GenFlagType.empty R)),
      ψ.evalAlg (∑ x ∈ S, f x) = ∑ x ∈ S, ψ.evalAlg (f x) := by
    intro S f; induction S using Finset.induction with
    | empty => simp [Finset.sum_empty, GenLimitFunctional.evalAlg, genEvalAlgOf, Finsupp.sum_zero_index]
    | insert _ _ hna ih =>
      rw [Finset.sum_insert hna, ψ.evalAlg_add, ih, Finset.sum_insert hna]
  have hnf_σ_pos : 0 < genNormalisationFactor σ σ.toFlag := by
    unfold genNormalisationFactor
    rw [genFlagAutCount_toFlag, Nat.cast_one, one_mul]
    exact div_pos (Nat.cast_pos.mpr (genFlagAutCount_pos (GenFlagType.empty R) σ.toFlag.forget))
      (Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr (le_refl _)))
  -- Qlim > 0 (otherwise L = 0, contradicting hψ)
  have hQlim_pos : 0 < Qlim := by
    by_contra h; push_neg at h
    have hQlim_zero : Qlim = 0 := le_antisymm h hQlim_nonneg
    have heval_σ_zero : ψ.eval σ.toFlag.forget = 0 :=
      (mul_eq_zero.mp (hQlim_def ▸ hQlim_zero)).resolve_left (ne_of_gt hnf_σ_pos)
    -- Squeeze: normFactor(F) · uD(∅,↓F,G_k) = Q_k · avg · corr → 0 since Q_k → 0
    have heval_forget_zero : ∀ cls ∈ v.support,
        genNormalisationFactor σ cls.out * ψ.eval cls.out.forget = 0 := by
      intro cls hcls
      have hid := fun k => genAveraging_density_identity σ cls.out (G k) Δ
      have htend_lhs : Filter.Tendsto
          (fun k => genNormalisationFactor σ cls.out *
            genUnlabelledDensity R (GenFlagType.empty R) cls.out.forget (G k) Δ)
          Filter.atTop (nhds (genNormalisationFactor σ cls.out * ψ.eval cls.out.forget)) :=
        (ψ.convergence cls.out.forget (hforget_local cls hcls)).const_mul _
      have htend_σ : Filter.Tendsto
          (fun k => genUnlabelledDensity R (GenFlagType.empty R) σ.toFlag.forget (G k) Δ)
          Filter.atTop (nhds 0) := by
        rw [← heval_σ_zero]; exact ψ.convergence σ.toFlag.forget hσ_forget_local
      obtain ⟨C_F, hC_F_nonneg, hC_F_bound⟩ := (hlocal cls hcls).bounded
      have havg_le : ∀ k, (∑ θ : GenSigmaEmb' σ (G k),
          genUnlabelledDensity R σ cls.out (genSigmaFlagOfEmb' θ) Δ) /
          (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ) ≤ C_F := by
        intro k
        by_cases hΘ : (Fintype.card (GenSigmaEmb' σ (G k))) = 0
        · simp [hΘ]; exact hC_F_nonneg
        · have hΘ_pos : (0 : ℝ) < (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ) :=
            Nat.cast_pos.mpr (Nat.pos_of_ne_zero hΘ)
          rw [div_le_iff₀ hΘ_pos]
          calc ∑ θ : GenSigmaEmb' σ (G k),
                genUnlabelledDensity R σ cls.out (genSigmaFlagOfEmb' θ) Δ
              ≤ ∑ _ : GenSigmaEmb' σ (G k), C_F := by
                apply Finset.sum_le_sum; intro θ _
                exact le_trans (genUnlabelledDensity_le_genLocalDensity σ cls.out
                  (genSigmaFlagOfEmb' θ) Δ) (hC_F_bound (genSigmaFlagOfEmb' θ) (ψ.seq_in_class (ψ.sub k)))
            _ = C_F * (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ) := by
                simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
      set f_size := cls.out.size - σ.size
      have htend_corr : Filter.Tendsto
          (fun k => (Nat.choose (Δ (G k).forget) f_size : ℝ) /
            (Nat.choose (Δ (G k).forget - σ.size) f_size : ℝ))
          Filter.atTop (nhds 1) :=
        (choose_ratio_tendsto_one f_size σ.size).comp
          (ψ.seq.increasing.comp ψ.sub_strictMono).tendsto_atTop
      -- Squeeze: f(k) ≤ normFactor(σ) * uD_σ(k) * C_F * corr(k) → 0
      have hle : ∀ k, genNormalisationFactor σ cls.out *
          genUnlabelledDensity R (GenFlagType.empty R) cls.out.forget (G k) Δ ≤
          genNormalisationFactor σ σ.toFlag *
          genUnlabelledDensity R (GenFlagType.empty R) σ.toFlag.forget (G k) Δ *
          C_F *
          ((Nat.choose (Δ (G k).forget) f_size : ℝ) /
            (Nat.choose (Δ (G k).forget - σ.size) f_size : ℝ)) := by
        intro k
        rw [hid k]
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left (havg_le k)
          exact mul_nonneg (genNormalisationFactor_nonneg σ σ.toFlag)
            (genUnlabelledDensity_nonneg (GenFlagType.empty R) σ.toFlag.forget (G k) Δ)
        · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have htend_g : Filter.Tendsto
          (fun k => genNormalisationFactor σ σ.toFlag *
            genUnlabelledDensity R (GenFlagType.empty R) σ.toFlag.forget (G k) Δ *
            C_F *
            ((Nat.choose (Δ (G k).forget) f_size : ℝ) /
              (Nat.choose (Δ (G k).forget - σ.size) f_size : ℝ)))
          Filter.atTop (nhds 0) := by
        rw [show (0 : ℝ) = genNormalisationFactor σ σ.toFlag * 0 * C_F * 1 from by ring]
        exact ((htend_σ.const_mul _).mul tendsto_const_nhds).mul htend_corr
      exact tendsto_nhds_unique htend_lhs
        (squeeze_zero (fun k => mul_nonneg (genNormalisationFactor_nonneg σ cls.out)
          (genUnlabelledDensity_nonneg (GenFlagType.empty R) cls.out.forget (G k) Δ)) hle htend_g)
    -- L = Σ v(cls) · normFactor · ψ.eval(↓F) = Σ v(cls) · 0 = 0, contradicting hψ
    linarith [show L = 0 from by
      rw [hL_def]; show ψ.evalAlg (genAveragingAlg σ v) = 0
      simp only [genAveragingAlg, Finsupp.sum]; rw [evalAlg_sum]
      exact Finset.sum_eq_zero fun cls hcls => by
        rw [ψ.evalAlg_smul]; simp only [genClassAveraging, genAveraging]
        rw [ψ.evalAlg_smul, ψ.evalAlg_single, heval_forget_zero cls hcls, mul_zero]]
  refine ⟨L / (2 * Qlim), div_neg_of_neg_of_pos hψ (mul_pos two_pos hQlim_pos), ?_⟩
  -- Main convergence: show E_θ[v.uED] → L/Qlim < L/(2·Qlim) eventually
  have htend_Q : Filter.Tendsto
      (fun k => genNormalisationFactor σ σ.toFlag *
        genUnlabelledDensity R (GenFlagType.empty R) σ.toFlag.forget (G k) Δ)
      Filter.atTop (nhds Qlim) :=
    (ψ.convergence σ.toFlag.forget hσ_forget_local).const_mul _
  -- S_k = Σ v(cls) * normFactor * uD_forget → L
  have htend_S_L : Filter.Tendsto
      (fun k => ∑ cls ∈ v.support, v cls * (genNormalisationFactor σ cls.out *
        genUnlabelledDensity R (GenFlagType.empty R) cls.out.forget (G k) Δ))
      Filter.atTop (nhds L) := by
    have hS_limit_eq_L :
        ∑ cls ∈ v.support, v cls *
          (genNormalisationFactor σ cls.out * ψ.eval cls.out.forget) = L := by
      rw [hL_def]; simp only [genAveragingAlg, Finsupp.sum]; rw [evalAlg_sum]
      congr 1; ext cls; rw [ψ.evalAlg_smul]; congr 1
      simp only [genClassAveraging, genAveraging]; rw [ψ.evalAlg_smul, ψ.evalAlg_single]
    rw [← hS_limit_eq_L]
    exact tendsto_finset_sum _ fun cls hcls =>
      ((ψ.convergence cls.out.forget (hforget_local cls hcls)).const_mul _).const_mul _
  -- Summed averaging identity at each k
  have hid_sum : ∀ k,
      ∑ cls ∈ v.support, v cls * (genNormalisationFactor σ cls.out *
        genUnlabelledDensity R (GenFlagType.empty R) cls.out.forget (G k) Δ) =
      (genNormalisationFactor σ σ.toFlag *
        genUnlabelledDensity R (GenFlagType.empty R) σ.toFlag.forget (G k) Δ) *
      ∑ cls ∈ v.support, v cls *
        ((∑ θ : GenSigmaEmb' σ (G k),
            genUnlabelledDensity R σ cls.out (genSigmaFlagOfEmb' θ) Δ) /
          (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ)) *
        ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ)) := by
    intro k; rw [Finset.mul_sum]; congr 1; ext cls
    rw [genAveraging_density_identity σ cls.out (G k) Δ]; ring
  -- Expand genEvalAlgOf sum
  have hcuD : ∀ (cls : GenFlagClass R σ) (G' : GenFlag R σ),
      genClassUnlabelledDensity R σ G' Δ cls = genUnlabelledDensity R σ cls.out G' Δ := by
    intro cls G'; rfl
  have huED_expand : ∀ k,
      ∑ θ : GenSigmaEmb' σ (G k),
        genUnlabelledEvalDensity v (genSigmaFlagOfEmb' θ) Δ =
      ∑ cls ∈ v.support, v cls * ∑ θ : GenSigmaEmb' σ (G k),
        genUnlabelledDensity R σ cls.out (genSigmaFlagOfEmb' θ) Δ := by
    intro k
    simp only [genUnlabelledEvalDensity, Finsupp.sum, hcuD]
    rw [Finset.sum_comm]
    congr 1; ext cls; rw [Finset.mul_sum]
  have hEθ_eq : ∀ k,
      (∑ θ : GenSigmaEmb' σ (G k),
        genUnlabelledEvalDensity v (genSigmaFlagOfEmb' θ) Δ) /
        (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ) =
      ∑ cls ∈ v.support, v cls *
        ((∑ θ : GenSigmaEmb' σ (G k),
            genUnlabelledDensity R σ cls.out (genSigmaFlagOfEmb' θ) Δ) /
          (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ)) := by
    intro k; rw [huED_expand k, Finset.sum_div]
    congr 1; ext cls; ring
  have htend_Δ : Filter.Tendsto (fun k => Δ (G k).forget) Filter.atTop Filter.atTop :=
    (ψ.seq.increasing.comp ψ.sub_strictMono).tendsto_atTop
  have htend_corr_cls : ∀ cls ∈ v.support, Filter.Tendsto
      (fun k => (Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
        (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ))
      Filter.atTop (nhds 1) :=
    fun cls _ => (choose_ratio_tendsto_one (cls.out.size - σ.size) σ.size).comp htend_Δ
  have havg_bound : ∀ cls ∈ v.support, ∃ C_cls : ℝ, ∀ k,
      ‖v cls *
        ((∑ θ : GenSigmaEmb' σ (G k),
            genUnlabelledDensity R σ cls.out (genSigmaFlagOfEmb' θ) Δ) /
          (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ))‖ ≤ C_cls := by
    intro cls hcls
    obtain ⟨C_F, hC_F_nonneg, hC_F_bound⟩ := (hlocal cls hcls).bounded
    refine ⟨|v cls| * C_F, fun k => ?_⟩
    rw [Real.norm_eq_abs, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [abs_of_nonneg (div_nonneg (Finset.sum_nonneg (fun θ _ =>
        genUnlabelledDensity_nonneg σ cls.out (genSigmaFlagOfEmb' θ) Δ)) (Nat.cast_nonneg _))]
    by_cases hΘ : (Fintype.card (GenSigmaEmb' σ (G k))) = 0
    · simp [hΘ]; exact hC_F_nonneg
    · have hΘ_pos : (0 : ℝ) < ↑(Fintype.card (GenSigmaEmb' σ (G k))) :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero hΘ)
      rw [div_le_iff₀ hΘ_pos]
      calc ∑ θ : GenSigmaEmb' σ (G k),
              genUnlabelledDensity R σ cls.out (genSigmaFlagOfEmb' θ) Δ
            ≤ ∑ _ : GenSigmaEmb' σ (G k), C_F := by
              apply Finset.sum_le_sum; intro θ _
              exact le_trans (genUnlabelledDensity_le_genLocalDensity σ cls.out
                (genSigmaFlagOfEmb' θ) Δ) (hC_F_bound (genSigmaFlagOfEmb' θ) (ψ.seq_in_class (ψ.sub k)))
          _ = C_F * ↑(Fintype.card (GenSigmaEmb' σ (G k))) := by
              simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  -- Each diff term v(cls) * avg * (corr - 1) → 0
  have hdiff_term_tendsto : ∀ cls ∈ v.support, Filter.Tendsto
      (fun k => v cls *
        ((∑ θ : GenSigmaEmb' σ (G k),
            genUnlabelledDensity R σ cls.out (genSigmaFlagOfEmb' θ) Δ) /
          (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ)) *
        ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1))
      Filter.atTop (nhds 0) := by
    intro cls hcls
    obtain ⟨C_cls, hC_cls⟩ := havg_bound cls hcls
    have hcorr_sub : Filter.Tendsto
        (fun k => (Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1)
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ) = 1 - 1 from by ring]
      exact (htend_corr_cls cls hcls).sub tendsto_const_nhds
    apply squeeze_zero_norm'
      (Filter.Eventually.of_forall (fun (k : ℕ) => show
        ‖v cls *
          ((∑ θ : GenSigmaEmb' σ (G k),
              genUnlabelledDensity R σ cls.out (genSigmaFlagOfEmb' θ) Δ) /
            (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ)) *
          ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
            (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1)‖ ≤
        C_cls * ‖(Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
            (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1‖ from by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC_cls k) (norm_nonneg _)))
    rw [show (0:ℝ) = C_cls * 0 from by ring]
    have htend_norm : Filter.Tendsto
        (fun k => ‖(Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
            (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1‖)
        Filter.atTop (nhds (0 : ℝ)) := by
      rw [show (0 : ℝ) = ‖(0 : ℝ)‖ from by simp]; exact hcorr_sub.norm
    exact htend_norm.const_mul _
  have hdiff_sum_tendsto : Filter.Tendsto
      (fun k => ∑ cls ∈ v.support, v cls *
        ((∑ θ : GenSigmaEmb' σ (G k),
            genUnlabelledDensity R σ cls.out (genSigmaFlagOfEmb' θ) Δ) /
          (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ)) *
        ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1))
      Filter.atTop (nhds 0) := by
    rw [show (0 : ℝ) = ∑ _ ∈ v.support, (0 : ℝ) from by simp]
    exact tendsto_finset_sum _ hdiff_term_tendsto
  have hsum_split : ∀ k,
      ∑ cls ∈ v.support, v cls *
        ((∑ θ : GenSigmaEmb' σ (G k),
            genUnlabelledDensity R σ cls.out (genSigmaFlagOfEmb' θ) Δ) /
          (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ)) *
        ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ)) =
      (∑ θ : GenSigmaEmb' σ (G k),
          genUnlabelledEvalDensity v (genSigmaFlagOfEmb' θ) Δ) /
        (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ) +
      ∑ cls ∈ v.support, v cls *
        ((∑ θ : GenSigmaEmb' σ (G k),
            genUnlabelledDensity R σ cls.out (genSigmaFlagOfEmb' θ) Δ) /
          (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ)) *
        ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1) := by
    intro k; rw [hEθ_eq k, ← Finset.sum_add_distrib]; congr 1; ext cls; ring
  -- E_θ = S_k/Q_k - diff eventually (when Q_k > 0)
  have hEθ_eventually : ∀ᶠ k in Filter.atTop,
      (∑ θ : GenSigmaEmb' σ (G k),
        genUnlabelledEvalDensity v (genSigmaFlagOfEmb' θ) Δ) /
        (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ) =
      (∑ cls ∈ v.support, v cls * (genNormalisationFactor σ cls.out *
        genUnlabelledDensity R (GenFlagType.empty R) cls.out.forget (G k) Δ)) /
        (genNormalisationFactor σ σ.toFlag *
          genUnlabelledDensity R (GenFlagType.empty R) σ.toFlag.forget (G k) Δ) -
      ∑ cls ∈ v.support, v cls *
        ((∑ θ : GenSigmaEmb' σ (G k),
            genUnlabelledDensity R σ cls.out (genSigmaFlagOfEmb' θ) Δ) /
          (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ)) *
        ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1) := by
    filter_upwards [htend_Q.eventually (Ioi_mem_nhds (half_lt_self_iff.mpr hQlim_pos))] with k hk_pos
    have hQ_ne : genNormalisationFactor σ σ.toFlag *
        genUnlabelledDensity R (GenFlagType.empty R) σ.toFlag.forget (G k) Δ ≠ 0 :=
      ne_of_gt (lt_trans (div_pos hQlim_pos two_pos) hk_pos)
    have h_id := hid_sum k; rw [hsum_split k] at h_id
    have h_div : (∑ θ : GenSigmaEmb' σ (G k),
          genUnlabelledEvalDensity v (genSigmaFlagOfEmb' θ) Δ) /
        (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ) +
      ∑ cls ∈ v.support, v cls *
        ((∑ θ : GenSigmaEmb' σ (G k),
            genUnlabelledDensity R σ cls.out (genSigmaFlagOfEmb' θ) Δ) /
          (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ)) *
        ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
          (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1) =
      (∑ cls ∈ v.support, v cls * (genNormalisationFactor σ cls.out *
        genUnlabelledDensity R (GenFlagType.empty R) cls.out.forget (G k) Δ)) /
        (genNormalisationFactor σ σ.toFlag *
          genUnlabelledDensity R (GenFlagType.empty R) σ.toFlag.forget (G k) Δ) :=
      (div_eq_of_eq_mul hQ_ne (by rw [mul_comm]; exact h_id)).symm
    linarith
  -- E_θ → L/Qlim → eventually ≤ L/(2·Qlim)
  have htend_Eθ : Filter.Tendsto
      (fun k => (∑ θ : GenSigmaEmb' σ (G k),
        genUnlabelledEvalDensity v (genSigmaFlagOfEmb' θ) Δ) /
        (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ))
      Filter.atTop (nhds (L / Qlim)) := by
    have htend_sub : Filter.Tendsto
        (fun k => (∑ cls ∈ v.support, v cls * (genNormalisationFactor σ cls.out *
          genUnlabelledDensity R (GenFlagType.empty R) cls.out.forget (G k) Δ)) /
          (genNormalisationFactor σ σ.toFlag *
            genUnlabelledDensity R (GenFlagType.empty R) σ.toFlag.forget (G k) Δ) -
        ∑ cls ∈ v.support, v cls *
          ((∑ θ : GenSigmaEmb' σ (G k),
              genUnlabelledDensity R σ cls.out (genSigmaFlagOfEmb' θ) Δ) /
            (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ)) *
          ((Nat.choose (Δ (G k).forget) (cls.out.size - σ.size) : ℝ) /
            (Nat.choose (Δ (G k).forget - σ.size) (cls.out.size - σ.size) : ℝ) - 1))
        Filter.atTop (nhds (L / Qlim)) := by
      rw [show L / Qlim = L / Qlim - 0 from by ring]
      exact (htend_S_L.div htend_Q (ne_of_gt hQlim_pos)).sub hdiff_sum_tendsto
    exact htend_sub.congr' (Filter.EventuallyEq.symm hEθ_eventually)
  -- Now bridge from genUnlabelledEvalDensity to genExpectedEvalDensity'
  -- genExpectedEvalDensity' = if N = 0 then 0 else (∑ genEvalAlgOf ...) / N
  -- genEvalAlgOf (fun F => genUnlabelledDensity R σ F (genSigmaFlagOfEmb' θ) Δ) v
  --   = genUnlabelledEvalDensity v (genSigmaFlagOfEmb' θ) Δ
  have hEvalAlg_eq_uED : ∀ k (θ : GenSigmaEmb' σ (G k)),
      genEvalAlgOf (fun F => genUnlabelledDensity R σ F (genSigmaFlagOfEmb' θ) Δ) v =
      genUnlabelledEvalDensity v (genSigmaFlagOfEmb' θ) Δ := by
    intro k θ; rfl
  have hEED_eq : ∀ k, genExpectedEvalDensity' σ v (G k) Δ =
      if (Fintype.card (GenSigmaEmb' σ (G k))) = 0 then 0
      else (∑ θ : GenSigmaEmb' σ (G k),
        genUnlabelledEvalDensity v (genSigmaFlagOfEmb' θ) Δ) /
        (Fintype.card (GenSigmaEmb' σ (G k)) : ℝ) := by
    intro k; unfold genExpectedEvalDensity'; simp only []
    split_ifs with h
    · rfl
    · simp only [hEvalAlg_eq_uED]
  -- Eventually N ≠ 0 (since Q_k → Qlim > 0 implies σ-embedding count is positive)
  have hN_eventually_pos : ∀ᶠ k in Filter.atTop,
      (Fintype.card (GenSigmaEmb' σ (G k))) ≠ 0 := by
    -- genNormalisationFactor σ σ.toFlag * uD(σ.toFlag.forget, G k) → Qlim > 0
    -- uD = IC / (C * Aut), and IC = card(GenSigmaEmb') by genInducedCount_toFlag_forget_eq_sigmaEmb
    -- If card = 0 then IC = 0, so uD = 0, so product = 0
    -- But eventually product > Qlim/2 > 0
    filter_upwards [htend_Q.eventually (Ioi_mem_nhds (half_lt_self_iff.mpr hQlim_pos))] with k hk
    intro hN0
    have huD_zero : genUnlabelledDensity R (GenFlagType.empty R) σ.toFlag.forget (G k) Δ = 0 := by
      unfold genUnlabelledDensity
      rw [show genInducedCount R (GenFlagType.empty R) σ.toFlag.forget (G k) = 0 from by
        rw [genInducedCount_toFlag_forget_eq_sigmaEmb]; exact hN0]
      simp
    linarith [lt_trans (div_pos hQlim_pos two_pos) hk, show
      genNormalisationFactor σ σ.toFlag *
        genUnlabelledDensity R (GenFlagType.empty R) σ.toFlag.forget (G k) Δ = 0 from by
      rw [huD_zero, mul_zero]]
  -- Combine: eventually genExpectedEvalDensity' = sum/N ≤ L/(2·Qlim)
  have hfinal : ∀ᶠ k in Filter.atTop,
      genExpectedEvalDensity' σ v (G k) Δ ≤ L / (2 * Qlim) := by
    have hLQ_lt : L / Qlim < L / (2 * Qlim) := by
      have h2Q_pos := mul_pos two_pos hQlim_pos
      rw [div_lt_div_iff₀ hQlim_pos h2Q_pos]
      nlinarith
    have htend_le := htend_Eθ.eventually (gt_mem_nhds hLQ_lt)
    filter_upwards [htend_le, hN_eventually_pos] with k hk_le hk_pos
    rw [hEED_eq k, if_neg hk_pos]
    exact le_of_lt hk_le
  exact Filter.eventually_atTop.mp (hfinal.mono fun k hk => hk)

/-- **Averaging preserves positivity** (thesis Lemma 2.8, generic version):
    For a local type σ, if v ∈ SemCone^σ has local support, then ⟦v⟧ ∈ SemCone^∅.

    The proof (for the SimpleGraph case, lines 7259-7950) constructs a σ-functional
    from an ∅-functional via the density identity + pigeonhole + Tychonoff.
    The generic version follows the same strategy.

    This is a standard fact in flag algebra theory (Razborov 2007, Lemma 2.8).

    The proof constructs a σ-functional from an ∅-functional:
    1. If ψ.evalAlg(⟦v⟧) < 0, then along ψ's sequence, the expected σ-density
       of v is eventually negative (by `genAveraging_eventually_neg`).
    2. Pigeonhole gives θ_k with v.uED(G_k, θ_k) ≤ expected < 0.
    3. Build a σ-level Δ-increasing sequence from these (G_k, θ_k).
    4. Apply `genLimit_functional_construction` → get φ with φ.evalAlg(v) < 0.
    5. This contradicts v.isPositive. -/
theorem genAveraging_preserves_positivity {R : RelUniverse} {σ : GenFlagType R}
    {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    (hσ : GenIsLocalType σ 𝒢 Δ)
    (v : GenFlagAlg R σ)
    (hv : v.isPositive 𝒢 Δ)
    (hlocal : ∀ cls ∈ v.support, GenIsLocalFlag σ cls.out 𝒢 Δ) :
    (genAveragingAlg σ v).isPositive 𝒢 Δ := by
  -- Contrapositive: assume ⟦v⟧ is not positive → find σ-functional with v < 0
  intro ψ
  by_contra hψ_neg
  push_neg at hψ_neg
  -- hψ_neg : ψ.evalAlg (genAveragingAlg σ v) < 0
  -- We construct a σ-functional φ with φ.evalAlg v < 0, contradicting hv.
  -- Step 1: Build a σ-level Δ-increasing sequence with v.uED ≤ c < 0.
  -- By density identity + pigeonhole along ψ's sequence, for large k,
  -- ∃ θ_k : GenSigmaEmb' σ G_k with v evaluated at (G_k, θ_k) ≤ c < 0.
  have hsuff : ∃ (seq : GenDeltaIncreasingSeq R σ Δ)
      (hclass : ∀ k, 𝒢 (seq.seq k).forget)
      (c : ℝ) (_ : c < 0),
      ∀ k, genEvalAlgOf
        (fun F => genUnlabelledDensity R σ F (seq.seq k) Δ) v ≤ c := by
    -- Step (a): By genAveraging_eventually_neg, ∃ c < 0, N₀ such that
    -- for k ≥ N₀, the average σ-density of v at G_k ≤ c.
    obtain ⟨c, hc_neg, N₀, hN₀⟩ :=
      genAveraging_eventually_neg' hσ v hlocal ψ hψ_neg
    -- Step (b): Pigeonhole — average ≤ c → ∃ individual ≤ c.
    have hexists_neg : ∀ k, N₀ ≤ k →
        ∃ θ : GenSigmaEmb' σ (ψ.seq.seq (ψ.sub k)),
          genEvalAlgOf (fun F => genUnlabelledDensity R σ F
            (genSigmaFlagOfEmb' θ) Δ) v ≤ c := by
      intro k hk
      have havg := hN₀ k hk
      simp only [genExpectedEvalDensity'] at havg
      by_cases hN : Fintype.card (GenSigmaEmb' σ (ψ.seq.seq (ψ.sub k))) = 0
      · simp [hN] at havg; linarith
      · -- Average ≤ c, nonempty → ∃ individual ≤ c (pigeonhole)
        have hN_pos : (0 : ℝ) < (Fintype.card (GenSigmaEmb' σ (ψ.seq.seq (ψ.sub k))) : ℝ) :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
        rw [if_neg hN, div_le_iff₀ hN_pos] at havg
        have hnonempty : (Finset.univ : Finset (GenSigmaEmb' σ (ψ.seq.seq (ψ.sub k)))).Nonempty :=
          Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hN))
        have hsum_const : ∑ _ : GenSigmaEmb' σ (ψ.seq.seq (ψ.sub k)), c =
            (Fintype.card (GenSigmaEmb' σ (ψ.seq.seq (ψ.sub k))) : ℝ) * c := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [mul_comm] at havg; rw [← hsum_const] at havg
        obtain ⟨θ, _, hθ⟩ := Finset.exists_le_of_sum_le hnonempty havg
        exact ⟨θ, hθ⟩
    -- Step (c): Build the shifted sequence — for each k, choose θ_{k+N₀}.
    classical
    have hchoice : ∀ k, ∃ θ : GenSigmaEmb' σ (ψ.seq.seq (ψ.sub (k + N₀))),
        genEvalAlgOf (fun F => genUnlabelledDensity R σ F
          (genSigmaFlagOfEmb' θ) Δ) v ≤ c :=
      fun k => hexists_neg (k + N₀) (Nat.le_add_left N₀ k)
    let θ_seq : (k : ℕ) → GenSigmaEmb' σ (ψ.seq.seq (ψ.sub (k + N₀))) :=
      fun k => (hchoice k).choose
    have hθ_bound : ∀ k, genEvalAlgOf (fun F => genUnlabelledDensity R σ F
        (genSigmaFlagOfEmb' (θ_seq k)) Δ) v ≤ c :=
      fun k => (hchoice k).choose_spec
    -- Step (d): Build the GenDeltaIncreasingSeq at type σ.
    let seq : GenDeltaIncreasingSeq R σ Δ := {
      seq := fun k => genSigmaFlagOfEmb' (θ_seq k)
      increasing := by
        intro a b hab
        -- Δ of forget = Δ of G_k since genSigmaFlagOfEmb preserves size/str
        change Δ (genSigmaFlagOfEmb' (θ_seq a)).forget <
             Δ (genSigmaFlagOfEmb' (θ_seq b)).forget
        -- genSigmaFlagOfEmb'(θ_seq k).forget = ψ.seq.seq(ψ.sub(k+N₀))
        -- (genSigmaFlagOfEmb' (θ_seq k)).forget = ψ.seq.seq(ψ.sub(k+N₀))
        -- and ψ.seq.seq(x).forget = ψ.seq.seq(x) for ∅-type flags
        -- The goal is Δ (...).forget < Δ (...).forget, which after rewriting becomes
        -- Δ (ψ.seq.seq(ψ.sub(a+N₀))).forget < Δ (ψ.seq.seq(ψ.sub(b+N₀))).forget
        -- = (fun k => Δ (ψ.seq.seq k).forget)(ψ.sub(a+N₀)) < ... = ψ.seq.increasing
        convert ψ.seq.increasing (ψ.sub_strictMono (show a + N₀ < b + N₀ by omega))
          using 2
    }
    refine ⟨seq, ?_, c, hc_neg, hθ_bound⟩
    intro k
    -- Goal: 𝒢 (genSigmaFlagOfEmb' (θ_seq k)).forget
    -- = 𝒢 (ψ.seq.seq ...) = 𝒢 (ψ.seq.seq ...).forget   [by forget = id for ∅-type]
    have hfk := genSigmaFlagOfEmb'_forget (θ_seq k)
    have hforget : (ψ.seq.seq (ψ.sub (k + N₀))).forget = ψ.seq.seq (ψ.sub (k + N₀)) :=
      GenFlag.empty_ext _ _ rfl rfl
    rw [hfk, ← hforget]
    exact ψ.seq_in_class (ψ.sub (k + N₀))
  obtain ⟨seq, hclass, c, hc_neg, hbound⟩ := hsuff
  -- Step 2: Build limit functional from this σ-sequence.
  let φ := genLimit_functional_construction R σ 𝒢 Δ seq hclass
  -- Step 3: φ.evalAlg v ≤ c < 0.
  -- φ's convergence gives: for each local F, genUnlabelledDensity F (seq(φ.sub k)) → φ.eval F
  -- So genEvalAlgOf φ.eval v = lim genEvalAlgOf (density at seq(φ.sub k)) v
  -- Each term ≤ c (since φ.sub k is a subsequence of ℕ and ALL terms satisfy the bound)
  -- Therefore the limit ≤ c < 0.
  have hφ_neg : φ.evalAlg v < 0 := by
    -- genEvalAlgOf φ.eval v = Σ_cls v(cls) * φ.eval(cls.out)
    -- φ.eval(cls.out) = lim genUnlabelledDensity cls.out (seq(φ.sub k))
    -- So genEvalAlgOf φ.eval v = lim genEvalAlgOf (density at seq(φ.sub k)) v
    -- Each term ≤ c (from hbound, since φ.sub k ∈ ℕ), so limit ≤ c < 0.
    change genEvalAlgOf φ.eval v < 0
    -- Step A: each coordinate converges
    have hconv : ∀ cls ∈ v.support, Filter.Tendsto
        (fun k => genUnlabelledDensity R σ cls.out (seq.seq (φ.sub k)) Δ)
        Filter.atTop (nhds (φ.eval cls.out)) :=
      fun cls hcls => φ.convergence cls.out (hlocal cls hcls)
    -- Step B: finite sum converges (tendsto_finset_sum)
    have htend : Filter.Tendsto
        (fun k => genEvalAlgOf (fun F => genUnlabelledDensity R σ F (seq.seq (φ.sub k)) Δ) v)
        Filter.atTop (nhds (genEvalAlgOf φ.eval v)) := by
      simp only [genEvalAlgOf, Finsupp.sum]
      exact tendsto_finset_sum v.support
        (fun cls hcls => (hconv cls hcls).const_mul (v cls))
    -- Step C: each term ≤ c (since hbound applies to ALL k, including φ.sub k)
    have hle : ∀ k, genEvalAlgOf
        (fun F => genUnlabelledDensity R σ F (seq.seq (φ.sub k)) Δ) v ≤ c :=
      fun k => hbound (φ.sub k)
    -- Step D: limit ≤ c < 0
    exact lt_of_le_of_lt (le_of_tendsto htend (Filter.Eventually.of_forall hle)) hc_neg
  -- Step 4: Contradiction with v.isPositive
  exact absurd (hv φ) (not_le.mpr hφ_neg)

/-- `evalAlg` distributes over `Finset.sum`. -/
theorem GenLimitFunctional.evalAlg_finset_sum {R : RelUniverse} {σ : GenFlagType R}
    {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    (ψ : GenLimitFunctional R σ 𝒢 Δ) {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → GenFlagAlg R σ) :
    ψ.evalAlg (∑ x ∈ S, f x) = ∑ x ∈ S, ψ.evalAlg (f x) := by
  induction S using Finset.induction with
  | empty =>
    simp [GenLimitFunctional.evalAlg, genEvalAlgOf, Finsupp.sum_zero_index]
  | @insert a s hna ih =>
    rw [Finset.sum_insert hna, ψ.evalAlg_add, ih, Finset.sum_insert hna]

/-- **Averaging–evaluation identity**: evaluating `genAveragingAlg σ v` through
    an ∅-type limit functional decomposes as a sum over the Finsupp support of `v`,
    weighted by normalisation factors and forget evaluations.

    `ψ.evalAlg(⟦v⟧) = Σ_cls v(cls) · q_σ(cls.out) · ψ.eval(cls.out.forget)` -/
theorem evalAlg_genAveragingAlg {R : RelUniverse} {σ : GenFlagType R}
    {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    (ψ : GenLimitFunctional R (GenFlagType.empty R) 𝒢 Δ)
    (v : GenFlagAlg R σ) :
    ψ.evalAlg (genAveragingAlg σ v) =
      v.sum (fun cls c =>
        c * (genNormalisationFactor σ cls.out * ψ.eval cls.out.forget)) := by
  simp only [genAveragingAlg, genClassAveraging, genAveraging, Finsupp.sum]
  rw [ψ.evalAlg_finset_sum]
  congr 1; ext cls
  rw [ψ.evalAlg_smul, ψ.evalAlg_smul, ψ.evalAlg_single]

/-- `evalAlg` distributes over finite sums in `GenFlagAlg`. -/
theorem GenLimitFunctional.evalAlg_finset_sum_genFlagAlg {R : RelUniverse}
    {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    (ψ : GenLimitFunctional R (GenFlagType.empty R) 𝒢 Δ)
    {ι : Type*} (S : Finset ι) (f : ι → GenFlagAlg R (GenFlagType.empty R)) :
    ψ.evalAlg (S.sum f) = S.sum (fun i => ψ.evalAlg (f i)) := by
  induction S using Finset.induction with
  | empty => simp [ψ.evalAlg_eq_genEvalAlgOf, genEvalAlgOf, Finsupp.sum_zero_index]
  | @insert a s ha ih => rw [Finset.sum_insert ha, ψ.evalAlg_add, ih, Finset.sum_insert ha]

/-- Expand `evalAlg(genAveragingAlg(genLocalFlagProduct F₁ F₂))` as a finset sum
    over `genClassesOfSize`. -/
theorem evalAlg_genAveragingAlg_genLocalFlagProduct {R : RelUniverse} {σ : GenFlagType R}
    {𝒢 : GenGraphClass R} {Δ : GenGraphParam R}
    (ψ : GenLimitFunctional R (GenFlagType.empty R) 𝒢 Δ)
    (F₁ F₂ : GenFlag R σ)
    (hn : σ.size ≤ F₁.size + F₂.size - σ.size) :
    ψ.evalAlg (genAveragingAlg σ (genLocalFlagProduct R σ F₁ F₂)) =
      ((genFlagAutCount R σ F₁ : ℝ) * (genFlagAutCount R σ F₂ : ℝ))⁻¹ *
      ∑ cls ∈ genClassesOfSize R σ (F₁.size + F₂.size - σ.size) hn,
        genJointInducedDensity R σ F₁ F₂ cls.out *
        (genNormalisationFactor σ cls.out * ψ.eval cls.out.forget) := by
  -- Step 1: Unfold genLocalFlagProduct
  simp only [genLocalFlagProduct, dif_pos hn]
  -- Step 2: Push genAveragingAlg through smul
  rw [genAveragingAlg_smul]
  -- Step 3: Push evalAlg through smul
  rw [ψ.evalAlg_smul]
  congr 1
  -- Step 4: Push genAveragingAlg through finset sum
  -- genAveragingAlg of a finset sum = finset sum of genAveragingAlg of each term
  have genAvg_finset : genAveragingAlg σ
      ((genClassesOfSize R σ (F₁.size + F₂.size - σ.size) hn).sum
        (fun cls => Finsupp.single cls (genJointInducedDensity R σ F₁ F₂ cls.out))) =
      (genClassesOfSize R σ (F₁.size + F₂.size - σ.size) hn).sum
        (fun cls => genAveragingAlg σ (Finsupp.single cls (genJointInducedDensity R σ F₁ F₂ cls.out))) := by
    induction (genClassesOfSize R σ (F₁.size + F₂.size - σ.size) hn) using Finset.induction with
    | empty => simp [genAveragingAlg, Finsupp.sum_zero_index]
    | @insert a s ha ih => rw [Finset.sum_insert ha, genAveragingAlg_add, ih, Finset.sum_insert ha]
  rw [genAvg_finset]
  -- Step 5: Push evalAlg through finset sum
  rw [ψ.evalAlg_finset_sum_genFlagAlg]
  -- Step 6: Simplify each term: evalAlg (genAveragingAlg σ (single cls jid))
  congr 1; ext cls
  -- genAveragingAlg σ (single cls jid) = jid • genClassAveraging σ cls
  have h_avg : genAveragingAlg σ (Finsupp.single cls (genJointInducedDensity R σ F₁ F₂ cls.out)) =
      (genJointInducedDensity R σ F₁ F₂ cls.out) • genClassAveraging σ cls := by
    simp only [genAveragingAlg]
    rw [Finsupp.sum_single_index (by exact zero_smul ℝ (genClassAveraging σ cls))]
  rw [h_avg, ψ.evalAlg_smul]
  -- genClassAveraging σ cls = nf • single(cls.out.forget)
  simp only [genClassAveraging, genAveraging]
  rw [ψ.evalAlg_smul, ψ.evalAlg_single]

end Davey2024
