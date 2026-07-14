import DaveyThesis2024.Basic

/-!
# Flag Isomorphism and Isomorphism Classes

Defines flag isomorphism (σ-compatible graph isomorphism) and the quotient
`FlagClass σ` of flags modulo isomorphism. This provides the foundation for
constructing the flag algebra `FlagAlg σ` as `FlagClass σ →₀ ℝ`.

Two σ-flags (F, θ) and (F', θ') are isomorphic if there exists a graph
isomorphism φ : F ≃g F' satisfying φ ∘ θ = θ'. This matches the thesis's
convention that flag algebra elements are formal sums over isomorphism classes.

## Main definitions

* `FlagIso σ F F'` — flag isomorphism: ∃ φ : F.graph ≃g F'.graph, φ ∘ emb = emb'
* `flagSetoid σ` — the equivalence relation on `Flag σ` given by `FlagIso`
* `FlagClass σ` — isomorphism classes of σ-flags (quotient type)

## Main results

* `FlagIso.refl`, `.symm`, `.trans` — equivalence relation
* `inducedCount_flagIso` — induced count is invariant under flag isomorphism
* `inducedDensity_flagIso` — induced density respects isomorphism
* `localDensity_flagIso` — local density respects isomorphism
-/

set_option linter.style.openClassical false

open Finset BigOperators Classical

namespace Davey2024

/-! ## Flag Isomorphism -/

/-- Two σ-flags are **isomorphic** if there exists a graph isomorphism between
    their underlying graphs that commutes with the σ-embeddings.
    (F, θ) ≅ (F', θ') iff ∃ φ : F ≃g F', φ ∘ θ = θ'. -/
def FlagIso (σ : FlagType) (F F' : Flag σ) : Prop :=
  ∃ (φ : F.graph ≃g F'.graph),
    ∀ i : Fin σ.size, φ (F.embedding i) = F'.embedding i

theorem FlagIso.refl (σ : FlagType) (F : Flag σ) : FlagIso σ F F :=
  ⟨RelIso.refl _, fun _ => rfl⟩

theorem FlagIso.symm {σ : FlagType} {F F' : Flag σ} (h : FlagIso σ F F') :
    FlagIso σ F' F := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.symm, fun i => ?_⟩
  simp [← hφ i]

theorem FlagIso.trans {σ : FlagType} {F F' F'' : Flag σ}
    (h1 : FlagIso σ F F') (h2 : FlagIso σ F' F'') : FlagIso σ F F'' := by
  obtain ⟨φ₁, hφ₁⟩ := h1
  obtain ⟨φ₂, hφ₂⟩ := h2
  refine ⟨φ₁.trans φ₂, fun i => ?_⟩
  simp [RelIso.trans_apply, hφ₁ i, hφ₂ i]

/-- Flag isomorphism is an equivalence relation. -/
instance flagSetoid (σ : FlagType) : Setoid (Flag σ) where
  r := FlagIso σ
  iseqv := ⟨FlagIso.refl σ, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-! ## Isomorphism Classes -/

/-- **Isomorphism class** of σ-flags: the quotient of `Flag σ` by `FlagIso`.
    Elements of `FlagClass σ` are the basis elements of the flag algebra. -/
def FlagClass (σ : FlagType) := Quotient (flagSetoid σ)

/-- Quotient map: send a flag to its isomorphism class. -/
def FlagClass.mk {σ : FlagType} (F : Flag σ) : FlagClass σ :=
  Quotient.mk (flagSetoid σ) F

@[simp]
theorem FlagClass.mk_eq {σ : FlagType} (F F' : Flag σ) :
    FlagClass.mk F = FlagClass.mk F' ↔ FlagIso σ F F' :=
  Quotient.eq (r := flagSetoid σ)

noncomputable instance (σ : FlagType) : DecidableEq (FlagClass σ) :=
  Classical.decEq _

/-! ## Well-Definedness: Induced Embeddings Respect Isomorphism

We show that isomorphic flags have the same induced counts and densities,
which is needed to lift density functions to `FlagClass`. -/

/-- Transport an induced embedding along a flag isomorphism.
    Given φ : F₁ ≃g F₂ and e : F₂ ↪ G, construct F₁ ↪ G by precomposing with φ. -/
def InducedEmbedding.mapIso {σ : FlagType} {F₁ F₂ G : Flag σ}
    (φ : F₁.graph ≃g F₂.graph) (hφ : ∀ i : Fin σ.size, φ (F₁.embedding i) = F₂.embedding i)
    (e : InducedEmbedding σ F₂ G) : InducedEmbedding σ F₁ G where
  toFun := e.toFun ∘ φ
  injective := e.injective.comp (RelIso.injective φ)
  map_adj u v h := e.map_adj _ _ (φ.map_rel_iff'.mpr h)
  map_non_adj u v hne hnadj := by
    apply e.map_non_adj _ _ ((RelIso.injective φ).ne hne)
    intro h; exact hnadj (φ.map_rel_iff'.mp h)
  compat i := by
    change e.toFun (φ (F₁.embedding i)) = G.embedding i
    rw [hφ i]; exact e.compat i

/-- The inverse transport: given φ : F₁ ≃g F₂ and e : F₁ ↪ G, construct F₂ ↪ G. -/
def InducedEmbedding.mapIsoInv {σ : FlagType} {F₁ F₂ G : Flag σ}
    (φ : F₁.graph ≃g F₂.graph) (hφ : ∀ i : Fin σ.size, φ (F₁.embedding i) = F₂.embedding i)
    (e : InducedEmbedding σ F₁ G) : InducedEmbedding σ F₂ G :=
  InducedEmbedding.mapIso φ.symm
    (fun i => by simp [← hφ i]) e

/-- Flag isomorphism induces a bijection on induced embeddings. -/
noncomputable def InducedEmbedding.equivOfIso {σ : FlagType} {F₁ F₂ G : Flag σ}
    (φ : F₁.graph ≃g F₂.graph) (hφ : ∀ i : Fin σ.size, φ (F₁.embedding i) = F₂.embedding i) :
    InducedEmbedding σ F₁ G ≃ InducedEmbedding σ F₂ G where
  toFun := InducedEmbedding.mapIsoInv φ hφ
  invFun := InducedEmbedding.mapIso φ hφ
  left_inv e := by
    cases e; simp only [mapIso, mapIsoInv]
    congr 1; ext x; simp
  right_inv e := by
    cases e; simp only [mapIso, mapIsoInv]
    congr 1; ext x; simp

/-- Isomorphic flags have the same size. -/
theorem flagIso_size_eq {σ : FlagType} {F₁ F₂ : Flag σ}
    (h : FlagIso σ F₁ F₂) : F₁.size = F₂.size := by
  obtain ⟨φ, _⟩ := h
  simpa using Fintype.card_congr φ.toEquiv

/-- Isomorphic flags have the same induced count into any host graph. -/
theorem inducedCount_flagIso {σ : FlagType} {F₁ F₂ G : Flag σ}
    (h : FlagIso σ F₁ F₂) : inducedCount σ F₁ G = inducedCount σ F₂ G := by
  obtain ⟨φ, hφ⟩ := h
  unfold inducedCount
  exact Fintype.card_congr (InducedEmbedding.equivOfIso φ hφ)

/-- Isomorphic flags have the same induced density into any host graph. -/
theorem inducedDensity_flagIso {σ : FlagType} {F₁ F₂ G : Flag σ}
    (h : FlagIso σ F₁ F₂) : inducedDensity σ F₁ G = inducedDensity σ F₂ G := by
  obtain ⟨φ, hφ⟩ := h
  unfold inducedDensity
  rw [inducedCount_flagIso ⟨φ, hφ⟩, flagIso_size_eq ⟨φ, hφ⟩]

/-- Isomorphic flags have the same local density into any host graph. -/
theorem localDensity_flagIso {σ : FlagType} {F₁ F₂ G : Flag σ} {Δ : GraphParam}
    (h : FlagIso σ F₁ F₂) : localDensity σ F₁ G Δ = localDensity σ F₂ G Δ := by
  obtain ⟨φ, hφ⟩ := h
  unfold localDensity
  rw [inducedCount_flagIso ⟨φ, hφ⟩, flagIso_size_eq ⟨φ, hφ⟩]

/-! ## IsLocalFlag Respects Isomorphism -/

/-- Bounded density respects flag isomorphism. -/
theorem IsBoundedDensity_flagIso {σ : FlagType} {F₁ F₂ : Flag σ} {𝒢 : GraphClass} {Δ : GraphParam}
    (hiso : FlagIso σ F₁ F₂) (hbd : IsBoundedDensity σ F₁ 𝒢 Δ) :
    IsBoundedDensity σ F₂ 𝒢 Δ := by
  obtain ⟨C, hC0, hC⟩ := hbd
  exact ⟨C, hC0, fun G hG => localDensity_flagIso hiso ▸ hC G hG⟩

/-- Transport a label extension backwards along a flag isomorphism.
    Given φ : F₁ ≃g F₂ and ext₂ : LabelExtension σ F₂,
    construct ext₁ : LabelExtension σ F₁ using φ⁻¹. -/
noncomputable def LabelExtension.ofFlagIso {σ : FlagType} {F₁ F₂ : Flag σ}
    (φ : F₁.graph ≃g F₂.graph) (hφ : ∀ i : Fin σ.size, φ (F₁.embedding i) = F₂.embedding i)
    (ext₂ : LabelExtension σ F₂) : LabelExtension σ F₁ where
  vertex := φ.symm ext₂.vertex
  unlabelled := by
    intro ⟨i, hi⟩
    exact ext₂.unlabelled ⟨i, by
      calc F₂.embedding i = φ (F₁.embedding i) := (hφ i).symm
        _ = φ (φ.symm ext₂.vertex) := by rw [hi]
        _ = ext₂.vertex := φ.apply_symm_apply ext₂.vertex⟩

/-- The vertex maps of corresponding extensions are related by φ. -/
theorem LabelExtension.vertexMap_ofFlagIso {σ : FlagType} {F₁ F₂ : Flag σ}
    (φ : F₁.graph ≃g F₂.graph) (hφ : ∀ i : Fin σ.size, φ (F₁.embedding i) = F₂.embedding i)
    (ext₂ : LabelExtension σ F₂) (i : Fin (σ.size + 1)) :
    φ ((ofFlagIso φ hφ ext₂).vertexMap i) = ext₂.vertexMap i := by
  obtain ⟨j, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
  · simp [vertexMap, ofFlagIso, Fin.lastCases_castSucc, hφ]
  · simp [vertexMap, ofFlagIso, Fin.lastCases_last]

/-- The extended types of corresponding extensions are equal. -/
theorem LabelExtension.extendedType_ofFlagIso_eq {σ : FlagType} {F₁ F₂ : Flag σ}
    (φ : F₁.graph ≃g F₂.graph) (hφ : ∀ i : Fin σ.size, φ (F₁.embedding i) = F₂.embedding i)
    (ext₂ : LabelExtension σ F₂) :
    (ofFlagIso φ hφ ext₂).extendedType = ext₂.extendedType := by
  simp only [extendedType]
  congr 1
  ext a b
  change F₁.graph.Adj ((ofFlagIso φ hφ ext₂).vertexMap a) ((ofFlagIso φ hφ ext₂).vertexMap b) ↔
    F₂.graph.Adj (ext₂.vertexMap a) (ext₂.vertexMap b)
  constructor
  · intro h
    have := φ.map_rel_iff'.mpr h
    simp only [RelIso.coe_fn_toEquiv] at this
    rwa [vertexMap_ofFlagIso φ hφ ext₂ a, vertexMap_ofFlagIso φ hφ ext₂ b] at this
  · intro h
    rw [← φ.map_rel_iff']
    simp only [RelIso.coe_fn_toEquiv]
    rwa [vertexMap_ofFlagIso φ hφ ext₂ a, vertexMap_ofFlagIso φ hφ ext₂ b]

/-- `IsLocalFlag` respects flag isomorphism, generalized across `FlagType` equality.
    This is needed for the recursive step where extensions change the type. -/
theorem IsLocalFlag_flagIso_gen (n : ℕ) :
    ∀ {σ₁ σ₂ : FlagType} (hσ : σ₁ = σ₂) {F₁ : Flag σ₁} {F₂ : Flag σ₂}
      {𝒢 : GraphClass} {Δ : GraphParam},
    F₁.unlabelledSize ≤ n →
    (φ : F₁.graph ≃g F₂.graph) →
    (∀ i : Fin σ₁.size, φ (F₁.embedding i) =
      F₂.embedding (Fin.cast (congrArg FlagType.size hσ) i)) →
    IsLocalFlag σ₁ F₁ 𝒢 Δ → IsLocalFlag σ₂ F₂ 𝒢 Δ := by
  induction n with
  | zero =>
    intro σ₁ σ₂ hσ F₁ F₂ 𝒢 Δ hn φ hφ h
    subst hσ; simp only [Fin.cast_eq_self] at hφ
    cases h with | intro _ _ _ _ hbd hext =>
    apply IsLocalFlag.intro _ _ _ _ (IsBoundedDensity_flagIso ⟨φ, hφ⟩ hbd)
    intro ext₂; exfalso
    have hsz : F₁.size = F₂.size := flagIso_size_eq ⟨φ, hφ⟩
    have := ext₂.size_le
    unfold Flag.unlabelledSize at hn; omega
  | succ n ih_n =>
    intro σ₁ σ₂ hσ F₁ F₂ 𝒢 Δ hn φ hφ h
    subst hσ; simp only [Fin.cast_eq_self] at hφ
    cases h with | intro _ _ _ _ hbd hext =>
    apply IsLocalFlag.intro _ _ _ _ (IsBoundedDensity_flagIso ⟨φ, hφ⟩ hbd)
    intro ext₂
    let ext₁ := LabelExtension.ofFlagIso φ hφ ext₂
    have hteq := LabelExtension.extendedType_ofFlagIso_eq φ hφ ext₂
    apply ih_n hteq ?_ φ ?_ (hext ext₁)
    · -- Unlabelled size bound: ext₁.extendedFlag.unlabelledSize ≤ n
      simp only [Flag.unlabelledSize, LabelExtension.extendedFlag, LabelExtension.extendedType]
      unfold Flag.unlabelledSize at hn; omega
    · -- Compatibility: φ (ext₁.vertexMap i) = ext₂.vertexMap (Fin.cast _ i)
      intro i
      -- extendedFlag.embedding is comap of vertexMap, so it equals vertexMap
      change φ (ext₁.vertexMap i) = ext₂.vertexMap (Fin.cast _ i)
      have hcast : Fin.cast (congrArg FlagType.size hteq) i = i := Fin.ext rfl
      rw [hcast]
      exact LabelExtension.vertexMap_ofFlagIso φ hφ ext₂ i

/-- `IsLocalFlag` respects flag isomorphism: isomorphic flags are both local or both non-local. -/
theorem IsLocalFlag_flagIso {σ : FlagType} {F₁ F₂ : Flag σ} {𝒢 : GraphClass} {Δ : GraphParam}
    (hiso : FlagIso σ F₁ F₂) (h : IsLocalFlag σ F₁ 𝒢 Δ) : IsLocalFlag σ F₂ 𝒢 Δ := by
  obtain ⟨φ, hφ⟩ := hiso
  have : ∀ i : Fin σ.size, φ (F₁.embedding i) = F₂.embedding (Fin.cast rfl i) := by
    simp only [Fin.cast_eq_self]; exact hφ
  exact IsLocalFlag_flagIso_gen F₁.unlabelledSize rfl le_rfl φ this h

/-! ## Forget Respects Isomorphism -/

/-- Construct a `Flag σ` from an embedding of σ.graph into F.graph.
    Used for the normalisation factor: each embedding gives a σ-flag on the same graph. -/
def flagOfEmbedding {σ : FlagType} (F : Flag σ) (e : σ.graph ↪g F.graph) : Flag σ where
  size := F.size
  graph := F.graph
  embedding := e
  hsize := F.hsize

/-- Forgetting the σ-labelling preserves flag isomorphism:
    if F₁ ≅_σ F₂ then ↓F₁ ≅_∅ ↓F₂. -/
theorem forget_flagIso {σ : FlagType} {F₁ F₂ : Flag σ}
    (h : FlagIso σ F₁ F₂) : FlagIso emptyType F₁.forget F₂.forget := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ, fun i => Fin.elim0 i⟩

/-- The isomorphism class of the forgotten flag depends only on the isomorphism class. -/
theorem FlagClass.mk_forget_eq {σ : FlagType} {F₁ F₂ : Flag σ}
    (h : FlagIso σ F₁ F₂) :
    FlagClass.mk F₁.forget = FlagClass.mk F₂.forget :=
  (FlagClass.mk_eq _ _).mpr (forget_flagIso h)


/-! ## Label Permutation Invariance

Locality of flags is invariant under permutation of labels. This is needed
for `augmented_local_flag`, where the recursive step requires swapping the
last two labels to match the induction hypothesis. -/

/-- Apply a label permutation to a flag type.
    The type keeps the same size; the graph is pulled back through π. -/
def FlagType.relabel (σ : FlagType) (π : Equiv.Perm (Fin σ.size)) : FlagType where
  size := σ.size
  graph := σ.graph.comap π

/-- Apply a label permutation to a flag.
    The flag keeps the same size and graph; only the σ-embedding changes. -/
noncomputable def Flag.relabel {σ : FlagType} (F : Flag σ)
    (π : Equiv.Perm (Fin σ.size)) : Flag (σ.relabel π) where
  size := F.size
  graph := F.graph
  embedding :=
    ⟨⟨fun i => F.embedding (π i), fun {_ _} h => π.injective (F.embedding.injective h)⟩,
     fun {a b} => F.embedding.map_rel_iff' (a := π a) (b := π b)⟩
  hsize := F.hsize

@[simp] theorem Flag.relabel_size {σ : FlagType} (F : Flag σ)
    (π : Equiv.Perm (Fin σ.size)) : (F.relabel π).size = F.size := rfl

@[simp] theorem Flag.relabel_graph {σ : FlagType} (F : Flag σ)
    (π : Equiv.Perm (Fin σ.size)) : (F.relabel π).graph = F.graph := rfl

theorem Flag.relabel_embedding_apply {σ : FlagType} (F : Flag σ)
    (π : Equiv.Perm (Fin σ.size)) (i : Fin σ.size) :
    (F.relabel π).embedding i = F.embedding (π i) := rfl

@[simp] theorem Flag.relabel_forget {σ : FlagType} (F : Flag σ)
    (π : Equiv.Perm (Fin σ.size)) : (F.relabel π).forget = F.forget := rfl

@[simp] theorem Flag.relabel_unlabelledSize {σ : FlagType} (F : Flag σ)
    (π : Equiv.Perm (Fin σ.size)) :
    (F.relabel π).unlabelledSize = F.unlabelledSize := rfl

/-- The range of the embedding is unchanged by label permutation. -/
theorem Flag.relabel_embedding_range {σ : FlagType} (F : Flag σ)
    (π : Equiv.Perm (Fin σ.size)) :
    Set.range (F.relabel π).embedding = Set.range F.embedding := by
  ext v; constructor
  · rintro ⟨i, rfl⟩; exact ⟨π i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨π.symm i, by
      change F.embedding (π (π.symm i)) = F.embedding i
      simp [π.apply_symm_apply]⟩

/-- `IsBoundedDensity` is invariant under label permutation. -/
theorem IsBoundedDensity_relabel {σ : FlagType} {F : Flag σ}
    {𝒢 : GraphClass} {Δ : GraphParam}
    (π : Equiv.Perm (Fin σ.size))
    (h : IsBoundedDensity σ F 𝒢 Δ) :
    IsBoundedDensity (σ.relabel π) (F.relabel π) 𝒢 Δ := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun G' hG' => ?_⟩
  -- Construct G : Flag σ from G' by relabelling with π⁻¹
  let G : Flag σ :=
    { size := G'.size
      graph := G'.graph
      embedding :=
        ⟨⟨fun i => G'.embedding (π.symm i),
          fun {a b} h => π.symm.injective (G'.embedding.injective h)⟩,
         fun {a b} => by
          symm
          change σ.graph.Adj a b ↔ G'.graph.Adj (G'.embedding (π.symm a)) (G'.embedding (π.symm b))
          have h : σ.graph.Adj a b ↔ (σ.graph.comap π).Adj (π.symm a) (π.symm b) := by
            simp [SimpleGraph.comap_adj, π.apply_symm_apply]
          rw [h]
          exact (G'.embedding.map_rel_iff' (a := π.symm a) (b := π.symm b)).symm⟩
      hsize := G'.hsize }
  have hG_forget : G.forget = G'.forget := rfl
  have hG_bound := hbound G (hG_forget ▸ hG')
  -- Show localDensity are equal via bijection on InducedEmbedding
  suffices inducedCount (σ.relabel π) (F.relabel π) G' = inducedCount σ F G by
    unfold localDensity at hG_bound ⊢
    rw [this, Flag.relabel_size]
    convert hG_bound using 2
  unfold inducedCount
  apply Fintype.card_congr
  exact Equiv.ofBijective
    (fun e => InducedEmbedding.mk e.toFun e.injective e.map_adj e.map_non_adj
      fun k => by
        have := e.compat (π.symm k)
        simp only [Flag.relabel_embedding_apply, π.apply_symm_apply] at this
        exact this)
    ⟨fun e₁ e₂ h => by
      cases e₁; cases e₂; simp only [InducedEmbedding.mk.injEq] at h ⊢; exact h,
     fun e => ⟨InducedEmbedding.mk e.toFun e.injective e.map_adj e.map_non_adj
      (fun k => by
        have h1 := e.compat (π k)
        change e.toFun ((F.relabel π).embedding k) = G'.embedding k
        rw [Flag.relabel_embedding_apply]
        exact h1.trans (congrArg G'.embedding (π.symm_apply_apply k))),
      by cases e; simp⟩⟩

/-- Extend a permutation on `Fin n` to `Fin (n + 1)` by fixing the last element. -/
noncomputable def Equiv.Perm.extendFin {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective
    (Fin.lastCases (Fin.last n) (Fin.castSucc ∘ π))
    ⟨by
      intro a b h
      obtain (⟨i, rfl⟩ | rfl) := a.eq_castSucc_or_eq_last
      · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
        · simp only [Fin.lastCases_castSucc, Function.comp_apply, Fin.castSucc_inj] at h
          exact congr_arg Fin.castSucc (π.injective h)
        · simp only [Fin.lastCases_castSucc, Function.comp_apply, Fin.lastCases_last] at h
          exact absurd h (Fin.castSucc_lt_last _).ne
      · obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
        · simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Function.comp_apply] at h
          exact absurd h.symm (Fin.castSucc_lt_last _).ne
        · rfl,
     by
      intro b
      obtain (⟨j, rfl⟩ | rfl) := b.eq_castSucc_or_eq_last
      · exact ⟨Fin.castSucc (π.symm j), by
          simp [Fin.lastCases_castSucc, Function.comp_apply, π.apply_symm_apply]⟩
      · exact ⟨Fin.last n, by simp [Fin.lastCases_last]⟩⟩

theorem Equiv.Perm.extendFin_castSucc {n : ℕ}
    (π : Equiv.Perm (Fin n)) (i : Fin n) :
    Equiv.Perm.extendFin π (Fin.castSucc i) = Fin.castSucc (π i) := by
  change (Equiv.ofBijective _ _) (Fin.castSucc i) = _
  simp [Equiv.ofBijective_apply, Fin.lastCases_castSucc, Function.comp_apply]

theorem Equiv.Perm.extendFin_last {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    Equiv.Perm.extendFin π (Fin.last n) = Fin.last n := by
  change (Equiv.ofBijective _ _) (Fin.last n) = _
  simp [Equiv.ofBijective_apply, Fin.lastCases_last]

/-- The vertex map of a label extension of `F.relabel π` equals
    `ext.vertexMap ∘ π.extendFin`, where `ext` is the corresponding
    label extension of `F` at the same vertex. -/
theorem LabelExtension.vertexMap_relabel_eq {σ : FlagType} {F : Flag σ}
    (π : Equiv.Perm (Fin σ.size)) (v : Fin F.size)
    (hv : v ∉ Set.range F.embedding) :
    let ext : LabelExtension σ F := ⟨v, hv⟩
    let ext' : LabelExtension (σ.relabel π) (F.relabel π) :=
      ⟨v, by rw [Flag.relabel_embedding_range]; exact hv⟩
    ext'.vertexMap = ext.vertexMap ∘ Equiv.Perm.extendFin π := by
  funext i
  obtain (⟨j, rfl⟩ | rfl) := i.eq_castSucc_or_eq_last
  · simp only [LabelExtension.vertexMap, Fin.lastCases_castSucc, Function.comp_apply,
               Flag.relabel_embedding_apply, Equiv.Perm.extendFin_castSucc]
  · simp only [LabelExtension.vertexMap, Fin.lastCases_last, Function.comp_apply,
               Equiv.Perm.extendFin_last, FlagType.relabel]

/-- `IsLocalFlag` is invariant under label permutation.

    Proof by induction on unlabelledSize. IsBoundedDensity follows from the
    bijection on InducedEmbedding. For extensions, each label extension of
    `F.relabel π` at vertex `v` corresponds to an extension of `F` at `v`,
    and the extended flag/type equals `ext.extendedFlag.relabel π'` /
    `ext.extendedType.relabel π'` where `π' = π.extendFin`. -/
theorem IsLocalFlag_relabel (n : ℕ) :
    ∀ {σ : FlagType} {F : Flag σ} {𝒢 : GraphClass} {Δ : GraphParam}
      (π : Equiv.Perm (Fin σ.size)),
    F.unlabelledSize ≤ n →
    IsLocalFlag σ F 𝒢 Δ → IsLocalFlag (σ.relabel π) (F.relabel π) 𝒢 Δ := by
  induction n with
  | zero =>
    intro σ F 𝒢 Δ π hn h
    cases h with | intro _ _ _ _ hbd hext =>
    apply IsLocalFlag.intro _ _ _ _ (IsBoundedDensity_relabel π hbd)
    intro ext'
    exfalso
    have h1 : σ.size + 1 ≤ F.size := ext'.size_le
    have h2 := F.hsize
    unfold Flag.unlabelledSize at hn
    omega
  | succ n ih =>
    intro σ F 𝒢 Δ π hn h
    cases h with | intro _ _ _ _ hbd hext =>
    apply IsLocalFlag.intro _ _ _ _ (IsBoundedDensity_relabel π hbd)
    intro ext'
    -- ext' : LabelExtension (σ.relabel π) (F.relabel π) at vertex v
    -- Same vertex is unlabelled in F
    have hv_unlab : ext'.vertex ∉ Set.range F.embedding := by
      rw [← Flag.relabel_embedding_range F π]
      exact ext'.unlabelled
    let ext : LabelExtension σ F := ⟨ext'.vertex, hv_unlab⟩
    -- ext.extendedFlag is local (from h)
    have hext_local := hext ext
    -- Apply the IH with π' = Equiv.Perm.extendFin π
    have ih_result := ih (Equiv.Perm.extendFin π)
      (by unfold Flag.unlabelledSize at hn ⊢
          simp only [LabelExtension.extendedFlag, LabelExtension.extendedType]
          have h1 := ext.size_le
          omega)
      hext_local
    -- Type equality: ext'.extendedType = ext.extendedType.relabel (extendFin π)
    have htype_eq : ext'.extendedType = ext.extendedType.relabel (Equiv.Perm.extendFin π) := by
      change FlagType.mk (σ.size + 1) (F.graph.comap ext'.vertexMap) =
        FlagType.mk (σ.size + 1) ((F.graph.comap ext.vertexMap).comap (Equiv.Perm.extendFin π))
      congr 1
      rw [SimpleGraph.comap_comap]
      exact congr_arg (F.graph.comap ·)
        (LabelExtension.vertexMap_relabel_eq π ext'.vertex hv_unlab)
    -- Transport via IsLocalFlag_flagIso_gen
    exact IsLocalFlag_flagIso_gen
      (ext.extendedFlag.relabel (Equiv.Perm.extendFin π)).unlabelledSize
      htype_eq.symm le_rfl (RelIso.refl _)
      (fun i => by
        change ext.vertexMap (Equiv.Perm.extendFin π i) =
          ext'.vertexMap (Fin.cast (congrArg FlagType.size htype_eq.symm) i)
        have : Fin.cast (congrArg FlagType.size htype_eq.symm) i = i := Fin.ext rfl
        rw [this, LabelExtension.vertexMap_relabel_eq π ext'.vertex hv_unlab]
        rfl)
      ih_result


/-! ## Generic Flag Isomorphism -/

/-- Two generic flags are **isomorphic** if there exists an equivalence
    between their vertex sets that pulls back one structure to the other
    and commutes with the σ-embeddings. -/
def GenFlagIso {R : RelUniverse} (σ : GenFlagType R) (F F' : GenFlag R σ) : Prop :=
  ∃ (φ : Fin F.size ≃ Fin F'.size),
    R.comap φ F'.str = F.str ∧
    ∀ i : Fin σ.size, φ (F.embedding i) = F'.embedding i

theorem GenFlagIso.refl {R : RelUniverse} (σ : GenFlagType R) (F : GenFlag R σ) :
    GenFlagIso σ F F :=
  ⟨Equiv.refl _, by change R.comap id F.str = F.str; rw [R.comap_id], fun _ => rfl⟩

theorem GenFlagIso.symm {R : RelUniverse} {σ : GenFlagType R} {F F' : GenFlag R σ}
    (h : GenFlagIso σ F F') : GenFlagIso σ F' F := by
  obtain ⟨φ, hstr, hcompat⟩ := h
  refine ⟨φ.symm, ?_, fun i => ?_⟩
  · rw [← hstr, ← R.comap_comp, φ.self_comp_symm, R.comap_id]
  · simp [← hcompat i]

theorem GenFlagIso.trans {R : RelUniverse} {σ : GenFlagType R} {F F' F'' : GenFlag R σ}
    (h1 : GenFlagIso σ F F') (h2 : GenFlagIso σ F' F'') : GenFlagIso σ F F'' := by
  obtain ⟨φ₁, hstr₁, hcompat₁⟩ := h1
  obtain ⟨φ₂, hstr₂, hcompat₂⟩ := h2
  refine ⟨φ₁.trans φ₂, ?_, fun i => ?_⟩
  · change R.comap (⇑φ₂ ∘ ⇑φ₁) F''.str = F.str
    rw [R.comap_comp, hstr₂, hstr₁]
  · simp [Equiv.trans_apply, hcompat₁, hcompat₂]

instance genFlagSetoid {R : RelUniverse} (σ : GenFlagType R) : Setoid (GenFlag R σ) where
  r := GenFlagIso σ
  iseqv := ⟨GenFlagIso.refl σ, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

def GenFlagClass (R : RelUniverse) (σ : GenFlagType R) := Quotient (genFlagSetoid σ)

def GenFlagClass.mk {R : RelUniverse} {σ : GenFlagType R} (F : GenFlag R σ) :
    GenFlagClass R σ :=
  Quotient.mk (genFlagSetoid σ) F

noncomputable instance {R : RelUniverse} {σ : GenFlagType R} :
    DecidableEq (GenFlagClass R σ) :=
  Classical.decEq _

theorem genFlagIso_size_eq {R : RelUniverse} {σ : GenFlagType R} {F₁ F₂ : GenFlag R σ}
    (h : GenFlagIso σ F₁ F₂) : F₁.size = F₂.size := by
  obtain ⟨φ, _, _⟩ := h
  simpa using Fintype.card_congr φ

/-- Transport a generic induced embedding along a flag isomorphism. -/
def GenInducedEmbedding.mapIso {R : RelUniverse} {σ : GenFlagType R} {F₁ F₂ G : GenFlag R σ}
    (φ : Fin F₁.size ≃ Fin F₂.size)
    (hstr : R.comap φ F₂.str = F₁.str)
    (hcompat : ∀ i : Fin σ.size, φ (F₁.embedding i) = F₂.embedding i)
    (e : GenInducedEmbedding R σ F₂ G) : GenInducedEmbedding R σ F₁ G where
  toFun := e.toFun ∘ φ
  injective := e.injective.comp φ.injective
  isInduced := by rw [R.comap_comp, e.isInduced, hstr]
  compat i := by simp [Function.comp, hcompat, e.compat]

theorem genInducedCount_flagIso {R : RelUniverse} {σ : GenFlagType R} {F₁ F₂ G : GenFlag R σ}
    (h : GenFlagIso σ F₁ F₂) : genInducedCount R σ F₁ G = genInducedCount R σ F₂ G := by
  obtain ⟨φ, hstr, hcompat⟩ := h
  unfold genInducedCount
  apply Fintype.card_congr
  have hsymm : R.comap (⇑φ.symm) F₁.str = F₂.str := by
    rw [← hstr, ← R.comap_comp, φ.self_comp_symm, R.comap_id]
  have hcompat_symm : ∀ i, φ.symm (F₂.embedding i) = F₁.embedding i := by
    intro i; simp [← hcompat i]
  exact {
    toFun := GenInducedEmbedding.mapIso φ.symm hsymm hcompat_symm
    invFun := GenInducedEmbedding.mapIso φ hstr hcompat
    left_inv := fun e => by
      cases e
      simp only [GenInducedEmbedding.mapIso, GenInducedEmbedding.mk.injEq]
      ext x; simp [Function.comp]
    right_inv := fun e => by
      cases e
      simp only [GenInducedEmbedding.mapIso, GenInducedEmbedding.mk.injEq]
      ext x; simp [Function.comp]
  }

end Davey2024
