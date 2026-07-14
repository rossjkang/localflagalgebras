import DaveyThesis2024.CGraphBridge
import DaveyThesis2024.SdpFlags
import DaveyThesis2024.Extensions

-- The avgProd evaluation lemmas, eval identities, and σ-cone proofs all rely on

/-!
# SDP evaluation proofs

Bridge-dependent proofs for the pentagon conjecture SDP certificate.
These theorems require CGraphBridge (which provides `native_decide`-verified
numerical facts about flag automorphism counts and joint counts).

## Main results

* `F77_witness_emptyAutCount` — aut count of F77_witness.forget = 6
* `F77_witness_jointCount` — joint count of F77_witness = 2
* `avgProd_F77` — evaluation of the F7·F7 averaging product
* `hsq_eval_identity` — full h² evaluation identity
-/

namespace Davey2024

open Finset

set_option maxHeartbeats 800000 in
/-- Structural decomposition for csType7 joint embeddings of two size-4 flags.
    When genJointCount > 0, extracts named vertices, an equivalence φ : Fin G.size ≃ Fin 5,
    adjacency/colour preservation, and vertex covering. -/
theorem csType7_product_structure
    (F₁ F₂ : GenFlag CG2 csType7)
    (hF₁size : F₁.size = 4) (hF₂size : F₂.size = 4)
    (hF₁emb : ∀ i : Fin 3, (F₁.embedding i).val = i.val)
    (hF₂emb : ∀ i : Fin 3, (F₂.embedding i).val = i.val)
    (G : GenFlag CG2 csType7)
    (hjc : genJointCount CG2 csType7 F₁ F₂ G > 0) :
    G.size = 5 ∧
    ∃ (e₁ : GenInducedEmbedding CG2 csType7 F₁ G)
      (e₂ : GenInducedEmbedding CG2 csType7 F₂ G)
      (φ : Fin G.size ≃ Fin 5),
      -- φ maps type vertices to 0,1,2
      (∀ i : Fin 3, φ (G.embedding i) = Fin.castLE (by omega) i) ∧
      -- φ maps free vertices to 3,4
      (φ (e₁.toFun ⟨3, by omega⟩) = ⟨3, by omega⟩) ∧
      (φ (e₂.toFun ⟨3, by omega⟩) = ⟨4, by omega⟩) ∧
      -- e₁ maps type indices to G.embedding
      (∀ i : Fin 3, e₁.toFun ⟨i.val, by omega⟩ = G.embedding i) ∧
      -- e₂ maps type indices to G.embedding
      (∀ i : Fin 3, e₂.toFun ⟨i.val, by omega⟩ = G.embedding i) ∧
      -- Adjacency preservation via isInduced
      (∀ i j : Fin F₁.size, G.str.1.Adj (e₁.toFun i) (e₁.toFun j) ↔ F₁.str.1.Adj i j) ∧
      (∀ i j : Fin F₂.size, G.str.1.Adj (e₂.toFun i) (e₂.toFun j) ↔ F₂.str.1.Adj i j) ∧
      -- Colour preservation
      (∀ i : Fin F₁.size, G.str.2 (e₁.toFun i) = F₁.str.2 i) ∧
      (∀ i : Fin F₂.size, G.str.2 (e₂.toFun i) = F₂.str.2 i) ∧
      -- Free vertices are distinct
      (e₁.toFun ⟨3, by omega⟩ ≠ e₂.toFun ⟨3, by omega⟩) ∧
      -- Free vertices not in range(G.embedding)
      (e₁.toFun ⟨3, by omega⟩ ∉ Set.range G.embedding) ∧
      (e₂.toFun ⟨3, by omega⟩ ∉ Set.range G.embedding) ∧
      -- Covering: every vertex is one of the 5 named vertices
      (∀ v : Fin G.size,
        v = G.embedding ⟨0, by decide⟩ ∨ v = G.embedding ⟨1, by decide⟩ ∨
        v = G.embedding ⟨2, by decide⟩ ∨ v = e₁.toFun ⟨3, by omega⟩ ∨
        v = e₂.toFun ⟨3, by omega⟩) := by
  -- Step 1: Extract joint embedding witness
  have hjc' : 0 < genJointCount CG2 csType7 F₁ F₂ G := hjc
  unfold genJointCount at hjc'
  rw [Fintype.card_pos_iff] at hjc'
  obtain ⟨⟨⟨e₁, e₂⟩, hoverlap, hcovering⟩⟩ := hjc'
  -- Step 2: Derive G.size = 5 from covering/overlap
  have hGsize : G.size = 5 := by
    have hS₁ : (Finset.univ.image e₁.toFun).card = F₁.size := by
      rw [Finset.card_image_of_injective _ e₁.injective, Finset.card_univ, Fintype.card_fin]
    have hS₂ : (Finset.univ.image e₂.toFun).card = F₂.size := by
      rw [Finset.card_image_of_injective _ e₂.injective, Finset.card_univ, Fintype.card_fin]
    have hSσ : (Finset.univ.image G.embedding).card = csType7.size := by
      rw [Finset.card_image_of_injective _ G.embedding.injective, Finset.card_univ,
          Fintype.card_fin]
    simp only [csType7] at hSσ
    have hinter : Finset.univ.image e₁.toFun ∩ Finset.univ.image e₂.toFun =
        Finset.univ.image G.embedding := by
      ext i; simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩⟩
        obtain ⟨k, hk⟩ := (hoverlap i).mp ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩⟩
        exact ⟨k, hk⟩
      · rintro ⟨j, hj⟩
        obtain ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩ := (hoverlap i).mpr ⟨j, hj⟩
        exact ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩
    have hunion : Finset.univ.image e₁.toFun ∪ Finset.univ.image e₂.toFun = Finset.univ := by
      ext i; constructor
      · intro; exact Finset.mem_univ _
      · intro _; rw [Finset.mem_union]
        rcases hcovering i with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · left; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        · right; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hcard := Finset.card_union_add_card_inter
      (Finset.univ.image e₁.toFun) (Finset.univ.image e₂.toFun)
    rw [hunion] at hcard
    rw [hinter] at hcard
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  -- Step 3: Compat conditions — e maps type vertices to G.embedding
  have he₁_compat : ∀ k : Fin 3, e₁.toFun ⟨k.val, by omega⟩ = G.embedding k := by
    intro k
    have h := e₁.compat k
    have hemb : F₁.embedding k = ⟨k.val, by omega⟩ := Fin.ext (hF₁emb k)
    rw [hemb] at h; exact h
  have he₂_compat : ∀ k : Fin 3, e₂.toFun ⟨k.val, by omega⟩ = G.embedding k := by
    intro k
    have h := e₂.compat k
    have hemb : F₂.embedding k = ⟨k.val, by omega⟩ := Fin.ext (hF₂emb k)
    rw [hemb] at h; exact h
  -- Step 4: Free vertices e₁(3) and e₂(3) are not in range(G.embedding)
  have he₁_3_not_emb : e₁.toFun ⟨3, by omega⟩ ∉ Set.range G.embedding := by
    intro ⟨k, hk⟩
    have hk' := he₁_compat k
    have hinj := e₁.injective (hk'.trans hk)
    fin_cases k <;> simp [Fin.ext_iff] at hinj
  have he₂_3_not_emb : e₂.toFun ⟨3, by omega⟩ ∉ Set.range G.embedding := by
    intro ⟨k, hk⟩
    have hk' := he₂_compat k
    have hinj := e₂.injective (hk'.trans hk)
    fin_cases k <;> simp [Fin.ext_iff] at hinj
  -- e₁(3) ≠ e₂(3): overlap says in both ranges ↔ in range(G.embedding)
  have he_ne : e₁.toFun ⟨3, by omega⟩ ≠ e₂.toFun ⟨3, by omega⟩ := by
    intro heq
    have : e₁.toFun ⟨3, by omega⟩ ∈ Set.range G.embedding := by
      apply (hoverlap _).mp
      exact ⟨⟨⟨3, by omega⟩, rfl⟩, ⟨⟨3, by omega⟩, heq.symm⟩⟩
    exact he₁_3_not_emb this
  -- Step 5: Adjacency and colour from isInduced
  have hind₁ := e₁.isInduced
  have hind₂ := e₂.isInduced
  have hadj₁ : ∀ u v : Fin F₁.size, G.str.1.Adj (e₁.toFun u) (e₁.toFun v) ↔
      F₁.str.1.Adj u v := by
    intro u v
    have h := congr_arg Prod.fst hind₁
    simp only [colouredGraphUniverse] at h
    have : (G.str.1.comap e₁.toFun).Adj u v ↔ F₁.str.1.Adj u v := by rw [h]
    simpa [SimpleGraph.comap_adj] using this
  have hadj₂ : ∀ u v : Fin F₂.size, G.str.1.Adj (e₂.toFun u) (e₂.toFun v) ↔
      F₂.str.1.Adj u v := by
    intro u v
    have h := congr_arg Prod.fst hind₂
    simp only [colouredGraphUniverse] at h
    have : (G.str.1.comap e₂.toFun).Adj u v ↔ F₂.str.1.Adj u v := by rw [h]
    simpa [SimpleGraph.comap_adj] using this
  have hcol₁ : ∀ u : Fin F₁.size, G.str.2 (e₁.toFun u) = F₁.str.2 u := by
    intro u
    have h := congr_arg Prod.snd hind₁
    simp only [colouredGraphUniverse] at h
    exact congr_fun h u
  have hcol₂ : ∀ u : Fin F₂.size, G.str.2 (e₂.toFun u) = F₂.str.2 u := by
    intro u
    have h := congr_arg Prod.snd hind₂
    simp only [colouredGraphUniverse] at h
    exact congr_fun h u
  -- Step 6: Distinctness facts and covering
  have hemb_ne_01 : G.embedding ⟨0, by decide⟩ ≠ G.embedding ⟨1, by decide⟩ :=
    G.embedding.injective.ne (by simp [Fin.ext_iff])
  have hemb_ne_02 : G.embedding ⟨0, by decide⟩ ≠ G.embedding ⟨2, by decide⟩ :=
    G.embedding.injective.ne (by simp [Fin.ext_iff])
  have hemb_ne_12 : G.embedding ⟨1, by decide⟩ ≠ G.embedding ⟨2, by decide⟩ :=
    G.embedding.injective.ne (by simp [Fin.ext_iff])
  have he₁_3_ne_emb0 : e₁.toFun ⟨3, by omega⟩ ≠ G.embedding ⟨0, by decide⟩ :=
    fun h => he₁_3_not_emb ⟨⟨0, by decide⟩, h.symm⟩
  have he₁_3_ne_emb1 : e₁.toFun ⟨3, by omega⟩ ≠ G.embedding ⟨1, by decide⟩ :=
    fun h => he₁_3_not_emb ⟨⟨1, by decide⟩, h.symm⟩
  have he₁_3_ne_emb2 : e₁.toFun ⟨3, by omega⟩ ≠ G.embedding ⟨2, by decide⟩ :=
    fun h => he₁_3_not_emb ⟨⟨2, by decide⟩, h.symm⟩
  have he₂_3_ne_emb0 : e₂.toFun ⟨3, by omega⟩ ≠ G.embedding ⟨0, by decide⟩ :=
    fun h => he₂_3_not_emb ⟨⟨0, by decide⟩, h.symm⟩
  have he₂_3_ne_emb1 : e₂.toFun ⟨3, by omega⟩ ≠ G.embedding ⟨1, by decide⟩ :=
    fun h => he₂_3_not_emb ⟨⟨1, by decide⟩, h.symm⟩
  have he₂_3_ne_emb2 : e₂.toFun ⟨3, by omega⟩ ≠ G.embedding ⟨2, by decide⟩ :=
    fun h => he₂_3_not_emb ⟨⟨2, by decide⟩, h.symm⟩
  -- Covering
  have he₁_0 : e₁.toFun ⟨0, by omega⟩ = G.embedding ⟨0, by decide⟩ := he₁_compat ⟨0, by decide⟩
  have he₁_1 : e₁.toFun ⟨1, by omega⟩ = G.embedding ⟨1, by decide⟩ := he₁_compat ⟨1, by decide⟩
  have he₁_2 : e₁.toFun ⟨2, by omega⟩ = G.embedding ⟨2, by decide⟩ := he₁_compat ⟨2, by decide⟩
  have he₂_0 : e₂.toFun ⟨0, by omega⟩ = G.embedding ⟨0, by decide⟩ := he₂_compat ⟨0, by decide⟩
  have he₂_1 : e₂.toFun ⟨1, by omega⟩ = G.embedding ⟨1, by decide⟩ := he₂_compat ⟨1, by decide⟩
  have he₂_2 : e₂.toFun ⟨2, by omega⟩ = G.embedding ⟨2, by decide⟩ := he₂_compat ⟨2, by decide⟩
  have hcover : ∀ v : Fin G.size,
      v = G.embedding ⟨0, by decide⟩ ∨ v = G.embedding ⟨1, by decide⟩ ∨
      v = G.embedding ⟨2, by decide⟩ ∨ v = e₁.toFun ⟨3, by omega⟩ ∨
      v = e₂.toFun ⟨3, by omega⟩ := by
    intro v
    rcases hcovering v with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- j : Fin F₁.size with e₁.toFun j = v
      by_cases h0 : j.val = 0
      · left; rw [← hj, show j = ⟨0, by omega⟩ from Fin.ext h0, he₁_0]
      · by_cases h1 : j.val = 1
        · right; left; rw [← hj, show j = ⟨1, by omega⟩ from Fin.ext h1, he₁_1]
        · by_cases h2 : j.val = 2
          · right; right; left; rw [← hj, show j = ⟨2, by omega⟩ from Fin.ext h2, he₁_2]
          · right; right; right; left
            have : j.val = 3 := by omega
            rw [← hj, show j = ⟨3, by omega⟩ from Fin.ext this]
    · by_cases h0 : j.val = 0
      · left; rw [← hj, show j = ⟨0, by omega⟩ from Fin.ext h0, he₂_0]
      · by_cases h1 : j.val = 1
        · right; left; rw [← hj, show j = ⟨1, by omega⟩ from Fin.ext h1, he₂_1]
        · by_cases h2 : j.val = 2
          · right; right; left; rw [← hj, show j = ⟨2, by omega⟩ from Fin.ext h2, he₂_2]
          · right; right; right; right
            have : j.val = 3 := by omega
            rw [← hj, show j = ⟨3, by omega⟩ from Fin.ext this]
  -- Step 7: Construct the equivalence φ : Fin G.size ≃ Fin 5
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by omega⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by omega⟩ with hv4_def
  set fwd : Fin G.size → Fin 5 := fun v =>
    if v = v0 then 0
    else if v = v1 then 1
    else if v = v2 then 2
    else if v = v3 then 3
    else 4
    with hfwd_def
  have hfwd_v0 : fwd v0 = 0 := if_pos rfl
  have hfwd_v1 : fwd v1 = 1 := by
    show fwd v1 = 1; dsimp only [fwd]
    rw [if_neg (Ne.symm hemb_ne_01), if_pos rfl]
  have hfwd_v2 : fwd v2 = 2 := by
    show fwd v2 = 2; dsimp only [fwd]
    rw [if_neg (Ne.symm hemb_ne_02), if_neg (Ne.symm hemb_ne_12), if_pos rfl]
  have hfwd_v3 : fwd v3 = 3 := by
    show fwd v3 = 3; dsimp only [fwd]
    rw [if_neg he₁_3_ne_emb0, if_neg he₁_3_ne_emb1, if_neg he₁_3_ne_emb2, if_pos rfl]
  have hfwd_v4 : fwd v4 = 4 := by
    show fwd v4 = 4; dsimp only [fwd]
    rw [if_neg he₂_3_ne_emb0, if_neg he₂_3_ne_emb1, if_neg he₂_3_ne_emb2,
        if_neg (Ne.symm he_ne)]
  let inv : Fin 5 → Fin G.size := fun i =>
    if i = 0 then v0
    else if i = 1 then v1
    else if i = 2 then v2
    else if i = 3 then v3
    else v4
  have hinv_0 : inv 0 = v0 := if_pos rfl
  have hinv_1 : inv 1 = v1 := by
    show inv 1 = v1; dsimp only [inv]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
  have hinv_2 : inv 2 = v2 := by
    show inv 2 = v2; dsimp only [inv]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
  have hinv_3 : inv 3 = v3 := by
    show inv 3 = v3; dsimp only [inv]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
  have hinv_4 : inv 4 = v4 := by
    show inv 4 = v4; dsimp only [inv]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
  have hli : ∀ x, inv (fwd x) = x := by
    intro x
    rcases hcover x with rfl | rfl | rfl | rfl | rfl
    · rw [hfwd_v0, hinv_0]
    · rw [hfwd_v1, hinv_1]
    · rw [hfwd_v2, hinv_2]
    · rw [hfwd_v3, hinv_3]
    · rw [hfwd_v4, hinv_4]
  have hri : ∀ x, fwd (inv x) = x := by
    intro x; fin_cases x <;> simp only [] <;>
      first
      | (change fwd (inv 0) = 0; rw [hinv_0, hfwd_v0])
      | (change fwd (inv 1) = 1; rw [hinv_1, hfwd_v1])
      | (change fwd (inv 2) = 2; rw [hinv_2, hfwd_v2])
      | (change fwd (inv 3) = 3; rw [hinv_3, hfwd_v3])
      | (change fwd (inv 4) = 4; rw [hinv_4, hfwd_v4])
  let φ : Fin G.size ≃ Fin 5 := ⟨fwd, inv, hli, hri⟩
  -- Assemble the result
  refine ⟨hGsize, e₁, e₂, φ, ?_, ?_, ?_, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩
  · -- φ maps type vertices to 0,1,2
    intro i; fin_cases i <;> simp only [Fin.castLE] <;>
      first
      | (change fwd v0 = _; rw [hfwd_v0]; rfl)
      | (change fwd v1 = _; rw [hfwd_v1]; rfl)
      | (change fwd v2 = _; rw [hfwd_v2]; rfl)
  · -- φ maps e₁(3) to 3
    change fwd v3 = _; rw [hfwd_v3]; rfl
  · -- φ maps e₂(3) to 4
    change fwd v4 = _; rw [hfwd_v4]; rfl

/-- Generic helper for `_jid_nf` proofs at sizes (F.size = 5, σ.size = 3, F₁.size = F₂.size = 4).
    Given the three count witness lemmas, reduces `jid * nf` to a single arithmetic equality
    on `ℝ` over rational constants. Used by ~28 instances across the file. -/
theorem jid_nf_5_3_4_4 {σ : GenFlagType CG2} (F₁ F₂ F : GenFlag CG2 σ)
    (hF : F.size = 5) (hσ : σ.size = 3) (hF₁ : F₁.size = 4) (hF₂ : F₂.size = 4)
    {jc sac eac : ℕ}
    (hjc : genJointCount CG2 σ F₁ F₂ F = jc)
    (hsac : genFlagAutCount CG2 σ F = sac)
    (heac : genFlagAutCount CG2 (GenFlagType.empty CG2) F.forget = eac) :
    genJointInducedDensity CG2 σ F₁ F₂ F * genNormalisationFactor σ F =
      (eac : ℝ) * (jc : ℝ) / ((sac : ℝ) * 120) := by
  unfold genJointInducedDensity genNormalisationFactor
  rw [hjc, hsac, heac, hF, hσ, hF₁, hF₂,
    show Nat.choose (5 - 3) (4 - 3) = 2 from by norm_num,
    show Nat.choose (5 - 3 - (4 - 3)) (4 - 3) = 1 from by norm_num,
    show Nat.descFactorial 5 3 = 60 from by norm_num]
  push_cast; ring

/-- `genFlagAutCount CG2 (GenFlagType.empty CG2) F77_witness.forget = 6`.
    Aut group = S₃ on {0,3,4}, fixing {1,2}. Computationally verified via
    cInducedCount (tcGraph cF7 cF7 false) (tcGraph cF7 cF7 false) = 6 in CGraphBridge. -/
theorem F77_witness_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F77_witness.forget = 6 :=
  F77_witness_emptyAutCount_bridge

/-- `genJointCount CG2 csType7 cs1Flag7 cs1Flag7 F77_witness = 2`.
    Computationally verified via tcJointCount 3 cF7 cF7 (tcGraph cF7 cF7 false) = 2
    in CGraphBridge. Each GIE is determined by e(3) in {3,4}; overlap forces the
    two embeddings to use different values. -/
theorem F77_witness_jointCount :
    genJointCount CG2 csType7 cs1Flag7 cs1Flag7 F77_witness = 2 :=
  F77_witness_jointCount_bridge

-- The combined coefficient: genJointInducedDensity * genNormalisationFactor = 1/20.
theorem F77_witness_jid_nf :
    genJointInducedDensity CG2 csType7 cs1Flag7 cs1Flag7 F77_witness *
      genNormalisationFactor csType7 F77_witness = 1/20 := by
  rw [jid_nf_5_3_4_4 cs1Flag7 cs1Flag7 F77_witness rfl rfl rfl rfl
    F77_witness_jointCount F77_witness_sigmaAutCount F77_witness_emptyAutCount]
  norm_num

-- Key structural fact: if the joint count is positive and the forget is triangle-free,
-- the flag must be isomorphic to F77_witness.
-- Proof sketch: joint embeddings determine all edges except adj(e₁(3), e₂(3)),
-- which must be false (otherwise triangle), giving exactly F77_witness's structure.
-- Structural classification: positive joint count + triangle-free forget
-- implies typed isomorphism to F77_witness.
-- Joint embeddings determine all adjacencies except between the two free
-- vertices, and triangle-freeness forces that edge absent.
set_option maxHeartbeats 4000000 in
private theorem F77_unique_class_of_jc_pos_tri_free
    (G : GenFlag CG2 csType7)
    (hjc : genJointCount CG2 csType7 cs1Flag7 cs1Flag7 G > 0)
    (hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType7 G F77_witness := by
  -- Apply structural lemma
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType7_product_structure cs1Flag7 cs1Flag7 rfl rfl
      (by intro i; fin_cases i <;> simp [cs1Flag7, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs1Flag7, Fin.castSucc])
      G hjc
  -- Named vertex abbreviations
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs1Flag7.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs1Flag7.size; decide⟩ with hv4_def
  -- Compat aliases for named vertices
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  -- Triangle-freeness → adj(e₁(3), e₂(3)) = false
  have hno_adj_free : ¬G.str.1.Adj v3 v4 := by
    intro hadj
    apply hno_tri
    change ∃ u v w : Fin G.size,
      G.str.1.Adj u v ∧ G.str.1.Adj v w ∧ G.str.1.Adj u w
    refine ⟨e₁.toFun ⟨1, by decide⟩, v3, v4, ?_, ?_, ?_⟩
    · rw [hadj₁]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
    · exact hadj
    · rw [he₁_1, ← he₂_1]
      rw [hadj₂]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
  -- Construct the GenFlagIso
  -- φ values for named vertices (used in graph and colour components)
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  refine ⟨φ, ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · -- Graph component
      change F77_witness.str.1.comap (⇑φ) = G.str.1
      -- Collect adjacency facts
      have G_01 : G.str.1.Adj v0 v1 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
      have G_02 : G.str.1.Adj v0 v2 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
      have G_13 : G.str.1.Adj v1 v3 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
      have G_23 : G.str.1.Adj v2 v3 := by
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
      have G_14 : G.str.1.Adj v1 v4 := by
        rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
        rw [hadj₂]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
      have G_24 : G.str.1.Adj v2 v4 := by
        rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
        rw [hadj₂]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
      have G_n03 : ¬G.str.1.Adj v0 v3 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
        rw [hadj₁]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
      have G_n12 : ¬G.str.1.Adj v1 v2 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
      have G_n04 : ¬G.str.1.Adj v0 v4 := by
        rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
        rw [hadj₂]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
      have G_n34 : ¬G.str.1.Adj v3 v4 := hno_adj_free
      -- Prove graph equality by ext over all vertex pairs
      ext u w; simp only [SimpleGraph.comap_adj]
      have hF77 := @SimpleGraph.fromRel_adj (Fin 5)
      rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
        rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
        change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
        first
        | rw [hfwd_v0, hfwd_v1]
        | rw [hfwd_v0, hfwd_v2]
        | rw [hfwd_v0, hfwd_v3]
        | rw [hfwd_v0, hfwd_v4]
        | rw [hfwd_v0]
        | rw [hfwd_v1, hfwd_v0]
        | rw [hfwd_v1, hfwd_v2]
        | rw [hfwd_v1, hfwd_v3]
        | rw [hfwd_v1, hfwd_v4]
        | rw [hfwd_v1]
        | rw [hfwd_v2, hfwd_v0]
        | rw [hfwd_v2, hfwd_v1]
        | rw [hfwd_v2, hfwd_v3]
        | rw [hfwd_v2, hfwd_v4]
        | rw [hfwd_v2]
        | rw [hfwd_v3, hfwd_v0]
        | rw [hfwd_v3, hfwd_v1]
        | rw [hfwd_v3, hfwd_v2]
        | rw [hfwd_v3, hfwd_v4]
        | rw [hfwd_v3]
        | rw [hfwd_v4, hfwd_v0]
        | rw [hfwd_v4, hfwd_v1]
        | rw [hfwd_v4, hfwd_v2]
        | rw [hfwd_v4, hfwd_v3]
        | rw [hfwd_v4]) <;>
      all_goals (
        constructor <;> intro h
        · first
          | exact G_01 | exact G_01.symm
          | exact G_02 | exact G_02.symm
          | exact G_13 | exact G_13.symm
          | exact G_23 | exact G_23.symm
          | exact G_14 | exact G_14.symm
          | exact G_24 | exact G_24.symm
          | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
        · first
          | exact absurd h G_n03
          | exact absurd h (fun x => G_n03 x.symm)
          | exact absurd h G_n12
          | exact absurd h (fun x => G_n12 x.symm)
          | exact absurd h G_n04
          | exact absurd h (fun x => G_n04 x.symm)
          | exact absurd h G_n34
          | exact absurd h (fun x => G_n34 x.symm)
          | exact absurd h (fun x => x.ne rfl)
          | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
    · -- Colour component
      change F77_witness.str.2 ∘ (⇑φ) = G.str.2
      funext u
      change F77_witness.str.2 (φ u) = G.str.2 u
      rcases hcover u with rfl | rfl | rfl | rfl | rfl
      · -- v0
        rw [hfwd_v0]; simp only [F77_witness]
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs1Flag7]
      · -- v1
        rw [hfwd_v1]; simp only [F77_witness]
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs1Flag7]
      · -- v2
        rw [hfwd_v2]; simp only [F77_witness]
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs1Flag7]
      · -- v3
        rw [hfwd_v3]; simp only [F77_witness]
        rw [hcol₁]; simp [cs1Flag7]
      · -- v4
        rw [hfwd_v4]; simp only [F77_witness]
        rw [hcol₂]; simp [cs1Flag7]
  · -- Embedding compatibility: φ ∘ G.embedding = F77_witness.embedding
    intro i
    fin_cases i <;> simp only [F77_witness, Function.Embedding.coeFn_mk, Fin.castLE] <;>
      first
      | (change φ v0 = _; rw [hφ_emb ⟨0, by decide⟩]; rfl)
      | (change φ v1 = _; rw [hφ_emb ⟨1, by decide⟩]; rfl)
      | (change φ v2 = _; rw [hφ_emb ⟨2, by decide⟩]; rfl)

-- For any class other than F77_witness, the summand is 0.
-- Uses the general `avgProd_other_classes_zero_of_classification` with
-- `F77_unique_class_of_jc_pos_tri_free` as the classification lemma.
theorem avgProd_F77_other_classes_zero
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta)
    (cls : GenFlagClass CG2 csType7)
    (hne : cls ≠ GenFlagClass.mk F77_witness) :
    genJointInducedDensity CG2 csType7 cs1Flag7 cs1Flag7 cls.out *
      (genNormalisationFactor csType7 cls.out * phi.eval cls.out.forget) = 0 :=
  avgProd_other_classes_zero_of_classification phi csType7 cs1Flag7 cs1Flag7
    F77_witness cls hne F77_unique_class_of_jc_pos_tri_free

-- The F7*F7 averaged product evaluates to (1/20) * phi.eval flag34.
-- Uses general `avgProd_eval_single_witness` infrastructure:
--   witness = F77_witness, classification = F77_unique_class_of_jc_pos_tri_free,
--   numerical facts = F77_witness_jid_nf + genFlagAutCount_cs1Flag7 + F77_witness_forget_iso.
set_option maxHeartbeats 800000 in
theorem avgProd_F77
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd cs1Flag7 cs1Flag7) = (1/20 : ℝ) * phi.eval flag34 := by
  apply avgProd_eval_single_witness phi cs1Flag7 cs1Flag7 F77_witness flag34 (1/20) (by decide)
  · -- Witness membership in genClassesOfSize
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨F77_witness.str, F77_witness.embedding, F77_witness.isInduced⟩, rfl⟩
  · -- Summand value: aut⁻¹ * (jid * nf * eval) = (1/20) * eval flag34
    have haut : (genFlagAutCount CG2 csType7 cs1Flag7 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag7]; norm_num
    rw [haut, one_mul, inv_one, one_mul, ← mul_assoc, F77_witness_jid_nf]
    congr 1
    exact phi.eval_iso _ _ F77_witness_forget_iso
  · -- Other classes contribute 0
    exact fun cls hne => avgProd_F77_other_classes_zero phi cls hne

/-! ### F57: cs1Flag5 × cs1Flag7 → sdpFlag9 -/

theorem F57_witness_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F57_witness.forget = 2 :=
  F57_witness_emptyAutCount_bridge

theorem F57_witness_jointCount :
    genJointCount CG2 csType7 cs1Flag5 cs1Flag7 F57_witness = 1 :=
  F57_witness_jointCount_bridge

theorem F57_witness_jid_nf :
    genJointInducedDensity CG2 csType7 cs1Flag5 cs1Flag7 F57_witness *
      genNormalisationFactor csType7 F57_witness = 1/60 := by
  rw [jid_nf_5_3_4_4 cs1Flag5 cs1Flag7 F57_witness rfl rfl rfl rfl
    F57_witness_jointCount F57_witness_sigmaAutCount F57_witness_emptyAutCount]
  norm_num

set_option maxHeartbeats 4000000 in
private theorem F57_unique_class_of_jc_pos_tri_free
    (G : GenFlag CG2 csType7)
    (hjc : genJointCount CG2 csType7 cs1Flag5 cs1Flag7 G > 0)
    (hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType7 G F57_witness := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType7_product_structure cs1Flag5 cs1Flag7 rfl rfl
      (by intro i; fin_cases i <;> simp [cs1Flag5, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs1Flag7, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs1Flag5.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs1Flag7.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hno_adj_free : ¬G.str.1.Adj v3 v4 := by
    intro hadj; apply hno_tri
    change ∃ u v w : Fin G.size, G.str.1.Adj u v ∧ G.str.1.Adj v w ∧ G.str.1.Adj u w
    refine ⟨e₁.toFun ⟨2, by decide⟩, v3, v4, ?_, ?_, ?_⟩
    · rw [hadj₁]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
    · exact hadj
    · rw [he₁_2, ← he₂_2]; rw [hadj₂]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  refine ⟨φ, ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · change F57_witness.str.1.comap (⇑φ) = G.str.1
      have G_01 : G.str.1.Adj v0 v1 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
      have G_02 : G.str.1.Adj v0 v2 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
      have G_23 : G.str.1.Adj v2 v3 := by
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
      have G_14 : G.str.1.Adj v1 v4 := by
        rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
        rw [hadj₂]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
      have G_24 : G.str.1.Adj v2 v4 := by
        rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
        rw [hadj₂]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
      have G_n03 : ¬G.str.1.Adj v0 v3 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
        rw [hadj₁]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
      have G_n12 : ¬G.str.1.Adj v1 v2 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
      have G_n13 : ¬G.str.1.Adj v1 v3 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
      have G_n04 : ¬G.str.1.Adj v0 v4 := by
        rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
        rw [hadj₂]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
      have G_n34 : ¬G.str.1.Adj v3 v4 := hno_adj_free
      ext u w; simp only [SimpleGraph.comap_adj]
      rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
        rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
        change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
        first
        | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3]
        | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0] | rw [hfwd_v1, hfwd_v0]
        | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4]
        | rw [hfwd_v1] | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1]
        | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
        | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2]
        | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3] | rw [hfwd_v4, hfwd_v0]
        | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3]
        | rw [hfwd_v4]) <;>
      all_goals (
        constructor <;> intro h
        · first
          | exact G_01 | exact G_01.symm | exact G_02 | exact G_02.symm
          | exact G_23 | exact G_23.symm | exact G_14 | exact G_14.symm
          | exact G_24 | exact G_24.symm
          | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
        · first
          | exact absurd h G_n03 | exact absurd h (fun x => G_n03 x.symm)
          | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
          | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
          | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
          | exact absurd h G_n34 | exact absurd h (fun x => G_n34 x.symm)
          | exact absurd h (fun x => x.ne rfl)
          | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
    · change F57_witness.str.2 ∘ (⇑φ) = G.str.2
      funext u; change F57_witness.str.2 (φ u) = G.str.2 u
      rcases hcover u with rfl | rfl | rfl | rfl | rfl
      · rw [hfwd_v0]; simp only [F57_witness]
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs1Flag5]
      · rw [hfwd_v1]; simp only [F57_witness]
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs1Flag5]
      · rw [hfwd_v2]; simp only [F57_witness]
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs1Flag5]
      · rw [hfwd_v3]; simp only [F57_witness]; rw [hcol₁]; simp [cs1Flag5]
      · rw [hfwd_v4]; simp only [F57_witness]; rw [hcol₂]; simp [cs1Flag7]
  · intro i
    fin_cases i <;> simp only [F57_witness, Function.Embedding.coeFn_mk, Fin.castLE] <;>
      first
      | (change φ v0 = _; rw [hφ_emb ⟨0, by decide⟩]; rfl)
      | (change φ v1 = _; rw [hφ_emb ⟨1, by decide⟩]; rfl)
      | (change φ v2 = _; rw [hφ_emb ⟨2, by decide⟩]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd_F57
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd cs1Flag5 cs1Flag7) = (1/60 : ℝ) * phi.eval sdpFlag9 := by
  apply avgProd_eval_single_witness phi cs1Flag5 cs1Flag7 F57_witness sdpFlag9 (1/60) (by decide)
  · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨F57_witness.str, F57_witness.embedding, F57_witness.isInduced⟩, rfl⟩
  · have haut₁ : (genFlagAutCount CG2 csType7 cs1Flag5 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag5]; norm_num
    have haut₂ : (genFlagAutCount CG2 csType7 cs1Flag7 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag7]; norm_num
    rw [haut₁, haut₂, one_mul, inv_one, one_mul, ← mul_assoc, F57_witness_jid_nf]
    congr 1
    exact phi.eval_iso _ _ F57_witness_forget_iso
  · exact fun cls hne => avgProd_other_classes_zero_of_classification phi csType7 cs1Flag5 cs1Flag7
      F57_witness cls hne F57_unique_class_of_jc_pos_tri_free

/-! ### F44: cs1Flag4 × cs1Flag4 → flag25 -/

theorem F44_witness_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F44_witness.forget = 2 :=
  F44_witness_emptyAutCount_bridge

theorem F44_witness_jointCount :
    genJointCount CG2 csType7 cs1Flag4 cs1Flag4 F44_witness = 2 :=
  F44_witness_jointCount_bridge

theorem F44_witness_jid_nf :
    genJointInducedDensity CG2 csType7 cs1Flag4 cs1Flag4 F44_witness *
      genNormalisationFactor csType7 F44_witness = 1/60 := by
  rw [jid_nf_5_3_4_4 cs1Flag4 cs1Flag4 F44_witness rfl rfl rfl rfl
    F44_witness_jointCount F44_witness_sigmaAutCount F44_witness_emptyAutCount]
  norm_num

set_option maxHeartbeats 4000000 in
private theorem F44_unique_class_of_jc_pos_tri_free
    (G : GenFlag CG2 csType7)
    (hjc : genJointCount CG2 csType7 cs1Flag4 cs1Flag4 G > 0)
    (hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType7 G F44_witness := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType7_product_structure cs1Flag4 cs1Flag4 rfl rfl
      (by intro i; fin_cases i <;> simp [cs1Flag4, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs1Flag4, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs1Flag4.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs1Flag4.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hno_adj_free : ¬G.str.1.Adj v3 v4 := by
    intro hadj; apply hno_tri
    change ∃ u v w : Fin G.size, G.str.1.Adj u v ∧ G.str.1.Adj v w ∧ G.str.1.Adj u w
    refine ⟨e₁.toFun ⟨1, by decide⟩, v3, v4, ?_, ?_, ?_⟩
    · rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
    · exact hadj
    · rw [he₁_1, ← he₂_1]; rw [hadj₂]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  refine ⟨φ, ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · change F44_witness.str.1.comap (⇑φ) = G.str.1
      have G_01 : G.str.1.Adj v0 v1 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
      have G_02 : G.str.1.Adj v0 v2 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
      have G_13 : G.str.1.Adj v1 v3 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
      have G_14 : G.str.1.Adj v1 v4 := by
        rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
        rw [hadj₂]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
      have G_n03 : ¬G.str.1.Adj v0 v3 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
        rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
      have G_n12 : ¬G.str.1.Adj v1 v2 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
      have G_n23 : ¬G.str.1.Adj v2 v3 := by
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
      have G_n04 : ¬G.str.1.Adj v0 v4 := by
        rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
        rw [hadj₂]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
      have G_n24 : ¬G.str.1.Adj v2 v4 := by
        rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
        rw [hadj₂]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
      have G_n34 : ¬G.str.1.Adj v3 v4 := hno_adj_free
      ext u w; simp only [SimpleGraph.comap_adj]
      rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
        rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
        change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
        first
        | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3]
        | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0] | rw [hfwd_v1, hfwd_v0]
        | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4]
        | rw [hfwd_v1] | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1]
        | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
        | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2]
        | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3] | rw [hfwd_v4, hfwd_v0]
        | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3]
        | rw [hfwd_v4]) <;>
      all_goals (
        constructor <;> intro h
        · first
          | exact G_01 | exact G_01.symm | exact G_02 | exact G_02.symm
          | exact G_13 | exact G_13.symm | exact G_14 | exact G_14.symm
          | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
        · first
          | exact absurd h G_n03 | exact absurd h (fun x => G_n03 x.symm)
          | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
          | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
          | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
          | exact absurd h G_n24 | exact absurd h (fun x => G_n24 x.symm)
          | exact absurd h G_n34 | exact absurd h (fun x => G_n34 x.symm)
          | exact absurd h (fun x => x.ne rfl)
          | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
    · change F44_witness.str.2 ∘ (⇑φ) = G.str.2
      funext u; change F44_witness.str.2 (φ u) = G.str.2 u
      rcases hcover u with rfl | rfl | rfl | rfl | rfl
      · rw [hfwd_v0]; simp only [F44_witness]
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs1Flag4]
      · rw [hfwd_v1]; simp only [F44_witness]
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs1Flag4]
      · rw [hfwd_v2]; simp only [F44_witness]
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs1Flag4]
      · rw [hfwd_v3]; simp only [F44_witness]; rw [hcol₁]; simp [cs1Flag4]
      · rw [hfwd_v4]; simp only [F44_witness]; rw [hcol₂]; simp [cs1Flag4]
  · intro i
    fin_cases i <;> simp only [F44_witness, Function.Embedding.coeFn_mk, Fin.castLE] <;>
      first
      | (change φ v0 = _; rw [hφ_emb ⟨0, by decide⟩]; rfl)
      | (change φ v1 = _; rw [hφ_emb ⟨1, by decide⟩]; rfl)
      | (change φ v2 = _; rw [hφ_emb ⟨2, by decide⟩]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd_F44
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd cs1Flag4 cs1Flag4) = (1/60 : ℝ) * phi.eval flag25 := by
  apply avgProd_eval_single_witness phi cs1Flag4 cs1Flag4 F44_witness flag25 (1/60) (by decide)
  · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨F44_witness.str, F44_witness.embedding, F44_witness.isInduced⟩, rfl⟩
  · have haut : (genFlagAutCount CG2 csType7 cs1Flag4 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag4]; norm_num
    rw [haut, one_mul, inv_one, one_mul, ← mul_assoc, F44_witness_jid_nf]
    congr 1
    exact phi.eval_iso _ _ F44_witness_forget_iso
  · exact fun cls hne => avgProd_other_classes_zero_of_classification phi csType7 cs1Flag4 cs1Flag4
      F44_witness cls hne F44_unique_class_of_jc_pos_tri_free

/-! ### F47: cs1Flag4 × cs1Flag7 → flag15 -/

theorem F47_witness_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F47_witness.forget = 2 :=
  F47_witness_emptyAutCount_bridge

theorem F47_witness_jointCount :
    genJointCount CG2 csType7 cs1Flag4 cs1Flag7 F47_witness = 1 :=
  F47_witness_jointCount_bridge

theorem F47_witness_jid_nf :
    genJointInducedDensity CG2 csType7 cs1Flag4 cs1Flag7 F47_witness *
      genNormalisationFactor csType7 F47_witness = 1/60 := by
  rw [jid_nf_5_3_4_4 cs1Flag4 cs1Flag7 F47_witness rfl rfl rfl rfl
    F47_witness_jointCount F47_witness_sigmaAutCount F47_witness_emptyAutCount]
  norm_num

set_option maxHeartbeats 4000000 in
private theorem F47_unique_class_of_jc_pos_tri_free
    (G : GenFlag CG2 csType7)
    (hjc : genJointCount CG2 csType7 cs1Flag4 cs1Flag7 G > 0)
    (hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType7 G F47_witness := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType7_product_structure cs1Flag4 cs1Flag7 rfl rfl
      (by intro i; fin_cases i <;> simp [cs1Flag4, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs1Flag7, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs1Flag4.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs1Flag7.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hno_adj_free : ¬G.str.1.Adj v3 v4 := by
    intro hadj; apply hno_tri
    change ∃ u v w : Fin G.size, G.str.1.Adj u v ∧ G.str.1.Adj v w ∧ G.str.1.Adj u w
    refine ⟨e₁.toFun ⟨1, by decide⟩, v3, v4, ?_, ?_, ?_⟩
    · rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
    · exact hadj
    · rw [he₁_1, ← he₂_1]; rw [hadj₂]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  refine ⟨φ, ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · change F47_witness.str.1.comap (⇑φ) = G.str.1
      have G_01 : G.str.1.Adj v0 v1 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
      have G_02 : G.str.1.Adj v0 v2 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
      have G_13 : G.str.1.Adj v1 v3 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
      have G_14 : G.str.1.Adj v1 v4 := by
        rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
        rw [hadj₂]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
      have G_24 : G.str.1.Adj v2 v4 := by
        rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
        rw [hadj₂]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
      have G_n03 : ¬G.str.1.Adj v0 v3 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
        rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
      have G_n12 : ¬G.str.1.Adj v1 v2 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
      have G_n23 : ¬G.str.1.Adj v2 v3 := by
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
      have G_n04 : ¬G.str.1.Adj v0 v4 := by
        rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
        rw [hadj₂]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
      have G_n34 : ¬G.str.1.Adj v3 v4 := hno_adj_free
      ext u w; simp only [SimpleGraph.comap_adj]
      rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
        rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
        change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
        first
        | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3]
        | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0] | rw [hfwd_v1, hfwd_v0]
        | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4]
        | rw [hfwd_v1] | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1]
        | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
        | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2]
        | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3] | rw [hfwd_v4, hfwd_v0]
        | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3]
        | rw [hfwd_v4]) <;>
      all_goals (
        constructor <;> intro h
        · first
          | exact G_01 | exact G_01.symm | exact G_02 | exact G_02.symm
          | exact G_13 | exact G_13.symm | exact G_14 | exact G_14.symm
          | exact G_24 | exact G_24.symm
          | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
        · first
          | exact absurd h G_n03 | exact absurd h (fun x => G_n03 x.symm)
          | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
          | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
          | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
          | exact absurd h G_n34 | exact absurd h (fun x => G_n34 x.symm)
          | exact absurd h (fun x => x.ne rfl)
          | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
    · change F47_witness.str.2 ∘ (⇑φ) = G.str.2
      funext u; change F47_witness.str.2 (φ u) = G.str.2 u
      rcases hcover u with rfl | rfl | rfl | rfl | rfl
      · rw [hfwd_v0]; simp only [F47_witness]
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs1Flag4]
      · rw [hfwd_v1]; simp only [F47_witness]
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs1Flag4]
      · rw [hfwd_v2]; simp only [F47_witness]
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs1Flag4]
      · rw [hfwd_v3]; simp only [F47_witness]; rw [hcol₁]; simp [cs1Flag4]
      · rw [hfwd_v4]; simp only [F47_witness]; rw [hcol₂]; simp [cs1Flag7]
  · intro i
    fin_cases i <;> simp only [F47_witness, Function.Embedding.coeFn_mk, Fin.castLE] <;>
      first
      | (change φ v0 = _; rw [hφ_emb ⟨0, by decide⟩]; rfl)
      | (change φ v1 = _; rw [hφ_emb ⟨1, by decide⟩]; rfl)
      | (change φ v2 = _; rw [hφ_emb ⟨2, by decide⟩]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd_F47
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd cs1Flag4 cs1Flag7) = (1/60 : ℝ) * phi.eval flag15 := by
  apply avgProd_eval_single_witness phi cs1Flag4 cs1Flag7 F47_witness flag15 (1/60) (by decide)
  · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨F47_witness.str, F47_witness.embedding, F47_witness.isInduced⟩, rfl⟩
  · have haut₁ : (genFlagAutCount CG2 csType7 cs1Flag4 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag4]; norm_num
    have haut₂ : (genFlagAutCount CG2 csType7 cs1Flag7 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag7]; norm_num
    rw [haut₁, haut₂, one_mul, inv_one, one_mul, ← mul_assoc, F47_witness_jid_nf]
    congr 1
    exact phi.eval_iso _ _ F47_witness_forget_iso
  · exact fun cls hne => avgProd_other_classes_zero_of_classification phi csType7 cs1Flag4 cs1Flag7
      F47_witness cls hne F47_unique_class_of_jc_pos_tri_free

/-! ### F55: cs1Flag5 × cs1Flag5 → flag16 -/

theorem F55_witness_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F55_witness.forget = 2 :=
  F55_witness_emptyAutCount_bridge

theorem F55_witness_jointCount :
    genJointCount CG2 csType7 cs1Flag5 cs1Flag5 F55_witness = 2 :=
  F55_witness_jointCount_bridge

theorem F55_witness_jid_nf :
    genJointInducedDensity CG2 csType7 cs1Flag5 cs1Flag5 F55_witness *
      genNormalisationFactor csType7 F55_witness = 1/60 := by
  rw [jid_nf_5_3_4_4 cs1Flag5 cs1Flag5 F55_witness rfl rfl rfl rfl
    F55_witness_jointCount F55_witness_sigmaAutCount F55_witness_emptyAutCount]
  norm_num

set_option maxHeartbeats 4000000 in
private theorem F55_unique_class_of_jc_pos_tri_free
    (G : GenFlag CG2 csType7)
    (hjc : genJointCount CG2 csType7 cs1Flag5 cs1Flag5 G > 0)
    (hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType7 G F55_witness := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType7_product_structure cs1Flag5 cs1Flag5 rfl rfl
      (by intro i; fin_cases i <;> simp [cs1Flag5, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs1Flag5, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs1Flag5.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs1Flag5.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hno_adj_free : ¬G.str.1.Adj v3 v4 := by
    intro hadj; apply hno_tri
    change ∃ u v w : Fin G.size, G.str.1.Adj u v ∧ G.str.1.Adj v w ∧ G.str.1.Adj u w
    refine ⟨e₁.toFun ⟨2, by decide⟩, v3, v4, ?_, ?_, ?_⟩
    · rw [hadj₁]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
    · exact hadj
    · rw [he₁_2, ← he₂_2]; rw [hadj₂]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  refine ⟨φ, ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · change F55_witness.str.1.comap (⇑φ) = G.str.1
      have G_01 : G.str.1.Adj v0 v1 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
      have G_02 : G.str.1.Adj v0 v2 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
      have G_23 : G.str.1.Adj v2 v3 := by
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
      have G_24 : G.str.1.Adj v2 v4 := by
        rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
        rw [hadj₂]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
      have G_n03 : ¬G.str.1.Adj v0 v3 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
        rw [hadj₁]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
      have G_n12 : ¬G.str.1.Adj v1 v2 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
      have G_n13 : ¬G.str.1.Adj v1 v3 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
      have G_n04 : ¬G.str.1.Adj v0 v4 := by
        rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
        rw [hadj₂]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
      have G_n14 : ¬G.str.1.Adj v1 v4 := by
        rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
        rw [hadj₂]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
      have G_n34 : ¬G.str.1.Adj v3 v4 := hno_adj_free
      ext u w; simp only [SimpleGraph.comap_adj]
      rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
        rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
        change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
        first
        | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3]
        | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0] | rw [hfwd_v1, hfwd_v0]
        | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4]
        | rw [hfwd_v1] | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1]
        | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
        | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2]
        | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3] | rw [hfwd_v4, hfwd_v0]
        | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3]
        | rw [hfwd_v4]) <;>
      all_goals (
        constructor <;> intro h
        · first
          | exact G_01 | exact G_01.symm | exact G_02 | exact G_02.symm
          | exact G_23 | exact G_23.symm | exact G_24 | exact G_24.symm
          | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
        · first
          | exact absurd h G_n03 | exact absurd h (fun x => G_n03 x.symm)
          | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
          | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
          | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
          | exact absurd h G_n14 | exact absurd h (fun x => G_n14 x.symm)
          | exact absurd h G_n34 | exact absurd h (fun x => G_n34 x.symm)
          | exact absurd h (fun x => x.ne rfl)
          | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
    · change F55_witness.str.2 ∘ (⇑φ) = G.str.2
      funext u; change F55_witness.str.2 (φ u) = G.str.2 u
      rcases hcover u with rfl | rfl | rfl | rfl | rfl
      · rw [hfwd_v0]; simp only [F55_witness]
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs1Flag5]
      · rw [hfwd_v1]; simp only [F55_witness]
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs1Flag5]
      · rw [hfwd_v2]; simp only [F55_witness]
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs1Flag5]
      · rw [hfwd_v3]; simp only [F55_witness]; rw [hcol₁]; simp [cs1Flag5]
      · rw [hfwd_v4]; simp only [F55_witness]; rw [hcol₂]; simp [cs1Flag5]
  · intro i
    fin_cases i <;> simp only [F55_witness, Function.Embedding.coeFn_mk, Fin.castLE] <;>
      first
      | (change φ v0 = _; rw [hφ_emb ⟨0, by decide⟩]; rfl)
      | (change φ v1 = _; rw [hφ_emb ⟨1, by decide⟩]; rfl)
      | (change φ v2 = _; rw [hφ_emb ⟨2, by decide⟩]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd_F55_eval
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd cs1Flag5 cs1Flag5) = (1/60 : ℝ) * phi.eval flag16 := by
  apply avgProd_eval_single_witness phi cs1Flag5 cs1Flag5 F55_witness flag16 (1/60) (by decide)
  · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨F55_witness.str, F55_witness.embedding, F55_witness.isInduced⟩, rfl⟩
  · have haut : (genFlagAutCount CG2 csType7 cs1Flag5 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag5]; norm_num
    rw [haut, one_mul, inv_one, one_mul, ← mul_assoc, F55_witness_jid_nf]
    congr 1
    exact phi.eval_iso _ _ F55_witness_forget_iso
  · exact fun cls hne => avgProd_other_classes_zero_of_classification phi csType7 cs1Flag5 cs1Flag5
      F55_witness cls hne F55_unique_class_of_jc_pos_tri_free

/-! ### F45: cs1Flag4 × cs1Flag5 → sdpFlag37 + sdpFlag55 -/

theorem F45_witness_false_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F45_witness_false.forget = 1 :=
  F45_witness_false_emptyAutCount_bridge

theorem F45_witness_false_jointCount :
    genJointCount CG2 csType7 cs1Flag4 cs1Flag5 F45_witness_false = 1 :=
  F45_witness_false_jointCount_bridge

theorem F45_witness_true_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F45_witness_true.forget = 2 :=
  F45_witness_true_emptyAutCount_bridge

theorem F45_witness_true_jointCount :
    genJointCount CG2 csType7 cs1Flag4 cs1Flag5 F45_witness_true = 1 :=
  F45_witness_true_jointCount_bridge

-- jid * nf for F45_witness_false: (1/2) * (1/(1*60)) = 1/120
theorem F45_witness_false_jid_nf :
    genJointInducedDensity CG2 csType7 cs1Flag4 cs1Flag5 F45_witness_false *
      genNormalisationFactor csType7 F45_witness_false = 1/120 := by
  rw [jid_nf_5_3_4_4 cs1Flag4 cs1Flag5 F45_witness_false rfl rfl rfl rfl
    F45_witness_false_jointCount F45_witness_false_sigmaAutCount
    F45_witness_false_emptyAutCount]
  norm_num

-- jid * nf for F45_witness_true: (1/2) * (2/(1*60)) = 1/60
theorem F45_witness_true_jid_nf :
    genJointInducedDensity CG2 csType7 cs1Flag4 cs1Flag5 F45_witness_true *
      genNormalisationFactor csType7 F45_witness_true = 1/60 := by
  rw [jid_nf_5_3_4_4 cs1Flag4 cs1Flag5 F45_witness_true rfl rfl rfl rfl
    F45_witness_true_jointCount F45_witness_true_sigmaAutCount
    F45_witness_true_emptyAutCount]
  norm_num

-- Classification: jc > 0 + triangle-free → iso to F45_witness_false or F45_witness_true.
-- The two embeddings determine all edges except adj(e₁(3), e₂(3)).
-- Both values of that Boolean give triangle-free graphs.
set_option maxHeartbeats 8000000 in
private theorem F45_two_classes_of_jc_pos_tri_free
    (G : GenFlag CG2 csType7)
    (hjc : genJointCount CG2 csType7 cs1Flag4 cs1Flag5 G > 0)
    (_hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType7 G F45_witness_false ∨ GenFlagIso csType7 G F45_witness_true := by
  -- Step 1: Extract joint embedding witness
  have hjc' : 0 < genJointCount CG2 csType7 cs1Flag4 cs1Flag5 G := hjc
  unfold genJointCount at hjc'
  rw [Fintype.card_pos_iff] at hjc'
  obtain ⟨⟨⟨e₁, e₂⟩, hoverlap, hcovering⟩⟩ := hjc'
  -- Step 2: Derive G.size = 5
  have hGsize : G.size = 5 := by
    have hS₁ : (Finset.univ.image e₁.toFun).card = cs1Flag4.size := by
      rw [Finset.card_image_of_injective _ e₁.injective, Finset.card_univ, Fintype.card_fin]
    have hS₂ : (Finset.univ.image e₂.toFun).card = cs1Flag5.size := by
      rw [Finset.card_image_of_injective _ e₂.injective, Finset.card_univ, Fintype.card_fin]
    have hSσ : (Finset.univ.image G.embedding).card = csType7.size := by
      rw [Finset.card_image_of_injective _ G.embedding.injective, Finset.card_univ,
          Fintype.card_fin]
    simp only [cs1Flag4, cs1Flag5, csType7] at hS₁ hS₂ hSσ
    have hinter : Finset.univ.image e₁.toFun ∩ Finset.univ.image e₂.toFun =
        Finset.univ.image G.embedding := by
      ext i; simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩⟩
        exact (hoverlap i).mp ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩⟩
      · rintro ⟨j, hj⟩
        exact (hoverlap i).mpr ⟨j, hj⟩
    have hunion : Finset.univ.image e₁.toFun ∪ Finset.univ.image e₂.toFun = Finset.univ := by
      ext i; constructor
      · intro; exact Finset.mem_univ _
      · intro _; rw [Finset.mem_union]
        rcases hcovering i with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · left; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        · right; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hcard := Finset.card_union_add_card_inter
      (Finset.univ.image e₁.toFun) (Finset.univ.image e₂.toFun)
    rw [hunion, hS₁, hS₂] at hcard
    rw [hinter] at hcard
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  -- Step 3: Compat conditions
  have he₁_0 : e₁.toFun ⟨0, by decide⟩ = G.embedding ⟨0, by decide⟩ := by
    have := e₁.compat ⟨0, by decide⟩
    simp only [cs1Flag4, Function.Embedding.coeFn_mk, Fin.castSucc] at this; exact this
  have he₁_1 : e₁.toFun ⟨1, by decide⟩ = G.embedding ⟨1, by decide⟩ := by
    have := e₁.compat ⟨1, by decide⟩
    simp only [cs1Flag4, Function.Embedding.coeFn_mk, Fin.castSucc] at this; exact this
  have he₁_2 : e₁.toFun ⟨2, by decide⟩ = G.embedding ⟨2, by decide⟩ := by
    have := e₁.compat ⟨2, by decide⟩
    simp only [cs1Flag4, Function.Embedding.coeFn_mk, Fin.castSucc] at this; exact this
  have he₂_0 : e₂.toFun ⟨0, by decide⟩ = G.embedding ⟨0, by decide⟩ := by
    have := e₂.compat ⟨0, by decide⟩
    simp only [cs1Flag5, Function.Embedding.coeFn_mk, Fin.castSucc] at this; exact this
  have he₂_1 : e₂.toFun ⟨1, by decide⟩ = G.embedding ⟨1, by decide⟩ := by
    have := e₂.compat ⟨1, by decide⟩
    simp only [cs1Flag5, Function.Embedding.coeFn_mk, Fin.castSucc] at this; exact this
  have he₂_2 : e₂.toFun ⟨2, by decide⟩ = G.embedding ⟨2, by decide⟩ := by
    have := e₂.compat ⟨2, by decide⟩
    simp only [cs1Flag5, Function.Embedding.coeFn_mk, Fin.castSucc] at this; exact this
  -- Step 4: Free vertices not in range(G.embedding), and distinct
  have he₁_3_not_emb : e₁.toFun ⟨3, by decide⟩ ∉ Set.range G.embedding := by
    intro ⟨k, hk⟩
    have hk' := e₁.compat k
    simp only [cs1Flag4, Function.Embedding.coeFn_mk, Fin.castSucc] at hk'
    have hinj := e₁.injective (hk'.trans hk)
    fin_cases k <;> simp [Fin.ext_iff] at hinj
  have he₂_3_not_emb : e₂.toFun ⟨3, by decide⟩ ∉ Set.range G.embedding := by
    intro ⟨k, hk⟩
    have hk' := e₂.compat k
    simp only [cs1Flag5, Function.Embedding.coeFn_mk, Fin.castSucc] at hk'
    have hinj := e₂.injective (hk'.trans hk)
    fin_cases k <;> simp [Fin.ext_iff] at hinj
  have he_ne : e₁.toFun ⟨3, by decide⟩ ≠ e₂.toFun ⟨3, by decide⟩ := by
    intro heq
    have : e₁.toFun ⟨3, by decide⟩ ∈ Set.range G.embedding := by
      apply (hoverlap _).mp
      exact ⟨⟨⟨3, by decide⟩, rfl⟩, ⟨⟨3, by decide⟩, heq.symm⟩⟩
    exact he₁_3_not_emb this
  -- Step 5: Adjacency/colour from isInduced
  have hind₁ := e₁.isInduced
  have hind₂ := e₂.isInduced
  have hadj₁ : ∀ u v : Fin 4, G.str.1.Adj (e₁.toFun u) (e₁.toFun v) ↔
      cs1Flag4.str.1.Adj u v := by
    intro u v
    have h := congr_arg Prod.fst hind₁
    simp only [colouredGraphUniverse] at h
    have : (G.str.1.comap e₁.toFun).Adj u v ↔ cs1Flag4.str.1.Adj u v := by rw [h]
    simpa [SimpleGraph.comap_adj] using this
  have hadj₂ : ∀ u v : Fin 4, G.str.1.Adj (e₂.toFun u) (e₂.toFun v) ↔
      cs1Flag5.str.1.Adj u v := by
    intro u v
    have h := congr_arg Prod.fst hind₂
    simp only [colouredGraphUniverse] at h
    have : (G.str.1.comap e₂.toFun).Adj u v ↔ cs1Flag5.str.1.Adj u v := by rw [h]
    simpa [SimpleGraph.comap_adj] using this
  have hcol₁ : ∀ u : Fin 4, G.str.2 (e₁.toFun u) = cs1Flag4.str.2 u := by
    intro u; exact congr_fun (congr_arg Prod.snd hind₁) u
  have hcol₂ : ∀ u : Fin 4, G.str.2 (e₂.toFun u) = cs1Flag5.str.2 u := by
    intro u; exact congr_fun (congr_arg Prod.snd hind₂) u
  -- Step 6: Distinctness and covering
  have hemb_ne_01 : G.embedding ⟨0, by decide⟩ ≠ G.embedding ⟨1, by decide⟩ :=
    G.embedding.injective.ne (by simp [Fin.ext_iff])
  have hemb_ne_02 : G.embedding ⟨0, by decide⟩ ≠ G.embedding ⟨2, by decide⟩ :=
    G.embedding.injective.ne (by simp [Fin.ext_iff])
  have hemb_ne_12 : G.embedding ⟨1, by decide⟩ ≠ G.embedding ⟨2, by decide⟩ :=
    G.embedding.injective.ne (by simp [Fin.ext_iff])
  have he₁_3_ne_emb0 : e₁.toFun ⟨3, by decide⟩ ≠ G.embedding ⟨0, by decide⟩ :=
    fun h => he₁_3_not_emb ⟨⟨0, by decide⟩, h.symm⟩
  have he₁_3_ne_emb1 : e₁.toFun ⟨3, by decide⟩ ≠ G.embedding ⟨1, by decide⟩ :=
    fun h => he₁_3_not_emb ⟨⟨1, by decide⟩, h.symm⟩
  have he₁_3_ne_emb2 : e₁.toFun ⟨3, by decide⟩ ≠ G.embedding ⟨2, by decide⟩ :=
    fun h => he₁_3_not_emb ⟨⟨2, by decide⟩, h.symm⟩
  have he₂_3_ne_emb0 : e₂.toFun ⟨3, by decide⟩ ≠ G.embedding ⟨0, by decide⟩ :=
    fun h => he₂_3_not_emb ⟨⟨0, by decide⟩, h.symm⟩
  have he₂_3_ne_emb1 : e₂.toFun ⟨3, by decide⟩ ≠ G.embedding ⟨1, by decide⟩ :=
    fun h => he₂_3_not_emb ⟨⟨1, by decide⟩, h.symm⟩
  have he₂_3_ne_emb2 : e₂.toFun ⟨3, by decide⟩ ≠ G.embedding ⟨2, by decide⟩ :=
    fun h => he₂_3_not_emb ⟨⟨2, by decide⟩, h.symm⟩
  have hcover : ∀ v : Fin G.size,
      v = G.embedding ⟨0, by decide⟩ ∨ v = G.embedding ⟨1, by decide⟩ ∨
      v = G.embedding ⟨2, by decide⟩ ∨ v = e₁.toFun ⟨3, by decide⟩ ∨
      v = e₂.toFun ⟨3, by decide⟩ := by
    intro v
    rcases hcovering v with ⟨j, hj⟩ | ⟨j, hj⟩
    · fin_cases j
      · left; rw [← hj, he₁_0]
      · right; left; rw [← hj, he₁_1]
      · right; right; left; rw [← hj, he₁_2]
      · right; right; right; left; exact hj.symm
    · fin_cases j
      · left; rw [← hj, he₂_0]
      · right; left; rw [← hj, he₂_1]
      · right; right; left; rw [← hj, he₂_2]
      · right; right; right; right; exact hj.symm
  -- Step 7: Set up named vertices and construct the isomorphism
  -- The key insight: everything is determined except adj(v3, v4)
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by decide⟩ with hv4_def
  -- Adjacency facts from the two embeddings
  -- cs1Flag4 edges: 0-1, 0-2, 1-3; non-edges: 0-3, 1-2, 2-3
  have G_01 : G.str.1.Adj v0 v1 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
  have G_02 : G.str.1.Adj v0 v2 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
  have G_13 : G.str.1.Adj v1 v3 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
  have G_24 : G.str.1.Adj v2 v4 := by
    rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
    rw [hadj₂]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
  -- Non-edges
  have G_n03 : ¬G.str.1.Adj v0 v3 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
    rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
  have G_n12 : ¬G.str.1.Adj v1 v2 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
  have G_n23 : ¬G.str.1.Adj v2 v3 := by
    rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
  have G_n04 : ¬G.str.1.Adj v0 v4 := by
    rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
    rw [hadj₂]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
  have G_n14 : ¬G.str.1.Adj v1 v4 := by
    rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
    rw [hadj₂]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
  -- Step 8: Branch on adj(v3, v4)
  -- Define forward map (same for both cases: identity on named vertices)
  set fwd : Fin G.size → Fin 5 := fun v =>
    if v = v0 then 0
    else if v = v1 then 1
    else if v = v2 then 2
    else if v = v3 then 3
    else 4
    with hfwd_def
  have hfwd_v0 : fwd v0 = 0 := if_pos rfl
  have hfwd_v1 : fwd v1 = 1 := by
    show fwd v1 = 1; dsimp only [fwd]
    rw [if_neg (Ne.symm hemb_ne_01), if_pos rfl]
  have hfwd_v2 : fwd v2 = 2 := by
    show fwd v2 = 2; dsimp only [fwd]
    rw [if_neg (Ne.symm hemb_ne_02), if_neg (Ne.symm hemb_ne_12), if_pos rfl]
  have hfwd_v3 : fwd v3 = 3 := by
    show fwd v3 = 3; dsimp only [fwd]
    rw [if_neg he₁_3_ne_emb0, if_neg he₁_3_ne_emb1, if_neg he₁_3_ne_emb2, if_pos rfl]
  have hfwd_v4 : fwd v4 = 4 := by
    show fwd v4 = 4; dsimp only [fwd]
    rw [if_neg he₂_3_ne_emb0, if_neg he₂_3_ne_emb1, if_neg he₂_3_ne_emb2,
        if_neg (Ne.symm he_ne)]
  -- Build inverse and equivalence
  by_cases h34 : G.str.1.Adj v3 v4
  · -- Case: adj(v3, v4) = true → iso to F45_witness_true
    right
    let inv : Fin 5 → Fin G.size := fun i =>
      if i = 0 then v0 else if i = 1 then v1 else if i = 2 then v2
      else if i = 3 then v3 else v4
    have hinv_0 : inv 0 = v0 := if_pos rfl
    have hinv_1 : inv 1 = v1 := by show inv 1 = v1; dsimp only [inv]; simp
    have hinv_2 : inv 2 = v2 := by show inv 2 = v2; dsimp only [inv]; simp [Fin.reduceEq]
    have hinv_3 : inv 3 = v3 := by show inv 3 = v3; dsimp only [inv]; simp [Fin.reduceEq]
    have hinv_4 : inv 4 = v4 := by show inv 4 = v4; dsimp only [inv]; simp [Fin.reduceEq]
    have hli : ∀ x, inv (fwd x) = x := by
      intro x; rcases hcover x with rfl | rfl | rfl | rfl | rfl
      · rw [hfwd_v0, hinv_0]
      · rw [hfwd_v1, hinv_1]
      · rw [hfwd_v2, hinv_2]
      · rw [hfwd_v3, hinv_3]
      · rw [hfwd_v4, hinv_4]
    have hri : ∀ x, fwd (inv x) = x := by
      intro x; fin_cases x <;> simp only [] <;>
        first
        | (change fwd (inv 0) = 0; rw [hinv_0, hfwd_v0])
        | (change fwd (inv 1) = 1; rw [hinv_1, hfwd_v1])
        | (change fwd (inv 2) = 2; rw [hinv_2, hfwd_v2])
        | (change fwd (inv 3) = 3; rw [hinv_3, hfwd_v3])
        | (change fwd (inv 4) = 4; rw [hinv_4, hfwd_v4])
    let φ : Fin G.size ≃ Fin 5 := ⟨fwd, inv, hli, hri⟩
    refine ⟨φ, ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change F45_witness_true.str.1.comap (⇑φ) = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (fwd _) (fwd _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3]
          | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3]
          | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3]
          | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2]
          | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2]
          | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm | exact G_02 | exact G_02.symm
            | exact G_13 | exact G_13.symm | exact G_24 | exact G_24.symm
            | exact h34 | exact h34.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n03 | exact absurd h (fun x => G_n03 x.symm)
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h G_n14 | exact absurd h (fun x => G_n14 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change F45_witness_true.str.2 ∘ (⇑φ) = G.str.2
        funext u; change F45_witness_true.str.2 (fwd u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, F45_witness_true] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs1Flag4])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs1Flag4])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs1Flag4])
          | (rw [hcol₁]; simp [cs1Flag4])
          | (rw [hcol₂]; simp [cs1Flag5])
    · intro i; fin_cases i <;>
        simp only [F45_witness_true, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change fwd v0 = _; rw [hfwd_v0]; rfl)
        | (change fwd v1 = _; rw [hfwd_v1]; rfl)
        | (change fwd v2 = _; rw [hfwd_v2]; rfl)
  · -- Case: adj(v3, v4) = false → iso to F45_witness_false
    left
    let inv : Fin 5 → Fin G.size := fun i =>
      if i = 0 then v0 else if i = 1 then v1 else if i = 2 then v2
      else if i = 3 then v3 else v4
    have hinv_0 : inv 0 = v0 := if_pos rfl
    have hinv_1 : inv 1 = v1 := by show inv 1 = v1; dsimp only [inv]; simp
    have hinv_2 : inv 2 = v2 := by show inv 2 = v2; dsimp only [inv]; simp [Fin.reduceEq]
    have hinv_3 : inv 3 = v3 := by show inv 3 = v3; dsimp only [inv]; simp [Fin.reduceEq]
    have hinv_4 : inv 4 = v4 := by show inv 4 = v4; dsimp only [inv]; simp [Fin.reduceEq]
    have hli : ∀ x, inv (fwd x) = x := by
      intro x; rcases hcover x with rfl | rfl | rfl | rfl | rfl
      · rw [hfwd_v0, hinv_0]
      · rw [hfwd_v1, hinv_1]
      · rw [hfwd_v2, hinv_2]
      · rw [hfwd_v3, hinv_3]
      · rw [hfwd_v4, hinv_4]
    have hri : ∀ x, fwd (inv x) = x := by
      intro x; fin_cases x <;> simp only [] <;>
        first
        | (change fwd (inv 0) = 0; rw [hinv_0, hfwd_v0])
        | (change fwd (inv 1) = 1; rw [hinv_1, hfwd_v1])
        | (change fwd (inv 2) = 2; rw [hinv_2, hfwd_v2])
        | (change fwd (inv 3) = 3; rw [hinv_3, hfwd_v3])
        | (change fwd (inv 4) = 4; rw [hinv_4, hfwd_v4])
    let φ : Fin G.size ≃ Fin 5 := ⟨fwd, inv, hli, hri⟩
    refine ⟨φ, ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change F45_witness_false.str.1.comap (⇑φ) = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (fwd _) (fwd _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3]
          | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3]
          | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3]
          | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2]
          | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2]
          | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm | exact G_02 | exact G_02.symm
            | exact G_13 | exact G_13.symm | exact G_24 | exact G_24.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n03 | exact absurd h (fun x => G_n03 x.symm)
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h G_n14 | exact absurd h (fun x => G_n14 x.symm)
            | exact absurd h h34 | exact absurd h (fun x => h34 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change F45_witness_false.str.2 ∘ (⇑φ) = G.str.2
        funext u; change F45_witness_false.str.2 (fwd u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, F45_witness_false] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs1Flag4])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs1Flag4])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs1Flag4])
          | (rw [hcol₁]; simp [cs1Flag4])
          | (rw [hcol₂]; simp [cs1Flag5])
    · intro i; fin_cases i <;>
        simp only [F45_witness_false, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change fwd v0 = _; rw [hfwd_v0]; rfl)
        | (change fwd v1 = _; rw [hfwd_v1]; rfl)
        | (change fwd v2 = _; rw [hfwd_v2]; rfl)

-- The final avgProd_F45 proof using dual-witness infrastructure.
set_option maxHeartbeats 800000 in
theorem avgProd_F45
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd cs1Flag4 cs1Flag5) =
      (1/120 : ℝ) * phi.eval sdpFlag37 + (1/60 : ℝ) * phi.eval sdpFlag55 := by
  apply avgProd_eval_dual_witness phi cs1Flag4 cs1Flag5
    F45_witness_false F45_witness_true sdpFlag37 sdpFlag55 (1/120) (1/60) (by decide)
    F45_witnesses_not_iso
  · -- w₁ membership
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨F45_witness_false.str, F45_witness_false.embedding, F45_witness_false.isInduced⟩, rfl⟩
  · -- w₂ membership
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨F45_witness_true.str, F45_witness_true.embedding, F45_witness_true.isInduced⟩, rfl⟩
  · -- Summand₁ = (1/120) * phi.eval sdpFlag37
    have haut4 : (genFlagAutCount CG2 csType7 cs1Flag4 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag4]; norm_num
    have haut5 : (genFlagAutCount CG2 csType7 cs1Flag5 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag5]; norm_num
    rw [haut4, haut5, one_mul, inv_one, one_mul, ← mul_assoc, F45_witness_false_jid_nf]
    congr 1
    exact phi.eval_iso _ _ F45_witness_false_forget_iso
  · -- Summand₂ = (1/60) * phi.eval sdpFlag55
    have haut4 : (genFlagAutCount CG2 csType7 cs1Flag4 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag4]; norm_num
    have haut5 : (genFlagAutCount CG2 csType7 cs1Flag5 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag5]; norm_num
    rw [haut4, haut5, one_mul, inv_one, one_mul, ← mul_assoc, F45_witness_true_jid_nf]
    congr 1
    exact phi.eval_iso _ _ F45_witness_true_forget_iso
  · -- Other classes contribute 0
    intro cls hne₁ hne₂
    exact avgProd_other_classes_zero_of_dual_classification phi csType7 cs1Flag4 cs1Flag5
      F45_witness_false F45_witness_true cls hne₁ hne₂
      F45_two_classes_of_jc_pos_tri_free

/-- Full h² evaluation identity in unlabelled density convention.
    240·eval(⟦h²⟧) = -4f₉ + 2f₁₅ + 4f₁₆ + f₂₅ + 3f₃₄ - 2f₃₇ - 4f₅₅
    (matches thesis 120·⟦h²⟧ expansion §3.6 with c₄=+1/2 in cs1_h). -/
theorem hsq_eval_identity
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    240 * phi.evalAlg (genAveragingAlg csType7 (cs1_h.mul cs1_h)) =
      -4 * phi.eval sdpFlag9 + 2 * phi.eval flag15 + 4 * phi.eval flag16 +
      phi.eval flag25 + 3 * phi.eval flag34
      - 2 * phi.eval sdpFlag37 - 4 * phi.eval sdpFlag55 := by
  rw [hsq_eval_distribute]
  rw [avgProd_F44 phi, avgProd_F45 phi, avgProd_F47 phi,
      avgProd_F55_eval phi, avgProd_F57 phi, avgProd_F77 phi]
  ring

/-! ### ℓ² per-product evaluation identities -/

/-! #### F33: cs1Flag3 × cs1Flag3 → flag5 (single witness) -/

theorem F33_witness_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F33_witness.forget = 6 :=
  F33_witness_emptyAutCount_bridge

theorem F33_witness_jointCount :
    genJointCount CG2 csType7 cs1Flag3 cs1Flag3 F33_witness = 2 :=
  F33_witness_jointCount_bridge

theorem F33_witness_jid_nf :
    genJointInducedDensity CG2 csType7 cs1Flag3 cs1Flag3 F33_witness *
      genNormalisationFactor csType7 F33_witness = 1/20 := by
  rw [jid_nf_5_3_4_4 cs1Flag3 cs1Flag3 F33_witness rfl rfl rfl rfl
    F33_witness_jointCount F33_witness_sigmaAutCount F33_witness_emptyAutCount]
  norm_num

-- F33: adj34=true creates triangle {0,3,4}, so only adj34=false is triangle-free.
set_option maxHeartbeats 4000000 in
private theorem F33_unique_class_of_jc_pos_tri_free
    (G : GenFlag CG2 csType7)
    (hjc : genJointCount CG2 csType7 cs1Flag3 cs1Flag3 G > 0)
    (hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType7 G F33_witness := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType7_product_structure cs1Flag3 cs1Flag3 rfl rfl
      (by intro i; fin_cases i <;> simp [cs1Flag3, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs1Flag3, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs1Flag3.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs1Flag3.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  -- adj(v3,v4) would create triangle {v0,v3,v4} since v3 adj v0 and v4 adj v0
  have hno_adj_free : ¬G.str.1.Adj v3 v4 := by
    intro hadj; apply hno_tri
    change ∃ u v w : Fin G.size, G.str.1.Adj u v ∧ G.str.1.Adj v w ∧ G.str.1.Adj u w
    refine ⟨e₁.toFun ⟨0, by decide⟩, v3, v4, ?_, ?_, ?_⟩
    · rw [hadj₁]; simp [cs1Flag3, SimpleGraph.fromRel_adj]
    · exact hadj
    · rw [he₁_0, ← he₂_0]; rw [hadj₂]; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  refine ⟨φ, ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · change F33_witness.str.1.comap (⇑φ) = G.str.1
      have G_01 : G.str.1.Adj v0 v1 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs1Flag3, SimpleGraph.fromRel_adj]
      have G_02 : G.str.1.Adj v0 v2 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs1Flag3, SimpleGraph.fromRel_adj]
      have G_03 : G.str.1.Adj v0 v3 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
        rw [hadj₁]; simp [cs1Flag3, SimpleGraph.fromRel_adj]
      have G_04 : G.str.1.Adj v0 v4 := by
        rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
        rw [hadj₂]; simp [cs1Flag3, SimpleGraph.fromRel_adj]
      have G_n12 : ¬G.str.1.Adj v1 v2 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        intro h; rw [hadj₁] at h; revert h; simp [cs1Flag3, SimpleGraph.fromRel_adj]
      have G_n13 : ¬G.str.1.Adj v1 v3 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        intro h; rw [hadj₁] at h; revert h; simp [cs1Flag3, SimpleGraph.fromRel_adj]
      have G_n23 : ¬G.str.1.Adj v2 v3 := by
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        intro h; rw [hadj₁] at h; revert h; simp [cs1Flag3, SimpleGraph.fromRel_adj]
      have G_n14 : ¬G.str.1.Adj v1 v4 := by
        rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
        intro h; rw [hadj₂] at h; revert h; simp [cs1Flag3, SimpleGraph.fromRel_adj]
      have G_n24 : ¬G.str.1.Adj v2 v4 := by
        rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
        intro h; rw [hadj₂] at h; revert h; simp [cs1Flag3, SimpleGraph.fromRel_adj]
      ext u w; simp only [SimpleGraph.comap_adj]
      rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
        rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
        change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
        first
        | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3]
        | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
        | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3]
        | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
        | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3]
        | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
        | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2]
        | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
        | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2]
        | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]) <;>
      all_goals (
        constructor <;> intro h
        · first
          | exact G_01 | exact G_01.symm | exact G_02 | exact G_02.symm
          | exact G_03 | exact G_03.symm | exact G_04 | exact G_04.symm
          | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
        · first
          | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
          | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
          | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
          | exact absurd h G_n14 | exact absurd h (fun x => G_n14 x.symm)
          | exact absurd h G_n24 | exact absurd h (fun x => G_n24 x.symm)
          | exact absurd h hno_adj_free | exact absurd h (fun x => hno_adj_free x.symm)
          | exact absurd h (fun x => x.ne rfl)
          | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
    · change F33_witness.str.2 ∘ (⇑φ) = G.str.2
      funext u; change F33_witness.str.2 (φ u) = G.str.2 u
      rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
        simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, F33_witness] <;>
        first
        | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs1Flag3])
        | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs1Flag3])
        | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs1Flag3])
        | (rw [hcol₁]; simp [cs1Flag3])
        | (rw [hcol₂]; simp [cs1Flag3])
  · intro i; fin_cases i <;>
      simp only [F33_witness, Function.Embedding.coeFn_mk, Fin.castLE] <;>
      first
      | (change φ v0 = _; rw [hfwd_v0]; rfl)
      | (change φ v1 = _; rw [hfwd_v1]; rfl)
      | (change φ v2 = _; rw [hfwd_v2]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd_F33
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd cs1Flag3 cs1Flag3) = (1/20 : ℝ) * phi.eval flag5 := by
  apply avgProd_eval_single_witness phi cs1Flag3 cs1Flag3 F33_witness flag5 (1/20) (by decide)
  · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨F33_witness.str, F33_witness.embedding, F33_witness.isInduced⟩, rfl⟩
  · have haut : (genFlagAutCount CG2 csType7 cs1Flag3 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag3]; norm_num
    rw [haut, one_mul, inv_one, one_mul, ← mul_assoc, F33_witness_jid_nf]
    congr 1
    exact phi.eval_iso _ _ F33_witness_forget_iso
  · exact fun cls hne => avgProd_other_classes_zero_of_classification phi csType7 cs1Flag3 cs1Flag3
      F33_witness cls hne F33_unique_class_of_jc_pos_tri_free

/-! #### F34: cs1Flag3 × cs1Flag4 → flag24 + flag12 (dual witness) -/

theorem F34_witness_false_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F34_witness_false.forget = 2 :=
  F34_witness_false_emptyAutCount_bridge

theorem F34_witness_false_jointCount :
    genJointCount CG2 csType7 cs1Flag3 cs1Flag4 F34_witness_false = 1 :=
  F34_witness_false_jointCount_bridge

theorem F34_witness_true_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F34_witness_true.forget = 1 :=
  F34_witness_true_emptyAutCount_bridge

theorem F34_witness_true_jointCount :
    genJointCount CG2 csType7 cs1Flag3 cs1Flag4 F34_witness_true = 1 :=
  F34_witness_true_jointCount_bridge

theorem F34_witness_false_jid_nf :
    genJointInducedDensity CG2 csType7 cs1Flag3 cs1Flag4 F34_witness_false *
      genNormalisationFactor csType7 F34_witness_false = 1/60 := by
  rw [jid_nf_5_3_4_4 cs1Flag3 cs1Flag4 F34_witness_false rfl rfl rfl rfl
    F34_witness_false_jointCount F34_witness_false_sigmaAutCount
    F34_witness_false_emptyAutCount]
  norm_num

theorem F34_witness_true_jid_nf :
    genJointInducedDensity CG2 csType7 cs1Flag3 cs1Flag4 F34_witness_true *
      genNormalisationFactor csType7 F34_witness_true = 1/120 := by
  rw [jid_nf_5_3_4_4 cs1Flag3 cs1Flag4 F34_witness_true rfl rfl rfl rfl
    F34_witness_true_jointCount F34_witness_true_sigmaAutCount
    F34_witness_true_emptyAutCount]
  norm_num

-- Both pastings are triangle-free, so classify by adj(v3,v4).
set_option maxHeartbeats 8000000 in
private theorem F34_two_classes_of_jc_pos_tri_free
    (G : GenFlag CG2 csType7)
    (hjc : genJointCount CG2 csType7 cs1Flag3 cs1Flag4 G > 0)
    (_hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType7 G F34_witness_false ∨ GenFlagIso csType7 G F34_witness_true := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType7_product_structure cs1Flag3 cs1Flag4 rfl rfl
      (by intro i; fin_cases i <;> simp [cs1Flag3, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs1Flag4, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs1Flag3.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs1Flag4.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  -- Extract the known edges from the flag types
  have G_01 : G.str.1.Adj v0 v1 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    rw [hadj₁]; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_02 : G.str.1.Adj v0 v2 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_03 : G.str.1.Adj v0 v3 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
    rw [hadj₁]; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_14 : G.str.1.Adj v1 v4 := by
    rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
    rw [hadj₂]; simp [cs1Flag4, SimpleGraph.fromRel_adj]
  have G_n12 : ¬G.str.1.Adj v1 v2 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    intro h; rw [hadj₁] at h; revert h; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_n13 : ¬G.str.1.Adj v1 v3 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    intro h; rw [hadj₁] at h; revert h; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_n23 : ¬G.str.1.Adj v2 v3 := by
    rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    intro h; rw [hadj₁] at h; revert h; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_n04 : ¬G.str.1.Adj v0 v4 := by
    rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
    intro h; rw [hadj₂] at h; revert h; simp [cs1Flag4, SimpleGraph.fromRel_adj]
  have G_n24 : ¬G.str.1.Adj v2 v4 := by
    rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
    intro h; rw [hadj₂] at h; revert h; simp [cs1Flag4, SimpleGraph.fromRel_adj]
  -- fwd/inv bijection
  let fwd : Fin G.size → Fin 5 := φ
  let inv : Fin 5 → Fin G.size := fun i =>
    if i = 0 then v0 else if i = 1 then v1 else if i = 2 then v2
    else if i = 3 then v3 else v4
  have hinv_0 : inv 0 = v0 := if_pos rfl
  have hinv_1 : inv 1 = v1 := by show inv 1 = v1; dsimp only [inv]; simp
  have hinv_2 : inv 2 = v2 := by show inv 2 = v2; dsimp only [inv]; simp [Fin.reduceEq]
  have hinv_3 : inv 3 = v3 := by show inv 3 = v3; dsimp only [inv]; simp [Fin.reduceEq]
  have hinv_4 : inv 4 = v4 := by show inv 4 = v4; dsimp only [inv]; simp [Fin.reduceEq]
  have hli : ∀ x, inv (fwd x) = x := by
    intro x; change inv (φ x) = x
    rcases hcover x with rfl | rfl | rfl | rfl | rfl
    · rw [hfwd_v0, hinv_0]
    · rw [hfwd_v1, hinv_1]
    · rw [hfwd_v2, hinv_2]
    · rw [hfwd_v3, hinv_3]
    · rw [hfwd_v4, hinv_4]
  have hri : ∀ x, fwd (inv x) = x := by
    intro x; change φ (inv x) = x
    fin_cases x <;> simp only [] <;>
      first
      | (change φ (inv 0) = 0; rw [hinv_0, hfwd_v0])
      | (change φ (inv 1) = 1; rw [hinv_1, hfwd_v1])
      | (change φ (inv 2) = 2; rw [hinv_2, hfwd_v2])
      | (change φ (inv 3) = 3; rw [hinv_3, hfwd_v3])
      | (change φ (inv 4) = 4; rw [hinv_4, hfwd_v4])
  let φ' : Fin G.size ≃ Fin 5 := ⟨fwd, inv, hli, hri⟩
  -- Split on adj(v3, v4)
  by_cases h34 : G.str.1.Adj v3 v4
  · -- Case: adj(v3, v4) = true → iso to F34_witness_true
    right
    refine ⟨φ', ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change F34_witness_true.str.1.comap (⇑φ') = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3]
          | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3]
          | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3]
          | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2]
          | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2]
          | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm | exact G_02 | exact G_02.symm
            | exact G_03 | exact G_03.symm | exact G_14 | exact G_14.symm
            | exact h34 | exact h34.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h G_n24 | exact absurd h (fun x => G_n24 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change F34_witness_true.str.2 ∘ (⇑φ') = G.str.2
        funext u; change F34_witness_true.str.2 (φ u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, F34_witness_true] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs1Flag3])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs1Flag3])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs1Flag3])
          | (rw [hcol₁]; simp [cs1Flag3])
          | (rw [hcol₂]; simp [cs1Flag4])
    · intro i; fin_cases i <;>
        simp only [F34_witness_true, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change φ v0 = _; rw [hfwd_v0]; rfl)
        | (change φ v1 = _; rw [hfwd_v1]; rfl)
        | (change φ v2 = _; rw [hfwd_v2]; rfl)
  · -- Case: adj(v3, v4) = false → iso to F34_witness_false
    left
    refine ⟨φ', ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change F34_witness_false.str.1.comap (⇑φ') = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3]
          | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3]
          | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3]
          | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2]
          | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2]
          | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm | exact G_02 | exact G_02.symm
            | exact G_03 | exact G_03.symm | exact G_14 | exact G_14.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h G_n24 | exact absurd h (fun x => G_n24 x.symm)
            | exact absurd h h34 | exact absurd h (fun x => h34 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change F34_witness_false.str.2 ∘ (⇑φ') = G.str.2
        funext u; change F34_witness_false.str.2 (φ u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, F34_witness_false] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs1Flag3])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs1Flag3])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs1Flag3])
          | (rw [hcol₁]; simp [cs1Flag3])
          | (rw [hcol₂]; simp [cs1Flag4])
    · intro i; fin_cases i <;>
        simp only [F34_witness_false, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change φ v0 = _; rw [hfwd_v0]; rfl)
        | (change φ v1 = _; rw [hfwd_v1]; rfl)
        | (change φ v2 = _; rw [hfwd_v2]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd_F34
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd cs1Flag3 cs1Flag4) =
      (1/60 : ℝ) * phi.eval flag24 + (1/120 : ℝ) * phi.eval flag12 := by
  apply avgProd_eval_dual_witness phi cs1Flag3 cs1Flag4
    F34_witness_false F34_witness_true flag24 flag12 (1/60) (1/120) (by decide)
    F34_witnesses_not_iso
  · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨F34_witness_false.str, F34_witness_false.embedding, F34_witness_false.isInduced⟩, rfl⟩
  · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨F34_witness_true.str, F34_witness_true.embedding, F34_witness_true.isInduced⟩, rfl⟩
  · have haut3 : (genFlagAutCount CG2 csType7 cs1Flag3 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag3]; norm_num
    have haut4 : (genFlagAutCount CG2 csType7 cs1Flag4 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag4]; norm_num
    rw [haut3, haut4, one_mul, inv_one, one_mul, ← mul_assoc, F34_witness_false_jid_nf]
    congr 1
    exact phi.eval_iso _ _ F34_witness_false_forget_iso
  · have haut3 : (genFlagAutCount CG2 csType7 cs1Flag3 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag3]; norm_num
    have haut4 : (genFlagAutCount CG2 csType7 cs1Flag4 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag4]; norm_num
    rw [haut3, haut4, one_mul, inv_one, one_mul, ← mul_assoc, F34_witness_true_jid_nf]
    congr 1
    exact phi.eval_iso _ _ F34_witness_true_forget_iso
  · intro cls hne₁ hne₂
    exact avgProd_other_classes_zero_of_dual_classification phi csType7 cs1Flag3 cs1Flag4
      F34_witness_false F34_witness_true cls hne₁ hne₂
      F34_two_classes_of_jc_pos_tri_free

/-! #### F35: cs1Flag3 × cs1Flag5 → flag17 + sdpFlag9 (dual witness) -/

theorem F35_witness_false_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F35_witness_false.forget = 1 :=
  F35_witness_false_emptyAutCount_bridge

theorem F35_witness_false_jointCount :
    genJointCount CG2 csType7 cs1Flag3 cs1Flag5 F35_witness_false = 1 :=
  F35_witness_false_jointCount_bridge

theorem F35_witness_true_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F35_witness_true.forget = 2 :=
  F35_witness_true_emptyAutCount_bridge

theorem F35_witness_true_jointCount :
    genJointCount CG2 csType7 cs1Flag3 cs1Flag5 F35_witness_true = 1 :=
  F35_witness_true_jointCount_bridge

theorem F35_witness_false_jid_nf :
    genJointInducedDensity CG2 csType7 cs1Flag3 cs1Flag5 F35_witness_false *
      genNormalisationFactor csType7 F35_witness_false = 1/120 := by
  rw [jid_nf_5_3_4_4 cs1Flag3 cs1Flag5 F35_witness_false rfl rfl rfl rfl
    F35_witness_false_jointCount F35_witness_false_sigmaAutCount
    F35_witness_false_emptyAutCount]
  norm_num

theorem F35_witness_true_jid_nf :
    genJointInducedDensity CG2 csType7 cs1Flag3 cs1Flag5 F35_witness_true *
      genNormalisationFactor csType7 F35_witness_true = 1/60 := by
  rw [jid_nf_5_3_4_4 cs1Flag3 cs1Flag5 F35_witness_true rfl rfl rfl rfl
    F35_witness_true_jointCount F35_witness_true_sigmaAutCount
    F35_witness_true_emptyAutCount]
  norm_num

set_option maxHeartbeats 8000000 in
private theorem F35_two_classes_of_jc_pos_tri_free
    (G : GenFlag CG2 csType7)
    (hjc : genJointCount CG2 csType7 cs1Flag3 cs1Flag5 G > 0)
    (_hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType7 G F35_witness_false ∨ GenFlagIso csType7 G F35_witness_true := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType7_product_structure cs1Flag3 cs1Flag5 rfl rfl
      (by intro i; fin_cases i <;> simp [cs1Flag3, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs1Flag5, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs1Flag3.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs1Flag5.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  -- cs1Flag3: edges {0-1, 0-2, 0-3}. cs1Flag5: edges {0-1, 0-2, 2-3}.
  have G_01 : G.str.1.Adj v0 v1 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    rw [hadj₁]; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_02 : G.str.1.Adj v0 v2 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_03 : G.str.1.Adj v0 v3 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
    rw [hadj₁]; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_24 : G.str.1.Adj v2 v4 := by
    rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
    rw [hadj₂]; simp [cs1Flag5, SimpleGraph.fromRel_adj]
  have G_n12 : ¬G.str.1.Adj v1 v2 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    intro h; rw [hadj₁] at h; revert h; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_n13 : ¬G.str.1.Adj v1 v3 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    intro h; rw [hadj₁] at h; revert h; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_n23 : ¬G.str.1.Adj v2 v3 := by
    rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    intro h; rw [hadj₁] at h; revert h; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_n04 : ¬G.str.1.Adj v0 v4 := by
    rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
    intro h; rw [hadj₂] at h; revert h; simp [cs1Flag5, SimpleGraph.fromRel_adj]
  have G_n14 : ¬G.str.1.Adj v1 v4 := by
    rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
    intro h; rw [hadj₂] at h; revert h; simp [cs1Flag5, SimpleGraph.fromRel_adj]
  let fwd : Fin G.size → Fin 5 := φ
  let inv : Fin 5 → Fin G.size := fun i =>
    if i = 0 then v0 else if i = 1 then v1 else if i = 2 then v2
    else if i = 3 then v3 else v4
  have hinv_0 : inv 0 = v0 := if_pos rfl
  have hinv_1 : inv 1 = v1 := by show inv 1 = v1; dsimp only [inv]; simp
  have hinv_2 : inv 2 = v2 := by show inv 2 = v2; dsimp only [inv]; simp [Fin.reduceEq]
  have hinv_3 : inv 3 = v3 := by show inv 3 = v3; dsimp only [inv]; simp [Fin.reduceEq]
  have hinv_4 : inv 4 = v4 := by show inv 4 = v4; dsimp only [inv]; simp [Fin.reduceEq]
  have hli : ∀ x, inv (fwd x) = x := by
    intro x; change inv (φ x) = x
    rcases hcover x with rfl | rfl | rfl | rfl | rfl
    · rw [hfwd_v0, hinv_0]
    · rw [hfwd_v1, hinv_1]
    · rw [hfwd_v2, hinv_2]
    · rw [hfwd_v3, hinv_3]
    · rw [hfwd_v4, hinv_4]
  have hri : ∀ x, fwd (inv x) = x := by
    intro x; change φ (inv x) = x
    fin_cases x <;> simp only [] <;>
      first
      | (change φ (inv 0) = 0; rw [hinv_0, hfwd_v0])
      | (change φ (inv 1) = 1; rw [hinv_1, hfwd_v1])
      | (change φ (inv 2) = 2; rw [hinv_2, hfwd_v2])
      | (change φ (inv 3) = 3; rw [hinv_3, hfwd_v3])
      | (change φ (inv 4) = 4; rw [hinv_4, hfwd_v4])
  let φ' : Fin G.size ≃ Fin 5 := ⟨fwd, inv, hli, hri⟩
  by_cases h34 : G.str.1.Adj v3 v4
  · right
    refine ⟨φ', ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change F35_witness_true.str.1.comap (⇑φ') = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3]
          | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3]
          | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3]
          | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2]
          | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2]
          | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm | exact G_02 | exact G_02.symm
            | exact G_03 | exact G_03.symm | exact G_24 | exact G_24.symm
            | exact h34 | exact h34.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h G_n14 | exact absurd h (fun x => G_n14 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change F35_witness_true.str.2 ∘ (⇑φ') = G.str.2
        funext u; change F35_witness_true.str.2 (φ u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, F35_witness_true] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs1Flag3])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs1Flag3])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs1Flag3])
          | (rw [hcol₁]; simp [cs1Flag3])
          | (rw [hcol₂]; simp [cs1Flag5])
    · intro i; fin_cases i <;>
        simp only [F35_witness_true, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change φ v0 = _; rw [hfwd_v0]; rfl)
        | (change φ v1 = _; rw [hfwd_v1]; rfl)
        | (change φ v2 = _; rw [hfwd_v2]; rfl)
  · left
    refine ⟨φ', ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change F35_witness_false.str.1.comap (⇑φ') = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3]
          | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3]
          | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3]
          | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2]
          | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2]
          | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm | exact G_02 | exact G_02.symm
            | exact G_03 | exact G_03.symm | exact G_24 | exact G_24.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h G_n14 | exact absurd h (fun x => G_n14 x.symm)
            | exact absurd h h34 | exact absurd h (fun x => h34 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change F35_witness_false.str.2 ∘ (⇑φ') = G.str.2
        funext u; change F35_witness_false.str.2 (φ u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, F35_witness_false] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs1Flag3])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs1Flag3])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs1Flag3])
          | (rw [hcol₁]; simp [cs1Flag3])
          | (rw [hcol₂]; simp [cs1Flag5])
    · intro i; fin_cases i <;>
        simp only [F35_witness_false, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change φ v0 = _; rw [hfwd_v0]; rfl)
        | (change φ v1 = _; rw [hfwd_v1]; rfl)
        | (change φ v2 = _; rw [hfwd_v2]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd_F35
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd cs1Flag3 cs1Flag5) =
      (1/120 : ℝ) * phi.eval flag17 + (1/60 : ℝ) * phi.eval sdpFlag9 := by
  apply avgProd_eval_dual_witness phi cs1Flag3 cs1Flag5
    F35_witness_false F35_witness_true flag17 sdpFlag9 (1/120) (1/60) (by decide)
    F35_witnesses_not_iso
  · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨F35_witness_false.str, F35_witness_false.embedding, F35_witness_false.isInduced⟩, rfl⟩
  · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨F35_witness_true.str, F35_witness_true.embedding, F35_witness_true.isInduced⟩, rfl⟩
  · have haut3 : (genFlagAutCount CG2 csType7 cs1Flag3 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag3]; norm_num
    have haut5 : (genFlagAutCount CG2 csType7 cs1Flag5 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag5]; norm_num
    rw [haut3, haut5, one_mul, inv_one, one_mul, ← mul_assoc, F35_witness_false_jid_nf]
    congr 1
    exact phi.eval_iso _ _ F35_witness_false_forget_iso
  · have haut3 : (genFlagAutCount CG2 csType7 cs1Flag3 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag3]; norm_num
    have haut5 : (genFlagAutCount CG2 csType7 cs1Flag5 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag5]; norm_num
    rw [haut3, haut5, one_mul, inv_one, one_mul, ← mul_assoc, F35_witness_true_jid_nf]
    congr 1
    exact phi.eval_iso _ _ F35_witness_true_forget_iso
  · intro cls hne₁ hne₂
    exact avgProd_other_classes_zero_of_dual_classification phi csType7 cs1Flag3 cs1Flag5
      F35_witness_false F35_witness_true cls hne₁ hne₂
      F35_two_classes_of_jc_pos_tri_free

/-! #### F37: cs1Flag3 × cs1Flag7 → flag12 + flag32 (dual witness) -/

theorem F37_witness_false_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F37_witness_false.forget = 1 :=
  F37_witness_false_emptyAutCount_bridge

theorem F37_witness_false_jointCount :
    genJointCount CG2 csType7 cs1Flag3 cs1Flag7 F37_witness_false = 1 :=
  F37_witness_false_jointCount_bridge

theorem F37_witness_true_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) F37_witness_true.forget = 4 :=
  F37_witness_true_emptyAutCount_bridge

theorem F37_witness_true_jointCount :
    genJointCount CG2 csType7 cs1Flag3 cs1Flag7 F37_witness_true = 1 :=
  F37_witness_true_jointCount_bridge

theorem F37_witness_false_jid_nf :
    genJointInducedDensity CG2 csType7 cs1Flag3 cs1Flag7 F37_witness_false *
      genNormalisationFactor csType7 F37_witness_false = 1/120 := by
  rw [jid_nf_5_3_4_4 cs1Flag3 cs1Flag7 F37_witness_false rfl rfl rfl rfl
    F37_witness_false_jointCount F37_witness_false_sigmaAutCount
    F37_witness_false_emptyAutCount]
  norm_num

theorem F37_witness_true_jid_nf :
    genJointInducedDensity CG2 csType7 cs1Flag3 cs1Flag7 F37_witness_true *
      genNormalisationFactor csType7 F37_witness_true = 1/30 := by
  rw [jid_nf_5_3_4_4 cs1Flag3 cs1Flag7 F37_witness_true rfl rfl rfl rfl
    F37_witness_true_jointCount F37_witness_true_sigmaAutCount
    F37_witness_true_emptyAutCount]
  norm_num

set_option maxHeartbeats 8000000 in
private theorem F37_two_classes_of_jc_pos_tri_free
    (G : GenFlag CG2 csType7)
    (hjc : genJointCount CG2 csType7 cs1Flag3 cs1Flag7 G > 0)
    (_hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType7 G F37_witness_false ∨ GenFlagIso csType7 G F37_witness_true := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType7_product_structure cs1Flag3 cs1Flag7 rfl rfl
      (by intro i; fin_cases i <;> simp [cs1Flag3, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs1Flag7, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs1Flag3.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs1Flag7.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  -- cs1Flag3: edges {0-1, 0-2, 0-3}. cs1Flag7: edges {0-1, 0-2, 1-3, 2-3}.
  have G_01 : G.str.1.Adj v0 v1 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    rw [hadj₁]; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_02 : G.str.1.Adj v0 v2 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_03 : G.str.1.Adj v0 v3 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
    rw [hadj₁]; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_14 : G.str.1.Adj v1 v4 := by
    rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
    rw [hadj₂]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
  have G_24 : G.str.1.Adj v2 v4 := by
    rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
    rw [hadj₂]; simp [cs1Flag7, SimpleGraph.fromRel_adj]
  have G_n12 : ¬G.str.1.Adj v1 v2 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    intro h; rw [hadj₁] at h; revert h; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_n13 : ¬G.str.1.Adj v1 v3 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    intro h; rw [hadj₁] at h; revert h; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_n23 : ¬G.str.1.Adj v2 v3 := by
    rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    intro h; rw [hadj₁] at h; revert h; simp [cs1Flag3, SimpleGraph.fromRel_adj]
  have G_n04 : ¬G.str.1.Adj v0 v4 := by
    rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
    intro h; rw [hadj₂] at h; revert h; simp [cs1Flag7, SimpleGraph.fromRel_adj]
  let fwd : Fin G.size → Fin 5 := φ
  let inv : Fin 5 → Fin G.size := fun i =>
    if i = 0 then v0 else if i = 1 then v1 else if i = 2 then v2
    else if i = 3 then v3 else v4
  have hinv_0 : inv 0 = v0 := if_pos rfl
  have hinv_1 : inv 1 = v1 := by show inv 1 = v1; dsimp only [inv]; simp
  have hinv_2 : inv 2 = v2 := by show inv 2 = v2; dsimp only [inv]; simp [Fin.reduceEq]
  have hinv_3 : inv 3 = v3 := by show inv 3 = v3; dsimp only [inv]; simp [Fin.reduceEq]
  have hinv_4 : inv 4 = v4 := by show inv 4 = v4; dsimp only [inv]; simp [Fin.reduceEq]
  have hli : ∀ x, inv (fwd x) = x := by
    intro x; change inv (φ x) = x
    rcases hcover x with rfl | rfl | rfl | rfl | rfl
    · rw [hfwd_v0, hinv_0]
    · rw [hfwd_v1, hinv_1]
    · rw [hfwd_v2, hinv_2]
    · rw [hfwd_v3, hinv_3]
    · rw [hfwd_v4, hinv_4]
  have hri : ∀ x, fwd (inv x) = x := by
    intro x; change φ (inv x) = x
    fin_cases x <;> simp only [] <;>
      first
      | (change φ (inv 0) = 0; rw [hinv_0, hfwd_v0])
      | (change φ (inv 1) = 1; rw [hinv_1, hfwd_v1])
      | (change φ (inv 2) = 2; rw [hinv_2, hfwd_v2])
      | (change φ (inv 3) = 3; rw [hinv_3, hfwd_v3])
      | (change φ (inv 4) = 4; rw [hinv_4, hfwd_v4])
  let φ' : Fin G.size ≃ Fin 5 := ⟨fwd, inv, hli, hri⟩
  by_cases h34 : G.str.1.Adj v3 v4
  · right
    refine ⟨φ', ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change F37_witness_true.str.1.comap (⇑φ') = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3]
          | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3]
          | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3]
          | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2]
          | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2]
          | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm | exact G_02 | exact G_02.symm
            | exact G_03 | exact G_03.symm | exact G_14 | exact G_14.symm
            | exact G_24 | exact G_24.symm
            | exact h34 | exact h34.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change F37_witness_true.str.2 ∘ (⇑φ') = G.str.2
        funext u; change F37_witness_true.str.2 (φ u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, F37_witness_true] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs1Flag3])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs1Flag3])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs1Flag3])
          | (rw [hcol₁]; simp [cs1Flag3])
          | (rw [hcol₂]; simp [cs1Flag7])
    · intro i; fin_cases i <;>
        simp only [F37_witness_true, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change φ v0 = _; rw [hfwd_v0]; rfl)
        | (change φ v1 = _; rw [hfwd_v1]; rfl)
        | (change φ v2 = _; rw [hfwd_v2]; rfl)
  · left
    refine ⟨φ', ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change F37_witness_false.str.1.comap (⇑φ') = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3]
          | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3]
          | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3]
          | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2]
          | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2]
          | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm | exact G_02 | exact G_02.symm
            | exact G_03 | exact G_03.symm | exact G_14 | exact G_14.symm
            | exact G_24 | exact G_24.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h h34 | exact absurd h (fun x => h34 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change F37_witness_false.str.2 ∘ (⇑φ') = G.str.2
        funext u; change F37_witness_false.str.2 (φ u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, F37_witness_false] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs1Flag3])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs1Flag3])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs1Flag3])
          | (rw [hcol₁]; simp [cs1Flag3])
          | (rw [hcol₂]; simp [cs1Flag7])
    · intro i; fin_cases i <;>
        simp only [F37_witness_false, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change φ v0 = _; rw [hfwd_v0]; rfl)
        | (change φ v1 = _; rw [hfwd_v1]; rfl)
        | (change φ v2 = _; rw [hfwd_v2]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd_F37
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd cs1Flag3 cs1Flag7) =
      (1/120 : ℝ) * phi.eval flag12 + (1/30 : ℝ) * phi.eval flag32 := by
  apply avgProd_eval_dual_witness phi cs1Flag3 cs1Flag7
    F37_witness_false F37_witness_true flag12 flag32 (1/120) (1/30) (by decide)
    F37_witnesses_not_iso
  · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨F37_witness_false.str, F37_witness_false.embedding, F37_witness_false.isInduced⟩, rfl⟩
  · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨F37_witness_true.str, F37_witness_true.embedding, F37_witness_true.isInduced⟩, rfl⟩
  · have haut3 : (genFlagAutCount CG2 csType7 cs1Flag3 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag3]; norm_num
    have haut7 : (genFlagAutCount CG2 csType7 cs1Flag7 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag7]; norm_num
    rw [haut3, haut7, one_mul, inv_one, one_mul, ← mul_assoc, F37_witness_false_jid_nf]
    congr 1
    exact phi.eval_iso _ _ F37_witness_false_forget_iso
  · have haut3 : (genFlagAutCount CG2 csType7 cs1Flag3 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag3]; norm_num
    have haut7 : (genFlagAutCount CG2 csType7 cs1Flag7 : ℝ) = 1 := by
      rw [genFlagAutCount_cs1Flag7]; norm_num
    rw [haut3, haut7, one_mul, inv_one, one_mul, ← mul_assoc, F37_witness_true_jid_nf]
    congr 1
    exact phi.eval_iso _ _ F37_witness_true_forget_iso
  · intro cls hne₁ hne₂
    exact avgProd_other_classes_zero_of_dual_classification phi csType7 cs1Flag3 cs1Flag7
      F37_witness_false F37_witness_true cls hne₁ hne₂
      F37_two_classes_of_jc_pos_tri_free

/-! ### Full ℓ² evaluation identity -/

/-- Full ℓ² evaluation identity in unlabelled density convention.
    The RHS coefficients (×240) should match the lsq_x2 vector (×120) from BrrbCertificate.lean,
    i.e., the coefficients here should be lsq_x2 × 2. -/
theorem lsq_eval_identity
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    240 * phi.evalAlg (genAveragingAlg csType7 (cs1_l.mul cs1_l)) =
      12 * phi.eval flag5 - 8 * phi.eval flag12 + 8 * phi.eval flag15 +
      4 * phi.eval flag16 + 4 * phi.eval flag17 - 8 * phi.eval flag24 +
      4 * phi.eval flag25 - 16 * phi.eval flag32 + 12 * phi.eval flag34 -
      4 * phi.eval sdpFlag37 - 8 * phi.eval sdpFlag55 := by
  rw [lsq_eval_distribute]
  rw [avgProd_F33 phi, avgProd_F34 phi, avgProd_F35 phi, avgProd_F37 phi,
      avgProd_F44 phi, avgProd_F45 phi, avgProd_F47 phi,
      avgProd_F55_eval phi, avgProd_F57 phi, avgProd_F77 phi]
  ring

/-! ## cs0 (σ₆) product evaluation infrastructure -/

set_option maxHeartbeats 800000 in
/-- Structural decomposition for csType6 joint embeddings of two size-4 flags.
    Identical structure to `csType7_product_structure` — only the type differs. -/
theorem csType6_product_structure
    (F₁ F₂ : GenFlag CG2 csType6)
    (hF₁size : F₁.size = 4) (hF₂size : F₂.size = 4)
    (hF₁emb : ∀ i : Fin 3, (F₁.embedding i).val = i.val)
    (hF₂emb : ∀ i : Fin 3, (F₂.embedding i).val = i.val)
    (G : GenFlag CG2 csType6)
    (hjc : genJointCount CG2 csType6 F₁ F₂ G > 0) :
    G.size = 5 ∧
    ∃ (e₁ : GenInducedEmbedding CG2 csType6 F₁ G)
      (e₂ : GenInducedEmbedding CG2 csType6 F₂ G)
      (φ : Fin G.size ≃ Fin 5),
      (∀ i : Fin 3, φ (G.embedding i) = Fin.castLE (by omega) i) ∧
      (φ (e₁.toFun ⟨3, by omega⟩) = ⟨3, by omega⟩) ∧
      (φ (e₂.toFun ⟨3, by omega⟩) = ⟨4, by omega⟩) ∧
      (∀ i : Fin 3, e₁.toFun ⟨i.val, by omega⟩ = G.embedding i) ∧
      (∀ i : Fin 3, e₂.toFun ⟨i.val, by omega⟩ = G.embedding i) ∧
      (∀ i j : Fin F₁.size, G.str.1.Adj (e₁.toFun i) (e₁.toFun j) ↔ F₁.str.1.Adj i j) ∧
      (∀ i j : Fin F₂.size, G.str.1.Adj (e₂.toFun i) (e₂.toFun j) ↔ F₂.str.1.Adj i j) ∧
      (∀ i : Fin F₁.size, G.str.2 (e₁.toFun i) = F₁.str.2 i) ∧
      (∀ i : Fin F₂.size, G.str.2 (e₂.toFun i) = F₂.str.2 i) ∧
      (e₁.toFun ⟨3, by omega⟩ ≠ e₂.toFun ⟨3, by omega⟩) ∧
      (e₁.toFun ⟨3, by omega⟩ ∉ Set.range G.embedding) ∧
      (e₂.toFun ⟨3, by omega⟩ ∉ Set.range G.embedding) ∧
      (∀ v : Fin G.size,
        v = G.embedding ⟨0, by decide⟩ ∨ v = G.embedding ⟨1, by decide⟩ ∨
        v = G.embedding ⟨2, by decide⟩ ∨ v = e₁.toFun ⟨3, by omega⟩ ∨
        v = e₂.toFun ⟨3, by omega⟩) := by
  have hjc' : 0 < genJointCount CG2 csType6 F₁ F₂ G := hjc
  unfold genJointCount at hjc'
  rw [Fintype.card_pos_iff] at hjc'
  obtain ⟨⟨⟨e₁, e₂⟩, hoverlap, hcovering⟩⟩ := hjc'
  have hGsize : G.size = 5 := by
    have hS₁ : (Finset.univ.image e₁.toFun).card = F₁.size := by
      rw [Finset.card_image_of_injective _ e₁.injective, Finset.card_univ, Fintype.card_fin]
    have hS₂ : (Finset.univ.image e₂.toFun).card = F₂.size := by
      rw [Finset.card_image_of_injective _ e₂.injective, Finset.card_univ, Fintype.card_fin]
    have hSσ : (Finset.univ.image G.embedding).card = csType6.size := by
      rw [Finset.card_image_of_injective _ G.embedding.injective, Finset.card_univ,
          Fintype.card_fin]
    simp only [csType6] at hSσ
    have hinter : Finset.univ.image e₁.toFun ∩ Finset.univ.image e₂.toFun =
        Finset.univ.image G.embedding := by
      ext i; simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩⟩
        obtain ⟨k, hk⟩ := (hoverlap i).mp ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩⟩
        exact ⟨k, hk⟩
      · rintro ⟨j, hj⟩
        obtain ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩ := (hoverlap i).mpr ⟨j, hj⟩
        exact ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩
    have hunion : Finset.univ.image e₁.toFun ∪ Finset.univ.image e₂.toFun = Finset.univ := by
      ext i; constructor
      · intro; exact Finset.mem_univ _
      · intro _; rw [Finset.mem_union]
        rcases hcovering i with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · left; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        · right; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hcard := Finset.card_union_add_card_inter
      (Finset.univ.image e₁.toFun) (Finset.univ.image e₂.toFun)
    rw [hunion] at hcard
    rw [hinter] at hcard
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  have he₁_compat : ∀ k : Fin 3, e₁.toFun ⟨k.val, by omega⟩ = G.embedding k := by
    intro k
    have h := e₁.compat k
    have hemb : F₁.embedding k = ⟨k.val, by omega⟩ := Fin.ext (hF₁emb k)
    rw [hemb] at h; exact h
  have he₂_compat : ∀ k : Fin 3, e₂.toFun ⟨k.val, by omega⟩ = G.embedding k := by
    intro k
    have h := e₂.compat k
    have hemb : F₂.embedding k = ⟨k.val, by omega⟩ := Fin.ext (hF₂emb k)
    rw [hemb] at h; exact h
  have he₁_3_not_emb : e₁.toFun ⟨3, by omega⟩ ∉ Set.range G.embedding := by
    intro ⟨k, hk⟩
    have hk' := he₁_compat k
    have hinj := e₁.injective (hk'.trans hk)
    fin_cases k <;> simp [Fin.ext_iff] at hinj
  have he₂_3_not_emb : e₂.toFun ⟨3, by omega⟩ ∉ Set.range G.embedding := by
    intro ⟨k, hk⟩
    have hk' := he₂_compat k
    have hinj := e₂.injective (hk'.trans hk)
    fin_cases k <;> simp [Fin.ext_iff] at hinj
  have he_ne : e₁.toFun ⟨3, by omega⟩ ≠ e₂.toFun ⟨3, by omega⟩ := by
    intro heq
    have : e₁.toFun ⟨3, by omega⟩ ∈ Set.range G.embedding := by
      apply (hoverlap _).mp
      exact ⟨⟨⟨3, by omega⟩, rfl⟩, ⟨⟨3, by omega⟩, heq.symm⟩⟩
    exact he₁_3_not_emb this
  have hind₁ := e₁.isInduced
  have hind₂ := e₂.isInduced
  have hadj₁ : ∀ u v : Fin F₁.size, G.str.1.Adj (e₁.toFun u) (e₁.toFun v) ↔
      F₁.str.1.Adj u v := by
    intro u v
    have h := congr_arg Prod.fst hind₁
    simp only [colouredGraphUniverse] at h
    have : (G.str.1.comap e₁.toFun).Adj u v ↔ F₁.str.1.Adj u v := by rw [h]
    simpa [SimpleGraph.comap_adj] using this
  have hadj₂ : ∀ u v : Fin F₂.size, G.str.1.Adj (e₂.toFun u) (e₂.toFun v) ↔
      F₂.str.1.Adj u v := by
    intro u v
    have h := congr_arg Prod.fst hind₂
    simp only [colouredGraphUniverse] at h
    have : (G.str.1.comap e₂.toFun).Adj u v ↔ F₂.str.1.Adj u v := by rw [h]
    simpa [SimpleGraph.comap_adj] using this
  have hcol₁ : ∀ u : Fin F₁.size, G.str.2 (e₁.toFun u) = F₁.str.2 u := by
    intro u
    have h := congr_arg Prod.snd hind₁
    simp only [colouredGraphUniverse] at h
    exact congr_fun h u
  have hcol₂ : ∀ u : Fin F₂.size, G.str.2 (e₂.toFun u) = F₂.str.2 u := by
    intro u
    have h := congr_arg Prod.snd hind₂
    simp only [colouredGraphUniverse] at h
    exact congr_fun h u
  have hemb_ne_01 : G.embedding ⟨0, by decide⟩ ≠ G.embedding ⟨1, by decide⟩ :=
    G.embedding.injective.ne (by simp [Fin.ext_iff])
  have hemb_ne_02 : G.embedding ⟨0, by decide⟩ ≠ G.embedding ⟨2, by decide⟩ :=
    G.embedding.injective.ne (by simp [Fin.ext_iff])
  have hemb_ne_12 : G.embedding ⟨1, by decide⟩ ≠ G.embedding ⟨2, by decide⟩ :=
    G.embedding.injective.ne (by simp [Fin.ext_iff])
  have he₁_3_ne_emb0 : e₁.toFun ⟨3, by omega⟩ ≠ G.embedding ⟨0, by decide⟩ :=
    fun h => he₁_3_not_emb ⟨⟨0, by decide⟩, h.symm⟩
  have he₁_3_ne_emb1 : e₁.toFun ⟨3, by omega⟩ ≠ G.embedding ⟨1, by decide⟩ :=
    fun h => he₁_3_not_emb ⟨⟨1, by decide⟩, h.symm⟩
  have he₁_3_ne_emb2 : e₁.toFun ⟨3, by omega⟩ ≠ G.embedding ⟨2, by decide⟩ :=
    fun h => he₁_3_not_emb ⟨⟨2, by decide⟩, h.symm⟩
  have he₂_3_ne_emb0 : e₂.toFun ⟨3, by omega⟩ ≠ G.embedding ⟨0, by decide⟩ :=
    fun h => he₂_3_not_emb ⟨⟨0, by decide⟩, h.symm⟩
  have he₂_3_ne_emb1 : e₂.toFun ⟨3, by omega⟩ ≠ G.embedding ⟨1, by decide⟩ :=
    fun h => he₂_3_not_emb ⟨⟨1, by decide⟩, h.symm⟩
  have he₂_3_ne_emb2 : e₂.toFun ⟨3, by omega⟩ ≠ G.embedding ⟨2, by decide⟩ :=
    fun h => he₂_3_not_emb ⟨⟨2, by decide⟩, h.symm⟩
  have he₁_0 : e₁.toFun ⟨0, by omega⟩ = G.embedding ⟨0, by decide⟩ :=
    he₁_compat ⟨0, by decide⟩
  have he₁_1 : e₁.toFun ⟨1, by omega⟩ = G.embedding ⟨1, by decide⟩ :=
    he₁_compat ⟨1, by decide⟩
  have he₁_2 : e₁.toFun ⟨2, by omega⟩ = G.embedding ⟨2, by decide⟩ :=
    he₁_compat ⟨2, by decide⟩
  have he₂_0 : e₂.toFun ⟨0, by omega⟩ = G.embedding ⟨0, by decide⟩ :=
    he₂_compat ⟨0, by decide⟩
  have he₂_1 : e₂.toFun ⟨1, by omega⟩ = G.embedding ⟨1, by decide⟩ :=
    he₂_compat ⟨1, by decide⟩
  have he₂_2 : e₂.toFun ⟨2, by omega⟩ = G.embedding ⟨2, by decide⟩ :=
    he₂_compat ⟨2, by decide⟩
  have hcover : ∀ v : Fin G.size,
      v = G.embedding ⟨0, by decide⟩ ∨ v = G.embedding ⟨1, by decide⟩ ∨
      v = G.embedding ⟨2, by decide⟩ ∨ v = e₁.toFun ⟨3, by omega⟩ ∨
      v = e₂.toFun ⟨3, by omega⟩ := by
    intro v
    rcases hcovering v with ⟨j, hj⟩ | ⟨j, hj⟩
    · by_cases h0 : j.val = 0
      · left; rw [← hj, show j = ⟨0, by omega⟩ from Fin.ext h0, he₁_0]
      · by_cases h1 : j.val = 1
        · right; left; rw [← hj, show j = ⟨1, by omega⟩ from Fin.ext h1, he₁_1]
        · by_cases h2 : j.val = 2
          · right; right; left
            rw [← hj, show j = ⟨2, by omega⟩ from Fin.ext h2, he₁_2]
          · right; right; right; left
            have : j.val = 3 := by omega
            rw [← hj, show j = ⟨3, by omega⟩ from Fin.ext this]
    · by_cases h0 : j.val = 0
      · left; rw [← hj, show j = ⟨0, by omega⟩ from Fin.ext h0, he₂_0]
      · by_cases h1 : j.val = 1
        · right; left; rw [← hj, show j = ⟨1, by omega⟩ from Fin.ext h1, he₂_1]
        · by_cases h2 : j.val = 2
          · right; right; left
            rw [← hj, show j = ⟨2, by omega⟩ from Fin.ext h2, he₂_2]
          · right; right; right; right
            have : j.val = 3 := by omega
            rw [← hj, show j = ⟨3, by omega⟩ from Fin.ext this]
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by omega⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by omega⟩ with hv4_def
  set fwd : Fin G.size → Fin 5 := fun v =>
    if v = v0 then 0
    else if v = v1 then 1
    else if v = v2 then 2
    else if v = v3 then 3
    else 4
    with hfwd_def
  have hfwd_v0 : fwd v0 = 0 := if_pos rfl
  have hfwd_v1 : fwd v1 = 1 := by
    show fwd v1 = 1; dsimp only [fwd]
    rw [if_neg (Ne.symm hemb_ne_01), if_pos rfl]
  have hfwd_v2 : fwd v2 = 2 := by
    show fwd v2 = 2; dsimp only [fwd]
    rw [if_neg (Ne.symm hemb_ne_02), if_neg (Ne.symm hemb_ne_12), if_pos rfl]
  have hfwd_v3 : fwd v3 = 3 := by
    show fwd v3 = 3; dsimp only [fwd]
    rw [if_neg he₁_3_ne_emb0, if_neg he₁_3_ne_emb1, if_neg he₁_3_ne_emb2,
        if_pos rfl]
  have hfwd_v4 : fwd v4 = 4 := by
    show fwd v4 = 4; dsimp only [fwd]
    rw [if_neg he₂_3_ne_emb0, if_neg he₂_3_ne_emb1, if_neg he₂_3_ne_emb2,
        if_neg (Ne.symm he_ne)]
  let inv : Fin 5 → Fin G.size := fun i =>
    if i = 0 then v0
    else if i = 1 then v1
    else if i = 2 then v2
    else if i = 3 then v3
    else v4
  have hinv_0 : inv 0 = v0 := if_pos rfl
  have hinv_1 : inv 1 = v1 := by
    show inv 1 = v1; dsimp only [inv]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
  have hinv_2 : inv 2 = v2 := by
    show inv 2 = v2; dsimp only [inv]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
  have hinv_3 : inv 3 = v3 := by
    show inv 3 = v3; dsimp only [inv]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
  have hinv_4 : inv 4 = v4 := by
    show inv 4 = v4; dsimp only [inv]
    simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte]
  have hli : ∀ x, inv (fwd x) = x := by
    intro x
    rcases hcover x with rfl | rfl | rfl | rfl | rfl
    · rw [hfwd_v0, hinv_0]
    · rw [hfwd_v1, hinv_1]
    · rw [hfwd_v2, hinv_2]
    · rw [hfwd_v3, hinv_3]
    · rw [hfwd_v4, hinv_4]
  have hri : ∀ x, fwd (inv x) = x := by
    intro x; fin_cases x <;> simp only [] <;>
      first
      | (change fwd (inv 0) = 0; rw [hinv_0, hfwd_v0])
      | (change fwd (inv 1) = 1; rw [hinv_1, hfwd_v1])
      | (change fwd (inv 2) = 2; rw [hinv_2, hfwd_v2])
      | (change fwd (inv 3) = 3; rw [hinv_3, hfwd_v3])
      | (change fwd (inv 4) = 4; rw [hinv_4, hfwd_v4])
  let φ : Fin G.size ≃ Fin 5 := ⟨fwd, inv, hli, hri⟩
  refine ⟨hGsize, e₁, e₂, φ, ?_, ?_, ?_, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩
  · intro i; fin_cases i <;> simp only [Fin.castLE] <;>
      first
      | (change fwd v0 = _; rw [hfwd_v0]; rfl)
      | (change fwd v1 = _; rw [hfwd_v1]; rfl)
      | (change fwd v2 = _; rw [hfwd_v2]; rfl)
  · change fwd v3 = _; rw [hfwd_v3]; rfl
  · change fwd v4 = _; rw [hfwd_v4]; rfl

/-! ### Averaged product abbreviation for csType6 -/

/-- Abbreviation for averaged product evaluation at csType6. -/
noncomputable abbrev avgProd6
    (F₁ F₂ : GenFlag CG2 csType6) : GenFlagAlg CG2 (GenFlagType.empty CG2) :=
  genAveragingAlg csType6 (genLocalFlagProduct CG2 csType6 F₁ F₂)

/-! ### f² and g² algebraic expansion -/

/-- The f² expansion at csType6:
    f·f = (-1)²F₃² + 2(-1)(1/4)F₃F₄ + 2(-1)(1/4)F₃F₅ + 2(-1)(1/2)F₃F₆
        + (1/4)²F₄² + 2(1/4)(1/4)F₄F₅ + 2(1/4)(1/2)F₄F₆
        + (1/4)²F₅² + 2(1/4)(1/2)F₅F₆
        + (1/2)²F₆²
    = F₃² - (1/2)F₃F₄ - (1/2)F₃F₅ - F₃F₆
      + (1/16)F₄² + (1/8)F₄F₅ + (1/4)F₄F₆
      + (1/16)F₅² + (1/4)F₅F₆
      + (1/4)F₆² -/
theorem cs0_f_sq_expansion :
    cs0_f.mul cs0_f =
      (1 : ℝ) • genLocalFlagProduct CG2 csType6 cs0Flag3 cs0Flag3 +
      (-1/2 : ℝ) • genLocalFlagProduct CG2 csType6 cs0Flag3 cs0Flag4 +
      (-1/2 : ℝ) • genLocalFlagProduct CG2 csType6 cs0Flag3 cs0Flag5 +
      (-1 : ℝ) • genLocalFlagProduct CG2 csType6 cs0Flag3 cs0Flag6 +
      (1/16 : ℝ) • genLocalFlagProduct CG2 csType6 cs0Flag4 cs0Flag4 +
      (1/8 : ℝ) • genLocalFlagProduct CG2 csType6 cs0Flag4 cs0Flag5 +
      (1/4 : ℝ) • genLocalFlagProduct CG2 csType6 cs0Flag4 cs0Flag6 +
      (1/16 : ℝ) • genLocalFlagProduct CG2 csType6 cs0Flag5 cs0Flag5 +
      (1/4 : ℝ) • genLocalFlagProduct CG2 csType6 cs0Flag5 cs0Flag6 +
      (1/4 : ℝ) • genLocalFlagProduct CG2 csType6 cs0Flag6 cs0Flag6 := by
  simp only [cs0_f, GenFlagAlg.add_mul, GenFlagAlg.mul_add, GenFlagAlg.smul_mul,
    GenFlagAlg.mul_smul, GenFlagAlg.mul_single, smul_smul, smul_add]
  rw [genProduct_comm csType6 cs0Flag4 cs0Flag3,
      genProduct_comm csType6 cs0Flag5 cs0Flag3,
      genProduct_comm csType6 cs0Flag6 cs0Flag3,
      genProduct_comm csType6 cs0Flag5 cs0Flag4,
      genProduct_comm csType6 cs0Flag6 cs0Flag4,
      genProduct_comm csType6 cs0Flag6 cs0Flag5]
  module

/-- The g² expansion at csType6:
    g·g = (1/16)F₄² + (-1/8)F₄F₅ + (1/16)F₅² -/
theorem cs0_g_sq_expansion :
    cs0_g.mul cs0_g =
      (1/16 : ℝ) • genLocalFlagProduct CG2 csType6 cs0Flag4 cs0Flag4 +
      (-1/8 : ℝ) • genLocalFlagProduct CG2 csType6 cs0Flag4 cs0Flag5 +
      (1/16 : ℝ) • genLocalFlagProduct CG2 csType6 cs0Flag5 cs0Flag5 := by
  simp only [cs0_g, GenFlagAlg.add_mul, GenFlagAlg.mul_add, GenFlagAlg.smul_mul,
    GenFlagAlg.mul_smul, GenFlagAlg.mul_single, smul_smul, smul_add]
  rw [genProduct_comm csType6 cs0Flag5 cs0Flag4]
  module

/-- The f² averaged product distributes as a sum of 10 averaged products. -/
theorem fsq_eval_distribute
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (genAveragingAlg csType6 (cs0_f.mul cs0_f)) =
      (1 : ℝ) * phi.evalAlg (avgProd6 cs0Flag3 cs0Flag3) +
      (-1/2 : ℝ) * phi.evalAlg (avgProd6 cs0Flag3 cs0Flag4) +
      (-1/2 : ℝ) * phi.evalAlg (avgProd6 cs0Flag3 cs0Flag5) +
      (-1 : ℝ) * phi.evalAlg (avgProd6 cs0Flag3 cs0Flag6) +
      (1/16 : ℝ) * phi.evalAlg (avgProd6 cs0Flag4 cs0Flag4) +
      (1/8 : ℝ) * phi.evalAlg (avgProd6 cs0Flag4 cs0Flag5) +
      (1/4 : ℝ) * phi.evalAlg (avgProd6 cs0Flag4 cs0Flag6) +
      (1/16 : ℝ) * phi.evalAlg (avgProd6 cs0Flag5 cs0Flag5) +
      (1/4 : ℝ) * phi.evalAlg (avgProd6 cs0Flag5 cs0Flag6) +
      (1/4 : ℝ) * phi.evalAlg (avgProd6 cs0Flag6 cs0Flag6) := by
  rw [cs0_f_sq_expansion]
  simp only [genAveragingAlg_add, genAveragingAlg_smul,
    phi.evalAlg_add, phi.evalAlg_smul, avgProd6]

/-- The g² averaged product distributes as a sum of 3 averaged products. -/
theorem gsq_eval_distribute
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (genAveragingAlg csType6 (cs0_g.mul cs0_g)) =
      (1/16 : ℝ) * phi.evalAlg (avgProd6 cs0Flag4 cs0Flag4) +
      (-1/8 : ℝ) * phi.evalAlg (avgProd6 cs0Flag4 cs0Flag5) +
      (1/16 : ℝ) * phi.evalAlg (avgProd6 cs0Flag5 cs0Flag5) := by
  rw [cs0_g_sq_expansion]
  simp only [genAveragingAlg_add, genAveragingAlg_smul,
    phi.evalAlg_add, phi.evalAlg_smul, avgProd6]

/-! ### Per-product evaluations for cs0 (σ₆)

Each of the 10 products cs0Fᵢ×cs0Fⱼ evaluates to a linear combination of
phi.eval of ∅-type flags. The product data (computed in CGraphBridge.lean):

| Product | Witnesses | aut∅ | autσ | jc |
|---------|-----------|------|------|----|
| S0F3×S0F3 | single (adj34=F) | 24 | 2 | 2 |
| S0F3×S0F4 | dual (adj34=F,T) | 2,2 | 1,1 | 1,1 |
| S0F3×S0F5 | dual (adj34=F,T) | 2,2 | 1,1 | 1,1 |
| S0F3×S0F6 | dual (adj34=F,T) | 2,12 | 1,1 | 1,1 |
| S0F4×S0F4 | single (adj34=F) | 2 | 2 | 2 |
| S0F4×S0F5 | dual (adj34=F,T) | 2,2 | 1,1 | 1,1 |
| S0F4×S0F6 | single (adj34=F) | 2 | 1 | 1 |
| S0F5×S0F5 | single (adj34=F) | 2 | 2 | 2 |
| S0F5×S0F6 | single (adj34=F) | 2 | 1 | 1 |
| S0F6×S0F6 | single (adj34=F) | 12 | 2 | 2 |

Coefficients: jid*nf = jc/(autσ * choose(2,1)*choose(1,1)) * 1/(5!/3!) = jc/(autσ * 2 * 60)
For jc=2,autσ=2: 2/(2*120) = 1/120
For jc=1,autσ=1: 1/(1*120) = 1/120
For jc=2,autσ=2 (but aut∅=24): 1/120, then divide by aut∅=24 for nf... let me use the formula.

Actually: genJointInducedDensity = jc / (autσ * choose(n-k, m₁-k) * choose(n-k-(m₁-k), m₂-k))
where n=5, k=3, m₁=m₂=4.
= jc / (autσ * choose(2,1) * choose(1,1)) = jc / (autσ * 2)

genNormalisationFactor = 1 / (aut∅ * descFactorial(5,3) / aut∅) = aut∅ / (aut∅ * 60) = 1/60
Wait, that's not right. Let me look at the formula:
genNormalisationFactor σ F = 1 / ((F.size).descFactorial σ.size)
= 1 / descFactorial(5,3) = 1/60

So jid*nf = (jc / (autσ * 2)) * (1/60) = jc / (120 * autσ)

Then avgProd eval = (1/aut_F₁) * (1/aut_F₂) * Σ jid*nf * phi.eval(forget)
Since all cs0 flag auts = 1, this simplifies to Σ jid*nf * phi.eval(forget).

For single-witness cases: avgProd = jid*nf * phi.eval(forget)
For dual-witness cases: avgProd = jid₁*nf₁ * phi.eval(forget₁) + jid₂*nf₂ * phi.eval(forget₂)

The per-product avgProd6 evaluation theorems are stated below with sorry.
Each needs:
1. Witness def in PentagonConjecture.lean
2. CGraph bridge in CGraphBridge.lean
3. Classification proof using csType6_product_structure
4. Numerical computation (jid_nf)
5. Forget iso proof
-/

/-- Single-witness avgProd6 evaluation at csType6 (σ₆). -/
theorem avgProd6_eval_single_witness
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta)
    (F₁ F₂ : GenFlag CG2 csType6)
    (witness : GenFlag CG2 csType6)
    (target : GenFlag CG2 (GenFlagType.empty CG2))
    (coeff : ℝ)
    (hn : csType6.size ≤ F₁.size + F₂.size - csType6.size)
    (hmem : GenFlagClass.mk witness ∈
      genClassesOfSize CG2 csType6 (F₁.size + F₂.size - csType6.size) hn)
    (hsummand : ((genFlagAutCount CG2 csType6 F₁ : ℝ) * (genFlagAutCount CG2 csType6 F₂ : ℝ))⁻¹ *
      (genJointInducedDensity CG2 csType6 F₁ F₂ witness *
        (genNormalisationFactor csType6 witness * phi.eval witness.forget)) =
      coeff * phi.eval target)
    (hothers : ∀ cls : GenFlagClass CG2 csType6,
      cls ≠ GenFlagClass.mk witness →
      genJointInducedDensity CG2 csType6 F₁ F₂ cls.out *
        (genNormalisationFactor csType6 cls.out * phi.eval cls.out.forget) = 0) :
    phi.evalAlg (avgProd6 F₁ F₂) = coeff * phi.eval target := by
  simp only [avgProd6]
  rw [evalAlg_genAveragingAlg_genLocalFlagProduct phi F₁ F₂ hn]
  have hiso_w := Quotient.exact (Quotient.out_eq (GenFlagClass.mk witness))
  have hsummand_cls : genJointInducedDensity CG2 csType6 F₁ F₂
      (GenFlagClass.mk witness).out *
      (genNormalisationFactor csType6 (GenFlagClass.mk witness).out *
        phi.eval (GenFlagClass.mk witness).out.forget) =
      genJointInducedDensity CG2 csType6 F₁ F₂ witness *
        (genNormalisationFactor csType6 witness * phi.eval witness.forget) := by
    rw [genJointInducedDensity_flagIso_target' hiso_w,
        genNormalisationFactor_flagIso hiso_w,
        phi.eval_iso _ _ (genFlagIso_forget hiso_w)]
  generalize genClassesOfSize CG2 csType6
    (F₁.size + F₂.size - csType6.size) hn = S at hmem ⊢
  rw [show ((genFlagAutCount CG2 csType6 F₁ : ℝ) * ↑(genFlagAutCount CG2 csType6 F₂))⁻¹ *
    ∑ cls ∈ S, genJointInducedDensity CG2 csType6 F₁ F₂ cls.out *
      (genNormalisationFactor csType6 cls.out * phi.eval cls.out.forget) =
    ((genFlagAutCount CG2 csType6 F₁ : ℝ) * ↑(genFlagAutCount CG2 csType6 F₂))⁻¹ *
    (genJointInducedDensity CG2 csType6 F₁ F₂ witness *
      (genNormalisationFactor csType6 witness * phi.eval witness.forget)) from by
    congr 1
    exact finset_sum_single_witness S (GenFlagClass.mk witness)
      (fun cls => genJointInducedDensity CG2 csType6 F₁ F₂ cls.out *
        (genNormalisationFactor csType6 cls.out * phi.eval cls.out.forget))
      _ hmem hsummand_cls (fun x _ hne => hothers x hne)]
  exact hsummand

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
set_option linter.constructorNameAsVariable false in
/-- Dual-witness avgProd6 evaluation at csType6 (σ₆). -/
theorem avgProd6_eval_dual_witness
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta)
    (F₁ F₂ : GenFlag CG2 csType6)
    (w₁ w₂ : GenFlag CG2 csType6)
    (target₁ target₂ : GenFlag CG2 (GenFlagType.empty CG2))
    (coeff₁ coeff₂ : ℝ)
    (hn : csType6.size ≤ F₁.size + F₂.size - csType6.size)
    (hw_ne : GenFlagClass.mk w₁ ≠ GenFlagClass.mk w₂)
    (hmem₁ : GenFlagClass.mk w₁ ∈
      genClassesOfSize CG2 csType6 (F₁.size + F₂.size - csType6.size) hn)
    (hmem₂ : GenFlagClass.mk w₂ ∈
      genClassesOfSize CG2 csType6 (F₁.size + F₂.size - csType6.size) hn)
    (hsummand₁ : ((genFlagAutCount CG2 csType6 F₁ : ℝ) * (genFlagAutCount CG2 csType6 F₂ : ℝ))⁻¹ *
      (genJointInducedDensity CG2 csType6 F₁ F₂ w₁ *
        (genNormalisationFactor csType6 w₁ * phi.eval w₁.forget)) =
      coeff₁ * phi.eval target₁)
    (hsummand₂ : ((genFlagAutCount CG2 csType6 F₁ : ℝ) * (genFlagAutCount CG2 csType6 F₂ : ℝ))⁻¹ *
      (genJointInducedDensity CG2 csType6 F₁ F₂ w₂ *
        (genNormalisationFactor csType6 w₂ * phi.eval w₂.forget)) =
      coeff₂ * phi.eval target₂)
    (hothers : ∀ cls : GenFlagClass CG2 csType6,
      cls ≠ GenFlagClass.mk w₁ → cls ≠ GenFlagClass.mk w₂ →
      genJointInducedDensity CG2 csType6 F₁ F₂ cls.out *
        (genNormalisationFactor csType6 cls.out * phi.eval cls.out.forget) = 0) :
    phi.evalAlg (avgProd6 F₁ F₂) = coeff₁ * phi.eval target₁ + coeff₂ * phi.eval target₂ := by
  simp only [avgProd6]
  rw [evalAlg_genAveragingAlg_genLocalFlagProduct phi F₁ F₂ hn]
  have hiso_w₁ := Quotient.exact (Quotient.out_eq (GenFlagClass.mk w₁))
  have hiso_w₂ := Quotient.exact (Quotient.out_eq (GenFlagClass.mk w₂))
  have hsummand_cls₁ : genJointInducedDensity CG2 csType6 F₁ F₂
      (GenFlagClass.mk w₁).out *
      (genNormalisationFactor csType6 (GenFlagClass.mk w₁).out *
        phi.eval (GenFlagClass.mk w₁).out.forget) =
      genJointInducedDensity CG2 csType6 F₁ F₂ w₁ *
        (genNormalisationFactor csType6 w₁ * phi.eval w₁.forget) := by
    rw [genJointInducedDensity_flagIso_target' hiso_w₁,
        genNormalisationFactor_flagIso hiso_w₁,
        phi.eval_iso _ _ (genFlagIso_forget hiso_w₁)]
  have hsummand_cls₂ : genJointInducedDensity CG2 csType6 F₁ F₂
      (GenFlagClass.mk w₂).out *
      (genNormalisationFactor csType6 (GenFlagClass.mk w₂).out *
        phi.eval (GenFlagClass.mk w₂).out.forget) =
      genJointInducedDensity CG2 csType6 F₁ F₂ w₂ *
        (genNormalisationFactor csType6 w₂ * phi.eval w₂.forget) := by
    rw [genJointInducedDensity_flagIso_target' hiso_w₂,
        genNormalisationFactor_flagIso hiso_w₂,
        phi.eval_iso _ _ (genFlagIso_forget hiso_w₂)]
  generalize genClassesOfSize CG2 csType6
    (F₁.size + F₂.size - csType6.size) hn = S at hmem₁ hmem₂ ⊢
  have : ((genFlagAutCount CG2 csType6 F₁ : ℝ) * ↑(genFlagAutCount CG2 csType6 F₂))⁻¹ *
    ∑ cls ∈ S, genJointInducedDensity CG2 csType6 F₁ F₂ cls.out *
      (genNormalisationFactor csType6 cls.out * phi.eval cls.out.forget) =
    ((genFlagAutCount CG2 csType6 F₁ : ℝ) * ↑(genFlagAutCount CG2 csType6 F₂))⁻¹ *
    (genJointInducedDensity CG2 csType6 F₁ F₂ w₁ *
      (genNormalisationFactor csType6 w₁ * phi.eval w₁.forget) +
     genJointInducedDensity CG2 csType6 F₁ F₂ w₂ *
      (genNormalisationFactor csType6 w₂ * phi.eval w₂.forget)) := by
    congr 1
    exact finset_sum_dual_witness S (GenFlagClass.mk w₁) (GenFlagClass.mk w₂)
      (fun cls => genJointInducedDensity CG2 csType6 F₁ F₂ cls.out *
        (genNormalisationFactor csType6 cls.out * phi.eval cls.out.forget))
      _ _ hw_ne hmem₁ hmem₂ hsummand_cls₁ hsummand_cls₂
      (fun x _ hne₁ hne₂ => hothers x hne₁ hne₂)
  rw [this, mul_add, hsummand₁, hsummand₂]

/-! ### S0F33: cs0Flag3 × cs0Flag3 (single witness) -/

theorem S0F33_witness_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F33_witness.forget = 4 :=
  S0F33_witness_emptyAutCount_bridge

theorem S0F33_witness_jointCount :
    genJointCount CG2 csType6 cs0Flag3 cs0Flag3 S0F33_witness = 2 :=
  S0F33_witness_jointCount_bridge

theorem S0F33_witness_jid_nf :
    genJointInducedDensity CG2 csType6 cs0Flag3 cs0Flag3 S0F33_witness *
      genNormalisationFactor csType6 S0F33_witness = 1/30 := by
  rw [jid_nf_5_3_4_4 cs0Flag3 cs0Flag3 S0F33_witness rfl rfl rfl rfl
    S0F33_witness_jointCount S0F33_witness_sigmaAutCount S0F33_witness_emptyAutCount]
  norm_num

set_option maxHeartbeats 4000000 in
private theorem S0F33_unique_class_of_jc_pos_tri_free
    (G : GenFlag CG2 csType6)
    (hjc : genJointCount CG2 csType6 cs0Flag3 cs0Flag3 G > 0)
    (hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType6 G S0F33_witness := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType6_product_structure cs0Flag3 cs0Flag3 rfl rfl
      (by intro i; fin_cases i <;> simp [cs0Flag3, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs0Flag3, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs0Flag3.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs0Flag3.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hno_adj_free : ¬G.str.1.Adj v3 v4 := by
    intro hadj; apply hno_tri
    change ∃ u v w : Fin G.size, G.str.1.Adj u v ∧ G.str.1.Adj v w ∧ G.str.1.Adj u w
    refine ⟨e₁.toFun ⟨0, by decide⟩, v3, v4, ?_, ?_, ?_⟩
    · rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
    · exact hadj
    · rw [he₁_0, ← he₂_0]; rw [hadj₂]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  refine ⟨φ, ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · change S0F33_witness.str.1.comap (⇑φ) = G.str.1
      have G_01 : G.str.1.Adj v0 v1 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
      have G_02 : G.str.1.Adj v0 v2 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
      have G_03 : G.str.1.Adj v0 v3 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
        rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
      have G_04 : G.str.1.Adj v0 v4 := by
        rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
        rw [hadj₂]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
      have G_n12 : ¬G.str.1.Adj v1 v2 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
      have G_n13 : ¬G.str.1.Adj v1 v3 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
      have G_n23 : ¬G.str.1.Adj v2 v3 := by
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
      have G_n14 : ¬G.str.1.Adj v1 v4 := by
        rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
        rw [hadj₂]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
      have G_n24 : ¬G.str.1.Adj v2 v4 := by
        rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
        rw [hadj₂]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
      have G_n34 : ¬G.str.1.Adj v3 v4 := hno_adj_free
      ext u w; simp only [SimpleGraph.comap_adj]
      rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
        rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
        change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
        first
        | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3]
        | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
        | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3]
        | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
        | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3]
        | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
        | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2]
        | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
        | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2]
        | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]) <;>
      all_goals (
        constructor <;> intro h
        · first
          | exact G_01 | exact G_01.symm | exact G_02 | exact G_02.symm
          | exact G_03 | exact G_03.symm | exact G_04 | exact G_04.symm
          | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
        · first
          | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
          | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
          | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
          | exact absurd h G_n14 | exact absurd h (fun x => G_n14 x.symm)
          | exact absurd h G_n24 | exact absurd h (fun x => G_n24 x.symm)
          | exact absurd h G_n34 | exact absurd h (fun x => G_n34 x.symm)
          | exact absurd h (fun x => x.ne rfl)
          | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
    · change S0F33_witness.str.2 ∘ (⇑φ) = G.str.2
      funext u; change S0F33_witness.str.2 (φ u) = G.str.2 u
      rcases hcover u with rfl | rfl | rfl | rfl | rfl
      · rw [hfwd_v0]; simp only [S0F33_witness]
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs0Flag3]
      · rw [hfwd_v1]; simp only [S0F33_witness]
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs0Flag3]
      · rw [hfwd_v2]; simp only [S0F33_witness]
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs0Flag3]
      · rw [hfwd_v3]; simp only [S0F33_witness]
        rw [hcol₁]; simp [cs0Flag3]
      · rw [hfwd_v4]; simp only [S0F33_witness]
        rw [hcol₂]; simp [cs0Flag3]
  · intro i; fin_cases i <;>
      simp only [S0F33_witness, Function.Embedding.coeFn_mk, Fin.castLE] <;>
      first
      | (change φ v0 = _; rw [hφ_emb ⟨0, by decide⟩]; rfl)
      | (change φ v1 = _; rw [hφ_emb ⟨1, by decide⟩]; rfl)
      | (change φ v2 = _; rw [hφ_emb ⟨2, by decide⟩]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd6_S0F33
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd6 cs0Flag3 cs0Flag3) = (1/30 : ℝ) * phi.eval cs0_flag_S0F33 := by
   apply avgProd6_eval_single_witness phi cs0Flag3 cs0Flag3 S0F33_witness cs0_flag_S0F33 (1/30) (by decide)
   · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
     exact ⟨⟨S0F33_witness.str, S0F33_witness.embedding, S0F33_witness.isInduced⟩, rfl⟩
   · have haut : (genFlagAutCount CG2 csType6 cs0Flag3 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag3]; norm_num
     rw [haut, one_mul, inv_one, one_mul, ← mul_assoc, S0F33_witness_jid_nf]
     congr 1
   · exact fun cls hne => avgProd_other_classes_zero_of_classification phi csType6 cs0Flag3 cs0Flag3
       S0F33_witness cls hne S0F33_unique_class_of_jc_pos_tri_free

/-! ### S0F34: cs0Flag3 × cs0Flag4 (dual witness) -/

theorem S0F34_witness_false_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F34_witness_false.forget = 1 :=
  S0F34_witness_false_emptyAutCount_bridge

theorem S0F34_witness_false_jointCount :
    genJointCount CG2 csType6 cs0Flag3 cs0Flag4 S0F34_witness_false = 1 :=
  S0F34_witness_false_jointCount_bridge

theorem S0F34_witness_false_jid_nf :
    genJointInducedDensity CG2 csType6 cs0Flag3 cs0Flag4 S0F34_witness_false *
      genNormalisationFactor csType6 S0F34_witness_false = 1/120 := by
  rw [jid_nf_5_3_4_4 cs0Flag3 cs0Flag4 S0F34_witness_false rfl rfl rfl rfl
    S0F34_witness_false_jointCount S0F34_witness_false_sigmaAutCount
    S0F34_witness_false_emptyAutCount]
  norm_num

theorem S0F34_witness_true_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F34_witness_true.forget = 1 :=
  S0F34_witness_true_emptyAutCount_bridge

theorem S0F34_witness_true_jointCount :
    genJointCount CG2 csType6 cs0Flag3 cs0Flag4 S0F34_witness_true = 1 :=
  S0F34_witness_true_jointCount_bridge

theorem S0F34_witness_true_jid_nf :
    genJointInducedDensity CG2 csType6 cs0Flag3 cs0Flag4 S0F34_witness_true *
      genNormalisationFactor csType6 S0F34_witness_true = 1/120 := by
  rw [jid_nf_5_3_4_4 cs0Flag3 cs0Flag4 S0F34_witness_true rfl rfl rfl rfl
    S0F34_witness_true_jointCount S0F34_witness_true_sigmaAutCount
    S0F34_witness_true_emptyAutCount]
  norm_num

set_option maxHeartbeats 4000000 in
private theorem S0F34_two_classes_of_jc_pos_tri_free
    (G : GenFlag CG2 csType6)
    (hjc : genJointCount CG2 csType6 cs0Flag3 cs0Flag4 G > 0)
    (_hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType6 G S0F34_witness_false ∨ GenFlagIso csType6 G S0F34_witness_true := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType6_product_structure cs0Flag3 cs0Flag4 rfl rfl
      (by intro i; fin_cases i <;> simp [cs0Flag3, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs0Flag4, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs0Flag3.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs0Flag4.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  have G_01 : G.str.1.Adj v0 v1 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_02 : G.str.1.Adj v0 v2 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_03 : G.str.1.Adj v0 v3 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_14 : G.str.1.Adj v1 v4 := by
    rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
    rw [hadj₂]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
  have G_n12 : ¬G.str.1.Adj v1 v2 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_n13 : ¬G.str.1.Adj v1 v3 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_n23 : ¬G.str.1.Adj v2 v3 := by
    rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_n04 : ¬G.str.1.Adj v0 v4 := by
    rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
    rw [hadj₂]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
  have G_n24 : ¬G.str.1.Adj v2 v4 := by
    rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
    rw [hadj₂]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
  let fwd : Fin G.size → Fin 5 := φ
  let inv : Fin 5 → Fin G.size := fun i =>
    if i = 0 then v0 else if i = 1 then v1 else if i = 2 then v2
    else if i = 3 then v3 else v4
  have hinv_0 : inv 0 = v0 := if_pos rfl
  have hinv_1 : inv 1 = v1 := by show inv 1 = v1; dsimp only [inv]; simp
  have hinv_2 : inv 2 = v2 := by show inv 2 = v2; dsimp only [inv]; simp [Fin.reduceEq]
  have hinv_3 : inv 3 = v3 := by show inv 3 = v3; dsimp only [inv]; simp [Fin.reduceEq]
  have hinv_4 : inv 4 = v4 := by show inv 4 = v4; dsimp only [inv]; simp [Fin.reduceEq]
  have hli : ∀ x, inv (fwd x) = x := by
    intro x; change inv (φ x) = x
    rcases hcover x with rfl | rfl | rfl | rfl | rfl
    · rw [hfwd_v0, hinv_0]
    · rw [hfwd_v1, hinv_1]
    · rw [hfwd_v2, hinv_2]
    · rw [hfwd_v3, hinv_3]
    · rw [hfwd_v4, hinv_4]
  have hri : ∀ x, fwd (inv x) = x := by
    intro x; change φ (inv x) = x
    fin_cases x <;> simp only [] <;>
      first
      | (change φ (inv 0) = 0; rw [hinv_0, hfwd_v0])
      | (change φ (inv 1) = 1; rw [hinv_1, hfwd_v1])
      | (change φ (inv 2) = 2; rw [hinv_2, hfwd_v2])
      | (change φ (inv 3) = 3; rw [hinv_3, hfwd_v3])
      | (change φ (inv 4) = 4; rw [hinv_4, hfwd_v4])
  let φ' : Fin G.size ≃ Fin 5 := ⟨fwd, inv, hli, hri⟩
  by_cases h34 : G.str.1.Adj v3 v4
  · right
    refine ⟨φ', ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change S0F34_witness_true.str.1.comap (⇑φ') = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3] | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2] | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]
          ) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm
            | exact G_02 | exact G_02.symm
            | exact G_03 | exact G_03.symm
            | exact G_14 | exact G_14.symm
            | exact h34 | exact h34.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h G_n24 | exact absurd h (fun x => G_n24 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change S0F34_witness_true.str.2 ∘ (⇑φ') = G.str.2
        funext u; change S0F34_witness_true.str.2 (φ u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, S0F34_witness_true] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs0Flag3])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs0Flag3])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs0Flag3])
          | (rw [hcol₁]; simp [cs0Flag3])
          | (rw [hcol₂]; simp [cs0Flag4])
    · intro i; fin_cases i <;>
        simp only [S0F34_witness_true, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change φ v0 = _; rw [hfwd_v0]; rfl)
        | (change φ v1 = _; rw [hfwd_v1]; rfl)
        | (change φ v2 = _; rw [hfwd_v2]; rfl)
  · left
    refine ⟨φ', ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change S0F34_witness_false.str.1.comap (⇑φ') = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3] | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2] | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]
          ) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm
            | exact G_02 | exact G_02.symm
            | exact G_03 | exact G_03.symm
            | exact G_14 | exact G_14.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h G_n24 | exact absurd h (fun x => G_n24 x.symm)
            | exact absurd h h34 | exact absurd h (fun x => h34 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change S0F34_witness_false.str.2 ∘ (⇑φ') = G.str.2
        funext u; change S0F34_witness_false.str.2 (φ u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, S0F34_witness_false] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs0Flag3])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs0Flag3])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs0Flag3])
          | (rw [hcol₁]; simp [cs0Flag3])
          | (rw [hcol₂]; simp [cs0Flag4])
    · intro i; fin_cases i <;>
        simp only [S0F34_witness_false, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change φ v0 = _; rw [hfwd_v0]; rfl)
        | (change φ v1 = _; rw [hfwd_v1]; rfl)
        | (change φ v2 = _; rw [hfwd_v2]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd6_S0F34
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd6 cs0Flag3 cs0Flag4) =
      (1/120 : ℝ) * phi.eval cs0_flag_S0F34F + (1/120 : ℝ) * phi.eval cs0_flag_S0F34T := by
   apply avgProd6_eval_dual_witness phi cs0Flag3 cs0Flag4
     S0F34_witness_false S0F34_witness_true cs0_flag_S0F34F cs0_flag_S0F34T (1/120) (1/120) (by decide)
     S0F34_witnesses_not_iso
   · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
     exact ⟨⟨S0F34_witness_false.str, S0F34_witness_false.embedding, S0F34_witness_false.isInduced⟩, rfl⟩
   · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
     exact ⟨⟨S0F34_witness_true.str, S0F34_witness_true.embedding, S0F34_witness_true.isInduced⟩, rfl⟩
   · have haut3 : (genFlagAutCount CG2 csType6 cs0Flag3 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag3]; norm_num
     have haut4 : (genFlagAutCount CG2 csType6 cs0Flag4 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag4]; norm_num
     rw [haut3, haut4, one_mul, inv_one, one_mul, ← mul_assoc, S0F34_witness_false_jid_nf]
     congr 1
   · have haut3 : (genFlagAutCount CG2 csType6 cs0Flag3 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag3]; norm_num
     have haut4 : (genFlagAutCount CG2 csType6 cs0Flag4 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag4]; norm_num
     rw [haut3, haut4, one_mul, inv_one, one_mul, ← mul_assoc, S0F34_witness_true_jid_nf]
     congr 1
   · intro cls hne₁ hne₂
     exact avgProd_other_classes_zero_of_dual_classification phi csType6 cs0Flag3 cs0Flag4
       S0F34_witness_false S0F34_witness_true cls hne₁ hne₂
       S0F34_two_classes_of_jc_pos_tri_free

/-! ### S0F35: cs0Flag3 × cs0Flag5 (dual witness) -/

theorem S0F35_witness_false_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F35_witness_false.forget = 1 :=
  S0F35_witness_false_emptyAutCount_bridge

theorem S0F35_witness_false_jointCount :
    genJointCount CG2 csType6 cs0Flag3 cs0Flag5 S0F35_witness_false = 1 :=
  S0F35_witness_false_jointCount_bridge

theorem S0F35_witness_false_jid_nf :
    genJointInducedDensity CG2 csType6 cs0Flag3 cs0Flag5 S0F35_witness_false *
      genNormalisationFactor csType6 S0F35_witness_false = 1/120 := by
  rw [jid_nf_5_3_4_4 cs0Flag3 cs0Flag5 S0F35_witness_false rfl rfl rfl rfl
    S0F35_witness_false_jointCount S0F35_witness_false_sigmaAutCount
    S0F35_witness_false_emptyAutCount]
  norm_num

theorem S0F35_witness_true_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F35_witness_true.forget = 1 :=
  S0F35_witness_true_emptyAutCount_bridge

theorem S0F35_witness_true_jointCount :
    genJointCount CG2 csType6 cs0Flag3 cs0Flag5 S0F35_witness_true = 1 :=
  S0F35_witness_true_jointCount_bridge

theorem S0F35_witness_true_jid_nf :
    genJointInducedDensity CG2 csType6 cs0Flag3 cs0Flag5 S0F35_witness_true *
      genNormalisationFactor csType6 S0F35_witness_true = 1/120 := by
  rw [jid_nf_5_3_4_4 cs0Flag3 cs0Flag5 S0F35_witness_true rfl rfl rfl rfl
    S0F35_witness_true_jointCount S0F35_witness_true_sigmaAutCount
    S0F35_witness_true_emptyAutCount]
  norm_num

set_option maxHeartbeats 4000000 in
private theorem S0F35_two_classes_of_jc_pos_tri_free
    (G : GenFlag CG2 csType6)
    (hjc : genJointCount CG2 csType6 cs0Flag3 cs0Flag5 G > 0)
    (_hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType6 G S0F35_witness_false ∨ GenFlagIso csType6 G S0F35_witness_true := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType6_product_structure cs0Flag3 cs0Flag5 rfl rfl
      (by intro i; fin_cases i <;> simp [cs0Flag3, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs0Flag5, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs0Flag3.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs0Flag5.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  have G_01 : G.str.1.Adj v0 v1 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_02 : G.str.1.Adj v0 v2 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_03 : G.str.1.Adj v0 v3 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_24 : G.str.1.Adj v2 v4 := by
    rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
    rw [hadj₂]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
  have G_n12 : ¬G.str.1.Adj v1 v2 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_n13 : ¬G.str.1.Adj v1 v3 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_n23 : ¬G.str.1.Adj v2 v3 := by
    rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_n04 : ¬G.str.1.Adj v0 v4 := by
    rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
    rw [hadj₂]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
  have G_n14 : ¬G.str.1.Adj v1 v4 := by
    rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
    rw [hadj₂]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
  let fwd : Fin G.size → Fin 5 := φ
  let inv : Fin 5 → Fin G.size := fun i =>
    if i = 0 then v0 else if i = 1 then v1 else if i = 2 then v2
    else if i = 3 then v3 else v4
  have hinv_0 : inv 0 = v0 := if_pos rfl
  have hinv_1 : inv 1 = v1 := by show inv 1 = v1; dsimp only [inv]; simp
  have hinv_2 : inv 2 = v2 := by show inv 2 = v2; dsimp only [inv]; simp [Fin.reduceEq]
  have hinv_3 : inv 3 = v3 := by show inv 3 = v3; dsimp only [inv]; simp [Fin.reduceEq]
  have hinv_4 : inv 4 = v4 := by show inv 4 = v4; dsimp only [inv]; simp [Fin.reduceEq]
  have hli : ∀ x, inv (fwd x) = x := by
    intro x; change inv (φ x) = x
    rcases hcover x with rfl | rfl | rfl | rfl | rfl
    · rw [hfwd_v0, hinv_0]
    · rw [hfwd_v1, hinv_1]
    · rw [hfwd_v2, hinv_2]
    · rw [hfwd_v3, hinv_3]
    · rw [hfwd_v4, hinv_4]
  have hri : ∀ x, fwd (inv x) = x := by
    intro x; change φ (inv x) = x
    fin_cases x <;> simp only [] <;>
      first
      | (change φ (inv 0) = 0; rw [hinv_0, hfwd_v0])
      | (change φ (inv 1) = 1; rw [hinv_1, hfwd_v1])
      | (change φ (inv 2) = 2; rw [hinv_2, hfwd_v2])
      | (change φ (inv 3) = 3; rw [hinv_3, hfwd_v3])
      | (change φ (inv 4) = 4; rw [hinv_4, hfwd_v4])
  let φ' : Fin G.size ≃ Fin 5 := ⟨fwd, inv, hli, hri⟩
  by_cases h34 : G.str.1.Adj v3 v4
  · right
    refine ⟨φ', ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change S0F35_witness_true.str.1.comap (⇑φ') = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3] | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2] | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]
          ) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm
            | exact G_02 | exact G_02.symm
            | exact G_03 | exact G_03.symm
            | exact G_24 | exact G_24.symm
            | exact h34 | exact h34.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h G_n14 | exact absurd h (fun x => G_n14 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change S0F35_witness_true.str.2 ∘ (⇑φ') = G.str.2
        funext u; change S0F35_witness_true.str.2 (φ u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, S0F35_witness_true] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs0Flag3])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs0Flag3])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs0Flag3])
          | (rw [hcol₁]; simp [cs0Flag3])
          | (rw [hcol₂]; simp [cs0Flag5])
    · intro i; fin_cases i <;>
        simp only [S0F35_witness_true, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change φ v0 = _; rw [hfwd_v0]; rfl)
        | (change φ v1 = _; rw [hfwd_v1]; rfl)
        | (change φ v2 = _; rw [hfwd_v2]; rfl)
  · left
    refine ⟨φ', ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change S0F35_witness_false.str.1.comap (⇑φ') = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3] | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2] | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]
          ) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm
            | exact G_02 | exact G_02.symm
            | exact G_03 | exact G_03.symm
            | exact G_24 | exact G_24.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h G_n14 | exact absurd h (fun x => G_n14 x.symm)
            | exact absurd h h34 | exact absurd h (fun x => h34 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change S0F35_witness_false.str.2 ∘ (⇑φ') = G.str.2
        funext u; change S0F35_witness_false.str.2 (φ u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, S0F35_witness_false] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs0Flag3])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs0Flag3])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs0Flag3])
          | (rw [hcol₁]; simp [cs0Flag3])
          | (rw [hcol₂]; simp [cs0Flag5])
    · intro i; fin_cases i <;>
        simp only [S0F35_witness_false, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change φ v0 = _; rw [hfwd_v0]; rfl)
        | (change φ v1 = _; rw [hfwd_v1]; rfl)
        | (change φ v2 = _; rw [hfwd_v2]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd6_S0F35
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd6 cs0Flag3 cs0Flag5) =
      (1/120 : ℝ) * phi.eval cs0_flag_S0F35F + (1/120 : ℝ) * phi.eval cs0_flag_S0F35T := by
   apply avgProd6_eval_dual_witness phi cs0Flag3 cs0Flag5
     S0F35_witness_false S0F35_witness_true cs0_flag_S0F35F cs0_flag_S0F35T (1/120) (1/120) (by decide)
     S0F35_witnesses_not_iso
   · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
     exact ⟨⟨S0F35_witness_false.str, S0F35_witness_false.embedding, S0F35_witness_false.isInduced⟩, rfl⟩
   · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
     exact ⟨⟨S0F35_witness_true.str, S0F35_witness_true.embedding, S0F35_witness_true.isInduced⟩, rfl⟩
   · have haut3 : (genFlagAutCount CG2 csType6 cs0Flag3 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag3]; norm_num
     have haut5 : (genFlagAutCount CG2 csType6 cs0Flag5 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag5]; norm_num
     rw [haut3, haut5, one_mul, inv_one, one_mul, ← mul_assoc, S0F35_witness_false_jid_nf]
     congr 1
   · have haut3 : (genFlagAutCount CG2 csType6 cs0Flag3 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag3]; norm_num
     have haut5 : (genFlagAutCount CG2 csType6 cs0Flag5 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag5]; norm_num
     rw [haut3, haut5, one_mul, inv_one, one_mul, ← mul_assoc, S0F35_witness_true_jid_nf]
     congr 1
   · intro cls hne₁ hne₂
     exact avgProd_other_classes_zero_of_dual_classification phi csType6 cs0Flag3 cs0Flag5
       S0F35_witness_false S0F35_witness_true cls hne₁ hne₂
       S0F35_two_classes_of_jc_pos_tri_free

/-! ### S0F36: cs0Flag3 × cs0Flag6 (dual witness) -/

theorem S0F36_witness_false_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F36_witness_false.forget = 2 :=
  S0F36_witness_false_emptyAutCount_bridge

theorem S0F36_witness_false_jointCount :
    genJointCount CG2 csType6 cs0Flag3 cs0Flag6 S0F36_witness_false = 1 :=
  S0F36_witness_false_jointCount_bridge

theorem S0F36_witness_false_jid_nf :
    genJointInducedDensity CG2 csType6 cs0Flag3 cs0Flag6 S0F36_witness_false *
      genNormalisationFactor csType6 S0F36_witness_false = 1/60 := by
  rw [jid_nf_5_3_4_4 cs0Flag3 cs0Flag6 S0F36_witness_false rfl rfl rfl rfl
    S0F36_witness_false_jointCount S0F36_witness_false_sigmaAutCount
    S0F36_witness_false_emptyAutCount]
  norm_num

theorem S0F36_witness_true_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F36_witness_true.forget = 4 :=
  S0F36_witness_true_emptyAutCount_bridge

theorem S0F36_witness_true_jointCount :
    genJointCount CG2 csType6 cs0Flag3 cs0Flag6 S0F36_witness_true = 1 :=
  S0F36_witness_true_jointCount_bridge

theorem S0F36_witness_true_jid_nf :
    genJointInducedDensity CG2 csType6 cs0Flag3 cs0Flag6 S0F36_witness_true *
      genNormalisationFactor csType6 S0F36_witness_true = 1/30 := by
  rw [jid_nf_5_3_4_4 cs0Flag3 cs0Flag6 S0F36_witness_true rfl rfl rfl rfl
    S0F36_witness_true_jointCount S0F36_witness_true_sigmaAutCount
    S0F36_witness_true_emptyAutCount]
  norm_num

set_option maxHeartbeats 4000000 in
private theorem S0F36_two_classes_of_jc_pos_tri_free
    (G : GenFlag CG2 csType6)
    (hjc : genJointCount CG2 csType6 cs0Flag3 cs0Flag6 G > 0)
    (_hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType6 G S0F36_witness_false ∨ GenFlagIso csType6 G S0F36_witness_true := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType6_product_structure cs0Flag3 cs0Flag6 rfl rfl
      (by intro i; fin_cases i <;> simp [cs0Flag3, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs0Flag6, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs0Flag3.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs0Flag6.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  have G_01 : G.str.1.Adj v0 v1 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_02 : G.str.1.Adj v0 v2 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_03 : G.str.1.Adj v0 v3 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_14 : G.str.1.Adj v1 v4 := by
    rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
    rw [hadj₂]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
  have G_24 : G.str.1.Adj v2 v4 := by
    rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
    rw [hadj₂]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
  have G_n12 : ¬G.str.1.Adj v1 v2 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_n13 : ¬G.str.1.Adj v1 v3 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_n23 : ¬G.str.1.Adj v2 v3 := by
    rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs0Flag3, SimpleGraph.fromRel_adj]
  have G_n04 : ¬G.str.1.Adj v0 v4 := by
    rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
    rw [hadj₂]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
  let fwd : Fin G.size → Fin 5 := φ
  let inv : Fin 5 → Fin G.size := fun i =>
    if i = 0 then v0 else if i = 1 then v1 else if i = 2 then v2
    else if i = 3 then v3 else v4
  have hinv_0 : inv 0 = v0 := if_pos rfl
  have hinv_1 : inv 1 = v1 := by show inv 1 = v1; dsimp only [inv]; simp
  have hinv_2 : inv 2 = v2 := by show inv 2 = v2; dsimp only [inv]; simp [Fin.reduceEq]
  have hinv_3 : inv 3 = v3 := by show inv 3 = v3; dsimp only [inv]; simp [Fin.reduceEq]
  have hinv_4 : inv 4 = v4 := by show inv 4 = v4; dsimp only [inv]; simp [Fin.reduceEq]
  have hli : ∀ x, inv (fwd x) = x := by
    intro x; change inv (φ x) = x
    rcases hcover x with rfl | rfl | rfl | rfl | rfl
    · rw [hfwd_v0, hinv_0]
    · rw [hfwd_v1, hinv_1]
    · rw [hfwd_v2, hinv_2]
    · rw [hfwd_v3, hinv_3]
    · rw [hfwd_v4, hinv_4]
  have hri : ∀ x, fwd (inv x) = x := by
    intro x; change φ (inv x) = x
    fin_cases x <;> simp only [] <;>
      first
      | (change φ (inv 0) = 0; rw [hinv_0, hfwd_v0])
      | (change φ (inv 1) = 1; rw [hinv_1, hfwd_v1])
      | (change φ (inv 2) = 2; rw [hinv_2, hfwd_v2])
      | (change φ (inv 3) = 3; rw [hinv_3, hfwd_v3])
      | (change φ (inv 4) = 4; rw [hinv_4, hfwd_v4])
  let φ' : Fin G.size ≃ Fin 5 := ⟨fwd, inv, hli, hri⟩
  by_cases h34 : G.str.1.Adj v3 v4
  · right
    refine ⟨φ', ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change S0F36_witness_true.str.1.comap (⇑φ') = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3] | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2] | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]
          ) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm
            | exact G_02 | exact G_02.symm
            | exact G_03 | exact G_03.symm
            | exact G_14 | exact G_14.symm
            | exact G_24 | exact G_24.symm
            | exact h34 | exact h34.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change S0F36_witness_true.str.2 ∘ (⇑φ') = G.str.2
        funext u; change S0F36_witness_true.str.2 (φ u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, S0F36_witness_true] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs0Flag3])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs0Flag3])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs0Flag3])
          | (rw [hcol₁]; simp [cs0Flag3])
          | (rw [hcol₂]; simp [cs0Flag6])
    · intro i; fin_cases i <;>
        simp only [S0F36_witness_true, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change φ v0 = _; rw [hfwd_v0]; rfl)
        | (change φ v1 = _; rw [hfwd_v1]; rfl)
        | (change φ v2 = _; rw [hfwd_v2]; rfl)
  · left
    refine ⟨φ', ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change S0F36_witness_false.str.1.comap (⇑φ') = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3] | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2] | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]
          ) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm
            | exact G_02 | exact G_02.symm
            | exact G_03 | exact G_03.symm
            | exact G_14 | exact G_14.symm
            | exact G_24 | exact G_24.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h h34 | exact absurd h (fun x => h34 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change S0F36_witness_false.str.2 ∘ (⇑φ') = G.str.2
        funext u; change S0F36_witness_false.str.2 (φ u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, S0F36_witness_false] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs0Flag3])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs0Flag3])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs0Flag3])
          | (rw [hcol₁]; simp [cs0Flag3])
          | (rw [hcol₂]; simp [cs0Flag6])
    · intro i; fin_cases i <;>
        simp only [S0F36_witness_false, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change φ v0 = _; rw [hfwd_v0]; rfl)
        | (change φ v1 = _; rw [hfwd_v1]; rfl)
        | (change φ v2 = _; rw [hfwd_v2]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd6_S0F36
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd6 cs0Flag3 cs0Flag6) =
      (1/60 : ℝ) * phi.eval cs0_flag_S0F36F + (1/30 : ℝ) * phi.eval cs0_flag_S0F36T := by
   apply avgProd6_eval_dual_witness phi cs0Flag3 cs0Flag6
     S0F36_witness_false S0F36_witness_true cs0_flag_S0F36F cs0_flag_S0F36T (1/60) (1/30) (by decide)
     S0F36_witnesses_not_iso
   · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
     exact ⟨⟨S0F36_witness_false.str, S0F36_witness_false.embedding, S0F36_witness_false.isInduced⟩, rfl⟩
   · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
     exact ⟨⟨S0F36_witness_true.str, S0F36_witness_true.embedding, S0F36_witness_true.isInduced⟩, rfl⟩
   · have haut3 : (genFlagAutCount CG2 csType6 cs0Flag3 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag3]; norm_num
     have haut6 : (genFlagAutCount CG2 csType6 cs0Flag6 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag6]; norm_num
     rw [haut3, haut6, one_mul, inv_one, one_mul, ← mul_assoc, S0F36_witness_false_jid_nf]
     congr 1
   · have haut3 : (genFlagAutCount CG2 csType6 cs0Flag3 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag3]; norm_num
     have haut6 : (genFlagAutCount CG2 csType6 cs0Flag6 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag6]; norm_num
     rw [haut3, haut6, one_mul, inv_one, one_mul, ← mul_assoc, S0F36_witness_true_jid_nf]
     congr 1
   · intro cls hne₁ hne₂
     exact avgProd_other_classes_zero_of_dual_classification phi csType6 cs0Flag3 cs0Flag6
       S0F36_witness_false S0F36_witness_true cls hne₁ hne₂
       S0F36_two_classes_of_jc_pos_tri_free

/-! ### S0F44: cs0Flag4 × cs0Flag4 (single witness) -/

theorem S0F44_witness_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F44_witness.forget = 2 :=
  S0F44_witness_emptyAutCount_bridge

theorem S0F44_witness_jointCount :
    genJointCount CG2 csType6 cs0Flag4 cs0Flag4 S0F44_witness = 2 :=
  S0F44_witness_jointCount_bridge

theorem S0F44_witness_jid_nf :
    genJointInducedDensity CG2 csType6 cs0Flag4 cs0Flag4 S0F44_witness *
      genNormalisationFactor csType6 S0F44_witness = 1/60 := by
  rw [jid_nf_5_3_4_4 cs0Flag4 cs0Flag4 S0F44_witness rfl rfl rfl rfl
    S0F44_witness_jointCount S0F44_witness_sigmaAutCount S0F44_witness_emptyAutCount]
  norm_num

set_option maxHeartbeats 4000000 in
private theorem S0F44_unique_class_of_jc_pos_tri_free
    (G : GenFlag CG2 csType6)
    (hjc : genJointCount CG2 csType6 cs0Flag4 cs0Flag4 G > 0)
    (hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType6 G S0F44_witness := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType6_product_structure cs0Flag4 cs0Flag4 rfl rfl
      (by intro i; fin_cases i <;> simp [cs0Flag4, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs0Flag4, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs0Flag4.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs0Flag4.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  have hno_adj_free : ¬G.str.1.Adj v3 v4 := by
    intro hadj; apply hno_tri
    change ∃ u v w : Fin G.size, G.str.1.Adj u v ∧ G.str.1.Adj v w ∧ G.str.1.Adj u w
    refine ⟨e₁.toFun ⟨1, by decide⟩, v3, v4, ?_, ?_, ?_⟩
    · rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
    · exact hadj
    · rw [he₁_1, ← he₂_1]; rw [hadj₂]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
  refine ⟨φ, ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · change S0F44_witness.str.1.comap (⇑φ) = G.str.1
      have G_01 : G.str.1.Adj v0 v1 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
      have G_02 : G.str.1.Adj v0 v2 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
      have G_13 : G.str.1.Adj v1 v3 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
      have G_14 : G.str.1.Adj v1 v4 := by
        rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
        rw [hadj₂]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
      have G_n12 : ¬G.str.1.Adj v1 v2 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
      have G_n03 : ¬G.str.1.Adj v0 v3 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
        rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
      have G_n23 : ¬G.str.1.Adj v2 v3 := by
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
      have G_n04 : ¬G.str.1.Adj v0 v4 := by
        rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
        rw [hadj₂]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
      have G_n24 : ¬G.str.1.Adj v2 v4 := by
        rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
        rw [hadj₂]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
      have G_n34 : ¬G.str.1.Adj v3 v4 := hno_adj_free
      ext u w; simp only [SimpleGraph.comap_adj]
      rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
        rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
        change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
        first
        | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3] | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
        | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
        | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
        | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2] | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
        | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]
        ) <;>
      all_goals (
        constructor <;> intro h
        · first
          | exact G_01 | exact G_01.symm
          | exact G_02 | exact G_02.symm
          | exact G_13 | exact G_13.symm
          | exact G_14 | exact G_14.symm
          | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
        · first
          | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
          | exact absurd h G_n03 | exact absurd h (fun x => G_n03 x.symm)
          | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
          | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
          | exact absurd h G_n24 | exact absurd h (fun x => G_n24 x.symm)
          | exact absurd h G_n34 | exact absurd h (fun x => G_n34 x.symm)
          | exact absurd h (fun x => x.ne rfl)
          | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
    · change S0F44_witness.str.2 ∘ (⇑φ) = G.str.2
      funext u; change S0F44_witness.str.2 (φ u) = G.str.2 u
      rcases hcover u with rfl | rfl | rfl | rfl | rfl
      · rw [hfwd_v0]; simp only [S0F44_witness]
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs0Flag4]
      · rw [hfwd_v1]; simp only [S0F44_witness]
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs0Flag4]
      · rw [hfwd_v2]; simp only [S0F44_witness]
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs0Flag4]
      · rw [hfwd_v3]; simp only [S0F44_witness]
        rw [hcol₁]; simp [cs0Flag4]
      · rw [hfwd_v4]; simp only [S0F44_witness]
        rw [hcol₂]; simp [cs0Flag4]
  · intro i; fin_cases i <;>
      simp only [S0F44_witness, Function.Embedding.coeFn_mk, Fin.castLE] <;>
      first
      | (change φ v0 = _; rw [hφ_emb ⟨0, by decide⟩]; rfl)
      | (change φ v1 = _; rw [hφ_emb ⟨1, by decide⟩]; rfl)
      | (change φ v2 = _; rw [hφ_emb ⟨2, by decide⟩]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd6_S0F44
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd6 cs0Flag4 cs0Flag4) = (1/60 : ℝ) * phi.eval cs0_flag_S0F44 := by 
   apply avgProd6_eval_single_witness phi cs0Flag4 cs0Flag4 S0F44_witness cs0_flag_S0F44 (1/60) (by decide)
   · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
     exact ⟨⟨S0F44_witness.str, S0F44_witness.embedding, S0F44_witness.isInduced⟩, rfl⟩
   · have haut : (genFlagAutCount CG2 csType6 cs0Flag4 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag4]; norm_num
     rw [haut, one_mul, inv_one, one_mul, ← mul_assoc, S0F44_witness_jid_nf]
     congr 1
   · exact fun cls hne => avgProd_other_classes_zero_of_classification phi csType6 cs0Flag4 cs0Flag4
       S0F44_witness cls hne S0F44_unique_class_of_jc_pos_tri_free

/-! ### S0F45: cs0Flag4 × cs0Flag5 (dual witness) -/

theorem S0F45_witness_false_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F45_witness_false.forget = 2 :=
  S0F45_witness_false_emptyAutCount_bridge

theorem S0F45_witness_false_jointCount :
    genJointCount CG2 csType6 cs0Flag4 cs0Flag5 S0F45_witness_false = 1 :=
  S0F45_witness_false_jointCount_bridge

theorem S0F45_witness_false_jid_nf :
    genJointInducedDensity CG2 csType6 cs0Flag4 cs0Flag5 S0F45_witness_false *
      genNormalisationFactor csType6 S0F45_witness_false = 1/60 := by
  rw [jid_nf_5_3_4_4 cs0Flag4 cs0Flag5 S0F45_witness_false rfl rfl rfl rfl
    S0F45_witness_false_jointCount S0F45_witness_false_sigmaAutCount
    S0F45_witness_false_emptyAutCount]
  norm_num

theorem S0F45_witness_true_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F45_witness_true.forget = 2 :=
  S0F45_witness_true_emptyAutCount_bridge

theorem S0F45_witness_true_jointCount :
    genJointCount CG2 csType6 cs0Flag4 cs0Flag5 S0F45_witness_true = 1 :=
  S0F45_witness_true_jointCount_bridge

theorem S0F45_witness_true_jid_nf :
    genJointInducedDensity CG2 csType6 cs0Flag4 cs0Flag5 S0F45_witness_true *
      genNormalisationFactor csType6 S0F45_witness_true = 1/60 := by
  rw [jid_nf_5_3_4_4 cs0Flag4 cs0Flag5 S0F45_witness_true rfl rfl rfl rfl
    S0F45_witness_true_jointCount S0F45_witness_true_sigmaAutCount
    S0F45_witness_true_emptyAutCount]
  norm_num

set_option maxHeartbeats 4000000 in
private theorem S0F45_two_classes_of_jc_pos_tri_free
    (G : GenFlag CG2 csType6)
    (hjc : genJointCount CG2 csType6 cs0Flag4 cs0Flag5 G > 0)
    (_hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType6 G S0F45_witness_false ∨ GenFlagIso csType6 G S0F45_witness_true := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType6_product_structure cs0Flag4 cs0Flag5 rfl rfl
      (by intro i; fin_cases i <;> simp [cs0Flag4, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs0Flag5, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs0Flag4.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs0Flag5.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  have G_01 : G.str.1.Adj v0 v1 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
  have G_02 : G.str.1.Adj v0 v2 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
  have G_13 : G.str.1.Adj v1 v3 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
    rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
  have G_24 : G.str.1.Adj v2 v4 := by
    rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
    rw [hadj₂]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
  have G_n12 : ¬G.str.1.Adj v1 v2 := by
    rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
        show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
  have G_n03 : ¬G.str.1.Adj v0 v3 := by
    rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
    rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
  have G_n23 : ¬G.str.1.Adj v2 v3 := by
    rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
    rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
  have G_n04 : ¬G.str.1.Adj v0 v4 := by
    rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
    rw [hadj₂]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
  have G_n14 : ¬G.str.1.Adj v1 v4 := by
    rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
    rw [hadj₂]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
  let fwd : Fin G.size → Fin 5 := φ
  let inv : Fin 5 → Fin G.size := fun i =>
    if i = 0 then v0 else if i = 1 then v1 else if i = 2 then v2
    else if i = 3 then v3 else v4
  have hinv_0 : inv 0 = v0 := if_pos rfl
  have hinv_1 : inv 1 = v1 := by show inv 1 = v1; dsimp only [inv]; simp
  have hinv_2 : inv 2 = v2 := by show inv 2 = v2; dsimp only [inv]; simp [Fin.reduceEq]
  have hinv_3 : inv 3 = v3 := by show inv 3 = v3; dsimp only [inv]; simp [Fin.reduceEq]
  have hinv_4 : inv 4 = v4 := by show inv 4 = v4; dsimp only [inv]; simp [Fin.reduceEq]
  have hli : ∀ x, inv (fwd x) = x := by
    intro x; change inv (φ x) = x
    rcases hcover x with rfl | rfl | rfl | rfl | rfl
    · rw [hfwd_v0, hinv_0]
    · rw [hfwd_v1, hinv_1]
    · rw [hfwd_v2, hinv_2]
    · rw [hfwd_v3, hinv_3]
    · rw [hfwd_v4, hinv_4]
  have hri : ∀ x, fwd (inv x) = x := by
    intro x; change φ (inv x) = x
    fin_cases x <;> simp only [] <;>
      first
      | (change φ (inv 0) = 0; rw [hinv_0, hfwd_v0])
      | (change φ (inv 1) = 1; rw [hinv_1, hfwd_v1])
      | (change φ (inv 2) = 2; rw [hinv_2, hfwd_v2])
      | (change φ (inv 3) = 3; rw [hinv_3, hfwd_v3])
      | (change φ (inv 4) = 4; rw [hinv_4, hfwd_v4])
  let φ' : Fin G.size ≃ Fin 5 := ⟨fwd, inv, hli, hri⟩
  by_cases h34 : G.str.1.Adj v3 v4
  · right
    refine ⟨φ', ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change S0F45_witness_true.str.1.comap (⇑φ') = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3] | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2] | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]
          ) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm
            | exact G_02 | exact G_02.symm
            | exact G_13 | exact G_13.symm
            | exact G_24 | exact G_24.symm
            | exact h34 | exact h34.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n03 | exact absurd h (fun x => G_n03 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h G_n14 | exact absurd h (fun x => G_n14 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change S0F45_witness_true.str.2 ∘ (⇑φ') = G.str.2
        funext u; change S0F45_witness_true.str.2 (φ u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, S0F45_witness_true] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs0Flag4])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs0Flag4])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs0Flag4])
          | (rw [hcol₁]; simp [cs0Flag4])
          | (rw [hcol₂]; simp [cs0Flag5])
    · intro i; fin_cases i <;>
        simp only [S0F45_witness_true, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change φ v0 = _; rw [hfwd_v0]; rfl)
        | (change φ v1 = _; rw [hfwd_v1]; rfl)
        | (change φ v2 = _; rw [hfwd_v2]; rfl)
  · left
    refine ⟨φ', ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · change S0F45_witness_false.str.1.comap (⇑φ') = G.str.1
        ext u w; simp only [SimpleGraph.comap_adj]
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
          change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
          first
          | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3] | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
          | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
          | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
          | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2] | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
          | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]
          ) <;>
        all_goals (
          constructor <;> intro h
          · first
            | exact G_01 | exact G_01.symm
            | exact G_02 | exact G_02.symm
            | exact G_13 | exact G_13.symm
            | exact G_24 | exact G_24.symm
            | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
          · first
            | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
            | exact absurd h G_n03 | exact absurd h (fun x => G_n03 x.symm)
            | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
            | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
            | exact absurd h G_n14 | exact absurd h (fun x => G_n14 x.symm)
            | exact absurd h h34 | exact absurd h (fun x => h34 x.symm)
            | exact absurd h (fun x => x.ne rfl)
            | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
      · change S0F45_witness_false.str.2 ∘ (⇑φ') = G.str.2
        funext u; change S0F45_witness_false.str.2 (φ u) = G.str.2 u
        rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
          simp only [hfwd_v0, hfwd_v1, hfwd_v2, hfwd_v3, hfwd_v4, S0F45_witness_false] <;>
          first
          | (rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs0Flag4])
          | (rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs0Flag4])
          | (rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs0Flag4])
          | (rw [hcol₁]; simp [cs0Flag4])
          | (rw [hcol₂]; simp [cs0Flag5])
    · intro i; fin_cases i <;>
        simp only [S0F45_witness_false, Function.Embedding.coeFn_mk, Fin.castLE] <;>
        first
        | (change φ v0 = _; rw [hfwd_v0]; rfl)
        | (change φ v1 = _; rw [hfwd_v1]; rfl)
        | (change φ v2 = _; rw [hfwd_v2]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd6_S0F45
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd6 cs0Flag4 cs0Flag5) =
      (1/60 : ℝ) * phi.eval cs0_flag_S0F45F + (1/60 : ℝ) * phi.eval cs0_flag_S0F45T := by 
   apply avgProd6_eval_dual_witness phi cs0Flag4 cs0Flag5
     S0F45_witness_false S0F45_witness_true cs0_flag_S0F45F cs0_flag_S0F45T (1/60) (1/60) (by decide)
     S0F45_witnesses_not_iso
   · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
     exact ⟨⟨S0F45_witness_false.str, S0F45_witness_false.embedding, S0F45_witness_false.isInduced⟩, rfl⟩
   · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
     exact ⟨⟨S0F45_witness_true.str, S0F45_witness_true.embedding, S0F45_witness_true.isInduced⟩, rfl⟩
   · have haut4 : (genFlagAutCount CG2 csType6 cs0Flag4 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag4]; norm_num
     have haut5 : (genFlagAutCount CG2 csType6 cs0Flag5 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag5]; norm_num
     rw [haut4, haut5, one_mul, inv_one, one_mul, ← mul_assoc, S0F45_witness_false_jid_nf]
     congr 1
   · have haut4 : (genFlagAutCount CG2 csType6 cs0Flag4 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag4]; norm_num
     have haut5 : (genFlagAutCount CG2 csType6 cs0Flag5 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag5]; norm_num
     rw [haut4, haut5, one_mul, inv_one, one_mul, ← mul_assoc, S0F45_witness_true_jid_nf]
     congr 1
   · intro cls hne₁ hne₂
     exact avgProd_other_classes_zero_of_dual_classification phi csType6 cs0Flag4 cs0Flag5
       S0F45_witness_false S0F45_witness_true cls hne₁ hne₂
       S0F45_two_classes_of_jc_pos_tri_free

/-! ### S0F46: cs0Flag4 × cs0Flag6 (single witness) -/

theorem S0F46_witness_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F46_witness.forget = 2 :=
  S0F46_witness_emptyAutCount_bridge

theorem S0F46_witness_jointCount :
    genJointCount CG2 csType6 cs0Flag4 cs0Flag6 S0F46_witness = 1 :=
  S0F46_witness_jointCount_bridge

theorem S0F46_witness_jid_nf :
    genJointInducedDensity CG2 csType6 cs0Flag4 cs0Flag6 S0F46_witness *
      genNormalisationFactor csType6 S0F46_witness = 1/60 := by
  rw [jid_nf_5_3_4_4 cs0Flag4 cs0Flag6 S0F46_witness rfl rfl rfl rfl
    S0F46_witness_jointCount S0F46_witness_sigmaAutCount S0F46_witness_emptyAutCount]
  norm_num

set_option maxHeartbeats 4000000 in
private theorem S0F46_unique_class_of_jc_pos_tri_free
    (G : GenFlag CG2 csType6)
    (hjc : genJointCount CG2 csType6 cs0Flag4 cs0Flag6 G > 0)
    (hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType6 G S0F46_witness := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType6_product_structure cs0Flag4 cs0Flag6 rfl rfl
      (by intro i; fin_cases i <;> simp [cs0Flag4, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs0Flag6, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs0Flag4.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs0Flag6.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  have hno_adj_free : ¬G.str.1.Adj v3 v4 := by
    intro hadj; apply hno_tri
    change ∃ u v w : Fin G.size, G.str.1.Adj u v ∧ G.str.1.Adj v w ∧ G.str.1.Adj u w
    refine ⟨e₁.toFun ⟨1, by decide⟩, v3, v4, ?_, ?_, ?_⟩
    · rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
    · exact hadj
    · rw [he₁_1, ← he₂_1]; rw [hadj₂]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
  refine ⟨φ, ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · change S0F46_witness.str.1.comap (⇑φ) = G.str.1
      have G_01 : G.str.1.Adj v0 v1 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
      have G_02 : G.str.1.Adj v0 v2 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
      have G_13 : G.str.1.Adj v1 v3 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
      have G_14 : G.str.1.Adj v1 v4 := by
        rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
        rw [hadj₂]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
      have G_24 : G.str.1.Adj v2 v4 := by
        rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
        rw [hadj₂]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
      have G_n12 : ¬G.str.1.Adj v1 v2 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
      have G_n03 : ¬G.str.1.Adj v0 v3 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
        rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
      have G_n23 : ¬G.str.1.Adj v2 v3 := by
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag4, SimpleGraph.fromRel_adj]
      have G_n04 : ¬G.str.1.Adj v0 v4 := by
        rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
        rw [hadj₂]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
      have G_n34 : ¬G.str.1.Adj v3 v4 := hno_adj_free
      ext u w; simp only [SimpleGraph.comap_adj]
      rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
        rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
        change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
        first
        | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3] | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
        | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
        | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
        | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2] | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
        | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]
        ) <;>
      all_goals (
        constructor <;> intro h
        · first
          | exact G_01 | exact G_01.symm
          | exact G_02 | exact G_02.symm
          | exact G_13 | exact G_13.symm
          | exact G_14 | exact G_14.symm
          | exact G_24 | exact G_24.symm
          | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
        · first
          | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
          | exact absurd h G_n03 | exact absurd h (fun x => G_n03 x.symm)
          | exact absurd h G_n23 | exact absurd h (fun x => G_n23 x.symm)
          | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
          | exact absurd h G_n34 | exact absurd h (fun x => G_n34 x.symm)
          | exact absurd h (fun x => x.ne rfl)
          | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
    · change S0F46_witness.str.2 ∘ (⇑φ) = G.str.2
      funext u; change S0F46_witness.str.2 (φ u) = G.str.2 u
      rcases hcover u with rfl | rfl | rfl | rfl | rfl
      · rw [hfwd_v0]; simp only [S0F46_witness]
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs0Flag4]
      · rw [hfwd_v1]; simp only [S0F46_witness]
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs0Flag4]
      · rw [hfwd_v2]; simp only [S0F46_witness]
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs0Flag4]
      · rw [hfwd_v3]; simp only [S0F46_witness]
        rw [hcol₁]; simp [cs0Flag4]
      · rw [hfwd_v4]; simp only [S0F46_witness]
        rw [hcol₂]; simp [cs0Flag6]
  · intro i; fin_cases i <;>
      simp only [S0F46_witness, Function.Embedding.coeFn_mk, Fin.castLE] <;>
      first
      | (change φ v0 = _; rw [hφ_emb ⟨0, by decide⟩]; rfl)
      | (change φ v1 = _; rw [hφ_emb ⟨1, by decide⟩]; rfl)
      | (change φ v2 = _; rw [hφ_emb ⟨2, by decide⟩]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd6_S0F46
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd6 cs0Flag4 cs0Flag6) = (1/60 : ℝ) * phi.eval cs0_flag_S0F46 := by 
   apply avgProd6_eval_single_witness phi cs0Flag4 cs0Flag6 S0F46_witness cs0_flag_S0F46 (1/60) (by decide)
   · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
     exact ⟨⟨S0F46_witness.str, S0F46_witness.embedding, S0F46_witness.isInduced⟩, rfl⟩
   · have haut4 : (genFlagAutCount CG2 csType6 cs0Flag4 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag4]; norm_num
     have haut6 : (genFlagAutCount CG2 csType6 cs0Flag6 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag6]; norm_num
     rw [haut4, haut6, one_mul, inv_one, one_mul, ← mul_assoc, S0F46_witness_jid_nf]
     congr 1
   · exact fun cls hne => avgProd_other_classes_zero_of_classification phi csType6 cs0Flag4 cs0Flag6
       S0F46_witness cls hne S0F46_unique_class_of_jc_pos_tri_free

/-! ### S0F55: cs0Flag5 × cs0Flag5 (single witness) -/

theorem S0F55_witness_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F55_witness.forget = 2 :=
  S0F55_witness_emptyAutCount_bridge

theorem S0F55_witness_jointCount :
    genJointCount CG2 csType6 cs0Flag5 cs0Flag5 S0F55_witness = 2 :=
  S0F55_witness_jointCount_bridge

theorem S0F55_witness_jid_nf :
    genJointInducedDensity CG2 csType6 cs0Flag5 cs0Flag5 S0F55_witness *
      genNormalisationFactor csType6 S0F55_witness = 1/60 := by
  rw [jid_nf_5_3_4_4 cs0Flag5 cs0Flag5 S0F55_witness rfl rfl rfl rfl
    S0F55_witness_jointCount S0F55_witness_sigmaAutCount S0F55_witness_emptyAutCount]
  norm_num

set_option maxHeartbeats 4000000 in
private theorem S0F55_unique_class_of_jc_pos_tri_free
    (G : GenFlag CG2 csType6)
    (hjc : genJointCount CG2 csType6 cs0Flag5 cs0Flag5 G > 0)
    (hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType6 G S0F55_witness := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType6_product_structure cs0Flag5 cs0Flag5 rfl rfl
      (by intro i; fin_cases i <;> simp [cs0Flag5, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs0Flag5, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs0Flag5.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs0Flag5.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  have hno_adj_free : ¬G.str.1.Adj v3 v4 := by
    intro hadj; apply hno_tri
    change ∃ u v w : Fin G.size, G.str.1.Adj u v ∧ G.str.1.Adj v w ∧ G.str.1.Adj u w
    refine ⟨e₁.toFun ⟨2, by decide⟩, v3, v4, ?_, ?_, ?_⟩
    · rw [hadj₁]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
    · exact hadj
    · rw [he₁_2, ← he₂_2]; rw [hadj₂]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
  refine ⟨φ, ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · change S0F55_witness.str.1.comap (⇑φ) = G.str.1
      have G_01 : G.str.1.Adj v0 v1 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
      have G_02 : G.str.1.Adj v0 v2 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
      have G_23 : G.str.1.Adj v2 v3 := by
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
      have G_24 : G.str.1.Adj v2 v4 := by
        rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
        rw [hadj₂]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
      have G_n12 : ¬G.str.1.Adj v1 v2 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
      have G_n03 : ¬G.str.1.Adj v0 v3 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
        rw [hadj₁]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
      have G_n13 : ¬G.str.1.Adj v1 v3 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
      have G_n04 : ¬G.str.1.Adj v0 v4 := by
        rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
        rw [hadj₂]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
      have G_n14 : ¬G.str.1.Adj v1 v4 := by
        rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
        rw [hadj₂]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
      have G_n34 : ¬G.str.1.Adj v3 v4 := hno_adj_free
      ext u w; simp only [SimpleGraph.comap_adj]
      rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
        rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
        change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
        first
        | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3] | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
        | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
        | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
        | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2] | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
        | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]
        ) <;>
      all_goals (
        constructor <;> intro h
        · first
          | exact G_01 | exact G_01.symm
          | exact G_02 | exact G_02.symm
          | exact G_23 | exact G_23.symm
          | exact G_24 | exact G_24.symm
          | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
        · first
          | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
          | exact absurd h G_n03 | exact absurd h (fun x => G_n03 x.symm)
          | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
          | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
          | exact absurd h G_n14 | exact absurd h (fun x => G_n14 x.symm)
          | exact absurd h G_n34 | exact absurd h (fun x => G_n34 x.symm)
          | exact absurd h (fun x => x.ne rfl)
          | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
    · change S0F55_witness.str.2 ∘ (⇑φ) = G.str.2
      funext u; change S0F55_witness.str.2 (φ u) = G.str.2 u
      rcases hcover u with rfl | rfl | rfl | rfl | rfl
      · rw [hfwd_v0]; simp only [S0F55_witness]
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs0Flag5]
      · rw [hfwd_v1]; simp only [S0F55_witness]
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs0Flag5]
      · rw [hfwd_v2]; simp only [S0F55_witness]
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs0Flag5]
      · rw [hfwd_v3]; simp only [S0F55_witness]
        rw [hcol₁]; simp [cs0Flag5]
      · rw [hfwd_v4]; simp only [S0F55_witness]
        rw [hcol₂]; simp [cs0Flag5]
  · intro i; fin_cases i <;>
      simp only [S0F55_witness, Function.Embedding.coeFn_mk, Fin.castLE] <;>
      first
      | (change φ v0 = _; rw [hφ_emb ⟨0, by decide⟩]; rfl)
      | (change φ v1 = _; rw [hφ_emb ⟨1, by decide⟩]; rfl)
      | (change φ v2 = _; rw [hφ_emb ⟨2, by decide⟩]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd6_S0F55
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd6 cs0Flag5 cs0Flag5) = (1/60 : ℝ) * phi.eval cs0_flag_S0F55 := by 
   apply avgProd6_eval_single_witness phi cs0Flag5 cs0Flag5 S0F55_witness cs0_flag_S0F55 (1/60) (by decide)
   · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
     exact ⟨⟨S0F55_witness.str, S0F55_witness.embedding, S0F55_witness.isInduced⟩, rfl⟩
   · have haut : (genFlagAutCount CG2 csType6 cs0Flag5 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag5]; norm_num
     rw [haut, one_mul, inv_one, one_mul, ← mul_assoc, S0F55_witness_jid_nf]
     congr 1
   · exact fun cls hne => avgProd_other_classes_zero_of_classification phi csType6 cs0Flag5 cs0Flag5
       S0F55_witness cls hne S0F55_unique_class_of_jc_pos_tri_free

/-! ### S0F56: cs0Flag5 × cs0Flag6 (single witness) -/

theorem S0F56_witness_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F56_witness.forget = 2 :=
  S0F56_witness_emptyAutCount_bridge

theorem S0F56_witness_jointCount :
    genJointCount CG2 csType6 cs0Flag5 cs0Flag6 S0F56_witness = 1 :=
  S0F56_witness_jointCount_bridge

theorem S0F56_witness_jid_nf :
    genJointInducedDensity CG2 csType6 cs0Flag5 cs0Flag6 S0F56_witness *
      genNormalisationFactor csType6 S0F56_witness = 1/60 := by
  rw [jid_nf_5_3_4_4 cs0Flag5 cs0Flag6 S0F56_witness rfl rfl rfl rfl
    S0F56_witness_jointCount S0F56_witness_sigmaAutCount S0F56_witness_emptyAutCount]
  norm_num

set_option maxHeartbeats 4000000 in
private theorem S0F56_unique_class_of_jc_pos_tri_free
    (G : GenFlag CG2 csType6)
    (hjc : genJointCount CG2 csType6 cs0Flag5 cs0Flag6 G > 0)
    (hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType6 G S0F56_witness := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType6_product_structure cs0Flag5 cs0Flag6 rfl rfl
      (by intro i; fin_cases i <;> simp [cs0Flag5, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs0Flag6, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs0Flag5.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs0Flag6.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  have hno_adj_free : ¬G.str.1.Adj v3 v4 := by
    intro hadj; apply hno_tri
    change ∃ u v w : Fin G.size, G.str.1.Adj u v ∧ G.str.1.Adj v w ∧ G.str.1.Adj u w
    refine ⟨e₁.toFun ⟨2, by decide⟩, v3, v4, ?_, ?_, ?_⟩
    · rw [hadj₁]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
    · exact hadj
    · rw [he₁_2, ← he₂_2]; rw [hadj₂]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
  refine ⟨φ, ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · change S0F56_witness.str.1.comap (⇑φ) = G.str.1
      have G_01 : G.str.1.Adj v0 v1 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
      have G_02 : G.str.1.Adj v0 v2 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
      have G_23 : G.str.1.Adj v2 v3 := by
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
      have G_14 : G.str.1.Adj v1 v4 := by
        rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
        rw [hadj₂]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
      have G_24 : G.str.1.Adj v2 v4 := by
        rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
        rw [hadj₂]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
      have G_n12 : ¬G.str.1.Adj v1 v2 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
      have G_n03 : ¬G.str.1.Adj v0 v3 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
        rw [hadj₁]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
      have G_n13 : ¬G.str.1.Adj v1 v3 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs0Flag5, SimpleGraph.fromRel_adj]
      have G_n04 : ¬G.str.1.Adj v0 v4 := by
        rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
        rw [hadj₂]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
      have G_n34 : ¬G.str.1.Adj v3 v4 := hno_adj_free
      ext u w; simp only [SimpleGraph.comap_adj]
      rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
        rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
        change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
        first
        | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3] | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
        | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
        | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
        | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2] | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
        | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]
        ) <;>
      all_goals (
        constructor <;> intro h
        · first
          | exact G_01 | exact G_01.symm
          | exact G_02 | exact G_02.symm
          | exact G_23 | exact G_23.symm
          | exact G_14 | exact G_14.symm
          | exact G_24 | exact G_24.symm
          | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
        · first
          | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
          | exact absurd h G_n03 | exact absurd h (fun x => G_n03 x.symm)
          | exact absurd h G_n13 | exact absurd h (fun x => G_n13 x.symm)
          | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
          | exact absurd h G_n34 | exact absurd h (fun x => G_n34 x.symm)
          | exact absurd h (fun x => x.ne rfl)
          | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
    · change S0F56_witness.str.2 ∘ (⇑φ) = G.str.2
      funext u; change S0F56_witness.str.2 (φ u) = G.str.2 u
      rcases hcover u with rfl | rfl | rfl | rfl | rfl
      · rw [hfwd_v0]; simp only [S0F56_witness]
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs0Flag5]
      · rw [hfwd_v1]; simp only [S0F56_witness]
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs0Flag5]
      · rw [hfwd_v2]; simp only [S0F56_witness]
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs0Flag5]
      · rw [hfwd_v3]; simp only [S0F56_witness]
        rw [hcol₁]; simp [cs0Flag5]
      · rw [hfwd_v4]; simp only [S0F56_witness]
        rw [hcol₂]; simp [cs0Flag6]
  · intro i; fin_cases i <;>
      simp only [S0F56_witness, Function.Embedding.coeFn_mk, Fin.castLE] <;>
      first
      | (change φ v0 = _; rw [hφ_emb ⟨0, by decide⟩]; rfl)
      | (change φ v1 = _; rw [hφ_emb ⟨1, by decide⟩]; rfl)
      | (change φ v2 = _; rw [hφ_emb ⟨2, by decide⟩]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd6_S0F56
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd6 cs0Flag5 cs0Flag6) = (1/60 : ℝ) * phi.eval cs0_flag_S0F56 := by 
   apply avgProd6_eval_single_witness phi cs0Flag5 cs0Flag6 S0F56_witness cs0_flag_S0F56 (1/60) (by decide)
   · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
     exact ⟨⟨S0F56_witness.str, S0F56_witness.embedding, S0F56_witness.isInduced⟩, rfl⟩
   · have haut5 : (genFlagAutCount CG2 csType6 cs0Flag5 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag5]; norm_num
     have haut6 : (genFlagAutCount CG2 csType6 cs0Flag6 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag6]; norm_num
     rw [haut5, haut6, one_mul, inv_one, one_mul, ← mul_assoc, S0F56_witness_jid_nf]
     congr 1
   · exact fun cls hne => avgProd_other_classes_zero_of_classification phi csType6 cs0Flag5 cs0Flag6
       S0F56_witness cls hne S0F56_unique_class_of_jc_pos_tri_free

/-! ### S0F66: cs0Flag6 × cs0Flag6 (single witness) -/

theorem S0F66_witness_emptyAutCount :
    genFlagAutCount CG2 (GenFlagType.empty CG2) S0F66_witness.forget = 12 :=
  S0F66_witness_emptyAutCount_bridge

theorem S0F66_witness_jointCount :
    genJointCount CG2 csType6 cs0Flag6 cs0Flag6 S0F66_witness = 2 :=
  S0F66_witness_jointCount_bridge

theorem S0F66_witness_jid_nf :
    genJointInducedDensity CG2 csType6 cs0Flag6 cs0Flag6 S0F66_witness *
      genNormalisationFactor csType6 S0F66_witness = 1/10 := by
  rw [jid_nf_5_3_4_4 cs0Flag6 cs0Flag6 S0F66_witness rfl rfl rfl rfl
    S0F66_witness_jointCount S0F66_witness_sigmaAutCount S0F66_witness_emptyAutCount]
  norm_num

set_option maxHeartbeats 4000000 in
private theorem S0F66_unique_class_of_jc_pos_tri_free
    (G : GenFlag CG2 csType6)
    (hjc : genJointCount CG2 csType6 cs0Flag6 cs0Flag6 G > 0)
    (hno_tri : ¬∃ u v w : Fin G.forget.size,
      G.forget.str.1.Adj u v ∧ G.forget.str.1.Adj v w ∧
      G.forget.str.1.Adj u w) :
    GenFlagIso csType6 G S0F66_witness := by
  obtain ⟨hGsize, e₁, e₂, φ, hφ_emb, hφ_e₁, hφ_e₂, he₁_compat, he₂_compat,
          hadj₁, hadj₂, hcol₁, hcol₂, he_ne, he₁_3_not_emb, he₂_3_not_emb, hcover⟩ :=
    csType6_product_structure cs0Flag6 cs0Flag6 rfl rfl
      (by intro i; fin_cases i <;> simp [cs0Flag6, Fin.castSucc])
      (by intro i; fin_cases i <;> simp [cs0Flag6, Fin.castSucc])
      G hjc
  set v0 := G.embedding ⟨0, by decide⟩ with hv0_def
  set v1 := G.embedding ⟨1, by decide⟩ with hv1_def
  set v2 := G.embedding ⟨2, by decide⟩ with hv2_def
  set v3 := e₁.toFun ⟨3, by show 3 < cs0Flag6.size; decide⟩ with hv3_def
  set v4 := e₂.toFun ⟨3, by show 3 < cs0Flag6.size; decide⟩ with hv4_def
  have he₁_0 := he₁_compat ⟨0, by decide⟩
  have he₁_1 := he₁_compat ⟨1, by decide⟩
  have he₁_2 := he₁_compat ⟨2, by decide⟩
  have he₂_0 := he₂_compat ⟨0, by decide⟩
  have he₂_1 := he₂_compat ⟨1, by decide⟩
  have he₂_2 := he₂_compat ⟨2, by decide⟩
  have hfwd_v0 : φ v0 = 0 := hφ_emb ⟨0, by decide⟩
  have hfwd_v1 : φ v1 = 1 := hφ_emb ⟨1, by decide⟩
  have hfwd_v2 : φ v2 = 2 := hφ_emb ⟨2, by decide⟩
  have hfwd_v3 : φ v3 = (3 : Fin 5) := hφ_e₁
  have hfwd_v4 : φ v4 = (4 : Fin 5) := hφ_e₂
  have hno_adj_free : ¬G.str.1.Adj v3 v4 := by
    intro hadj; apply hno_tri
    change ∃ u v w : Fin G.size, G.str.1.Adj u v ∧ G.str.1.Adj v w ∧ G.str.1.Adj u w
    refine ⟨e₁.toFun ⟨1, by decide⟩, v3, v4, ?_, ?_, ?_⟩
    · rw [hadj₁]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
    · exact hadj
    · rw [he₁_1, ← he₂_1]; rw [hadj₂]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
  refine ⟨φ, ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · change S0F66_witness.str.1.comap (⇑φ) = G.str.1
      have G_01 : G.str.1.Adj v0 v1 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
      have G_02 : G.str.1.Adj v0 v2 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
      have G_13 : G.str.1.Adj v1 v3 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm]
        rw [hadj₁]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
      have G_23 : G.str.1.Adj v2 v3 := by
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
      have G_14 : G.str.1.Adj v1 v4 := by
        rw [show v1 = e₂.toFun ⟨1, by decide⟩ from he₂_1.symm]
        rw [hadj₂]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
      have G_24 : G.str.1.Adj v2 v4 := by
        rw [show v2 = e₂.toFun ⟨2, by decide⟩ from he₂_2.symm]
        rw [hadj₂]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
      have G_n12 : ¬G.str.1.Adj v1 v2 := by
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm,
            show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm]
        rw [hadj₁]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
      have G_n03 : ¬G.str.1.Adj v0 v3 := by
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm]
        rw [hadj₁]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
      have G_n04 : ¬G.str.1.Adj v0 v4 := by
        rw [show v0 = e₂.toFun ⟨0, by decide⟩ from he₂_0.symm]
        rw [hadj₂]; simp [cs0Flag6, SimpleGraph.fromRel_adj]
      have G_n34 : ¬G.str.1.Adj v3 v4 := hno_adj_free
      ext u w; simp only [SimpleGraph.comap_adj]
      rcases hcover u with rfl | rfl | rfl | rfl | rfl <;>
        rcases hcover w with rfl | rfl | rfl | rfl | rfl <;> (
        change (SimpleGraph.fromRel _).Adj (φ _) (φ _) ↔ _
        first
        | rw [hfwd_v0, hfwd_v1] | rw [hfwd_v0, hfwd_v2] | rw [hfwd_v0, hfwd_v3] | rw [hfwd_v0, hfwd_v4] | rw [hfwd_v0]
        | rw [hfwd_v1, hfwd_v0] | rw [hfwd_v1, hfwd_v2] | rw [hfwd_v1, hfwd_v3] | rw [hfwd_v1, hfwd_v4] | rw [hfwd_v1]
        | rw [hfwd_v2, hfwd_v0] | rw [hfwd_v2, hfwd_v1] | rw [hfwd_v2, hfwd_v3] | rw [hfwd_v2, hfwd_v4] | rw [hfwd_v2]
        | rw [hfwd_v3, hfwd_v0] | rw [hfwd_v3, hfwd_v1] | rw [hfwd_v3, hfwd_v2] | rw [hfwd_v3, hfwd_v4] | rw [hfwd_v3]
        | rw [hfwd_v4, hfwd_v0] | rw [hfwd_v4, hfwd_v1] | rw [hfwd_v4, hfwd_v2] | rw [hfwd_v4, hfwd_v3] | rw [hfwd_v4]
        ) <;>
      all_goals (
        constructor <;> intro h
        · first
          | exact G_01 | exact G_01.symm
          | exact G_02 | exact G_02.symm
          | exact G_13 | exact G_13.symm
          | exact G_23 | exact G_23.symm
          | exact G_14 | exact G_14.symm
          | exact G_24 | exact G_24.symm
          | (exfalso; revert h; simp [SimpleGraph.fromRel_adj]; try omega)
        · first
          | exact absurd h G_n12 | exact absurd h (fun x => G_n12 x.symm)
          | exact absurd h G_n03 | exact absurd h (fun x => G_n03 x.symm)
          | exact absurd h G_n04 | exact absurd h (fun x => G_n04 x.symm)
          | exact absurd h G_n34 | exact absurd h (fun x => G_n34 x.symm)
          | exact absurd h (fun x => x.ne rfl)
          | (rw [SimpleGraph.fromRel_adj]; refine ⟨by decide, ?_⟩; omega))
    · change S0F66_witness.str.2 ∘ (⇑φ) = G.str.2
      funext u; change S0F66_witness.str.2 (φ u) = G.str.2 u
      rcases hcover u with rfl | rfl | rfl | rfl | rfl
      · rw [hfwd_v0]; simp only [S0F66_witness]
        rw [show v0 = e₁.toFun ⟨0, by decide⟩ from he₁_0.symm, hcol₁]; simp [cs0Flag6]
      · rw [hfwd_v1]; simp only [S0F66_witness]
        rw [show v1 = e₁.toFun ⟨1, by decide⟩ from he₁_1.symm, hcol₁]; simp [cs0Flag6]
      · rw [hfwd_v2]; simp only [S0F66_witness]
        rw [show v2 = e₁.toFun ⟨2, by decide⟩ from he₁_2.symm, hcol₁]; simp [cs0Flag6]
      · rw [hfwd_v3]; simp only [S0F66_witness]
        rw [hcol₁]; simp [cs0Flag6]
      · rw [hfwd_v4]; simp only [S0F66_witness]
        rw [hcol₂]; simp [cs0Flag6]
  · intro i; fin_cases i <;>
      simp only [S0F66_witness, Function.Embedding.coeFn_mk, Fin.castLE] <;>
      first
      | (change φ v0 = _; rw [hφ_emb ⟨0, by decide⟩]; rfl)
      | (change φ v1 = _; rw [hφ_emb ⟨1, by decide⟩]; rfl)
      | (change φ v2 = _; rw [hφ_emb ⟨2, by decide⟩]; rfl)

set_option maxHeartbeats 800000 in
theorem avgProd6_S0F66
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (avgProd6 cs0Flag6 cs0Flag6) = (1/10 : ℝ) * phi.eval cs0_flag_S0F66 := by 
   apply avgProd6_eval_single_witness phi cs0Flag6 cs0Flag6 S0F66_witness cs0_flag_S0F66 (1/10) (by decide)
   · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
     exact ⟨⟨S0F66_witness.str, S0F66_witness.embedding, S0F66_witness.isInduced⟩, rfl⟩
   · have haut : (genFlagAutCount CG2 csType6 cs0Flag6 : ℝ) = 1 := by
       rw [genFlagAutCount_cs0Flag6]; norm_num
     rw [haut, one_mul, inv_one, one_mul, ← mul_assoc, S0F66_witness_jid_nf]
     congr 1
   · exact fun cls hne => avgProd_other_classes_zero_of_classification phi csType6 cs0Flag6 cs0Flag6
       S0F66_witness cls hne S0F66_unique_class_of_jc_pos_tri_free

/-! ### f² and g² evaluation identities -/

/-- Full f² evaluation identity:
    120·eval(⟦f²⟧₆) = eval(S0F33) - (1/2)(eval(S0F34F)+eval(S0F34T))
      - (1/2)(eval(S0F35F)+eval(S0F35T)) - (eval(S0F36F)+eval(S0F36T))
      + (1/16)eval(S0F44) + (1/8)(eval(S0F45F)+eval(S0F45T))
      + (1/4)eval(S0F46) + (1/16)eval(S0F55) + (1/4)eval(S0F56)
      + (1/4)eval(S0F66) -/
theorem fsq_eval_identity
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    120 * phi.evalAlg (genAveragingAlg csType6 (cs0_f.mul cs0_f)) =
      4 * phi.eval cs0_flag_S0F33
      - (1/2) * phi.eval cs0_flag_S0F34F - (1/2) * phi.eval cs0_flag_S0F34T
      - (1/2) * phi.eval cs0_flag_S0F35F - (1/2) * phi.eval cs0_flag_S0F35T
      - 2 * phi.eval cs0_flag_S0F36F - 4 * phi.eval cs0_flag_S0F36T
      + (1/8) * phi.eval cs0_flag_S0F44
      + (1/4) * phi.eval cs0_flag_S0F45F + (1/4) * phi.eval cs0_flag_S0F45T
      + (1/2) * phi.eval cs0_flag_S0F46
      + (1/8) * phi.eval cs0_flag_S0F55
      + (1/2) * phi.eval cs0_flag_S0F56
      + 3 * phi.eval cs0_flag_S0F66 := by
  rw [fsq_eval_distribute]
  rw [avgProd6_S0F33 phi, avgProd6_S0F34 phi, avgProd6_S0F35 phi, avgProd6_S0F36 phi,
      avgProd6_S0F44 phi, avgProd6_S0F45 phi, avgProd6_S0F46 phi,
      avgProd6_S0F55 phi, avgProd6_S0F56 phi, avgProd6_S0F66 phi]
  ring

/-- Full g² evaluation identity:
    120·eval(⟦g²⟧₆) = (1/16)eval(S0F44)
      - (1/8)(eval(S0F45F)+eval(S0F45T))
      + (1/16)eval(S0F55) -/
theorem gsq_eval_identity
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta) :
    120 * phi.evalAlg (genAveragingAlg csType6 (cs0_g.mul cs0_g)) =
      (1/8) * phi.eval cs0_flag_S0F44
      - (1/4) * phi.eval cs0_flag_S0F45F - (1/4) * phi.eval cs0_flag_S0F45T
      + (1/8) * phi.eval cs0_flag_S0F55 := by
  rw [gsq_eval_distribute, avgProd6_S0F44 phi, avgProd6_S0F45 phi, avgProd6_S0F55 phi]
  ring

/-! ## Sigma component helpers for linSum decomposition

The linSum decomposes as `6·B₁ + σ₁ + (1/4)·σ₂ + σ₃ + σ₄ + 2·σ₅`
(BrrbCertificate.lean, verified by `native_decide`). Each component
evaluates nonneg by extension ordering + regularity.

These helper theorems state each component's nonnegativity in the
`phi.eval` convention (unlabelled density in the local flag algebra).

Convention: p-density `p(F) = aut(F)/120 · phi.eval(F)`. The cert
vectors give coefficients in p-density; multiplying by `aut(F)` converts
to `phi.eval` coefficients. -/

attribute [local instance] Classical.propDecidable

/-! ### B₁ nonnegativity discharge (Phases 1–3)

`B₁ = 5·p(F₁) - p(F₆)`, i.e. `600·eval(certF1) - 24·eval(certF6) ≥ 0`.

Closed via density identification:
* Phase 1 (Extensions.lean): IC formulas for certF1, certF6 on a `ColouredGraphClass`.
* Phase 2 (here): build CGC from `phi.seq.seq k`, identify per-graph densities.
* Phase 3 (here): lift via `phi.convergence` to `phi.eval certF1 = 1`,
  `phi.eval certF6 = 5`.

Given the hypotheses (regularity, |black| = Δ), we build a `ColouredGraphClass`
from each `phi.seq.seq k`, apply the IC formulas (Phase 1), compute densities
exactly, and lift to `phi.eval certF1 = 1`, `phi.eval certF6 = 5` via
convergence. The bound `0 ≤ 600·1 - 24·5 = 480` is then immediate. -/

/-- Construct a `ColouredGraphClass` from `phi.seq.seq k` using the regularity,
    black-count = Δ, and `phi.seq_in_class` hypotheses. The resulting CGC has
    `toGenFlag.forget` propositionally equal to `(phi.seq.seq k).forget`. -/
private noncomputable def phiSeqAsCGC
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget)
    (hblack : ∀ k, (Finset.univ.filter
      (fun v : Fin (phi.seq.seq k).size => (phi.seq.seq k).str.2 v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget)
    (k : ℕ) : ColouredGraphClass where
  graph := {
    size := (phi.seq.seq k).size
    graph := (phi.seq.seq k).str.1
    embedding := ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
    hsize := Nat.zero_le _ }
  colouring := (phi.seq.seq k).str.2
  triangleFree := by
    intro u v w
    have h := phi.seq_in_class k
    -- h.1 is triangleFree
    intro huv hvw huw
    exact h.1 u v w huv hvw huw
  regular := by
    intro v
    -- (phi.seq.seq k).forget.size = (phi.seq.seq k).size and str.1 unchanged
    have h := hreg k v
    -- Goal: deg(v) = maxDegree of the graph
    -- maxDegree is sup over all v's of degree
    -- brrbGenDelta = sup, so they match
    rw [h]
    change brrbGenDelta (phi.seq.seq k).forget = _
    -- maxDegree of `Flag emptyType` with size and graph defined here
    change Finset.sup Finset.univ
        (fun u => (Finset.univ.filter ((phi.seq.seq k).forget.str.1.Adj u)).card) =
      Finset.sup Finset.univ
        (fun u => (Finset.univ.filter (fun w => (phi.seq.seq k).str.1.Adj u w)).card)
    rfl
  blackCount := by
    have h := hblack k
    rw [h]
    change brrbGenDelta (phi.seq.seq k).forget = _
    rfl
  blackIndependent := by
    intro u v hu hv hadj
    exact (phi.seq_in_class k).2.1 u v hu hv hadj

/-- The `toGenFlag` of `phiSeqAsCGC` equals `phi.seq.seq k` (modulo `GenFlag.empty_ext`). -/
private theorem phiSeqAsCGC_toGenFlag_forget
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget)
    (hblack : ∀ k, (Finset.univ.filter
      (fun v : Fin (phi.seq.seq k).size => (phi.seq.seq k).str.2 v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget)
    (k : ℕ) :
    (phiSeqAsCGC phi hreg hblack k).toGenFlag.forget = (phi.seq.seq k).forget :=
  GenFlag.empty_ext _ _ rfl rfl

/-- IC(certF1, phi.seq.seq k) = (Δ_k)_5, where Δ_k = brrbGenDelta (phi.seq.seq k).forget. -/
private theorem phi_IC_certF1
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget)
    (hblack : ∀ k, (Finset.univ.filter
      (fun v : Fin (phi.seq.seq k).size => (phi.seq.seq k).str.2 v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget)
    (k : ℕ) :
    genInducedCount CG2 (GenFlagType.empty CG2) certF1 (phi.seq.seq k) =
      Nat.descFactorial (brrbGenDelta (phi.seq.seq k).forget) 5 := by
  have h := IC_certF1_eq_descFactorial (phiSeqAsCGC phi hreg hblack k)
  -- h : IC certF1 (phiSeqAsCGC phi hreg hblack k).toGenFlag.forget = (Δ)_5
  rw [phiSeqAsCGC_toGenFlag_forget phi hreg hblack k] at h
  -- maxDegree of (phiSeqAsCGC ...).graph = brrbGenDelta (phi.seq.seq k).forget
  have hmax : maxDegree (phiSeqAsCGC phi hreg hblack k).graph =
      brrbGenDelta (phi.seq.seq k).forget := by
    change Finset.sup Finset.univ
        (fun v => (Finset.univ.filter (fun u => (phi.seq.seq k).str.1.Adj v u)).card) =
      Finset.sup Finset.univ
        (fun u => (Finset.univ.filter ((phi.seq.seq k).forget.str.1.Adj u)).card)
    rfl
  rw [hmax] at h
  -- h : IC certF1 (phi.seq.seq k).forget = (Δ)_5
  -- Goal uses (phi.seq.seq k), but .forget for empty type is the same flag.
  have heq : (phi.seq.seq k).forget = phi.seq.seq k :=
    GenFlag.empty_ext _ _ rfl rfl
  rwa [← heq]

/-- IC(certF6, phi.seq.seq k) = Δ_k · (Δ_k)_4, where Δ_k = brrbGenDelta. -/
private theorem phi_IC_certF6
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget)
    (hblack : ∀ k, (Finset.univ.filter
      (fun v : Fin (phi.seq.seq k).size => (phi.seq.seq k).str.2 v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget)
    (k : ℕ) :
    genInducedCount CG2 (GenFlagType.empty CG2) certF6 (phi.seq.seq k) =
      brrbGenDelta (phi.seq.seq k).forget *
        Nat.descFactorial (brrbGenDelta (phi.seq.seq k).forget) 4 := by
  have h := IC_certF6_eq_blackCount_mul_descFactorial
    (phiSeqAsCGC phi hreg hblack k)
  rw [phiSeqAsCGC_toGenFlag_forget phi hreg hblack k] at h
  -- (phiSeqAsCGC ...).blackCount in the structure is the proof; we need numerical
  -- equality at the formula level.
  have hbc : (Finset.univ.filter
      (fun v : Fin (phiSeqAsCGC phi hreg hblack k).graph.size =>
        (phiSeqAsCGC phi hreg hblack k).colouring v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget := hblack k
  have hmax : maxDegree (phiSeqAsCGC phi hreg hblack k).graph =
      brrbGenDelta (phi.seq.seq k).forget := by
    change Finset.sup Finset.univ
        (fun v => (Finset.univ.filter (fun u => (phi.seq.seq k).str.1.Adj v u)).card) =
      Finset.sup Finset.univ
        (fun u => (Finset.univ.filter ((phi.seq.seq k).forget.str.1.Adj u)).card)
    rfl
  rw [hbc, hmax] at h
  have heq : (phi.seq.seq k).forget = phi.seq.seq k :=
    GenFlag.empty_ext _ _ rfl rfl
  rwa [← heq]

/-! ### Density evaluation -/

/-- For Δ ≥ 5: `(Δ)_5 / (C(Δ, 5) · 120) = 1`. The descFactorial / choose ratio
    cleanly equals 5! = 120, cancelling. -/
private theorem density_certF1_eq_one
    (Δ : ℕ) (hΔ : 5 ≤ Δ) :
    (Nat.descFactorial Δ 5 : ℝ) / ((Nat.choose Δ 5 : ℝ) * 120) = 1 := by
  have h_desc : Nat.descFactorial Δ 5 = Nat.choose Δ 5 * 120 := by
    -- (Δ)_5 = C(Δ, 5) · 5! = C(Δ, 5) · 120
    rw [show (120 : ℕ) = Nat.factorial 5 from by decide]
    exact (Nat.descFactorial_eq_factorial_mul_choose Δ 5).trans (by ring_nf)
  have hC_pos : 0 < Nat.choose Δ 5 := Nat.choose_pos hΔ
  have hC_R : (Nat.choose Δ 5 : ℝ) > 0 := by exact_mod_cast hC_pos
  field_simp
  exact_mod_cast h_desc

/-- For Δ ≥ 5: `Δ · (Δ)_4 / (C(Δ, 5) · 24) = 5Δ / (Δ - 4)`. -/
private theorem density_certF6_formula
    (Δ : ℕ) (hΔ : 5 ≤ Δ) :
    ((Δ * Nat.descFactorial Δ 4 : ℕ) : ℝ) / ((Nat.choose Δ 5 : ℝ) * 24) =
      5 * (Δ : ℝ) / ((Δ : ℝ) - 4) := by
  -- Δ · (Δ)_4 = Δ · 4! · C(Δ, 4) = 24 · Δ · C(Δ, 4)
  -- (Δ)_5 = 5! · C(Δ, 5) = 120 · C(Δ, 5) = (Δ - 4) · (Δ)_4 = (Δ - 4) · 24 · C(Δ, 4)
  -- So C(Δ, 5) = (Δ - 4) · C(Δ, 4) / 5
  have h_desc4 : Nat.descFactorial Δ 4 = Nat.choose Δ 4 * 24 := by
    rw [show (24 : ℕ) = Nat.factorial 4 from by decide]
    exact (Nat.descFactorial_eq_factorial_mul_choose Δ 4).trans (by ring_nf)
  have hC4_pos : 0 < Nat.choose Δ 4 := Nat.choose_pos (by omega)
  have hC5_pos : 0 < Nat.choose Δ 5 := Nat.choose_pos hΔ
  -- Use C(Δ, 5) = C(Δ, 4) · (Δ - 4) / 5 in the form 5·C(Δ, 5) = C(Δ, 4) · (Δ - 4).
  have hChoose : Nat.choose Δ 5 * 5 = Nat.choose Δ 4 * (Δ - 4) := by
    -- C(n, k+1) = C(n, k) * (n - k) / (k + 1), i.e., (k+1) * C(n, k+1) = C(n, k) * (n - k)
    have : Nat.choose Δ 5 * (5) = Nat.choose Δ 4 * (Δ - 4) := by
      have hkk : 5 = 4 + 1 := rfl
      rw [hkk, Nat.choose_succ_right_eq]
    exact this
  have hChooseR : ((Nat.choose Δ 5 : ℕ) : ℝ) * 5 =
      ((Nat.choose Δ 4 : ℕ) : ℝ) * ((Δ : ℝ) - 4) := by
    have h_subt : 4 ≤ Δ := by omega
    have h_cast_sub : ((Δ - 4 : ℕ) : ℝ) = (Δ : ℝ) - 4 := by
      rw [Nat.cast_sub h_subt]; norm_num
    have h1 : ((Nat.choose Δ 5 : ℕ) : ℝ) * 5 =
        ((Nat.choose Δ 4 : ℕ) : ℝ) * ((Δ - 4 : ℕ) : ℝ) := by
      have := hChoose
      exact_mod_cast this
    rw [h1, h_cast_sub]
  have hC5_R : (Nat.choose Δ 5 : ℝ) > 0 := by exact_mod_cast hC5_pos
  have hC4_R : (Nat.choose Δ 4 : ℝ) > 0 := by exact_mod_cast hC4_pos
  have hΔ_minus4_pos : (0 : ℝ) < (Δ : ℝ) - 4 := by
    have : (4 : ℝ) < (Δ : ℝ) := by exact_mod_cast (show 4 < Δ from by omega)
    linarith
  -- Now compute LHS
  push_cast
  rw [h_desc4]
  push_cast
  -- LHS: (Δ * (C 4 * 24)) / (C 5 * 24) = Δ * C 4 / C 5
  -- = Δ * C 4 / C 5
  -- By hChooseR: C 5 = C 4 * (Δ - 4) / 5, so C 4 / C 5 = 5 / (Δ - 4)
  -- → LHS = 5Δ / (Δ - 4) ✓
  field_simp
  linarith [hChooseR]

/-! ### Tendsto of densities -/

/-- For all k with `Δ_k ≥ 5`, `genUnlabelledDensity certF1 (phi.seq.seq k) brrbGenDelta = 1`. -/
private theorem density_certF1_phi_eq_one
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget)
    (hblack : ∀ k, (Finset.univ.filter
      (fun v : Fin (phi.seq.seq k).size => (phi.seq.seq k).str.2 v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget)
    (k : ℕ) (hΔ : 5 ≤ brrbGenDelta (phi.seq.seq k).forget) :
    genUnlabelledDensity CG2 (GenFlagType.empty CG2) certF1
      (phi.seq.seq k) brrbGenDelta = 1 := by
  unfold genUnlabelledDensity
  rw [phi_IC_certF1 phi hreg hblack k, certF1_aut]
  have hsz : certF1.size - (GenFlagType.empty CG2).size = 5 := rfl
  rw [hsz]
  exact density_certF1_eq_one _ hΔ

/-- For all k with `Δ_k ≥ 5`, the density of certF6 equals 5·Δ/(Δ-4). -/
private theorem density_certF6_phi_eq
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget)
    (hblack : ∀ k, (Finset.univ.filter
      (fun v : Fin (phi.seq.seq k).size => (phi.seq.seq k).str.2 v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget)
    (k : ℕ) (hΔ : 5 ≤ brrbGenDelta (phi.seq.seq k).forget) :
    genUnlabelledDensity CG2 (GenFlagType.empty CG2) certF6
      (phi.seq.seq k) brrbGenDelta =
        5 * (brrbGenDelta (phi.seq.seq k).forget : ℝ) /
          ((brrbGenDelta (phi.seq.seq k).forget : ℝ) - 4) := by
  unfold genUnlabelledDensity
  rw [phi_IC_certF6 phi hreg hblack k, certF6_aut]
  have hsz : certF6.size - (GenFlagType.empty CG2).size = 5 := rfl
  rw [hsz]
  exact density_certF6_formula _ hΔ

/-! ### Limit identification -/

/-- `phi.eval certF1 = 1`. -/
theorem phi_eval_certF1_eq_one
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget)
    (hblack : ∀ k, (Finset.univ.filter
      (fun v : Fin (phi.seq.seq k).size => (phi.seq.seq k).str.2 v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget) :
    phi.eval certF1 = 1 := by
  -- Δ_k → ∞ along the convergent subsequence
  have h_Δ_to_inf : Filter.Tendsto
      (fun k => brrbGenDelta (phi.seq.seq (phi.sub k)).forget)
      Filter.atTop Filter.atTop :=
    (phi.seq.increasing.comp phi.sub_strictMono).tendsto_atTop
  -- Convergence: density tendsto phi.eval certF1
  have h_local : GenIsLocalFlag (GenFlagType.empty CG2) certF1
      brrbGenGraphClass brrbGenDelta := certF1_isLocalFlag
  have h_conv := phi.convergence certF1 h_local
  -- For all k large enough, Δ_(sub k) ≥ 5 → density = 1.
  apply tendsto_nhds_unique h_conv
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [h_Δ_to_inf.eventually_ge_atTop 5] with k hk
  exact (density_certF1_phi_eq_one phi hreg hblack (phi.sub k) hk).symm

/-- `phi.eval certF6 = 5`. -/
theorem phi_eval_certF6_eq_five
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget)
    (hblack : ∀ k, (Finset.univ.filter
      (fun v : Fin (phi.seq.seq k).size => (phi.seq.seq k).str.2 v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget) :
    phi.eval certF6 = 5 := by
  have h_Δ_to_inf : Filter.Tendsto
      (fun k => brrbGenDelta (phi.seq.seq (phi.sub k)).forget)
      Filter.atTop Filter.atTop :=
    (phi.seq.increasing.comp phi.sub_strictMono).tendsto_atTop
  -- For real-valued tendsto, lift Δ → ∞ in ℕ to (Δ : ℝ) → ∞ in ℝ.
  have h_Δ_R_to_inf : Filter.Tendsto
      (fun k => (brrbGenDelta (phi.seq.seq (phi.sub k)).forget : ℝ))
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.mpr ?_
    intro M
    obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp h_Δ_to_inf (Nat.ceil M)
    refine ⟨N, ?_⟩
    intro k hk
    have := hN k hk
    have : (Nat.ceil M : ℝ) ≤ ((brrbGenDelta (phi.seq.seq (phi.sub k)).forget : ℕ) : ℝ) := by
      exact_mod_cast this
    have hM_le : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
    linarith
  -- The density 5Δ/(Δ - 4) tendsto 5 as Δ → ∞.
  have h_density_tendsto : Filter.Tendsto
      (fun k => 5 * (brrbGenDelta (phi.seq.seq (phi.sub k)).forget : ℝ) /
        ((brrbGenDelta (phi.seq.seq (phi.sub k)).forget : ℝ) - 4))
      Filter.atTop (nhds 5) := by
    -- 5Δ/(Δ - 4) = 5 / (1 - 4/Δ); as Δ → ∞, 4/Δ → 0, so ratio → 5.
    have h_inv_tendsto : Filter.Tendsto
        (fun k : ℕ => (4 : ℝ) /
          (brrbGenDelta (phi.seq.seq (phi.sub k)).forget : ℝ))
        Filter.atTop (nhds 0) := by
      have := h_Δ_R_to_inf
      exact (this.const_div_atTop 4)
    -- 1 - 4/Δ → 1
    have h_sub : Filter.Tendsto
        (fun k => 1 - (4 : ℝ) /
          (brrbGenDelta (phi.seq.seq (phi.sub k)).forget : ℝ))
        Filter.atTop (nhds 1) := by
      have := h_inv_tendsto.const_sub 1
      simpa using this
    -- 5 / (1 - 4/Δ) → 5
    have h_div : Filter.Tendsto
        (fun k => (5 : ℝ) / (1 - (4 : ℝ) /
          (brrbGenDelta (phi.seq.seq (phi.sub k)).forget : ℝ)))
        Filter.atTop (nhds (5 / 1 : ℝ)) :=
      tendsto_const_nhds.div h_sub (by norm_num)
    simp only [div_one] at h_div
    -- Show pointwise eventually equal: 5Δ/(Δ-4) = 5 / (1 - 4/Δ) for Δ > 4.
    apply h_div.congr'
    filter_upwards [h_Δ_to_inf.eventually_ge_atTop 5] with k hk
    have hΔ_R : (5 : ℝ) ≤ (brrbGenDelta (phi.seq.seq (phi.sub k)).forget : ℝ) := by
      exact_mod_cast hk
    have hΔ_pos : (0 : ℝ) < (brrbGenDelta (phi.seq.seq (phi.sub k)).forget : ℝ) := by
      linarith
    have hΔ_minus4_pos : (0 : ℝ) <
        (brrbGenDelta (phi.seq.seq (phi.sub k)).forget : ℝ) - 4 := by linarith
    field_simp
  have h_local : GenIsLocalFlag (GenFlagType.empty CG2) certF6
      brrbGenGraphClass brrbGenDelta := certF6_isLocalFlag
  have h_conv := phi.convergence certF6 h_local
  apply tendsto_nhds_unique h_conv
  apply h_density_tendsto.congr'
  filter_upwards [h_Δ_to_inf.eventually_ge_atTop 5] with k hk
  exact (density_certF6_phi_eq phi hreg hblack (phi.sub k) hk).symm

theorem b1_nonneg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget)
    (hblack : ∀ k, (Finset.univ.filter
      (fun v : Fin (phi.seq.seq k).size => (phi.seq.seq k).str.2 v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget) :
    0 ≤ 5 * phi.eval certF1 - phi.eval certF6 := by
  rw [phi_eval_certF1_eq_one phi hreg hblack,
      phi_eval_certF6_eq_five phi hreg hblack]
  norm_num


/-! ## σ₁ nonnegativity plan (thesis §3.6, Lemma 3.10 case σ₁)

    **STATUS: CLOSED** (commit `11a08cb`, 2026-05-08). All 5 σ-cone bounds
    (σ₁..σ₅) for `pentagon_bound_simple` are now proved with 0 user axioms.
    See the development notes for the recipe (template
    transferred to σ₂..σ₅).

    The extension ordering at `thesisType1` evaluates nonneg.

    Cert: `BrrbCertificate.sig1x2 = 120·⟦ext_a^σ₁ - ext_b^σ₁⟧` in p-density
    `[-4F₄, -6F₅, 2F₁₂, 2F₂₄, 4F₃₂]` (= sig1x2 / 2).
    Goal RHS in p-density convention (matches σ-cone closure formula
    `120·evalAlg(genAveragingAlg σ (extSum a − extSum b)) = goal RHS`).

    ## Reduction via `Extensions.sigma_nonneg_template`

    σ = `thesisType1` (K_{1,3} at v0=R, edges 0-1, 0-2, 0-3, colours [R,B,R,R]).

    σ-aut group: stabiliser of v0=R, fixing v1=B (lone B leaf), permuting
    {v2, v3} (R leaves). 3 orbits: {v0}, {v1}, {v2, v3}.

    Cert pair (per `Degree::regularity` in `local-flags-certificates/src/degree.rs`,
    cyclic over orbit list): orbit list iteration-order = [v0, v1, v2].
    Docstring `ext₂ - ext₁` (1-indexed orbit positions) → likely Lean
    pair (a, b) = (⟨1, _⟩, ⟨0, _⟩) — v1=B leaf vs v0=R centre. Different
    orbits, genuine deg-gap (v1 deg 1, v0 deg 3 in σ).

    NOTE: The exact Lean Fin indices for (a, b) will be confirmed during
    Phase 5 enumeration (the named-flag combo determines the pair uniquely).

    ## Phase 2 output (DONE, used by Phase 5)

    - `thesisType1_isLocalType` (PentagonConjecture.lean): σ-locality.

    ## Phase 3 output (DONE, but pair may not match cert)

    - `thesisType1_ext_ordering` proved `ext(v1) + 0 ≤ ext(v2)` (Lean indices),
      i.e., between two leaves. NOT used directly by σᵢ_nonneg, since the
      proof uses `unlabel_extDiff_eq_zero` (saturation at the limit, σ-cone
      closure) rather than a per-embedding ineq. Phase 3 retained as
      sanity-check / documentation.

    ## Phase 5 progress (σ₁-4-E)

    DONE (Extensions.lean infrastructure ready for assembly):
    - **σ-side**: `sigma1_extSum_diff_psi_eq_zero` proves
      `ψ.evalAlg(extSum_v1 - extSum_v0) = 0` at any regular σ-functional ψ
      (via `extSum_eval_one`). Discharges hypothesis #2 of
      `sigma_nonneg_template_perfunc_weakened`.
    - **Locality**: `genIsLocalFlag_extAdj_BRRB` provides BRRB σ-locality
      for any size-(σ.size+1) σ-flag with extAdjacency. Discharges
      hypothesis #1 (locality side of disjunction).
    - **Witnesses**: 6 size-5 thesisType1-flags `t1_v1_a/b/c/d`, `t1_v0_R/B`
      with `forget` isos to the 5 named flags (certF4, flag5, flag12,
      flag24, flag32) via explicit Fin 5 ≃ Fin 5 permutations.
    - **Classifications** (Extensions.lean): 6 theorems
      `t1_v*_classification` (now `theorem` not `private`) prove that
      any size-5 thesisType1-flag G with extAdj-vᵢ + BRRB constraints
      (no BB-edge, no triangle) is σ-iso to one of the 6 witnesses,
      based on case-split of (w-v2, w-v3) ∈ {T,F}² for v1-side and
      (w colour ∈ {R, B}) for v0-side.
    - **Dichotomies** (Extensions.lean): `t1_extAdj_v1_dichotomy` and
      `t1_extAdj_v0_dichotomy` prove that every cls in the extAdj filter
      either is iso to a t1_v* witness OR `phi.eval cls.out.forget = 0`.
      The eval-zero branch uses `eval_zero_of_adj_black` (for BB-edge)
      or `eval_zero_of_triangle` (for triangle), avoiding the heavier
      `IsForbidden` infrastructure.

    ## Phase 5 remaining work (master identity assembly, ~250-400 LOC)

    The final assembly requires: `Finset.sum`-level cancellation of
    non-witness contributions via the dichotomies + iso-invariance of
    `phi.eval`, `genFlagAutCount`, `genNormalisationFactor`. With
    `aut(t1_v1_a.forget) = 2`, `aut(t1_v1_b/c.forget) = 1`,
    `aut(t1_v1_d.forget) = 4`, `aut(t1_v0_R.forget) = 6`,
    `aut(t1_v0_B.forget) = 4`, this gives:

      `120 · phi.evalAlg(genAveragingAlg σ (extSum_v1 - extSum_v0)) =
        2·phi.eval(flag24) + phi.eval(flag12) + phi.eval(flag12) +
        4·phi.eval(flag32) - 6·phi.eval(flag5) - 4·phi.eval(certF4)`

    matching the goal RHS (with sign convention: ext_a = ext_v1, ext_b = ext_v0
    but goal sign is flipped — note positive flag24/flag12/flag32 vs
    negative certF4/flag5).

    Once master identity proven, sigma1_nonneg closes via
    `sigma_nonneg_template_perfunc_weakened` with all hypotheses in place.
    See `sigma1_witness_contribution_*` lemmas above and Extensions.lean
    dichotomy theorems. -/

set_option maxHeartbeats 4000000 in
private theorem sigma1_witness_contribution_v1_a
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType1 ⟨1, by decide⟩) (GenFlagClass.mk t1_v1_a)) *
      (genNormalisationFactor thesisType1 (GenFlagClass.mk t1_v1_a).out *
        phi.eval (GenFlagClass.mk t1_v1_a).out.forget) =
      2 / 120 * phi.eval flag24 := by
  have h_iso : GenFlagIso thesisType1 (GenFlagClass.mk t1_v1_a).out t1_v1_a :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t1_v1_a))
  have h_adj : extAdjacencyClass thesisType1 (GenFlagClass.mk t1_v1_a) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t1_v1_a_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType1 ⟨1, by decide⟩) (GenFlagClass.mk t1_v1_a) =
      (genFlagAutCount CG2 thesisType1 (GenFlagClass.mk t1_v1_a).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t1_v1_a.str, t1_v1_a.embedding, t1_v1_a.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t1_v1_a).out.forget t1_v1_a.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t1_v1_a_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t1_v1_a_sigmaAutCount,
      genFlagAutCount_flagIso t1_v1_a_forget_iso, flag24_aut]
  have h_df : (Nat.descFactorial t1_v1_a.size thesisType1.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma1_witness_contribution_v1_b
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType1 ⟨1, by decide⟩) (GenFlagClass.mk t1_v1_b)) *
      (genNormalisationFactor thesisType1 (GenFlagClass.mk t1_v1_b).out *
        phi.eval (GenFlagClass.mk t1_v1_b).out.forget) =
      1 / 120 * phi.eval flag12 := by
  have h_iso : GenFlagIso thesisType1 (GenFlagClass.mk t1_v1_b).out t1_v1_b :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t1_v1_b))
  have h_adj : extAdjacencyClass thesisType1 (GenFlagClass.mk t1_v1_b) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t1_v1_b_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType1 ⟨1, by decide⟩) (GenFlagClass.mk t1_v1_b) =
      (genFlagAutCount CG2 thesisType1 (GenFlagClass.mk t1_v1_b).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t1_v1_b.str, t1_v1_b.embedding, t1_v1_b.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t1_v1_b).out.forget t1_v1_b.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t1_v1_b_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t1_v1_b_sigmaAutCount,
      genFlagAutCount_flagIso t1_v1_b_forget_iso, flag12_aut]
  have h_df : (Nat.descFactorial t1_v1_b.size thesisType1.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma1_witness_contribution_v1_c
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType1 ⟨1, by decide⟩) (GenFlagClass.mk t1_v1_c)) *
      (genNormalisationFactor thesisType1 (GenFlagClass.mk t1_v1_c).out *
        phi.eval (GenFlagClass.mk t1_v1_c).out.forget) =
      1 / 120 * phi.eval flag12 := by
  have h_iso : GenFlagIso thesisType1 (GenFlagClass.mk t1_v1_c).out t1_v1_c :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t1_v1_c))
  have h_adj : extAdjacencyClass thesisType1 (GenFlagClass.mk t1_v1_c) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t1_v1_c_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType1 ⟨1, by decide⟩) (GenFlagClass.mk t1_v1_c) =
      (genFlagAutCount CG2 thesisType1 (GenFlagClass.mk t1_v1_c).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t1_v1_c.str, t1_v1_c.embedding, t1_v1_c.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t1_v1_c).out.forget t1_v1_c.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t1_v1_c_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t1_v1_c_sigmaAutCount,
      genFlagAutCount_flagIso t1_v1_c_forget_iso, flag12_aut]
  have h_df : (Nat.descFactorial t1_v1_c.size thesisType1.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma1_witness_contribution_v1_d
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType1 ⟨1, by decide⟩) (GenFlagClass.mk t1_v1_d)) *
      (genNormalisationFactor thesisType1 (GenFlagClass.mk t1_v1_d).out *
        phi.eval (GenFlagClass.mk t1_v1_d).out.forget) =
      4 / 120 * phi.eval flag32 := by
  have h_iso : GenFlagIso thesisType1 (GenFlagClass.mk t1_v1_d).out t1_v1_d :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t1_v1_d))
  have h_adj : extAdjacencyClass thesisType1 (GenFlagClass.mk t1_v1_d) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t1_v1_d_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType1 ⟨1, by decide⟩) (GenFlagClass.mk t1_v1_d) =
      (genFlagAutCount CG2 thesisType1 (GenFlagClass.mk t1_v1_d).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t1_v1_d.str, t1_v1_d.embedding, t1_v1_d.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t1_v1_d).out.forget t1_v1_d.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t1_v1_d_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t1_v1_d_sigmaAutCount,
      genFlagAutCount_flagIso t1_v1_d_forget_iso, flag32_aut]
  have h_df : (Nat.descFactorial t1_v1_d.size thesisType1.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma1_witness_contribution_v0_R
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType1 ⟨0, by decide⟩) (GenFlagClass.mk t1_v0_R)) *
      (genNormalisationFactor thesisType1 (GenFlagClass.mk t1_v0_R).out *
        phi.eval (GenFlagClass.mk t1_v0_R).out.forget) =
      6 / 120 * phi.eval flag5 := by
  have h_iso : GenFlagIso thesisType1 (GenFlagClass.mk t1_v0_R).out t1_v0_R :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t1_v0_R))
  have h_adj : extAdjacencyClass thesisType1 (GenFlagClass.mk t1_v0_R) ⟨0, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨0, by decide⟩).mpr t1_v0_R_extAdj_v0_raw
  have h_extSum_val : (extSum thesisType1 ⟨0, by decide⟩) (GenFlagClass.mk t1_v0_R) =
      (genFlagAutCount CG2 thesisType1 (GenFlagClass.mk t1_v0_R).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t1_v0_R.str, t1_v0_R.embedding, t1_v0_R.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t1_v0_R).out.forget t1_v0_R.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t1_v0_R_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t1_v0_R_sigmaAutCount,
      genFlagAutCount_flagIso t1_v0_R_forget_iso, flag5_aut]
  have h_df : (Nat.descFactorial t1_v0_R.size thesisType1.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma1_witness_contribution_v0_B
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType1 ⟨0, by decide⟩) (GenFlagClass.mk t1_v0_B)) *
      (genNormalisationFactor thesisType1 (GenFlagClass.mk t1_v0_B).out *
        phi.eval (GenFlagClass.mk t1_v0_B).out.forget) =
      4 / 120 * phi.eval certF4 := by
  have h_iso : GenFlagIso thesisType1 (GenFlagClass.mk t1_v0_B).out t1_v0_B :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t1_v0_B))
  have h_adj : extAdjacencyClass thesisType1 (GenFlagClass.mk t1_v0_B) ⟨0, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨0, by decide⟩).mpr t1_v0_B_extAdj_v0_raw
  have h_extSum_val : (extSum thesisType1 ⟨0, by decide⟩) (GenFlagClass.mk t1_v0_B) =
      (genFlagAutCount CG2 thesisType1 (GenFlagClass.mk t1_v0_B).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t1_v0_B.str, t1_v0_B.embedding, t1_v0_B.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t1_v0_B).out.forget t1_v0_B.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t1_v0_B_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t1_v0_B_sigmaAutCount,
      genFlagAutCount_flagIso t1_v0_B_forget_iso, certF4_aut]
  have h_df : (Nat.descFactorial t1_v0_B.size thesisType1.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

/-! ### σ₁-4-E.6: pairwise distinctness of the 6 witness classes

Each `t1_v*` witness has `embedding = Fin.castLE` (sending `⟨i, _⟩ → ⟨i, _⟩`),
so any σ-iso `φ : F ≃ F'` between two witnesses fixes positions 0..3 by
`compat`. The remaining position 4 is forced to itself by injectivity of `φ`
on `Fin 5`. Hence `φ = id` and the iso reduces to structural equality of
`(str.1, str.2)`, which is decidable.

Need: 7 distinctness facts.
* v1-side: `C(4,2) = 6` pairs (a-b, a-c, a-d, b-c, b-d, c-d).
* v0-side: 1 pair (R-B).

The v1-side and v0-side master sums are computed *separately*, so cross-side
distinctness is not needed for the sigma1_nonneg proof. -/

/-- Generic helper: for any σ-iso `φ : F ≃ F'` between flags `F, F'` at a size-4
    `σ`-type, both with size 5 and `Fin.castLE`-style embeddings, we have
    `(φ x).val = x.val` for all `x : Fin F.size`. Used by all five `tN_size5_iso_id_castLE`. -/
private theorem genT_size5_iso_id_castLE
    {σ : GenFlagType CG2} (hσ : σ.size = 4)
    {F F' : GenFlag CG2 σ}
    (hF_size : F.size = 5) (hF'_size : F'.size = 5)
    (hF_emb : ∀ i : Fin σ.size, (F.embedding i).val = i.val)
    (hF'_emb : ∀ i : Fin σ.size, (F'.embedding i).val = i.val)
    (φ : Fin F.size ≃ Fin F'.size)
    (hcompat : ∀ i : Fin σ.size, φ (F.embedding i) = F'.embedding i) :
    ∀ x : Fin F.size, (φ x).val = x.val := by
  have h_fix : ∀ i : Fin σ.size,
      (φ (F.embedding i)).val = (F.embedding i).val := by
    intro i
    rw [hcompat i, hF_emb i, hF'_emb i]
  have h_fix_val : ∀ k : ℕ, k < 4 → ∀ y : Fin F.size, y.val = k → (φ y).val = k := by
    intro k hk y hy
    have hi_lt : k < σ.size := hσ ▸ hk
    let i : Fin σ.size := ⟨k, hi_lt⟩
    have h_emb_val : (F.embedding i).val = k := hF_emb i
    have hy_emb : y = F.embedding i := Fin.ext (by rw [h_emb_val]; exact hy)
    rw [hy_emb, h_fix i, h_emb_val]
  intro x
  have hx_lt : x.val < 5 := hF_size ▸ x.isLt
  by_cases hx4 : x.val = 4
  · have hφx_lt : (φ x).val < 5 := hF'_size ▸ (φ x).isLt
    by_contra h_ne
    have hφx_4 : (φ x).val < 4 := by
      rcases Nat.lt_or_ge (φ x).val 4 with h | h
      · exact h
      · exfalso; apply h_ne; omega
    have hy_lt_F : (φ x).val < F.size := by
      have : F.size = 5 := hF_size
      omega
    let y : Fin F.size := ⟨(φ x).val, hy_lt_F⟩
    have hy_val : y.val = (φ x).val := rfl
    have h_φy : (φ y).val = (φ x).val := h_fix_val (φ x).val hφx_4 y hy_val
    have h_φ_eq : φ y = φ x := Fin.ext h_φy
    have h_eq : y = x := φ.injective h_φ_eq
    have heq_val : y.val = x.val := congr_arg Fin.val h_eq
    rw [hy_val, hx4] at heq_val
    omega
  · have hxlt4 : x.val < 4 := by omega
    exact h_fix_val x.val hxlt4 x rfl

/-- Generic helper: if `comap φ F'.str = F.str` and φ is identity on values, then
    `F.str.1.Adj u v ↔ F'.str.1.Adj u' v'` whenever `u.val = u'.val` and `v.val = v'.val`.
    Independent of the σ-type. -/
private theorem genT_iso_str_adj_transport
    {σ : GenFlagType CG2} {F F' : GenFlag CG2 σ}
    (φ : Fin F.size ≃ Fin F'.size)
    (hstr : CG2.comap φ F'.str = F.str)
    (hφ_id : ∀ x : Fin F.size, (φ x).val = x.val)
    (u v : Fin F.size) (u' v' : Fin F'.size)
    (huv : u.val = u'.val) (hvv : v.val = v'.val) :
    F.str.1.Adj u v ↔ F'.str.1.Adj u' v' := by
  have h1 : F.str.1 = (CG2.comap φ F'.str).1 := by rw [hstr]
  have h2 : F.str.1.Adj u v ↔ F'.str.1.Adj (φ u) (φ v) := by
    rw [h1]; rfl
  have hφu : φ u = u' := Fin.ext (by rw [hφ_id u, huv])
  have hφv : φ v = v' := Fin.ext (by rw [hφ_id v, hvv])
  rw [h2, hφu, hφv]

/-- Generic helper for colour transport — independent of the σ-type. -/
private theorem genT_iso_str_col_transport
    {σ : GenFlagType CG2} {F F' : GenFlag CG2 σ}
    (φ : Fin F.size ≃ Fin F'.size)
    (hstr : CG2.comap φ F'.str = F.str)
    (hφ_id : ∀ x : Fin F.size, (φ x).val = x.val)
    (u : Fin F.size) (u' : Fin F'.size) (huv : u.val = u'.val) :
    F.str.2 u = F'.str.2 u' := by
  have h1 : F.str.2 = (CG2.comap φ F'.str).2 := by rw [hstr]
  have h2 : F.str.2 u = F'.str.2 (φ u) := by
    rw [h1]; rfl
  have hφu : φ u = u' := Fin.ext (by rw [hφ_id u, huv])
  rw [h2, hφu]

/-- For any σ-iso `φ : F ≃ F'` between thesisType1-flags `F, F'` of size 5 with
    embeddings `Fin.castLE` (sending `⟨i,_⟩ → ⟨i,_⟩`), we have `(φ x).val = x.val`
    for all `x : Fin F.size`. -/
private theorem t1_size5_iso_id_castLE
    {F F' : GenFlag CG2 thesisType1}
    (hF_size : F.size = 5) (hF'_size : F'.size = 5)
    (hF_emb : ∀ i : Fin thesisType1.size, (F.embedding i).val = i.val)
    (hF'_emb : ∀ i : Fin thesisType1.size, (F'.embedding i).val = i.val)
    (φ : Fin F.size ≃ Fin F'.size)
    (hcompat : ∀ i : Fin thesisType1.size, φ (F.embedding i) = F'.embedding i) :
    ∀ x : Fin F.size, (φ x).val = x.val :=
  genT_size5_iso_id_castLE rfl hF_size hF'_size hF_emb hF'_emb φ hcompat

/-- Helper: if `comap φ F'.str = F.str` and φ is identity on values, then
    `F.str.1.Adj u v ↔ F'.str.1.Adj u' v'` whenever `u.val = u'.val` and
    `v.val = v'.val`. -/
private theorem t1_iso_str_adj_transport
    {F F' : GenFlag CG2 thesisType1}
    (φ : Fin F.size ≃ Fin F'.size)
    (hstr : CG2.comap φ F'.str = F.str)
    (hφ_id : ∀ x : Fin F.size, (φ x).val = x.val)
    (u v : Fin F.size) (u' v' : Fin F'.size)
    (huv : u.val = u'.val) (hvv : v.val = v'.val) :
    F.str.1.Adj u v ↔ F'.str.1.Adj u' v' :=
  genT_iso_str_adj_transport φ hstr hφ_id u v u' v' huv hvv

/-- Helper: similar for colours. -/
private theorem t1_iso_str_col_transport
    {F F' : GenFlag CG2 thesisType1}
    (φ : Fin F.size ≃ Fin F'.size)
    (hstr : CG2.comap φ F'.str = F.str)
    (hφ_id : ∀ x : Fin F.size, (φ x).val = x.val)
    (u : Fin F.size) (u' : Fin F'.size) (huv : u.val = u'.val) :
    F.str.2 u = F'.str.2 u' :=
  genT_iso_str_col_transport φ hstr hφ_id u u' huv

/-- `t1_v1_a` and `t1_v1_b` are not σ-iso: different (w-v2) adjacencies. -/
private theorem t1_v1_a_not_iso_t1_v1_b :
    ¬ GenFlagIso thesisType1 t1_v1_a t1_v1_b := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t1_v1_a.size, (φ x).val = x.val :=
    t1_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  -- t1_v1_b adj 4-2, but t1_v1_a does not.
  have h_iff : t1_v1_a.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t1_v1_b.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t1_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hb : t1_v1_b.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t1_v1_b, SimpleGraph.fromRel_adj]
  have ha : ¬ t1_v1_a.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t1_v1_a, SimpleGraph.fromRel_adj]
  exact ha (h_iff.mpr hb)

/-- `t1_v1_a` and `t1_v1_c` are not σ-iso: different (w-v3) adjacencies. -/
private theorem t1_v1_a_not_iso_t1_v1_c :
    ¬ GenFlagIso thesisType1 t1_v1_a t1_v1_c := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t1_v1_a.size, (φ x).val = x.val :=
    t1_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t1_v1_a.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ ↔
      t1_v1_c.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ :=
    t1_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hc : t1_v1_c.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t1_v1_c, SimpleGraph.fromRel_adj]
  have ha : ¬ t1_v1_a.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t1_v1_a, SimpleGraph.fromRel_adj]
  exact ha (h_iff.mpr hc)

/-- `t1_v1_a` and `t1_v1_d` are not σ-iso. -/
private theorem t1_v1_a_not_iso_t1_v1_d :
    ¬ GenFlagIso thesisType1 t1_v1_a t1_v1_d := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t1_v1_a.size, (φ x).val = x.val :=
    t1_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t1_v1_a.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t1_v1_d.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t1_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hd : t1_v1_d.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t1_v1_d, SimpleGraph.fromRel_adj]
  have ha : ¬ t1_v1_a.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t1_v1_a, SimpleGraph.fromRel_adj]
  exact ha (h_iff.mpr hd)

/-- `t1_v1_b` and `t1_v1_c` are not σ-iso: differ at (w-v2). -/
private theorem t1_v1_b_not_iso_t1_v1_c :
    ¬ GenFlagIso thesisType1 t1_v1_b t1_v1_c := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t1_v1_b.size, (φ x).val = x.val :=
    t1_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t1_v1_b.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t1_v1_c.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t1_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hb : t1_v1_b.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t1_v1_b, SimpleGraph.fromRel_adj]
  have hc : ¬ t1_v1_c.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t1_v1_c, SimpleGraph.fromRel_adj]
  exact hc (h_iff.mp hb)

/-- `t1_v1_b` and `t1_v1_d` are not σ-iso: differ at (w-v3). -/
private theorem t1_v1_b_not_iso_t1_v1_d :
    ¬ GenFlagIso thesisType1 t1_v1_b t1_v1_d := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t1_v1_b.size, (φ x).val = x.val :=
    t1_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t1_v1_b.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ ↔
      t1_v1_d.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ :=
    t1_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hd : t1_v1_d.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t1_v1_d, SimpleGraph.fromRel_adj]
  have hb : ¬ t1_v1_b.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t1_v1_b, SimpleGraph.fromRel_adj]
  exact hb (h_iff.mpr hd)

/-- `t1_v1_c` and `t1_v1_d` are not σ-iso: differ at (w-v2). -/
private theorem t1_v1_c_not_iso_t1_v1_d :
    ¬ GenFlagIso thesisType1 t1_v1_c t1_v1_d := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t1_v1_c.size, (φ x).val = x.val :=
    t1_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t1_v1_c.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t1_v1_d.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t1_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hd : t1_v1_d.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t1_v1_d, SimpleGraph.fromRel_adj]
  have hc : ¬ t1_v1_c.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t1_v1_c, SimpleGraph.fromRel_adj]
  exact hc (h_iff.mpr hd)

/-- `t1_v0_R` and `t1_v0_B` are not σ-iso: differ at colour of v4. -/
private theorem t1_v0_R_not_iso_t1_v0_B :
    ¬ GenFlagIso thesisType1 t1_v0_R t1_v0_B := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t1_v0_R.size, (φ x).val = x.val :=
    t1_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t1_v0_R.str.2 (⟨4, by decide⟩ : Fin 5) = t1_v0_B.str.2 ⟨4, by decide⟩ :=
    t1_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t1_v0_R.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 1 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t1_v0_B.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 1 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

/-- Lifted to classes: `⟦t1_v1_a⟧ ≠ ⟦t1_v1_b⟧`. -/
private theorem mk_t1_v1_a_ne_mk_t1_v1_b :
    (GenFlagClass.mk t1_v1_a : GenFlagClass CG2 thesisType1) ≠ GenFlagClass.mk t1_v1_b :=
  fun h => t1_v1_a_not_iso_t1_v1_b (Quotient.exact h)

private theorem mk_t1_v1_a_ne_mk_t1_v1_c :
    (GenFlagClass.mk t1_v1_a : GenFlagClass CG2 thesisType1) ≠ GenFlagClass.mk t1_v1_c :=
  fun h => t1_v1_a_not_iso_t1_v1_c (Quotient.exact h)

private theorem mk_t1_v1_a_ne_mk_t1_v1_d :
    (GenFlagClass.mk t1_v1_a : GenFlagClass CG2 thesisType1) ≠ GenFlagClass.mk t1_v1_d :=
  fun h => t1_v1_a_not_iso_t1_v1_d (Quotient.exact h)

private theorem mk_t1_v1_b_ne_mk_t1_v1_c :
    (GenFlagClass.mk t1_v1_b : GenFlagClass CG2 thesisType1) ≠ GenFlagClass.mk t1_v1_c :=
  fun h => t1_v1_b_not_iso_t1_v1_c (Quotient.exact h)

private theorem mk_t1_v1_b_ne_mk_t1_v1_d :
    (GenFlagClass.mk t1_v1_b : GenFlagClass CG2 thesisType1) ≠ GenFlagClass.mk t1_v1_d :=
  fun h => t1_v1_b_not_iso_t1_v1_d (Quotient.exact h)

private theorem mk_t1_v1_c_ne_mk_t1_v1_d :
    (GenFlagClass.mk t1_v1_c : GenFlagClass CG2 thesisType1) ≠ GenFlagClass.mk t1_v1_d :=
  fun h => t1_v1_c_not_iso_t1_v1_d (Quotient.exact h)

private theorem mk_t1_v0_R_ne_mk_t1_v0_B :
    (GenFlagClass.mk t1_v0_R : GenFlagClass CG2 thesisType1) ≠ GenFlagClass.mk t1_v0_B :=
  fun h => t1_v0_R_not_iso_t1_v0_B (Quotient.exact h)

/-! ### σ₅-4-E.5: per-witness contribution lemmas for thesisType5

Mirrors `sigma1_witness_contribution_v*` for the 6 σ₅ witnesses. The
cancelling pair `t5_v2_b ↔ t5_v0_R_b` uses `t5_v0_R_b.forget` as a shared
reference and carries `genFlagAutCount t5_v0_R_b.forget` symbolically;
their contributions cancel in `sigma5_nonneg`'s combo via subtraction. -/

set_option maxHeartbeats 4000000 in
private theorem sigma5_witness_contribution_v2_a
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType5 ⟨2, by decide⟩) (GenFlagClass.mk t5_v2_a)) *
      (genNormalisationFactor thesisType5 (GenFlagClass.mk t5_v2_a).out *
        phi.eval (GenFlagClass.mk t5_v2_a).out.forget) =
      1 / 120 * phi.eval sdpFlag37 := by
  have h_iso : GenFlagIso thesisType5 (GenFlagClass.mk t5_v2_a).out t5_v2_a :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t5_v2_a))
  have h_adj : extAdjacencyClass thesisType5 (GenFlagClass.mk t5_v2_a) ⟨2, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨2, by decide⟩).mpr t5_v2_a_extAdj_v2_raw
  have h_extSum_val : (extSum thesisType5 ⟨2, by decide⟩) (GenFlagClass.mk t5_v2_a) =
      (genFlagAutCount CG2 thesisType5 (GenFlagClass.mk t5_v2_a).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t5_v2_a.str, t5_v2_a.embedding, t5_v2_a.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t5_v2_a).out.forget t5_v2_a.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t5_v2_a_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t5_v2_a_sigmaAutCount,
      genFlagAutCount_flagIso t5_v2_a_forget_iso, sdpFlag37_aut]
  have h_df : (Nat.descFactorial t5_v2_a.size thesisType5.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma5_witness_contribution_v2_b
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType5 ⟨2, by decide⟩) (GenFlagClass.mk t5_v2_b)) *
      (genNormalisationFactor thesisType5 (GenFlagClass.mk t5_v2_b).out *
        phi.eval (GenFlagClass.mk t5_v2_b).out.forget) =
      (genFlagAutCount CG2 (GenFlagType.empty CG2) t5_v0_R_b.forget : ℝ) / 120 *
        phi.eval t5_v0_R_b.forget := by
  have h_iso : GenFlagIso thesisType5 (GenFlagClass.mk t5_v2_b).out t5_v2_b :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t5_v2_b))
  have h_adj : extAdjacencyClass thesisType5 (GenFlagClass.mk t5_v2_b) ⟨2, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨2, by decide⟩).mpr t5_v2_b_extAdj_v2_raw
  have h_extSum_val : (extSum thesisType5 ⟨2, by decide⟩) (GenFlagClass.mk t5_v2_b) =
      (genFlagAutCount CG2 thesisType5 (GenFlagClass.mk t5_v2_b).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t5_v2_b.str, t5_v2_b.embedding, t5_v2_b.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t5_v2_b).out.forget t5_v2_b.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t5_v2_b_forget_iso_v0_R_b)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t5_v2_b_sigmaAutCount,
      genFlagAutCount_flagIso t5_v2_b_forget_iso_v0_R_b]
  have h_df : (Nat.descFactorial t5_v2_b.size thesisType5.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma5_witness_contribution_v2_c
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType5 ⟨2, by decide⟩) (GenFlagClass.mk t5_v2_c)) *
      (genNormalisationFactor thesisType5 (GenFlagClass.mk t5_v2_c).out *
        phi.eval (GenFlagClass.mk t5_v2_c).out.forget) =
      2 / 120 * phi.eval sdpFlag55 := by
  have h_iso : GenFlagIso thesisType5 (GenFlagClass.mk t5_v2_c).out t5_v2_c :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t5_v2_c))
  have h_adj : extAdjacencyClass thesisType5 (GenFlagClass.mk t5_v2_c) ⟨2, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨2, by decide⟩).mpr t5_v2_c_extAdj_v2_raw
  have h_extSum_val : (extSum thesisType5 ⟨2, by decide⟩) (GenFlagClass.mk t5_v2_c) =
      (genFlagAutCount CG2 thesisType5 (GenFlagClass.mk t5_v2_c).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t5_v2_c.str, t5_v2_c.embedding, t5_v2_c.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t5_v2_c).out.forget t5_v2_c.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t5_v2_c_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t5_v2_c_sigmaAutCount,
      genFlagAutCount_flagIso t5_v2_c_forget_iso, sdpFlag55_aut]
  have h_df : (Nat.descFactorial t5_v2_c.size thesisType5.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma5_witness_contribution_v0_R_a
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType5 ⟨0, by decide⟩) (GenFlagClass.mk t5_v0_R_a)) *
      (genNormalisationFactor thesisType5 (GenFlagClass.mk t5_v0_R_a).out *
        phi.eval (GenFlagClass.mk t5_v0_R_a).out.forget) =
      1 / 120 * phi.eval flag17 := by
  have h_iso : GenFlagIso thesisType5 (GenFlagClass.mk t5_v0_R_a).out t5_v0_R_a :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t5_v0_R_a))
  have h_adj : extAdjacencyClass thesisType5 (GenFlagClass.mk t5_v0_R_a) ⟨0, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨0, by decide⟩).mpr t5_v0_R_a_extAdj_v0_raw
  have h_extSum_val : (extSum thesisType5 ⟨0, by decide⟩) (GenFlagClass.mk t5_v0_R_a) =
      (genFlagAutCount CG2 thesisType5 (GenFlagClass.mk t5_v0_R_a).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t5_v0_R_a.str, t5_v0_R_a.embedding, t5_v0_R_a.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t5_v0_R_a).out.forget t5_v0_R_a.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t5_v0_R_a_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t5_v0_R_a_sigmaAutCount,
      genFlagAutCount_flagIso t5_v0_R_a_forget_iso, flag17_aut]
  have h_df : (Nat.descFactorial t5_v0_R_a.size thesisType5.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma5_witness_contribution_v0_R_b
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType5 ⟨0, by decide⟩) (GenFlagClass.mk t5_v0_R_b)) *
      (genNormalisationFactor thesisType5 (GenFlagClass.mk t5_v0_R_b).out *
        phi.eval (GenFlagClass.mk t5_v0_R_b).out.forget) =
      (genFlagAutCount CG2 (GenFlagType.empty CG2) t5_v0_R_b.forget : ℝ) / 120 *
        phi.eval t5_v0_R_b.forget := by
  have h_iso : GenFlagIso thesisType5 (GenFlagClass.mk t5_v0_R_b).out t5_v0_R_b :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t5_v0_R_b))
  have h_adj : extAdjacencyClass thesisType5 (GenFlagClass.mk t5_v0_R_b) ⟨0, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨0, by decide⟩).mpr t5_v0_R_b_extAdj_v0_raw
  have h_extSum_val : (extSum thesisType5 ⟨0, by decide⟩) (GenFlagClass.mk t5_v0_R_b) =
      (genFlagAutCount CG2 thesisType5 (GenFlagClass.mk t5_v0_R_b).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t5_v0_R_b.str, t5_v0_R_b.embedding, t5_v0_R_b.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t5_v0_R_b).out.forget t5_v0_R_b.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ h_iso_forget]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t5_v0_R_b_sigmaAutCount]
  have h_df : (Nat.descFactorial t5_v0_R_b.size thesisType5.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma5_witness_contribution_v0_B
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType5 ⟨0, by decide⟩) (GenFlagClass.mk t5_v0_B)) *
      (genNormalisationFactor thesisType5 (GenFlagClass.mk t5_v0_B).out *
        phi.eval (GenFlagClass.mk t5_v0_B).out.forget) =
      2 / 120 * phi.eval flag16 := by
  have h_iso : GenFlagIso thesisType5 (GenFlagClass.mk t5_v0_B).out t5_v0_B :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t5_v0_B))
  have h_adj : extAdjacencyClass thesisType5 (GenFlagClass.mk t5_v0_B) ⟨0, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨0, by decide⟩).mpr t5_v0_B_extAdj_v0_raw
  have h_extSum_val : (extSum thesisType5 ⟨0, by decide⟩) (GenFlagClass.mk t5_v0_B) =
      (genFlagAutCount CG2 thesisType5 (GenFlagClass.mk t5_v0_B).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t5_v0_B.str, t5_v0_B.embedding, t5_v0_B.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t5_v0_B).out.forget t5_v0_B.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t5_v0_B_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t5_v0_B_sigmaAutCount,
      genFlagAutCount_flagIso t5_v0_B_forget_iso, flag16_aut]
  have h_df : (Nat.descFactorial t5_v0_B.size thesisType5.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

/-! ### σ₄-4-E.5: per-witness contribution lemmas for thesisType4

6 contributions: 2 v0-side + 4 v1-side. Each maps to a named cert flag
(certF8, certF31, flag12, flag15, flag32, flag34). -/

set_option maxHeartbeats 4000000 in
private theorem sigma4_witness_contribution_v0_a
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType4 ⟨0, by decide⟩) (GenFlagClass.mk t4_v0_a)) *
      (genNormalisationFactor thesisType4 (GenFlagClass.mk t4_v0_a).out *
        phi.eval (GenFlagClass.mk t4_v0_a).out.forget) =
      2 / 120 * phi.eval flag15 := by
  have h_iso : GenFlagIso thesisType4 (GenFlagClass.mk t4_v0_a).out t4_v0_a :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t4_v0_a))
  have h_adj : extAdjacencyClass thesisType4 (GenFlagClass.mk t4_v0_a) ⟨0, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨0, by decide⟩).mpr t4_v0_a_extAdj_v0_raw
  have h_extSum_val : (extSum thesisType4 ⟨0, by decide⟩) (GenFlagClass.mk t4_v0_a) =
      (genFlagAutCount CG2 thesisType4 (GenFlagClass.mk t4_v0_a).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t4_v0_a.str, t4_v0_a.embedding, t4_v0_a.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t4_v0_a).out.forget t4_v0_a.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t4_v0_a_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t4_v0_a_sigmaAutCount,
      genFlagAutCount_flagIso t4_v0_a_forget_iso, flag15_aut]
  have h_df : (Nat.descFactorial t4_v0_a.size thesisType4.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma4_witness_contribution_v0_b
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType4 ⟨0, by decide⟩) (GenFlagClass.mk t4_v0_b)) *
      (genNormalisationFactor thesisType4 (GenFlagClass.mk t4_v0_b).out *
        phi.eval (GenFlagClass.mk t4_v0_b).out.forget) =
      6 / 120 * phi.eval flag34 := by
  have h_iso : GenFlagIso thesisType4 (GenFlagClass.mk t4_v0_b).out t4_v0_b :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t4_v0_b))
  have h_adj : extAdjacencyClass thesisType4 (GenFlagClass.mk t4_v0_b) ⟨0, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨0, by decide⟩).mpr t4_v0_b_extAdj_v0_raw
  have h_extSum_val : (extSum thesisType4 ⟨0, by decide⟩) (GenFlagClass.mk t4_v0_b) =
      (genFlagAutCount CG2 thesisType4 (GenFlagClass.mk t4_v0_b).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t4_v0_b.str, t4_v0_b.embedding, t4_v0_b.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t4_v0_b).out.forget t4_v0_b.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t4_v0_b_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t4_v0_b_sigmaAutCount,
      genFlagAutCount_flagIso t4_v0_b_forget_iso, flag34_aut]
  have h_df : (Nat.descFactorial t4_v0_b.size thesisType4.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma4_witness_contribution_v1_a
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType4 ⟨1, by decide⟩) (GenFlagClass.mk t4_v1_a)) *
      (genNormalisationFactor thesisType4 (GenFlagClass.mk t4_v1_a).out *
        phi.eval (GenFlagClass.mk t4_v1_a).out.forget) =
      1 / 120 * phi.eval flag12 := by
  have h_iso : GenFlagIso thesisType4 (GenFlagClass.mk t4_v1_a).out t4_v1_a :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t4_v1_a))
  have h_adj : extAdjacencyClass thesisType4 (GenFlagClass.mk t4_v1_a) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t4_v1_a_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType4 ⟨1, by decide⟩) (GenFlagClass.mk t4_v1_a) =
      (genFlagAutCount CG2 thesisType4 (GenFlagClass.mk t4_v1_a).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t4_v1_a.str, t4_v1_a.embedding, t4_v1_a.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t4_v1_a).out.forget t4_v1_a.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t4_v1_a_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t4_v1_a_sigmaAutCount,
      genFlagAutCount_flagIso t4_v1_a_forget_iso, flag12_aut]
  have h_df : (Nat.descFactorial t4_v1_a.size thesisType4.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma4_witness_contribution_v1_b
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType4 ⟨1, by decide⟩) (GenFlagClass.mk t4_v1_b)) *
      (genNormalisationFactor thesisType4 (GenFlagClass.mk t4_v1_b).out *
        phi.eval (GenFlagClass.mk t4_v1_b).out.forget) =
      4 / 120 * phi.eval flag32 := by
  have h_iso : GenFlagIso thesisType4 (GenFlagClass.mk t4_v1_b).out t4_v1_b :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t4_v1_b))
  have h_adj : extAdjacencyClass thesisType4 (GenFlagClass.mk t4_v1_b) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t4_v1_b_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType4 ⟨1, by decide⟩) (GenFlagClass.mk t4_v1_b) =
      (genFlagAutCount CG2 thesisType4 (GenFlagClass.mk t4_v1_b).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t4_v1_b.str, t4_v1_b.embedding, t4_v1_b.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t4_v1_b).out.forget t4_v1_b.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t4_v1_b_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t4_v1_b_sigmaAutCount,
      genFlagAutCount_flagIso t4_v1_b_forget_iso, flag32_aut]
  have h_df : (Nat.descFactorial t4_v1_b.size thesisType4.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma4_witness_contribution_v1_c
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType4 ⟨1, by decide⟩) (GenFlagClass.mk t4_v1_c)) *
      (genNormalisationFactor thesisType4 (GenFlagClass.mk t4_v1_c).out *
        phi.eval (GenFlagClass.mk t4_v1_c).out.forget) =
      1 / 120 * phi.eval certF8 := by
  have h_iso : GenFlagIso thesisType4 (GenFlagClass.mk t4_v1_c).out t4_v1_c :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t4_v1_c))
  have h_adj : extAdjacencyClass thesisType4 (GenFlagClass.mk t4_v1_c) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t4_v1_c_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType4 ⟨1, by decide⟩) (GenFlagClass.mk t4_v1_c) =
      (genFlagAutCount CG2 thesisType4 (GenFlagClass.mk t4_v1_c).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t4_v1_c.str, t4_v1_c.embedding, t4_v1_c.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t4_v1_c).out.forget t4_v1_c.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t4_v1_c_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t4_v1_c_sigmaAutCount,
      genFlagAutCount_flagIso t4_v1_c_forget_iso, certF8_aut]
  have h_df : (Nat.descFactorial t4_v1_c.size thesisType4.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma4_witness_contribution_v1_d
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType4 ⟨1, by decide⟩) (GenFlagClass.mk t4_v1_d)) *
      (genNormalisationFactor thesisType4 (GenFlagClass.mk t4_v1_d).out *
        phi.eval (GenFlagClass.mk t4_v1_d).out.forget) =
      4 / 120 * phi.eval certF31 := by
  have h_iso : GenFlagIso thesisType4 (GenFlagClass.mk t4_v1_d).out t4_v1_d :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t4_v1_d))
  have h_adj : extAdjacencyClass thesisType4 (GenFlagClass.mk t4_v1_d) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t4_v1_d_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType4 ⟨1, by decide⟩) (GenFlagClass.mk t4_v1_d) =
      (genFlagAutCount CG2 thesisType4 (GenFlagClass.mk t4_v1_d).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t4_v1_d.str, t4_v1_d.embedding, t4_v1_d.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t4_v1_d).out.forget t4_v1_d.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t4_v1_d_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t4_v1_d_sigmaAutCount,
      genFlagAutCount_flagIso t4_v1_d_forget_iso, certF31_aut]
  have h_df : (Nat.descFactorial t4_v1_d.size thesisType4.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

/-! ### σ₃-4-E.5: per-witness contribution lemmas for thesisType3

6 contributions: 2 v0-side + 4 v1-side. Each maps to a named cert flag
(flag12, flag15, flag24, flag25, certF11, certF22). -/

set_option maxHeartbeats 4000000 in
private theorem sigma3_witness_contribution_v0_a
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType3 ⟨0, by decide⟩) (GenFlagClass.mk t3_v0_a)) *
      (genNormalisationFactor thesisType3 (GenFlagClass.mk t3_v0_a).out *
        phi.eval (GenFlagClass.mk t3_v0_a).out.forget) =
      2 / 120 * phi.eval flag25 := by
  have h_iso : GenFlagIso thesisType3 (GenFlagClass.mk t3_v0_a).out t3_v0_a :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t3_v0_a))
  have h_adj : extAdjacencyClass thesisType3 (GenFlagClass.mk t3_v0_a) ⟨0, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨0, by decide⟩).mpr t3_v0_a_extAdj_v0_raw
  have h_extSum_val : (extSum thesisType3 ⟨0, by decide⟩) (GenFlagClass.mk t3_v0_a) =
      (genFlagAutCount CG2 thesisType3 (GenFlagClass.mk t3_v0_a).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t3_v0_a.str, t3_v0_a.embedding, t3_v0_a.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t3_v0_a).out.forget t3_v0_a.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t3_v0_a_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t3_v0_a_sigmaAutCount,
      genFlagAutCount_flagIso t3_v0_a_forget_iso, flag25_aut]
  have h_df : (Nat.descFactorial t3_v0_a.size thesisType3.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma3_witness_contribution_v0_b
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType3 ⟨0, by decide⟩) (GenFlagClass.mk t3_v0_b)) *
      (genNormalisationFactor thesisType3 (GenFlagClass.mk t3_v0_b).out *
        phi.eval (GenFlagClass.mk t3_v0_b).out.forget) =
      2 / 120 * phi.eval flag15 := by
  have h_iso : GenFlagIso thesisType3 (GenFlagClass.mk t3_v0_b).out t3_v0_b :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t3_v0_b))
  have h_adj : extAdjacencyClass thesisType3 (GenFlagClass.mk t3_v0_b) ⟨0, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨0, by decide⟩).mpr t3_v0_b_extAdj_v0_raw
  have h_extSum_val : (extSum thesisType3 ⟨0, by decide⟩) (GenFlagClass.mk t3_v0_b) =
      (genFlagAutCount CG2 thesisType3 (GenFlagClass.mk t3_v0_b).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t3_v0_b.str, t3_v0_b.embedding, t3_v0_b.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t3_v0_b).out.forget t3_v0_b.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t3_v0_b_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t3_v0_b_sigmaAutCount,
      genFlagAutCount_flagIso t3_v0_b_forget_iso, flag15_aut]
  have h_df : (Nat.descFactorial t3_v0_b.size thesisType3.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma3_witness_contribution_v1_a
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType3 ⟨1, by decide⟩) (GenFlagClass.mk t3_v1_a)) *
      (genNormalisationFactor thesisType3 (GenFlagClass.mk t3_v1_a).out *
        phi.eval (GenFlagClass.mk t3_v1_a).out.forget) =
      2 / 120 * phi.eval flag24 := by
  have h_iso : GenFlagIso thesisType3 (GenFlagClass.mk t3_v1_a).out t3_v1_a :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t3_v1_a))
  have h_adj : extAdjacencyClass thesisType3 (GenFlagClass.mk t3_v1_a) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t3_v1_a_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType3 ⟨1, by decide⟩) (GenFlagClass.mk t3_v1_a) =
      (genFlagAutCount CG2 thesisType3 (GenFlagClass.mk t3_v1_a).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t3_v1_a.str, t3_v1_a.embedding, t3_v1_a.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t3_v1_a).out.forget t3_v1_a.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t3_v1_a_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t3_v1_a_sigmaAutCount,
      genFlagAutCount_flagIso t3_v1_a_forget_iso, flag24_aut]
  have h_df : (Nat.descFactorial t3_v1_a.size thesisType3.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma3_witness_contribution_v1_b
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType3 ⟨1, by decide⟩) (GenFlagClass.mk t3_v1_b)) *
      (genNormalisationFactor thesisType3 (GenFlagClass.mk t3_v1_b).out *
        phi.eval (GenFlagClass.mk t3_v1_b).out.forget) =
      1 / 120 * phi.eval flag12 := by
  have h_iso : GenFlagIso thesisType3 (GenFlagClass.mk t3_v1_b).out t3_v1_b :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t3_v1_b))
  have h_adj : extAdjacencyClass thesisType3 (GenFlagClass.mk t3_v1_b) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t3_v1_b_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType3 ⟨1, by decide⟩) (GenFlagClass.mk t3_v1_b) =
      (genFlagAutCount CG2 thesisType3 (GenFlagClass.mk t3_v1_b).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t3_v1_b.str, t3_v1_b.embedding, t3_v1_b.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t3_v1_b).out.forget t3_v1_b.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t3_v1_b_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t3_v1_b_sigmaAutCount,
      genFlagAutCount_flagIso t3_v1_b_forget_iso, flag12_aut]
  have h_df : (Nat.descFactorial t3_v1_b.size thesisType3.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma3_witness_contribution_v1_c
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType3 ⟨1, by decide⟩) (GenFlagClass.mk t3_v1_c)) *
      (genNormalisationFactor thesisType3 (GenFlagClass.mk t3_v1_c).out *
        phi.eval (GenFlagClass.mk t3_v1_c).out.forget) =
      1 / 120 * phi.eval certF22 := by
  have h_iso : GenFlagIso thesisType3 (GenFlagClass.mk t3_v1_c).out t3_v1_c :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t3_v1_c))
  have h_adj : extAdjacencyClass thesisType3 (GenFlagClass.mk t3_v1_c) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t3_v1_c_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType3 ⟨1, by decide⟩) (GenFlagClass.mk t3_v1_c) =
      (genFlagAutCount CG2 thesisType3 (GenFlagClass.mk t3_v1_c).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t3_v1_c.str, t3_v1_c.embedding, t3_v1_c.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t3_v1_c).out.forget t3_v1_c.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t3_v1_c_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t3_v1_c_sigmaAutCount,
      genFlagAutCount_flagIso t3_v1_c_forget_iso, certF22_aut]
  have h_df : (Nat.descFactorial t3_v1_c.size thesisType3.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma3_witness_contribution_v1_d
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType3 ⟨1, by decide⟩) (GenFlagClass.mk t3_v1_d)) *
      (genNormalisationFactor thesisType3 (GenFlagClass.mk t3_v1_d).out *
        phi.eval (GenFlagClass.mk t3_v1_d).out.forget) =
      2 / 120 * phi.eval certF11 := by
  have h_iso : GenFlagIso thesisType3 (GenFlagClass.mk t3_v1_d).out t3_v1_d :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t3_v1_d))
  have h_adj : extAdjacencyClass thesisType3 (GenFlagClass.mk t3_v1_d) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t3_v1_d_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType3 ⟨1, by decide⟩) (GenFlagClass.mk t3_v1_d) =
      (genFlagAutCount CG2 thesisType3 (GenFlagClass.mk t3_v1_d).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t3_v1_d.str, t3_v1_d.embedding, t3_v1_d.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t3_v1_d).out.forget t3_v1_d.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t3_v1_d_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t3_v1_d_sigmaAutCount,
      genFlagAutCount_flagIso t3_v1_d_forget_iso, certF11_aut]
  have h_df : (Nat.descFactorial t3_v1_d.size thesisType3.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

/-! ### σ₂-4-E.5: per-witness contribution lemmas for thesisType2

9 contributions: 1 v0-side + 8 v1-side. Each maps to a named cert flag
(certF6, flag15, flag25, flag34, sdpF7, sdpF20, sdpF30) with the aut
count computed via CGraphBridge. -/

set_option maxHeartbeats 4000000 in
private theorem sigma2_witness_contribution_v0
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType2 ⟨0, by decide⟩) (GenFlagClass.mk t2_v0)) *
      (genNormalisationFactor thesisType2 (GenFlagClass.mk t2_v0).out *
        phi.eval (GenFlagClass.mk t2_v0).out.forget) =
      24 / 120 * phi.eval certF6 := by
  have h_iso : GenFlagIso thesisType2 (GenFlagClass.mk t2_v0).out t2_v0 :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t2_v0))
  have h_adj : extAdjacencyClass thesisType2 (GenFlagClass.mk t2_v0) ⟨0, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨0, by decide⟩).mpr t2_v0_extAdj_v0_raw
  have h_extSum_val : (extSum thesisType2 ⟨0, by decide⟩) (GenFlagClass.mk t2_v0) =
      (genFlagAutCount CG2 thesisType2 (GenFlagClass.mk t2_v0).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t2_v0.str, t2_v0.embedding, t2_v0.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t2_v0).out.forget t2_v0.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t2_v0_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t2_v0_sigmaAutCount,
      genFlagAutCount_flagIso t2_v0_forget_iso, certF6_aut]
  have h_df : (Nat.descFactorial t2_v0.size thesisType2.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma2_witness_contribution_v1_a
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_a)) *
      (genNormalisationFactor thesisType2 (GenFlagClass.mk t2_v1_a).out *
        phi.eval (GenFlagClass.mk t2_v1_a).out.forget) =
      2 / 120 * phi.eval flag25 := by
  have h_iso : GenFlagIso thesisType2 (GenFlagClass.mk t2_v1_a).out t2_v1_a :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t2_v1_a))
  have h_adj : extAdjacencyClass thesisType2 (GenFlagClass.mk t2_v1_a) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t2_v1_a_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_a) =
      (genFlagAutCount CG2 thesisType2 (GenFlagClass.mk t2_v1_a).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t2_v1_a.str, t2_v1_a.embedding, t2_v1_a.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t2_v1_a).out.forget t2_v1_a.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t2_v1_a_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t2_v1_a_sigmaAutCount,
      genFlagAutCount_flagIso t2_v1_a_forget_iso, flag25_aut]
  have h_df : (Nat.descFactorial t2_v1_a.size thesisType2.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma2_witness_contribution_v1_b
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_b)) *
      (genNormalisationFactor thesisType2 (GenFlagClass.mk t2_v1_b).out *
        phi.eval (GenFlagClass.mk t2_v1_b).out.forget) =
      2 / 120 * phi.eval flag15 := by
  have h_iso : GenFlagIso thesisType2 (GenFlagClass.mk t2_v1_b).out t2_v1_b :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t2_v1_b))
  have h_adj : extAdjacencyClass thesisType2 (GenFlagClass.mk t2_v1_b) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t2_v1_b_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_b) =
      (genFlagAutCount CG2 thesisType2 (GenFlagClass.mk t2_v1_b).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t2_v1_b.str, t2_v1_b.embedding, t2_v1_b.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t2_v1_b).out.forget t2_v1_b.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t2_v1_b_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t2_v1_b_sigmaAutCount,
      genFlagAutCount_flagIso t2_v1_b_forget_iso, flag15_aut]
  have h_df : (Nat.descFactorial t2_v1_b.size thesisType2.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma2_witness_contribution_v1_c
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_c)) *
      (genNormalisationFactor thesisType2 (GenFlagClass.mk t2_v1_c).out *
        phi.eval (GenFlagClass.mk t2_v1_c).out.forget) =
      6 / 120 * phi.eval flag34 := by
  have h_iso : GenFlagIso thesisType2 (GenFlagClass.mk t2_v1_c).out t2_v1_c :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t2_v1_c))
  have h_adj : extAdjacencyClass thesisType2 (GenFlagClass.mk t2_v1_c) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t2_v1_c_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_c) =
      (genFlagAutCount CG2 thesisType2 (GenFlagClass.mk t2_v1_c).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t2_v1_c.str, t2_v1_c.embedding, t2_v1_c.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t2_v1_c).out.forget t2_v1_c.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t2_v1_c_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t2_v1_c_sigmaAutCount,
      genFlagAutCount_flagIso t2_v1_c_forget_iso, flag34_aut]
  have h_df : (Nat.descFactorial t2_v1_c.size thesisType2.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma2_witness_contribution_v1_g
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_g)) *
      (genNormalisationFactor thesisType2 (GenFlagClass.mk t2_v1_g).out *
        phi.eval (GenFlagClass.mk t2_v1_g).out.forget) =
      2 / 120 * phi.eval flag15 := by
  have h_iso : GenFlagIso thesisType2 (GenFlagClass.mk t2_v1_g).out t2_v1_g :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t2_v1_g))
  have h_adj : extAdjacencyClass thesisType2 (GenFlagClass.mk t2_v1_g) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t2_v1_g_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_g) =
      (genFlagAutCount CG2 thesisType2 (GenFlagClass.mk t2_v1_g).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t2_v1_g.str, t2_v1_g.embedding, t2_v1_g.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t2_v1_g).out.forget t2_v1_g.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t2_v1_g_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t2_v1_g_sigmaAutCount,
      genFlagAutCount_flagIso t2_v1_g_forget_iso, flag15_aut]
  have h_df : (Nat.descFactorial t2_v1_g.size thesisType2.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma2_witness_contribution_v1_d
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_d)) *
      (genNormalisationFactor thesisType2 (GenFlagClass.mk t2_v1_d).out *
        phi.eval (GenFlagClass.mk t2_v1_d).out.forget) =
      2 / 120 * phi.eval sdpF20 := by
  have h_iso : GenFlagIso thesisType2 (GenFlagClass.mk t2_v1_d).out t2_v1_d :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t2_v1_d))
  have h_adj : extAdjacencyClass thesisType2 (GenFlagClass.mk t2_v1_d) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t2_v1_d_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_d) =
      (genFlagAutCount CG2 thesisType2 (GenFlagClass.mk t2_v1_d).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t2_v1_d.str, t2_v1_d.embedding, t2_v1_d.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t2_v1_d).out.forget t2_v1_d.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t2_v1_d_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t2_v1_d_sigmaAutCount,
      genFlagAutCount_flagIso t2_v1_d_forget_iso, sdpF20_aut]
  have h_df : (Nat.descFactorial t2_v1_d.size thesisType2.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma2_witness_contribution_v1_e
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_e)) *
      (genNormalisationFactor thesisType2 (GenFlagClass.mk t2_v1_e).out *
        phi.eval (GenFlagClass.mk t2_v1_e).out.forget) =
      2 / 120 * phi.eval sdpF7 := by
  have h_iso : GenFlagIso thesisType2 (GenFlagClass.mk t2_v1_e).out t2_v1_e :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t2_v1_e))
  have h_adj : extAdjacencyClass thesisType2 (GenFlagClass.mk t2_v1_e) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t2_v1_e_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_e) =
      (genFlagAutCount CG2 thesisType2 (GenFlagClass.mk t2_v1_e).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t2_v1_e.str, t2_v1_e.embedding, t2_v1_e.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t2_v1_e).out.forget t2_v1_e.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t2_v1_e_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t2_v1_e_sigmaAutCount,
      genFlagAutCount_flagIso t2_v1_e_forget_iso, sdpF7_aut]
  have h_df : (Nat.descFactorial t2_v1_e.size thesisType2.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma2_witness_contribution_v1_f
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_f)) *
      (genNormalisationFactor thesisType2 (GenFlagClass.mk t2_v1_f).out *
        phi.eval (GenFlagClass.mk t2_v1_f).out.forget) =
      12 / 120 * phi.eval sdpF30 := by
  have h_iso : GenFlagIso thesisType2 (GenFlagClass.mk t2_v1_f).out t2_v1_f :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t2_v1_f))
  have h_adj : extAdjacencyClass thesisType2 (GenFlagClass.mk t2_v1_f) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t2_v1_f_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_f) =
      (genFlagAutCount CG2 thesisType2 (GenFlagClass.mk t2_v1_f).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t2_v1_f.str, t2_v1_f.embedding, t2_v1_f.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t2_v1_f).out.forget t2_v1_f.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t2_v1_f_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t2_v1_f_sigmaAutCount,
      genFlagAutCount_flagIso t2_v1_f_forget_iso, sdpF30_aut]
  have h_df : (Nat.descFactorial t2_v1_f.size thesisType2.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

set_option maxHeartbeats 4000000 in
private theorem sigma2_witness_contribution_v1_h
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    ((extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_h)) *
      (genNormalisationFactor thesisType2 (GenFlagClass.mk t2_v1_h).out *
        phi.eval (GenFlagClass.mk t2_v1_h).out.forget) =
      2 / 120 * phi.eval sdpF7 := by
  have h_iso : GenFlagIso thesisType2 (GenFlagClass.mk t2_v1_h).out t2_v1_h :=
    Quotient.exact (Quotient.out_eq (GenFlagClass.mk t2_v1_h))
  have h_adj : extAdjacencyClass thesisType2 (GenFlagClass.mk t2_v1_h) ⟨1, by decide⟩ :=
    (extAdjacency_iso_invariant h_iso ⟨1, by decide⟩).mpr t2_v1_h_extAdj_v1_raw
  have h_extSum_val : (extSum thesisType2 ⟨1, by decide⟩) (GenFlagClass.mk t2_v1_h) =
      (genFlagAutCount CG2 thesisType2 (GenFlagClass.mk t2_v1_h).out : ℝ) := by
    rw [extSum_apply, if_pos]
    rw [Finset.mem_filter]
    refine ⟨?_, h_adj⟩
    simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨t2_v1_h.str, t2_v1_h.embedding, t2_v1_h.isInduced⟩, rfl⟩
  rw [h_extSum_val]
  have h_iso_forget : GenFlagIso (GenFlagType.empty CG2)
      (GenFlagClass.mk t2_v1_h).out.forget t2_v1_h.forget := by
    obtain ⟨φ, hstr, _⟩ := h_iso
    exact ⟨φ, hstr, fun i => Fin.elim0 i⟩
  rw [genNormalisationFactor_flagIso h_iso,
      phi.eval_iso _ _ (h_iso_forget.trans t2_v1_h_forget_iso)]
  unfold genNormalisationFactor
  rw [genFlagAutCount_flagIso h_iso, t2_v1_h_sigmaAutCount,
      genFlagAutCount_flagIso t2_v1_h_forget_iso, sdpF7_aut]
  have h_df : (Nat.descFactorial t2_v1_h.size thesisType2.size : ℝ) = 120 := by
    change (Nat.descFactorial 5 4 : ℝ) = 120
    norm_num [Nat.descFactorial]
  rw [h_df]; push_cast; ring

/-! ### σ₄-4-E.6: pairwise distinctness for thesisType4 witnesses

v0-side: 2 witnesses → 1 pair. v1-side: 4 witnesses → 6 pairs. Total 7.
Helpers + 7 not_iso + 7 mk_ne. Mirrors σ₃-4-E.6 template. -/

private theorem t4_size5_iso_id_castLE
    {F F' : GenFlag CG2 thesisType4}
    (hF_size : F.size = 5) (hF'_size : F'.size = 5)
    (hF_emb : ∀ i : Fin thesisType4.size, (F.embedding i).val = i.val)
    (hF'_emb : ∀ i : Fin thesisType4.size, (F'.embedding i).val = i.val)
    (φ : Fin F.size ≃ Fin F'.size)
    (hcompat : ∀ i : Fin thesisType4.size, φ (F.embedding i) = F'.embedding i) :
    ∀ x : Fin F.size, (φ x).val = x.val :=
  genT_size5_iso_id_castLE rfl hF_size hF'_size hF_emb hF'_emb φ hcompat

private theorem t4_iso_str_adj_transport
    {F F' : GenFlag CG2 thesisType4}
    (φ : Fin F.size ≃ Fin F'.size)
    (hstr : CG2.comap φ F'.str = F.str)
    (hφ_id : ∀ x : Fin F.size, (φ x).val = x.val)
    (u v : Fin F.size) (u' v' : Fin F'.size)
    (huv : u.val = u'.val) (hvv : v.val = v'.val) :
    F.str.1.Adj u v ↔ F'.str.1.Adj u' v' :=
  genT_iso_str_adj_transport φ hstr hφ_id u v u' v' huv hvv

private theorem t4_iso_str_col_transport
    {F F' : GenFlag CG2 thesisType4}
    (φ : Fin F.size ≃ Fin F'.size)
    (hstr : CG2.comap φ F'.str = F.str)
    (hφ_id : ∀ x : Fin F.size, (φ x).val = x.val)
    (u : Fin F.size) (u' : Fin F'.size) (huv : u.val = u'.val) :
    F.str.2 u = F'.str.2 u' :=
  genT_iso_str_col_transport φ hstr hφ_id u u' huv

/-! Same-color pairs (3): adjacency-distinguishing at vertex 4. -/

private theorem t4_v0_a_not_iso_t4_v0_b :
    ¬ GenFlagIso thesisType4 t4_v0_a t4_v0_b := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t4_v0_a.size, (φ x).val = x.val :=
    t4_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t4_v0_a.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ ↔
      t4_v0_b.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ :=
    t4_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hb : t4_v0_b.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t4_v0_b, SimpleGraph.fromRel_adj]
  have ha : ¬ t4_v0_a.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t4_v0_a, SimpleGraph.fromRel_adj]
  exact ha (h_iff.mpr hb)

private theorem t4_v1_a_not_iso_t4_v1_b :
    ¬ GenFlagIso thesisType4 t4_v1_a t4_v1_b := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t4_v1_a.size, (φ x).val = x.val :=
    t4_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t4_v1_a.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t4_v1_b.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t4_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hb : t4_v1_b.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t4_v1_b, SimpleGraph.fromRel_adj]
  have ha : ¬ t4_v1_a.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t4_v1_a, SimpleGraph.fromRel_adj]
  exact ha (h_iff.mpr hb)

private theorem t4_v1_c_not_iso_t4_v1_d :
    ¬ GenFlagIso thesisType4 t4_v1_c t4_v1_d := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t4_v1_c.size, (φ x).val = x.val :=
    t4_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t4_v1_c.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t4_v1_d.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t4_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hd : t4_v1_d.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t4_v1_d, SimpleGraph.fromRel_adj]
  have hc : ¬ t4_v1_c.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t4_v1_c, SimpleGraph.fromRel_adj]
  exact hc (h_iff.mpr hd)

/-! Cross-color pairs (4): R vs B at vertex 4. -/

private theorem t4_v1_a_not_iso_t4_v1_c :
    ¬ GenFlagIso thesisType4 t4_v1_a t4_v1_c := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t4_v1_a.size, (φ x).val = x.val :=
    t4_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t4_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = t4_v1_c.str.2 ⟨4, by decide⟩ :=
    t4_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t4_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t4_v1_c.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t4_v1_a_not_iso_t4_v1_d :
    ¬ GenFlagIso thesisType4 t4_v1_a t4_v1_d := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t4_v1_a.size, (φ x).val = x.val :=
    t4_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t4_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = t4_v1_d.str.2 ⟨4, by decide⟩ :=
    t4_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t4_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t4_v1_d.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t4_v1_b_not_iso_t4_v1_c :
    ¬ GenFlagIso thesisType4 t4_v1_b t4_v1_c := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t4_v1_b.size, (φ x).val = x.val :=
    t4_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t4_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = t4_v1_c.str.2 ⟨4, by decide⟩ :=
    t4_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t4_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t4_v1_c.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t4_v1_b_not_iso_t4_v1_d :
    ¬ GenFlagIso thesisType4 t4_v1_b t4_v1_d := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t4_v1_b.size, (φ x).val = x.val :=
    t4_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t4_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = t4_v1_d.str.2 ⟨4, by decide⟩ :=
    t4_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t4_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t4_v1_d.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

/-! Lifted to classes: 7 mk_t4_v*_ne_mk_t4_v*. -/

private theorem mk_t4_v0_a_ne_mk_t4_v0_b :
    (GenFlagClass.mk t4_v0_a : GenFlagClass CG2 thesisType4) ≠ GenFlagClass.mk t4_v0_b :=
  fun h => t4_v0_a_not_iso_t4_v0_b (Quotient.exact h)
private theorem mk_t4_v1_a_ne_mk_t4_v1_b :
    (GenFlagClass.mk t4_v1_a : GenFlagClass CG2 thesisType4) ≠ GenFlagClass.mk t4_v1_b :=
  fun h => t4_v1_a_not_iso_t4_v1_b (Quotient.exact h)
private theorem mk_t4_v1_a_ne_mk_t4_v1_c :
    (GenFlagClass.mk t4_v1_a : GenFlagClass CG2 thesisType4) ≠ GenFlagClass.mk t4_v1_c :=
  fun h => t4_v1_a_not_iso_t4_v1_c (Quotient.exact h)
private theorem mk_t4_v1_a_ne_mk_t4_v1_d :
    (GenFlagClass.mk t4_v1_a : GenFlagClass CG2 thesisType4) ≠ GenFlagClass.mk t4_v1_d :=
  fun h => t4_v1_a_not_iso_t4_v1_d (Quotient.exact h)
private theorem mk_t4_v1_b_ne_mk_t4_v1_c :
    (GenFlagClass.mk t4_v1_b : GenFlagClass CG2 thesisType4) ≠ GenFlagClass.mk t4_v1_c :=
  fun h => t4_v1_b_not_iso_t4_v1_c (Quotient.exact h)
private theorem mk_t4_v1_b_ne_mk_t4_v1_d :
    (GenFlagClass.mk t4_v1_b : GenFlagClass CG2 thesisType4) ≠ GenFlagClass.mk t4_v1_d :=
  fun h => t4_v1_b_not_iso_t4_v1_d (Quotient.exact h)
private theorem mk_t4_v1_c_ne_mk_t4_v1_d :
    (GenFlagClass.mk t4_v1_c : GenFlagClass CG2 thesisType4) ≠ GenFlagClass.mk t4_v1_d :=
  fun h => t4_v1_c_not_iso_t4_v1_d (Quotient.exact h)

/-! ### σ₃-4-E.6: pairwise distinctness for thesisType3 witnesses

v0-side: 2 witnesses → 1 pair. v1-side: 4 witnesses → 6 pairs. Total 7.
Helpers + 7 not_iso + 7 mk_ne (lifted to GenFlagClass.mk). -/

private theorem t3_size5_iso_id_castLE
    {F F' : GenFlag CG2 thesisType3}
    (hF_size : F.size = 5) (hF'_size : F'.size = 5)
    (hF_emb : ∀ i : Fin thesisType3.size, (F.embedding i).val = i.val)
    (hF'_emb : ∀ i : Fin thesisType3.size, (F'.embedding i).val = i.val)
    (φ : Fin F.size ≃ Fin F'.size)
    (hcompat : ∀ i : Fin thesisType3.size, φ (F.embedding i) = F'.embedding i) :
    ∀ x : Fin F.size, (φ x).val = x.val :=
  genT_size5_iso_id_castLE rfl hF_size hF'_size hF_emb hF'_emb φ hcompat

private theorem t3_iso_str_adj_transport
    {F F' : GenFlag CG2 thesisType3}
    (φ : Fin F.size ≃ Fin F'.size)
    (hstr : CG2.comap φ F'.str = F.str)
    (hφ_id : ∀ x : Fin F.size, (φ x).val = x.val)
    (u v : Fin F.size) (u' v' : Fin F'.size)
    (huv : u.val = u'.val) (hvv : v.val = v'.val) :
    F.str.1.Adj u v ↔ F'.str.1.Adj u' v' :=
  genT_iso_str_adj_transport φ hstr hφ_id u v u' v' huv hvv

private theorem t3_iso_str_col_transport
    {F F' : GenFlag CG2 thesisType3}
    (φ : Fin F.size ≃ Fin F'.size)
    (hstr : CG2.comap φ F'.str = F.str)
    (hφ_id : ∀ x : Fin F.size, (φ x).val = x.val)
    (u : Fin F.size) (u' : Fin F'.size) (huv : u.val = u'.val) :
    F.str.2 u = F'.str.2 u' :=
  genT_iso_str_col_transport φ hstr hφ_id u u' huv

/-! Same-color pairs (3): adjacency-distinguishing at vertex 4. -/

private theorem t3_v0_a_not_iso_t3_v0_b :
    ¬ GenFlagIso thesisType3 t3_v0_a t3_v0_b := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t3_v0_a.size, (φ x).val = x.val :=
    t3_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t3_v0_a.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ ↔
      t3_v0_b.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ :=
    t3_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hb : t3_v0_b.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t3_v0_b, SimpleGraph.fromRel_adj]
  have ha : ¬ t3_v0_a.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t3_v0_a, SimpleGraph.fromRel_adj]
  exact ha (h_iff.mpr hb)

private theorem t3_v1_a_not_iso_t3_v1_b :
    ¬ GenFlagIso thesisType3 t3_v1_a t3_v1_b := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t3_v1_a.size, (φ x).val = x.val :=
    t3_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t3_v1_a.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t3_v1_b.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t3_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hb : t3_v1_b.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t3_v1_b, SimpleGraph.fromRel_adj]
  have ha : ¬ t3_v1_a.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t3_v1_a, SimpleGraph.fromRel_adj]
  exact ha (h_iff.mpr hb)

private theorem t3_v1_c_not_iso_t3_v1_d :
    ¬ GenFlagIso thesisType3 t3_v1_c t3_v1_d := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t3_v1_c.size, (φ x).val = x.val :=
    t3_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t3_v1_c.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t3_v1_d.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t3_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hd : t3_v1_d.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t3_v1_d, SimpleGraph.fromRel_adj]
  have hc : ¬ t3_v1_c.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t3_v1_c, SimpleGraph.fromRel_adj]
  exact hc (h_iff.mpr hd)

/-! Cross-color pairs (4): R vs B at vertex 4. -/

private theorem t3_v1_a_not_iso_t3_v1_c :
    ¬ GenFlagIso thesisType3 t3_v1_a t3_v1_c := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t3_v1_a.size, (φ x).val = x.val :=
    t3_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t3_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = t3_v1_c.str.2 ⟨4, by decide⟩ :=
    t3_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t3_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t3_v1_c.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t3_v1_a_not_iso_t3_v1_d :
    ¬ GenFlagIso thesisType3 t3_v1_a t3_v1_d := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t3_v1_a.size, (φ x).val = x.val :=
    t3_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t3_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = t3_v1_d.str.2 ⟨4, by decide⟩ :=
    t3_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t3_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t3_v1_d.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t3_v1_b_not_iso_t3_v1_c :
    ¬ GenFlagIso thesisType3 t3_v1_b t3_v1_c := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t3_v1_b.size, (φ x).val = x.val :=
    t3_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t3_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = t3_v1_c.str.2 ⟨4, by decide⟩ :=
    t3_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t3_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t3_v1_c.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t3_v1_b_not_iso_t3_v1_d :
    ¬ GenFlagIso thesisType3 t3_v1_b t3_v1_d := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t3_v1_b.size, (φ x).val = x.val :=
    t3_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t3_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = t3_v1_d.str.2 ⟨4, by decide⟩ :=
    t3_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t3_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t3_v1_d.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

/-! Lifted to classes: 7 mk_t3_v*_ne_mk_t3_v*. -/

private theorem mk_t3_v0_a_ne_mk_t3_v0_b :
    (GenFlagClass.mk t3_v0_a : GenFlagClass CG2 thesisType3) ≠ GenFlagClass.mk t3_v0_b :=
  fun h => t3_v0_a_not_iso_t3_v0_b (Quotient.exact h)
private theorem mk_t3_v1_a_ne_mk_t3_v1_b :
    (GenFlagClass.mk t3_v1_a : GenFlagClass CG2 thesisType3) ≠ GenFlagClass.mk t3_v1_b :=
  fun h => t3_v1_a_not_iso_t3_v1_b (Quotient.exact h)
private theorem mk_t3_v1_a_ne_mk_t3_v1_c :
    (GenFlagClass.mk t3_v1_a : GenFlagClass CG2 thesisType3) ≠ GenFlagClass.mk t3_v1_c :=
  fun h => t3_v1_a_not_iso_t3_v1_c (Quotient.exact h)
private theorem mk_t3_v1_a_ne_mk_t3_v1_d :
    (GenFlagClass.mk t3_v1_a : GenFlagClass CG2 thesisType3) ≠ GenFlagClass.mk t3_v1_d :=
  fun h => t3_v1_a_not_iso_t3_v1_d (Quotient.exact h)
private theorem mk_t3_v1_b_ne_mk_t3_v1_c :
    (GenFlagClass.mk t3_v1_b : GenFlagClass CG2 thesisType3) ≠ GenFlagClass.mk t3_v1_c :=
  fun h => t3_v1_b_not_iso_t3_v1_c (Quotient.exact h)
private theorem mk_t3_v1_b_ne_mk_t3_v1_d :
    (GenFlagClass.mk t3_v1_b : GenFlagClass CG2 thesisType3) ≠ GenFlagClass.mk t3_v1_d :=
  fun h => t3_v1_b_not_iso_t3_v1_d (Quotient.exact h)
private theorem mk_t3_v1_c_ne_mk_t3_v1_d :
    (GenFlagClass.mk t3_v1_c : GenFlagClass CG2 thesisType3) ≠ GenFlagClass.mk t3_v1_d :=
  fun h => t3_v1_c_not_iso_t3_v1_d (Quotient.exact h)

/-! ### σ₂-4-E.6: pairwise distinctness for thesisType2 witnesses

8 v1-side witnesses (R/B × 4 leaf-subsets) → C(8,2) = 28 pairs.
v0-side has 1 witness so 0 pairs there. Helpers + 28 not_iso + 28 mk_ne. -/

private theorem t2_size5_iso_id_castLE
    {F F' : GenFlag CG2 thesisType2}
    (hF_size : F.size = 5) (hF'_size : F'.size = 5)
    (hF_emb : ∀ i : Fin thesisType2.size, (F.embedding i).val = i.val)
    (hF'_emb : ∀ i : Fin thesisType2.size, (F'.embedding i).val = i.val)
    (φ : Fin F.size ≃ Fin F'.size)
    (hcompat : ∀ i : Fin thesisType2.size, φ (F.embedding i) = F'.embedding i) :
    ∀ x : Fin F.size, (φ x).val = x.val :=
  genT_size5_iso_id_castLE rfl hF_size hF'_size hF_emb hF'_emb φ hcompat

private theorem t2_iso_str_adj_transport
    {F F' : GenFlag CG2 thesisType2}
    (φ : Fin F.size ≃ Fin F'.size)
    (hstr : CG2.comap φ F'.str = F.str)
    (hφ_id : ∀ x : Fin F.size, (φ x).val = x.val)
    (u v : Fin F.size) (u' v' : Fin F'.size)
    (huv : u.val = u'.val) (hvv : v.val = v'.val) :
    F.str.1.Adj u v ↔ F'.str.1.Adj u' v' :=
  genT_iso_str_adj_transport φ hstr hφ_id u v u' v' huv hvv

private theorem t2_iso_str_col_transport
    {F F' : GenFlag CG2 thesisType2}
    (φ : Fin F.size ≃ Fin F'.size)
    (hstr : CG2.comap φ F'.str = F.str)
    (hφ_id : ∀ x : Fin F.size, (φ x).val = x.val)
    (u : Fin F.size) (u' : Fin F'.size) (huv : u.val = u'.val) :
    F.str.2 u = F'.str.2 u' :=
  genT_iso_str_col_transport φ hstr hφ_id u u' huv

/-! Same-colour adjacency-distinguished pairs (12 R-R + B-B). The
    key facts are at (vw=4, v2 or v3): which witness has w-vᵢ edge. -/

private theorem t2_v1_a_not_iso_t2_v1_b :
    ¬ GenFlagIso thesisType2 t2_v1_a t2_v1_b := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_a.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t2_v1_a.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t2_v1_b.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t2_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hb : t2_v1_b.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_b, SimpleGraph.fromRel_adj]
  have ha : ¬ t2_v1_a.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_a, SimpleGraph.fromRel_adj]
  exact ha (h_iff.mpr hb)

private theorem t2_v1_a_not_iso_t2_v1_c :
    ¬ GenFlagIso thesisType2 t2_v1_a t2_v1_c := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_a.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t2_v1_a.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t2_v1_c.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t2_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hc : t2_v1_c.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_c, SimpleGraph.fromRel_adj]
  have ha : ¬ t2_v1_a.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_a, SimpleGraph.fromRel_adj]
  exact ha (h_iff.mpr hc)

private theorem t2_v1_a_not_iso_t2_v1_g :
    ¬ GenFlagIso thesisType2 t2_v1_a t2_v1_g := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_a.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t2_v1_a.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ ↔
      t2_v1_g.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ :=
    t2_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hg : t2_v1_g.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_g, SimpleGraph.fromRel_adj]
  have ha : ¬ t2_v1_a.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_a, SimpleGraph.fromRel_adj]
  exact ha (h_iff.mpr hg)

private theorem t2_v1_b_not_iso_t2_v1_c :
    ¬ GenFlagIso thesisType2 t2_v1_b t2_v1_c := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_b.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t2_v1_b.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ ↔
      t2_v1_c.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ :=
    t2_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hc : t2_v1_c.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_c, SimpleGraph.fromRel_adj]
  have hb : ¬ t2_v1_b.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_b, SimpleGraph.fromRel_adj]
  exact hb (h_iff.mpr hc)

private theorem t2_v1_b_not_iso_t2_v1_g :
    ¬ GenFlagIso thesisType2 t2_v1_b t2_v1_g := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_b.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t2_v1_b.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t2_v1_g.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t2_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hb : t2_v1_b.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_b, SimpleGraph.fromRel_adj]
  have hg : ¬ t2_v1_g.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_g, SimpleGraph.fromRel_adj]
  exact hg (h_iff.mp hb)

private theorem t2_v1_c_not_iso_t2_v1_g :
    ¬ GenFlagIso thesisType2 t2_v1_c t2_v1_g := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_c.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t2_v1_c.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t2_v1_g.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t2_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hc : t2_v1_c.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_c, SimpleGraph.fromRel_adj]
  have hg : ¬ t2_v1_g.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_g, SimpleGraph.fromRel_adj]
  exact hg (h_iff.mp hc)

private theorem t2_v1_d_not_iso_t2_v1_e :
    ¬ GenFlagIso thesisType2 t2_v1_d t2_v1_e := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_d.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t2_v1_d.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t2_v1_e.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t2_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have he : t2_v1_e.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_e, SimpleGraph.fromRel_adj]
  have hd : ¬ t2_v1_d.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_d, SimpleGraph.fromRel_adj]
  exact hd (h_iff.mpr he)

private theorem t2_v1_d_not_iso_t2_v1_f :
    ¬ GenFlagIso thesisType2 t2_v1_d t2_v1_f := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_d.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t2_v1_d.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t2_v1_f.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t2_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hf : t2_v1_f.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_f, SimpleGraph.fromRel_adj]
  have hd : ¬ t2_v1_d.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_d, SimpleGraph.fromRel_adj]
  exact hd (h_iff.mpr hf)

private theorem t2_v1_d_not_iso_t2_v1_h :
    ¬ GenFlagIso thesisType2 t2_v1_d t2_v1_h := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_d.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t2_v1_d.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ ↔
      t2_v1_h.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ :=
    t2_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hh : t2_v1_h.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_h, SimpleGraph.fromRel_adj]
  have hd : ¬ t2_v1_d.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_d, SimpleGraph.fromRel_adj]
  exact hd (h_iff.mpr hh)

private theorem t2_v1_e_not_iso_t2_v1_f :
    ¬ GenFlagIso thesisType2 t2_v1_e t2_v1_f := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_e.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t2_v1_e.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ ↔
      t2_v1_f.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ :=
    t2_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hf : t2_v1_f.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_f, SimpleGraph.fromRel_adj]
  have he : ¬ t2_v1_e.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_e, SimpleGraph.fromRel_adj]
  exact he (h_iff.mpr hf)

private theorem t2_v1_e_not_iso_t2_v1_h :
    ¬ GenFlagIso thesisType2 t2_v1_e t2_v1_h := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_e.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t2_v1_e.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t2_v1_h.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t2_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have he : t2_v1_e.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_e, SimpleGraph.fromRel_adj]
  have hh : ¬ t2_v1_h.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_h, SimpleGraph.fromRel_adj]
  exact hh (h_iff.mp he)

private theorem t2_v1_f_not_iso_t2_v1_h :
    ¬ GenFlagIso thesisType2 t2_v1_f t2_v1_h := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_f.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t2_v1_f.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ ↔
      t2_v1_h.str.1.Adj ⟨4, by decide⟩ ⟨2, by decide⟩ :=
    t2_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hf : t2_v1_f.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_f, SimpleGraph.fromRel_adj]
  have hh : ¬ t2_v1_h.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨2, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t2_v1_h, SimpleGraph.fromRel_adj]
  exact hh (h_iff.mp hf)

/-! Different-colour pairs (16): distinguished by colour of v4 (R=0 vs B=1).
    Inline pattern matches σ₁/σ₅'s `t1_v0_R_not_iso_t1_v0_B`. -/

private theorem t2_v1_a_not_iso_t2_v1_d :
    ¬ GenFlagIso thesisType2 t2_v1_a t2_v1_d := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_a.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_d.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_d.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t2_v1_a_not_iso_t2_v1_e :
    ¬ GenFlagIso thesisType2 t2_v1_a t2_v1_e := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_a.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_e.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_e.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t2_v1_a_not_iso_t2_v1_f :
    ¬ GenFlagIso thesisType2 t2_v1_a t2_v1_f := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_a.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_f.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_f.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t2_v1_a_not_iso_t2_v1_h :
    ¬ GenFlagIso thesisType2 t2_v1_a t2_v1_h := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_a.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_h.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_a.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_h.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t2_v1_b_not_iso_t2_v1_d :
    ¬ GenFlagIso thesisType2 t2_v1_b t2_v1_d := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_b.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_d.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_d.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t2_v1_b_not_iso_t2_v1_e :
    ¬ GenFlagIso thesisType2 t2_v1_b t2_v1_e := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_b.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_e.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_e.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t2_v1_b_not_iso_t2_v1_f :
    ¬ GenFlagIso thesisType2 t2_v1_b t2_v1_f := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_b.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_f.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_f.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t2_v1_b_not_iso_t2_v1_h :
    ¬ GenFlagIso thesisType2 t2_v1_b t2_v1_h := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_b.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_h.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_b.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_h.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t2_v1_c_not_iso_t2_v1_d :
    ¬ GenFlagIso thesisType2 t2_v1_c t2_v1_d := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_c.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_c.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_d.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_c.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_d.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t2_v1_c_not_iso_t2_v1_e :
    ¬ GenFlagIso thesisType2 t2_v1_c t2_v1_e := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_c.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_c.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_e.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_c.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_e.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t2_v1_c_not_iso_t2_v1_f :
    ¬ GenFlagIso thesisType2 t2_v1_c t2_v1_f := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_c.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_c.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_f.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_c.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_f.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t2_v1_c_not_iso_t2_v1_h :
    ¬ GenFlagIso thesisType2 t2_v1_c t2_v1_h := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_c.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_c.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_h.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_c.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_h.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t2_v1_g_not_iso_t2_v1_d :
    ¬ GenFlagIso thesisType2 t2_v1_g t2_v1_d := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_g.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_g.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_d.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_g.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_d.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t2_v1_g_not_iso_t2_v1_e :
    ¬ GenFlagIso thesisType2 t2_v1_g t2_v1_e := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_g.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_g.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_e.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_g.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_e.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t2_v1_g_not_iso_t2_v1_f :
    ¬ GenFlagIso thesisType2 t2_v1_g t2_v1_f := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_g.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_g.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_f.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_g.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_f.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

private theorem t2_v1_g_not_iso_t2_v1_h :
    ¬ GenFlagIso thesisType2 t2_v1_g t2_v1_h := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t2_v1_g.size, (φ x).val = x.val :=
    t2_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t2_v1_g.str.2 (⟨4, by decide⟩ : Fin 5) = t2_v1_h.str.2 ⟨4, by decide⟩ :=
    t2_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR : t2_v1_g.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 0 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t2_v1_h.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 0 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR, hB] at h_col
  exact absurd h_col (by decide)

/-! Lifted to classes: 28 mk_t2_v1_X_ne_mk_t2_v1_Y. -/

private theorem mk_t2_v1_a_ne_mk_t2_v1_b :
    (GenFlagClass.mk t2_v1_a : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_b :=
  fun h => t2_v1_a_not_iso_t2_v1_b (Quotient.exact h)
private theorem mk_t2_v1_a_ne_mk_t2_v1_c :
    (GenFlagClass.mk t2_v1_a : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_c :=
  fun h => t2_v1_a_not_iso_t2_v1_c (Quotient.exact h)
private theorem mk_t2_v1_a_ne_mk_t2_v1_g :
    (GenFlagClass.mk t2_v1_a : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_g :=
  fun h => t2_v1_a_not_iso_t2_v1_g (Quotient.exact h)
private theorem mk_t2_v1_a_ne_mk_t2_v1_d :
    (GenFlagClass.mk t2_v1_a : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_d :=
  fun h => t2_v1_a_not_iso_t2_v1_d (Quotient.exact h)
private theorem mk_t2_v1_a_ne_mk_t2_v1_e :
    (GenFlagClass.mk t2_v1_a : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_e :=
  fun h => t2_v1_a_not_iso_t2_v1_e (Quotient.exact h)
private theorem mk_t2_v1_a_ne_mk_t2_v1_f :
    (GenFlagClass.mk t2_v1_a : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_f :=
  fun h => t2_v1_a_not_iso_t2_v1_f (Quotient.exact h)
private theorem mk_t2_v1_a_ne_mk_t2_v1_h :
    (GenFlagClass.mk t2_v1_a : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_h :=
  fun h => t2_v1_a_not_iso_t2_v1_h (Quotient.exact h)
private theorem mk_t2_v1_b_ne_mk_t2_v1_c :
    (GenFlagClass.mk t2_v1_b : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_c :=
  fun h => t2_v1_b_not_iso_t2_v1_c (Quotient.exact h)
private theorem mk_t2_v1_b_ne_mk_t2_v1_g :
    (GenFlagClass.mk t2_v1_b : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_g :=
  fun h => t2_v1_b_not_iso_t2_v1_g (Quotient.exact h)
private theorem mk_t2_v1_b_ne_mk_t2_v1_d :
    (GenFlagClass.mk t2_v1_b : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_d :=
  fun h => t2_v1_b_not_iso_t2_v1_d (Quotient.exact h)
private theorem mk_t2_v1_b_ne_mk_t2_v1_e :
    (GenFlagClass.mk t2_v1_b : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_e :=
  fun h => t2_v1_b_not_iso_t2_v1_e (Quotient.exact h)
private theorem mk_t2_v1_b_ne_mk_t2_v1_f :
    (GenFlagClass.mk t2_v1_b : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_f :=
  fun h => t2_v1_b_not_iso_t2_v1_f (Quotient.exact h)
private theorem mk_t2_v1_b_ne_mk_t2_v1_h :
    (GenFlagClass.mk t2_v1_b : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_h :=
  fun h => t2_v1_b_not_iso_t2_v1_h (Quotient.exact h)
private theorem mk_t2_v1_c_ne_mk_t2_v1_g :
    (GenFlagClass.mk t2_v1_c : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_g :=
  fun h => t2_v1_c_not_iso_t2_v1_g (Quotient.exact h)
private theorem mk_t2_v1_c_ne_mk_t2_v1_d :
    (GenFlagClass.mk t2_v1_c : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_d :=
  fun h => t2_v1_c_not_iso_t2_v1_d (Quotient.exact h)
private theorem mk_t2_v1_c_ne_mk_t2_v1_e :
    (GenFlagClass.mk t2_v1_c : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_e :=
  fun h => t2_v1_c_not_iso_t2_v1_e (Quotient.exact h)
private theorem mk_t2_v1_c_ne_mk_t2_v1_f :
    (GenFlagClass.mk t2_v1_c : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_f :=
  fun h => t2_v1_c_not_iso_t2_v1_f (Quotient.exact h)
private theorem mk_t2_v1_c_ne_mk_t2_v1_h :
    (GenFlagClass.mk t2_v1_c : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_h :=
  fun h => t2_v1_c_not_iso_t2_v1_h (Quotient.exact h)
private theorem mk_t2_v1_g_ne_mk_t2_v1_d :
    (GenFlagClass.mk t2_v1_g : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_d :=
  fun h => t2_v1_g_not_iso_t2_v1_d (Quotient.exact h)
private theorem mk_t2_v1_g_ne_mk_t2_v1_e :
    (GenFlagClass.mk t2_v1_g : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_e :=
  fun h => t2_v1_g_not_iso_t2_v1_e (Quotient.exact h)
private theorem mk_t2_v1_g_ne_mk_t2_v1_f :
    (GenFlagClass.mk t2_v1_g : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_f :=
  fun h => t2_v1_g_not_iso_t2_v1_f (Quotient.exact h)
private theorem mk_t2_v1_g_ne_mk_t2_v1_h :
    (GenFlagClass.mk t2_v1_g : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_h :=
  fun h => t2_v1_g_not_iso_t2_v1_h (Quotient.exact h)
private theorem mk_t2_v1_d_ne_mk_t2_v1_e :
    (GenFlagClass.mk t2_v1_d : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_e :=
  fun h => t2_v1_d_not_iso_t2_v1_e (Quotient.exact h)
private theorem mk_t2_v1_d_ne_mk_t2_v1_f :
    (GenFlagClass.mk t2_v1_d : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_f :=
  fun h => t2_v1_d_not_iso_t2_v1_f (Quotient.exact h)
private theorem mk_t2_v1_d_ne_mk_t2_v1_h :
    (GenFlagClass.mk t2_v1_d : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_h :=
  fun h => t2_v1_d_not_iso_t2_v1_h (Quotient.exact h)
private theorem mk_t2_v1_e_ne_mk_t2_v1_f :
    (GenFlagClass.mk t2_v1_e : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_f :=
  fun h => t2_v1_e_not_iso_t2_v1_f (Quotient.exact h)
private theorem mk_t2_v1_e_ne_mk_t2_v1_h :
    (GenFlagClass.mk t2_v1_e : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_h :=
  fun h => t2_v1_e_not_iso_t2_v1_h (Quotient.exact h)
private theorem mk_t2_v1_f_ne_mk_t2_v1_h :
    (GenFlagClass.mk t2_v1_f : GenFlagClass CG2 thesisType2) ≠ GenFlagClass.mk t2_v1_h :=
  fun h => t2_v1_f_not_iso_t2_v1_h (Quotient.exact h)

/-! ### σ₅-4-E.6: pairwise distinctness for thesisType5 witnesses

Per σ₁ template adapted to thesisType5: helpers + 6 σ-non-iso theorems
(C(3,2) = 3 per side × 2 sides = 6 pairs needed for the witnessSet
sum_insert chain). -/

private theorem t5_size5_iso_id_castLE
    {F F' : GenFlag CG2 thesisType5}
    (hF_size : F.size = 5) (hF'_size : F'.size = 5)
    (hF_emb : ∀ i : Fin thesisType5.size, (F.embedding i).val = i.val)
    (hF'_emb : ∀ i : Fin thesisType5.size, (F'.embedding i).val = i.val)
    (φ : Fin F.size ≃ Fin F'.size)
    (hcompat : ∀ i : Fin thesisType5.size, φ (F.embedding i) = F'.embedding i) :
    ∀ x : Fin F.size, (φ x).val = x.val :=
  genT_size5_iso_id_castLE rfl hF_size hF'_size hF_emb hF'_emb φ hcompat

private theorem t5_iso_str_adj_transport
    {F F' : GenFlag CG2 thesisType5}
    (φ : Fin F.size ≃ Fin F'.size)
    (hstr : CG2.comap φ F'.str = F.str)
    (hφ_id : ∀ x : Fin F.size, (φ x).val = x.val)
    (u v : Fin F.size) (u' v' : Fin F'.size)
    (huv : u.val = u'.val) (hvv : v.val = v'.val) :
    F.str.1.Adj u v ↔ F'.str.1.Adj u' v' :=
  genT_iso_str_adj_transport φ hstr hφ_id u v u' v' huv hvv

private theorem t5_iso_str_col_transport
    {F F' : GenFlag CG2 thesisType5}
    (φ : Fin F.size ≃ Fin F'.size)
    (hstr : CG2.comap φ F'.str = F.str)
    (hφ_id : ∀ x : Fin F.size, (φ x).val = x.val)
    (u : Fin F.size) (u' : Fin F'.size) (huv : u.val = u'.val) :
    F.str.2 u = F'.str.2 u' :=
  genT_iso_str_col_transport φ hstr hφ_id u u' huv

/-- `t5_v2_a` and `t5_v2_b` not σ-iso: differ at (w-v1) adjacency. -/
private theorem t5_v2_a_not_iso_t5_v2_b :
    ¬ GenFlagIso thesisType5 t5_v2_a t5_v2_b := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t5_v2_a.size, (φ x).val = x.val :=
    t5_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t5_v2_a.str.1.Adj ⟨4, by decide⟩ ⟨1, by decide⟩ ↔
      t5_v2_b.str.1.Adj ⟨4, by decide⟩ ⟨1, by decide⟩ :=
    t5_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hb : t5_v2_b.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨1, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t5_v2_b, SimpleGraph.fromRel_adj]
  have ha : ¬ t5_v2_a.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨1, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t5_v2_a, SimpleGraph.fromRel_adj]
  exact ha (h_iff.mpr hb)

/-- `t5_v2_a` and `t5_v2_c` not σ-iso: differ at (w-v3) adjacency. -/
private theorem t5_v2_a_not_iso_t5_v2_c :
    ¬ GenFlagIso thesisType5 t5_v2_a t5_v2_c := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t5_v2_a.size, (φ x).val = x.val :=
    t5_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t5_v2_a.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ ↔
      t5_v2_c.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ :=
    t5_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hc : t5_v2_c.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t5_v2_c, SimpleGraph.fromRel_adj]
  have ha : ¬ t5_v2_a.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t5_v2_a, SimpleGraph.fromRel_adj]
  exact ha (h_iff.mpr hc)

/-- `t5_v2_b` and `t5_v2_c` not σ-iso: differ at (w-v1) adjacency. -/
private theorem t5_v2_b_not_iso_t5_v2_c :
    ¬ GenFlagIso thesisType5 t5_v2_b t5_v2_c := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t5_v2_b.size, (φ x).val = x.val :=
    t5_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t5_v2_b.str.1.Adj ⟨4, by decide⟩ ⟨1, by decide⟩ ↔
      t5_v2_c.str.1.Adj ⟨4, by decide⟩ ⟨1, by decide⟩ :=
    t5_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hb : t5_v2_b.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨1, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t5_v2_b, SimpleGraph.fromRel_adj]
  have hc : ¬ t5_v2_c.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨1, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t5_v2_c, SimpleGraph.fromRel_adj]
  exact hc (h_iff.mp hb)

/-- `t5_v0_R_a` and `t5_v0_R_b` not σ-iso: differ at (w-v3) adjacency. -/
private theorem t5_v0_R_a_not_iso_t5_v0_R_b :
    ¬ GenFlagIso thesisType5 t5_v0_R_a t5_v0_R_b := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t5_v0_R_a.size, (φ x).val = x.val :=
    t5_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_iff : t5_v0_R_a.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ ↔
      t5_v0_R_b.str.1.Adj ⟨4, by decide⟩ ⟨3, by decide⟩ :=
    t5_iso_str_adj_transport φ hstr hφ_id _ _ _ _ rfl rfl
  have hb : t5_v0_R_b.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change (SimpleGraph.fromRel _).Adj _ _
    simp [t5_v0_R_b, SimpleGraph.fromRel_adj]
  have ha : ¬ t5_v0_R_a.str.1.Adj (⟨4, by decide⟩ : Fin 5) ⟨3, by decide⟩ := by
    change ¬ (SimpleGraph.fromRel _).Adj _ _
    simp [t5_v0_R_a, SimpleGraph.fromRel_adj]
  exact ha (h_iff.mpr hb)

/-- `t5_v0_R_a` and `t5_v0_B` not σ-iso: differ at colour of v4. -/
private theorem t5_v0_R_a_not_iso_t5_v0_B :
    ¬ GenFlagIso thesisType5 t5_v0_R_a t5_v0_B := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t5_v0_R_a.size, (φ x).val = x.val :=
    t5_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t5_v0_R_a.str.2 (⟨4, by decide⟩ : Fin 5) = t5_v0_B.str.2 ⟨4, by decide⟩ :=
    t5_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR_a : t5_v0_R_a.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 2 ∨ (4 : ℕ) = 3 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t5_v0_B.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 2 ∨ (4 : ℕ) = 3 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR_a, hB] at h_col
  exact absurd h_col (by decide)

/-- `t5_v0_R_b` and `t5_v0_B` not σ-iso: differ at colour of v4. -/
private theorem t5_v0_R_b_not_iso_t5_v0_B :
    ¬ GenFlagIso thesisType5 t5_v0_R_b t5_v0_B := by
  rintro ⟨φ, hstr, hcompat⟩
  have hφ_id : ∀ x : Fin t5_v0_R_b.size, (φ x).val = x.val :=
    t5_size5_iso_id_castLE rfl rfl (fun i => rfl) (fun i => rfl) φ hcompat
  have h_col : t5_v0_R_b.str.2 (⟨4, by decide⟩ : Fin 5) = t5_v0_B.str.2 ⟨4, by decide⟩ :=
    t5_iso_str_col_transport φ hstr hφ_id _ _ rfl
  have hR_b : t5_v0_R_b.str.2 (⟨4, by decide⟩ : Fin 5) = 0 := by
    change (if (4 : ℕ) = 2 ∨ (4 : ℕ) = 3 then (1 : Fin 2) else 0) = 0; rfl
  have hB : t5_v0_B.str.2 (⟨4, by decide⟩ : Fin 5) = 1 := by
    change (if (4 : ℕ) = 2 ∨ (4 : ℕ) = 3 ∨ (4 : ℕ) = 4 then (1 : Fin 2) else 0) = 1; rfl
  rw [hR_b, hB] at h_col
  exact absurd h_col (by decide)

private theorem mk_t5_v2_a_ne_mk_t5_v2_b :
    (GenFlagClass.mk t5_v2_a : GenFlagClass CG2 thesisType5) ≠ GenFlagClass.mk t5_v2_b :=
  fun h => t5_v2_a_not_iso_t5_v2_b (Quotient.exact h)

private theorem mk_t5_v2_a_ne_mk_t5_v2_c :
    (GenFlagClass.mk t5_v2_a : GenFlagClass CG2 thesisType5) ≠ GenFlagClass.mk t5_v2_c :=
  fun h => t5_v2_a_not_iso_t5_v2_c (Quotient.exact h)

private theorem mk_t5_v2_b_ne_mk_t5_v2_c :
    (GenFlagClass.mk t5_v2_b : GenFlagClass CG2 thesisType5) ≠ GenFlagClass.mk t5_v2_c :=
  fun h => t5_v2_b_not_iso_t5_v2_c (Quotient.exact h)

private theorem mk_t5_v0_R_a_ne_mk_t5_v0_R_b :
    (GenFlagClass.mk t5_v0_R_a : GenFlagClass CG2 thesisType5) ≠ GenFlagClass.mk t5_v0_R_b :=
  fun h => t5_v0_R_a_not_iso_t5_v0_R_b (Quotient.exact h)

private theorem mk_t5_v0_R_a_ne_mk_t5_v0_B :
    (GenFlagClass.mk t5_v0_R_a : GenFlagClass CG2 thesisType5) ≠ GenFlagClass.mk t5_v0_B :=
  fun h => t5_v0_R_a_not_iso_t5_v0_B (Quotient.exact h)

private theorem mk_t5_v0_R_b_ne_mk_t5_v0_B :
    (GenFlagClass.mk t5_v0_R_b : GenFlagClass CG2 thesisType5) ≠ GenFlagClass.mk t5_v0_B :=
  fun h => t5_v0_R_b_not_iso_t5_v0_B (Quotient.exact h)

/-! ### σ₁-4-E.7: per-side master sum lemmas

For each side (v1, v0), expand `phi.evalAlg(genAveragingAlg σ (extSum σ ⟨i,_⟩))`
into a sum of named-flag contributions. -/

/-- thesisType1.size + 1 = 5, definitionally. -/
private theorem thesisType1_succ_eq_5 : thesisType1.size + 1 = 5 := rfl

-- Inlined membership proofs (instead of `mk_F_mem_genClassesOfSize`, which triggers
-- stack overflow on these size-5 thesisType1 flags). Pattern from F77_witness_mem_genClassesOfSize.
-- Conclusion uses `thesisType1.size + 1` to avoid unification at call sites.
set_option maxHeartbeats 800000 in
private theorem t1_v1_a_mk_mem_genClassesOfSize :
    GenFlagClass.mk t1_v1_a ∈
      genClassesOfSize CG2 thesisType1 (thesisType1.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t1_v1_a.str, t1_v1_a.embedding, t1_v1_a.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t1_v1_b_mk_mem_genClassesOfSize :
    GenFlagClass.mk t1_v1_b ∈
      genClassesOfSize CG2 thesisType1 (thesisType1.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t1_v1_b.str, t1_v1_b.embedding, t1_v1_b.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t1_v1_c_mk_mem_genClassesOfSize :
    GenFlagClass.mk t1_v1_c ∈
      genClassesOfSize CG2 thesisType1 (thesisType1.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t1_v1_c.str, t1_v1_c.embedding, t1_v1_c.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t1_v1_d_mk_mem_genClassesOfSize :
    GenFlagClass.mk t1_v1_d ∈
      genClassesOfSize CG2 thesisType1 (thesisType1.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t1_v1_d.str, t1_v1_d.embedding, t1_v1_d.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t1_v0_R_mk_mem_genClassesOfSize :
    GenFlagClass.mk t1_v0_R ∈
      genClassesOfSize CG2 thesisType1 (thesisType1.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t1_v0_R.str, t1_v0_R.embedding, t1_v0_R.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t1_v0_B_mk_mem_genClassesOfSize :
    GenFlagClass.mk t1_v0_B ∈
      genClassesOfSize CG2 thesisType1 (thesisType1.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t1_v0_B.str, t1_v0_B.embedding, t1_v0_B.isInduced⟩, rfl⟩

/-- The 4-element v1-side witness set as a Finset. -/
private noncomputable def t1_v1_witnessSet : Finset (GenFlagClass CG2 thesisType1) :=
  {GenFlagClass.mk t1_v1_a, GenFlagClass.mk t1_v1_b,
   GenFlagClass.mk t1_v1_c, GenFlagClass.mk t1_v1_d}

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t1_v1_a_mem_witnessSet :
    GenFlagClass.mk t1_v1_a ∈ t1_v1_witnessSet := by
  unfold t1_v1_witnessSet
  exact Finset.mem_insert_self _ _

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t1_v1_b_mem_witnessSet :
    GenFlagClass.mk t1_v1_b ∈ t1_v1_witnessSet := by
  unfold t1_v1_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert]
  exact Or.inr (Or.inl rfl)

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t1_v1_c_mem_witnessSet :
    GenFlagClass.mk t1_v1_c ∈ t1_v1_witnessSet := by
  unfold t1_v1_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert]
  exact Or.inr (Or.inr (Or.inl rfl))

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t1_v1_d_mem_witnessSet :
    GenFlagClass.mk t1_v1_d ∈ t1_v1_witnessSet := by
  unfold t1_v1_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr (Or.inr rfl))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
/-- v1-side master sum: phi.evalAlg of the averaged extSum over v1 equals the
    sum of 4 witness contributions (a, b, c, d). -/
private theorem phi_eval_v1_side
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (genAveragingAlg thesisType1 (extSum thesisType1 ⟨1, by decide⟩)) =
    2 / 120 * phi.eval flag24 + 1 / 120 * phi.eval flag12 +
    1 / 120 * phi.eval flag12 + 4 / 120 * phi.eval flag32 := by
  classical
  rw [evalAlg_genAveragingAlg_expand, extSum_support_eq]
  -- Outside-witnessSet contributions are 0 via dichotomy. Hoisted to
  -- Extensions.lean to keep the recursion-heavy elaboration out of this body.
  have h_outside_zero :=
    t1_v1_extSum_outside_witnessSet_zero phi t1_v1_witnessSet
      t1_v1_a_mem_witnessSet t1_v1_b_mem_witnessSet
      t1_v1_c_mem_witnessSet t1_v1_d_mem_witnessSet
  -- witnessSet ⊆ filter.
  have h_sub : t1_v1_witnessSet ⊆
      (genClassesOfSize CG2 thesisType1 (thesisType1.size + 1) (Nat.le_succ _)).filter
        (fun cls => extAdjacencyClass thesisType1 cls ⟨1, by decide⟩) := by
    intro cls hcls
    unfold t1_v1_witnessSet at hcls
    rw [Finset.mem_filter]
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton] at hcls
    rcases hcls with h | h | h | h
    · refine ⟨?_, ?_⟩ <;> rw [h]
      · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨t1_v1_a.str, t1_v1_a.embedding, t1_v1_a.isInduced⟩, rfl⟩
      · exact t1_v1_a_extAdj_v1
    · refine ⟨?_, ?_⟩ <;> rw [h]
      · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨t1_v1_b.str, t1_v1_b.embedding, t1_v1_b.isInduced⟩, rfl⟩
      · exact t1_v1_b_extAdj_v1
    · refine ⟨?_, ?_⟩ <;> rw [h]
      · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨t1_v1_c.str, t1_v1_c.embedding, t1_v1_c.isInduced⟩, rfl⟩
      · exact t1_v1_c_extAdj_v1
    · refine ⟨?_, ?_⟩ <;> rw [h]
      · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨t1_v1_d.str, t1_v1_d.embedding, t1_v1_d.isInduced⟩, rfl⟩
      · exact t1_v1_d_extAdj_v1
  rw [← Finset.sum_subset h_sub h_outside_zero]
  -- Expand witnessSet via sum_insert + sum_singleton.
  have h_ab : (GenFlagClass.mk t1_v1_a : GenFlagClass CG2 thesisType1) ∉
      ({GenFlagClass.mk t1_v1_b, GenFlagClass.mk t1_v1_c,
        GenFlagClass.mk t1_v1_d} : Finset _) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨mk_t1_v1_a_ne_mk_t1_v1_b, mk_t1_v1_a_ne_mk_t1_v1_c, mk_t1_v1_a_ne_mk_t1_v1_d⟩
  have h_bc : (GenFlagClass.mk t1_v1_b : GenFlagClass CG2 thesisType1) ∉
      ({GenFlagClass.mk t1_v1_c, GenFlagClass.mk t1_v1_d} : Finset _) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨mk_t1_v1_b_ne_mk_t1_v1_c, mk_t1_v1_b_ne_mk_t1_v1_d⟩
  have h_cd : (GenFlagClass.mk t1_v1_c : GenFlagClass CG2 thesisType1) ∉
      ({GenFlagClass.mk t1_v1_d} : Finset _) := by
    rw [Finset.mem_singleton]
    exact mk_t1_v1_c_ne_mk_t1_v1_d
  unfold t1_v1_witnessSet
  rw [Finset.sum_insert h_ab, Finset.sum_insert h_bc,
      Finset.sum_insert h_cd, Finset.sum_singleton]
  rw [sigma1_witness_contribution_v1_a phi, sigma1_witness_contribution_v1_b phi,
      sigma1_witness_contribution_v1_c phi, sigma1_witness_contribution_v1_d phi]
  ring

/-- The 2-element v0-side witness set. -/
private noncomputable def t1_v0_witnessSet : Finset (GenFlagClass CG2 thesisType1) :=
  {GenFlagClass.mk t1_v0_R, GenFlagClass.mk t1_v0_B}

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t1_v0_R_mem_witnessSet :
    GenFlagClass.mk t1_v0_R ∈ t1_v0_witnessSet := by
  unfold t1_v0_witnessSet
  exact Finset.mem_insert_self _ _

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t1_v0_B_mem_witnessSet :
    GenFlagClass.mk t1_v0_B ∈ t1_v0_witnessSet := by
  unfold t1_v0_witnessSet
  rw [Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
/-- v0-side master sum: phi.evalAlg of the averaged extSum over v0 equals the
    sum of 2 witness contributions (R, B). -/
private theorem phi_eval_v0_side
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (genAveragingAlg thesisType1 (extSum thesisType1 ⟨0, by decide⟩)) =
    6 / 120 * phi.eval flag5 + 4 / 120 * phi.eval certF4 := by
  classical
  rw [evalAlg_genAveragingAlg_expand, extSum_support_eq]
  have h_outside_zero :=
    t1_v0_extSum_outside_witnessSet_zero phi t1_v0_witnessSet
      t1_v0_R_mem_witnessSet t1_v0_B_mem_witnessSet
  have h_sub : t1_v0_witnessSet ⊆
      (genClassesOfSize CG2 thesisType1 (thesisType1.size + 1) (Nat.le_succ _)).filter
        (fun cls => extAdjacencyClass thesisType1 cls ⟨0, by decide⟩) := by
    intro cls hcls
    unfold t1_v0_witnessSet at hcls
    rw [Finset.mem_filter]
    rw [Finset.mem_insert, Finset.mem_singleton] at hcls
    rcases hcls with h | h
    · refine ⟨?_, ?_⟩ <;> rw [h]
      · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨t1_v0_R.str, t1_v0_R.embedding, t1_v0_R.isInduced⟩, rfl⟩
      · exact t1_v0_R_extAdj_v0
    · refine ⟨?_, ?_⟩ <;> rw [h]
      · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨t1_v0_B.str, t1_v0_B.embedding, t1_v0_B.isInduced⟩, rfl⟩
      · exact t1_v0_B_extAdj_v0
  rw [← Finset.sum_subset h_sub h_outside_zero]
  have h_RB : (GenFlagClass.mk t1_v0_R : GenFlagClass CG2 thesisType1) ∉
      ({GenFlagClass.mk t1_v0_B} : Finset _) := by
    rw [Finset.mem_singleton]
    exact mk_t1_v0_R_ne_mk_t1_v0_B
  unfold t1_v0_witnessSet
  rw [Finset.sum_insert h_RB, Finset.sum_singleton]
  rw [sigma1_witness_contribution_v0_R phi, sigma1_witness_contribution_v0_B phi]

set_option maxHeartbeats 8000000 in
theorem sigma1_nonneg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget) :
    0 ≤ -4 * phi.eval certF4 - 6 * phi.eval flag5
      + 2 * phi.eval flag12 + 2 * phi.eval flag24
      + 4 * phi.eval flag32 := by
  -- Local-or-zero discharge from hoisted helpers in Extensions.lean.
  have h_loz_a := t1_v1_extAdj_filter_local_or_zero phi
  have h_loz_b := t1_v0_extAdj_filter_local_or_zero phi
  -- σ-positivity of `extSum_v1 - extSum_v0` at every regular σ-functional.
  -- Reduces to 0 = 0 via `sigma1_extSum_diff_psi_eq_zero`.
  have h_sigma_pos_ab : ∀ ψ : GenLimitFunctional CG2 thesisType1
        brrbGenGraphClass brrbGenDelta,
      (∀ k, ∀ u : Fin (ψ.seq.seq k).size,
        (Finset.univ.filter ((ψ.seq.seq k).str.1.Adj u)).card =
          brrbGenDelta (ψ.seq.seq k).forget) →
      0 ≤ ψ.evalAlg (extSum thesisType1 ⟨1, by decide⟩
        - extSum thesisType1 ⟨0, by decide⟩) := by
    intro ψ h_reg
    rw [sigma1_extSum_diff_psi_eq_zero ψ h_reg]
  have h_sigma_pos_ba : ∀ ψ : GenLimitFunctional CG2 thesisType1
        brrbGenGraphClass brrbGenDelta,
      (∀ k, ∀ u : Fin (ψ.seq.seq k).size,
        (Finset.univ.filter ((ψ.seq.seq k).str.1.Adj u)).card =
          brrbGenDelta (ψ.seq.seq k).forget) →
      0 ≤ ψ.evalAlg (extSum thesisType1 ⟨0, by decide⟩
        - extSum thesisType1 ⟨1, by decide⟩) := by
    intro ψ h_reg
    have h := sigma1_extSum_diff_psi_eq_zero ψ h_reg
    have hflip : (extSum thesisType1 ⟨0, by decide⟩
        - extSum thesisType1 ⟨1, by decide⟩ : GenFlagAlg CG2 thesisType1) =
        (-1 : ℝ) • (extSum thesisType1 ⟨1, by decide⟩
        - extSum thesisType1 ⟨0, by decide⟩) := by
      rw [neg_smul, one_smul]; abel
    rw [hflip, ψ.evalAlg_smul, h, mul_zero]
  -- Combinatorial identity: 120 × phi.evalAlg of the difference equals the
  -- named-flag combo. Decompose via genAveragingAlg's linearity, evalAlg's
  -- linearity, and the per-side master sums.
  have h_combo : 120 * phi.evalAlg (genAveragingAlg thesisType1
      (extSum thesisType1 ⟨1, by decide⟩ - extSum thesisType1 ⟨0, by decide⟩)) =
      -4 * phi.eval certF4 - 6 * phi.eval flag5
        + 2 * phi.eval flag12 + 2 * phi.eval flag24
        + 4 * phi.eval flag32 := by
    have hsub : (extSum thesisType1 ⟨1, by decide⟩
        - extSum thesisType1 ⟨0, by decide⟩ : GenFlagAlg CG2 thesisType1) =
        extSum thesisType1 ⟨1, by decide⟩
        + (-1 : ℝ) • extSum thesisType1 ⟨0, by decide⟩ := by
      rw [neg_one_smul]; abel
    rw [hsub, genAveragingAlg_add, genAveragingAlg_smul,
        phi.evalAlg_add, phi.evalAlg_smul,
        phi_eval_v1_side phi, phi_eval_v0_side phi]
    ring
  exact sigma_nonneg_template_perfunc_weakened thesisType1 thesisType1_isLocalType
    ⟨1, by decide⟩ ⟨0, by decide⟩ phi hreg h_loz_a h_loz_b
    h_sigma_pos_ab h_sigma_pos_ba _ h_combo

/-! ### σ₂ nonnegativity infrastructure

Cert: `[24F₆, -4F₁₃, -4F₁₅, -2F₁₈, -2F₂₅, -12F₃₃, -6F₃₄]` (= sig2x2/2).
F₁₃ → sdpF7, F₁₈ → sdpF20, F₃₃ → sdpF30 in Lean.
Cert pair (a, b) = (⟨0⟩, ⟨1⟩) — v0=B centre vs v1=R leaf.
Master sum: extSum_v0 - extSum_v1 → 24/120*F₆ on v0-side minus the 8
v1-side contributions; ×120 yields the cert combo. -/

set_option maxHeartbeats 800000 in
private theorem t2_v0_mk_mem_genClassesOfSize :
    GenFlagClass.mk t2_v0 ∈
      genClassesOfSize CG2 thesisType2 (thesisType2.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t2_v0.str, t2_v0.embedding, t2_v0.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t2_v1_a_mk_mem_genClassesOfSize :
    GenFlagClass.mk t2_v1_a ∈
      genClassesOfSize CG2 thesisType2 (thesisType2.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t2_v1_a.str, t2_v1_a.embedding, t2_v1_a.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t2_v1_b_mk_mem_genClassesOfSize :
    GenFlagClass.mk t2_v1_b ∈
      genClassesOfSize CG2 thesisType2 (thesisType2.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t2_v1_b.str, t2_v1_b.embedding, t2_v1_b.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t2_v1_c_mk_mem_genClassesOfSize :
    GenFlagClass.mk t2_v1_c ∈
      genClassesOfSize CG2 thesisType2 (thesisType2.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t2_v1_c.str, t2_v1_c.embedding, t2_v1_c.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t2_v1_g_mk_mem_genClassesOfSize :
    GenFlagClass.mk t2_v1_g ∈
      genClassesOfSize CG2 thesisType2 (thesisType2.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t2_v1_g.str, t2_v1_g.embedding, t2_v1_g.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t2_v1_d_mk_mem_genClassesOfSize :
    GenFlagClass.mk t2_v1_d ∈
      genClassesOfSize CG2 thesisType2 (thesisType2.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t2_v1_d.str, t2_v1_d.embedding, t2_v1_d.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t2_v1_e_mk_mem_genClassesOfSize :
    GenFlagClass.mk t2_v1_e ∈
      genClassesOfSize CG2 thesisType2 (thesisType2.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t2_v1_e.str, t2_v1_e.embedding, t2_v1_e.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t2_v1_f_mk_mem_genClassesOfSize :
    GenFlagClass.mk t2_v1_f ∈
      genClassesOfSize CG2 thesisType2 (thesisType2.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t2_v1_f.str, t2_v1_f.embedding, t2_v1_f.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t2_v1_h_mk_mem_genClassesOfSize :
    GenFlagClass.mk t2_v1_h ∈
      genClassesOfSize CG2 thesisType2 (thesisType2.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t2_v1_h.str, t2_v1_h.embedding, t2_v1_h.isInduced⟩, rfl⟩

/-- Singleton v0-side σ₂ witness set. -/
private noncomputable def t2_v0_witnessSet : Finset (GenFlagClass CG2 thesisType2) :=
  {GenFlagClass.mk t2_v0}

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t2_v0_mem_witnessSet :
    GenFlagClass.mk t2_v0 ∈ t2_v0_witnessSet := by
  unfold t2_v0_witnessSet
  exact Finset.mem_singleton.mpr rfl

/-- 8-element v1-side σ₂ witness set. -/
private noncomputable def t2_v1_witnessSet : Finset (GenFlagClass CG2 thesisType2) :=
  {GenFlagClass.mk t2_v1_a, GenFlagClass.mk t2_v1_b, GenFlagClass.mk t2_v1_c,
   GenFlagClass.mk t2_v1_g, GenFlagClass.mk t2_v1_d, GenFlagClass.mk t2_v1_e,
   GenFlagClass.mk t2_v1_f, GenFlagClass.mk t2_v1_h}

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t2_v1_a_mem_witnessSet :
    GenFlagClass.mk t2_v1_a ∈ t2_v1_witnessSet := by
  unfold t2_v1_witnessSet
  exact Finset.mem_insert_self _ _

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t2_v1_b_mem_witnessSet :
    GenFlagClass.mk t2_v1_b ∈ t2_v1_witnessSet := by
  unfold t2_v1_witnessSet
  rw [Finset.mem_insert]
  right; rw [Finset.mem_insert]; left; rfl

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t2_v1_c_mem_witnessSet :
    GenFlagClass.mk t2_v1_c ∈ t2_v1_witnessSet := by
  unfold t2_v1_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert]
  right; right; rw [Finset.mem_insert]; left; rfl

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t2_v1_g_mem_witnessSet :
    GenFlagClass.mk t2_v1_g ∈ t2_v1_witnessSet := by
  unfold t2_v1_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert]
  right; right; right; rw [Finset.mem_insert]; left; rfl

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t2_v1_d_mem_witnessSet :
    GenFlagClass.mk t2_v1_d ∈ t2_v1_witnessSet := by
  unfold t2_v1_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert]
  right; right; right; right; rw [Finset.mem_insert]; left; rfl

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t2_v1_e_mem_witnessSet :
    GenFlagClass.mk t2_v1_e ∈ t2_v1_witnessSet := by
  unfold t2_v1_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_insert, Finset.mem_insert]
  right; right; right; right; right; rw [Finset.mem_insert]; left; rfl

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t2_v1_f_mem_witnessSet :
    GenFlagClass.mk t2_v1_f ∈ t2_v1_witnessSet := by
  unfold t2_v1_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_insert, Finset.mem_insert, Finset.mem_insert]
  right; right; right; right; right; right; rw [Finset.mem_insert]; left; rfl

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t2_v1_h_mem_witnessSet :
    GenFlagClass.mk t2_v1_h ∈ t2_v1_witnessSet := by
  unfold t2_v1_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_insert, Finset.mem_singleton]
  right; right; right; right; right; right; right; rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
/-- v0-side master sum for σ₂. -/
private theorem phi_eval_v0_side_t2
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (genAveragingAlg thesisType2 (extSum thesisType2 ⟨0, by decide⟩)) =
    24 / 120 * phi.eval certF6 := by
  classical
  rw [evalAlg_genAveragingAlg_expand, extSum_support_eq]
  have h_outside_zero :=
    t2_v0_extSum_outside_witnessSet_zero phi t2_v0_witnessSet t2_v0_mem_witnessSet
  have h_sub : t2_v0_witnessSet ⊆
      (genClassesOfSize CG2 thesisType2 (thesisType2.size + 1) (Nat.le_succ _)).filter
        (fun cls => extAdjacencyClass thesisType2 cls ⟨0, by decide⟩) := by
    intro cls hcls
    unfold t2_v0_witnessSet at hcls
    rw [Finset.mem_filter, Finset.mem_singleton] at *
    refine ⟨?_, ?_⟩ <;> rw [hcls]
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t2_v0.str, t2_v0.embedding, t2_v0.isInduced⟩, rfl⟩
    · exact t2_v0_extAdj_v0
  rw [← Finset.sum_subset h_sub h_outside_zero]
  unfold t2_v0_witnessSet
  rw [Finset.sum_singleton]
  rw [sigma2_witness_contribution_v0 phi]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
/-- v1-side master sum for σ₂. 8 witnesses. -/
private theorem phi_eval_v1_side_t2
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (genAveragingAlg thesisType2 (extSum thesisType2 ⟨1, by decide⟩)) =
    2 / 120 * phi.eval flag25 + 2 / 120 * phi.eval flag15 +
      6 / 120 * phi.eval flag34 + 2 / 120 * phi.eval flag15 +
      2 / 120 * phi.eval sdpF20 + 2 / 120 * phi.eval sdpF7 +
      12 / 120 * phi.eval sdpF30 + 2 / 120 * phi.eval sdpF7 := by
  classical
  rw [evalAlg_genAveragingAlg_expand, extSum_support_eq]
  have h_outside_zero :=
    t2_v1_extSum_outside_witnessSet_zero phi t2_v1_witnessSet
      t2_v1_a_mem_witnessSet t2_v1_b_mem_witnessSet t2_v1_c_mem_witnessSet
      t2_v1_g_mem_witnessSet t2_v1_d_mem_witnessSet t2_v1_e_mem_witnessSet
      t2_v1_f_mem_witnessSet t2_v1_h_mem_witnessSet
  have h_sub : t2_v1_witnessSet ⊆
      (genClassesOfSize CG2 thesisType2 (thesisType2.size + 1) (Nat.le_succ _)).filter
        (fun cls => extAdjacencyClass thesisType2 cls ⟨1, by decide⟩) := by
    intro cls hcls
    unfold t2_v1_witnessSet at hcls
    rw [Finset.mem_filter]
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_singleton] at hcls
    rcases hcls with h | h | h | h | h | h | h | h
    all_goals refine ⟨?_, ?_⟩ <;> rw [h]
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t2_v1_a.str, t2_v1_a.embedding, t2_v1_a.isInduced⟩, rfl⟩
    · exact t2_v1_a_extAdj_v1
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t2_v1_b.str, t2_v1_b.embedding, t2_v1_b.isInduced⟩, rfl⟩
    · exact t2_v1_b_extAdj_v1
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t2_v1_c.str, t2_v1_c.embedding, t2_v1_c.isInduced⟩, rfl⟩
    · exact t2_v1_c_extAdj_v1
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t2_v1_g.str, t2_v1_g.embedding, t2_v1_g.isInduced⟩, rfl⟩
    · exact t2_v1_g_extAdj_v1
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t2_v1_d.str, t2_v1_d.embedding, t2_v1_d.isInduced⟩, rfl⟩
    · exact t2_v1_d_extAdj_v1
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t2_v1_e.str, t2_v1_e.embedding, t2_v1_e.isInduced⟩, rfl⟩
    · exact t2_v1_e_extAdj_v1
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t2_v1_f.str, t2_v1_f.embedding, t2_v1_f.isInduced⟩, rfl⟩
    · exact t2_v1_f_extAdj_v1
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t2_v1_h.str, t2_v1_h.embedding, t2_v1_h.isInduced⟩, rfl⟩
    · exact t2_v1_h_extAdj_v1
  rw [← Finset.sum_subset h_sub h_outside_zero]
  -- Expand witnessSet via 7 sum_inserts + sum_singleton.
  have h_a_notin : (GenFlagClass.mk t2_v1_a : GenFlagClass CG2 thesisType2) ∉
      ({GenFlagClass.mk t2_v1_b, GenFlagClass.mk t2_v1_c,
        GenFlagClass.mk t2_v1_g, GenFlagClass.mk t2_v1_d,
        GenFlagClass.mk t2_v1_e, GenFlagClass.mk t2_v1_f,
        GenFlagClass.mk t2_v1_h} : Finset _) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton]
    push_neg
    exact ⟨mk_t2_v1_a_ne_mk_t2_v1_b, mk_t2_v1_a_ne_mk_t2_v1_c,
           mk_t2_v1_a_ne_mk_t2_v1_g, mk_t2_v1_a_ne_mk_t2_v1_d,
           mk_t2_v1_a_ne_mk_t2_v1_e, mk_t2_v1_a_ne_mk_t2_v1_f,
           mk_t2_v1_a_ne_mk_t2_v1_h⟩
  have h_b_notin : (GenFlagClass.mk t2_v1_b : GenFlagClass CG2 thesisType2) ∉
      ({GenFlagClass.mk t2_v1_c, GenFlagClass.mk t2_v1_g,
        GenFlagClass.mk t2_v1_d, GenFlagClass.mk t2_v1_e,
        GenFlagClass.mk t2_v1_f, GenFlagClass.mk t2_v1_h} : Finset _) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨mk_t2_v1_b_ne_mk_t2_v1_c, mk_t2_v1_b_ne_mk_t2_v1_g,
           mk_t2_v1_b_ne_mk_t2_v1_d, mk_t2_v1_b_ne_mk_t2_v1_e,
           mk_t2_v1_b_ne_mk_t2_v1_f, mk_t2_v1_b_ne_mk_t2_v1_h⟩
  have h_c_notin : (GenFlagClass.mk t2_v1_c : GenFlagClass CG2 thesisType2) ∉
      ({GenFlagClass.mk t2_v1_g, GenFlagClass.mk t2_v1_d,
        GenFlagClass.mk t2_v1_e, GenFlagClass.mk t2_v1_f,
        GenFlagClass.mk t2_v1_h} : Finset _) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨mk_t2_v1_c_ne_mk_t2_v1_g, mk_t2_v1_c_ne_mk_t2_v1_d,
           mk_t2_v1_c_ne_mk_t2_v1_e, mk_t2_v1_c_ne_mk_t2_v1_f,
           mk_t2_v1_c_ne_mk_t2_v1_h⟩
  have h_g_notin : (GenFlagClass.mk t2_v1_g : GenFlagClass CG2 thesisType2) ∉
      ({GenFlagClass.mk t2_v1_d, GenFlagClass.mk t2_v1_e,
        GenFlagClass.mk t2_v1_f, GenFlagClass.mk t2_v1_h} : Finset _) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton]
    push_neg
    exact ⟨mk_t2_v1_g_ne_mk_t2_v1_d, mk_t2_v1_g_ne_mk_t2_v1_e,
           mk_t2_v1_g_ne_mk_t2_v1_f, mk_t2_v1_g_ne_mk_t2_v1_h⟩
  have h_d_notin : (GenFlagClass.mk t2_v1_d : GenFlagClass CG2 thesisType2) ∉
      ({GenFlagClass.mk t2_v1_e, GenFlagClass.mk t2_v1_f,
        GenFlagClass.mk t2_v1_h} : Finset _) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨mk_t2_v1_d_ne_mk_t2_v1_e, mk_t2_v1_d_ne_mk_t2_v1_f,
           mk_t2_v1_d_ne_mk_t2_v1_h⟩
  have h_e_notin : (GenFlagClass.mk t2_v1_e : GenFlagClass CG2 thesisType2) ∉
      ({GenFlagClass.mk t2_v1_f, GenFlagClass.mk t2_v1_h} : Finset _) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨mk_t2_v1_e_ne_mk_t2_v1_f, mk_t2_v1_e_ne_mk_t2_v1_h⟩
  have h_f_notin : (GenFlagClass.mk t2_v1_f : GenFlagClass CG2 thesisType2) ∉
      ({GenFlagClass.mk t2_v1_h} : Finset _) := by
    rw [Finset.mem_singleton]
    exact mk_t2_v1_f_ne_mk_t2_v1_h
  unfold t2_v1_witnessSet
  rw [Finset.sum_insert h_a_notin, Finset.sum_insert h_b_notin,
      Finset.sum_insert h_c_notin, Finset.sum_insert h_g_notin,
      Finset.sum_insert h_d_notin, Finset.sum_insert h_e_notin,
      Finset.sum_insert h_f_notin, Finset.sum_singleton]
  rw [sigma2_witness_contribution_v1_a phi, sigma2_witness_contribution_v1_b phi,
      sigma2_witness_contribution_v1_c phi, sigma2_witness_contribution_v1_g phi,
      sigma2_witness_contribution_v1_d phi, sigma2_witness_contribution_v1_e phi,
      sigma2_witness_contribution_v1_f phi, sigma2_witness_contribution_v1_h phi]
  ring

set_option maxHeartbeats 8000000 in
theorem sigma2_nonneg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget) :
    0 ≤ 24 * phi.eval certF6 - 4 * phi.eval sdpF7
      - 4 * phi.eval flag15 - 2 * phi.eval sdpF20
      - 2 * phi.eval flag25 - 12 * phi.eval sdpF30
      - 6 * phi.eval flag34 := by
  have h_loz_a := t2_v0_extAdj_filter_local_or_zero phi
  have h_loz_b := t2_v1_extAdj_filter_local_or_zero phi
  have h_sigma_pos_ab : ∀ ψ : GenLimitFunctional CG2 thesisType2
        brrbGenGraphClass brrbGenDelta,
      (∀ k, ∀ u : Fin (ψ.seq.seq k).size,
        (Finset.univ.filter ((ψ.seq.seq k).str.1.Adj u)).card =
          brrbGenDelta (ψ.seq.seq k).forget) →
      0 ≤ ψ.evalAlg (extSum thesisType2 ⟨0, by decide⟩
        - extSum thesisType2 ⟨1, by decide⟩) := by
    intro ψ h_reg
    rw [extSum_diff_psi_eq_zero thesisType2 ⟨0, by decide⟩ ⟨1, by decide⟩ ψ h_reg]
  have h_sigma_pos_ba : ∀ ψ : GenLimitFunctional CG2 thesisType2
        brrbGenGraphClass brrbGenDelta,
      (∀ k, ∀ u : Fin (ψ.seq.seq k).size,
        (Finset.univ.filter ((ψ.seq.seq k).str.1.Adj u)).card =
          brrbGenDelta (ψ.seq.seq k).forget) →
      0 ≤ ψ.evalAlg (extSum thesisType2 ⟨1, by decide⟩
        - extSum thesisType2 ⟨0, by decide⟩) := by
    intro ψ h_reg
    have h := extSum_diff_psi_eq_zero thesisType2 ⟨0, by decide⟩ ⟨1, by decide⟩ ψ h_reg
    have hflip : (extSum thesisType2 ⟨1, by decide⟩
        - extSum thesisType2 ⟨0, by decide⟩ : GenFlagAlg CG2 thesisType2) =
        (-1 : ℝ) • (extSum thesisType2 ⟨0, by decide⟩
        - extSum thesisType2 ⟨1, by decide⟩) := by
      rw [neg_smul, one_smul]; abel
    rw [hflip, ψ.evalAlg_smul, h, mul_zero]
  have h_combo : 120 * phi.evalAlg (genAveragingAlg thesisType2
      (extSum thesisType2 ⟨0, by decide⟩ - extSum thesisType2 ⟨1, by decide⟩)) =
      24 * phi.eval certF6 - 4 * phi.eval sdpF7
        - 4 * phi.eval flag15 - 2 * phi.eval sdpF20
        - 2 * phi.eval flag25 - 12 * phi.eval sdpF30
        - 6 * phi.eval flag34 := by
    have hsub : (extSum thesisType2 ⟨0, by decide⟩
        - extSum thesisType2 ⟨1, by decide⟩ : GenFlagAlg CG2 thesisType2) =
        extSum thesisType2 ⟨0, by decide⟩
        + (-1 : ℝ) • extSum thesisType2 ⟨1, by decide⟩ := by
      rw [neg_one_smul]; abel
    rw [hsub, genAveragingAlg_add, genAveragingAlg_smul,
        phi.evalAlg_add, phi.evalAlg_smul,
        phi_eval_v0_side_t2 phi, phi_eval_v1_side_t2 phi]
    ring
  exact sigma_nonneg_template_perfunc_weakened thesisType2 thesisType2_isLocalType
    ⟨0, by decide⟩ ⟨1, by decide⟩ phi hreg h_loz_a h_loz_b
    h_sigma_pos_ab h_sigma_pos_ba _ h_combo

/-! ### σ₃-4-E.7: master sum infrastructure for thesisType3

mk_mem ×6, two witnessSets ({v0_a, v0_b}, {v1_a, v1_b, v1_c, v1_d}),
mem_witnessSet ×6, two master sums (v0-side, v1-side). -/

set_option maxHeartbeats 800000 in
private theorem t3_v0_a_mk_mem_genClassesOfSize :
    GenFlagClass.mk t3_v0_a ∈
      genClassesOfSize CG2 thesisType3 (thesisType3.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t3_v0_a.str, t3_v0_a.embedding, t3_v0_a.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t3_v0_b_mk_mem_genClassesOfSize :
    GenFlagClass.mk t3_v0_b ∈
      genClassesOfSize CG2 thesisType3 (thesisType3.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t3_v0_b.str, t3_v0_b.embedding, t3_v0_b.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t3_v1_a_mk_mem_genClassesOfSize :
    GenFlagClass.mk t3_v1_a ∈
      genClassesOfSize CG2 thesisType3 (thesisType3.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t3_v1_a.str, t3_v1_a.embedding, t3_v1_a.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t3_v1_b_mk_mem_genClassesOfSize :
    GenFlagClass.mk t3_v1_b ∈
      genClassesOfSize CG2 thesisType3 (thesisType3.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t3_v1_b.str, t3_v1_b.embedding, t3_v1_b.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t3_v1_c_mk_mem_genClassesOfSize :
    GenFlagClass.mk t3_v1_c ∈
      genClassesOfSize CG2 thesisType3 (thesisType3.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t3_v1_c.str, t3_v1_c.embedding, t3_v1_c.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t3_v1_d_mk_mem_genClassesOfSize :
    GenFlagClass.mk t3_v1_d ∈
      genClassesOfSize CG2 thesisType3 (thesisType3.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t3_v1_d.str, t3_v1_d.embedding, t3_v1_d.isInduced⟩, rfl⟩

/-- 2-element v0-side σ₃ witness set. -/
private noncomputable def t3_v0_witnessSet : Finset (GenFlagClass CG2 thesisType3) :=
  {GenFlagClass.mk t3_v0_a, GenFlagClass.mk t3_v0_b}

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t3_v0_a_mem_witnessSet :
    GenFlagClass.mk t3_v0_a ∈ t3_v0_witnessSet := by
  unfold t3_v0_witnessSet
  exact Finset.mem_insert_self _ _

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t3_v0_b_mem_witnessSet :
    GenFlagClass.mk t3_v0_b ∈ t3_v0_witnessSet := by
  unfold t3_v0_witnessSet
  rw [Finset.mem_insert, Finset.mem_singleton]
  right; rfl

/-- 4-element v1-side σ₃ witness set. -/
private noncomputable def t3_v1_witnessSet : Finset (GenFlagClass CG2 thesisType3) :=
  {GenFlagClass.mk t3_v1_a, GenFlagClass.mk t3_v1_b,
   GenFlagClass.mk t3_v1_c, GenFlagClass.mk t3_v1_d}

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t3_v1_a_mem_witnessSet :
    GenFlagClass.mk t3_v1_a ∈ t3_v1_witnessSet := by
  unfold t3_v1_witnessSet
  exact Finset.mem_insert_self _ _

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t3_v1_b_mem_witnessSet :
    GenFlagClass.mk t3_v1_b ∈ t3_v1_witnessSet := by
  unfold t3_v1_witnessSet
  rw [Finset.mem_insert]
  right; rw [Finset.mem_insert]; left; rfl

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t3_v1_c_mem_witnessSet :
    GenFlagClass.mk t3_v1_c ∈ t3_v1_witnessSet := by
  unfold t3_v1_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert]
  right; right; rw [Finset.mem_insert]; left; rfl

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t3_v1_d_mem_witnessSet :
    GenFlagClass.mk t3_v1_d ∈ t3_v1_witnessSet := by
  unfold t3_v1_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton]
  right; right; right; rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
/-- v0-side master sum for σ₃. -/
private theorem phi_eval_v0_side_t3
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (genAveragingAlg thesisType3 (extSum thesisType3 ⟨0, by decide⟩)) =
    2 / 120 * phi.eval flag25 + 2 / 120 * phi.eval flag15 := by
  classical
  rw [evalAlg_genAveragingAlg_expand, extSum_support_eq]
  have h_outside_zero :=
    t3_v0_extSum_outside_witnessSet_zero phi t3_v0_witnessSet
      t3_v0_a_mem_witnessSet t3_v0_b_mem_witnessSet
  have h_sub : t3_v0_witnessSet ⊆
      (genClassesOfSize CG2 thesisType3 (thesisType3.size + 1) (Nat.le_succ _)).filter
        (fun cls => extAdjacencyClass thesisType3 cls ⟨0, by decide⟩) := by
    intro cls hcls
    unfold t3_v0_witnessSet at hcls
    rw [Finset.mem_filter]
    rw [Finset.mem_insert, Finset.mem_singleton] at hcls
    rcases hcls with h | h
    all_goals refine ⟨?_, ?_⟩ <;> rw [h]
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t3_v0_a.str, t3_v0_a.embedding, t3_v0_a.isInduced⟩, rfl⟩
    · exact t3_v0_a_extAdj_v0
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t3_v0_b.str, t3_v0_b.embedding, t3_v0_b.isInduced⟩, rfl⟩
    · exact t3_v0_b_extAdj_v0
  rw [← Finset.sum_subset h_sub h_outside_zero]
  have h_a_notin : (GenFlagClass.mk t3_v0_a : GenFlagClass CG2 thesisType3) ∉
      ({GenFlagClass.mk t3_v0_b} : Finset _) := by
    rw [Finset.mem_singleton]
    exact mk_t3_v0_a_ne_mk_t3_v0_b
  unfold t3_v0_witnessSet
  rw [Finset.sum_insert h_a_notin, Finset.sum_singleton]
  rw [sigma3_witness_contribution_v0_a phi, sigma3_witness_contribution_v0_b phi]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
/-- v1-side master sum for σ₃. 4 witnesses. -/
private theorem phi_eval_v1_side_t3
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (genAveragingAlg thesisType3 (extSum thesisType3 ⟨1, by decide⟩)) =
    2 / 120 * phi.eval flag24 + 1 / 120 * phi.eval flag12 +
      1 / 120 * phi.eval certF22 + 2 / 120 * phi.eval certF11 := by
  classical
  rw [evalAlg_genAveragingAlg_expand, extSum_support_eq]
  have h_outside_zero :=
    t3_v1_extSum_outside_witnessSet_zero phi t3_v1_witnessSet
      t3_v1_a_mem_witnessSet t3_v1_b_mem_witnessSet
      t3_v1_c_mem_witnessSet t3_v1_d_mem_witnessSet
  have h_sub : t3_v1_witnessSet ⊆
      (genClassesOfSize CG2 thesisType3 (thesisType3.size + 1) (Nat.le_succ _)).filter
        (fun cls => extAdjacencyClass thesisType3 cls ⟨1, by decide⟩) := by
    intro cls hcls
    unfold t3_v1_witnessSet at hcls
    rw [Finset.mem_filter]
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton] at hcls
    rcases hcls with h | h | h | h
    all_goals refine ⟨?_, ?_⟩ <;> rw [h]
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t3_v1_a.str, t3_v1_a.embedding, t3_v1_a.isInduced⟩, rfl⟩
    · exact t3_v1_a_extAdj_v1
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t3_v1_b.str, t3_v1_b.embedding, t3_v1_b.isInduced⟩, rfl⟩
    · exact t3_v1_b_extAdj_v1
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t3_v1_c.str, t3_v1_c.embedding, t3_v1_c.isInduced⟩, rfl⟩
    · exact t3_v1_c_extAdj_v1
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t3_v1_d.str, t3_v1_d.embedding, t3_v1_d.isInduced⟩, rfl⟩
    · exact t3_v1_d_extAdj_v1
  rw [← Finset.sum_subset h_sub h_outside_zero]
  have h_a_notin : (GenFlagClass.mk t3_v1_a : GenFlagClass CG2 thesisType3) ∉
      ({GenFlagClass.mk t3_v1_b, GenFlagClass.mk t3_v1_c,
        GenFlagClass.mk t3_v1_d} : Finset _) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨mk_t3_v1_a_ne_mk_t3_v1_b, mk_t3_v1_a_ne_mk_t3_v1_c,
           mk_t3_v1_a_ne_mk_t3_v1_d⟩
  have h_b_notin : (GenFlagClass.mk t3_v1_b : GenFlagClass CG2 thesisType3) ∉
      ({GenFlagClass.mk t3_v1_c, GenFlagClass.mk t3_v1_d} : Finset _) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨mk_t3_v1_b_ne_mk_t3_v1_c, mk_t3_v1_b_ne_mk_t3_v1_d⟩
  have h_c_notin : (GenFlagClass.mk t3_v1_c : GenFlagClass CG2 thesisType3) ∉
      ({GenFlagClass.mk t3_v1_d} : Finset _) := by
    rw [Finset.mem_singleton]
    exact mk_t3_v1_c_ne_mk_t3_v1_d
  unfold t3_v1_witnessSet
  rw [Finset.sum_insert h_a_notin, Finset.sum_insert h_b_notin,
      Finset.sum_insert h_c_notin, Finset.sum_singleton]
  rw [sigma3_witness_contribution_v1_a phi, sigma3_witness_contribution_v1_b phi,
      sigma3_witness_contribution_v1_c phi, sigma3_witness_contribution_v1_d phi]
  ring

/-- **σ₃ nonnegativity** (thesis §3.6, Lemma 3.10 case σ₃):
    The extension ordering at `thesisType3` evaluates nonneg.

    Cert pair `(a, b) = (⟨1, _⟩, ⟨0, _⟩)` (v1 minus v0); cert RHS
    [2F₁₁, F₁₂, -2F₁₅, F₂₂, 2F₂₄, -2F₂₅] from sig3x2 / 2.

    Proof via `Extensions.sigma_nonneg_template_perfunc_weakened`:
    - locality: `t3_v0/v1_extAdj_filter_local_or_zero` (BRRB always local).
    - σ-positivity: `extSum_diff_psi_eq_zero` (regular ⇒ all ext-diffs are 0).
    - combinatorial identity: `120 · phi.evalAlg (genAveragingAlg σ₃ (ext_v1 - ext_v0)) = RHS`,
      via `phi_eval_v0/v1_side_t3` master sums + `ring`. -/
theorem sigma3_nonneg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget) :
    0 ≤ 2 * phi.eval certF11 + phi.eval flag12
      - 2 * phi.eval flag15 + phi.eval certF22
      + 2 * phi.eval flag24 - 2 * phi.eval flag25 := by
  have h_loz_a := t3_v1_extAdj_filter_local_or_zero phi
  have h_loz_b := t3_v0_extAdj_filter_local_or_zero phi
  have h_sigma_pos_ab : ∀ ψ : GenLimitFunctional CG2 thesisType3
        brrbGenGraphClass brrbGenDelta,
      (∀ k, ∀ u : Fin (ψ.seq.seq k).size,
        (Finset.univ.filter ((ψ.seq.seq k).str.1.Adj u)).card =
          brrbGenDelta (ψ.seq.seq k).forget) →
      0 ≤ ψ.evalAlg (extSum thesisType3 ⟨1, by decide⟩
        - extSum thesisType3 ⟨0, by decide⟩) := by
    intro ψ h_reg
    have h := extSum_diff_psi_eq_zero thesisType3 ⟨1, by decide⟩ ⟨0, by decide⟩ ψ h_reg
    rw [h]
  have h_sigma_pos_ba : ∀ ψ : GenLimitFunctional CG2 thesisType3
        brrbGenGraphClass brrbGenDelta,
      (∀ k, ∀ u : Fin (ψ.seq.seq k).size,
        (Finset.univ.filter ((ψ.seq.seq k).str.1.Adj u)).card =
          brrbGenDelta (ψ.seq.seq k).forget) →
      0 ≤ ψ.evalAlg (extSum thesisType3 ⟨0, by decide⟩
        - extSum thesisType3 ⟨1, by decide⟩) := by
    intro ψ h_reg
    have h := extSum_diff_psi_eq_zero thesisType3 ⟨1, by decide⟩ ⟨0, by decide⟩ ψ h_reg
    have hflip : (extSum thesisType3 ⟨0, by decide⟩
        - extSum thesisType3 ⟨1, by decide⟩ : GenFlagAlg CG2 thesisType3) =
        (-1 : ℝ) • (extSum thesisType3 ⟨1, by decide⟩
        - extSum thesisType3 ⟨0, by decide⟩) := by
      rw [neg_smul, one_smul]; abel
    rw [hflip, ψ.evalAlg_smul, h, mul_zero]
  have h_combo : 120 * phi.evalAlg (genAveragingAlg thesisType3
      (extSum thesisType3 ⟨1, by decide⟩ - extSum thesisType3 ⟨0, by decide⟩)) =
      2 * phi.eval certF11 + phi.eval flag12
        - 2 * phi.eval flag15 + phi.eval certF22
        + 2 * phi.eval flag24 - 2 * phi.eval flag25 := by
    have hsub : (extSum thesisType3 ⟨1, by decide⟩
        - extSum thesisType3 ⟨0, by decide⟩ : GenFlagAlg CG2 thesisType3) =
        extSum thesisType3 ⟨1, by decide⟩
        + (-1 : ℝ) • extSum thesisType3 ⟨0, by decide⟩ := by
      rw [neg_one_smul]; abel
    rw [hsub, genAveragingAlg_add, genAveragingAlg_smul,
        phi.evalAlg_add, phi.evalAlg_smul,
        phi_eval_v1_side_t3 phi, phi_eval_v0_side_t3 phi]
    ring
  exact sigma_nonneg_template_perfunc_weakened thesisType3 thesisType3_isLocalType
    ⟨1, by decide⟩ ⟨0, by decide⟩ phi hreg h_loz_a h_loz_b
    h_sigma_pos_ab h_sigma_pos_ba _ h_combo

/-! ### σ₄-4-E.7: master sum infrastructure for thesisType4

mk_mem ×6, two witnessSets ({v0_a, v0_b}, {v1_a, v1_b, v1_c, v1_d}),
mem_witnessSet ×6, two master sums (v0-side, v1-side). -/

set_option maxHeartbeats 800000 in
private theorem t4_v0_a_mk_mem_genClassesOfSize :
    GenFlagClass.mk t4_v0_a ∈
      genClassesOfSize CG2 thesisType4 (thesisType4.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t4_v0_a.str, t4_v0_a.embedding, t4_v0_a.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t4_v0_b_mk_mem_genClassesOfSize :
    GenFlagClass.mk t4_v0_b ∈
      genClassesOfSize CG2 thesisType4 (thesisType4.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t4_v0_b.str, t4_v0_b.embedding, t4_v0_b.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t4_v1_a_mk_mem_genClassesOfSize :
    GenFlagClass.mk t4_v1_a ∈
      genClassesOfSize CG2 thesisType4 (thesisType4.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t4_v1_a.str, t4_v1_a.embedding, t4_v1_a.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t4_v1_b_mk_mem_genClassesOfSize :
    GenFlagClass.mk t4_v1_b ∈
      genClassesOfSize CG2 thesisType4 (thesisType4.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t4_v1_b.str, t4_v1_b.embedding, t4_v1_b.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t4_v1_c_mk_mem_genClassesOfSize :
    GenFlagClass.mk t4_v1_c ∈
      genClassesOfSize CG2 thesisType4 (thesisType4.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t4_v1_c.str, t4_v1_c.embedding, t4_v1_c.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t4_v1_d_mk_mem_genClassesOfSize :
    GenFlagClass.mk t4_v1_d ∈
      genClassesOfSize CG2 thesisType4 (thesisType4.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t4_v1_d.str, t4_v1_d.embedding, t4_v1_d.isInduced⟩, rfl⟩

/-- 2-element v0-side σ₄ witness set. -/
private noncomputable def t4_v0_witnessSet : Finset (GenFlagClass CG2 thesisType4) :=
  {GenFlagClass.mk t4_v0_a, GenFlagClass.mk t4_v0_b}

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t4_v0_a_mem_witnessSet :
    GenFlagClass.mk t4_v0_a ∈ t4_v0_witnessSet := by
  unfold t4_v0_witnessSet
  exact Finset.mem_insert_self _ _

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t4_v0_b_mem_witnessSet :
    GenFlagClass.mk t4_v0_b ∈ t4_v0_witnessSet := by
  unfold t4_v0_witnessSet
  rw [Finset.mem_insert, Finset.mem_singleton]
  right; rfl

/-- 4-element v1-side σ₄ witness set. -/
private noncomputable def t4_v1_witnessSet : Finset (GenFlagClass CG2 thesisType4) :=
  {GenFlagClass.mk t4_v1_a, GenFlagClass.mk t4_v1_b,
   GenFlagClass.mk t4_v1_c, GenFlagClass.mk t4_v1_d}

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t4_v1_a_mem_witnessSet :
    GenFlagClass.mk t4_v1_a ∈ t4_v1_witnessSet := by
  unfold t4_v1_witnessSet
  exact Finset.mem_insert_self _ _

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t4_v1_b_mem_witnessSet :
    GenFlagClass.mk t4_v1_b ∈ t4_v1_witnessSet := by
  unfold t4_v1_witnessSet
  rw [Finset.mem_insert]
  right; rw [Finset.mem_insert]; left; rfl

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t4_v1_c_mem_witnessSet :
    GenFlagClass.mk t4_v1_c ∈ t4_v1_witnessSet := by
  unfold t4_v1_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert]
  right; right; rw [Finset.mem_insert]; left; rfl

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t4_v1_d_mem_witnessSet :
    GenFlagClass.mk t4_v1_d ∈ t4_v1_witnessSet := by
  unfold t4_v1_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton]
  right; right; right; rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
/-- v0-side master sum for σ₄. -/
private theorem phi_eval_v0_side_t4
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (genAveragingAlg thesisType4 (extSum thesisType4 ⟨0, by decide⟩)) =
    2 / 120 * phi.eval flag15 + 6 / 120 * phi.eval flag34 := by
  classical
  rw [evalAlg_genAveragingAlg_expand, extSum_support_eq]
  have h_outside_zero :=
    t4_v0_extSum_outside_witnessSet_zero phi t4_v0_witnessSet
      t4_v0_a_mem_witnessSet t4_v0_b_mem_witnessSet
  have h_sub : t4_v0_witnessSet ⊆
      (genClassesOfSize CG2 thesisType4 (thesisType4.size + 1) (Nat.le_succ _)).filter
        (fun cls => extAdjacencyClass thesisType4 cls ⟨0, by decide⟩) := by
    intro cls hcls
    unfold t4_v0_witnessSet at hcls
    rw [Finset.mem_filter]
    rw [Finset.mem_insert, Finset.mem_singleton] at hcls
    rcases hcls with h | h
    all_goals refine ⟨?_, ?_⟩ <;> rw [h]
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t4_v0_a.str, t4_v0_a.embedding, t4_v0_a.isInduced⟩, rfl⟩
    · exact t4_v0_a_extAdj_v0
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t4_v0_b.str, t4_v0_b.embedding, t4_v0_b.isInduced⟩, rfl⟩
    · exact t4_v0_b_extAdj_v0
  rw [← Finset.sum_subset h_sub h_outside_zero]
  have h_a_notin : (GenFlagClass.mk t4_v0_a : GenFlagClass CG2 thesisType4) ∉
      ({GenFlagClass.mk t4_v0_b} : Finset _) := by
    rw [Finset.mem_singleton]
    exact mk_t4_v0_a_ne_mk_t4_v0_b
  unfold t4_v0_witnessSet
  rw [Finset.sum_insert h_a_notin, Finset.sum_singleton]
  rw [sigma4_witness_contribution_v0_a phi, sigma4_witness_contribution_v0_b phi]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
/-- v1-side master sum for σ₄. 4 witnesses. -/
private theorem phi_eval_v1_side_t4
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (genAveragingAlg thesisType4 (extSum thesisType4 ⟨1, by decide⟩)) =
    1 / 120 * phi.eval flag12 + 4 / 120 * phi.eval flag32 +
      1 / 120 * phi.eval certF8 + 4 / 120 * phi.eval certF31 := by
  classical
  rw [evalAlg_genAveragingAlg_expand, extSum_support_eq]
  have h_outside_zero :=
    t4_v1_extSum_outside_witnessSet_zero phi t4_v1_witnessSet
      t4_v1_a_mem_witnessSet t4_v1_b_mem_witnessSet
      t4_v1_c_mem_witnessSet t4_v1_d_mem_witnessSet
  have h_sub : t4_v1_witnessSet ⊆
      (genClassesOfSize CG2 thesisType4 (thesisType4.size + 1) (Nat.le_succ _)).filter
        (fun cls => extAdjacencyClass thesisType4 cls ⟨1, by decide⟩) := by
    intro cls hcls
    unfold t4_v1_witnessSet at hcls
    rw [Finset.mem_filter]
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton] at hcls
    rcases hcls with h | h | h | h
    all_goals refine ⟨?_, ?_⟩ <;> rw [h]
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t4_v1_a.str, t4_v1_a.embedding, t4_v1_a.isInduced⟩, rfl⟩
    · exact t4_v1_a_extAdj_v1
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t4_v1_b.str, t4_v1_b.embedding, t4_v1_b.isInduced⟩, rfl⟩
    · exact t4_v1_b_extAdj_v1
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t4_v1_c.str, t4_v1_c.embedding, t4_v1_c.isInduced⟩, rfl⟩
    · exact t4_v1_c_extAdj_v1
    · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨t4_v1_d.str, t4_v1_d.embedding, t4_v1_d.isInduced⟩, rfl⟩
    · exact t4_v1_d_extAdj_v1
  rw [← Finset.sum_subset h_sub h_outside_zero]
  have h_a_notin : (GenFlagClass.mk t4_v1_a : GenFlagClass CG2 thesisType4) ∉
      ({GenFlagClass.mk t4_v1_b, GenFlagClass.mk t4_v1_c,
        GenFlagClass.mk t4_v1_d} : Finset _) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨mk_t4_v1_a_ne_mk_t4_v1_b, mk_t4_v1_a_ne_mk_t4_v1_c,
           mk_t4_v1_a_ne_mk_t4_v1_d⟩
  have h_b_notin : (GenFlagClass.mk t4_v1_b : GenFlagClass CG2 thesisType4) ∉
      ({GenFlagClass.mk t4_v1_c, GenFlagClass.mk t4_v1_d} : Finset _) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨mk_t4_v1_b_ne_mk_t4_v1_c, mk_t4_v1_b_ne_mk_t4_v1_d⟩
  have h_c_notin : (GenFlagClass.mk t4_v1_c : GenFlagClass CG2 thesisType4) ∉
      ({GenFlagClass.mk t4_v1_d} : Finset _) := by
    rw [Finset.mem_singleton]
    exact mk_t4_v1_c_ne_mk_t4_v1_d
  unfold t4_v1_witnessSet
  rw [Finset.sum_insert h_a_notin, Finset.sum_insert h_b_notin,
      Finset.sum_insert h_c_notin, Finset.sum_singleton]
  rw [sigma4_witness_contribution_v1_a phi, sigma4_witness_contribution_v1_b phi,
      sigma4_witness_contribution_v1_c phi, sigma4_witness_contribution_v1_d phi]
  ring

/-- **σ₄ nonnegativity** (thesis §3.6, Lemma 3.10 case σ₄):
    Cert pair (a, b) = (⟨1, _⟩, ⟨0, _⟩); cert RHS
    [F₈, F₁₂, -2F₁₅, 4F₃₁, 4F₃₂, -6F₃₄]. -/
theorem sigma4_nonneg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget) :
    0 ≤ phi.eval certF8 + phi.eval flag12
      - 2 * phi.eval flag15 + 4 * phi.eval certF31
      + 4 * phi.eval flag32 - 6 * phi.eval flag34 := by
  have h_loz_a := t4_v1_extAdj_filter_local_or_zero phi
  have h_loz_b := t4_v0_extAdj_filter_local_or_zero phi
  have h_sigma_pos_ab : ∀ ψ : GenLimitFunctional CG2 thesisType4
        brrbGenGraphClass brrbGenDelta,
      (∀ k, ∀ u : Fin (ψ.seq.seq k).size,
        (Finset.univ.filter ((ψ.seq.seq k).str.1.Adj u)).card =
          brrbGenDelta (ψ.seq.seq k).forget) →
      0 ≤ ψ.evalAlg (extSum thesisType4 ⟨1, by decide⟩
        - extSum thesisType4 ⟨0, by decide⟩) := by
    intro ψ h_reg
    have h := extSum_diff_psi_eq_zero thesisType4 ⟨1, by decide⟩ ⟨0, by decide⟩ ψ h_reg
    rw [h]
  have h_sigma_pos_ba : ∀ ψ : GenLimitFunctional CG2 thesisType4
        brrbGenGraphClass brrbGenDelta,
      (∀ k, ∀ u : Fin (ψ.seq.seq k).size,
        (Finset.univ.filter ((ψ.seq.seq k).str.1.Adj u)).card =
          brrbGenDelta (ψ.seq.seq k).forget) →
      0 ≤ ψ.evalAlg (extSum thesisType4 ⟨0, by decide⟩
        - extSum thesisType4 ⟨1, by decide⟩) := by
    intro ψ h_reg
    have h := extSum_diff_psi_eq_zero thesisType4 ⟨1, by decide⟩ ⟨0, by decide⟩ ψ h_reg
    have hflip : (extSum thesisType4 ⟨0, by decide⟩
        - extSum thesisType4 ⟨1, by decide⟩ : GenFlagAlg CG2 thesisType4) =
        (-1 : ℝ) • (extSum thesisType4 ⟨1, by decide⟩
        - extSum thesisType4 ⟨0, by decide⟩) := by
      rw [neg_smul, one_smul]; abel
    rw [hflip, ψ.evalAlg_smul, h, mul_zero]
  have h_combo : 120 * phi.evalAlg (genAveragingAlg thesisType4
      (extSum thesisType4 ⟨1, by decide⟩ - extSum thesisType4 ⟨0, by decide⟩)) =
      phi.eval certF8 + phi.eval flag12
        - 2 * phi.eval flag15 + 4 * phi.eval certF31
        + 4 * phi.eval flag32 - 6 * phi.eval flag34 := by
    have hsub : (extSum thesisType4 ⟨1, by decide⟩
        - extSum thesisType4 ⟨0, by decide⟩ : GenFlagAlg CG2 thesisType4) =
        extSum thesisType4 ⟨1, by decide⟩
        + (-1 : ℝ) • extSum thesisType4 ⟨0, by decide⟩ := by
      rw [neg_one_smul]; abel
    rw [hsub, genAveragingAlg_add, genAveragingAlg_smul,
        phi.evalAlg_add, phi.evalAlg_smul,
        phi_eval_v1_side_t4 phi, phi_eval_v0_side_t4 phi]
    ring
  exact sigma_nonneg_template_perfunc_weakened thesisType4 thesisType4_isLocalType
    ⟨1, by decide⟩ ⟨0, by decide⟩ phi hreg h_loz_a h_loz_b
    h_sigma_pos_ab h_sigma_pos_ba _ h_combo

/-! ### σ₅ nonnegativity infrastructure

Cert pair (a, b) = (⟨2, _⟩, ⟨0, _⟩) — v2=B endpoint vs v0=R internal.
Cert: `[-2F₁₆, -F₁₇, F₃₇, 2F₅₅]` matches the 4 non-cancelling witnesses;
the cancelling pair `t5_v2_b ↔ t5_v0_R_b` cancels in `sigma5_nonneg`'s
combo via subtraction. -/

set_option maxHeartbeats 800000 in
private theorem t5_v2_a_mk_mem_genClassesOfSize :
    GenFlagClass.mk t5_v2_a ∈
      genClassesOfSize CG2 thesisType5 (thesisType5.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t5_v2_a.str, t5_v2_a.embedding, t5_v2_a.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t5_v2_b_mk_mem_genClassesOfSize :
    GenFlagClass.mk t5_v2_b ∈
      genClassesOfSize CG2 thesisType5 (thesisType5.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t5_v2_b.str, t5_v2_b.embedding, t5_v2_b.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t5_v2_c_mk_mem_genClassesOfSize :
    GenFlagClass.mk t5_v2_c ∈
      genClassesOfSize CG2 thesisType5 (thesisType5.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t5_v2_c.str, t5_v2_c.embedding, t5_v2_c.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t5_v0_R_a_mk_mem_genClassesOfSize :
    GenFlagClass.mk t5_v0_R_a ∈
      genClassesOfSize CG2 thesisType5 (thesisType5.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t5_v0_R_a.str, t5_v0_R_a.embedding, t5_v0_R_a.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t5_v0_R_b_mk_mem_genClassesOfSize :
    GenFlagClass.mk t5_v0_R_b ∈
      genClassesOfSize CG2 thesisType5 (thesisType5.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t5_v0_R_b.str, t5_v0_R_b.embedding, t5_v0_R_b.isInduced⟩, rfl⟩

set_option maxHeartbeats 800000 in
private theorem t5_v0_B_mk_mem_genClassesOfSize :
    GenFlagClass.mk t5_v0_B ∈
      genClassesOfSize CG2 thesisType5 (thesisType5.size + 1) (Nat.le_succ _) := by
  simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨t5_v0_B.str, t5_v0_B.embedding, t5_v0_B.isInduced⟩, rfl⟩

/-- The 3-element v2-side σ₅ witness set. -/
private noncomputable def t5_v2_witnessSet : Finset (GenFlagClass CG2 thesisType5) :=
  {GenFlagClass.mk t5_v2_a, GenFlagClass.mk t5_v2_b, GenFlagClass.mk t5_v2_c}

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t5_v2_a_mem_witnessSet :
    GenFlagClass.mk t5_v2_a ∈ t5_v2_witnessSet := by
  unfold t5_v2_witnessSet
  exact Finset.mem_insert_self _ _

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t5_v2_b_mem_witnessSet :
    GenFlagClass.mk t5_v2_b ∈ t5_v2_witnessSet := by
  unfold t5_v2_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert]
  exact Or.inr (Or.inl rfl)

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t5_v2_c_mem_witnessSet :
    GenFlagClass.mk t5_v2_c ∈ t5_v2_witnessSet := by
  unfold t5_v2_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr rfl)

/-- The 3-element v0-side σ₅ witness set. -/
private noncomputable def t5_v0_witnessSet : Finset (GenFlagClass CG2 thesisType5) :=
  {GenFlagClass.mk t5_v0_R_a, GenFlagClass.mk t5_v0_R_b, GenFlagClass.mk t5_v0_B}

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t5_v0_R_a_mem_witnessSet :
    GenFlagClass.mk t5_v0_R_a ∈ t5_v0_witnessSet := by
  unfold t5_v0_witnessSet
  exact Finset.mem_insert_self _ _

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t5_v0_R_b_mem_witnessSet :
    GenFlagClass.mk t5_v0_R_b ∈ t5_v0_witnessSet := by
  unfold t5_v0_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert]
  exact Or.inr (Or.inl rfl)

set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
private theorem t5_v0_B_mem_witnessSet :
    GenFlagClass.mk t5_v0_B ∈ t5_v0_witnessSet := by
  unfold t5_v0_witnessSet
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  exact Or.inr (Or.inr rfl)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
/-- v2-side master sum for σ₅. -/
private theorem phi_eval_v2_side_t5
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (genAveragingAlg thesisType5 (extSum thesisType5 ⟨2, by decide⟩)) =
    1 / 120 * phi.eval sdpFlag37 +
      (genFlagAutCount CG2 (GenFlagType.empty CG2) t5_v0_R_b.forget : ℝ) / 120 *
        phi.eval t5_v0_R_b.forget +
      2 / 120 * phi.eval sdpFlag55 := by
  classical
  rw [evalAlg_genAveragingAlg_expand, extSum_support_eq]
  have h_outside_zero :=
    t5_v2_extSum_outside_witnessSet_zero phi t5_v2_witnessSet
      t5_v2_a_mem_witnessSet t5_v2_b_mem_witnessSet t5_v2_c_mem_witnessSet
  have h_sub : t5_v2_witnessSet ⊆
      (genClassesOfSize CG2 thesisType5 (thesisType5.size + 1) (Nat.le_succ _)).filter
        (fun cls => extAdjacencyClass thesisType5 cls ⟨2, by decide⟩) := by
    intro cls hcls
    unfold t5_v2_witnessSet at hcls
    rw [Finset.mem_filter]
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hcls
    rcases hcls with h | h | h
    · refine ⟨?_, ?_⟩ <;> rw [h]
      · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨t5_v2_a.str, t5_v2_a.embedding, t5_v2_a.isInduced⟩, rfl⟩
      · exact t5_v2_a_extAdj_v2
    · refine ⟨?_, ?_⟩ <;> rw [h]
      · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨t5_v2_b.str, t5_v2_b.embedding, t5_v2_b.isInduced⟩, rfl⟩
      · exact t5_v2_b_extAdj_v2
    · refine ⟨?_, ?_⟩ <;> rw [h]
      · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨t5_v2_c.str, t5_v2_c.embedding, t5_v2_c.isInduced⟩, rfl⟩
      · exact t5_v2_c_extAdj_v2
  rw [← Finset.sum_subset h_sub h_outside_zero]
  have h_ab : (GenFlagClass.mk t5_v2_a : GenFlagClass CG2 thesisType5) ∉
      ({GenFlagClass.mk t5_v2_b, GenFlagClass.mk t5_v2_c} : Finset _) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨mk_t5_v2_a_ne_mk_t5_v2_b, mk_t5_v2_a_ne_mk_t5_v2_c⟩
  have h_bc : (GenFlagClass.mk t5_v2_b : GenFlagClass CG2 thesisType5) ∉
      ({GenFlagClass.mk t5_v2_c} : Finset _) := by
    rw [Finset.mem_singleton]
    exact mk_t5_v2_b_ne_mk_t5_v2_c
  unfold t5_v2_witnessSet
  rw [Finset.sum_insert h_ab, Finset.sum_insert h_bc, Finset.sum_singleton]
  rw [sigma5_witness_contribution_v2_a phi, sigma5_witness_contribution_v2_b phi,
      sigma5_witness_contribution_v2_c phi]
  ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 10000 in
set_option linter.constructorNameAsVariable false in
/-- v0-side master sum for σ₅. -/
private theorem phi_eval_v0_side_t5
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg (genAveragingAlg thesisType5 (extSum thesisType5 ⟨0, by decide⟩)) =
    1 / 120 * phi.eval flag17 +
      (genFlagAutCount CG2 (GenFlagType.empty CG2) t5_v0_R_b.forget : ℝ) / 120 *
        phi.eval t5_v0_R_b.forget +
      2 / 120 * phi.eval flag16 := by
  classical
  rw [evalAlg_genAveragingAlg_expand, extSum_support_eq]
  have h_outside_zero :=
    t5_v0_extSum_outside_witnessSet_zero phi t5_v0_witnessSet
      t5_v0_R_a_mem_witnessSet t5_v0_R_b_mem_witnessSet t5_v0_B_mem_witnessSet
  have h_sub : t5_v0_witnessSet ⊆
      (genClassesOfSize CG2 thesisType5 (thesisType5.size + 1) (Nat.le_succ _)).filter
        (fun cls => extAdjacencyClass thesisType5 cls ⟨0, by decide⟩) := by
    intro cls hcls
    unfold t5_v0_witnessSet at hcls
    rw [Finset.mem_filter]
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hcls
    rcases hcls with h | h | h
    · refine ⟨?_, ?_⟩ <;> rw [h]
      · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨t5_v0_R_a.str, t5_v0_R_a.embedding, t5_v0_R_a.isInduced⟩, rfl⟩
      · exact t5_v0_R_a_extAdj_v0
    · refine ⟨?_, ?_⟩ <;> rw [h]
      · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨t5_v0_R_b.str, t5_v0_R_b.embedding, t5_v0_R_b.isInduced⟩, rfl⟩
      · exact t5_v0_R_b_extAdj_v0
    · refine ⟨?_, ?_⟩ <;> rw [h]
      · simp only [genClassesOfSize, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨t5_v0_B.str, t5_v0_B.embedding, t5_v0_B.isInduced⟩, rfl⟩
      · exact t5_v0_B_extAdj_v0
  rw [← Finset.sum_subset h_sub h_outside_zero]
  have h_ab : (GenFlagClass.mk t5_v0_R_a : GenFlagClass CG2 thesisType5) ∉
      ({GenFlagClass.mk t5_v0_R_b, GenFlagClass.mk t5_v0_B} : Finset _) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    exact ⟨mk_t5_v0_R_a_ne_mk_t5_v0_R_b, mk_t5_v0_R_a_ne_mk_t5_v0_B⟩
  have h_bc : (GenFlagClass.mk t5_v0_R_b : GenFlagClass CG2 thesisType5) ∉
      ({GenFlagClass.mk t5_v0_B} : Finset _) := by
    rw [Finset.mem_singleton]
    exact mk_t5_v0_R_b_ne_mk_t5_v0_B
  unfold t5_v0_witnessSet
  rw [Finset.sum_insert h_ab, Finset.sum_insert h_bc, Finset.sum_singleton]
  rw [sigma5_witness_contribution_v0_R_a phi, sigma5_witness_contribution_v0_R_b phi,
      sigma5_witness_contribution_v0_B phi]
  ring

set_option maxHeartbeats 8000000 in
theorem sigma5_nonneg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget) :
    0 ≤ -2 * phi.eval flag16 - phi.eval flag17
      + phi.eval sdpFlag37 + 2 * phi.eval sdpFlag55 := by
  have h_loz_a := t5_v2_extAdj_filter_local_or_zero phi
  have h_loz_b := t5_v0_extAdj_filter_local_or_zero phi
  have h_sigma_pos_ab : ∀ ψ : GenLimitFunctional CG2 thesisType5
        brrbGenGraphClass brrbGenDelta,
      (∀ k, ∀ u : Fin (ψ.seq.seq k).size,
        (Finset.univ.filter ((ψ.seq.seq k).str.1.Adj u)).card =
          brrbGenDelta (ψ.seq.seq k).forget) →
      0 ≤ ψ.evalAlg (extSum thesisType5 ⟨2, by decide⟩
        - extSum thesisType5 ⟨0, by decide⟩) := by
    intro ψ h_reg
    rw [extSum_diff_psi_eq_zero thesisType5 ⟨2, by decide⟩ ⟨0, by decide⟩ ψ h_reg]
  have h_sigma_pos_ba : ∀ ψ : GenLimitFunctional CG2 thesisType5
        brrbGenGraphClass brrbGenDelta,
      (∀ k, ∀ u : Fin (ψ.seq.seq k).size,
        (Finset.univ.filter ((ψ.seq.seq k).str.1.Adj u)).card =
          brrbGenDelta (ψ.seq.seq k).forget) →
      0 ≤ ψ.evalAlg (extSum thesisType5 ⟨0, by decide⟩
        - extSum thesisType5 ⟨2, by decide⟩) := by
    intro ψ h_reg
    have h := extSum_diff_psi_eq_zero thesisType5 ⟨2, by decide⟩ ⟨0, by decide⟩ ψ h_reg
    have hflip : (extSum thesisType5 ⟨0, by decide⟩
        - extSum thesisType5 ⟨2, by decide⟩ : GenFlagAlg CG2 thesisType5) =
        (-1 : ℝ) • (extSum thesisType5 ⟨2, by decide⟩
        - extSum thesisType5 ⟨0, by decide⟩) := by
      rw [neg_smul, one_smul]; abel
    rw [hflip, ψ.evalAlg_smul, h, mul_zero]
  have h_combo : 120 * phi.evalAlg (genAveragingAlg thesisType5
      (extSum thesisType5 ⟨2, by decide⟩ - extSum thesisType5 ⟨0, by decide⟩)) =
      -2 * phi.eval flag16 - phi.eval flag17
        + phi.eval sdpFlag37 + 2 * phi.eval sdpFlag55 := by
    have hsub : (extSum thesisType5 ⟨2, by decide⟩
        - extSum thesisType5 ⟨0, by decide⟩ : GenFlagAlg CG2 thesisType5) =
        extSum thesisType5 ⟨2, by decide⟩
        + (-1 : ℝ) • extSum thesisType5 ⟨0, by decide⟩ := by
      rw [neg_one_smul]; abel
    rw [hsub, genAveragingAlg_add, genAveragingAlg_smul,
        phi.evalAlg_add, phi.evalAlg_smul,
        phi_eval_v2_side_t5 phi, phi_eval_v0_side_t5 phi]
    ring
  exact sigma_nonneg_template_perfunc_weakened thesisType5 thesisType5_isLocalType
    ⟨2, by decide⟩ ⟨0, by decide⟩ phi hreg h_loz_a h_loz_b
    h_sigma_pos_ab h_sigma_pos_ba _ h_combo

/-! ## Path 2: GenFlagAlg-level decomposition (Phase B)

Define algebra-level analogs of B₁ and each σᵢ as `GenFlagAlg` elements.
Each `sigmaᵢ_alg` is `120 · ⟦extSum_a − extSum_b⟧` matching the thesis cert.
`linSum_alg` is the structural decomposition target.

After this, `phi.evalAlg(sigmaᵢ_alg)` matches each `sigmaᵢ_nonneg` h_combo's RHS
by `evalAlg_smul + h_combo` (Phase C lemmas). Composition via `phi.evalAlg`'s
linearity gives `phi.evalAlg(linSum_alg) = RHS of linSum_decomposition_identity`. -/

/-- B₁ at the algebra level: `5·certF1 − certF6`. -/
noncomputable def b1_alg : GenFlagAlg CG2 (GenFlagType.empty CG2) :=
  (5 : ℝ) • Finsupp.single (GenFlagClass.mk certF1) (1 : ℝ)
    - Finsupp.single (GenFlagClass.mk certF6) (1 : ℝ)

/-- σ₁ at the algebra level: `120 · ⟦extSum_v1 − extSum_v0⟧` over thesisType1.
    Matches the cert pair `(a, b) = (⟨1, _⟩, ⟨0, _⟩)`. -/
noncomputable def sigma1_alg : GenFlagAlg CG2 (GenFlagType.empty CG2) :=
  (120 : ℝ) • genAveragingAlg thesisType1
    (extSum thesisType1 ⟨1, by decide⟩ - extSum thesisType1 ⟨0, by decide⟩)

/-- σ₂ at the algebra level: `120 · ⟦extSum_v0 − extSum_v1⟧` over thesisType2.
    Cert pair `(a, b) = (⟨0, _⟩, ⟨1, _⟩)`. -/
noncomputable def sigma2_alg : GenFlagAlg CG2 (GenFlagType.empty CG2) :=
  (120 : ℝ) • genAveragingAlg thesisType2
    (extSum thesisType2 ⟨0, by decide⟩ - extSum thesisType2 ⟨1, by decide⟩)

/-- σ₃ at the algebra level: `120 · ⟦extSum_v1 − extSum_v0⟧` over thesisType3. -/
noncomputable def sigma3_alg : GenFlagAlg CG2 (GenFlagType.empty CG2) :=
  (120 : ℝ) • genAveragingAlg thesisType3
    (extSum thesisType3 ⟨1, by decide⟩ - extSum thesisType3 ⟨0, by decide⟩)

/-- σ₄ at the algebra level: `120 · ⟦extSum_v1 − extSum_v0⟧` over thesisType4. -/
noncomputable def sigma4_alg : GenFlagAlg CG2 (GenFlagType.empty CG2) :=
  (120 : ℝ) • genAveragingAlg thesisType4
    (extSum thesisType4 ⟨1, by decide⟩ - extSum thesisType4 ⟨0, by decide⟩)

/-- σ₅ at the algebra level: `120 · ⟦extSum_v2 − extSum_v0⟧` over thesisType5. -/
noncomputable def sigma5_alg : GenFlagAlg CG2 (GenFlagType.empty CG2) :=
  (120 : ℝ) • genAveragingAlg thesisType5
    (extSum thesisType5 ⟨2, by decide⟩ - extSum thesisType5 ⟨0, by decide⟩)

/-- linSum at the algebra level (cert decomposition):
    `linSum_alg = 6·B₁_alg + σ₁_alg + ¼·σ₂_alg + σ₃_alg + σ₄_alg + 2·σ₅_alg`.

    Matches `BrrbCertificate.linSum_decomposition` at vector level. -/
noncomputable def linSum_alg : GenFlagAlg CG2 (GenFlagType.empty CG2) :=
  (6 : ℝ) • b1_alg + sigma1_alg + (1/4 : ℝ) • sigma2_alg
    + sigma3_alg + sigma4_alg + (2 : ℝ) • sigma5_alg

/-! ## Path 2: phi.evalAlg of each algebra-level component (Phase C)

Each `phi.evalAlg(sigmaᵢ_alg)` matches the σᵢ_nonneg goal RHS, derived
identically to each σᵢ_nonneg's `h_combo` (algebra-level decomposition
of `extSum_a − extSum_b` followed by the per-side master sum lemmas
`phi_eval_v*_side_t*` from σᵢ-4-E.7). -/

theorem phi_evalAlg_b1_alg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg b1_alg = 5 * phi.eval certF1 - phi.eval certF6 := by
  unfold b1_alg
  change phi.evalAlg ((5 : ℝ) • GenFlagAlg.single certF1
      - GenFlagAlg.single certF6) = _
  rw [show ((5 : ℝ) • GenFlagAlg.single certF1 - GenFlagAlg.single certF6 :
      GenFlagAlg CG2 (GenFlagType.empty CG2)) =
      (5 : ℝ) • GenFlagAlg.single certF1
        + (-1 : ℝ) • GenFlagAlg.single certF6 from by
    rw [neg_one_smul]; abel]
  rw [phi.evalAlg_add, phi.evalAlg_smul, phi.evalAlg_smul,
      phi.evalAlg_single, phi.evalAlg_single]
  ring

set_option maxHeartbeats 8000000 in
theorem phi_evalAlg_sigma1_alg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg sigma1_alg =
      -4 * phi.eval certF4 - 6 * phi.eval flag5
      + 2 * phi.eval flag12 + 2 * phi.eval flag24
      + 4 * phi.eval flag32 := by
  unfold sigma1_alg
  rw [phi.evalAlg_smul]
  have hsub : (extSum thesisType1 ⟨1, by decide⟩
      - extSum thesisType1 ⟨0, by decide⟩ : GenFlagAlg CG2 thesisType1) =
      extSum thesisType1 ⟨1, by decide⟩
      + (-1 : ℝ) • extSum thesisType1 ⟨0, by decide⟩ := by
    rw [neg_one_smul]; abel
  rw [hsub, genAveragingAlg_add, genAveragingAlg_smul,
      phi.evalAlg_add, phi.evalAlg_smul,
      phi_eval_v1_side phi, phi_eval_v0_side phi]
  ring

set_option maxHeartbeats 8000000 in
theorem phi_evalAlg_sigma2_alg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg sigma2_alg =
      24 * phi.eval certF6 - 4 * phi.eval sdpF7
      - 4 * phi.eval flag15 - 2 * phi.eval sdpF20
      - 2 * phi.eval flag25 - 12 * phi.eval sdpF30
      - 6 * phi.eval flag34 := by
  unfold sigma2_alg
  rw [phi.evalAlg_smul]
  have hsub : (extSum thesisType2 ⟨0, by decide⟩
      - extSum thesisType2 ⟨1, by decide⟩ : GenFlagAlg CG2 thesisType2) =
      extSum thesisType2 ⟨0, by decide⟩
      + (-1 : ℝ) • extSum thesisType2 ⟨1, by decide⟩ := by
    rw [neg_one_smul]; abel
  rw [hsub, genAveragingAlg_add, genAveragingAlg_smul,
      phi.evalAlg_add, phi.evalAlg_smul,
      phi_eval_v0_side_t2 phi, phi_eval_v1_side_t2 phi]
  ring

set_option maxHeartbeats 8000000 in
theorem phi_evalAlg_sigma3_alg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg sigma3_alg =
      2 * phi.eval certF11 + phi.eval flag12
      - 2 * phi.eval flag15 + phi.eval certF22
      + 2 * phi.eval flag24 - 2 * phi.eval flag25 := by
  unfold sigma3_alg
  rw [phi.evalAlg_smul]
  have hsub : (extSum thesisType3 ⟨1, by decide⟩
      - extSum thesisType3 ⟨0, by decide⟩ : GenFlagAlg CG2 thesisType3) =
      extSum thesisType3 ⟨1, by decide⟩
      + (-1 : ℝ) • extSum thesisType3 ⟨0, by decide⟩ := by
    rw [neg_one_smul]; abel
  rw [hsub, genAveragingAlg_add, genAveragingAlg_smul,
      phi.evalAlg_add, phi.evalAlg_smul,
      phi_eval_v1_side_t3 phi, phi_eval_v0_side_t3 phi]
  ring

set_option maxHeartbeats 8000000 in
theorem phi_evalAlg_sigma4_alg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg sigma4_alg =
      phi.eval certF8 + phi.eval flag12
      - 2 * phi.eval flag15 + 4 * phi.eval certF31
      + 4 * phi.eval flag32 - 6 * phi.eval flag34 := by
  unfold sigma4_alg
  rw [phi.evalAlg_smul]
  have hsub : (extSum thesisType4 ⟨1, by decide⟩
      - extSum thesisType4 ⟨0, by decide⟩ : GenFlagAlg CG2 thesisType4) =
      extSum thesisType4 ⟨1, by decide⟩
      + (-1 : ℝ) • extSum thesisType4 ⟨0, by decide⟩ := by
    rw [neg_one_smul]; abel
  rw [hsub, genAveragingAlg_add, genAveragingAlg_smul,
      phi.evalAlg_add, phi.evalAlg_smul,
      phi_eval_v1_side_t4 phi, phi_eval_v0_side_t4 phi]
  ring

set_option maxHeartbeats 8000000 in
theorem phi_evalAlg_sigma5_alg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg sigma5_alg =
      -2 * phi.eval flag16 - phi.eval flag17
      + phi.eval sdpFlag37 + 2 * phi.eval sdpFlag55 := by
  unfold sigma5_alg
  rw [phi.evalAlg_smul]
  have hsub : (extSum thesisType5 ⟨2, by decide⟩
      - extSum thesisType5 ⟨0, by decide⟩ : GenFlagAlg CG2 thesisType5) =
      extSum thesisType5 ⟨2, by decide⟩
      + (-1 : ℝ) • extSum thesisType5 ⟨0, by decide⟩ := by
    rw [neg_one_smul]; abel
  rw [hsub, genAveragingAlg_add, genAveragingAlg_smul,
      phi.evalAlg_add, phi.evalAlg_smul,
      phi_eval_v2_side_t5 phi, phi_eval_v0_side_t5 phi]
  ring

/-! ## Path 2: cs0_alg / cs1_alg / target_alg (Phase E1 Step 1)

Algebra-level analogs of the cs0/cs1 squared-elements and the SDP target.
Together with `linSum_alg`, these participate in the algebra-level cert
arithmetic `target_alg = linSum_alg + cs0_alg + cs1_alg`. -/

/-- cs0 at the algebra level: `120·⟦f²⟧ + 120·⟦g²⟧` over csType6. -/
noncomputable def cs0_alg : GenFlagAlg CG2 (GenFlagType.empty CG2) :=
  (120 : ℝ) • genAveragingAlg csType6 (cs0_f.mul cs0_f)
    + (120 : ℝ) • genAveragingAlg csType6 (cs0_g.mul cs0_g)

/-- cs1 at the algebra level: `120·⟦h²⟧ + 120·⟦ℓ²⟧` over csType7. -/
noncomputable def cs1_alg : GenFlagAlg CG2 (GenFlagType.empty CG2) :=
  (120 : ℝ) • genAveragingAlg csType7 (cs1_h.mul cs1_h)
    + (120 : ℝ) • genAveragingAlg csType7 (cs1_l.mul cs1_l)

/-- The SDP target at the algebra level: `30·certF1 − 2·F₉ − F₃₇ − 2·F₅₅`.

    The constant 30 is on the `certF1` generator (the all-black-no-edge
    size-5 flag whose density → 1 in BRRB regular limits, see
    `phi_eval_certF1_eq_one`). -/
noncomputable def target_alg : GenFlagAlg CG2 (GenFlagType.empty CG2) :=
  (30 : ℝ) • GenFlagAlg.single certF1
    - (2 : ℝ) • GenFlagAlg.single sdpFlag9
    - GenFlagAlg.single sdpFlag37
    - (2 : ℝ) • GenFlagAlg.single sdpFlag55

/-! ## Path 2: phi.evalAlg(linSum_alg) = RHS of linSum_decomposition_identity (Phase D)

By definition, `linSum_alg = 6•b1_alg + σ₁_alg + ¼•σ₂_alg + σ₃_alg + σ₄_alg + 2•σ₅_alg`.
Apply `phi.evalAlg`'s linearity + the Phase C lemmas to get the RHS. -/

set_option maxHeartbeats 8000000 in
theorem phi_evalAlg_linSum_alg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg linSum_alg =
      6 * (5 * phi.eval certF1 - phi.eval certF6)
      + (-4 * phi.eval certF4 - 6 * phi.eval flag5
         + 2 * phi.eval flag12 + 2 * phi.eval flag24 + 4 * phi.eval flag32)
      + 1 / 4 * (24 * phi.eval certF6 - 4 * phi.eval sdpF7
         - 4 * phi.eval flag15 - 2 * phi.eval sdpF20
         - 2 * phi.eval flag25 - 12 * phi.eval sdpF30 - 6 * phi.eval flag34)
      + (2 * phi.eval certF11 + phi.eval flag12
         - 2 * phi.eval flag15 + phi.eval certF22
         + 2 * phi.eval flag24 - 2 * phi.eval flag25)
      + (phi.eval certF8 + phi.eval flag12
         - 2 * phi.eval flag15 + 4 * phi.eval certF31
         + 4 * phi.eval flag32 - 6 * phi.eval flag34)
      + 2 * (-2 * phi.eval flag16 - phi.eval flag17
         + phi.eval sdpFlag37 + 2 * phi.eval sdpFlag55) := by
  unfold linSum_alg
  rw [phi.evalAlg_add, phi.evalAlg_add, phi.evalAlg_add, phi.evalAlg_add,
      phi.evalAlg_add, phi.evalAlg_smul, phi.evalAlg_smul, phi.evalAlg_smul,
      phi_evalAlg_b1_alg, phi_evalAlg_sigma1_alg, phi_evalAlg_sigma2_alg,
      phi_evalAlg_sigma3_alg, phi_evalAlg_sigma4_alg, phi_evalAlg_sigma5_alg]

/-! ## Path 2: phi.evalAlg of cs0_alg / cs1_alg / target_alg (Phase E1 Step 2)

Each component's `phi.evalAlg` is computed:
- `phi_evalAlg_cs0_alg`: via `fsq_eval_identity` + `gsq_eval_identity` (S0F basis).
- `phi_evalAlg_cs1_alg`: via `hsq_eval_identity` + `lsq_eval_identity` (named-flag basis).
- `phi_evalAlg_target_alg`: via `evalAlg_add/_smul/_single` + `phi_eval_certF1_eq_one`. -/

set_option maxHeartbeats 8000000 in
theorem phi_evalAlg_cs0_alg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg cs0_alg =
      4 * phi.eval cs0_flag_S0F33
      - (1/2) * phi.eval cs0_flag_S0F34F - (1/2) * phi.eval cs0_flag_S0F34T
      - (1/2) * phi.eval cs0_flag_S0F35F - (1/2) * phi.eval cs0_flag_S0F35T
      - 2 * phi.eval cs0_flag_S0F36F - 4 * phi.eval cs0_flag_S0F36T
      + 1 / 4 * phi.eval cs0_flag_S0F44
      + 1 / 2 * phi.eval cs0_flag_S0F46
      + 1 / 4 * phi.eval cs0_flag_S0F55
      + 1 / 2 * phi.eval cs0_flag_S0F56
      + 3 * phi.eval cs0_flag_S0F66 := by
  unfold cs0_alg
  rw [phi.evalAlg_add, phi.evalAlg_smul, phi.evalAlg_smul]
  have h_fsq := fsq_eval_identity phi
  have h_gsq := gsq_eval_identity phi
  linarith

set_option maxHeartbeats 8000000 in
theorem phi_evalAlg_cs1_alg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta) :
    phi.evalAlg cs1_alg =
      -2 * phi.eval sdpFlag9
      + 6 * phi.eval flag5 - 4 * phi.eval flag12 + 5 * phi.eval flag15
      + 4 * phi.eval flag16 + 2 * phi.eval flag17 - 4 * phi.eval flag24
      + 5 / 2 * phi.eval flag25 - 8 * phi.eval flag32
      + 15 / 2 * phi.eval flag34
      - 3 * phi.eval sdpFlag37 - 6 * phi.eval sdpFlag55 := by
  unfold cs1_alg
  rw [phi.evalAlg_add, phi.evalAlg_smul, phi.evalAlg_smul]
  have h_hsq := hsq_eval_identity phi
  have h_lsq := lsq_eval_identity phi
  linarith

set_option maxHeartbeats 8000000 in
theorem phi_evalAlg_target_alg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2)
      brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget)
    (hblack : ∀ k, (Finset.univ.filter
      (fun v : Fin (phi.seq.seq k).size => (phi.seq.seq k).str.2 v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget) :
    phi.evalAlg target_alg =
      30 - 2 * phi.eval sdpFlag9 - phi.eval sdpFlag37 - 2 * phi.eval sdpFlag55 := by
  unfold target_alg
  -- Rewrite subtractions as `a + (-c) • b` to use evalAlg_add + evalAlg_smul.
  have hsub : ((30 : ℝ) • GenFlagAlg.single certF1
      - (2 : ℝ) • GenFlagAlg.single sdpFlag9
      - GenFlagAlg.single sdpFlag37
      - (2 : ℝ) • GenFlagAlg.single sdpFlag55 :
      GenFlagAlg CG2 (GenFlagType.empty CG2)) =
      (30 : ℝ) • GenFlagAlg.single certF1
      + (-1 : ℝ) • ((2 : ℝ) • GenFlagAlg.single sdpFlag9)
      + (-1 : ℝ) • GenFlagAlg.single sdpFlag37
      + (-1 : ℝ) • ((2 : ℝ) • GenFlagAlg.single sdpFlag55) := by
    rw [show (-1 : ℝ) • ((2 : ℝ) • GenFlagAlg.single sdpFlag9) =
        -((2 : ℝ) • GenFlagAlg.single sdpFlag9) from by rw [neg_smul, one_smul],
      show (-1 : ℝ) • GenFlagAlg.single sdpFlag37 =
        -(GenFlagAlg.single sdpFlag37) from by rw [neg_smul, one_smul],
      show (-1 : ℝ) • ((2 : ℝ) • GenFlagAlg.single sdpFlag55) =
        -((2 : ℝ) • GenFlagAlg.single sdpFlag55) from by rw [neg_smul, one_smul]]
    abel
  rw [hsub]
  simp only [phi.evalAlg_add, phi.evalAlg_smul, phi.evalAlg_single]
  rw [phi_eval_certF1_eq_one phi hreg hblack]
  ring

/-! ## Path 2: eval-level cert arithmetic (Phase E2)

Eval-level lift of `BrrbCertificate.brrb_certificate_arithmetic` (List Int
vector identity, `native_decide`-verified): for any `phi : GenLimitFunctional`
in a BRRB regular black-independent limit (i.e., satisfying `hreg + hblack`),
  `phi.evalAlg target_alg = phi.evalAlg linSum_alg + phi.evalAlg cs0_alg + phi.evalAlg cs1_alg`.

The proof reduces both sides to a polynomial in `phi.eval` of named flags via
the four `phi_evalAlg_*_alg` lemmas, applies S0F→cert/sdpFN iso rewrites for
cs0_alg's S0F-basis output, then closes by `ring` after substituting
`phi_eval_certF1_eq_one` (the constant-30 absorption for BRRB regular limits).

This eval-level statement is enough to close `linSum_decomposition_identity`
(and downstream `brrb_linSum_eval_nonneg` / `pentagon_bound_simple`) without
needing the algebra-level `target_alg = linSum_alg + cs0_alg + cs1_alg`
Finsupp identity. -/

set_option maxHeartbeats 8000000 in
/-- **Eval-level cert arithmetic identity** — for any `phi` in a BRRB regular
    black-independent limit, `phi.evalAlg target_alg = phi.evalAlg linSum_alg
    + phi.evalAlg cs0_alg + phi.evalAlg cs1_alg`. Eval-level lift of
    `BrrbCertificate.brrb_certificate_arithmetic`. -/
theorem brrb_certificate_arithmetic_eval
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget)
    (hblack : ∀ k, (Finset.univ.filter
      (fun v : Fin (phi.seq.seq k).size => (phi.seq.seq k).str.2 v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget) :
    phi.evalAlg target_alg
      = phi.evalAlg linSum_alg + phi.evalAlg cs0_alg + phi.evalAlg cs1_alg := by
  rw [phi_evalAlg_target_alg phi hreg hblack, phi_evalAlg_linSum_alg phi,
      phi_evalAlg_cs0_alg phi, phi_evalAlg_cs1_alg phi]
  have hS0F33 := phi.eval_iso cs0_flag_S0F33 certF4 S0F33_iso_certF4
  have hS0F34F := phi.eval_iso cs0_flag_S0F34F certF22 S0F34F_iso_certF22
  have hS0F34T := phi.eval_iso cs0_flag_S0F34T certF8 S0F34T_iso_certF8
  have hS0F35F := phi.eval_iso cs0_flag_S0F35F certF22
    (S0F34F_iso_S0F35F.symm.trans S0F34F_iso_certF22)
  have hS0F35T := phi.eval_iso cs0_flag_S0F35T certF8
    (S0F34T_iso_S0F35T.symm.trans S0F34T_iso_certF8)
  have hS0F36F := phi.eval_iso cs0_flag_S0F36F certF11 S0F36F_iso_certF11
  have hS0F36T := phi.eval_iso cs0_flag_S0F36T certF31 S0F36T_iso_certF31
  have hS0F44 := phi.eval_iso cs0_flag_S0F44 sdpF20 S0F44_iso_sdpF20
  have hS0F46 := phi.eval_iso cs0_flag_S0F46 sdpF7 S0F46_iso_sdpF7
  have hS0F55 := phi.eval_iso cs0_flag_S0F55 sdpF20
    (S0F44_iso_S0F55.symm.trans S0F44_iso_sdpF20)
  have hS0F56 := phi.eval_iso cs0_flag_S0F56 sdpF7
    (S0F46_iso_S0F56.symm.trans S0F46_iso_sdpF7)
  have hS0F66 := phi.eval_iso cs0_flag_S0F66 sdpF30 S0F66_iso_sdpF30
  rw [hS0F33, hS0F34F, hS0F34T, hS0F35F, hS0F35T, hS0F36F, hS0F36T,
      hS0F44, hS0F46, hS0F55, hS0F56, hS0F66,
      phi_eval_certF1_eq_one phi hreg hblack]
  ring

/-- **LinSum decomposition identity** (thesis §3.6, eq:pent_lin_sum):
    The suffices expression (after iso rewrites to a unified flag basis) equals
    the weighted sum of B₁ and σᵢ components from BrrbCertificate.lean.

    Both sides represent `evalAlg(linSum)` but in different coordinate systems:
    - LHS: the eval-identity-derived expression (cs1-side + cs0-side flags)
    - RHS: the cert-vector-derived expression (cert-only flags + shared flags)

    **Path 2 proof**: bridge LHS to RHS via the eval-level cert arithmetic.
    LHS equals `phi.evalAlg(target_alg) − phi.evalAlg(cs0_alg) − phi.evalAlg(cs1_alg)`
    after applying S0F→cert/sdpFN iso rewrites to convert cs0_alg's S0F-basis form.
    By `brrb_certificate_arithmetic_eval`, this equals `phi.evalAlg(linSum_alg)`,
    which by `phi_evalAlg_linSum_alg` (Phase D) equals RHS.

    Requires `hreg` + `hblack` to absorb the constant 30 via
    `phi_eval_certF1_eq_one`. -/
theorem linSum_decomposition_identity
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget)
    (hblack : ∀ k, (Finset.univ.filter
      (fun v : Fin (phi.seq.seq k).size => (phi.seq.seq k).str.2 v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget) :
    30 - 6 * phi.eval flag5 + 4 * phi.eval flag12 - 5 * phi.eval flag15
      - 4 * phi.eval flag16 - 2 * phi.eval flag17 + 4 * phi.eval flag24
      - 5 / 2 * phi.eval flag25 + 8 * phi.eval flag32
      - 15 / 2 * phi.eval flag34
      - 4 * phi.eval certF4 + phi.eval certF8
      + phi.eval certF22 + 2 * phi.eval certF11 + 4 * phi.eval certF31
      - 1 / 2 * phi.eval sdpF20 - phi.eval sdpF7
      - 3 * phi.eval sdpF30
      + 2 * phi.eval sdpFlag37 + 4 * phi.eval sdpFlag55
    = 6 * (5 * phi.eval certF1 - phi.eval certF6)
      + (-4 * phi.eval certF4 - 6 * phi.eval flag5
         + 2 * phi.eval flag12 + 2 * phi.eval flag24 + 4 * phi.eval flag32)
      + 1 / 4 * (24 * phi.eval certF6 - 4 * phi.eval sdpF7
         - 4 * phi.eval flag15 - 2 * phi.eval sdpF20
         - 2 * phi.eval flag25 - 12 * phi.eval sdpF30 - 6 * phi.eval flag34)
      + (2 * phi.eval certF11 + phi.eval flag12
         - 2 * phi.eval flag15 + phi.eval certF22
         + 2 * phi.eval flag24 - 2 * phi.eval flag25)
      + (phi.eval certF8 + phi.eval flag12
         - 2 * phi.eval flag15 + 4 * phi.eval certF31
         + 4 * phi.eval flag32 - 6 * phi.eval flag34)
      + 2 * (-2 * phi.eval flag16 - phi.eval flag17
         + phi.eval sdpFlag37 + 2 * phi.eval sdpFlag55) := by
  -- Phase D: rewrite RHS using phi_evalAlg_linSum_alg.
  rw [← phi_evalAlg_linSum_alg phi]
  -- Phase E: bridge LHS to phi.evalAlg(linSum_alg) via the eval-level cert
  -- corollary (proved without sorry dependency).
  have heval := brrb_certificate_arithmetic_eval phi hreg hblack
  have h_target := phi_evalAlg_target_alg phi hreg hblack
  have h_cs0 := phi_evalAlg_cs0_alg phi
  have h_cs1 := phi_evalAlg_cs1_alg phi
  -- S0F→cert/sdpFN iso rewrites for cs0_alg's S0F-basis output.
  have hS0F33 := phi.eval_iso cs0_flag_S0F33 certF4 S0F33_iso_certF4
  have hS0F34F := phi.eval_iso cs0_flag_S0F34F certF22 S0F34F_iso_certF22
  have hS0F34T := phi.eval_iso cs0_flag_S0F34T certF8 S0F34T_iso_certF8
  have hS0F35F := phi.eval_iso cs0_flag_S0F35F certF22
    (S0F34F_iso_S0F35F.symm.trans S0F34F_iso_certF22)
  have hS0F35T := phi.eval_iso cs0_flag_S0F35T certF8
    (S0F34T_iso_S0F35T.symm.trans S0F34T_iso_certF8)
  have hS0F36F := phi.eval_iso cs0_flag_S0F36F certF11 S0F36F_iso_certF11
  have hS0F36T := phi.eval_iso cs0_flag_S0F36T certF31 S0F36T_iso_certF31
  have hS0F44 := phi.eval_iso cs0_flag_S0F44 sdpF20 S0F44_iso_sdpF20
  have hS0F46 := phi.eval_iso cs0_flag_S0F46 sdpF7 S0F46_iso_sdpF7
  have hS0F55 := phi.eval_iso cs0_flag_S0F55 sdpF20
    (S0F44_iso_S0F55.symm.trans S0F44_iso_sdpF20)
  have hS0F56 := phi.eval_iso cs0_flag_S0F56 sdpF7
    (S0F46_iso_S0F56.symm.trans S0F46_iso_sdpF7)
  have hS0F66 := phi.eval_iso cs0_flag_S0F66 sdpF30 S0F66_iso_sdpF30
  rw [hS0F33, hS0F34F, hS0F34T, hS0F35F, hS0F35T, hS0F36F, hS0F36T,
      hS0F44, hS0F46, hS0F55, hS0F56, hS0F66] at h_cs0
  linarith

/-! ## SDP Cone Bound and Downstream Theorems

These theorems were moved from PentagonConjecture.lean because they require
the evaluation identities proved above (hsq/lsq/fsq/gsq_eval_identity). -/

attribute [local instance] Classical.propDecidable

/-- **LinSum nonnegativity** (thesis §3.6):
    The linear sum component of the SDP certificate evaluates nonneg.
    `linSum_eval = target - cs₀_eval - cs₁_eval ≥ 0`

    The SDP certificate decomposes linSum = 6·B₁ + σ₁ + (1/4)·σ₂ + σ₃ + σ₄ + 2·σ₅
    where B₁ ≥ 0 is a counting identity and each σᵢ ≥ 0 is an extension ordering
    at a specific flag type (thesis §3.6, eq:pent_lin_sum). The decomposition is
    arithmetically verified by `native_decide` in BrrbCertificate.lean.

    **Proof strategy**: Substitute the four evaluation identities (hsq, lsq, fsq, gsq)
    to express the LHS as a linear combination of flag densities. Then show
    nonnegativity using the B₁ counting identity and extension ordering constraints.

    The key sub-results:
    - B₁ nonnegativity: `5·p(F₁) ≥ p(F₆)` (counting identity in the algebra)
    - σᵢ nonnegativity: extension orderings from regularity + graph class constraints
    - All coefficients are nonneg (6, 1, 1/4, 1, 1, 2)

    Each extension ordering holds because in a regular triangle-free
    black-independent graph, the extension counts at different orbits
    satisfy specific inequalities (thesis §3.6, Lemma 3.10). -/
theorem brrb_linSum_eval_nonneg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget)
    (hblack : ∀ k, (Finset.univ.filter
      (fun v : Fin (phi.seq.seq k).size => (phi.seq.seq k).str.2 v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget) :
    0 ≤ 30 - 2 * phi.eval sdpFlag9 - phi.eval sdpFlag37 - 2 * phi.eval sdpFlag55
      - (120 * phi.evalAlg (genAveragingAlg csType7 (cs1_h.mul cs1_h))
       + 120 * phi.evalAlg (genAveragingAlg csType7 (cs1_l.mul cs1_l))
       + 120 * phi.evalAlg (genAveragingAlg csType6 (cs0_f.mul cs0_f))
       + 120 * phi.evalAlg (genAveragingAlg csType6 (cs0_g.mul cs0_g))) := by
  -- Step 1: Substitute the four evaluation identities to eliminate evalAlg terms.
  -- After substitution, the f₉/f₃₇/f₅₅ terms cancel, leaving a linear combination
  -- of "auxiliary" flag densities = linSum component of the SDP certificate.
  have h_hsq := hsq_eval_identity phi
  have h_lsq := lsq_eval_identity phi
  have h_fsq := fsq_eval_identity phi
  have h_gsq := gsq_eval_identity phi
  -- Step 2: Reduce to the pure flag-eval "linSum" expression.
  -- LinSum = target - cs_eval, expressed purely in terms of phi.eval of specific flags.
  -- After the eval identity substitution, f₉/f₃₇/f₅₅ cancel completely.
  suffices hlinSum : 0 ≤ 30
      - 6 * phi.eval flag5 + 4 * phi.eval flag12 - 5 * phi.eval flag15
      - 4 * phi.eval flag16 - 2 * phi.eval flag17 + 4 * phi.eval flag24
      - 5 / 2 * phi.eval flag25 + 8 * phi.eval flag32
      - 15 / 2 * phi.eval flag34
      + 2 * phi.eval sdpFlag37 + 4 * phi.eval sdpFlag55
      - 4 * phi.eval cs0_flag_S0F33 + (1/2) * phi.eval cs0_flag_S0F34F
      + (1/2) * phi.eval cs0_flag_S0F34T + (1/2) * phi.eval cs0_flag_S0F35F
      + (1/2) * phi.eval cs0_flag_S0F35T + 2 * phi.eval cs0_flag_S0F36F
      + 4 * phi.eval cs0_flag_S0F36T
      - 1 / 4 * phi.eval cs0_flag_S0F44 - 1 / 2 * phi.eval cs0_flag_S0F46
      - 1 / 4 * phi.eval cs0_flag_S0F55 - 1 / 2 * phi.eval cs0_flag_S0F56
      - 3 * phi.eval cs0_flag_S0F66 by
    nlinarith
  -- Step 3: Prove the linSum flag-eval expression is nonneg.
  -- This requires the extension ordering constraints from regularity + graph class.
  -- The linSum decomposes as 6*B1 + sigma1 + (1/4)*sigma2 + sigma3 + sigma4 + 2*sigma5
  -- (BrrbCertificate.lean), where B1 >= 0 by counting and each sigma_i >= 0 by
  -- extension ordering in regular triangle-free black-independent graphs.
  --
  -- The suffices expression mixes two flag bases (Rust flags from cs1 eval identities
  -- and S0F flags from cs0 eval identities). The S0F-to-Rust correspondences are:
  --   S0F33 ~ F2, S0F34F ~ S0F35F ~ F20, S0F34T ~ S0F35T ~ S0F36F ~ F7,
  --   S0F36T ~ F30, S0F44 ~ S0F55 ~ F18, S0F46 ~ S0F56 ~ F13, S0F66 ~ F33.
  -- After unifying the basis, the expression matches the BrrbCertificate linSum
  -- (in the appropriate density convention) and decomposes into nonneg components.
  --
  -- Filling this sorry requires ~350-400 lines of infrastructure:
  --
  -- The linSum decomposes as 6*B1 + sigma_1 + (1/4)*sigma_2 + sigma_3 + sigma_4 + 2*sigma_5
  -- where each sigma_i is a LINEAR extension difference (NOT squared), so
  -- genSquare_in_cone does NOT apply. Positivity requires:
  --
  -- (1) Unify the mixed basis: prove 12 S0F-to-Rust flag isomorphisms
  --     (S0F33 ~ F2, S0F34F ~ F20, S0F34T ~ F7, S0F36T ~ F30, S0F44 ~ F18,
  --      S0F46 ~ F13, S0F66 ~ F33). Correspondences computed via canonical forms.
  --
  -- (2) For each sigma_i: define ext_diff_i as GenFlagAlg element, prove isPositive
  --     via per-embedding extension orderings lifted to limits, then apply
  --     genAveraging_preserves_positivity. Three orderings are proved
  --     (linSumType11, linSumType3, linSumType10_first); two remain.
  --
  -- (3) Prove B1 >= 0 (requires ones identity or direct counting argument).
  --
  -- (4) Assembly via linarith.
  --
  -- The ones identity (Sigma aut(F)*phi.eval(F) = 1) does NOT hold in the local
  -- flag algebra (normalization by C(Delta,5) not C(n,5)), so the constant 30
  -- cannot be absorbed into flag density terms this way.
  --
  -- See the development notes for the detailed proof strategy.
  --
  -- Phase 1: Convert all S0F flag evals to cert/SDP flag evals via isomorphisms.
  have hS0F33 := phi.eval_iso cs0_flag_S0F33 certF4 S0F33_iso_certF4
  have hS0F34F := phi.eval_iso cs0_flag_S0F34F certF22 S0F34F_iso_certF22
  have hS0F34T := phi.eval_iso cs0_flag_S0F34T certF8 S0F34T_iso_certF8
  have hS0F35F := phi.eval_iso cs0_flag_S0F35F certF22
    (S0F34F_iso_S0F35F.symm.trans S0F34F_iso_certF22)
  have hS0F35T := phi.eval_iso cs0_flag_S0F35T certF8
    (S0F34T_iso_S0F35T.symm.trans S0F34T_iso_certF8)
  have hS0F36F := phi.eval_iso cs0_flag_S0F36F certF11 S0F36F_iso_certF11
  have hS0F36T := phi.eval_iso cs0_flag_S0F36T certF31 S0F36T_iso_certF31
  have hS0F44 := phi.eval_iso cs0_flag_S0F44 sdpF20 S0F44_iso_sdpF20
  have hS0F46 := phi.eval_iso cs0_flag_S0F46 sdpF7 S0F46_iso_sdpF7
  have hS0F55 := phi.eval_iso cs0_flag_S0F55 sdpF20
    (S0F44_iso_S0F55.symm.trans S0F44_iso_sdpF20)
  have hS0F56 := phi.eval_iso cs0_flag_S0F56 sdpF7
    (S0F46_iso_S0F56.symm.trans S0F46_iso_sdpF7)
  have hS0F66 := phi.eval_iso cs0_flag_S0F66 sdpF30 S0F66_iso_sdpF30
  rw [hS0F33, hS0F34F, hS0F34T, hS0F35F, hS0F35T, hS0F36F, hS0F36T,
      hS0F44, hS0F46, hS0F55, hS0F56, hS0F66]
  -- Phase 2: Decompose into nonneg components via the linSum decomposition.
  -- The cert decomposition: linSum = 6·B₁ + σ₁ + ¼·σ₂ + σ₃ + σ₄ + 2·σ₅
  -- (verified by native_decide in BrrbCertificate.lean).
  -- The decomposition identity bridges the suffices flag basis (after iso rw)
  -- to the cert flag basis (cert-only flags + shared flags).
  have hdecomp := linSum_decomposition_identity phi hreg hblack
  have hB1 := b1_nonneg phi hreg hblack
  have hσ1 := sigma1_nonneg phi hreg
  have hσ2 := sigma2_nonneg phi hreg
  have hσ3 := sigma3_nonneg phi hreg
  have hσ4 := sigma4_nonneg phi hreg
  have hσ5 := sigma5_nonneg phi hreg
  linarith

/-- **SDP cone bound** (thesis §3.6, Lemma 3.11):
    The SDP certificate decomposes `30∅ - 120O` as a sum of nonneg flag algebra
    elements: `linSum + cs₀ + cs₁ = 30∅ - 120O ∈ SemCone^∅`.

    Evaluating through `ψ.evalAlg` (unlabelled density convention):
    `30 - 2f₉ - f₃₇ - 2f₅₅ ≥ 0`, i.e., `2f₉ + f₃₇ + 2f₅₅ ≤ 30`.

    Proof: The four CS positivity facts (cs0_f/g_avg_positive, cs1_h/l_avg_positive)
    combined with the evaluation identities and flag nonnegativity yield the bound.
    The key identity is: `30 - 2f₉ - f₃₇ - 2f₅₅ = cs1_eval + cs0_eval + linSum_eval`
    where each component evaluates nonneg. -/
theorem brrb_sdp_cone_nonneg
    (phi : GenLimitFunctional CG2 (GenFlagType.empty CG2) brrbGenGraphClass brrbGenDelta)
    (hreg : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget)
    (hblack : ∀ k, (Finset.univ.filter
      (fun v : Fin (phi.seq.seq k).size => (phi.seq.seq k).str.2 v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget) :
    0 ≤ 30 - 2 * phi.eval sdpFlag9 - phi.eval sdpFlag37 - 2 * phi.eval sdpFlag55 := by
  -- The SDP certificate decomposes the target as cs_eval + linSum_eval, both ≥ 0.
  -- cs_eval = 120·(h²+ℓ²+f²+g²) averaged, nonneg by Cauchy-Schwarz.
  -- linSum_eval = target - cs_eval, nonneg by extension ordering in regular graphs.
  have h_h := cs1_h_avg_positive phi
  have h_l := cs1_l_avg_positive phi
  have h_f := cs0_f_avg_positive phi
  have h_g := cs0_g_avg_positive phi
  -- LinSum nonnegativity: 0 ≤ target - cs_eval (requires regularity)
  have hlinSum := brrb_linSum_eval_nonneg phi hreg hblack
  -- CS nonnegativity: 0 ≤ cs_eval
  have hcs_nonneg : 0 ≤ 120 * phi.evalAlg (genAveragingAlg csType7 (cs1_h.mul cs1_h)) +
      120 * phi.evalAlg (genAveragingAlg csType7 (cs1_l.mul cs1_l)) +
      120 * phi.evalAlg (genAveragingAlg csType6 (cs0_f.mul cs0_f)) +
      120 * phi.evalAlg (genAveragingAlg csType6 (cs0_g.mul cs0_g)) := by
    have h1 := mul_nonneg (by norm_num : (0:ℝ) ≤ 120) h_h
    have h2 := mul_nonneg (by norm_num : (0:ℝ) ≤ 120) h_l
    have h3 := mul_nonneg (by norm_num : (0:ℝ) ≤ 120) h_f
    have h4 := mul_nonneg (by norm_num : (0:ℝ) ≤ 120) h_g
    linarith
  -- target = (target - cs_eval) + cs_eval ≥ 0 + 0 = 0
  linarith

/-- **BRRB averaging bridge + SDP limit bound** (thesis §3.5):
    Every convergent subsequential limit of `brrbCount(G)/C(Δ,4)` is at most 6. -/
theorem brrb_sdp_limit_bound :
    ∀ (seq : ℕ → ColouredGraphClass),
    StrictMono (fun k => maxDegree (seq k).graph) →
    ∀ (sub : ℕ → ℕ) (L : ℝ),
    StrictMono sub →
    Filter.Tendsto (fun k => (brrbCount (seq (sub k)) : ℝ) /
      (Nat.choose (maxDegree (seq (sub k)).graph) 4 : ℝ)) Filter.atTop (nhds L) →
    L ≤ 6 := by
  intro seq hΔ sub L hsub htend
  set phi := genLimit_functional_construction CG2 (GenFlagType.empty CG2)
    brrbGenGraphClass brrbGenDelta (toGenDeltaSeq (seq ∘ sub) (hΔ.comp hsub))
    (fun k => toGenFlag_in_brrbClass (seq (sub k)))
  -- Step 1: L = 2 * phi.eval brrbGenFlag
  have hbrrbLocal := brrbGenFlag_isLocalFlag
  have hconv_brrb : Filter.Tendsto
      (fun k => genUnlabelledDensity CG2 (GenFlagType.empty CG2) brrbGenFlag
        (phi.seq.seq (phi.sub k)) brrbGenDelta)
      Filter.atTop (nhds (phi.eval brrbGenFlag)) :=
    phi.convergence brrbGenFlag hbrrbLocal
  have hseq_eq : ∀ k, phi.seq.seq k = (seq (sub k)).toGenFlag := fun k => rfl
  have hpointwise : ∀ k,
      (brrbCount (seq (sub (phi.sub k))) : ℝ) /
        (Nat.choose (maxDegree (seq (sub (phi.sub k))).graph) 4 : ℝ) =
      (genFlagAutCount CG2 (GenFlagType.empty CG2) brrbGenFlag : ℝ) *
        genUnlabelledDensity CG2 (GenFlagType.empty CG2) brrbGenFlag
          (phi.seq.seq (phi.sub k)) brrbGenDelta := by
    intro k; rw [hseq_eq]; exact brrbCount_div_eq_aut_mul_unlabelledDensity (seq (sub (phi.sub k)))
  have htend_sub : Filter.Tendsto
      (fun k => (brrbCount (seq (sub (phi.sub k))) : ℝ) /
        (Nat.choose (maxDegree (seq (sub (phi.sub k))).graph) 4 : ℝ))
      Filter.atTop (nhds L) :=
    htend.comp (phi.sub_strictMono.tendsto_atTop)
  have htend_aut_uD : Filter.Tendsto
      (fun k => (genFlagAutCount CG2 (GenFlagType.empty CG2) brrbGenFlag : ℝ) *
        genUnlabelledDensity CG2 (GenFlagType.empty CG2) brrbGenFlag
          (phi.seq.seq (phi.sub k)) brrbGenDelta)
      Filter.atTop (nhds L) := by
    convert htend_sub using 1; ext k; exact (hpointwise k).symm
  have htend_aut_eval : Filter.Tendsto
      (fun k => (genFlagAutCount CG2 (GenFlagType.empty CG2) brrbGenFlag : ℝ) *
        genUnlabelledDensity CG2 (GenFlagType.empty CG2) brrbGenFlag
          (phi.seq.seq (phi.sub k)) brrbGenDelta)
      Filter.atTop (nhds ((genFlagAutCount CG2 (GenFlagType.empty CG2) brrbGenFlag : ℝ) *
        phi.eval brrbGenFlag)) :=
    hconv_brrb.const_mul _
  have hL_eq : L = (genFlagAutCount CG2 (GenFlagType.empty CG2) brrbGenFlag : ℝ) *
      phi.eval brrbGenFlag :=
    tendsto_nhds_unique htend_aut_uD htend_aut_eval
  rw [brrbGenFlag_autCount] at hL_eq
  -- hL_eq : L = 2 * phi.eval brrbGenFlag
  -- Step 2: averaging identity
  have hreg_phi : ∀ k, ∀ v : Fin (phi.seq.seq k).size,
      (Finset.univ.filter ((phi.seq.seq k).str.1.Adj v)).card =
        brrbGenDelta (phi.seq.seq k).forget := by
    intro k v; exact (seq (sub k)).regular v
  have hblack_phi : ∀ k, (Finset.univ.filter
      (fun v : Fin (phi.seq.seq k).size => (phi.seq.seq k).str.2 v = 1)).card =
      brrbGenDelta (phi.seq.seq k).forget := by
    intro k
    change (Finset.univ.filter
        (fun v : Fin (seq (sub k)).toGenFlag.size =>
          (seq (sub k)).toGenFlag.str.2 v = 1)).card =
      brrbGenDelta (seq (sub k)).toGenFlag.forget
    rw [brrbGenDelta_toGenFlag]
    exact (seq (sub k)).blackCount
  have hAvgId := brrb_averaging_identity phi hreg_phi
  -- Step 3: SDP bound
  have hSdp := brrb_sdp_cone_nonneg phi hreg_phi hblack_phi
  -- L = 2*((1/5)f₉+(1/10)f₃₇+(1/5)f₅₅) = (1/5)(2f₉+f₃₇+2f₅₅) ≤ 30/5 = 6
  rw [hL_eq, hAvgId]; push_cast
  linarith

/-- **SDP density bound (Theorem 3.2)**: The BRRB count is at most (6+eps)*C(Delta,4). -/
theorem brrb_count_density_bound :
    ∀ eps : ℝ, 0 < eps → ∃ D₀ : ℕ, ∀ G : ColouredGraphClass,
      D₀ ≤ maxDegree G.graph →
      (brrbCount G : ℝ) ≤ (6 + eps) * (Nat.choose (maxDegree G.graph) 4 : ℝ) := by
  apply brrb_bound_from_limit 6 (by norm_num)
  intro seq hΔ sub L hsub htend
  exact brrb_sdp_limit_bound seq hΔ sub L hsub htend

/-- **Bridge theorem**: asymptotic BRRB counting bound. -/
theorem brrb_asymptotic_bound :
    ∀ eps : ℝ, 0 < eps → ∃ D₀ : ℕ, ∀ G : ColouredGraphClass,
      D₀ ≤ maxDegree G.graph →
      (brrbCount G : ℝ) ≤ (1/4 + eps) * maxDegree G.graph ^ 4 := by
  intro eps heps
  have heps₁ : (0 : ℝ) < 24 * eps := by positivity
  obtain ⟨D₀, hD₀⟩ := brrb_count_density_bound (24 * eps) heps₁
  refine ⟨D₀, fun G hG => ?_⟩
  have h1 := hD₀ G hG
  have h2 : (Nat.choose (maxDegree G.graph) 4 : ℝ) ≤
      (maxDegree G.graph : ℝ) ^ 4 / (Nat.factorial 4 : ℝ) :=
    Nat.choose_le_pow_div 4 (maxDegree G.graph)
  have hfact : (Nat.factorial 4 : ℝ) = 24 := by norm_num
  rw [hfact] at h2
  have h3 : (6 + 24 * eps) * ((maxDegree G.graph : ℝ) ^ 4 / 24) =
      (1/4 + eps) * (maxDegree G.graph : ℝ) ^ 4 := by ring
  have h_coeff_nonneg : (0 : ℝ) ≤ 6 + 24 * eps := by linarith
  calc (brrbCount G : ℝ) ≤ (6 + 24 * eps) * (Nat.choose (maxDegree G.graph) 4 : ℝ) := h1
    _ ≤ (6 + 24 * eps) * ((maxDegree G.graph : ℝ) ^ 4 / 24) := by
        exact mul_le_mul_of_nonneg_left h2 h_coeff_nonneg
    _ = (1/4 + eps) * (maxDegree G.graph : ℝ) ^ 4 := h3

/-- **Theorem 3.2**: If G is triangle-free then P(G) * (5 * 8) <= |G| * Delta(G)^4. -/
theorem pentagon_bound_simple (G : Flag emptyType) (hG : IsTriangleFree G) :
    (pentagonCount G : ℝ) * (5 * 8) ≤ G.size * maxDegree G ^ 4 := by
  suffices h : (pentagonCount G : ℝ) ≤ 1 / (5 * 8) * G.size * maxDegree G ^ 4 by
    nlinarith
  refine pentagon_asymptotic_suffices (1 / (5 * 8)) (by norm_num) (fun eps heps => ?_) G hG
  have hlocal := brrb_reduction (1/4) brrb_asymptotic_bound
  have hlocal' : ∀ eps : ℝ, 0 < eps → ∃ D₀ : ℕ, ∀ G : Flag emptyType, ∀ v : Fin G.size,
      IsTriangleFree G → IsRegular G → D₀ ≤ maxDegree G →
      (pentagonCountAt G v : ℝ) ≤ (1/8 + eps) * maxDegree G ^ 4 := by
    intro eps heps; obtain ⟨D₀, hD₀⟩ := hlocal eps heps
    exact ⟨D₀, fun G v htf hreg hD => by have := hD₀ G v htf hreg hD; linarith⟩
  have hglobal := pentagon_local_count (1/8) hlocal'
  obtain ⟨D₀, hD₀⟩ := hglobal eps heps
  refine ⟨D₀, fun G' hTF' hDeg' => ?_⟩
  obtain ⟨G'', hTF'', hReg'', hDelta, hRatio⟩ := pentagon_regular_suffices G' hTF'
  have hD₀'' : D₀ ≤ maxDegree G'' := hDelta ▸ hDeg'
  have hbound := hD₀ G'' hTF'' hReg'' hD₀''
  by_cases hsize : (G''.size : ℝ) = 0
  · have hsize_nat : G''.size = 0 := by exact_mod_cast hsize
    have hmaxdeg'' : maxDegree G'' = 0 := by
      unfold maxDegree
      have : Finset.univ (α := Fin G''.size) = ∅ := by
        ext v; exact absurd v.isLt (by omega)
      rw [this, Finset.sup_empty]; rfl
    have hmaxdeg' : maxDegree G' = 0 := by omega
    have hno_edges : ∀ u v : Fin G'.size, ¬G'.graph.Adj u v := by
      intro u v hadj
      have h1 : (Finset.univ.filter (fun w => G'.graph.Adj u w)).card ≤ maxDegree G' :=
        Finset.le_sup (f := fun v =>
          (Finset.univ.filter (fun u => G'.graph.Adj v u)).card) (Finset.mem_univ u)
      have h2 : 0 < (Finset.univ.filter (fun w => G'.graph.Adj u w)).card :=
        Finset.card_pos.mpr ⟨v, by simp [hadj]⟩
      omega
    have hcount : pentagonCount G' = 0 := by
      unfold pentagonCount
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro S _
      rintro ⟨f, _, _, hf_adj⟩
      exact hno_edges (f 0) (f 1) ((hf_adj 0 1).mp (by
        unfold cycleGraph5; rw [SimpleGraph.fromRel_adj]; exact ⟨by decide, Or.inl (by decide)⟩))
    simp [hcount, hmaxdeg']
  · have hsize_pos : (0 : ℝ) < G''.size := by
      exact lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hsize)
    rw [hDelta] at hbound
    have hne : (G''.size : ℝ) ≠ 0 := ne_of_gt hsize_pos
    have hnorm : (1 : ℝ) / 8 / 5 = 1 / (5 * 8) := by norm_num
    rw [hnorm] at hbound
    have hcombined : (pentagonCount G' : ℝ) * G''.size ≤
        (1 / (5 * 8) + eps) * G'.size * (maxDegree G' : ℝ) ^ 4 * G''.size := by
      calc (pentagonCount G' : ℝ) * G''.size
          ≤ (pentagonCount G'' : ℝ) * G'.size := hRatio
        _ ≤ ((1 / (5 * 8) + eps) * G''.size * (maxDegree G' : ℝ) ^ 4) * G'.size :=
            mul_le_mul_of_nonneg_right hbound (Nat.cast_nonneg _)
        _ = (1 / (5 * 8) + eps) * G'.size * (maxDegree G' : ℝ) ^ 4 * G''.size := by ring
    exact le_of_mul_le_mul_right hcombined hsize_pos

end Davey2024
