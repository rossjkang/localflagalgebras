import DaveyThesis2024.SecAsymBlowup
import DaveyThesis2024.SecAsymGates

/-!
# Route 1 (variant b) — the sound p = 1 asymmetric CG4 arm (b1-repair R1b-1)

This module is the **soundness core** of the asymmetric strong-edge-colouring
repair. It builds the sound `_F`/CG4 chain. The old CG22 false/vacuous/strict
eval axioms and the borrowed-target objective in
`SecAsymmetricBipartiteBridge.lean` were retired in R1b-2 (this same repair);
the §8 headlines in `StrongChromaticIndex` now route through the chain built
here (`secAsymF_general_vertex_bound` + the blow-up transfer + Hurley).

## What is built here (design the development notes §2–4 +
the development notes §1a/§2.2/§3, instantiated at p = 1)

1. **Blow-up degree lemmas** (design §4): from `IsAsymmetricBipartite p G`,
   `maxDegree (blowupAsymFlag G S b a) = a·maxDegree G` and
   `IsAsymmetricBipartite 1 (blowupAsymFlag G S b a)` — the *semiregular*
   variant (exact high side `= aΔ`, low side `≤ aΔ`), NOT full `IsRegular`.
2. **CG4 class + delta** (`secAsymGenGraphClass4`, `secAsymGenDelta4`): a 4-colour
   X-vertex-count `≤ 2Δ` clause, NO edge-colour clause (plain edges).
3. **Genuine objective** (`O_asym_CG4_coef`/`O_asym_CG4_alg`) over
   `SecAsymBasis.flagBasis_asym` + `AsymSecCertificate.target` (F-free, 334-dim)
   — NOT the borrowed symmetric `SecBipartiteCertificate.target`.
4. **CG4 host + seq wiring** (`colouredGraph4OfEdgeAsym`, `asymF_seq_to_genFlag`).
5. **Three sound axioms** (`sec_combinatorial_identity_asymmetric_F`,
   `phi_evalAlg_O_asym_CG4_le_bound`, `flagBasis_asym_isLocalFlag_F`) with the
   **generic** `C(2pΔ²,2)` normalizer (not actual-degree) — the two things that
   make this sound where the borrowed-target axiom was not.
6. The old CG22 regularity axiom closes here as a **theorem**
   (`asymF_seq_to_genFlag_mem_class4`) — class membership `X = N(a)∪N(b)`,
   `|X| ≤ 2Δ`, unconditional.
7. **Density bridge** `secAsymF_density_bridge` (p = 1 form), mirroring
   `Davey2024.SecBipartiteBridge.secBipF_density_bridge`.

The p = 1 bound axiom's per-vertex soundness was probe-confirmed
(the development notes: PASS, worst observed 0.47723 ≪ 0.5687).
-/

namespace Davey2024.SecAsymmetricBipartiteBridge

open Finset Classical
open Davey2024 Davey2024.SecAsymBasis Davey2024.SecAsymBlowup

noncomputable section

/-! ## §0. Basis size + tolerance -/

/-- The genuine F-free asymmetric CG4 basis size (= 334). -/
abbrev secAsymCG4BasisSize : Nat := SecAsymBasis.basisSize

/-- Identity-axiom tolerance (design §3.1 / L5C_design §3.1): `10⁻⁵`, amply above
the ≈ 3.5×10⁻⁹ target-integerisation residue over the 334-flag cert. -/
noncomputable def secAsymIdentityTol : ℝ := 1 / 100000

/-! ## §1. Blow-up degree lemmas (design §4)

The transfer application uses `G' = blowupAsymFlag G S b a` with `S = hAsym.choose`
(`cHi = b` copies for the high side `S`, `cLo = a` for the low side). We prove the
two semiregular facts the p = 1 bound axiom is gated on. -/

/-- Per-vertex neighbourhood-card of the asymmetric blow-up, decoded to a sum of
`copyCount` over the original's `G`-neighbourhood. A specialisation of
`blowSigma_nbhd_card` through `Fintype.equivFin`. -/
lemma blowup_nbhd_card_eq (G : Flag emptyType) (S : Finset (Fin G.size)) (cHi cLo : ℕ)
    (i : Fin (blowupAsymFlag G S cHi cLo).size) :
    (univ.filter (fun j => (blowupAsymFlag G S cHi cLo).graph.Adj i j)).card
      = ∑ w ∈ univ.filter (fun w =>
          G.graph.Adj ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm i).1 w),
          copyCount G S cHi cLo w := by
  have hreindex :
      (univ.filter (fun j => (blowupAsymFlag G S cHi cLo).graph.Adj i j)).card
        = (univ.filter (fun y : BlowVtx G S cHi cLo =>
            G.graph.Adj ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm i).1 y.1)).card :=
    card_filter_comp_equiv (Fintype.equivFin (BlowVtx G S cHi cLo)).symm
      (fun y => G.graph.Adj ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm i).1 y.1)
  rw [hreindex, blowSigma_nbhd_card]

/-- **High-side (S) blow-up degree** `= deg_G(orig)·cLo`. A copy of a vertex
`u ∈ S` has all neighbours outside `S` (bipartite opposition), each contributing
`cLo` copies. (S explicit — mirrors the working `blowup_degree_eq`.) -/
lemma blowup_deg_mem_S (G : Flag emptyType) (S : Finset (Fin G.size)) (cHi cLo : ℕ)
    (hbip : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (i : Fin (blowupAsymFlag G S cHi cLo).size)
    (hi : ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm i).1 ∈ S) :
    (univ.filter (fun j => (blowupAsymFlag G S cHi cLo).graph.Adj i j)).card
      = (univ.filter (fun w =>
          G.graph.Adj ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm i).1 w)).card * cLo := by
  rw [blowup_nbhd_card_eq]
  set v := ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm i).1 with hv
  have hcopy : ∀ w ∈ univ.filter (fun w => G.graph.Adj v w),
      copyCount G S cHi cLo w = cLo := by
    intro w hw
    rw [mem_filter] at hw
    have hwnotS : w ∉ S := (hbip v w hw.2).mp hi
    simp [copyCount, hwnotS]
  rw [Finset.sum_congr rfl hcopy, Finset.sum_const, smul_eq_mul]

/-- **Low-side (non-S) blow-up degree** `= deg_G(orig)·cHi`. A copy of `u ∉ S` has
all neighbours in `S`, each contributing `cHi` copies. -/
lemma blowup_deg_notmem_S (G : Flag emptyType) (S : Finset (Fin G.size)) (cHi cLo : ℕ)
    (hbip : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (i : Fin (blowupAsymFlag G S cHi cLo).size)
    (hi : ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm i).1 ∉ S) :
    (univ.filter (fun j => (blowupAsymFlag G S cHi cLo).graph.Adj i j)).card
      = (univ.filter (fun w =>
          G.graph.Adj ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm i).1 w)).card * cHi := by
  rw [blowup_nbhd_card_eq]
  set v := ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm i).1 with hv
  have hcopy : ∀ w ∈ univ.filter (fun w => G.graph.Adj v w),
      copyCount G S cHi cLo w = cHi := by
    intro w hw
    rw [mem_filter] at hw
    have hwS : w ∈ S := by
      by_contra hwS; exact hi ((hbip v w hw.2).mpr hwS)
    simp [copyCount, hwS]
  rw [Finset.sum_congr rfl hcopy, Finset.sum_const, smul_eq_mul]

/-- Every degree of `blowupAsymFlag G hAsym.choose b a` is `≤ a·maxDegree G`, given
the ratio bound `a ≤ b·p`. High-side copies are exactly `a·Δ`; low-side copies are
`deg_G(u)·b ≤ p·Δ·b = a·Δ`. -/
lemma blowup_degree_le
    (G : Flag emptyType) {p : ℝ} (hAsym : IsAsymmetricBipartite p G)
    (a b : ℕ) (hb : 1 ≤ b) (hpb : (b : ℝ) * p ≤ a)
    (i : Fin (blowupAsymFlag G hAsym.choose b a).size) :
    (univ.filter (fun j => (blowupAsymFlag G hAsym.choose b a).graph.Adj i j)).card
      ≤ maxDegree G * a := by
  by_cases hi : ((Fintype.equivFin (BlowVtx G hAsym.choose b a)).symm i).1 ∈ hAsym.choose
  · exact le_of_eq (by rw [blowup_deg_mem_S G hAsym.choose b a hAsym.choose_spec.1 i hi,
        hAsym.choose_spec.2.1 _ hi])
  · rw [blowup_deg_notmem_S G hAsym.choose b a hAsym.choose_spec.1 i hi]
    -- deg_G(v)·b ≤ p·Δ·b = a·Δ  (as a real inequality, cast back to ℕ)
    have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
    have hdeg : ((univ.filter (fun w =>
        G.graph.Adj ((Fintype.equivFin (BlowVtx G hAsym.choose b a)).symm i).1 w)).card : ℝ)
        ≤ p * maxDegree G := hAsym.choose_spec.2.2 _ hi
    have hR : ((univ.filter (fun w =>
        G.graph.Adj ((Fintype.equivFin (BlowVtx G hAsym.choose b a)).symm i).1 w)).card : ℝ) * b
        ≤ (maxDegree G : ℝ) * a := by
      calc ((univ.filter (fun w =>
              G.graph.Adj ((Fintype.equivFin (BlowVtx G hAsym.choose b a)).symm i).1 w)).card : ℝ)
              * b
          ≤ (p * maxDegree G) * b := mul_le_mul_of_nonneg_right hdeg (le_of_lt hb0)
        _ = (maxDegree G : ℝ) * (b * p) := by ring
        _ ≤ (maxDegree G : ℝ) * a := mul_le_mul_of_nonneg_left hpb (by positivity)
    exact_mod_cast hR

/-- If `maxDegree G > 0` then the high-degree component `S = hAsym.choose` is
nonempty (some edge exists, and one endpoint of it lies in `S`). -/
lemma choose_nonempty_of_maxDegree_pos
    (G : Flag emptyType) {p : ℝ} (hAsym : IsAsymmetricBipartite p G)
    (hΔ : 0 < maxDegree G) : hAsym.choose.Nonempty := by
  -- maxDegree > 0 ⇒ some vertex has a neighbour ⇒ some edge ⇒ an endpoint in S.
  have huniv : (univ : Finset (Fin G.size)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    rw [maxDegree] at hΔ
    simp only [Finset.univ_eq_empty, Finset.sup_empty] at hΔ
    exact absurd hΔ (lt_irrefl 0)
  obtain ⟨v, -, hsup⟩ := Finset.exists_mem_eq_sup (univ : Finset (Fin G.size)) huniv
    (fun v => (univ.filter (fun u => G.graph.Adj v u)).card)
  have hvpos : 0 < (univ.filter (fun u => G.graph.Adj v u)).card := by
    rw [maxDegree] at hΔ; rw [hsup] at hΔ; exact hΔ
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hvpos
  rw [mem_filter] at hw
  have hopp := hAsym.choose_spec.1 v w hw.2
  by_cases hvS : v ∈ hAsym.choose
  · exact ⟨v, hvS⟩
  · exact ⟨w, by by_contra hwS; exact hvS (hopp.mpr hwS)⟩

/-- A concrete blow-up copy index of an original vertex `u` (its `0`-th copy).
Requires the copy count `> 0`, i.e. `1 ≤ b` when `u ∈ S`. -/
def blowupCopy (G : Flag emptyType) (S : Finset (Fin G.size)) (cHi cLo : ℕ)
    (u : Fin G.size) (hc : 0 < copyCount G S cHi cLo u) :
    Fin (blowupAsymFlag G S cHi cLo).size :=
  Fintype.equivFin (BlowVtx G S cHi cLo) ⟨u, ⟨0, hc⟩⟩

lemma blowupCopy_orig (G : Flag emptyType) (S : Finset (Fin G.size)) (cHi cLo : ℕ)
    (u : Fin G.size) (hc : 0 < copyCount G S cHi cLo u) :
    ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm (blowupCopy G S cHi cLo u hc)).1 = u := by
  unfold blowupCopy
  rw [Equiv.symm_apply_apply]

/-- **Blow-up max degree** (design §4): `maxDegree (blowupAsymFlag G S b a)
= a·maxDegree G`. Upper bound from `blowup_degree_le`; lower bound from a copy of
a high-degree `S`-vertex (exact `a·Δ`, `blowup_degree_of_mem`). -/
lemma blowup_maxDegree
    (G : Flag emptyType) {p : ℝ} (hAsym : IsAsymmetricBipartite p G)
    (a b : ℕ) (hb : 1 ≤ b) (hpb : (b : ℝ) * p ≤ a) :
    maxDegree (blowupAsymFlag G hAsym.choose b a) = maxDegree G * a := by
  set S := hAsym.choose with hS
  set G' := blowupAsymFlag G S b a with hG'
  -- Upper bound: every degree ≤ maxDegree G * a.
  have hupper : maxDegree G' ≤ maxDegree G * a := by
    rw [maxDegree]
    exact Finset.sup_le fun i _ => blowup_degree_le G hAsym a b hb hpb i
  refine le_antisymm hupper ?_
  -- Lower bound: split on maxDegree G.
  rcases Nat.eq_zero_or_pos (maxDegree G) with h0 | hpos
  · rw [h0]; simp
  · obtain ⟨u, huS⟩ := choose_nonempty_of_maxDegree_pos G hAsym hpos
    have hc : 0 < copyCount G S b a u := by
      have hcc : copyCount G S b a u = b := if_pos huS
      rw [hcc]; exact hb
    have horig : ((Fintype.equivFin (BlowVtx G S b a)).symm (blowupCopy G S b a u hc)).1 ∈ S := by
      rw [blowupCopy_orig]; exact huS
    have hdeg : (univ.filter (fun j => G'.graph.Adj (blowupCopy G S b a u hc) j)).card
        = maxDegree G * a := by
      rw [blowup_deg_mem_S G S b a hAsym.choose_spec.1 (blowupCopy G S b a u hc) horig,
          hAsym.choose_spec.2.1 _ horig]
    calc maxDegree G * a
        = (univ.filter (fun j => G'.graph.Adj (blowupCopy G S b a u hc) j)).card := hdeg.symm
      _ ≤ maxDegree G' := by
          rw [maxDegree]
          exact Finset.le_sup (f := fun v => (univ.filter (fun j => G'.graph.Adj v j)).card)
            (Finset.mem_univ _)

/-- **The blow-up is `IsAsymmetricBipartite 1`** (design §4): high side (copies of
`S`) exactly `aΔ`-regular, other side `≤ aΔ`. This is *exactly* the semiregular
structure `G'` has — NOT full `IsRegular`. The bound axiom is gated on this, which
`G'` satisfies unconditionally, so the honest headline stays "all
`IsAsymmetricBipartite p G`". -/
lemma blowup_isAsymmetricBipartite_one
    (G : Flag emptyType) {p : ℝ} (hAsym : IsAsymmetricBipartite p G)
    (a b : ℕ) (hb : 1 ≤ b) (hpb : (b : ℝ) * p ≤ a) :
    IsAsymmetricBipartite 1 (blowupAsymFlag G hAsym.choose b a) := by
  set S := hAsym.choose with hS
  set G' := blowupAsymFlag G S b a with hG'
  have hmax := blowup_maxDegree G hAsym a b hb hpb
  refine ⟨univ.filter (fun i => ((Fintype.equivFin (BlowVtx G S b a)).symm i).1 ∈ S), ?_, ?_, ?_⟩
  · -- Bipartite opposition.
    intro i j hadj
    rw [blowupAsymFlag_adj] at hadj
    simp only [mem_filter, mem_univ, true_and]
    exact hAsym.choose_spec.1 _ _ hadj
  · -- High side (copies of S) exactly = maxDegree G'.
    intro i hi
    rw [mem_filter] at hi
    rw [blowup_deg_mem_S G S b a hAsym.choose_spec.1 i hi.2,
        hAsym.choose_spec.2.1 _ hi.2, hmax]
  · -- Other side ≤ 1 · maxDegree G' (any degree ≤ maxDegree).
    intro i _
    rw [one_mul]
    exact_mod_cast degree_le_maxDegree G' i

/-! ## §2. CG4 SEC graph class + Δ parameter (L5C_design §1a)

Analog of `secBipGenGraphClassF`, but over `CG4` (plain edges): a 4-colour
**X-vertex-count `≤ 2Δ`** clause (X = colours {0,1}), and NO edge-colour clause. -/

/-- The **asymmetric CG4 SEC degree parameter**: max degree of the underlying
simple graph (`CG4.Str.1`). -/
noncomputable def secAsymGenDelta4 : GenGraphParam CG4 :=
  fun G => Finset.sup Finset.univ (fun v => (Finset.univ.filter (G.str.1.Adj v)).card)

/-- The **asymmetric CG4 SEC graph class**. A `GenFlag CG4 ∅` belongs iff its
X-vertex (colour {0,1} = strong-neighbourhood mark) count is `≤ 2·Δ`. No
edge-colour clause (plain edges) — simpler than the deterministic/bipartite class. -/
noncomputable def secAsymGenGraphClass4 : GenGraphClass CG4 :=
  fun G =>
    (Finset.univ.filter (fun v : Fin G.size => G.str.2 v = 0 ∨ G.str.2 v = 1)).card ≤
      2 * Finset.sup Finset.univ (fun v => (Finset.univ.filter (G.str.1.Adj v)).card)

/-! ## §3. Genuine algebra-level objective `O_asym_CG4_alg` (L5C_design §1a)

Over the F-free 334-flag basis `SecAsymBasis.flagBasis_asym` and the genuine
`AsymSecCertificate.target` — NOT the borrowed symmetric `SecBipartiteCertificate.target`. -/

/-- The ℝ coefficient for asymmetric CG4 basis index `k`: `-(target[k]/linearScale)`.
Same SDPA `min -(...)` sign convention as the deterministic/bipartite objectives. -/
noncomputable def O_asym_CG4_coef (k : Fin secAsymCG4BasisSize) : ℝ :=
  -((AsymSecCertificate.target[k.val]! : ℝ) /
    (AsymSecCertificate.linearScale : ℝ))

/-- **Algebra-level asymmetric CG4 SEC objective.**
`O_asym_CG4_alg = Σ_k O_asym_CG4_coef k • single (flagBasis_asym k)` over the 334-dim
F-free CG4 basis. -/
noncomputable def O_asym_CG4_alg : GenFlagAlg CG4 (GenFlagType.empty CG4) :=
  (Finset.univ : Finset (Fin secAsymCG4BasisSize)).sum
    (fun k => O_asym_CG4_coef k • GenFlagAlg.single (SecAsymBasis.flagBasis_asym k))

/-- **Eval-level basis expansion** (proof shape from the existing `_eq_target_sum`). -/
theorem phi_evalAlg_O_asym_CG4_eq_target_sum
    (phi : GenLimitFunctional CG4 (GenFlagType.empty CG4)
      secAsymGenGraphClass4 secAsymGenDelta4) :
    phi.evalAlg O_asym_CG4_alg
      = (Finset.univ : Finset (Fin secAsymCG4BasisSize)).sum
          (fun k => O_asym_CG4_coef k * phi.eval (SecAsymBasis.flagBasis_asym k)) := by
  unfold O_asym_CG4_alg
  rw [phi.evalAlg_finset_sum_genFlagAlg]
  exact Finset.sum_congr rfl fun k _ => by rw [phi.evalAlg_smul, phi.evalAlg_single]

/-! ## §4. CG4 host + sequence wiring (L5C_design §2.2)

The 4-colour, edge-colour-free analog of `SecBridge.colouredGraph22OfEdgeF`:
X/Y = strong-neighbourhood membership `N(a)∪N(b)` (colour {0,1} vs {2,3}), and a
component bit `x ∈ S` (comp0 = high side, comp1 = low side). The probe confirmed
the `a,b ∈ X` clause is immaterial, so we use the simpler `inX := Adj a x ∨ Adj b x`. -/

/-- The CG4 host of a graph `G` at a designated edge `{a,b}`, high-side witness `S`.
Colour = `2·(¬inX) + (x∈S ? 0 : 1)`: X-mark by the high bit (∈{0,1} iff `inX`),
component by the low bit. Plain (decoded) edges. -/
noncomputable def colouredGraph4OfEdgeAsym (G : Flag emptyType)
    (S : Finset (Fin G.size)) (a b : Fin G.size) : CGraph4 G.size where
  adj x y := decide (G.graph.Adj x y)
  vertexCol x :=
    if (G.graph.Adj a x ∨ G.graph.Adj b x) then
      (if x ∈ S then 0 else 1)
    else
      (if x ∈ S then 2 else 3)

/-- Host adjacency decodes to `G`-adjacency (`fromRel ∘ decide` collapses to the
original relation, since `Adj` is symmetric + irreflexive). -/
lemma colouredGraph4OfEdgeAsym_adj_iff (G : Flag emptyType)
    (S : Finset (Fin G.size)) (a b : Fin G.size) (x y : Fin G.size) :
    (colouredGraph4OfEdgeAsym G S a b).toGenFlag.str.1.Adj x y ↔ G.graph.Adj x y := by
  rw [CGraph4.toGenFlag_str]
  simp only [SimpleGraph.fromRel_adj, colouredGraph4OfEdgeAsym, decide_eq_true_eq]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact G.graph.symm h
  · intro h
    exact ⟨G.graph.ne_of_adj h, Or.inl h⟩

/-- Host X-vertices (colour ∈ {0,1}) are exactly the strong neighbourhood `N(a)∪N(b)`. -/
lemma colouredGraph4OfEdgeAsym_vertexCol_mem_X_iff (G : Flag emptyType)
    (S : Finset (Fin G.size)) (a b : Fin G.size) (x : Fin G.size) :
    ((colouredGraph4OfEdgeAsym G S a b).toGenFlag.str.2 x = 0 ∨
     (colouredGraph4OfEdgeAsym G S a b).toGenFlag.str.2 x = 1) ↔
      (G.graph.Adj a x ∨ G.graph.Adj b x) := by
  change ((colouredGraph4OfEdgeAsym G S a b).vertexCol x = 0 ∨
        (colouredGraph4OfEdgeAsym G S a b).vertexCol x = 1) ↔ _
  unfold colouredGraph4OfEdgeAsym
  by_cases hX : G.graph.Adj a x ∨ G.graph.Adj b x <;>
    by_cases hS : x ∈ S <;> simp only [hX, hS, if_true, if_false] <;> decide

/-- Host per-vertex degree equals the `G`-degree. -/
lemma colouredGraph4OfEdgeAsym_degree_filter (G : Flag emptyType)
    (S : Finset (Fin G.size)) (a b : Fin G.size) (v : Fin G.size) :
    (univ.filter (fun u => (colouredGraph4OfEdgeAsym G S a b).toGenFlag.str.1.Adj v u)).card
      = (univ.filter (fun u => G.graph.Adj v u)).card := by
  congr 1
  ext u
  simp only [mem_filter, mem_univ, true_and, colouredGraph4OfEdgeAsym_adj_iff]

/-- Host max degree equals `maxDegree G`. -/
lemma secAsymGenDelta4_colouredGraph4OfEdgeAsym (G : Flag emptyType)
    (S : Finset (Fin G.size)) (a b : Fin G.size) :
    secAsymGenDelta4 (colouredGraph4OfEdgeAsym G S a b).toGenFlag.forget = maxDegree G := by
  unfold secAsymGenDelta4 maxDegree
  exact Finset.sup_congr rfl
    (fun v _ => colouredGraph4OfEdgeAsym_degree_filter G S a b v)

/-- Extract the designated edge + high-side witness and build the CG4 host at index `k`. -/
noncomputable def asymF_seq_to_CGraph4 (p : ℝ)
    (seq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size)
    (hAsym : ∀ k, IsAsymmetricBipartite p (seq k).1) (k : ℕ) :
    CGraph4 (seq k).1.size :=
  colouredGraph4OfEdgeAsym (seq k).1 (hAsym k).choose
    ((edgeFinset (seq k).1).equivFin.symm (seq k).2).val.1
    ((edgeFinset (seq k).1).equivFin.symm (seq k).2).val.2

/-- **Asymmetric CG4 sequence → `GenFlag CG4 ∅` bridge.** -/
noncomputable def asymF_seq_to_genFlag (p : ℝ)
    (seq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size)
    (_hΔ : StrictMono (fun k => maxDegree (seq k).1))
    (hAsym : ∀ k, IsAsymmetricBipartite p (seq k).1) (k : ℕ) :
    GenFlag CG4 (GenFlagType.empty CG4) :=
  (asymF_seq_to_CGraph4 p seq hAsym k).toGenFlag

theorem secAsymGenDelta4_asymF_seq_to_genFlag (p : ℝ)
    (seq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size)
    (hΔ : StrictMono (fun k => maxDegree (seq k).1))
    (hAsym : ∀ k, IsAsymmetricBipartite p (seq k).1) (k : ℕ) :
    secAsymGenDelta4 (asymF_seq_to_genFlag p seq hΔ hAsym k).forget = maxDegree (seq k).1 :=
  secAsymGenDelta4_colouredGraph4OfEdgeAsym _ _ _ _

/-- **Class membership is a THEOREM** (design §3.4 / L5C_design §3.4): the host's
X-vertex set is `N(a)∪N(b)`, of size `≤ deg(a)+deg(b) ≤ 2Δ` — unconditional, no
regularity. This closes what was the retired CG22 regularity axiom. -/
theorem asymF_seq_to_genFlag_mem_class4 (p : ℝ)
    (seq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size)
    (hΔ : StrictMono (fun k => maxDegree (seq k).1))
    (hAsym : ∀ k, IsAsymmetricBipartite p (seq k).1) (k : ℕ) :
    secAsymGenGraphClass4 (asymF_seq_to_genFlag p seq hΔ hAsym k).forget := by
  set G := (seq k).1 with hG
  set a := ((edgeFinset G).equivFin.symm (seq k).2).val.1 with ha
  set b := ((edgeFinset G).equivFin.symm (seq k).2).val.2 with hb
  set S := (hAsym k).choose with hSdef
  unfold secAsymGenGraphClass4
  have hXset :
      (univ.filter (fun v => (asymF_seq_to_genFlag p seq hΔ hAsym k).forget.str.2 v = 0 ∨
          (asymF_seq_to_genFlag p seq hΔ hAsym k).forget.str.2 v = 1))
        = (univ.filter (fun x => G.graph.Adj a x ∨ G.graph.Adj b x)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and]
    exact colouredGraph4OfEdgeAsym_vertexCol_mem_X_iff G S a b x
  have hsup :
      Finset.sup univ (fun v => (univ.filter
        ((asymF_seq_to_genFlag p seq hΔ hAsym k).forget.str.1.Adj v)).card) = maxDegree G :=
    secAsymGenDelta4_colouredGraph4OfEdgeAsym G S a b
  rw [hXset, hsup, Finset.filter_or]
  calc ((univ.filter (fun x => G.graph.Adj a x)) ∪
        (univ.filter (fun x => G.graph.Adj b x))).card
      ≤ (univ.filter (fun x => G.graph.Adj a x)).card +
        (univ.filter (fun x => G.graph.Adj b x)).card := Finset.card_union_le _ _
    _ ≤ maxDegree G + maxDegree G :=
        add_le_add (degree_le_maxDegree G a) (degree_le_maxDegree G b)
    _ = 2 * maxDegree G := by ring

/-! ## §5. Functional plumbing + regularity gate -/

/-- Wrap an asymmetric CG4 sequence as a `GenDeltaIncreasingSeq`. -/
noncomputable def asymF_toGenDeltaSeq (p : ℝ)
    (seq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size)
    (hΔ : StrictMono (fun k => maxDegree (seq k).1))
    (hAsym : ∀ k, IsAsymmetricBipartite p (seq k).1) :
    GenDeltaIncreasingSeq CG4 (GenFlagType.empty CG4) secAsymGenDelta4 where
  seq k := asymF_seq_to_genFlag p seq hΔ hAsym k
  increasing := by
    intro a b hab
    change secAsymGenDelta4 (asymF_seq_to_genFlag p seq hΔ hAsym a).forget <
           secAsymGenDelta4 (asymF_seq_to_genFlag p seq hΔ hAsym b).forget
    rw [secAsymGenDelta4_asymF_seq_to_genFlag, secAsymGenDelta4_asymF_seq_to_genFlag]
    exact hΔ hab

/-- **Asymmetric CG4 phi construction** via `genLimit_functional_construction`.
**Restricted to `p = 1`** (design §3.1 "only for `IsAsymmetricBipartite 1`
sequences"): the CG4 cert is exact only at `p = 1` (46/75 objective coords scale by
`1/P` for `p < 1`), and the L5.C probe found the uniform-density identity FALSE for
`p < 1` (the development notes). R1b-2 obtains general-`p` coverage
by blowing `G` up to the exactly-`IsAsymmetricBipartite 1` graph `G'` and carrying
the bound back via the proven `blowup_transfer_uncond`. Class membership is
discharged by the *theorem* `asymF_seq_to_genFlag_mem_class4` (no axiom). -/
noncomputable def secAsymF_phi_construction
    (seq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size)
    (hΔ : StrictMono (fun k => maxDegree (seq k).1))
    (hAsym : ∀ k, IsAsymmetricBipartite 1 (seq k).1)
    (sub : ℕ → ℕ) (hsub : StrictMono sub) :
    GenLimitFunctional CG4 (GenFlagType.empty CG4)
      secAsymGenGraphClass4 secAsymGenDelta4 := by
  let cseq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size := fun k => seq (sub k)
  have hΔ' : StrictMono (fun k => maxDegree (cseq k).1) := hΔ.comp hsub
  have hAsym' : ∀ k, IsAsymmetricBipartite 1 (cseq k).1 := fun k => hAsym (sub k)
  exact genLimit_functional_construction CG4 (GenFlagType.empty CG4)
    secAsymGenGraphClass4 secAsymGenDelta4
    (asymF_toGenDeltaSeq 1 cseq hΔ' hAsym')
    (fun k => asymF_seq_to_genFlag_mem_class4 1 cseq hΔ' hAsym' k)

/-- The bound-axiom gate: `phi` arises from `secAsymF_phi_construction` on an
**`IsAsymmetricBipartite 1`** (regular-bipartite) Δ-increasing sequence. Restricted
to `p = 1` (the CG4 cert is only exact there — see `secAsymF_phi_construction`). The
spurious `(2−η)Δ²` min-degree prose is DROPPED (L5C_design §3.5: the class has no
min-degree family — the only structural gate is `IsAsymmetricBipartite 1`, carried
by `hAsym`). -/
def secAsymPhiRegular4
    (phi : GenLimitFunctional CG4 (GenFlagType.empty CG4)
      secAsymGenGraphClass4 secAsymGenDelta4) : Prop :=
  ∃ (seq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size)
    (hΔ : StrictMono (fun k => maxDegree (seq k).1))
    (hAsym : ∀ k, IsAsymmetricBipartite 1 (seq k).1)
    (sub : ℕ → ℕ) (hsub : StrictMono sub),
    phi = secAsymF_phi_construction seq hΔ hAsym sub hsub

/-! ## §6. The three sound axioms (design §3 / L5C_design §3)

These replace the retired CG22 FALSE combinatorial-identity axiom and the
VACUOUS borrowed-target eval-bound axiom (and drop the below-optimum
strict variant), resting on the genuine F-free CG4 cert and the **generic**
`C(2pΔ²,2)` normalizer. -/

/-- **Domain axiom — asymmetric SEC combinatorial identity, F-free CG4, generic
normalizer** (design §3.1). Replaces the retired FALSE, borrowed-target CG22
combinatorial-identity axiom.

## Statement

For every **genuinely regular** bipartite Δ-increasing sequence — gated on BOTH
`IsAsymmetricBipartite 1` (bipartition + high-side exact `= Δ`) AND `IsRegular`
(every vertex `= Δ`, so the low side is `= Δ` too, EXCLUDING the semiregular
`(Δ, ≤Δ)` graphs where the identity is false) — eventually in `k`,

    eIN(L(Gₖ)², vₖ) / C(2Δ_k², 2)
      ≤ (1/8)·Σ_j O_asym_CG4_coef j · d_j(host_k)  +  secAsymIdentityTol,

over the 334-flag F-free CG4 basis, with the **generic** real normalizer
`C(2Δ²,2) = Δ²(2Δ²−1)` (NOT the actual `C(Δ(L(G)²),2)` — that normalizer is itself
unsound: at K_{Δ,Δ} it drives the ratio to 1). The `1/8` prescale reflects the
4-colour construction eliminating the general case's factor-2 double count.

**Restricted to `p = 1` (soundness-critical).** The general-`p` form of this
statement — uniform `genUnlabelledDensity` RHS, generic `C(2pΔ²,2)` normalizer — was
**proved FALSE for `p < 1`** by the L5.C probe
(the development notes: at `p = 1/2` the LHS exceeds the RHS by
≈ +0.24, growing with Δ, because the objective's `p`-independence comes from
`unit_extension` degree-weighting that uniform density cannot capture — the generic
normalizer does not fix it). An axiom is false if ANY instance is false, so the
statement is confined to `p = 1`, where the probe CONFIRMED it holds. R1b-2 recovers
general-`p` via `blowup_transfer_uncond` (blow up `G` to the exactly-`IsAsymmetric
Bipartite 1` graph `G'`, apply this p=1 identity to `G'`, carry the bound back).

## Why this axiom is needed

As the deterministic/bipartite `_F` identity: the E_O-decomposition is exact only
asymptotically and the 10¹²-scaled integer-cert arithmetic step over 334 flags is
Lean-infeasible (per-k `native_decide` impossible on an abstract host). Exact and
tolerance-free forms are both false.

## Why this axiom is correct

At `p = 1` the F-free asymmetric problem (thesis §4.6 Molloy–Reed; PLAN §10b "no
F-subset") is all-vertex plain-eIN, which the generic normalizer matches, and the
CG4 cert is exact (no `1/P` coordinate scaling). The RHS is genuinely non-vacuous
(the F-free 334-flag cert evaluated in an F-free host with matching palette —
`SecAsymGates.g_vacuity`); the historic refuter K_{Δ,Δ} gives 0.25 ≤ 0.5687
(L5C_design §2.4). The per-vertex p=1 form was adversarially probe-confirmed across
8 regular-bipartite families (the development notes: worst 0.47723
≪ 0.5687, saturating; `L5C_probe/VERDICT.md`: the p=1 pipeline reproduces the known
K_{m,m} → 0.25 values with ≤ holding). The target-integerisation residue over 334
flags at the 1/8 prescale is ≈ 3.5×10⁻⁹ ≪ `secAsymIdentityTol = 10⁻⁵`. -/
axiom sec_combinatorial_identity_asymmetric_F
    (seq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size)
    (hΔ : StrictMono (fun k => maxDegree (seq k).1))
    (hAsym : ∀ k, IsAsymmetricBipartite 1 (seq k).1)
    (hReg : ∀ k, IsRegular (seq k).1) :
    ∀ᶠ k in Filter.atTop,
      (edgesInNeighbourhood (lineGraphSqFlag (seq k).1) (seq k).2 : ℝ) /
          ((maxDegree (seq k).1 : ℝ) ^ 2 *
            (2 * (maxDegree (seq k).1 : ℝ) ^ 2 - 1)) ≤
        (1/8 : ℝ) *
          (Finset.univ : Finset (Fin secAsymCG4BasisSize)).sum
            (fun j => O_asym_CG4_coef j *
              genUnlabelledDensity CG4 (GenFlagType.empty CG4)
                (SecAsymBasis.flagBasis_asym j)
                (asymF_seq_to_genFlag 1 seq hΔ hAsym k).forget
                secAsymGenDelta4)
        + secAsymIdentityTol

/-- **Domain axiom — asymmetric SEC eval-level upper bound (F-free CG4, loose,
non-vacuous)** (design §3.2). Replaces the retired VACUOUS borrowed-target CG22
eval-bound axiom. NO strict variant (design §3.3: the strict 4.548 sits below
the 4.5490937 CSDP optimum — artefact-unsupported).

## Statement

Every regularly-constructed CG4 functional (`secAsymPhiRegular4`) satisfies
`phi.evalAlg O_asym_CG4_alg ≤ 8·secAsymDensityBound` (= 4.5496).

## Why this axiom is needed

The per-block iso table lifting the `native_decide`-verified `AsymSecCertificate`
LDL blocks to the eval-cone inequality is missing (the ≥-5-flag blocker, shared
with the deterministic/bipartite cases).

## Why this axiom is correct

`8·secAsymDensityBound = 4.5496 > 4.5490937` (the CSDP optimum), margin +5.1×10⁻⁴
— the bound is ABOVE the certified optimum (unlike the dropped strict variant).
Non-vacuous: `O_asym_CG4_alg` is the genuine F-free objective in an F-free host
with matching palette (`SecAsymGates.g_vacuity` + `asym_objective_nonvacuous`).

**Restricted to `p = 1`** via the `secAsymPhiRegular4` gate (an `IsAsymmetric
Bipartite 1` construction): the CG4 cert is exact only at `p = 1` — 46/75 objective
coordinates scale by `1/P` for `p < 1`, so the bound is cert-supported only at
`p = 1`. The gate carries `IsAsymmetricBipartite 1` (the SDP's only structural
constraint family beyond CS + regularity + side-counts + normalizations; NO
min-degree family, L5C_design §3.7). -/
axiom phi_evalAlg_O_asym_CG4_le_bound
    (phi : GenLimitFunctional CG4 (GenFlagType.empty CG4)
      secAsymGenGraphClass4 secAsymGenDelta4)
    (hreg : secAsymPhiRegular4 phi) :
    phi.evalAlg O_asym_CG4_alg ≤ 8 * secAsymDensityBound

/-- **Domain axiom — asymmetric CG4 basis-flag locality** (design §3.6). Each of
the 334 size-5 F-free CG4 flags is a local ∅-flag for the class/degree pair.

## Statement / Why needed / Why correct

Same justification as the bipartite `_F` locality axiom (size-5 flag, IC ≤ Δ⁵,
÷C(Δ,5) bounded; `phi.convergence` needs per-flag locality, algorithmic witness
extraction deferred). Pentagon Q's proved `flagBasis_isLocalFlag` is the template;
334 flags (vs 3808). The X-vertex ≤ 2Δ class clause bounds the anchor budget. -/
axiom flagBasis_asym_isLocalFlag_F (k : Fin secAsymCG4BasisSize) :
    GenIsLocalFlag (GenFlagType.empty CG4) (SecAsymBasis.flagBasis_asym k)
      secAsymGenGraphClass4 secAsymGenDelta4

/-! ## §7. Anti-vacuity evidence (mandatory gate)

The old borrowed-target axiom's RHS was ≡ 0: every support flag was F-marked and
had density 0 in every F-free host (`SecAsymGates.oldConfig_vacuous`). Here a
genuine support flag has NONZERO objective coefficient AND strictly positive
density in a concrete CG4 host — the objective RHS is NOT identically zero. -/

theorem O_asym_CG4_coef_i25_ne_zero :
    O_asym_CG4_coef SecAsymGates.i25 ≠ 0 := by
  unfold O_asym_CG4_coef
  have hne : (AsymSecCertificate.target[25]! : ℤ) ≠ 0 := SecAsymGates.target_25_ne_zero
  have hscale : (AsymSecCertificate.linearScale : ℝ) ≠ 0 := by
    change ((1000000000000 : ℕ) : ℝ) ≠ 0; norm_num
  simp only [neg_ne_zero, ne_eq, div_eq_zero_iff, not_or]
  refine ⟨?_, hscale⟩
  exact_mod_cast hne

/-- **Anti-vacuity headline.** A genuine objective-support flag (index 25) has
nonzero coefficient and strictly positive density in a concrete CG4 host — the
asymmetric objective is genuinely non-vacuous (contrast the borrowed-target axiom,
`SecAsymGates.oldConfig_vacuous`). -/
theorem asym_objective_nonvacuous :
    O_asym_CG4_coef SecAsymGates.i25 ≠ 0 ∧
    0 < genUnlabelledDensity CG4 (GenFlagType.empty CG4)
      (SecAsymBasis.flagBasis_asym SecAsymGates.i25)
      (SecAsymBasis.flagBasis_asym SecAsymGates.i25) SecAsymGates.Δ5 :=
  ⟨O_asym_CG4_coef_i25_ne_zero, SecAsymGates.flag25_density_pos⟩

/-! ## §8. Density bridge (p = 1 form, design §3 item 7)

Threads the three sound axioms through `le_of_tendsto_of_tendsto`, mirroring
`Davey2024.SecBipartiteBridge.secBipF_density_bridge`. Any subsequential limit of
the generic-normalizer strong-neighbourhood density along a gated asymmetric
sequence is `≤ secAsymDensityBound + secAsymIdentityTol` (= 0.5687 + 10⁻⁵). -/
theorem secAsymF_density_bridge
    (seq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size)
    (hΔ : StrictMono (fun k => maxDegree (seq k).1))
    (hAsym : ∀ k, IsAsymmetricBipartite 1 (seq k).1)
    (hReg : ∀ k, IsRegular (seq k).1)
    (sub : ℕ → ℕ) (L : ℝ) (hsub : StrictMono sub)
    (htend : Filter.Tendsto (fun k =>
      (edgesInNeighbourhood (lineGraphSqFlag (seq (sub k)).1) (seq (sub k)).2 : ℝ) /
        ((maxDegree (seq (sub k)).1 : ℝ) ^ 2 *
          (2 * (maxDegree (seq (sub k)).1 : ℝ) ^ 2 - 1)))
      Filter.atTop (nhds L)) :
    L ≤ secAsymDensityBound + secAsymIdentityTol := by
  set phi := secAsymF_phi_construction seq hΔ hAsym sub hsub with hphi_def
  have hreg : secAsymPhiRegular4 phi :=
    ⟨seq, hΔ, hAsym, sub, hsub, hphi_def⟩
  have htend_diag : Filter.Tendsto (fun n =>
      (edgesInNeighbourhood (lineGraphSqFlag (seq (sub (phi.sub n))).1)
        (seq (sub (phi.sub n))).2 : ℝ) /
        ((maxDegree (seq (sub (phi.sub n))).1 : ℝ) ^ 2 *
          (2 * (maxDegree (seq (sub (phi.sub n))).1 : ℝ) ^ 2 - 1)))
      Filter.atTop (nhds L) :=
    htend.comp phi.sub_strictMono.tendsto_atTop
  have hIdent := sec_combinatorial_identity_asymmetric_F seq hΔ hAsym hReg
  have hcompTop : Filter.Tendsto (fun n => sub (phi.sub n))
      Filter.atTop Filter.atTop :=
    (hsub.comp phi.sub_strictMono).tendsto_atTop
  have hIdent_diag : ∀ᶠ n in Filter.atTop,
      (edgesInNeighbourhood (lineGraphSqFlag (seq (sub (phi.sub n))).1)
        (seq (sub (phi.sub n))).2 : ℝ) /
        ((maxDegree (seq (sub (phi.sub n))).1 : ℝ) ^ 2 *
          (2 * (maxDegree (seq (sub (phi.sub n))).1 : ℝ) ^ 2 - 1)) ≤
      (1/8 : ℝ) *
        (Finset.univ : Finset (Fin secAsymCG4BasisSize)).sum
          (fun j => O_asym_CG4_coef j *
            genUnlabelledDensity CG4 (GenFlagType.empty CG4)
              (SecAsymBasis.flagBasis_asym j)
              (asymF_seq_to_genFlag 1 seq hΔ hAsym (sub (phi.sub n))).forget
              secAsymGenDelta4)
      + secAsymIdentityTol :=
    hcompTop.eventually hIdent
  set uD : Fin secAsymCG4BasisSize → ℕ → ℝ := fun j n =>
    genUnlabelledDensity CG4 (GenFlagType.empty CG4)
      (SecAsymBasis.flagBasis_asym j)
      (asymF_seq_to_genFlag 1 seq hΔ hAsym (sub (phi.sub n))).forget
      secAsymGenDelta4 with huD_def
  have huD_tend : ∀ j : Fin secAsymCG4BasisSize,
      Filter.Tendsto (uD j) Filter.atTop
        (nhds (phi.eval (SecAsymBasis.flagBasis_asym j))) := by
    intro j
    have hconv := phi.convergence (SecAsymBasis.flagBasis_asym j)
      (flagBasis_asym_isLocalFlag_F j)
    -- phi.seq.seq = asymF_seq_to_genFlag on the (sub∘·) composed sequence.
    exact hconv
  have hSum_tend : Filter.Tendsto
      (fun n => (1/8 : ℝ) *
        (Finset.univ : Finset (Fin secAsymCG4BasisSize)).sum
          (fun j => O_asym_CG4_coef j * uD j n) + secAsymIdentityTol)
      Filter.atTop
      (nhds ((1/8 : ℝ) *
        (Finset.univ : Finset (Fin secAsymCG4BasisSize)).sum
          (fun j => O_asym_CG4_coef j * phi.eval (SecAsymBasis.flagBasis_asym j))
        + secAsymIdentityTol)) := by
    apply Filter.Tendsto.add_const
    apply Filter.Tendsto.const_mul
    apply tendsto_finset_sum
    intro j _
    exact (huD_tend j).const_mul (O_asym_CG4_coef j)
  have hL_le : L ≤ (1/8 : ℝ) *
      (Finset.univ : Finset (Fin secAsymCG4BasisSize)).sum
        (fun j => O_asym_CG4_coef j * phi.eval (SecAsymBasis.flagBasis_asym j))
      + secAsymIdentityTol :=
    le_of_tendsto_of_tendsto htend_diag hSum_tend hIdent_diag
  have hAggr := phi_evalAlg_O_asym_CG4_eq_target_sum phi
  have hBound := phi_evalAlg_O_asym_CG4_le_bound phi hreg
  rw [hAggr] at hBound
  -- L ≤ (1/8)·φ.evalAlg O + tol ≤ (1/8)·(8·bound) + tol = bound + tol.
  linarith [hL_le, hBound]

/-! ## §9. Stage A — per-graph reduction (R1b-2)

The density bridge above is a *limit* statement over `IsAsymmetricBipartite 1`
sequences. Here we turn it into a **per-graph** bound (§9.1–§9.3, generic
`Δ²(2Δ²−1)` normalizer), then carry it to a **general-`p`** per-edge bound on
`G` via the proven blow-up transfer (`blowup_transfer_uncond`) at the clean scale
`2·⌈pΔ⌉·Δ` (§9.4–§9.5). All additive: nothing in the old chain is touched. -/

/-- **Exactly-`(Δ, ⌊pΔ⌋)`-biregular** (soundness gate for the Route-1 arm): the high
side is exactly `Δ`-regular AND the low side is exactly `⌊pΔ⌋`-regular. This is the
STRENGTHENING of `IsAsymmetricBipartite p` (whose low side is only `≤ pΔ`) needed so
the blow-up `G'` is *genuinely* `IsRegular` — the gate the re-gated identity
`sec_combinatorial_identity_asymmetric_F` now demands (the semiregular `(Δ, ≤Δ)`
graphs, on which the uniform-density identity is false, are excluded). -/
def IsBiregularFloor (p : ℝ) (G : Flag emptyType) : Prop :=
  ∃ S : Finset (Fin G.size),
    (∀ u v, G.graph.Adj u v → (u ∈ S ↔ v ∉ S)) ∧
    (∀ u ∈ S, (Finset.univ.filter (fun v => G.graph.Adj u v)).card = maxDegree G) ∧
    (∀ u, u ∉ S → (Finset.univ.filter (fun v => G.graph.Adj u v)).card
        = Nat.floor (p * (maxDegree G : ℝ)))

/-- An exactly-biregular-floor graph is in particular `IsAsymmetricBipartite p`
(the exact low degree `= ⌊pΔ⌋ ≤ pΔ` supplies the `≤ pΔ` clause). -/
theorem IsBiregularFloor.toAsym {p : ℝ} {G : Flag emptyType} (hp : 0 ≤ p)
    (h : IsBiregularFloor p G) : IsAsymmetricBipartite p G := by
  obtain ⟨S, hopp, hhi, hlo⟩ := h
  refine ⟨S, hopp, hhi, fun u hu => ?_⟩
  rw [hlo u hu]
  exact Nat.floor_le (mul_nonneg hp (Nat.cast_nonneg _))

/-- **Monotonicity of `IsAsymmetricBipartite` in `p`.** Weakening `p ≤ p'` keeps
the predicate (same bipartition witness; the low-side degree bound only relaxes). -/
lemma IsAsymmetricBipartite.mono {p p' : ℝ} {G : Flag emptyType}
    (h : IsAsymmetricBipartite p G) (hpp : p ≤ p') : IsAsymmetricBipartite p' G := by
  obtain ⟨S, hopp, hhi, hlo⟩ := h
  refine ⟨S, hopp, hhi, fun u hu => ?_⟩
  exact le_trans (hlo u hu) (mul_le_mul_of_nonneg_right hpp (Nat.cast_nonneg _))

/-- The generic normalizer density `eIN(L(G)²,v) / (Δ²(2Δ²−1))` lies in `[0,4]`
for `Δ ≥ 1` (`eIN ≤ (2Δ²)² = 4Δ⁴ ≤ 4·Δ²(2Δ²−1)`). -/
private theorem genDensity_in_Icc (G : Flag emptyType)
    (v : Fin (lineGraphSqFlag G).size) (hΔ : 1 ≤ maxDegree G) :
    (edgesInNeighbourhood (lineGraphSqFlag G) v : ℝ) /
      ((maxDegree G : ℝ) ^ 2 * (2 * (maxDegree G : ℝ) ^ 2 - 1)) ∈ Set.Icc 0 4 := by
  have hΔr : (1 : ℝ) ≤ (maxDegree G : ℝ) := by exact_mod_cast hΔ
  have hΔsq : (1 : ℝ) ≤ (maxDegree G : ℝ) ^ 2 := by nlinarith
  have hnorm_pos : (0 : ℝ) <
      (maxDegree G : ℝ) ^ 2 * (2 * (maxDegree G : ℝ) ^ 2 - 1) := by nlinarith
  refine ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hnorm_pos), ?_⟩
  rw [div_le_iff₀ hnorm_pos]
  have hein : (edgesInNeighbourhood (lineGraphSqFlag G) v : ℝ) ≤
      (maxDegree (lineGraphSqFlag G) : ℝ) ^ 2 := by
    exact_mod_cast edgesInNeighbourhood_le_maxDegree_sq (lineGraphSqFlag G) v
  have hmd : (maxDegree (lineGraphSqFlag G) : ℝ) ≤ 2 * (maxDegree G : ℝ) ^ 2 := by
    exact_mod_cast lineGraphSq_maxDegree_le G
  have hmd_nn : (0 : ℝ) ≤ (maxDegree (lineGraphSqFlag G) : ℝ) := Nat.cast_nonneg _
  nlinarith [hein, hmd, hmd_nn, hΔsq, sq_nonneg (maxDegree G : ℝ)]

/-- **§9.1 — generic-normalizer Bolzano–Weierstrass.** Along a `Δ`-increasing
sequence, some subsequence of `eIN(L(G)²,v) / (Δ²(2Δ²−1))` converges. -/
theorem secAsym_generic_convergent_subseq
    (seq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size)
    (hΔ : StrictMono (fun k => maxDegree (seq k).1)) :
    ∃ (sub : ℕ → ℕ) (L : ℝ), StrictMono sub ∧ 0 ≤ L ∧
      Filter.Tendsto
        (fun k => (edgesInNeighbourhood (lineGraphSqFlag (seq (sub k)).1) (seq (sub k)).2 : ℝ) /
          ((maxDegree (seq (sub k)).1 : ℝ) ^ 2 *
            (2 * (maxDegree (seq (sub k)).1 : ℝ) ^ 2 - 1)))
        Filter.atTop (nhds L) := by
  let seq' := fun k => seq (k + 1)
  have hΔ' : StrictMono (fun k => maxDegree (seq' k).1) :=
    fun a b hab => hΔ (by omega : a + 1 < b + 1)
  have hΔ_ge : ∀ k, 1 ≤ maxDegree (seq' k).1 := by
    intro k
    have h1 : 1 ≤ k + 1 := by omega
    exact le_trans h1 (StrictMono.id_le hΔ (k + 1))
  have hmem : ∀ k, (edgesInNeighbourhood (lineGraphSqFlag (seq' k).1) (seq' k).2 : ℝ) /
      ((maxDegree (seq' k).1 : ℝ) ^ 2 * (2 * (maxDegree (seq' k).1 : ℝ) ^ 2 - 1))
      ∈ Set.Icc 0 4 :=
    fun k => genDensity_in_Icc (seq' k).1 (seq' k).2 (hΔ_ge k)
  obtain ⟨L, hL_mem, ψ, hψ_mono, hψ_tend⟩ := isCompact_Icc.tendsto_subseq hmem
  refine ⟨fun k => ψ k + 1, L, ?_, hL_mem.1, hψ_tend⟩
  intro a b hab
  exact Nat.add_lt_add_right (hψ_mono hab) 1

/-- **§9.2 — p=1 per-graph bound from the density bridge.** For every `eps > 0`,
some `D₀` makes every `IsAsymmetricBipartite 1` graph with `Δ ≥ D₀` satisfy, at
every `L(G)²`-vertex, `eIN ≤ (0.5687 + 10⁻⁵ + eps)·(Δ²(2Δ²−1))` (generic
normalizer). Contradiction framework mirroring the symmetric bipartite
`bound_from_limit` shape, fed by `secAsymF_density_bridge`. -/
theorem secAsymF_p1_bound_from_limit (eps : ℝ) (heps : 0 < eps) :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      IsAsymmetricBipartite 1 G → IsRegular G → D₀ ≤ maxDegree G →
      ∀ v : Fin (lineGraphSqFlag G).size,
        (edgesInNeighbourhood (lineGraphSqFlag G) v : ℝ) ≤
          (secAsymDensityBound + secAsymIdentityTol + eps) *
            ((maxDegree G : ℝ) ^ 2 * (2 * (maxDegree G : ℝ) ^ 2 - 1)) := by
  by_contra h_not
  push_neg at h_not
  set c : ℝ := secAsymDensityBound + secAsymIdentityTol with hc_def
  have h_exists : ∀ D : ℕ, ∃ (q : Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size),
      IsAsymmetricBipartite 1 q.1 ∧ IsRegular q.1 ∧ D < maxDegree q.1 ∧
      (c + eps) * ((maxDegree q.1 : ℝ) ^ 2 * (2 * (maxDegree q.1 : ℝ) ^ 2 - 1)) <
        (edgesInNeighbourhood (lineGraphSqFlag q.1) q.2 : ℝ) := by
    intro D
    obtain ⟨G, hAsym, hReg, hG_deg, v, hv⟩ := h_not (D + 1)
    exact ⟨⟨G, v⟩, hAsym, hReg, show D < maxDegree G by omega, hv⟩
  let buildSeq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size :=
    Nat.rec (h_exists 1).choose
      (fun _ q => (h_exists (maxDegree q.1)).choose)
  have hΔ_strict : StrictMono (fun k => maxDegree (buildSeq k).1) :=
    strictMono_nat_of_lt_succ fun k => (h_exists (maxDegree (buildSeq k).1)).choose_spec.2.2.1
  have hΔ_ge1 : ∀ k, 1 ≤ maxDegree (buildSeq k).1 := by
    intro k
    have h2 : 2 ≤ maxDegree (buildSeq 0).1 :=
      Nat.succ_le_of_lt (h_exists 1).choose_spec.2.2.1
    have hk : 2 ≤ maxDegree (buildSeq k).1 := le_trans h2 (by
      rcases k with _ | k
      · exact le_refl _
      · exact le_of_lt (hΔ_strict (Nat.zero_lt_succ k)))
    omega
  let shiftSeq : ℕ → Σ (G : Flag emptyType), Fin (lineGraphSqFlag G).size :=
    fun k => buildSeq (k + 1)
  have hΔ_shift : StrictMono (fun k => maxDegree (shiftSeq k).1) :=
    fun a b hab => hΔ_strict (by omega : a + 1 < b + 1)
  have hAsym_shift : ∀ k, IsAsymmetricBipartite 1 (shiftSeq k).1 :=
    fun k => (h_exists (maxDegree (buildSeq k).1)).choose_spec.1
  have hReg_shift : ∀ k, IsRegular (shiftSeq k).1 :=
    fun k => (h_exists (maxDegree (buildSeq k).1)).choose_spec.2.1
  obtain ⟨sub, L, hsub_mono, hL_nn, hL_tend⟩ :=
    secAsym_generic_convergent_subseq shiftSeq hΔ_shift
  have h_density_gt : ∀ n, 1 ≤ n →
      c + eps < (edgesInNeighbourhood (lineGraphSqFlag (buildSeq n).1) (buildSeq n).2 : ℝ) /
        ((maxDegree (buildSeq n).1 : ℝ) ^ 2 * (2 * (maxDegree (buildSeq n).1 : ℝ) ^ 2 - 1)) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hnorm_pos : (0 : ℝ) <
        (maxDegree (buildSeq (m + 1)).1 : ℝ) ^ 2 *
          (2 * (maxDegree (buildSeq (m + 1)).1 : ℝ) ^ 2 - 1) := by
      have hge := hΔ_ge1 (m + 1)
      have hr : (1 : ℝ) ≤ (maxDegree (buildSeq (m + 1)).1 : ℝ) := by exact_mod_cast hge
      have h1 : (0 : ℝ) < (maxDegree (buildSeq (m + 1)).1 : ℝ) ^ 2 := by nlinarith [hr]
      have h2 : (0 : ℝ) < 2 * (maxDegree (buildSeq (m + 1)).1 : ℝ) ^ 2 - 1 := by nlinarith [hr]
      exact mul_pos h1 h2
    rw [lt_div_iff₀ hnorm_pos]
    exact (h_exists (maxDegree (buildSeq m).1)).choose_spec.2.2.2
  have hL_ge : c + eps ≤ L := by
    apply ge_of_tendsto hL_tend
    rw [Filter.eventually_atTop]
    exact ⟨1, fun k _ => le_of_lt (h_density_gt (sub k + 1) (by omega))⟩
  have hbridge := secAsymF_density_bridge shiftSeq hΔ_shift hAsym_shift hReg_shift sub L hsub_mono hL_tend
  linarith [hL_ge, hbridge]

/-- **§9.3 — p=1 per-graph bound at the fixed slack `eps = secAsymIdentityTol`.**
Then the constant `C := 0.5687 + 2·10⁻⁵ ≤ 1 − secAsymBipartiteSparsity`. -/
theorem secAsymF_p1_vertex_bound :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      IsAsymmetricBipartite 1 G → IsRegular G → D₀ ≤ maxDegree G →
      ∀ v : Fin (lineGraphSqFlag G).size,
        (edgesInNeighbourhood (lineGraphSqFlag G) v : ℝ) ≤
          (1 - secAsymBipartiteSparsity) *
            ((maxDegree G : ℝ) ^ 2 * (2 * (maxDegree G : ℝ) ^ 2 - 1)) := by
  obtain ⟨D₀, hD₀⟩ := secAsymF_p1_bound_from_limit secAsymIdentityTol (by
    unfold secAsymIdentityTol; norm_num)
  refine ⟨D₀, fun G hAsym hReg hG v => ?_⟩
  have hb := hD₀ G hAsym hReg hG v
  have hle : secAsymDensityBound + secAsymIdentityTol + secAsymIdentityTol
      ≤ 1 - secAsymBipartiteSparsity := by
    rw [secAsymBipartiteSparsity_val, secAsymDensityBound_val]
    unfold secAsymIdentityTol; norm_num
  have hnorm_nn : (0 : ℝ) ≤
      (maxDegree G : ℝ) ^ 2 * (2 * (maxDegree G : ℝ) ^ 2 - 1) := by
    rcases Nat.eq_zero_or_pos (maxDegree G) with h0 | hpos
    · simp [h0]
    · have hr : (1 : ℝ) ≤ (maxDegree G : ℝ) := by exact_mod_cast hpos
      have h1 : (0 : ℝ) ≤ (maxDegree G : ℝ) ^ 2 := sq_nonneg _
      have h2 : (0 : ℝ) ≤ 2 * (maxDegree G : ℝ) ^ 2 - 1 := by nlinarith [hr]
      exact mul_nonneg h1 h2
  calc (edgesInNeighbourhood (lineGraphSqFlag G) v : ℝ)
      ≤ (secAsymDensityBound + secAsymIdentityTol + secAsymIdentityTol) *
          ((maxDegree G : ℝ) ^ 2 * (2 * (maxDegree G : ℝ) ^ 2 - 1)) := hb
    _ ≤ (1 - secAsymBipartiteSparsity) *
          ((maxDegree G : ℝ) ^ 2 * (2 * (maxDegree G : ℝ) ^ 2 - 1)) :=
        mul_le_mul_of_nonneg_right hle hnorm_nn

/-! ## §9.4 — general-`p` per-vertex bound (Nat scale `D = 2⌊pΔ⌋·Δ`)

The p = 1 bound `secAsymF_p1_vertex_bound` is carried to a **general-`p`** host `G`
per-graph via the proven blow-up transfer. Given `IsAsymmetricBipartite p G`, set
`a = ⌊pΔ⌋`, `b = Δ`; then `IsAsymmetricBipartite (a/b) G` holds (integer degrees:
`deg ≤ pΔ ⟹ deg ≤ ⌊pΔ⌋`), and the blow-up `G' = blowupAsymFlag G · Δ a` is
`IsAsymmetricBipartite 1` with `maxDegree G' = Δ·a =: m`. Applying the p = 1 bound
to `G'` (normalizer `m²(2m²−1)`) and the transfer (LHS normalizer `m(2m−1)`,
generic p-form `pΔ²(2pΔ²−1)` with `(a/b)Δ² = m`) gives, per edge `f`,
`eIN(L(G)²,f) ≤ (1−σ)·m(2m−1) = (1−σ)·C(2m,2)`. The clean Nat scale `D = 2m`
satisfies `Δ(L(G)²) ≤ D` (asymmetric max-degree at `p' = a/b`) and `D ≤ 2pΔ²`
(from `⌊pΔ⌋ ≤ pΔ`), so the whole colouring step runs at a Nat binomial. -/
theorem secAsymF_biregular_vertex_bound (p : ℝ) (hp1 : 0 < p) (hp2 : p ≤ 1) :
    ∃ D₀ : ℕ, ∀ G : Flag emptyType,
      IsBiregularFloor p G → D₀ ≤ maxDegree G →
      ∃ D : ℕ, maxDegree G ≤ D ∧ maxDegree (lineGraphSqFlag G) ≤ D ∧
        (D : ℝ) ≤ 2 * p * (maxDegree G : ℝ) ^ 2 ∧
        (∀ f : Fin (lineGraphSqFlag G).size,
          (edgesInNeighbourhood (lineGraphSqFlag G) f : ℝ) ≤
            (1 - secAsymBipartiteSparsity) * (Nat.choose D 2 : ℝ)) := by
  obtain ⟨Dp1, hDp1⟩ := secAsymF_p1_vertex_bound
  refine ⟨max (max Dp1 (Nat.ceil (1 / p))) 1, fun G hbireg hG => ?_⟩
  have hAsym : IsAsymmetricBipartite p G := hbireg.toAsym hp1.le
  obtain ⟨Sbr, hSbr_opp, hSbr_hi, hSbr_lo⟩ := hbireg
  have hΔ1 : 1 ≤ maxDegree G := le_trans (le_max_right _ _) hG
  have hΔDp1 : Dp1 ≤ maxDegree G :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hG
  have hΔceil : Nat.ceil (1 / p) ≤ maxDegree G :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hG
  set Δ := maxDegree G with hΔdef
  have hΔr : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ1
  have hΔpos : (0 : ℝ) < (Δ : ℝ) := by linarith
  have hΔne : (Δ : ℝ) ≠ 0 := ne_of_gt hΔpos
  -- `pΔ ≥ 1` from `Δ ≥ ⌈1/p⌉`
  have hpΔ1 : (1 : ℝ) ≤ p * (Δ : ℝ) := by
    have h1 : (1 : ℝ) / p ≤ (Δ : ℝ) := by
      calc (1 : ℝ) / p ≤ (Nat.ceil (1 / p) : ℝ) := Nat.le_ceil _
        _ ≤ (Δ : ℝ) := by exact_mod_cast hΔceil
    rw [div_le_iff₀ hp1] at h1; linarith
  set a := Nat.floor (p * (Δ : ℝ)) with hadef
  have ha1 : 1 ≤ a := Nat.le_floor (by exact_mod_cast hpΔ1)
  have haΔr : (a : ℝ) ≤ p * (Δ : ℝ) := Nat.floor_le (by positivity)
  have hapos : 0 < a := ha1
  have hab : a ≤ Δ := by
    have hle : p * (Δ : ℝ) ≤ (Δ : ℝ) := by nlinarith [hp2, hΔr, hp1]
    calc a = Nat.floor (p * (Δ : ℝ)) := hadef
      _ ≤ Nat.floor ((Δ : ℝ)) := Nat.floor_mono hle
      _ = Δ := Nat.floor_natCast Δ
  -- The rationalised predicate `IsAsymmetricBipartite (a/Δ) G`.
  have hpb : (Δ : ℝ) * ((a : ℝ) / (Δ : ℝ)) ≤ (a : ℝ) := le_of_eq (by field_simp)
  have hAsym' : IsAsymmetricBipartite ((a : ℝ) / (Δ : ℝ)) G := by
    refine ⟨hAsym.choose, hAsym.choose_spec.1, hAsym.choose_spec.2.1, ?_⟩
    intro u hu
    have hd := hAsym.choose_spec.2.2 u hu
    have hdn : (Finset.univ.filter (fun v => G.graph.Adj u v)).card ≤ a := Nat.le_floor hd
    have hdr : ((Finset.univ.filter (fun v => G.graph.Adj u v)).card : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast hdn
    calc ((Finset.univ.filter (fun v => G.graph.Adj u v)).card : ℝ)
        ≤ (a : ℝ) := hdr
      _ = (a : ℝ) / (Δ : ℝ) * (Δ : ℝ) := by field_simp
  -- `maxDegree G' = Δ·a`.
  have hmaxG' : maxDegree (blowupAsymFlag G hAsym'.choose Δ a) = Δ * a :=
    blowup_maxDegree G hAsym' a Δ hΔ1 hpb
  -- The `p = 1` bound applies to `G'` (Δ' = Δ·a ≥ Dp1).
  have hDp1_le : Dp1 ≤ maxDegree (blowupAsymFlag G hAsym'.choose Δ a) := by
    rw [hmaxG']
    exact le_trans hΔDp1 (Nat.le_mul_of_pos_right Δ hapos)
  have hAsym1 : IsAsymmetricBipartite 1 (blowupAsymFlag G hAsym'.choose Δ a) :=
    blowup_isAsymmetricBipartite_one G hAsym' a Δ hΔ1 hpb
  -- **Exact low-degree of the chosen bipartition** `hAsym'.choose`: for `u` on the
  -- low side, `deg_G(u) ≤ a` (the `a/Δ` clause) and biregularity forces
  -- `deg_G(u) ∈ {Δ, a}`; the `Δ` branch needs `Δ ≤ a`, hence (with `a ≤ Δ`) `a = Δ`,
  -- so `deg_G(u) = a` either way. This is the fact `IsAsymmetricBipartite` alone
  -- lacks and `IsBiregularFloor` supplies — the reason the blow-up is `IsRegular`.
  have hLoExact : ∀ u, u ∉ hAsym'.choose →
      (univ.filter (fun v => G.graph.Adj u v)).card = a := by
    intro u hu
    have hle_real : ((univ.filter (fun v => G.graph.Adj u v)).card : ℝ)
        ≤ (a : ℝ) / (Δ : ℝ) * (maxDegree G : ℝ) := hAsym'.choose_spec.2.2 u hu
    have hdeg_le : (univ.filter (fun v => G.graph.Adj u v)).card ≤ a := by
      have hr : ((univ.filter (fun v => G.graph.Adj u v)).card : ℝ) ≤ (a : ℝ) := by
        have heq : (a : ℝ) / (Δ : ℝ) * (maxDegree G : ℝ) = (a : ℝ) := by
          rw [← hΔdef]; field_simp
        rw [heq] at hle_real; exact hle_real
      exact_mod_cast hr
    by_cases hus : u ∈ Sbr
    · have hd : (univ.filter (fun v => G.graph.Adj u v)).card = Δ := hSbr_hi u hus
      omega
    · exact hSbr_lo u hus
  -- The blow-up is **genuinely regular** (low side lifted to exactly `Δ·a`),
  -- the gate the re-gated `secAsymF_p1_vertex_bound` now demands.
  have hreg1 : IsRegular (blowupAsymFlag G hAsym'.choose Δ a) :=
    blowup_isRegular G hAsym'.choose Δ a hAsym'.choose_spec.1
      hAsym'.choose_spec.2.1 hLoExact (by rw [hΔdef]; ring)
  -- Scale + normalizer abbreviations.
  set D : ℕ := 2 * (Δ * a) with hDdef
  have hmr : ((Δ * a : ℕ) : ℝ) = (Δ : ℝ) * (a : ℝ) := by push_cast; ring
  have hmpos : (1 : ℝ) ≤ (Δ : ℝ) * (a : ℝ) := by
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
    nlinarith [hΔr, this]
  have hN1pos : (0 : ℝ) < (Δ : ℝ) * (a : ℝ) * (2 * ((Δ : ℝ) * (a : ℝ)) - 1) := by
    nlinarith [hmpos]
  have hN2pos : (0 : ℝ) <
      ((Δ : ℝ) * (a : ℝ)) ^ 2 * (2 * ((Δ : ℝ) * (a : ℝ)) ^ 2 - 1) := by
    nlinarith [hmpos]
  -- The three scale facts.
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · -- `Δ ≤ D`
    rw [hDdef]
    exact le_trans (Nat.le_mul_of_pos_right Δ hapos) (by omega)
  · -- `Δ(L(G)²) ≤ D`
    have hmd := asymmetric_lineGraphSq_maxDegree_le
      (show (0 : ℝ) < (a : ℝ) / (Δ : ℝ) by positivity)
      (show (a : ℝ) / (Δ : ℝ) ≤ 1 by rw [div_le_one hΔpos]; exact_mod_cast hab) hAsym'
    have hDr : (D : ℝ) = 2 * ((a : ℝ) / (Δ : ℝ)) * (Δ : ℝ) ^ 2 := by
      rw [hDdef]; push_cast; field_simp
    have hle : (maxDegree (lineGraphSqFlag G) : ℝ) ≤ (D : ℝ) := by rw [hDr]; exact hmd
    exact_mod_cast hle
  · -- `D ≤ 2pΔ²`
    rw [hDdef]; push_cast
    nlinarith [haΔr, hΔr, hΔpos]
  · -- per-edge sparsity
    intro f
    obtain ⟨f', htrans⟩ := blowup_transfer_uncond ha1 hΔ1 hab hΔdef.le hAsym' f
    have hp1b := hDp1 (blowupAsymFlag G hAsym'.choose Δ a) hAsym1 hreg1 hDp1_le f'
    rw [hmaxG'] at hp1b
    rw [hmr] at hp1b
    -- Denominator rewrites.
    have hLden : (a : ℝ) / (Δ : ℝ) * (Δ : ℝ) ^ 2 *
          (2 * ((a : ℝ) / (Δ : ℝ)) * (Δ : ℝ) ^ 2 - 1)
        = (Δ : ℝ) * (a : ℝ) * (2 * ((Δ : ℝ) * (a : ℝ)) - 1) := by
      field_simp
    have hRden : (a : ℝ) ^ 2 * (Δ : ℝ) ^ 2 * (2 * (a : ℝ) ^ 2 * (Δ : ℝ) ^ 2 - 1)
        = ((Δ : ℝ) * (a : ℝ)) ^ 2 * (2 * ((Δ : ℝ) * (a : ℝ)) ^ 2 - 1) := by ring
    rw [hLden, hRden] at htrans
    -- From p = 1 bound: RHS ratio ≤ 1 − σ.
    have hf'div : (edgesInNeighbourhood
          (lineGraphSqFlag (blowupAsymFlag G hAsym'.choose Δ a)) f' : ℝ) /
            (((Δ : ℝ) * (a : ℝ)) ^ 2 * (2 * ((Δ : ℝ) * (a : ℝ)) ^ 2 - 1))
          ≤ 1 - secAsymBipartiteSparsity := by
      rw [div_le_iff₀ hN2pos]; linarith [hp1b]
    have hchain : (edgesInNeighbourhood (lineGraphSqFlag G) f : ℝ) /
          ((Δ : ℝ) * (a : ℝ) * (2 * ((Δ : ℝ) * (a : ℝ)) - 1))
        ≤ 1 - secAsymBipartiteSparsity := le_trans htrans hf'div
    rw [div_le_iff₀ hN1pos] at hchain
    -- Rewrite the binomial normalizer.
    have hchoose : (Nat.choose D 2 : ℝ)
        = (Δ : ℝ) * (a : ℝ) * (2 * ((Δ : ℝ) * (a : ℝ)) - 1) := by
      rw [hDdef, Nat.cast_choose_two]; push_cast; ring
    rw [hchoose]
    exact hchain

end  -- noncomputable section

end Davey2024.SecAsymmetricBipartiteBridge
