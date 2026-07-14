import DaveyThesis2024.StrongEdgeColouring
import DaveyThesis2024.SecAsymmetricBipartiteBridge

/-!
# Route 1 — Asymmetric blow-up and the σ-transfer lemma (b1-repair L5.C)

This module formalises the **proven** transfer lemma of
the development notes: for a `(Δ, pΔ)`-biregular bipartite
host `G` (`p = a/b`, `gcd(a,b)=1`), the **asymmetric blow-up** `G'` — replace each
component-0 vertex by `b` copies and each component-1 vertex by `a` copies — is an
`aΔ`-regular bipartite graph, and the σ-normalised neighbourhood-edge density of the
squared line graph does not decrease:

`eIN(L(G)², f) / C(2pΔ², 2)  ≤  eIN(L(G')², f') / C(2Δ'², 2)`   (`Δ' = aΔ`).

The mathematics is complete and adversarially stress-tested (PROOF.md §6). The file
is additive: it introduces **no new axioms** and modifies no existing declaration.

## Layout
* §A — the arithmetic core (real-binomial reduction, PROOF.md §3/§7). Pure real
  arithmetic over abstract `a, b, Δ, d, e, eIN'`, discharged from the weak eIN
  lower bound `eIN' ≥ m²e + m(m−1)d` (m = ab), the KEEP degree bound `bd ≤ 2aΔ²`,
  `e ≤ C(d,2)` and `Δ ≥ b`.
-/

namespace Davey2024.SecAsymBlowup

open Finset Classical

noncomputable section

/-! ## §A. Arithmetic core (PROOF.md §3 / §7)

The transfer inequality, after clearing the positive real-binomial denominators
`N_o = C(2pΔ²,2) = pΔ²(2pΔ²−1)` and `N_bl = C(2Δ'²,2) = a²Δ²(2a²Δ²−1)` (with
`p = a/b`, `Δ' = aΔ`) and substituting the *weak* neighbourhood-edge lower bound
`eIN' ≥ m²e + m(m−1)d`, is **equivalent** to the elementary fact `d(2aΔ²−b) ≥ b·e`,
which the three inputs discharge. See PROOF.md §7 (the cost-saving lower-bound
variant) for the exact chain of equivalences.
-/

/-- **Key reduced inequality** (PROOF.md §7): `b·e ≤ d·(2aΔ²−b)`.

From `2e ≤ d(d−1)` (stated cleanly as `2e + d ≤ d²`, avoiding truncated `ℕ`
subtraction), the KEEP bound `bd ≤ 2aΔ²` and `b ≤ Δ`. -/
lemma transfer_key
    {a b Δ d e : ℕ}
    (hKEEP : b * d ≤ 2 * a * Δ ^ 2)
    (heC : 2 * e + d ≤ d * d) :
    (b : ℝ) * e ≤ d * (2 * a * Δ ^ 2 - b) := by
  have ha_nn : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
  have hb_nn : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have he_nn : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg _
  -- Cast the hypotheses to ℝ.
  have hkeepR : (b : ℝ) * d ≤ 2 * a * Δ ^ 2 := by exact_mod_cast hKEEP
  have heCR : 2 * (e : ℝ) + d ≤ d * d := by exact_mod_cast heC
  -- Two nonnegative products feeding the final linear combination.
  have hb_e : (0 : ℝ) ≤ b * (d * d - d - 2 * e) := by
    apply mul_nonneg hb_nn; linarith
  have hd_keep : (0 : ℝ) ≤ d * (2 * a * Δ ^ 2 - b * d) := by
    apply mul_nonneg hd_nn; linarith
  nlinarith [hb_e, hd_keep, mul_nonneg hb_nn he_nn, ha_nn, hb_nn, hd_nn, he_nn]

/-- **Arithmetic core of the transfer lemma** (PROOF.md §3.1 + §7).

Given the *weak* neighbourhood-edge lower bound `eIN' ≥ m²e + m(m−1)d` on the
regular blow-up (`m = ab`), the KEEP degree bound `bd ≤ 2aΔ²`, the counting bound
`2e ≤ d(d−1)` (as `2e+d ≤ d²`), and the divisibility consequence `Δ ≥ b`,

`eIN(L(G)²,f) / C(2pΔ²,2)  ≤  eIN(L(G')²,f') / C(2Δ'²,2)`   with `p = a/b`, `Δ' = aΔ`.

Here `C(x,2) = x(x−1)/2` is the **real** binomial, so
`C(2pΔ²,2) = pΔ²(2pΔ²−1)` and `C(2Δ'²,2) = a²Δ²(2a²Δ²−1)`. -/
theorem transfer_arith
    {a b Δ d e eIN' : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hΔb : b ≤ Δ)
    (hKEEP : b * d ≤ 2 * a * Δ ^ 2)
    (heC : 2 * e + d ≤ d * d)
    (hLB : (a * b) ^ 2 * e + (a * b) * (a * b - 1) * d ≤ eIN') :
    (e : ℝ) / ((a / b : ℝ) * Δ ^ 2 * (2 * (a / b : ℝ) * Δ ^ 2 - 1))
      ≤ (eIN' : ℝ) / ((a : ℝ) ^ 2 * Δ ^ 2 * (2 * (a : ℝ) ^ 2 * Δ ^ 2 - 1)) := by
  -- Real casts and basic positivity.
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hΔbR : (b : ℝ) ≤ Δ := by exact_mod_cast hΔb
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hΔ1 : (1 : ℝ) ≤ Δ := le_trans hbR hΔbR
  have hΔ0 : (0 : ℝ) < Δ := by linarith
  have hbne : (b : ℝ) ≠ 0 := ne_of_gt hb0
  have hΔ2 : (0 : ℝ) < Δ ^ 2 := by positivity
  -- `2aΔ² ≥ b`  (in fact `≥ Δ² ≥ b`).
  have hΔsq : (Δ : ℝ) ≤ Δ ^ 2 := by nlinarith [hΔ1, hΔ0]
  have hbig : (b : ℝ) ≤ 2 * a * Δ ^ 2 := by
    have h1 : (b : ℝ) ≤ Δ ^ 2 := le_trans hΔbR hΔsq
    have h2 : (Δ : ℝ) ^ 2 ≤ 2 * a * Δ ^ 2 := by
      nlinarith [mul_nonneg (le_of_lt hΔ2) (by linarith [haR] : (0 : ℝ) ≤ 2 * a - 1)]
    linarith
  -- Denominators.
  set No : ℝ := (a / b : ℝ) * Δ ^ 2 * (2 * (a / b : ℝ) * Δ ^ 2 - 1) with hNo_def
  set Nbl : ℝ := (a : ℝ) ^ 2 * Δ ^ 2 * (2 * (a : ℝ) ^ 2 * Δ ^ 2 - 1) with hNbl_def
  -- `2pΔ² > 1`  ⇒  `N_o > 0`.
  have hab_pos : (0 : ℝ) < (a / b : ℝ) := div_pos ha0 hb0
  have hpΔ : (1 : ℝ) < 2 * (a / b : ℝ) * Δ ^ 2 := by
    have e1 : 2 * ((a : ℝ) / b) * Δ ^ 2 = (2 * a * Δ ^ 2) / b := by field_simp
    rw [e1, lt_div_iff₀ hb0]
    have : (b : ℝ) < 2 * a * Δ ^ 2 := by nlinarith [hbig, hbR]
    linarith
  have hNo_pos : 0 < No := by
    rw [hNo_def]; exact mul_pos (mul_pos hab_pos hΔ2) (by linarith)
  -- `2a²Δ² > 1`  ⇒  `N_bl > 0`.
  have haΔ : (1 : ℝ) < 2 * (a : ℝ) ^ 2 * Δ ^ 2 := by nlinarith [haR, hΔ1, hΔ2]
  have hNbl_pos : 0 < Nbl := by
    rw [hNbl_def]; exact mul_pos (mul_pos (pow_pos ha0 2) hΔ2) (by linarith)
  -- Clear the `1/b` in `N_o`: `N_o · b² = a·Δ²·(2aΔ²−b) =: M`.
  set M : ℝ := (a : ℝ) * Δ ^ 2 * (2 * a * Δ ^ 2 - b) with hM_def
  have hM_nn : 0 ≤ M := by
    rw [hM_def]; exact mul_nonneg (by positivity) (by linarith)
  have hNob2 : No * (b : ℝ) ^ 2 = M := by
    rw [hNo_def, hM_def]; field_simp
  -- The key reduced inequality `b·e ≤ d·(2aΔ²−b)`.
  have hkey : (b : ℝ) * e ≤ d * (2 * a * Δ ^ 2 - b) := transfer_key hKEEP heC
  -- Cast the weak eIN lower bound.
  have hLBR : ((a : ℝ) * b) ^ 2 * e + ((a : ℝ) * b) * ((a : ℝ) * b - 1) * d ≤ eIN' := by
    have : (((a * b) ^ 2 * e + (a * b) * (a * b - 1) * d : ℕ) : ℝ) ≤ (eIN' : ℝ) := by
      exact_mod_cast hLB
    push_cast at this
    -- `a*b ≥ 1` so `(a*b - 1 : ℕ)` casts to `a*b - 1`.
    have hab1 : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [Nat.cast_sub hab1] at this
    push_cast at this
    linarith [this]
  -- Step 1: `e·N_bl·b² ≤ (m²e + m(m−1)d)·M`  via the ring identity of PROOF.md §7.
  have hid :
      (((a : ℝ) * b) ^ 2 * e + ((a : ℝ) * b) * ((a : ℝ) * b - 1) * d) * M
        - e * Nbl * (b : ℝ) ^ 2
      = (Δ : ℝ) ^ 2 * a * (((a : ℝ) * b) * ((a : ℝ) * b - 1))
          * (d * (2 * a * Δ ^ 2 - b) - b * e) := by
    rw [hM_def, hNbl_def]; ring
  have hstep1 : e * Nbl * (b : ℝ) ^ 2
      ≤ (((a : ℝ) * b) ^ 2 * e + ((a : ℝ) * b) * ((a : ℝ) * b - 1) * d) * M := by
    have hab1 : (1 : ℝ) ≤ (a : ℝ) * b := by nlinarith [haR, hbR]
    have hab_nn : (0 : ℝ) ≤ (a : ℝ) * b := by positivity
    have hfac1 : (0 : ℝ) ≤ (Δ : ℝ) ^ 2 * a * (((a : ℝ) * b) * ((a : ℝ) * b - 1)) :=
      mul_nonneg (by positivity) (mul_nonneg hab_nn (by linarith))
    have hfac2 : (0 : ℝ) ≤ d * (2 * a * Δ ^ 2 - b) - b * e := by linarith [hkey]
    have hfac_nn : 0 ≤ (Δ : ℝ) ^ 2 * a * (((a : ℝ) * b) * ((a : ℝ) * b - 1))
        * (d * (2 * a * Δ ^ 2 - b) - b * e) := mul_nonneg hfac1 hfac2
    linarith [hid, hfac_nn]
  -- Step 2: monotone in `eIN'`.
  have hstep2 : (((a : ℝ) * b) ^ 2 * e + ((a : ℝ) * b) * ((a : ℝ) * b - 1) * d) * M
      ≤ (eIN' : ℝ) * M := mul_le_mul_of_nonneg_right hLBR hM_nn
  -- Combine and strip the `b²`.
  have hb2_pos : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
  have hcombined : (e * Nbl) * (b : ℝ) ^ 2 ≤ ((eIN' : ℝ) * No) * (b : ℝ) ^ 2 := by
    calc (e * Nbl) * (b : ℝ) ^ 2 = e * Nbl * (b : ℝ) ^ 2 := by ring
      _ ≤ (eIN' : ℝ) * M := le_trans hstep1 hstep2
      _ = (eIN' : ℝ) * (No * (b : ℝ) ^ 2) := by rw [hNob2]
      _ = ((eIN' : ℝ) * No) * (b : ℝ) ^ 2 := by ring
  have hcross : (e : ℝ) * Nbl ≤ (eIN' : ℝ) * No :=
    le_of_mul_le_mul_right hcombined hb2_pos
  -- Convert the cross-multiplied inequality back to the quotient form.
  rw [div_le_div_iff₀ hNo_pos hNbl_pos]
  linarith [hcross]

/-! ## §B. Asymmetric blow-up construction (PROOF.md §1.1)

The blow-up replaces each component-0 (`S`-side) vertex by `cHi` copies and each
component-1 vertex by `cLo` copies (in the transfer application `cHi = b`,
`cLo = a`, `p = a/b`); a copy of `u` is adjacent to a copy of `v` iff `u ~ v`.
On a biregular host (component-0 degree `dHi`, component-1 degree `dLo`) with the
matching condition `dHi·cLo = dLo·cHi`, the blow-up is `(dHi·cLo)`-regular and
bipartite (in the application `dHi = Δ`, `dLo = pΔ`, so `dHi·cLo = aΔ`). -/

/-- Generic helper: the cardinality of a `univ`-filter is invariant under
precomposition with an equivalence. Used to reindex blow-up neighbourhoods
through `Fintype.equivFin`. -/
lemma card_filter_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (p : β → Prop) :
    (univ.filter (fun a => p (e a))).card = (univ.filter p).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

/-- Per-vertex copy count: component-0 (the `S`-side) vertices get `cHi` copies,
component-1 vertices get `cLo` copies. -/
def copyCount (G : Flag emptyType) (S : Finset (Fin G.size)) (cHi cLo : ℕ)
    (v : Fin G.size) : ℕ :=
  if v ∈ S then cHi else cLo

/-- Blow-up vertex type: `Σ v, Fin (copyCount v)` — each vertex replaced by its
independent set of copies. -/
abbrev BlowVtx (G : Flag emptyType) (S : Finset (Fin G.size)) (cHi cLo : ℕ) :=
  Σ v : Fin G.size, Fin (copyCount G S cHi cLo v)

/-- Blow-up adjacency on the sigma type: two copies are adjacent iff their
originals are adjacent in `G` (copy indices are irrelevant). -/
def blowSigmaGraph (G : Flag emptyType) (S : Finset (Fin G.size)) (cHi cLo : ℕ) :
    SimpleGraph (BlowVtx G S cHi cLo) where
  Adj x y := G.graph.Adj x.1 y.1
  symm := fun {_ _} h => G.graph.symm h
  loopless := ⟨fun x h => G.graph.loopless.irrefl x.1 h⟩

/-- The **asymmetric blow-up** of `G` as a `Flag emptyType`, on the index set
`Fin (Fintype.card (BlowVtx …))`, adjacency transported from `blowSigmaGraph`
along the canonical `Fintype.equivFin`. -/
def blowupAsymFlag (G : Flag emptyType) (S : Finset (Fin G.size)) (cHi cLo : ℕ) :
    Flag emptyType where
  size := Fintype.card (BlowVtx G S cHi cLo)
  graph :=
    { Adj := fun i j => (blowSigmaGraph G S cHi cLo).Adj
        ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm i)
        ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm j)
      symm := fun {_ _} h => (blowSigmaGraph G S cHi cLo).symm h
      loopless := ⟨fun _i h => (blowSigmaGraph G S cHi cLo).loopless.irrefl _ h⟩ }
  embedding := ⟨⟨Fin.elim0, fun {a} => Fin.elim0 a⟩, fun {a} => Fin.elim0 a⟩
  hsize := Nat.zero_le _

/-- Adjacency in the blow-up flag decodes to `G`-adjacency of the originals. -/
lemma blowupAsymFlag_adj (G : Flag emptyType) (S : Finset (Fin G.size)) (cHi cLo : ℕ)
    (i j : Fin (blowupAsymFlag G S cHi cLo).size) :
    (blowupAsymFlag G S cHi cLo).graph.Adj i j ↔
      G.graph.Adj ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm i).1
        ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm j).1 := Iff.rfl

/-- Neighbourhood count of a copy in the sigma blow-up: `Σ_{w ~ v} copyCount w`. -/
lemma blowSigma_nbhd_card (G : Flag emptyType) (S : Finset (Fin G.size)) (cHi cLo : ℕ)
    (v : Fin G.size) :
    (univ.filter (fun y : BlowVtx G S cHi cLo => G.graph.Adj v y.1)).card
      = ∑ w ∈ univ.filter (fun w => G.graph.Adj v w), copyCount G S cHi cLo w := by
  have hset : (univ.filter (fun y : BlowVtx G S cHi cLo => G.graph.Adj v y.1))
      = (univ.filter (fun w => G.graph.Adj v w)).sigma (fun _ => univ) := by
    ext y
    obtain ⟨w, k⟩ := y
    simp only [mem_filter, mem_univ, true_and, Finset.mem_sigma, and_true]
  rw [hset, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro w _
  simp [Finset.card_univ, copyCount]

/-- **Regularity of the blow-up** (PROOF.md §1.1): on a biregular host with
`dHi·cLo = dLo·cHi`, every blow-up vertex has degree `dHi·cLo`. -/
lemma blowup_degree_eq (G : Flag emptyType) (S : Finset (Fin G.size)) (cHi cLo : ℕ)
    {dHi dLo : ℕ}
    (hbip : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (hdegHi : ∀ u ∈ S, (univ.filter (fun w => G.graph.Adj u w)).card = dHi)
    (hdegLo : ∀ u, u ∉ S → (univ.filter (fun w => G.graph.Adj u w)).card = dLo)
    (hreg : dHi * cLo = dLo * cHi)
    (i : Fin (blowupAsymFlag G S cHi cLo).size) :
    (univ.filter (fun j => (blowupAsymFlag G S cHi cLo).graph.Adj i j)).card
      = dHi * cLo := by
  -- Reindex the flag-neighbourhood filter through `Fintype.equivFin`.
  have hreindex :
      (univ.filter (fun j => (blowupAsymFlag G S cHi cLo).graph.Adj i j)).card
        = (univ.filter (fun y : BlowVtx G S cHi cLo =>
            G.graph.Adj ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm i).1 y.1)).card :=
    card_filter_comp_equiv (Fintype.equivFin (BlowVtx G S cHi cLo)).symm
      (fun y => G.graph.Adj ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm i).1 y.1)
  rw [hreindex, blowSigma_nbhd_card]
  set v := ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm i).1 with hv
  by_cases hvS : v ∈ S
  · -- `v ∈ S`: all neighbours `w ∉ S`, so `copyCount w = cLo`; `|N| = dHi`.
    have hcopy : ∀ w ∈ univ.filter (fun w => G.graph.Adj v w),
        copyCount G S cHi cLo w = cLo := by
      intro w hw
      rw [mem_filter] at hw
      have : w ∉ S := (hbip v w hw.2).mp hvS
      simp [copyCount, this]
    rw [Finset.sum_congr rfl hcopy, Finset.sum_const, hdegHi v hvS, smul_eq_mul]
  · -- `v ∉ S`: all neighbours `w ∈ S`, so `copyCount w = cHi`; `|N| = dLo`.
    have hcopy : ∀ w ∈ univ.filter (fun w => G.graph.Adj v w),
        copyCount G S cHi cLo w = cHi := by
      intro w hw
      rw [mem_filter] at hw
      have : w ∈ S := by by_contra hwS; exact hvS ((hbip v w hw.2).mpr hwS)
      simp [copyCount, this]
    rw [Finset.sum_congr rfl hcopy, Finset.sum_const, hdegLo v hvS, smul_eq_mul, ← hreg]

/-- The blow-up is `IsRegular` (every vertex has the common degree `dHi·cLo`). -/
lemma blowup_isRegular (G : Flag emptyType) (S : Finset (Fin G.size)) (cHi cLo : ℕ)
    {dHi dLo : ℕ}
    (hbip : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (hdegHi : ∀ u ∈ S, (univ.filter (fun w => G.graph.Adj u w)).card = dHi)
    (hdegLo : ∀ u, u ∉ S → (univ.filter (fun w => G.graph.Adj u w)).card = dLo)
    (hreg : dHi * cLo = dLo * cHi) :
    IsRegular (blowupAsymFlag G S cHi cLo) := by
  intro i
  have hconst : ∀ j, (univ.filter
      (fun k => (blowupAsymFlag G S cHi cLo).graph.Adj j k)).card = dHi * cLo :=
    fun j => blowup_degree_eq G S cHi cLo hbip hdegHi hdegLo hreg j
  have hmax : maxDegree (blowupAsymFlag G S cHi cLo) = dHi * cLo := by
    refine le_antisymm (Finset.sup_le fun j _ => le_of_eq (hconst j)) ?_
    calc dHi * cLo
        = (univ.filter
            (fun u => (blowupAsymFlag G S cHi cLo).graph.Adj i u)).card := (hconst i).symm
      _ ≤ maxDegree (blowupAsymFlag G S cHi cLo) :=
          Finset.le_sup (f := fun v => (univ.filter
            (fun u => (blowupAsymFlag G S cHi cLo).graph.Adj v u)).card) (mem_univ i)
  rw [hconst i, hmax]

/-- The blow-up is bipartite, with the `S`-side lifted to `{i : orig(i) ∈ S}`. -/
lemma blowup_isBipartite (G : Flag emptyType) (S : Finset (Fin G.size)) (cHi cLo : ℕ)
    (hbip : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S)) :
    IsBipartite (blowupAsymFlag G S cHi cLo) := by
  refine ⟨univ.filter
    (fun i => ((Fintype.equivFin (BlowVtx G S cHi cLo)).symm i).1 ∈ S), ?_⟩
  intro i j hadj
  rw [blowupAsymFlag_adj] at hadj
  simp only [mem_filter, mem_univ, true_and]
  exact hbip _ _ hadj

/-! ## §C. The transfer lemma on the real objects (PROOF.md §3 + §7)

We assemble `transfer_arith` on the genuine `edgesInNeighbourhood`/`lineGraphSqFlag`
objects. The only combinatorial input left as a hypothesis is the **weak
neighbourhood-edge lower bound** `hLB` (PROOF.md §7's two injective `Finset`
families); everything else — the KEEP degree bound and the elementary counting
bound `e ≤ C(d,2)` — is discharged here. -/

/-- **Counting bound** (PROOF.md §3.2(i)): the edges among the neighbourhood of a
vertex number at most `C(deg, 2)`, in the clean form `2·eIN + deg ≤ deg²`. A
general fact about the real `edgesInNeighbourhood`. -/
lemma edgesInNeighbourhood_two_mul_add_deg_le (H : Flag emptyType) (v : Fin H.size) :
    2 * edgesInNeighbourhood H v + (univ.filter (fun u => H.graph.Adj v u)).card
      ≤ (univ.filter (fun u => H.graph.Adj v u)).card
        * (univ.filter (fun u => H.graph.Adj v u)).card := by
  -- `eIN ≤ C(deg,2)` via the injection `p ↦ {p.1, p.2}` into 2-subsets of the
  -- neighbourhood; `edgesInNeighbourhood H v` is defeq to the filtered-pair card.
  have hle : edgesInNeighbourhood H v
      ≤ (univ.filter (fun u => H.graph.Adj v u)).card.choose 2 := by
    have key : ((univ.filter (fun u => H.graph.Adj v u) ×ˢ
          univ.filter (fun u => H.graph.Adj v u)).filter
          (fun p => p.1 < p.2 ∧ H.graph.Adj p.1 p.2)).card
        ≤ (univ.filter (fun u => H.graph.Adj v u)).card.choose 2 := by
      rw [← Finset.card_powersetCard 2 (univ.filter (fun u => H.graph.Adj v u))]
      apply Finset.card_le_card_of_injOn (fun p => ({p.1, p.2} : Finset (Fin H.size)))
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, mem_univ,
          true_and] at hp
        obtain ⟨⟨hp1, hp2⟩, hlt, _⟩ := hp
        simp only [Finset.mem_coe, Finset.mem_powersetCard]
        refine ⟨fun x hx => ?_, Finset.card_pair (ne_of_lt hlt)⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h <;> subst h
        · exact Finset.mem_filter.mpr ⟨mem_univ _, hp1⟩
        · exact Finset.mem_filter.mpr ⟨mem_univ _, hp2⟩
      · intro p hp q hq hpq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hq
        obtain ⟨_, hplt, _⟩ := hp
        obtain ⟨_, hqlt, _⟩ := hq
        have hpq' : ({p.1, p.2} : Finset (Fin H.size)) = {q.1, q.2} := hpq
        have hmem : ∀ x, x ∈ ({p.1, p.2} : Finset (Fin H.size))
            ↔ x ∈ ({q.1, q.2} : Finset (Fin H.size)) := fun x => by rw [hpq']
        have h1 := (hmem p.1).mp (by simp)
        have h2 := (hmem p.2).mp (by simp)
        have h3 := (hmem q.1).mpr (by simp)
        simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3
        have a1 : p.1.val = q.1.val ∨ p.1.val = q.2.val := by
          rcases h1 with h | h <;> [left; right] <;> exact congrArg Fin.val h
        have a2 : p.2.val = q.1.val ∨ p.2.val = q.2.val := by
          rcases h2 with h | h <;> [left; right] <;> exact congrArg Fin.val h
        have b1 : q.1.val = p.1.val ∨ q.1.val = p.2.val := by
          rcases h3 with h | h <;> [left; right] <;> exact congrArg Fin.val h
        have hpv : p.1.val < p.2.val := hplt
        have hqv : q.1.val < q.2.val := hqlt
        have e1 : p.1.val = q.1.val ∧ p.2.val = q.2.val := by omega
        exact Prod.ext (Fin.ext e1.1) (Fin.ext e1.2)
    exact key
  -- `2·C(deg,2) + deg = deg²`.
  have hchoose : ∀ n : ℕ, 2 * n.choose 2 + n = n * n := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih =>
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        have hstep : 2 * (k + k.choose 2) + (k + 1)
            = (2 * k.choose 2 + k) + (2 * k + 1) := by ring
        rw [hstep, ih]; ring
  have := hchoose (univ.filter (fun u => H.graph.Adj v u)).card
  omega

/-- **Transfer lemma** (PROOF.md §1.4 / §3): the σ-normalised neighbourhood-edge
density of `L(G)²` at an edge `f` is at most that of `L(G')²` at a blow-up copy
`f'`, for the real-binomial normalisers `C(2pΔ²,2)` and `C(2Δ'²,2)`
(`p = a/b`, `Δ = Δ(G)`, `Δ' = aΔ`).

The single combinatorial input `hLB` is the weak neighbourhood-edge lower bound
`eIN(L(G')²,f') ≥ m²·eIN(L(G)²,f) + m(m−1)·deg_{L(G)²}(f)` (`m = ab`) supplied by
PROOF.md §7's two injective `Finset` families over the blow-up; the KEEP degree
bound and `e ≤ C(d,2)` are discharged internally. -/
theorem blowup_transfer
    {G : Flag emptyType} {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≤ b)
    (hΔb : b ≤ maxDegree G)
    (hAsym : SecAsymmetricBipartiteBridge.IsAsymmetricBipartite ((a : ℝ) / b) G)
    (f : Fin (lineGraphSqFlag G).size)
    {G' : Flag emptyType} (f' : Fin (lineGraphSqFlag G').size)
    (hLB : (a * b) ^ 2 * edgesInNeighbourhood (lineGraphSqFlag G) f
            + (a * b) * (a * b - 1)
              * (univ.filter (fun k => (lineGraphSqFlag G).graph.Adj f k)).card
          ≤ edgesInNeighbourhood (lineGraphSqFlag G') f') :
    (edgesInNeighbourhood (lineGraphSqFlag G) f : ℝ)
        / (((a : ℝ) / b) * (maxDegree G : ℝ) ^ 2
            * (2 * ((a : ℝ) / b) * (maxDegree G : ℝ) ^ 2 - 1))
      ≤ (edgesInNeighbourhood (lineGraphSqFlag G') f' : ℝ)
        / ((a : ℝ) ^ 2 * (maxDegree G : ℝ) ^ 2
            * (2 * (a : ℝ) ^ 2 * (maxDegree G : ℝ) ^ 2 - 1)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hppos : (0 : ℝ) < (a : ℝ) / b := div_pos ha0 hb0
  have hple1 : (a : ℝ) / b ≤ 1 := by rw [div_le_one hb0]; exact_mod_cast hab
  -- item 4: `2·e + d ≤ d²` (with `d = deg_{L(G)²}(f)`).
  have hcount := edgesInNeighbourhood_two_mul_add_deg_le (lineGraphSqFlag G) f
  set d := (univ.filter (fun k => (lineGraphSqFlag G).graph.Adj f k)).card with hd
  -- item 3: `b·d ≤ 2aΔ²` from the KEEP degree bound `Δ(L(G)²) ≤ 2pΔ²`.
  have hKEEP : b * d ≤ 2 * a * (maxDegree G) ^ 2 := by
    have hdegR : (d : ℝ) ≤ (maxDegree (lineGraphSqFlag G) : ℝ) := by
      exact_mod_cast degree_le_maxDegree (lineGraphSqFlag G) f
    have hkeepR : (maxDegree (lineGraphSqFlag G) : ℝ)
        ≤ 2 * ((a : ℝ) / b) * (maxDegree G : ℝ) ^ 2 :=
      SecAsymmetricBipartiteBridge.asymmetric_lineGraphSq_maxDegree_le hppos hple1 hAsym
    have hbd : (b : ℝ) * d ≤ 2 * a * (maxDegree G : ℝ) ^ 2 := by
      have h1 : (b : ℝ) * d ≤ (b : ℝ) * (2 * ((a : ℝ) / b) * (maxDegree G : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (le_trans hdegR hkeepR) (le_of_lt hb0)
      have h2 : (b : ℝ) * (2 * ((a : ℝ) / b) * (maxDegree G : ℝ) ^ 2)
          = 2 * a * (maxDegree G : ℝ) ^ 2 := by field_simp
      linarith [h1, h2.le, h2.ge]
    exact_mod_cast hbd
  exact transfer_arith ha hb hΔb hKEEP hcount hLB

/-! ## §D. Discharging `hLB`: the neighbourhood-edge lower bound (PROOF.md §7)

We prove the weak lower bound
`eIN(L(G')², f') ≥ m²·eIN(L(G)²,f) + m(m−1)·deg_{L(G)²}(f)`  (`m = ab`)
for the concrete blow-up `G' = blowupAsymFlag G S b a`, via two edge-disjoint
injective `Finset` families (F4 cross-block, F3 intra-`f`-block), then feed it to
`transfer_arith` to make the transfer lemma UNCONDITIONAL.

### §D.0 Generic infrastructure (flag-agnostic). -/

/-- **Generic neighbourhood-edge lower bound.** If `Src` indexes a family of
`H`-edges `{a1 t, a2 t}` all lying inside `N_H(v)` (both endpoints adjacent to `v`)
with the two endpoints adjacent to each other, and the family is injective *as a
family of unordered pairs*, then `|Src| ≤ eIN(H, v)`. The canonical ordering of the
neighbourhood-edge count is absorbed by mapping each `t` to its sorted pair. -/
lemma edgesInNeighbourhood_ge {H : Flag emptyType} (v : Fin H.size)
    {ι : Type*} (Src : Finset ι) (a1 a2 : ι → Fin H.size)
    (hv1 : ∀ t ∈ Src, H.graph.Adj v (a1 t))
    (hv2 : ∀ t ∈ Src, H.graph.Adj v (a2 t))
    (h12 : ∀ t ∈ Src, H.graph.Adj (a1 t) (a2 t))
    (hinj : ∀ s ∈ Src, ∀ t ∈ Src,
      ({a1 s, a2 s} : Finset (Fin H.size)) = {a1 t, a2 t} → s = t) :
    Src.card ≤ edgesInNeighbourhood H v := by
  classical
  unfold edgesInNeighbourhood
  set nbrs := (univ.filter (fun u => H.graph.Adj v u)) with hnbrs
  -- Sorted-pair map into the neighbourhood-edge pair set.
  set ψ : ι → Fin H.size × Fin H.size :=
    fun t => if a1 t < a2 t then (a1 t, a2 t) else (a2 t, a1 t) with hψ
  -- The unordered pair of `ψ t` is `{a1 t, a2 t}`.
  have hψset : ∀ t, ({(ψ t).1, (ψ t).2} : Finset (Fin H.size)) = {a1 t, a2 t} := by
    intro t
    by_cases hc : a1 t < a2 t
    · simp [hψ, hc]
    · simp [hψ, hc, Finset.pair_comm]
  apply Finset.card_le_card_of_injOn ψ
  · -- membership in the pair set
    intro t ht
    have hne : a1 t ≠ a2 t := H.graph.ne_of_adj (h12 t ht)
    have hm1 : a1 t ∈ nbrs := by rw [hnbrs]; exact Finset.mem_filter.mpr ⟨mem_univ _, hv1 t ht⟩
    have hm2 : a2 t ∈ nbrs := by rw [hnbrs]; exact Finset.mem_filter.mpr ⟨mem_univ _, hv2 t ht⟩
    by_cases hc : a1 t < a2 t
    · have hval : ψ t = (a1 t, a2 t) := by simp only [hψ]; exact if_pos hc
      rw [hval]
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hm1, hm2⟩, hc, h12 t ht⟩
    · have hlt : a2 t < a1 t := lt_of_le_of_ne (not_lt.mp hc) (Ne.symm hne)
      have hval : ψ t = (a2 t, a1 t) := by simp only [hψ]; exact if_neg hc
      rw [hval]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hm2, hm1⟩, hlt, H.graph.symm (h12 t ht)⟩
  · -- injectivity via unordered pairs
    intro s hs t ht hst
    apply hinj s hs t ht
    rw [← hψset s, ← hψset t, hst]

/-- The copy-index-independent "endpoint conflict" relation on two edges of a flag
`Γ` (PROOF.md §2.1, the predicate `R`): some endpoint of the first is `Γ`-adjacent
to some endpoint of the second. -/
def Rrel (Γ : Flag emptyType) (e₁ e₂ : Fin Γ.size × Fin Γ.size) : Prop :=
  Γ.graph.Adj e₁.1 e₂.1 ∨ Γ.graph.Adj e₁.1 e₂.2 ∨
  Γ.graph.Adj e₁.2 e₂.1 ∨ Γ.graph.Adj e₁.2 e₂.2

/-- `Rrel` is invariant under swapping the two endpoints of the first edge. -/
lemma Rrel_swap_left (Γ : Flag emptyType) (p q : Fin Γ.size)
    (e₂ : Fin Γ.size × Fin Γ.size) :
    Rrel Γ (p, q) e₂ → Rrel Γ (q, p) e₂ := by
  rintro (h | h | h | h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- `Rrel` is invariant under swapping the two endpoints of the second edge. -/
lemma Rrel_swap_right (Γ : Flag emptyType) (e₁ : Fin Γ.size × Fin Γ.size)
    (p q : Fin Γ.size) :
    Rrel Γ e₁ (p, q) → Rrel Γ e₁ (q, p) := by
  rintro (h | h | h | h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

/-- **`lineGraphSqAdj ⇒ Rrel`** (PROOF.md §2.1, Claim A ⇒). The squared-line-graph
conflict relation implies the endpoint-conflict relation. -/
lemma lineGraphSqAdj_to_R (Γ : Flag emptyType) (e₁ e₂ : Fin Γ.size × Fin Γ.size)
    (h : lineGraphSqAdj Γ e₁ e₂) : Rrel Γ e₁ e₂ := by
  have mkR : ∀ (x y : Fin Γ.size), (x = e₁.1 ∨ x = e₁.2) →
      (y = e₂.1 ∨ y = e₂.2) → Γ.graph.Adj x y → Rrel Γ e₁ e₂ := by
    rintro x y (rfl | rfl) (rfl | rfl) hadj
    · exact Or.inl hadj
    · exact Or.inr (Or.inl hadj)
    · exact Or.inr (Or.inr (Or.inl hadj))
    · exact Or.inr (Or.inr (Or.inr hadj))
  obtain ⟨h1, _, _, _, hconn⟩ := h
  rcases hconn with ⟨_, _, _, hshare⟩ | ⟨e₃, he₃, ⟨_, _, _, hs13⟩, ⟨_, _, _, hs23⟩⟩
  · rcases hshare with heq | heq | heq | heq
    · exact mkR e₁.2 e₂.1 (Or.inr rfl) (Or.inl rfl) (by rw [← heq]; exact Γ.graph.symm h1)
    · exact mkR e₁.2 e₂.2 (Or.inr rfl) (Or.inr rfl) (by rw [← heq]; exact Γ.graph.symm h1)
    · exact mkR e₁.1 e₂.1 (Or.inl rfl) (Or.inl rfl) (by rw [← heq]; exact h1)
    · exact mkR e₁.1 e₂.2 (Or.inl rfl) (Or.inr rfl) (by rw [← heq]; exact h1)
  · obtain ⟨p, hp1, hp3⟩ : ∃ p, (p = e₁.1 ∨ p = e₁.2) ∧ (p = e₃.1 ∨ p = e₃.2) := by
      rcases hs13 with h | h | h | h
      · exact ⟨e₁.1, Or.inl rfl, Or.inl h⟩
      · exact ⟨e₁.1, Or.inl rfl, Or.inr h⟩
      · exact ⟨e₁.2, Or.inr rfl, Or.inl h⟩
      · exact ⟨e₁.2, Or.inr rfl, Or.inr h⟩
    obtain ⟨q, hq3, hq2⟩ : ∃ q, (q = e₃.1 ∨ q = e₃.2) ∧ (q = e₂.1 ∨ q = e₂.2) := by
      rcases hs23 with h | h | h | h
      · exact ⟨e₃.1, Or.inl rfl, Or.inl h⟩
      · exact ⟨e₃.1, Or.inl rfl, Or.inr h⟩
      · exact ⟨e₃.2, Or.inr rfl, Or.inl h⟩
      · exact ⟨e₃.2, Or.inr rfl, Or.inr h⟩
    by_cases hpq : p = q
    · subst hpq
      rcases hp1 with hp1 | hp1
      · exact mkR e₁.2 p (Or.inr rfl) hq2 (by rw [hp1]; exact Γ.graph.symm h1)
      · exact mkR e₁.1 p (Or.inl rfl) hq2 (by rw [hp1]; exact h1)
    · have hadjpq : Γ.graph.Adj p q := by
        rcases hp3 with hp3 | hp3 <;> rcases hq3 with hq3 | hq3
        · exact absurd (hp3.trans hq3.symm) hpq
        · rw [hp3, hq3]; exact he₃
        · rw [hp3, hq3]; exact Γ.graph.symm he₃
        · exact absurd (hp3.trans hq3.symm) hpq
      exact mkR p q hp1 hq2 hadjpq

/-- **`Rrel ⇒ lineGraphSqAdj`** (PROOF.md §2.1, Claim A ⇐). Given two genuine edges
that are distinct (and not reverses), the endpoint-conflict relation implies the
squared-line-graph conflict. -/
lemma lineGraphSqAdj_of_R (Γ : Flag emptyType) (e₁ e₂ : Fin Γ.size × Fin Γ.size)
    (h1 : Γ.graph.Adj e₁.1 e₁.2) (h2 : Γ.graph.Adj e₂.1 e₂.2)
    (hne : e₁ ≠ e₂) (hnerev : e₁ ≠ (e₂.2, e₂.1))
    (hR : Rrel Γ e₁ e₂) : lineGraphSqAdj Γ e₁ e₂ := by
  refine ⟨h1, h2, hne, hnerev, ?_⟩
  have buildConn : ∀ (x y : Fin Γ.size), (x = e₁.1 ∨ x = e₁.2) → (y = e₂.1 ∨ y = e₂.2) →
      Γ.graph.Adj x y →
      (lineGraphAdj Γ e₁ e₂ ∨ ∃ e₃ : Fin Γ.size × Fin Γ.size,
        Γ.graph.Adj e₃.1 e₃.2 ∧ lineGraphAdj Γ e₁ e₃ ∧ lineGraphAdj Γ e₃ e₂) := by
    intro x y hx hy hxy
    by_cases he13 : e₁ = (x, y)
    · left
      have hy2 : e₁.2 = y := (Prod.ext_iff.mp he13).2
      refine ⟨h1, h2, hne, ?_⟩
      rcases hy with hy | hy
      · exact Or.inr (Or.inr (Or.inl (hy2.trans hy)))
      · exact Or.inr (Or.inr (Or.inr (hy2.trans hy)))
    · by_cases he32 : (x, y) = e₂
      · left
        have hx1 : x = e₂.1 := (Prod.ext_iff.mp he32).1
        refine ⟨h1, h2, hne, ?_⟩
        rcases hx with hx | hx
        · exact Or.inl (hx.symm.trans hx1)
        · exact Or.inr (Or.inr (Or.inl (hx.symm.trans hx1)))
      · right
        refine ⟨(x, y), hxy, ⟨h1, hxy, he13, ?_⟩, ⟨hxy, h2, he32, ?_⟩⟩
        · rcases hx with hx | hx
          · exact Or.inl hx.symm
          · exact Or.inr (Or.inr (Or.inl hx.symm))
        · rcases hy with hy | hy
          · exact Or.inr (Or.inr (Or.inl hy))
          · exact Or.inr (Or.inr (Or.inr hy))
  rcases hR with hR | hR | hR | hR
  · exact buildConn e₁.1 e₂.1 (Or.inl rfl) (Or.inl rfl) hR
  · exact buildConn e₁.1 e₂.2 (Or.inl rfl) (Or.inr rfl) hR
  · exact buildConn e₁.2 e₂.1 (Or.inr rfl) (Or.inl rfl) hR
  · exact buildConn e₁.2 e₂.2 (Or.inr rfl) (Or.inr rfl) hR

/-! ### §D.1 Blow-up edge decode layer.  Here `G' = blowupAsymFlag G S b a`
(component-0/`S` side gets `b` copies, component-1 gets `a` copies). -/

/-- Forward index of a blow-up vertex in `Fin G'.size`. -/
noncomputable def bvIdx (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (x : BlowVtx G S b a) : Fin (blowupAsymFlag G S b a).size :=
  Fintype.equivFin (BlowVtx G S b a) x

lemma bvIdx_symm (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (x : BlowVtx G S b a) :
    (Fintype.equivFin (BlowVtx G S b a)).symm (bvIdx G S a b x) = x :=
  (Fintype.equivFin (BlowVtx G S b a)).symm_apply_apply x

lemma bvIdx_injective (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ) :
    Function.Injective (bvIdx G S a b) :=
  (Fintype.equivFin (BlowVtx G S b a)).injective

/-- Blow-up adjacency between forward-indexed vertices decodes to `G`-adjacency of
originals. -/
lemma bvIdx_adj (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (x y : BlowVtx G S b a) :
    (blowupAsymFlag G S b a).graph.Adj (bvIdx G S a b x) (bvIdx G S a b y)
      ↔ G.graph.Adj x.1 y.1 := by
  rw [blowupAsymFlag_adj, bvIdx_symm, bvIdx_symm]

/-- The two forward indices of an adjacent blow-up pair are distinct. -/
lemma bvIdx_ne (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (x y : BlowVtx G S b a) (h : G.graph.Adj x.1 y.1) :
    bvIdx G S a b x ≠ bvIdx G S a b y := by
  intro heq
  exact G.graph.ne_of_adj h (by rw [bvIdx_injective G S a b heq])

/-- **Canonical blow-up edge** from an adjacent pair of blow-up vertices. -/
noncomputable def mkBEdge (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (x y : BlowVtx G S b a) (h : G.graph.Adj x.1 y.1) :
    ↥(edgeFinset (blowupAsymFlag G S b a)) :=
  if hlt : bvIdx G S a b x < bvIdx G S a b y then
    ⟨(bvIdx G S a b x, bvIdx G S a b y),
      Finset.mem_filter.mpr ⟨mem_univ _, (bvIdx_adj G S a b x y).mpr h, hlt⟩⟩
  else
    ⟨(bvIdx G S a b y, bvIdx G S a b x),
      Finset.mem_filter.mpr ⟨mem_univ _, (bvIdx_adj G S a b y x).mpr (G.graph.symm h),
        lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm (bvIdx_ne G S a b x y h))⟩⟩

/-- The value of `mkBEdge` is the ordered pair, in one of the two orders. -/
lemma mkBEdge_val (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (x y : BlowVtx G S b a) (h : G.graph.Adj x.1 y.1) :
    (mkBEdge G S a b x y h).val = (bvIdx G S a b x, bvIdx G S a b y) ∨
      (mkBEdge G S a b x y h).val = (bvIdx G S a b y, bvIdx G S a b x) := by
  unfold mkBEdge
  by_cases hlt : bvIdx G S a b x < bvIdx G S a b y
  · left; rw [dif_pos hlt]
  · right; rw [dif_neg hlt]

/-! ### §D.2 Flag/edge reindex helpers and the copy-edge adjacency lemma. -/

/-- Squared-line-graph flag adjacency between edge-subtype vertices decodes to
`lineGraphSqAdj` on the underlying edges. -/
lemma lgsqFlag_adj (Γ : Flag emptyType) (E₁ E₂ : ↥(edgeFinset Γ)) :
    (lineGraphSqFlag Γ).graph.Adj ((edgeFinset Γ).equivFin E₁) ((edgeFinset Γ).equivFin E₂)
      ↔ lineGraphSqAdj Γ E₁.val E₂.val := by
  change lineGraphSqAdj Γ ((edgeFinset Γ).equivFin.symm ((edgeFinset Γ).equivFin E₁)).val
      ((edgeFinset Γ).equivFin.symm ((edgeFinset Γ).equivFin E₂)).val ↔ _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Canonical edges have `.1 < .2`. -/
lemma edge_lt (Γ : Flag emptyType) (E : ↥(edgeFinset Γ)) : E.val.1 < E.val.2 :=
  (Finset.mem_filter.mp E.property).2.2

/-- A canonical edge is never a reversed canonical edge. -/
lemma edge_ne_swap (Γ : Flag emptyType) (E₁ E₂ : ↥(edgeFinset Γ)) :
    E₁.val ≠ (E₂.val.2, E₂.val.1) := by
  intro h
  have h1 := edge_lt Γ E₁
  have h2 := edge_lt Γ E₂
  rw [Prod.ext_iff] at h
  obtain ⟨ha, hb⟩ := h
  rw [ha, hb] at h1
  exact lt_asymm h2 h1

/-- On a bipartite host, the copy-count product over the two endpoints of an edge
is `a*b` (one endpoint gets `b` copies, the other `a`). -/
lemma copyCount_prod (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (hbip : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (g : ↥(edgeFinset G)) :
    copyCount G S b a g.val.1 * copyCount G S b a g.val.2 = a * b := by
  have hadj := edgeFinset_adj G g
  have hiff := hbip g.val.1 g.val.2 hadj
  simp only [copyCount]
  by_cases h1 : g.val.1 ∈ S
  · have h2 : g.val.2 ∉ S := hiff.mp h1
    rw [if_pos h1, if_neg h2, Nat.mul_comm]
  · have h2 : g.val.2 ∈ S := by by_contra h; exact h1 (hiff.mpr h)
    rw [if_neg h1, if_pos h2]

/-- Original vertex underlying a blow-up index. -/
noncomputable def origV (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (i : Fin (blowupAsymFlag G S b a).size) : Fin G.size :=
  ((Fintype.equivFin (BlowVtx G S b a)).symm i).1

lemma origV_bvIdx (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (x : BlowVtx G S b a) : origV G S a b (bvIdx G S a b x) = x.1 := by
  unfold origV bvIdx
  rw [Equiv.symm_apply_apply]

/-- `Rrel` on the originals lifts to `Rrel` on the canonical blow-up edges. -/
lemma Rrel_mkBEdge (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (X₁ Y₁ X₂ Y₂ : BlowVtx G S b a) (hxy1 : G.graph.Adj X₁.1 Y₁.1)
    (hxy2 : G.graph.Adj X₂.1 Y₂.1)
    (hR : Rrel G (X₁.1, Y₁.1) (X₂.1, Y₂.1)) :
    Rrel (blowupAsymFlag G S b a)
      (mkBEdge G S a b X₁ Y₁ hxy1).val (mkBEdge G S a b X₂ Y₂ hxy2).val := by
  have base : Rrel (blowupAsymFlag G S b a)
      (bvIdx G S a b X₁, bvIdx G S a b Y₁) (bvIdx G S a b X₂, bvIdx G S a b Y₂) := by
    rcases hR with h | h | h | h
    · exact Or.inl ((bvIdx_adj G S a b X₁ X₂).mpr h)
    · exact Or.inr (Or.inl ((bvIdx_adj G S a b X₁ Y₂).mpr h))
    · exact Or.inr (Or.inr (Or.inl ((bvIdx_adj G S a b Y₁ X₂).mpr h)))
    · exact Or.inr (Or.inr (Or.inr ((bvIdx_adj G S a b Y₁ Y₂).mpr h)))
  rcases mkBEdge_val G S a b X₁ Y₁ hxy1 with hv1 | hv1 <;>
    rcases mkBEdge_val G S a b X₂ Y₂ hxy2 with hv2 | hv2 <;> rw [hv1, hv2]
  · exact base
  · exact Rrel_swap_right _ _ _ _ base
  · exact Rrel_swap_left _ _ _ _ base
  · exact Rrel_swap_left _ _ _ _ (Rrel_swap_right _ _ _ _ base)

/-! ### §D.3 Copy-edge vertices of `L(G')²`, their adjacency and injectivity. -/

/-- Copy-index type of a `G`-edge in the blow-up (`= a*b` elements). -/
abbrev CopIdx (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (g : ↥(edgeFinset G)) :=
  Fin (copyCount G S b a g.val.1) × Fin (copyCount G S b a g.val.2)

/-- The `L(G')²`-vertex given by a copy of the `G`-edge `g` with copy indices `p`. -/
noncomputable def cev (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (g : ↥(edgeFinset G)) (p : CopIdx G S a b g) :
    Fin (lineGraphSqFlag (blowupAsymFlag G S b a)).size :=
  (edgeFinset (blowupAsymFlag G S b a)).equivFin
    (mkBEdge G S a b ⟨g.val.1, p.1⟩ ⟨g.val.2, p.2⟩ (edgeFinset_adj G g))

/-- The underlying blow-up edge of `cev g p`. -/
noncomputable def cevEdge (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (g : ↥(edgeFinset G)) (p : CopIdx G S a b g) :
    ↥(edgeFinset (blowupAsymFlag G S b a)) :=
  mkBEdge G S a b ⟨g.val.1, p.1⟩ ⟨g.val.2, p.2⟩ (edgeFinset_adj G g)

lemma cev_eq (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (g : ↥(edgeFinset G)) (p : CopIdx G S a b g) :
    cev G S a b g p = (edgeFinset (blowupAsymFlag G S b a)).equivFin (cevEdge G S a b g p) :=
  rfl

/-- Adjacency of two copy-edge vertices from the endpoint-conflict of their originals
plus distinctness of the underlying blow-up edges. -/
lemma cev_adj (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (g₁ g₂ : ↥(edgeFinset G)) (p₁ : CopIdx G S a b g₁) (p₂ : CopIdx G S a b g₂)
    (hne : cevEdge G S a b g₁ p₁ ≠ cevEdge G S a b g₂ p₂)
    (hR : Rrel G g₁.val g₂.val) :
    (lineGraphSqFlag (blowupAsymFlag G S b a)).graph.Adj
      (cev G S a b g₁ p₁) (cev G S a b g₂ p₂) := by
  rw [cev_eq, cev_eq, lgsqFlag_adj]
  have hRb : Rrel (blowupAsymFlag G S b a)
      (cevEdge G S a b g₁ p₁).val (cevEdge G S a b g₂ p₂).val := by
    unfold cevEdge
    exact Rrel_mkBEdge G S a b _ _ _ _ _ _ hR
  exact lineGraphSqAdj_of_R _ _ _ (edgeFinset_adj _ _) (edgeFinset_adj _ _)
    (fun h => hne (Subtype.ext h)) (edge_ne_swap _ _ _) hRb

/-- Underlying blow-up edge of `cev`, decoded back to its original-endpoint set. -/
lemma cevEdge_origSet (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (g : ↥(edgeFinset G)) (p : CopIdx G S a b g) :
    ({origV G S a b (cevEdge G S a b g p).val.1,
      origV G S a b (cevEdge G S a b g p).val.2} : Finset (Fin G.size)) = {g.val.1, g.val.2} := by
  unfold cevEdge
  rcases mkBEdge_val G S a b ⟨g.val.1, p.1⟩ ⟨g.val.2, p.2⟩ (edgeFinset_adj G g) with hv | hv
  · rw [hv]
    change ({origV G S a b (bvIdx G S a b ⟨g.val.1, p.1⟩),
          origV G S a b (bvIdx G S a b ⟨g.val.2, p.2⟩)} : Finset _) = {g.val.1, g.val.2}
    rw [origV_bvIdx, origV_bvIdx]
  · rw [hv]
    change ({origV G S a b (bvIdx G S a b ⟨g.val.2, p.2⟩),
          origV G S a b (bvIdx G S a b ⟨g.val.1, p.1⟩)} : Finset _) = {g.val.1, g.val.2}
    rw [origV_bvIdx, origV_bvIdx]; exact Finset.pair_comm _ _

/-- The underlying blow-up edge of `cev`, decoded to its blow-up-vertex-index set. -/
lemma cevEdge_bvIdxSet (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (g : ↥(edgeFinset G)) (p : CopIdx G S a b g) :
    ({(cevEdge G S a b g p).val.1, (cevEdge G S a b g p).val.2}
        : Finset (Fin (blowupAsymFlag G S b a).size))
      = {bvIdx G S a b ⟨g.val.1, p.1⟩, bvIdx G S a b ⟨g.val.2, p.2⟩} := by
  unfold cevEdge
  rcases mkBEdge_val G S a b ⟨g.val.1, p.1⟩ ⟨g.val.2, p.2⟩ (edgeFinset_adj G g) with hv | hv
  · rw [hv]
  · rw [hv]; exact Finset.pair_comm _ _

/-- Two canonical edges with the same endpoint set are equal. -/
lemma edge_eq_of_set_eq (G : Flag emptyType) (g₁ g₂ : ↥(edgeFinset G))
    (h : ({g₁.val.1, g₁.val.2} : Finset (Fin G.size)) = {g₂.val.1, g₂.val.2}) : g₁ = g₂ := by
  have l1 := edge_lt G g₁
  have l2 := edge_lt G g₂
  have m21 : g₂.val.1 ∈ ({g₁.val.1, g₁.val.2} : Finset (Fin G.size)) := by
    rw [h]; exact Finset.mem_insert_self _ _
  have m22 : g₂.val.2 ∈ ({g₁.val.1, g₁.val.2} : Finset (Fin G.size)) := by
    rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have m11 : g₁.val.1 ∈ ({g₂.val.1, g₂.val.2} : Finset (Fin G.size)) := by
    rw [← h]; exact Finset.mem_insert_self _ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at m21 m22 m11
  have hcomp : g₁.val.1 = g₂.val.1 ∧ g₁.val.2 = g₂.val.2 := by
    rcases m21 with e21 | e21 <;> rcases m22 with e22 | e22 <;> rcases m11 with e11 | e11 <;>
      first
        | exact ⟨e21.symm, e22.symm⟩
        | (exfalso; omega)
  exact Subtype.ext (Prod.ext hcomp.1 hcomp.2)

/-- `cevEdge` distinguishes copies of different edges. -/
lemma cevEdge_ne_of_edge_ne (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (g₁ g₂ : ↥(edgeFinset G)) (p₁ : CopIdx G S a b g₁) (p₂ : CopIdx G S a b g₂)
    (hg : g₁ ≠ g₂) :
    cevEdge G S a b g₁ p₁ ≠ cevEdge G S a b g₂ p₂ := by
  intro heq
  apply hg
  apply edge_eq_of_set_eq
  have hv : (cevEdge G S a b g₁ p₁).val = (cevEdge G S a b g₂ p₂).val := by rw [heq]
  rw [← cevEdge_origSet G S a b g₁ p₁, ← cevEdge_origSet G S a b g₂ p₂, hv]

/-- `cevEdge` distinguishes different copies of the same edge. -/
lemma cevEdge_ne_of_copy_ne (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (g : ↥(edgeFinset G)) (p₁ p₂ : CopIdx G S a b g) (hp : p₁ ≠ p₂) :
    cevEdge G S a b g p₁ ≠ cevEdge G S a b g p₂ := by
  intro heq
  apply hp
  have hv : (cevEdge G S a b g p₁).val = (cevEdge G S a b g p₂).val := by rw [heq]
  have hset : ({bvIdx G S a b ⟨g.val.1, p₁.1⟩, bvIdx G S a b ⟨g.val.2, p₁.2⟩} : Finset _)
      = {bvIdx G S a b ⟨g.val.1, p₂.1⟩, bvIdx G S a b ⟨g.val.2, p₂.2⟩} := by
    rw [← cevEdge_bvIdxSet, ← cevEdge_bvIdxSet, hv]
  have hg12 : g.val.1 ≠ g.val.2 := ne_of_lt (edge_lt G g)
  have hm : bvIdx G S a b (⟨g.val.1, p₁.1⟩ : BlowVtx G S b a) ∈
      ({bvIdx G S a b ⟨g.val.1, p₂.1⟩, bvIdx G S a b ⟨g.val.2, p₂.2⟩} : Finset _) := by
    rw [← hset]; exact Finset.mem_insert_self _ _
  have hm2 : bvIdx G S a b (⟨g.val.2, p₁.2⟩ : BlowVtx G S b a) ∈
      ({bvIdx G S a b ⟨g.val.1, p₂.1⟩, bvIdx G S a b ⟨g.val.2, p₂.2⟩} : Finset _) := by
    rw [← hset]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm hm2
  have hX : (⟨g.val.1, p₁.1⟩ : BlowVtx G S b a) = ⟨g.val.1, p₂.1⟩ := by
    rcases hm with h | h
    · exact bvIdx_injective G S a b h
    · exact absurd (congrArg Sigma.fst (bvIdx_injective G S a b h)) hg12
  have hY : (⟨g.val.2, p₁.2⟩ : BlowVtx G S b a) = ⟨g.val.2, p₂.2⟩ := by
    rcases hm2 with h | h
    · exact absurd (congrArg Sigma.fst (bvIdx_injective G S a b h)) (Ne.symm hg12)
    · exact bvIdx_injective G S a b h
  have e1 : p₁.1 = p₂.1 := by simpa using (Sigma.mk.inj_iff.mp hX).2
  have e2 : p₁.2 = p₂.2 := by simpa using (Sigma.mk.inj_iff.mp hY).2
  exact Prod.ext e1 e2

/-- A uniform copy-index reparametrisation `Fin (a*b) ≃ CopIdx g` (both have `a*b`
elements on a bipartite host). -/
noncomputable def copyEquiv (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (hbip : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (g : ↥(edgeFinset G)) : Fin (a * b) ≃ CopIdx G S a b g :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      copyCount_prod G S a b hbip])

/-- `cev` as a function of `(edge, uniform copy index)` is injective, when the
underlying edges are known equal / handled separately. Concretely: if two
copy-edge vertices coincide then the underlying `cevEdge`s coincide. -/
lemma cev_injEdge (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (g₁ g₂ : ↥(edgeFinset G)) (p₁ : CopIdx G S a b g₁) (p₂ : CopIdx G S a b g₂)
    (h : cev G S a b g₁ p₁ = cev G S a b g₂ p₂) :
    cevEdge G S a b g₁ p₁ = cevEdge G S a b g₂ p₂ := by
  rw [cev_eq, cev_eq] at h
  exact (edgeFinset (blowupAsymFlag G S b a)).equivFin.injective h

/-! ### §D.4 Uniform copy-edge vertices and the family building blocks. -/

/-- `L(G')²`-flag adjacency decoded to `lineGraphSqAdj` on the underlying `G`-edges. -/
lemma lgsqFlag_adj_decode (G : Flag emptyType) (i j : Fin (lineGraphSqFlag G).size)
    (h : (lineGraphSqFlag G).graph.Adj i j) :
    lineGraphSqAdj G ((edgeFinset G).equivFin.symm i).val
      ((edgeFinset G).equivFin.symm j).val := by
  have h' := h
  rw [show i = (edgeFinset G).equivFin ((edgeFinset G).equivFin.symm i) from
        (Equiv.apply_symm_apply _ i).symm,
      show j = (edgeFinset G).equivFin ((edgeFinset G).equivFin.symm j) from
        (Equiv.apply_symm_apply _ j).symm] at h'
  exact (lgsqFlag_adj G _ _).mp h'

/-- Splitting a two-element-`Finset` equality into the two pairings. -/
lemma pair_eq_pair_cases {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b)
    (h : ({a, b} : Finset α) = {c, d}) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have ha : a ∈ ({c, d} : Finset α) := by rw [← h]; exact Finset.mem_insert_self _ _
  have hb : b ∈ ({c, d} : Finset α) := by
    rw [← h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact absurd (ha.trans hb.symm) hab
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact absurd (ha.trans hb.symm) hab

/-- Uniform copy-edge vertex: a copy of edge `g` indexed by `j : Fin (a*b)`. -/
noncomputable def ucev (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (hbip : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (g : ↥(edgeFinset G)) (j : Fin (a * b)) :
    Fin (lineGraphSqFlag (blowupAsymFlag G S b a)).size :=
  cev G S a b g (copyEquiv G S a b hbip g j)

/-- `ucev` is injective in `(edge, uniform copy index)`. -/
lemma ucev_inj (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (hbip : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (g₁ g₂ : ↥(edgeFinset G)) (j₁ j₂ : Fin (a * b))
    (h : ucev G S a b hbip g₁ j₁ = ucev G S a b hbip g₂ j₂) : g₁ = g₂ ∧ j₁ = j₂ := by
  have hE : cevEdge G S a b g₁ (copyEquiv G S a b hbip g₁ j₁)
      = cevEdge G S a b g₂ (copyEquiv G S a b hbip g₂ j₂) := cev_injEdge G S a b _ _ _ _ h
  have hg : g₁ = g₂ := by
    by_contra hne
    exact cevEdge_ne_of_edge_ne G S a b g₁ g₂ _ _ hne hE
  subst hg
  refine ⟨rfl, ?_⟩
  have hcopy : copyEquiv G S a b hbip g₁ j₁ = copyEquiv G S a b hbip g₁ j₂ := by
    by_contra hne
    exact cevEdge_ne_of_copy_ne G S a b g₁ _ _ hne hE
  exact (copyEquiv G S a b hbip g₁).injective hcopy

/-- Adjacency of two uniform copy-edge vertices from endpoint-conflict of originals. -/
lemma ucev_adj (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (hbip : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (g₁ g₂ : ↥(edgeFinset G)) (j₁ j₂ : Fin (a * b))
    (hne : cevEdge G S a b g₁ (copyEquiv G S a b hbip g₁ j₁)
        ≠ cevEdge G S a b g₂ (copyEquiv G S a b hbip g₂ j₂))
    (hR : Rrel G g₁.val g₂.val) :
    (lineGraphSqFlag (blowupAsymFlag G S b a)).graph.Adj
      (ucev G S a b hbip g₁ j₁) (ucev G S a b hbip g₂ j₂) := by
  unfold ucev
  exact cev_adj G S a b g₁ g₂ _ _ hne hR

/-! ### §D.5 The neighbourhood-edge lower bound (discharges `hLB`). -/

/-- **Weak neighbourhood-edge lower bound** (PROOF.md §7): on the asymmetric blow-up
`G' = blowupAsymFlag G S b a` of a bipartite host `G`, there is a copy `f'` of the
edge `f` with
`eIN(L(G')², f') ≥ (ab)²·eIN(L(G)²,f) + ab(ab−1)·deg_{L(G)²}(f)`.
Proved via two edge-disjoint injective `Finset` families (F4 cross-block, F3
intra-`f`-block). -/
theorem blowup_eIN_lb (G : Flag emptyType) (S : Finset (Fin G.size)) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hbip : ∀ u v : Fin G.size, G.graph.Adj u v → (u ∈ S ↔ v ∉ S))
    (f : Fin (lineGraphSqFlag G).size) :
    ∃ f' : Fin (lineGraphSqFlag (blowupAsymFlag G S b a)).size,
      (a * b) ^ 2 * edgesInNeighbourhood (lineGraphSqFlag G) f
          + (a * b) * (a * b - 1)
            * (univ.filter (fun k => (lineGraphSqFlag G).graph.Adj f k)).card
        ≤ edgesInNeighbourhood (lineGraphSqFlag (blowupAsymFlag G S b a)) f' := by
  classical
  set ef := (edgeFinset G).equivFin.symm f with hefdef
  set gk : Fin (lineGraphSqFlag G).size → ↥(edgeFinset G) :=
    fun k => (edgeFinset G).equivFin.symm k with hgkdef
  have hab : 0 < a * b := Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one ha)
    (lt_of_lt_of_le Nat.zero_lt_one hb)
  set j0 : Fin (a * b) := ⟨0, hab⟩ with hj0
  set nbrsF := univ.filter (fun k => (lineGraphSqFlag G).graph.Adj f k) with hnbrsF
  set P4 := (nbrsF ×ˢ nbrsF).filter
    (fun pr => pr.1 < pr.2 ∧ (lineGraphSqFlag G).graph.Adj pr.1 pr.2) with hP4
  -- Neighbour facts.
  have hnbr : ∀ k ∈ nbrsF, lineGraphSqAdj G ef.val (gk k).val := by
    intro k hk
    exact lgsqFlag_adj_decode G f k (Finset.mem_filter.mp hk).2
  have hne_ef : ∀ k ∈ nbrsF, ef ≠ gk k := by
    intro k hk h
    exact (hnbr k hk).2.2.1 (congrArg Subtype.val h)
  have hR_ef : ∀ k ∈ nbrsF, Rrel G ef.val (gk k).val :=
    fun k hk => lineGraphSqAdj_to_R _ _ _ (hnbr k hk)
  have hsymm_inj : ∀ i j : Fin (lineGraphSqFlag G).size, gk i = gk j → i = j :=
    fun i j h => (edgeFinset G).equivFin.symm.injective h
  refine ⟨ucev G S a b hbip ef j0, ?_⟩
  set a1 :
      (Fin (lineGraphSqFlag G).size × Fin (lineGraphSqFlag G).size)
        × (Fin (a * b) × Fin (a * b)) ⊕
      (Fin (lineGraphSqFlag G).size × (Fin (a * b) × Fin (a * b))) →
      Fin (lineGraphSqFlag (blowupAsymFlag G S b a)).size :=
    Sum.elim (fun u => ucev G S a b hbip (gk u.1.1) u.2.1)
      (fun w => ucev G S a b hbip (gk w.1) w.2.1) with ha1
  set a2 :
      (Fin (lineGraphSqFlag G).size × Fin (lineGraphSqFlag G).size)
        × (Fin (a * b) × Fin (a * b)) ⊕
      (Fin (lineGraphSqFlag G).size × (Fin (a * b) × Fin (a * b))) →
      Fin (lineGraphSqFlag (blowupAsymFlag G S b a)).size :=
    Sum.elim (fun u => ucev G S a b hbip (gk u.1.2) u.2.2)
      (fun w => ucev G S a b hbip ef w.2.2) with ha2
  set Src4 := P4 ×ˢ (Finset.univ : Finset (Fin (a * b) × Fin (a * b))) with hSrc4
  set Src3 := nbrsF ×ˢ ((Finset.univ : Finset (Fin (a * b)))
    ×ˢ ((Finset.univ : Finset (Fin (a * b))).erase j0)) with hSrc3
  set Src := Src4.disjSum Src3 with hSrc
  -- Membership extractors.
  have hP4mem : ∀ u, Sum.inl u ∈ Src → u.1 ∈ P4 :=
    fun u hu => (Finset.mem_product.mp (Finset.inl_mem_disjSum.mp hu)).1
  have hNmem : ∀ w, Sum.inr w ∈ Src → w.1 ∈ nbrsF :=
    fun w hw => (Finset.mem_product.mp (Finset.inr_mem_disjSum.mp hw)).1
  have hCmem : ∀ w, Sum.inr w ∈ Src → w.2.2 ≠ j0 := by
    intro w hw
    have := (Finset.mem_product.mp
      (Finset.mem_product.mp (Finset.inr_mem_disjSum.mp hw)).2).2
    exact (Finset.mem_erase.mp this).1
  -- From `u.1 ∈ P4`, the two endpoints are neighbours, ordered, adjacent.
  have hP4nb1 : ∀ u, Sum.inl u ∈ Src → u.1.1 ∈ nbrsF :=
    fun u hu => (Finset.mem_product.mp (Finset.mem_filter.mp (hP4mem u hu)).1).1
  have hP4nb2 : ∀ u, Sum.inl u ∈ Src → u.1.2 ∈ nbrsF :=
    fun u hu => (Finset.mem_product.mp (Finset.mem_filter.mp (hP4mem u hu)).1).2
  have hP4lt : ∀ u, Sum.inl u ∈ Src → u.1.1 < u.1.2 :=
    fun u hu => (Finset.mem_filter.mp (hP4mem u hu)).2.1
  have hP4adj : ∀ u, Sum.inl u ∈ Src → Rrel G (gk u.1.1).val (gk u.1.2).val :=
    fun u hu => lineGraphSqAdj_to_R _ _ _
      (lgsqFlag_adj_decode G u.1.1 u.1.2 (Finset.mem_filter.mp (hP4mem u hu)).2.2)
  -- `hv1`: f' adjacent to the first family member.
  have hv1 : ∀ t ∈ Src,
      (lineGraphSqFlag (blowupAsymFlag G S b a)).graph.Adj (ucev G S a b hbip ef j0) (a1 t) := by
    intro t ht
    cases t with
    | inl u =>
      simp only [ha1, Sum.elim_inl]
      exact ucev_adj G S a b hbip ef (gk u.1.1) j0 u.2.1
        (cevEdge_ne_of_edge_ne G S a b ef (gk u.1.1) _ _ (hne_ef u.1.1 (hP4nb1 u ht)))
        (hR_ef u.1.1 (hP4nb1 u ht))
    | inr w =>
      simp only [ha1, Sum.elim_inr]
      exact ucev_adj G S a b hbip ef (gk w.1) j0 w.2.1
        (cevEdge_ne_of_edge_ne G S a b ef (gk w.1) _ _ (hne_ef w.1 (hNmem w ht)))
        (hR_ef w.1 (hNmem w ht))
  -- `hv2`: f' adjacent to the second family member.
  have hv2 : ∀ t ∈ Src,
      (lineGraphSqFlag (blowupAsymFlag G S b a)).graph.Adj (ucev G S a b hbip ef j0) (a2 t) := by
    intro t ht
    cases t with
    | inl u =>
      simp only [ha2, Sum.elim_inl]
      exact ucev_adj G S a b hbip ef (gk u.1.2) j0 u.2.2
        (cevEdge_ne_of_edge_ne G S a b ef (gk u.1.2) _ _ (hne_ef u.1.2 (hP4nb2 u ht)))
        (hR_ef u.1.2 (hP4nb2 u ht))
    | inr w =>
      simp only [ha2, Sum.elim_inr]
      refine ucev_adj G S a b hbip ef ef j0 w.2.2 ?_ ?_
      · exact cevEdge_ne_of_copy_ne G S a b ef _ _
          ((copyEquiv G S a b hbip ef).injective.ne (Ne.symm (hCmem w ht)))
      · exact Or.inr (Or.inl (edgeFinset_adj G ef))
  -- `hadj12`: the two family members are adjacent (the neighbourhood edge).
  have hadj12 : ∀ t ∈ Src,
      (lineGraphSqFlag (blowupAsymFlag G S b a)).graph.Adj (a1 t) (a2 t) := by
    intro t ht
    cases t with
    | inl u =>
      simp only [ha1, ha2, Sum.elim_inl]
      have hgkne : gk u.1.1 ≠ gk u.1.2 :=
        fun h => (ne_of_lt (hP4lt u ht)) (hsymm_inj _ _ h)
      exact ucev_adj G S a b hbip (gk u.1.1) (gk u.1.2) u.2.1 u.2.2
        (cevEdge_ne_of_edge_ne G S a b (gk u.1.1) (gk u.1.2) _ _ hgkne)
        (hP4adj u ht)
    | inr w =>
      simp only [ha1, ha2, Sum.elim_inr]
      have hne : gk w.1 ≠ ef := Ne.symm (hne_ef w.1 (hNmem w ht))
      refine ucev_adj G S a b hbip (gk w.1) ef w.2.1 w.2.2 ?_ ?_
      · exact cevEdge_ne_of_edge_ne G S a b (gk w.1) ef _ _ hne
      · exact lineGraphSqAdj_to_R _ _ _ (lineGraphSqAdj_symm G _ _ (hnbr w.1 (hNmem w ht)))
  -- `hinj`: the combined family is injective as unordered pairs.
  have hinj : ∀ s ∈ Src, ∀ t ∈ Src,
      ({a1 s, a2 s} : Finset (Fin (lineGraphSqFlag (blowupAsymFlag G S b a)).size))
        = {a1 t, a2 t} → s = t := by
    intro s hs t ht hset
    have hab_s : a1 s ≠ a2 s :=
      (lineGraphSqFlag (blowupAsymFlag G S b a)).graph.ne_of_adj (hadj12 s hs)
    cases s with
    | inl u =>
      cases t with
      | inl u' =>
        simp only [ha1, ha2, Sum.elim_inl] at hset hab_s
        rcases pair_eq_pair_cases hab_s hset with ⟨E1, E2⟩ | ⟨E1, E2⟩
        · obtain ⟨he1, hj1⟩ := ucev_inj G S a b hbip _ _ _ _ E1
          obtain ⟨he2, hj2⟩ := ucev_inj G S a b hbip _ _ _ _ E2
          have hpr1 : u.1.1 = u'.1.1 := hsymm_inj _ _ he1
          have hpr2 : u.1.2 = u'.1.2 := hsymm_inj _ _ he2
          have hfst : u.1 = u'.1 := Prod.ext hpr1 hpr2
          have hsnd : u.2 = u'.2 := Prod.ext hj1 hj2
          exact congrArg Sum.inl (Prod.ext hfst hsnd)
        · obtain ⟨he1, -⟩ := ucev_inj G S a b hbip _ _ _ _ E1
          obtain ⟨he2, -⟩ := ucev_inj G S a b hbip _ _ _ _ E2
          have hpr1 : u.1.1 = u'.1.2 := hsymm_inj _ _ he1
          have hpr2 : u.1.2 = u'.1.1 := hsymm_inj _ _ he2
          exact absurd hpr1 (by
            have l1 := hP4lt u hs
            have l2 := hP4lt u' ht
            rw [hpr2] at l1
            exact ne_of_lt (lt_of_lt_of_le l1 (le_of_lt l2)))
      | inr w' =>
        simp only [ha1, ha2, Sum.elim_inl, Sum.elim_inr] at hset hab_s
        rcases pair_eq_pair_cases hab_s hset with ⟨_, E2⟩ | ⟨E1, _⟩
        · exact absurd (ucev_inj G S a b hbip _ _ _ _ E2).1
            (Ne.symm (hne_ef u.1.2 (hP4nb2 u hs)))
        · exact absurd (ucev_inj G S a b hbip _ _ _ _ E1).1
            (Ne.symm (hne_ef u.1.1 (hP4nb1 u hs)))
    | inr w =>
      cases t with
      | inl u' =>
        simp only [ha1, ha2, Sum.elim_inl, Sum.elim_inr] at hset hab_s
        rcases pair_eq_pair_cases hab_s hset with ⟨_, E2⟩ | ⟨_, E2⟩
        · exact absurd (ucev_inj G S a b hbip _ _ _ _ E2).1
            (hne_ef u'.1.2 (hP4nb2 u' ht))
        · exact absurd (ucev_inj G S a b hbip _ _ _ _ E2).1
            (hne_ef u'.1.1 (hP4nb1 u' ht))
      | inr w' =>
        simp only [ha1, ha2, Sum.elim_inr] at hset hab_s
        rcases pair_eq_pair_cases hab_s hset with ⟨E1, E2⟩ | ⟨E1, _⟩
        · obtain ⟨he1, hj1⟩ := ucev_inj G S a b hbip _ _ _ _ E1
          obtain ⟨-, hj2⟩ := ucev_inj G S a b hbip _ _ _ _ E2
          have hk : w.1 = w'.1 := hsymm_inj _ _ he1
          have hsnd : w.2 = w'.2 := Prod.ext hj1 hj2
          exact congrArg Sum.inr (Prod.ext hk hsnd)
        · exact absurd (ucev_inj G S a b hbip _ _ _ _ E1).1
            (Ne.symm (hne_ef w.1 (hNmem w hs)))
  -- Cardinalities.
  have heIN : edgesInNeighbourhood (lineGraphSqFlag G) f = P4.card := rfl
  have hSrc4card : Src4.card = (a * b) ^ 2 * P4.card := by
    rw [hSrc4, Finset.card_product]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    ring
  have hSrc3card : Src3.card = (a * b) * (a * b - 1) * nbrsF.card := by
    rw [hSrc3, Finset.card_product, Finset.card_product,
      Finset.card_erase_of_mem (Finset.mem_univ j0)]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_comm _ _
  have hcard :
      (a * b) ^ 2 * edgesInNeighbourhood (lineGraphSqFlag G) f
        + (a * b) * (a * b - 1) * nbrsF.card = Src.card := by
    rw [heIN, hSrc, Finset.card_disjSum, hSrc4card, hSrc3card]
  rw [hcard]
  exact edgesInNeighbourhood_ge (H := lineGraphSqFlag (blowupAsymFlag G S b a))
    (ucev G S a b hbip ef j0) Src a1 a2 hv1 hv2 hadj12 hinj

/-- **Unconditional transfer lemma** (Route 1, `hLB` discharged). For a
`(Δ, pΔ)`-biregular asymmetric bipartite host `G` (`p = a/b`), the asymmetric
blow-up `G' = blowupAsymFlag G S b a` (`S = hAsym.choose`) carries a copy `f'` of
every edge `f` whose σ-normalised squared-line-graph neighbourhood-edge density
dominates that of `f`:

`eIN(L(G)²,f) / C(2pΔ²,2)  ≤  eIN(L(G')²,f') / C(2Δ'²,2)`   (`Δ' = aΔ`).

This is `blowup_transfer` with its combinatorial hypothesis `hLB` **proven** via
`blowup_eIN_lb`; no hypothesis on the neighbourhood-edge count remains. -/
theorem blowup_transfer_uncond
    {G : Flag emptyType} {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a ≤ b)
    (hΔb : b ≤ maxDegree G)
    (hAsym : SecAsymmetricBipartiteBridge.IsAsymmetricBipartite ((a : ℝ) / b) G)
    (f : Fin (lineGraphSqFlag G).size) :
    ∃ f' : Fin (lineGraphSqFlag (blowupAsymFlag G hAsym.choose b a)).size,
      (edgesInNeighbourhood (lineGraphSqFlag G) f : ℝ)
          / (((a : ℝ) / b) * (maxDegree G : ℝ) ^ 2
              * (2 * ((a : ℝ) / b) * (maxDegree G : ℝ) ^ 2 - 1))
        ≤ (edgesInNeighbourhood (lineGraphSqFlag (blowupAsymFlag G hAsym.choose b a)) f' : ℝ)
          / ((a : ℝ) ^ 2 * (maxDegree G : ℝ) ^ 2
              * (2 * (a : ℝ) ^ 2 * (maxDegree G : ℝ) ^ 2 - 1)) := by
  obtain ⟨f', hLB⟩ := blowup_eIN_lb G hAsym.choose a b ha hb hAsym.choose_spec.1 f
  exact ⟨f', blowup_transfer ha hb hab hΔb hAsym f f' hLB⟩

end

end Davey2024.SecAsymBlowup
