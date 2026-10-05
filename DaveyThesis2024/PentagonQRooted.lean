import DaveyThesis2024.PentagonQWeights

/-!
# (a0): the rooted count as a `Finset.filter`

`PentagonQWeights.rootedCount` counts via `embeds`, a depth-first enumerator
written for the purpose.  When this file was written nothing proved that
enumerator ranges over exactly the injective, colour- and adjacency-preserving
maps with the root side condition, so `O_Q_weight_eq_combinatorial` connected
the certificate's weights to *that enumerator's output*, not to
`genInducedCount`, the development's own embedding count.  The asymptotic
identity needs the latter.

This file states the same count in the `Finset.filter` shape that
`CGraphBridge.cInducedCount_eq_genInducedCount'` already bridges; the agreement
with the enumerator is proved in `PentagonQWeightsBridge`, which is kept
separate because its `native_decide` was the dominant cost in the development
until the 2026-10-05 partition split it across four chunks, and would otherwise
re-elaborate on every edit to a proof in this file.

## What this closes

`cInducedCount` (`CGraphBridge.lean:37`) ranges over the same function space and
already bridges to `genInducedCount` for symmetric irreflexive adjacency.  What
it lacks is the root side condition -- the paper's `n_i` counts only embeddings
whose every out-of-image vertex is adjacent to the image of the vertex labelled
`1`.  `cRootedCount` below is `cInducedCount` plus exactly that clause.

So after this file, obligation (b)'s `n_i` are no longer "whatever `embeds`
returns": they are a count over the maps `genInducedCount` counts, subject to a
predicate on the image.  **That remaining step** — `cRootedCount = genInducedCount`-with-side-condition —
is `cRootedCount_eq_genRootedCount` at the foot of this file, proved on the
standard axioms.  It was outstanding when this header was first written; with it
and `PentagonQWeightsBridge` both proved, the chain from the certificate's
weights to `genInducedCount` is complete.

## Where the expensive check lives

See `PentagonQWeightsBridge`.
-/

namespace Davey2024
namespace PentagonQRooted

open Davey2024.PentagonQBasis Davey2024.PentagonQWeights Finset

/-- **The embedding half of the bridge, extracted.**  For an injective `f`,
preserving colours and Bool-adjacency is exactly pulling the target structure
back to the source.

This is the `have adj_iff` inside `CGraphBridge.cInducedCount_eq_genInducedCount'`,
lifted verbatim so the *rooted* count can reuse it.  The original is left
untouched: `CGraphBridge` sits deep in the import graph and editing it rebuilds
the 10k-line bridge and everything after. -/
theorem comap_iff_of_injective {n₁ n₂ : Nat} (F : CGraph n₁) (G : CGraph n₂)
    (hFs : ∀ i j, F.adj i j = F.adj j i) (hFi : ∀ i, F.adj i i = false)
    (hGs : ∀ i j, G.adj i j = G.adj j i) (hGi : ∀ i, G.adj i i = false)
    (f : Fin n₁ → Fin n₂) (hinj : Function.Injective f) :
    (((∀ i : Fin n₁, F.col i = G.col (f i)) ∧
      (∀ i j : Fin n₁, F.adj i j = G.adj (f i) (f j))) ↔
     (colouredGraphUniverse 2).comap f G.toGenFlag.str = F.toGenFlag.str) := by
  simp only [colouredGraphUniverse, CGraph.toGenFlag]
  constructor
  · rintro ⟨hcol, hadj⟩
    apply Prod.ext
    · -- Graph: comap f (fromRel G.adj) = fromRel F.adj
      ext u v
      simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj]
      -- Both sides: (_ ≠ _) ∧ (Bool↑Prop ∨ Bool↑Prop)
      -- For injective f: f u ≠ f v ↔ u ≠ v
      -- Bool adj is preserved by hadj, symmetry makes Or redundant
      constructor
      · rintro ⟨hfne, h⟩
        refine ⟨fun huv => hfne (congr_arg f huv), ?_⟩
        rcases h with h | h
        · left; rw [hadj u v]; exact h
        · right; rw [hadj v u]; exact h
      · rintro ⟨hne, h⟩
        refine ⟨fun h' => hne (hinj h'), ?_⟩
        rcases h with h | h
        · left; rw [← hadj u v]; exact h
        · right; rw [← hadj v u]; exact h
    · funext u; exact (hcol u).symm
  · intro hstr
    obtain ⟨hg, hc⟩ := Prod.mk.inj hstr
    refine ⟨fun i => (congr_fun hc i).symm, fun i j => ?_⟩
    by_cases hij : i = j
    · subst hij; simp only [hFi, hGi]
    · -- Use the graph equality at (i,j)
      have hge : ∀ a b : Fin n₁,
          (SimpleGraph.comap f (SimpleGraph.fromRel fun i j => ↑(G.adj i j))).Adj a b ↔
          (SimpleGraph.fromRel fun i j => ↑(F.adj i j)).Adj a b := by
        have hge' := hg
        intro a b
        rw [show (SimpleGraph.fromRel fun i j => ↑(G.adj i j)).comap f =
                SimpleGraph.fromRel fun i j => ↑(F.adj i j) from by exact_mod_cast hge']
      simp only [SimpleGraph.comap_adj, SimpleGraph.fromRel_adj] at hge
      -- Case split on Bool values
      have fne : f i ≠ f j := fun h => hij (hinj h)
      cases hF : F.adj i j <;> cases hG : G.adj (f i) (f j)
      · rfl
      · exfalso
        have h1 : (f i ≠ f j ∧ ((↑(G.adj (f i) (f j)) : Prop) ∨ (↑(G.adj (f j) (f i))))) := by
          exact ⟨fne, Or.inl (by simp [hG])⟩
        have h2 := (hge i j).mp h1
        obtain ⟨_, h3⟩ := h2
        cases h3 with
        | inl h => simp [hF] at h
        | inr h =>
          -- h : ↑(F.adj j i), but F.adj j i = F.adj i j = false
          have : F.adj j i = false := by rw [← hFs i j]; exact hF
          exact absurd h (by rw [this]; exact Bool.false_ne_true)
      · exfalso
        have h1 : (i ≠ j ∧ ((↑(F.adj i j) : Prop) ∨ (↑(F.adj j i)))) := by
          exact ⟨hij, Or.inl (by simp [hF])⟩
        have h2 := (hge i j).mpr h1
        obtain ⟨_, h3⟩ := h2
        cases h3 with
        | inl h => simp [hG] at h
        | inr h =>
          -- h : ↑(G.adj (f j) (f i)), but G.adj (f j) (f i) = G.adj (f i) (f j) = false
          have : G.adj (f j) (f i) = false := by rw [← hGs (f i) (f j)]; exact hG
          exact absurd h (by rw [this]; exact Bool.false_ne_true)
      · rfl

/-- The three rooted types as `CGraph`s, root at vertex `0`. -/
def patC (p : Pat) (n : Nat) : CGraph n where
  adj i j := (p.padj[i.val]!)[j.val]!
  col v := if p.cols[v.val]! == 1 then 1 else 0

/-- Injective, colour- and adjacency-preserving maps whose every out-of-image
vertex is adjacent to the image of the root.  This is the paper's `n_i`, stated
over the same function space `cInducedCount` uses. -/
def cRootedCount {m : Nat} (F : CGraph (m + 1)) (G : CGraph 8) : Nat :=
  (univ : Finset (Fin (m + 1) → Fin 8)).filter (fun f =>
    (∀ i j, f i = f j → i = j) ∧
    (∀ i, F.col i = G.col (f i)) ∧
    (∀ i j, F.adj i j = G.adj (f i) (f j)) ∧
    (∀ w : Fin 8, (∀ i, f i ≠ w) → G.adj (f 0) w = true)) |>.card

/-- The rooted count at the **`GenFlag` level**: induced embeddings of `F` into
`G` — the very objects `genInducedCount` counts — whose every out-of-image
vertex is adjacent to the image of the root.  The side condition is phrased on
`G`'s Bool adjacency, the same data the flag's structure is built from. -/
noncomputable def genRootedCount {m : Nat} (F : CGraph (m + 1)) (G : CGraph 8) : ℕ :=
  Nat.card {e : GenInducedEmbedding CG2 (GenFlagType.empty CG2) F.toGenFlag G.toGenFlag //
    ∀ w : Fin 8, (∀ i, e.toFun i ≠ w) → G.adj (e.toFun ⟨0, Nat.succ_pos m⟩) w = true}

/-- **(a0), the proof half.**  The `Finset` count and the `GenFlag`-level count
are the same number, by an explicit equivalence: a map satisfying the four
clauses *is* an induced embedding carrying the root condition, and conversely.
The `compat` field is free because the flags are `∅`-typed, so its index type is
empty. -/
theorem cRootedCount_eq_genRootedCount {m : Nat} (F : CGraph (m + 1)) (G : CGraph 8)
    (hFs : ∀ i j, F.adj i j = F.adj j i) (hFi : ∀ i, F.adj i i = false)
    (hGs : ∀ i j, G.adj i j = G.adj j i) (hGi : ∀ i, G.adj i i = false) :
    cRootedCount F G = genRootedCount F G := by
  unfold cRootedCount genRootedCount
  rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  apply Fintype.card_congr
  exact {
    toFun := fun x =>
      ⟨{ toFun := x.1
         injective := fun a b h => x.2.1 a b h
         isInduced :=
           (comap_iff_of_injective F G hFs hFi hGs hGi x.1 (fun a b h => x.2.1 a b h)).mp
             ⟨x.2.2.1, x.2.2.2.1⟩
         compat := fun i => i.elim0 }, x.2.2.2.2⟩
    invFun := fun y =>
      ⟨y.1.toFun,
        fun a b h => y.1.injective h,
        ((comap_iff_of_injective F G hFs hFi hGs hGi y.1.toFun y.1.injective).mpr
          y.1.isInduced).1,
        ((comap_iff_of_injective F G hFs hFi hGs hGi y.1.toFun y.1.injective).mpr
          y.1.isInduced).2,
        y.2⟩
    left_inv := fun x => rfl
    right_inv := fun y => rfl }

#print axioms cRootedCount_eq_genRootedCount
#print axioms comap_iff_of_injective

end PentagonQRooted
end Davey2024
