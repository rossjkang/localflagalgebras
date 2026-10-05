import DaveyThesis2024.PentagonQOrbit
import DaveyThesis2024.CGraphBridge

/-!
# Item C3, first piece: every `CG2` flag comes from a `CGraph`

`CGraph.toGenFlag` (`CGraphBridge.lean:46`) goes one way.  C3 needs the other:
an 8-subset of an abstract host gives a `GenFlag` (through `genInducedSubflag`),
and the enumeration reasons about `CGraph 8`, so the two must be connected.

The bridge is that `SimpleGraph.fromRel` — which `toGenFlag` wraps its `Bool`
adjacency in — recovers a graph from its own adjacency relation, because a
`SimpleGraph` is symmetric and loopless.  So the passage is an *equality* of
flags, not merely an isomorphism, and nothing has to be transported along it.
-/

namespace Davey2024
namespace PentagonQOfFlag

open Classical

/-- `fromRel` recovers a graph from its own adjacency: the `≠` it inserts is
implied by irreflexivity, and the symmetrised `∨` by symmetry. -/
theorem fromRel_adj_self {n : ℕ} (H : SimpleGraph (Fin n)) :
    SimpleGraph.fromRel (fun i j => (decide (H.Adj i j) : Bool) = true) = H := by
  ext u v
  simp only [SimpleGraph.fromRel_adj, decide_eq_true_eq]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨h.ne, Or.inl h⟩

/-- The `CGraph` underlying a `CG2` flag. -/
noncomputable def ofFlag {n : ℕ}
    (F : GenFlag (colouredGraphUniverse 2) (GenFlagType.empty (colouredGraphUniverse 2)))
    (hn : F.size = n) : CGraph n where
  adj i j := decide ((F.str.1).Adj (hn ▸ i) (hn ▸ j))
  col v := F.str.2 (hn ▸ v)

/-- **C3.1.**  At the flag's own size, `ofFlag` is a genuine inverse of
`toGenFlag`: the two flags are *equal*, so no transport is needed. -/
theorem toGenFlag_ofFlag
    (F : GenFlag (colouredGraphUniverse 2) (GenFlagType.empty (colouredGraphUniverse 2))) :
    (ofFlag F rfl).toGenFlag = F :=
  GenFlag.empty_ext _ _ rfl (Prod.ext_iff.mpr ⟨fromRel_adj_self F.str.1, rfl⟩)

/-- **C.**  A flag of size exactly `8` *is* a `CGraph 8`'s flag.

`ofFlag F hn` lands in `CGraph n` and `toGenFlag_ofFlag` is stated at `hn := rfl`,
so it yields the `CGraph F.size` version while the rest of the chain is indexed
at `8`.  Rather than transport along `F.size = 8` — the `▸` bookkeeping this
project's notes record as a recurring cost — destructure the flag first and
substitute, which makes the two indices literally the same. -/
theorem exists_cgraph_of_size_eight
    (F : GenFlag (colouredGraphUniverse 2) (GenFlagType.empty (colouredGraphUniverse 2)))
    (h8 : F.size = 8) : ∃ g : CGraph 8, g.toGenFlag = F := by
  obtain ⟨sz, str, emb, ind, hsz⟩ := F
  subst h8
  refine ⟨ofFlag (⟨8, str, emb, ind, hsz⟩ :
    GenFlag (colouredGraphUniverse 2) (GenFlagType.empty (colouredGraphUniverse 2))) rfl, ?_⟩
  exact toGenFlag_ofFlag ⟨8, str, emb, ind, hsz⟩

/-- The same, carrying the two structural facts every consumer needs.  `ofFlag`
reads its adjacency off a `SimpleGraph`, so symmetry and irreflexivity come for
free — but `exists_cgraph_of_size_eight` did not say so, and both
`muG_eq_sum_nzFinset` and `genClass_eq_of_cPermCount_ne_zero` ask for them. -/
theorem exists_cgraph_of_size_eight_struct
    (F : GenFlag (colouredGraphUniverse 2) (GenFlagType.empty (colouredGraphUniverse 2)))
    (h8 : F.size = 8) :
    ∃ g : CGraph 8, g.toGenFlag = F ∧
      (∀ i j, g.adj i j = g.adj j i) ∧ (∀ i, g.adj i i = false) := by
  obtain ⟨sz, str, emb, ind, hsz⟩ := F
  subst h8
  refine ⟨ofFlag (⟨8, str, emb, ind, hsz⟩ :
    GenFlag (colouredGraphUniverse 2) (GenFlagType.empty (colouredGraphUniverse 2))) rfl,
    toGenFlag_ofFlag ⟨8, str, emb, ind, hsz⟩, ?_, ?_⟩
  · intro i j; simp [ofFlag, SimpleGraph.adj_comm]
  · intro i; simp [ofFlag]

#print axioms exists_cgraph_of_size_eight_struct
#print axioms exists_cgraph_of_size_eight
#print axioms fromRel_adj_self
#print axioms toGenFlag_ofFlag

end PentagonQOfFlag
end Davey2024
