import DaveyThesis2024.PartitionExp.Chunk0
import DaveyThesis2024.PartitionExp.Chunk1
import DaveyThesis2024.PartitionExp.Chunk2
import DaveyThesis2024.PartitionExp.Chunk3

/-!
# Recombining the partitioned bridge check

`PentagonQWeightsBridge.rootedCount_eq_cRootedCount` is one `native_decide`
over all 9,295 basis flags, and as a single check it was too slow for a CI
ceiling.  Split into four independent chunk modules Lake schedules them
concurrently, so a cold build pays roughly one chunk rather than four.

This module puts the pieces back together: from the four range-restricted
`chunkOK` facts, the original statement over `Fin basisSize`.

**Verified a drop-in replacement**, by three checks in increasing strength:

* a `set_option pp.all` dump of both theorems is textually identical, down to
  the implicit `m` in `cRootedCount` (3 for `patC tau1 4`, 4 for the two at 5)
  and the `OfNat` literal encodings;
* a direct ascription of this theorem to the original's fully-qualified type
  elaborates;
* the equation `@original = @partitioned` is well-typed.

Note on that third one: **the `rfl` is not what does the work.** Elaborating
the equation forces the two types to unify, and once that succeeds `rfl`
closes by proof irrelevance and adds nothing — so the content is "the equation
is well-typed", not "it closes by `rfl`". The first two checks are the
stronger evidence. Negative controls (a dropped conjunct, `patC tau2 4` in the
second, conjuncts 2 and 3 swapped) all correctly fail to elaborate.

Both carry
`[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`.

**Where the content sits.** Of the 69 flags with nonzero `μ`, 61 fall in
chunk 0 and 8 in chunk 3; chunks 1 and 2 verify `0 = 0` throughout. That is
not a partition defect — it is exactly what the original verifies on those
indices, over 8^5 maps per flag — but those two chunks cannot catch an error
that only shows on the nonzero flags.
-/

namespace Davey2024.PartitionExp
open Davey2024.PentagonQBasis Davey2024.PentagonQWeights Davey2024.PentagonQRooted

/-- A chunk fact discharges every index inside its range. -/
theorem ok_of_chunk {lo len : Nat} (h : chunkOK lo len = true)
    (k : Fin basisSize) (h1 : lo ≤ k.val) (h2 : k.val < lo + len) : ok k = true := by
  rw [chunkOK, List.all_eq_true] at h
  have hm : k.val ∈ List.range' lo len := List.mem_range'_1.mpr ⟨h1, h2⟩
  have hk := h _ hm
  simpa [k.isLt] using hk

/-- **The four chunks cover `Fin basisSize`.** -/
theorem all_ok (k : Fin basisSize) : ok k = true := by
  have hlt : k.val < 9295 := k.isLt
  by_cases h0 : k.val < 2324
  · exact ok_of_chunk chunk0 k (Nat.zero_le _) (by omega)
  · by_cases h1 : k.val < 4648
    · exact ok_of_chunk chunk1 k (by omega) (by omega)
    · by_cases h2 : k.val < 6972
      · exact ok_of_chunk chunk2 k (by omega) (by omega)
      · exact ok_of_chunk chunk3 k (by omega) (by omega)

/-- **The original statement**, recovered from the partition: identical in form
to `PentagonQWeightsBridge.rootedCount_eq_cRootedCount`, but paid for in four
parallel pieces. -/
theorem rootedCount_eq_cRootedCount_partitioned :
    ∀ k : Fin basisSize,
      rootedCount (flagBasisCGraph k) tau1 = cRootedCount (patC tau1 4) (flagBasisCGraph k) ∧
      rootedCount (flagBasisCGraph k) tau2 = cRootedCount (patC tau2 5) (flagBasisCGraph k) ∧
      rootedCount (flagBasisCGraph k) tau3 = cRootedCount (patC tau3 5) (flagBasisCGraph k) := by
  intro k
  have h := all_ok k
  rw [ok, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end Davey2024.PartitionExp
