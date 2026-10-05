import DaveyThesis2024.PartitionExp.Sanity

/-! Partition experiment, chunk 2 of 4: basis indices [4648, 6972).

One of four independent chunks of `rootedCount_eq_cRootedCount`. Total CPU
work is unchanged by splitting; only scheduling differs, and Lake builds the
chunks concurrently, so a cold build pays roughly one chunk rather than four.

**In the default build since 2026-10-05**, when `PentagonQWeightsBridge` began
restating its theorem from `PartitionExp.Combine`. -/

namespace Davey2024.PartitionExp

set_option linter.style.nativeDecide false in
theorem chunk2 : chunkOK 4648 2324 = true := by native_decide

end Davey2024.PartitionExp
