# SEC counterexample-search results (Phase C/D/D2/E/D_asym)

**Date**: 2026-05-16 (Δ=17..19 added; asymmetric Faudree Δ_X ∈ {2,3,4} added)
**Source plan**: the development notes
**Tooling**:
- `local-flags-certificates/sec_search/compute_chi_s.py` — SAT-based exact χ'_s.
- `local-flags-certificates/sec_search/fast_check.py` — multi-stage
  bound check: L²-complete shortcut → DSATUR greedy upper bound →
  SAT fallback. 10–12× faster than SAT-on-everything.
- `local-flags-certificates/sec_search/sweep.py` — stream sweep
  (`--fast` uses fast_check; default uses single-SAT-call).
- nauty 2.8.8 (`geng`, `genbg`) for graph enumeration.

**Speedup table**: switching from SAT-on-everything to greedy-DSATUR
to C-implemented DSATUR + 8-way parallel:

| Sweep | Graphs | Python SAT | Python DSATUR | C single | Parallel-8 + C |
|---|---:|---:|---:|---:|---:|
| Δ=4 general n=14 | 88,168 | 329s (265 g/s) | 28s (3,160 g/s) | 4s (22k g/s) | **1s (88k g/s)** |
| Δ=4 general n=16 | 8,037,418 | (~9h est) | 53 min (2.5k g/s) | — | — |
| Δ=4 bipartite n=20 | 121,785 | 537s | 92s | — | — |
| Δ=4 bipartite n=22 | 5,582,592 | — | (~70 min est) | — | 17.5 min (5.3k g/s) |
| **Δ=4 bipartite n=24** | **317,579,563** | — | — | — | **3h 37min (24.4k g/s)** |

**329× total speedup** from original Python SAT to 8-way parallel C.

All Δ=4 small-n graphs have actual χ'_s ≤ 16–17, well under the bound
20 (general) or 16 (bipartite). DSATUR with multi-shot random orderings
finds a valid colouring at ≤ bound in microseconds — no SAT needed.

The C `fast_check` binary (`local-flags-certificates/sec_search/fast_check.c`,
~330 LOC) implements graph6 parsing + L²(G) bitset construction + DSATUR
greedy in a single fast pass. Compiled with `clang -O3 -march=native`.
Throughput is ~22k graphs/sec per core; parallelism is then nauty-bound
(genbg becomes the bottleneck at n=22+).

**Tool capacity** (current, after extension to 512-bit for Δ=17+):

| Bitset | Type | Limit |
|---|---|---:|
| `adj[v]` (vertex neighbours) | `uint64_t` | n ≤ 64 |
| `sadj[e]` (strong-adjacency in L²) | `ebitset_t = uint64_t[8]` | m ≤ 512 edges |
| `sat[v]` (forbidden colours per edge-vertex) | `ebitset_t = uint64_t[8]` | bound ≤ 512 colours |

This covers all conjecture bounds and edge counts at Δ ≤ 22 in K_{n,n}
at n=23 (m=506), and Δ=17 general at n=64 (m≤544 just fits on the
edge side for sparse cases). Earlier intermediate caps were 128-bit
(`__uint128_t`, used through Δ≤11) and 256-bit (`uint64_t[4]`, used
through Δ=16).

**Bipartite generator capacity**: `nauty`'s default `genbg` is capped
at `MAXN1=24` (`n1+n2 ≤ 32`). For Δ≥17 bipartite we built `genbgL`
(`make genbgL` with `MAXN1=30`, handles `n1+n2 ≤ 60`); the v1 sweep
silently produced 0 graphs for all Δ≥17 bipartite cases until this
was diagnosed.

Safety: explicit `if (inv == 0) return -1` guards prevent undefined
behaviour at the bound boundary; `ebs_ctz` is called only after
explicit zero-check via `ebs_is_zero`.

## Verdict

**No counterexample found** to either headline conjecture in the
searched region across Δ ∈ {3, 4, 5, 6, 7, 8} (~701M graphs).
Δ=3 consistency-check panels confirm SAT/DSATUR pipeline soundness
against known structural theorems (Andersen 1992 cubic ≤10;
Steger–Yu 1993 cubic bipartite ≤9).

| Δ | Conjecture | n range searched | Graphs | Result |
|---:|---|---|---:|---|
| 4 | EN | exhaustive ≤16 | 8.1M | hold |
| 4 | Faudree bip | exhaustive ≤24 | 323M | hold |
| 5 | EN | exhaustive ≤14 | 3.5M | hold |
| 5 | Faudree bip | exhaustive ≤22 | 157M | hold |
| 6 | EN | exhaustive ≤14 | 21.6M | hold |
| 6 | Faudree bip | exhaustive ≤22 | 157M | hold |
| 7 | EN | exhaustive ≤14 | 21.6M | hold |
| 7 | Faudree bip | exhaustive ≤22 | 5.6M | hold |
| 8 | EN | exhaustive ≤14 | 3.5M | hold |
| 8 | Faudree bip | exhaustive ≤22 | 7.5k | hold |
| 9 | EN | exhaustive ≤14 | 88k | hold |
| 9 | Faudree bip | exhaustive ≤24 | 56k | hold |
| 10 | EN | exhaustive ≤14 | 540 | hold |
| 10 | Faudree bip | exhaustive ≤26 | 481k | hold |
| 11 | EN | **exhaustive ≤16** | **8.0M** | hold |
| 11 | Faudree bip | exhaustive ≤26 | 24 | hold |
| 12 | EN | exhaustive ≤16 | 4.2k | hold |
| 12 | Faudree bip | exhaustive ≤28 | 34 | hold |
| 13 | EN | exhaustive ≤16 | 21 | hold |
| 13 | Faudree bip | exhaustive ≤28 | 1 | hold |
| 14 | EN | exhaustive ≤18 | 42k | hold |
| 14 | Faudree bip | exhaustive ≤30 | 1 | hold |
| 15 | EN | exhaustive ≤18 | 33 | hold |
| 15 | Faudree bip | exhaustive ≤32 | 1 | hold |
| 16 | EN | exhaustive ≤20 | 516k | hold |
| 16 | Faudree bip | exhaustive ≤32 (K_{16,16}) | 1 | hold |
| 17 | EN | exhaustive ≤20 (n=22 TIMEOUT/skip) | 50 | hold |
| 17 | Faudree bip | exhaustive ≤38 (20+20 TIMEOUT/skip) | 107 | hold |
| 18 | EN | exhaustive ≤22 (n=24 TIMEOUT/skip) | 7.37M | hold |
| 18 | Faudree bip | exhaustive ≤40 (21+21 TIMEOUT/skip) | 139 | hold |
| 19 | EN | exhaustive ≤22 (n=24 TIMEOUT/skip) | 74 | hold |
| 19 | Faudree bip | exhaustive ≤42 (22+22 TIMEOUT/skip) | 167 | hold |
| 2 | Faudree asym (×Δ_Y∈{3,4,5}) | smallest 5 splits per row | 366,207 | hold |
| 3 | Faudree asym (×Δ_Y∈{4,5,6}) | smallest 3 splits per row | 2,575,851 | hold |
| 4 | Faudree asym (×Δ_Y∈{5,6,7}) | smallest 2 splits per row | 1,341,388 | hold |

## Phase C: Erdős–Nešetřil at Δ=4 (general 4-regular)

Conjecture: χ'_s(G) ≤ 1.25·Δ² = **20** for Δ=4.
Search: exhaustive enumeration of all connected 4-regular graphs up to n=16.

| n | #4-reg connected graphs | candidates (χ'_s > 20) | runtime | path |
|---:|---:|---:|---:|---|
| 8 | 6 | 0 | 0.01s | SAT |
| 10 | 59 | 0 | 0.18s | SAT |
| 12 | 1,544 | 0 | 4.8s | SAT |
| 14 | 88,168 | 0 | 329s (slow) / 28s (fast) | SAT / DSATUR |
| **16** | **8,037,418** | **0** | **3,185s (~53 min, fast)** | **DSATUR** |
| **total ≤16** | **8,127,195** | **0** | **~58 min total** | |

**Result: every 4-regular connected graph on ≤16 vertices satisfies
χ'_s ≤ 20.** The Erdős–Nešetřil conjecture holds exhaustively at
Δ=4 in this regime. **All 8M n=16 graphs resolve via DSATUR greedy
alone — zero SAT calls needed.**

Pending (multi-hour): n=18 (~10⁹ graphs, would need parallel +
further engineering).

## Phase D: Faudree at Δ=4 (bipartite 4-regular)

Conjecture: χ'_s(G) ≤ Δ² = **16** for bipartite Δ=4.
Search: exhaustive enumeration of all connected 4-regular bipartite
graphs up to n=22 (split 11+11).

| n | split | #4-reg bipartite | candidates (χ'_s > 16) | runtime |
|---:|---|---:|---:|---:|
| 8  | 4+4   | 1 (K_{4,4}) | 0 | 0.001s |
| 10 | 5+5   | 1 | 0 | 0.002s |
| 12 | 6+6   | 4 | 0 | 0.009s |
| 14 | 7+7   | 16 | 0 | 0.047s |
| 16 | 8+8   | 193 | 0 | 0.65s |
| 18 | 9+9   | 3,528 | 0 | 12.9s |
| 20 | 10+10 | 121,785 | 0 | 537s slow / 92s fast |
| 22 | 11+11 | 5,582,592 | 0 | 1050s (~17.5 min, 8-way parallel) |
| **24** | **12+12** | **317,579,563** | **0** | **13,040s (~3h 37min, 8-way parallel + C)** |
| **total ≤24** | | **323,287,683** | **0** | **~4h** |

**Result: every 4-regular connected bipartite graph on ≤24 vertices
satisfies χ'_s ≤ 16.** The Faudree bipartite conjecture holds
exhaustively in this regime. Combined: **323.3 million graphs swept,
0 counterexamples.**

For 4-regular bipartite the two sides must have equal size (`4|A|=|E|=4|B|`),
so splits are forced 4+4 → 5+5 → ... → 12+12. The next case (n=26,
split 13+13) likely has ~10¹⁰ graphs and is beyond single-machine
exhaustive enumeration without further optimisation.

(Initial slice 0/64 estimate had suggested ~71M total at n=24; actual
came out 4.4× larger at 318M. nauty's residue partition has high
variance per residue class for this graph family.)

## Phase D2: Δ=3 consistency check (SAT pipeline soundness)

Confirms that the SAT pipeline correctly bounds χ'_s on regimes where
the answer is known by theorem.

### Cubic general (Andersen 1992: χ'_s ≤ 10)

| n | #cubic connected | candidates (χ'_s > 10) | runtime |
|---:|---:|---:|---:|
| 8 | 5 | 0 | 0.003s |
| 10 | 19 | 0 | 0.012s |
| 12 | 85 | 0 | 0.063s |
| 14 | 509 | 0 | 0.43s |
| 16 | 4,060 | 0 | 4.0s |
| **total ≤16** | **4,678** | **0** | **~5s** |

### Cubic bipartite (Steger-Yu 1993: χ'_s ≤ 9)

| n | split | #cubic bipartite | candidates (χ'_s > 9) | runtime |
|---:|---|---:|---:|---:|
| 6  | 3+3 | 1 (K_{3,3}) | 0 | <0.001s |
| 8  | 4+4 | 1 | 0 | 0.001s |
| 10 | 5+5 | 2 | 0 | 0.002s |
| 12 | 6+6 | 6 | 0 | 0.006s |
| 14 | 7+7 | 15 | 0 | 0.013s |
| 16 | 8+8 | 48 | 0 | 0.047s |
| **total ≤16** | | **73** | **0** | **~0.1s** |

**Both consistency checks pass on every graph in their range.** This
gives confidence that the Phase C/D negative results are pipeline-sound,
not pipeline-bug.

## Phase C5/D5: Δ=5 first-pass

Both conjectures are open at Δ=5 (no published structural proofs that
cover this regime; Cranston 2006 handles only Δ=4, and Bonamy-Perrett-Postle
2022's asymptotic 1.772·Δ² requires very large Δ to be tight).

### Δ=5 general (Erdős–Nešetřil: χ'_s ≤ 1.25·25 = 31)

| n | #5-reg connected | candidates | runtime |
|---:|---:|---:|---:|
| 10 | 60 | 0 | <0.1s |
| 12 | 7,848 | 0 | 0.5s |
| 14 | 3,459,383 | 0 | 177s (single-thread C) |
| **total ≤14** | **3,467,291** | **0** | ~3 min |

n=16 has billions of graphs (next-step growth ratio is ~500-1000×) —
beyond what's tractable without further engineering.

### Δ=5 bipartite (Faudree: χ'_s ≤ Δ² = 25)

| n | split | #5-reg bipartite | candidates | runtime |
|---:|---|---:|---:|---:|
| 10 | 5+5 | 1 (K_{5,5}) | 0 | <0.1s |
| 12 | 6+6 | 1 | 0 | <0.1s |
| 14 | 7+7 | 4 | 0 | <0.1s |
| 16 | 8+8 | 51 | 0 | <0.1s |
| 18 | 9+9 | 3,529 | 0 | 0.4s |
| 20 | 10+10 | 601,054 | 0 (after 20-shot DSATUR) | 67s |
| **22** | **11+11** | **156,473,847** | **0** | **4225s (~70 min, 8-way parallel + C)** |
| **total ≤22** | | **157,078,487** | **0** | **~71 min** |

K_{5,5} attains χ'_s = 25 exactly (the Faudree bound at Δ=5). No
5-regular bipartite graph in the searched range exceeds it.

## Phase C6/D6: Δ=6 first-pass

### Δ=6 general (Erdős-Nešetřil: χ'_s ≤ 1.25·36 = 45)

| n | #6-reg connected | candidates | runtime |
|---:|---:|---:|---:|
| 8 | 1 | 0 | <0.1s |
| 10 | 21 | 0 | <0.1s |
| 12 | 7,849 | 0 | <1s |
| 14 | 21,609,300 | 0 | 563s (8-way parallel) |
| **total ≤14** | **21,617,171** | **0** | ~10 min |

### Δ=6 bipartite (Faudree: χ'_s ≤ 36)

| n | split | #6-reg bipartite | candidates | runtime |
|---:|---|---:|---:|---:|
| 12 | 6+6 | 1 (K_{6,6}) | 0 | <0.1s |
| 14 | 7+7 | 1 | 0 | <0.1s |
| 16 | 8+8 | 7 | 0 | <0.1s |
| 18 | 9+9 | 224 | 0 | <0.1s |
| 20 | 10+10 | 121,790 | 0 | ~20s |
| **22** | **11+11** | **156,473,848** | **0** | **19630s (~5h 27m with 1h pause; ~4h 27m active, 8-way parallel + C)** |
| **total ≤22** | | **156,595,871** | **0** | **~4.5h** |

K_{6,6} attains χ'_s = 36 exactly (Faudree-tight at Δ=6). No 6-regular
bipartite graph in the searched range exceeds it.

**Tool extension**: n=22 (11+11) has m=66 > 64, so `fast_check.c` was
bumped from `uint64_t` to `__uint128_t` edge bitsets (MAX_M=128).
Curious coincidence: the n=22 count for Δ=6 bipartite (156,473,848)
matches Δ=5 bipartite n=22 (156,473,847) within 1 — likely numerical
coincidence but cross-checking via independent enumeration would
confirm.

## Phase C9..C16, D9..D16: Δ ∈ {9..16} pass

Run via `run_d9_d16_v2.sh` (256-bit fast_check tool, parallel 8-way,
30-min per-case cap, total wall ~10 min). All cases below completed
fully and confirmed 0 counterexamples.

### Δ=9..16 general (Erdős–Nešetřil ≤ ⌈1.25·Δ²⌉)

| Δ | bound | largest n | graphs | runtime |
|---:|---:|---:|---:|---:|
| 9 | 102 | 14 | 88,193 | 5s |
| 10 | 125 | 14 | 540 | 5s |
| 11 | 152 | **16** | **8,037,796** | **281s** |
| 12 | 180 | 16 | 4,207 | 5s |
| 13 | 212 | 16 | 21 | 5s |
| 14 | 245 | 18 | 42,110 | 5s |
| 15 | 282 | 18 | 33 | 5s |
| 16 | 320 | **20** | **516,344** | **40s** |

### Δ=9..16 bipartite (Faudree ≤ Δ²)

| Δ | bound | largest split | graphs | runtime |
|---:|---:|---:|---:|---:|
| 9  | 81  | 12+12 | 56,349 | 10s |
| 10 | 100 | **13+13** | **481,309** | **76s** |
| 11 | 121 | 13+13 | 24 | 5s |
| 12 | 144 | 14+14 | 34 | 5s |
| 13 | 169 | 14+14 | 1 | 5s |
| 14 | 196 | 15+15 | 1 | 5s |
| 15 | 225 | 16+16 | 1 | 5s |
| 16 | 256 | 16+16 (= K_{16,16}) | 1 | 5s |

All cases completed within the 30-min budget (each Δ=9..16 sweep takes
≤ 5 minutes wall time). **Zero counterexamples** across all 36 cases.

The "small counts" for high Δ are due to the complement bijection in
either K_n or K_{n_1,n_2}: at fixed n, Δ-regular ↔ (n-1-Δ)-regular
graphs (general) or (n_1-Δ)-regular (bipartite K_{n_1,n_2}). For Δ
near the maximum n-1 (or n_A for bipartite), the complement is
near-trivial (matching or sparse).

## Phase C17..C19, D17..D19: Δ ∈ {17..19} pass

Run via `run_d17_d20.sh` (Δ=17 + Δ=18 general + bipartite section)
followed by `run_d17_d20_resume.sh` (corrected bipartite + Δ=19),
30-min per-case strict cap, 8-way parallel. Δ=20 was queued but not
run (user pause). All reported cases below have **zero counterexamples**.

**Tool extension**: `fast_check.c` was bumped to `EBS_WORDS=8` (512-bit
edge/colour bitsets, `MAX_M=512`) to handle K_{17,17} (m=289) and
larger. The previous `__uint128_t` bound was no longer sufficient
for Δ≥12 bipartite at large splits.

**Generator bug discovered + fixed mid-run**: the first attempt
(`run_d17_d20.sh`) used `genbg`, whose default build caps at
`MAXN1=24, n1+n2 ≤ 32`. At Δ=17, every bipartite split (17+17 through
20+20) silently produced 0 graphs. `genbgL` (built with `MAXN1=30`,
`make genbgL`) handles n1+n2 ≤ 60 and was used for the resume + the
fix-up runs. Bogus "0 graphs" entries in `/tmp/d17to20_results/SUMMARY`
predate the `[genbgL]`-tagged sections, which supersede them.

### Δ=17..19 general (Erdős–Nešetřil ≤ ⌈1.25·Δ²⌉)

| Δ | bound | n | graphs | runtime |
|---:|---:|---:|---:|---:|
| 17 | 362 | 18 | 1 (K_{17}∪…) | 5s |
| 17 | 362 | 20 | 49 | 5s |
| 17 | 362 | 22 | TIMEOUT (>1800s) | — |
| 18 | 405 | 20 | 1 | 5s |
| 18 | 405 | 22 | **7,373,924** | **865s** |
| 18 | 405 | 24 | TIMEOUT (>1800s) | — |
| 19 | 452 | 20 | 1 | 5s |
| 19 | 452 | 22 | 73 | 5s |
| 19 | 452 | 24 | TIMEOUT (>1800s) | — |

The n=22 case at Δ=18 is the workhorse: 7.37M graphs in 14.4 min
(8,533 graphs/sec/core × 8 cores).

### Δ=17..19 bipartite (Faudree ≤ Δ²) — `genbgL`

| Δ | bound | split | graphs | runtime |
|---:|---:|---:|---:|---:|
| 17 | 289 | 17+17 (K_{17,17}) | 1 | 5s |
| 17 | 289 | 18+18 | 1 | 5s |
| 17 | 289 | 19+19 | 105 | 5s |
| 17 | 289 | 20+20 | TIMEOUT (>1800s) | — |
| 18 | 324 | 18+18 (K_{18,18}) | 1 | 5s |
| 18 | 324 | 19+19 | 1 | 5s |
| 18 | 324 | 20+20 | 137 | 5s |
| 18 | 324 | 21+21 | TIMEOUT (>1800s) | — |
| 19 | 361 | 19+19 (K_{19,19}) | 1 | 5s |
| 19 | 361 | 20+20 | 1 | 5s |
| 19 | 361 | 21+21 | 165 | 5s |
| 19 | 361 | 22+22 | TIMEOUT (>1800s) | — |

K_{n,n} (the n=Δ split) attains χ'_s = Δ² exactly at every Δ — the
Faudree bound is tight on the complete bipartite graph.

## Phase D_asym: asymmetric Faudree (Δ_X < Δ_Y)

Conjecture (Faudree-Schelp-Gyárfás-Tuza, asymmetric form): for
bipartite G with bipartition (X, Y) and side-wise maxima Δ_X, Δ_Y,
χ'_s(G) ≤ Δ_X · Δ_Y. Tight on K_{Δ_Y, Δ_X}. Plan:
the development notes.

Run via `run_sec_asym.sh` using `genbgL -c -d Δ_X:Δ_Y -D Δ_X:Δ_Y n_X n_Y`.
30-min per-case strict cap, 8-way parallel. Δ_X ∈ {2, 3, 4} fully
swept; Δ_X=5 partial (one row, Δ_Y=6); Δ_X ∈ {5..8} remainder paused.

### Δ_X = 2 (Faudree-asym ≤ 2·Δ_Y)

| Δ_X | Δ_Y | bound | (n_X, n_Y) | graphs | runtime |
|---:|---:|---:|---|---:|---:|
| 2 | 3 | 6 | (3,2) (6,4) (9,6) (12,8) (15,10) (18,12) | 1,2,6,20,91,**509** | ≤5s each |
| 2 | 4 | 8 | (4,2) (8,4) (12,6) (16,8) (20,10) (24,12) | 1,3,19,204,4330,**171,886** | last ≤110s |
| 2 | 5 | 10 | (5,2) (10,4) (15,6) (20,8) (25,10) | 1,4,49,1689,**187,392** | last ≤452s |

### Δ_X = 3 (Faudree-asym ≤ 3·Δ_Y)

| Δ_X | Δ_Y | bound | (n_X, n_Y) | graphs | runtime |
|---:|---:|---:|---|---:|---:|
| 3 | 4 | 12 | (4,3) (8,6) (12,9); (16,12) TIMEOUT | 1, 18, 22,651 | ≤5s each |
| 3 | 5 | 15 | (5,3) (10,6) (15,9); (20,12) TIMEOUT | 1, 45, **2,553,003** | last 85s |
| 3 | 6 | 18 | (6,3) (12,6); (18,9) TIMEOUT | 1, 131 | ≤5s |
| 3 | 7 | 21 | (7,3) (14,6); (21,9) TIMEOUT [par 16,819] | 1, 344 | ≤5s each |
| 3 | 8 | 24 | (8,3) (16,6); (24,9) TIMEOUT [par 0 — genbgL never emitted] | 1, 950 | ≤5s each |
| 3 | 9 | 27 | (9,3) (18,6); (27,9) TIMEOUT [par 0 — genbgL stalled, same wall] | 1, 2,456 | ≤5s each |
| 3 | 10 | 30 | (10,3) (20,6); larger skipped | 1, 6,197 | ≤5s, 35s |
| 3 | 11 | 33 | (11,3) (22,6); larger skipped | 1, 14,815 | ≤5s, 5:16 |
| 3 | 12 | 36 | (12,3); (24,6) TIMEOUT [par 19,878] | 1 | ≤5s |
| 3 | 13 | 39 | (13,3); (26,6) TIMEOUT [par 1,536] | 1 | ≤5s |
| 3 | 14..15 | 42..45 | (n_X=Δ_Y, 3) only [(2·Δ_Y, 6) TIMEOUT @ 0 — genbgL stalled] | 1 each | ≤5s |
| 3 | 16..20 | 48..60 | (n_X=Δ_Y, 3) only [(2·Δ_Y, 6) infeasible — n_X>30 MAXN1] | 1 each | ≤5s |

### Δ_X = 4 (Faudree-asym ≤ 4·Δ_Y) [`run_sec_asym_resume.sh`]

| Δ_X | Δ_Y | bound | (n_X, n_Y) | graphs | runtime |
|---:|---:|---:|---|---:|---:|
| 4 | 5 | 20 | (5,4) (10,8); (15,12) TIMEOUT | 1, 3,143 | ≤5s each |
| 4 | 6 | 24 | (6,4) (12,8); (18,12) TIMEOUT | 1, 65,547 | ≤5s each |
| 4 | 7 | 28 | (7,4) **(14,8)**; (21,12) TIMEOUT | 1, **1,272,695** | last 65s |

### Δ_X = 5 (Faudree-asym ≤ 5·Δ_Y) [`run_one_row.sh`]

| Δ_X | Δ_Y | bound | (n_X, n_Y) | graphs | runtime |
|---:|---:|---:|---|---:|---:|
| 5 | 6 | 30 | (6,5); (12,10) TIMEOUT [par 46.4M] | 1 | ≤5s |
| 5 | 7 | 35 | (7,5); (14,10) TIMEOUT [par 76.4M @ 2h]; (21,15) skipped | 1 | ≤5s |
| 5 | 8 | 40 | (8,5); (16,10) TIMEOUT [par 1.85M]; (24,15) skipped | 1 | ≤5s |

All three Δ_Y={6,7,8} rows TIMEOUT'd at 8-way parallel on the (2nd) split:
- (5,6) 12×10: 46.4M graphs in 1800s, 0 candidates. ~6.4K g/s aggregate.
- (5,7) 14×10: 11.6M graphs in 1800s, 0 candidates. ~6.4K g/s aggregate.
  Follow-up 2-hour run (2026-05-18, 22:24 → 00:24): **76.4M graphs**
  across 8 workers, still TIMEOUT. Per-worker rate climbed from
  800g/s at 30-min to 1270g/s at 2h (genbgL canonicalization amortizes
  with depth). Canonical count for (5,7) 14×10 is ≥ 76.4M, so even
  doubling the budget to 4h likely wouldn't complete it.
- (5,8) 16×10: 1.85M graphs in 1800s, 0 candidates. ~1.0K g/s aggregate.

Per-graph cost grows with Δ_Y due to more edges per graph (60, 70,
80 edges respectively) → more fast_check colouring work. Aggregate
rate drops from ~6.4K/s to ~1.0K/s across the Δ_Y={6,7,8} progression.

The original (5,7) 14×10 single-thread report of "600K graphs in
446s" was unreliable — almost certainly an early-termination on the
single-thread code path (run_one_row.sh bug: omitted `$PARSWEEP` so
no residue-class partitioning, plus no `--csv` flag so the count-stat
parsing in run_bounded was reading from a different stream). K_{Δ_Y,
Δ_X} smallest-splits confirm tight χ'_s on all three rows.

**Workhorses**:
- Δ_X=3, Δ_Y=5 at (15, 9) — 2.55M graphs in 85s.
- Δ_X=4, Δ_Y=7 at (14, 8) — 1.27M graphs in 65s.
- Δ_X=5, Δ_Y=6 at (12, 10) — 46.4M graphs in 1800s (TIMEOUT, 8-way par).
- Δ_X=5, Δ_Y=7 at (14, 10) — 11.6M graphs in 1800s (TIMEOUT, 8-way par);
  76.4M in 7200s on follow-up run (still TIMEOUT, canonical count ≥ 76M).
- Δ_X=5, Δ_Y=8 at (16, 10) — 1.85M graphs in 1800s (TIMEOUT, 8-way par).
- Δ_X=3, Δ_Y=7 at (21, 9) — 16,819 graphs in 1800s (TIMEOUT, 8-way par;
  ~9 g/s aggregate ≈ 1 g/s per worker). Two bottlenecks compound:
  (a) genbgL first-graph latency > 30s per residue class (standalone
  test emitted 0 in 30s); (b) once flowing, DSATUR on each graph at
  bound=21 / m=63 takes ~1s. So the "DSATUR feasibility wall" framing
  was only half-right — there's also a "nauty canonicalization wall"
  on the same row.
- Δ_X=3, Δ_Y=8 at (24, 9) — **0 graphs completed** in 1800s (TIMEOUT,
  8-way par). Bottleneck is entirely **genbgL canonicalization**:
  standalone `genbgL -c -d3:8 -D3:8 24 9 0/8` runs at 99% CPU for
  13+ minutes without emitting a single canonical graph. fast_check
  vs. sat_check would not matter — no graphs reach the consumer.

**Totals**: 26 rows × ~3–5 splits. **~125M** asymmetric bipartite
graphs swept (earlier rows + ~46.4M par on (5,6) 12×10 + ~76.4M par on
(5,7) 14×10 [from 2-hour follow-up run] + ~1.85M par on (5,8) 16×10 +
~17K par on (3,7) 21×9 + 0 par on (3,8) 24×9 [genbgL-stalled] + 0 par
on (3,9) 27×9 [genbgL-stalled] + the (3,10..20) widening 2026-05-18:
~6K, ~15K, 20K, 1.5K then 0s above Δ_Y=14), **0 counterexamples**.

For Δ_Y ∈ {16..20}, only the K_{Δ_Y, 3} extremal was actually swept
(1 graph each, saturating χ'_s = 3·Δ_Y trivially). The next feasible
split (2·Δ_Y, 6) has n_X ∈ {32..40} which exceeds genbgL's MAXN1=30
cap. Further widening at fixed Δ_X=3 would need a different generator
(e.g., a custom one without MAXN1 limit) or bumping genbgL's cap. K_{Δ_Y, Δ_X}
confirmed χ'_s = Δ_X · Δ_Y tight on every smallest-split case (saturating
the asymmetric Faudree bound exactly).

### Post-mortem: the (3,8) (24,9) wall

The 2026-05-17 attempt to push Δ_X=3 to Δ_Y ∈ {7, 8} surfaced a
**nauty canonical-form enumeration wall** at roughly n_X + n_Y > 25
with rich symmetry (here, 3-regular on one side):

| Case | n_X+n_Y | first-graph latency (standalone genbgL) |
|---|---:|---|
| (3,5) (15,9) | 24 | instant (~85 g/s over 10s) |
| (3,6) (18,9) | 27 | > 10s |
| (3,7) (21,9) | 30 | > 30s (parallel sweep eventually got 1 g/s) |
| (3,8) (24,9) | 33 | > 13 min (no graph ever emitted in tests) |
| (3,9) (27,9) | 36 | > 30 min × 8 workers = 0 graphs (2026-05-18 sweep) |

The slowdown is in nauty's automorphism-group computation at each
step of orderly canonical-form generation, which scales factorially
with vertex count for highly-symmetric biregular structures. Flag
options don't help — `-c` controls connectivity (not canonicalization);
nauty's canonical-form pruning is intrinsic to the genbg algorithm
and cannot be disabled.

This re-attributes a finding earlier (mis-)attributed to DSATUR.
On 2026-05-17 commit `c529963` the (3,8) (24,9) row was labelled
"DSATUR-hung", but standalone testing showed fast_check was idle
the whole time — genbgL never delivered a graph. Cf. commits
`2d1b7e4` and this commit for the corrected attribution.

**Practical options for pushing further**:
1. Wait it out — long first-graph latency, then steady output. (5,7)
   (21,9) confirmed this pattern; (24,9) didn't emit in a 13-min
   single-worker test, may emit in a multi-hour run.
2. Switch canonical engine — nauty's bundled `Traces` is often faster
   on graphs with rich symmetry; `bliss` is a separate library. Both
   need rebuilding genbg against a different backend.
3. Accept the limit — we've swept ~60M asym graphs with 0 CEs across
   14 rows. No CE has surfaced in any feasible (Δ_X, Δ_Y, n_X, n_Y).

Higher Δ — both conjectures are even more open (no Δ-specific
proofs at Δ ≥ 5 in the literature beyond asymptotic 1.772·Δ²).
Time-bounded to ≤1h compute per case.

### Δ=7 general (EN: χ'_s ≤ 1.25·49 = 61)

| n | #7-reg connected | candidates | runtime |
|---:|---:|---:|---:|
| 8 | 1 (K_8) | 0 | <0.1s |
| 10 | 5 | 0 | <0.1s |
| 12 | 1,547 | 0 | <0.1s |
| 14 | 21,609,301 | 0 | 485s (~8 min, 8-way parallel) |
| **total ≤14** | **21,610,854** | **0** | |

Count matches Δ=6 n=14 (21,609,300) within 1 — by complement
bijection: 14-vertex 7-reg ↔ 6-reg.

### Δ=7 bipartite (Faudree: χ'_s ≤ 49)

| n | split | #7-reg bipartite | candidates | runtime |
|---:|---|---:|---:|---:|
| 14 | 7+7 | 1 (K_{7,7}) | 0 | <0.1s |
| 16 | 8+8 | 1 | 0 | <0.1s |
| 18 | 9+9 | 8 | 0 | <0.1s |
| 20 | 10+10 | 1,165 | 0 | <0.1s |
| 22 | 11+11 | 5,582,612 | 0 | 276s (4.6 min, 8-way parallel) |
| **total ≤22** | | **5,583,787** | **0** | |

Count at 11+11 matches Δ=4 bipartite 11+11 (5,582,592) by complement
in K_{11,11}: 4-reg ↔ 7-reg.

### Δ=8 general (EN: χ'_s ≤ 1.25·64 = 80)

| n | #8-reg connected | candidates | runtime |
|---:|---:|---:|---:|
| 9 | 1 (K_9) | 0 | <0.1s |
| 10 | 1 | 0 | <0.1s |
| 12 | 94 | 0 | <0.1s |
| 14 | 3,459,386 | 0 | 341s (~6 min, single-thread C) |
| **total ≤14** | **3,459,482** | **0** | |

Count matches Δ=5 n=14 (3,459,383) within 3 — by complement (n=14
8-reg ↔ 5-reg).

### Δ=8 bipartite (Faudree: χ'_s ≤ 64)

| n | split | #8-reg bipartite | candidates | runtime |
|---:|---|---:|---:|---:|
| 16 | 8+8 | 1 (K_{8,8}) | 0 | <0.1s |
| 18 | 9+9 | 1 | 0 | <0.1s |
| 20 | 10+10 | 12 | 0 | <0.1s |
| 22 | 11+11 | 7,454 | 0 | 1s |
| **total ≤22** | | **7,468** | **0** | |

12+12 (n=24) was attempted but extrapolated to ~8h — over the 1h budget.
A 24+ core machine could fit it.

### Coda on complement bijection

For Δ-regular n-vertex graphs, the complement bijection gives
identical counts for Δ and (n-1-Δ). Verified empirically across
all our regimes:

| n=14 general | Δ=k count |
|---|---:|
| Δ=4 | 88,168 (was earlier) |
| Δ=5 | 3,459,383 |
| Δ=6 | 21,609,300 |
| Δ=7 | 21,609,301 |
| Δ=8 | 3,459,386 |
| Δ=9 | 88,169 (by symmetry, not directly counted) |

The off-by-one differences come from self-complementary graphs counted once.

## Phase E: Targeted near-extremal candidates

### 5-blowup of C₅ (the conjecture-tight extremal)

| Property | Value |
|---|---|
| Vertices | 25 |
| Edges | 125 |
| Δ | 10 |
| χ'_s (SAT) | **125** |
| ratio χ'_s/Δ² | **1.2500 (= 5/4 exactly)** |
| Erdős–Nešetřil tight value 1.25·Δ² | 125 |

**The 5-blowup of C₅ saturates the Erdős–Nešetřil conjecture
exactly: χ'_s = 1.25·Δ²**. SAT confirms this in 0.0s via the L²(G)-
complete shortcut (every edge-pair in this graph is strong-adjacent,
so all 125 edges need distinct colours).

This matches the formalised Lean theorem
`pentagon_conjecture_tight` (`PentagonConjecture.lean:751`), which
proves the corresponding "tight" half for the pentagon conjecture
(thesis Conj 4 / lemma `pentagon_conjecture.tex:51`).

## Summary table

| Phase | Conjecture | Δ | n range | #graphs swept | counterexamples |
|---|---|---:|---|---:|---:|
| C   | Erdős–Nešetřil | 4 | exhaustive ≤16 | 8,127,195 | 0 |
| D   | Faudree bipartite | 4 | **exhaustive ≤24** | **323,287,683** | **0** |
| D2  | Andersen consistency (proved) | 3 | exhaustive ≤16 | 4,678 | 0 (as expected) |
| D2  | Steger-Yu consistency (proved) | 3 bip | exhaustive ≤16 | 73 | 0 (as expected) |
| C5  | Erdős–Nešetřil | 5 | **exhaustive ≤14** | **3,467,291** | 0 |
| D5  | Faudree bipartite | 5 | **exhaustive ≤22** | **157,078,487** | 0* |
| C6  | Erdős–Nešetřil | 6 | **exhaustive ≤14** | **21,617,171** | 0 |
| D6  | Faudree bipartite | 6 | **exhaustive ≤22** | **156,595,871** | 0 |
| C7  | Erdős–Nešetřil | 7 | **exhaustive ≤14** | **21,610,854** | 0 |
| D7  | Faudree bipartite | 7 | **exhaustive ≤22** | **5,583,787** | 0 |
| C8  | Erdős–Nešetřil | 8 | **exhaustive ≤14** | **3,459,482** | 0 |
| D8  | Faudree bipartite | 8 | **exhaustive ≤22** | **7,468** | 0 |
| E   | conjecture-tight check | 10 | 5-blowup of C₅ | 1 | n/a (saturates 1.25·Δ²) |
| C17..C19 | Erdős–Nešetřil | 17..19 | n≤22 (skip-on-TIMEOUT past) | 7,374,049 | 0 |
| D17..D19 | Faudree bipartite | 17..19 | split≤21+21 (skip-on-TIMEOUT past) | 413 | 0 |
| D_asym | Faudree asymmetric Δ_X·Δ_Y | (Δ_X, Δ_Y) ∈ {2,3,4} × {next 3} | 4,283,446 | 0 |

**Total graphs swept: 712,497,949** (~712 million). All resolved via
greedy DSATUR alone (with SAT fallback for 2 false-positive candidates
at Δ=5 bipartite n=20, both confirmed colourable with χ'_s=25).
TIMEOUT cases (workhorse n=22+ at Δ≥17, larger splits) are skipped
rather than partially-counted under the 30-min-per-case wall cap.
The asymmetric Faudree extension (D_asym) covers (Δ_X, Δ_Y) ∈
{(2,3..5), (3,4..6), (4,5..7)}; rows (Δ_X ∈ {5..8}) were planned but paused
before launch.

*Asterisk on Δ=5 bipartite: 5-shot DSATUR initially flagged 2 of
601,054 graphs at n=20 as candidates, but SAT verification confirmed
both have χ'_s = 25 ≤ 25 (DSATUR false-positives — couldn't find
the optimal greedy ordering in 5 random tries). Re-run with 20-shot
DSATUR resolved all 601,054 cleanly. fast_check.c default bumped to
20 shots accordingly.

## Implications

The headline conjectures are **strongly empirically confirmed at
Δ=4 and Δ=5** in the searched ranges:
- Erdős–Nešetřil at Δ=4: holds for every connected 4-regular graph on
  ≤16 vertices (**8,127,195 graphs** — exhaustive via `geng`).
- Faudree bipartite at Δ=4: holds for every connected 4-regular
  bipartite graph on ≤24 vertices (**323,287,683 graphs** — exhaustive
  via `genbg`, parallel 8-way + C in 3h 37min at n=24).
- Erdős–Nešetřil at Δ=5: holds for every connected 5-regular graph on
  ≤14 vertices (**3,467,291 graphs** — exhaustive, ~3 min).
- Faudree bipartite at Δ=5: holds for every connected 5-regular
  bipartite graph on ≤22 vertices (**157,078,487 graphs** — exhaustive,
  parallel 8-way + C at n=22 in 70 min).
- Erdős–Nešetřil at Δ=6: holds for every connected 6-regular graph on
  ≤14 vertices (**21,617,171 graphs** — exhaustive, ~10 min).
- Faudree bipartite at Δ=6: holds for every connected 6-regular
  bipartite graph on ≤22 vertices (**156,595,871 graphs** — exhaustive,
  parallel 8-way + C at n=22 in ~4.5h active compute).
- Δ=7: general n≤14 (**21,610,854**), bipartite n≤22 (**5,583,787**)
  — both within ≤10 min, 0 counterexamples.
- Δ=8: general n≤14 (**3,459,482**), bipartite n≤22 (**7,468**) —
  both within ≤10 min, 0 counterexamples. Δ=8 bipartite n=24 (12+12)
  attempted but extrapolated to ~8h.
- Δ=9..16: complete pass within 30-min/case budget (see Phase C9..C16
  section); largest individual case Δ=11 general n=16 (**8.0M graphs**,
  281s) and Δ=16 general n=20 (**516k**, 40s). Zero counterexamples.
- Δ=17..19: largest workhorse Δ=18 general n=22 (**7.37M graphs**,
  14.4 min); Δ=17/19 also clean. Bipartite K_{n,n} confirmed
  Faudree-tight at every Δ (χ'_s = Δ² exactly on the only graph that
  saturates at small splits). TIMEOUTs at next-n in each series block
  further enumeration in this regime.

This appears to be the first exhaustive computational verification
at Δ=4 to this scale that's been written up (at least, no public
record was found in the ~30 min literature scan; see
the development notes for citations).

Cranston (2006) proved χ'_s ≤ 22 for Δ=4 in general; the empirical
evidence here suggests no graph in the searched range attains even
21, let alone exceeds the conjectured 20. The gap "Cranston 22
vs. conjectured 20" is not realized by any small graph.

## Limitations

- **Tool capacity (current)**: `fast_check.c` uses `uint64_t[8]`
  (512-bit) bitsets for both edges and colours, so it handles up to
  **512 edges** and bounds requiring up to **512 colours**. Vertex
  bitsets are still `uint64_t` (n ≤ 64); past n = 64 would need a
  further extension.
- **Bipartite generator (current)**: default `genbg` caps at
  `n1+n2 ≤ 32`; `genbgL` (`make genbgL`, MAXN1=30) handles
  `n1+n2 ≤ 60`. For larger splits, `genbgL` would need its own
  MAXN1 bump or a switch to `nauty`'s long-word builds.
- **Frontier-n cases beyond budget**: Δ=4 bipartite n=26 (~10⁹+
  graphs), Δ=8 bipartite n=24 (~10⁸ at ~8h compute), Δ=9 general
  n=16 (started, >15-min budget). Each would need a multi-hour or
  multi-day run on this hardware, or a larger machine.
- **Search confirms no counterexample *in the swept range***; cannot
  rule out counterexamples at larger n.
- **DSATUR completeness**: greedy can fail to find an optimal
  colouring even when one exists. The tool flags such cases as
  "unresolved" candidates; SAT (compute_chi_s.py) confirms or
  refutes. At Δ=5 bipartite n=20, 2 of 601k graphs were initial
  false-positive candidates with 5 shots; bumping default to 20
  shots eliminated them. Higher Δ (especially K_{n,n}-saturating
  cases) may need more shots or SAT fallback.
- **SAT correctness** assumes Glucose3 returns correct SAT/UNSAT,
  which is well-established but not formally verified.
- **SAT-based primary check (`sat_check.py`)** — added 2026-05-17 as
  a companion to `fast_check.c`. Same I/O contract; uses pysat/Glucose3
  for the strong-edge-colouring decision. Measured rates:
  - (3,5) (15,9) at bound 15: ~8 g/s per worker — much **slower**
    than fast_check (~30K g/s/worker on the same case). Avoid for
    loose-bound work.
  - (3,8) (16,6) at bound 24: ~55 g/s per worker — feasible.
  - One (3,8) (24,9) graph at bound 24: 0.33s SAT-decision in
    isolation.
  **Caveat (added on 2026-05-17 retrospective)**: sat_check is only
  useful when the consumer is the bottleneck. The (3,8) (24,9) case
  is upstream-bound by genbgL canonicalization (see post-mortem in
  the Δ_X=5 section), so swapping the consumer doesn't help. Where
  sat_check would matter: cases where genbgL emits but fast_check's
  DSATUR backtracks for many seconds per graph (we don't have a
  confirmed example of this — (3,7) (21,9) is partly this and partly
  upstream-bound). Not currently wired into `parallel_sweep.sh` /
  `run_one_row.sh` (which still call fast_check).
- **Genbg variance**: nauty's residue-class split (`r/N`) can have
  significant per-residue count variance (slice-0/64 estimates at
  n=24 4-reg bipartite missed the true count by 4.4×). For accurate
  count estimation, full enumeration or larger sampling is needed.

## Reproducer

### One-time setup

```bash
# Build nauty
cd /tmp && curl -sLO https://pallini.di.uniroma1.it/nauty2_8_8.tar.gz \
  && tar xf nauty2_8_8.tar.gz && cd nauty2_8_8 \
  && ./configure && make geng genbg

# Build the C consumer
cd local-flags-certificates/sec_search
clang -O3 -march=native -Wall -o fast_check fast_check.c

# Python fallback dependencies
pip3 install python-sat networkx
```

### Single-thread sweep

```bash
/tmp/nauty2_8_8/geng -d4 -D4 -c 14 \
  | ./local-flags-certificates/sec_search/fast_check 20 --csv \
  > sweep.csv 2> sweep.log
```

### 8-way parallel sweep (uses nauty residue-class split)

```bash
./local-flags-certificates/sec_search/parallel_sweep.sh \
  "/tmp/nauty2_8_8/geng -d4 -D4 -c 16" /tmp/out 20 8
```

For bipartite, swap `geng -dK -DK -c $n` for `genbg -c -dK -DK $n1 $n2`.

### Confirming a candidate via SAT (Python)

If `fast_check` reports any "CANDIDATE COUNTEREXAMPLE", the candidate
needs SAT verification before claiming a real counterexample:

```python
import sys; sys.path.insert(0, 'local-flags-certificates/sec_search')
from compute_chi_s import chi_s, strong_adjacency_pairs, _solve_k_colouring
import networkx as nx
G = nx.from_graph6_bytes(b"<g6 string>")
edges, sp = strong_adjacency_pairs(G)
sat, col = _solve_k_colouring(len(edges), sp, bound)
print("colourable at bound:", sat)
if sat: print("explicit colouring:", col)
```

Glucose3 returns SAT iff the bound is actually feasible; if SAT,
the candidate was a DSATUR false-positive (re-run with more shots
or with SAT fallback enabled).

### Where outputs go

- Per-graph CSVs land in `/tmp/sweep_*.csv` (large — multi-GB for
  100M+ graphs). Clean these when not needed.
- Progress + summary logs at `/tmp/sweep_*.log` (small).
- Final logs are archived in
  `local-flags-certificates/sec_search/delta{4,5,6,7,8}_logs/`.

## Cross-reference

- Plan: the development notes
- T3 panel (smaller exact-χ'_s tabulation):
  the development notes
- Thesis source for the two conjectures:
  `thesis_source/chapters/strong_edge_colouring.tex:54-60`
  (Erdős–Nešetřil) and `:10` (Faudree).
- Formalised tight extremals:
  - `pentagon_conjecture_tight` (Lean, `PentagonConjecture.lean:751`),
    proving the pentagon-conjecture analog at Δ=10.
  - The 5-blowup of C₅ construction directly verifies
    `χ'_s = 1.25·Δ²` at Δ=10, matching the Erdős–Nešetřil tight value.
