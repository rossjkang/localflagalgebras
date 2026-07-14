# SEC counterexample sweeps

Small-graph computational hunt for counterexamples to the open
**strong edge colouring** conjectures: Erdős–Nešetřil (general graphs),
Faudree (bipartite graphs), and Faudree-asymmetric (bipartite, per-side
max degrees).

| Conjecture | Statement | Tight extremal |
|---|---|---|
| Erdős–Nešetřil (1985) | χ'_s(G) ≤ 1.25·Δ² for all G | 5-blowup of C₅ at Δ=10 (χ'_s = 125) |
| Faudree et al. (1989) | χ'_s(G) ≤ Δ² for bipartite G | K_{Δ,Δ} |
| Faudree asymmetric | χ'_s(G) ≤ Δ_X · Δ_Y, G bipartite (X, Y) | K_{Δ_Y, Δ_X} |

**Headline result**: 0 counterexamples found across **~711M graphs**.
Detailed verdict per (Δ, n) in [`sec_counterexample_results.md`](sec_counterexample_results.md).

## Architecture

```
nauty (geng / genbgL)            ─┐
   │ stream of graph6 strings    │
   ▼                              │  parallel_sweep.sh splits into
fast_check (C, 512-bit bitsets)  │  res/N residue classes,
   │ exit 0 if χ'_s ≤ bound      │  pipes each into one fast_check.
   │ exit 1 + CSV otherwise      │  Master scripts (run_d*.sh)
                                  │  call this per (Δ, n) case
   │                              │  with 30-min strict cap.
   ▼                              │
SUMMARY (per (Δ, n) case)        ─┘
```

- **`fast_check.c`** — graph6 parser, builds L²(G) edge bitset,
  runs DSATUR greedy with 20 random orderings. Falls back to "CANDIDATE
  COUNTEREXAMPLE" output if every shot exceeds the bound (SAT
  verification with `compute_chi_s.py` then confirms or refutes). Uses
  `ebitset_t = uint64_t[8]` (512-bit) for edge and colour bitsets,
  covering m ≤ 512 and bound ≤ 512. Vertices are `uint64_t` (n ≤ 64).
- **`parallel_sweep.sh`** — splits a nauty generator into N residue
  classes (`r/N`), pipes each into a worker `fast_check`. Aggregates
  worker logs at the end (`total graphs: M` line).
- **`compute_chi_s.py`** — SAT-based exact χ'_s via PySAT/Glucose3.
  Slow but authoritative; used as fallback / candidate verification.
- **`emergency_cleanup.sh`** — kills orphan workers (use when a master
  script is SIGKILL'd, since traps don't fire on `kill -9`).

## Master sweep scripts (chronological)

| Script | Scope | Per-case cap | Tool / bitset |
|---|---|---|---|
| `run_d9_d16_v2.sh` | Δ ∈ {9..16}, gen + sym bipartite | 30 min strict | 256-bit |
| `run_d17_d20.sh` | Δ ∈ {17..20}, gen + sym bipartite *(bipartite buggy — used genbg)* | 30 min strict | 512-bit |
| `run_d17_d20_resume.sh` | Δ ∈ {17..19} bipartite redo with `genbgL` + Δ=19 gen continuation | 30 min strict | 512-bit |
| `run_sec_asym.sh` | Asymmetric Faudree, Δ_X ∈ {2..8}, Δ_Y > Δ_X | 30 min strict | 512-bit |

All four use the same trap-based descendant cleanup
(`descendants` + `emergency_cleanup` functions) and skip-on-TIMEOUT
policy (no partial results — if a (Δ, n) case can't finish in 30 min,
its larger n in the same series is skipped).

## Build

### nauty 2.8.8

```bash
cd /tmp && curl -sLO https://pallini.di.uniroma1.it/nauty2_8_8.tar.gz \
  && tar xf nauty2_8_8.tar.gz && cd nauty2_8_8 \
  && ./configure \
  && make geng genbg            # general graphs + bipartite up to n1+n2 ≤ 32
make genbgL                     # bipartite up to n1+n2 ≤ 60 (MAXN1=30)
```

**Pitfall**: default `genbg` caps at `MAXN1=24, n1+n2 ≤ 32`. At
Δ ≥ 17 bipartite (17+17 = 34 > 32), `genbg` silently produces 0 graphs.
Always use `genbgL` for Δ ≥ 17 splits.

### fast_check (C)

```bash
clang -O3 -march=native -Wall -o fast_check fast_check.c
```

Built-in safety: explicit `ebs_is_zero` check before `ebs_ctz` to
avoid UB when the saturation bitset is full.

### Python fallback

```bash
pip3 install python-sat networkx
```

## Single-case reproducer

### General (Erdős–Nešetřil at Δ=4, n=14, bound 20)

```bash
/tmp/nauty2_8_8/geng -d4 -D4 -c 14 | ./fast_check 20 --csv > out.csv 2> out.log
```

### Symmetric bipartite (Faudree at Δ=5, 11+11, bound 25)

```bash
/tmp/nauty2_8_8/genbgL -c -d5 -D5 11 11 | ./fast_check 25 --csv > out.csv 2> out.log
```

### Asymmetric bipartite (Faudree-asym at Δ_X=3, Δ_Y=5, n_X=15, n_Y=9, bound 15)

```bash
/tmp/nauty2_8_8/genbgL -c -d3:5 -D3:5 15 9 | ./fast_check 15 --csv > out.csv 2> out.log
```

(Feasibility: Δ_X · n_X = Δ_Y · n_Y. Smallest feasible split is
(n_X, n_Y) = (Δ_Y, Δ_X), i.e. K_{Δ_Y, Δ_X}, which saturates the bound.)

## 8-way parallel reproducer

```bash
./parallel_sweep.sh "/tmp/nauty2_8_8/geng -d4 -D4 -c 16" /tmp/out 20 8
```

Args: `<gen-cmd> <output-prefix> <bound> <num-workers>`. The gen-cmd
gets `res/N` appended per worker (nauty's residue-class split).

## Output format

Per-worker:
- `<prefix>_w<i>.log` — `# done: M graphs in T s (rate Rg/s)` summary
  + any `# CANDIDATE COUNTEREXAMPLE` lines.
- `<prefix>_w<i>.csv` (with `--csv`) — one row per processed graph.

Aggregate (via `parallel_sweep.sh`):
- `<prefix>.log` — `total graphs: M` line + per-worker rate.

SUMMARY (via master scripts): one line per (Δ, n) case, e.g.
```
  Δ=18 gen n=22: 7373924 graphs, 0 cands, 865s
  Δ=3/5 15x9: 2553003 graphs, 0 cands, 85s
```

## Confirming a candidate

If any worker emits `CANDIDATE COUNTEREXAMPLE`, SAT-verify before
claiming a real counterexample:

```python
import sys; sys.path.insert(0, '.')
from compute_chi_s import strong_adjacency_pairs, _solve_k_colouring
import networkx as nx
G = nx.from_graph6_bytes(b"<g6 string>")
edges, sp = strong_adjacency_pairs(G)
sat, col = _solve_k_colouring(len(edges), sp, bound)
print("colourable at bound:", sat)
```

A `True` here means the candidate was a DSATUR false-positive
(re-run with more shots, or trust the SAT result).

## Log archives

Each major sweep's full per-case + per-worker logs are committed
under sibling dirs:

- `delta5_logs/`, `delta6_logs/`, `delta78_logs/` — older Δ=5..8 runs
- `delta9to16_logs/` — `run_d9_d16_v2.sh` output
- `delta17to20_logs/` — `run_d17_d20.sh` + `run_d17_d20_resume.sh`
- `asym_logs/` — `run_sec_asym.sh` (Δ_X ∈ {2, 3} portion)

Each archive contains `SUMMARY`, the per-case `.log` (with the
`total graphs:` aggregate), and per-worker `_w[0-7].log` files.

## Plans + design docs

- the development notes — original Δ=3..16 search plan
- the development notes — asymmetric Faudree plan
- [`sec_counterexample_results.md`](sec_counterexample_results.md) — full verdict + per-phase tables

## Known limitations

- **Capacity**: m ≤ 512, n ≤ 64, bound ≤ 512. Past these would need
  another bitset bump (vertex side is the next ceiling).
- **Generator**: `genbgL` caps at `n1+n2 ≤ 60`. Past that needs a
  further MAXN1 bump or nauty's long-word builds.
- **TIMEOUT**: any 30-min case is skipped, **and** so are larger n in
  that series. Boundary-case verdicts always cite the largest finished
  (Δ, n) — verdicts at strictly larger n are unknown.
- **DSATUR false-positives**: bumped to 20 shots after 2 false-positive
  candidates at Δ=5 bipartite n=20 (both SAT-confirmed clean). Higher Δ
  or larger K_{n,n}-like cases may still need SAT fallback in principle.
- **SAT correctness** assumes Glucose3 returns correct SAT/UNSAT
  (well-established, not formally verified).
