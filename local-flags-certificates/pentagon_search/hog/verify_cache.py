#!/usr/bin/env python3
"""Phase 1 verification: walk ``g6_cache/`` and sanity-check every downloaded
graph.

Checks:
  - g6 strings parse via ``networkx.from_graph6_bytes``.
  - Each graph is triangle-free (``sum(nx.triangles(G).values()) == 0``).
  - Each graph has n ∈ [10, 200] and Δ ∈ [3, 50].
  - Total downloaded count matches Phase 0's predicted 20,450.
  - Sidecar JSON's recorded (n, Δ) match the parsed graph.

Outputs a summary to stdout and exits non-zero on any failure.
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

import networkx as nx


N_MIN, N_MAX = 10, 200
D_MIN, D_MAX = 3, 50
EXPECTED_TOTAL = 20_450


def verify(cache_dir: Path) -> int:
    g6_files = sorted(cache_dir.glob("d*.g6"))
    if not g6_files:
        print(f"FAIL: no g6 files found in {cache_dir}", file=sys.stderr)
        return 1

    total = 0
    parse_fail = 0
    tri_fail = 0
    range_fail = 0
    sidecar_mismatch = 0
    per_delta: Counter[int] = Counter()
    per_n: Counter[int] = Counter()

    for g6_file in g6_files:
        json_file = g6_file.with_suffix(".json")
        if not json_file.exists():
            print(f"FAIL: missing sidecar {json_file}", file=sys.stderr)
            return 1
        sidecar = json.loads(json_file.read_text())
        g6_lines = [ln.strip() for ln in g6_file.read_text().splitlines() if ln.strip()]
        if len(g6_lines) != len(sidecar):
            print(f"FAIL: {g6_file.name}: g6 line count {len(g6_lines)} != "
                  f"sidecar {len(sidecar)}", file=sys.stderr)
            return 1
        for g6, meta in zip(g6_lines, sidecar):
            total += 1
            try:
                G = nx.from_graph6_bytes(g6.encode("ascii"))
            except Exception as e:
                parse_fail += 1
                print(f"  parse fail in {g6_file.name}: {e}", file=sys.stderr)
                continue
            n = G.number_of_nodes()
            d = max((deg for _, deg in G.degree()), default=0)
            tri = sum(nx.triangles(G).values()) // 3
            if tri != 0:
                tri_fail += 1
                print(f"  NOT TF: hog_id={meta.get('hog_id')} g6={g6[:32]}... "
                      f"triangles={tri}", file=sys.stderr)
            if not (N_MIN <= n <= N_MAX and D_MIN <= d <= D_MAX):
                range_fail += 1
                print(f"  RANGE: hog_id={meta.get('hog_id')} n={n} d={d}",
                      file=sys.stderr)
            if (meta.get("n") is not None and meta["n"] != n) or \
               (meta.get("delta") is not None and meta["delta"] != d):
                sidecar_mismatch += 1
                print(f"  SIDECAR: hog_id={meta.get('hog_id')} "
                      f"sidecar=(n={meta.get('n')}, d={meta.get('delta')}) "
                      f"actual=(n={n}, d={d})", file=sys.stderr)
            per_delta[d] += 1
            per_n[n] += 1
        print(f"  ok: {g6_file.name}  {len(g6_lines)} graphs")

    print(f"\nTotal verified: {total}")
    print(f"Expected:      {EXPECTED_TOTAL}")
    print(f"parse_fail={parse_fail}  tri_fail={tri_fail}  "
          f"range_fail={range_fail}  sidecar_mismatch={sidecar_mismatch}")

    print("\nPer-Δ distribution:")
    for d in sorted(per_delta.keys()):
        print(f"  Δ={d:2d}: {per_delta[d]}")
    print(f"\nn range observed: [{min(per_n)}, {max(per_n)}]")

    bad = parse_fail + tri_fail + range_fail + sidecar_mismatch
    if bad > 0:
        print(f"\nFAIL: {bad} problems detected", file=sys.stderr)
        return 1
    if total != EXPECTED_TOTAL:
        print(f"\nFAIL: total {total} != expected {EXPECTED_TOTAL}",
              file=sys.stderr)
        return 1
    print("\nALL CHECKS PASSED.")
    return 0


def main() -> None:
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--cache-dir", type=str,
                    default="local-flags-certificates/pentagon_search/hog/g6_cache")
    args = ap.parse_args()
    sys.exit(verify(Path(args.cache_dir)))


if __name__ == "__main__":
    main()
