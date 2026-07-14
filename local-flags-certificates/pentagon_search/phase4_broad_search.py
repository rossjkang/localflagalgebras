#!/usr/bin/env python3
"""
Phase 4 — broad-construction sweep, unified driver.

Runs all five sub-categories of Phase 4 (4a-4e) and tabulates results
against the Clebsch benchmark P/(|G|·Δ⁴) = 12/625 ≈ 0.01920.

Per-category sub-scripts:
  4a — phase4/cat_4a_finite_geometries.py (Levi/Kneser/Johnson/Polarity)
  4b — phase4/cat_4b_random_regular.py (random TF Δ-regular)
  4c — phase4/cat_4c_sporadic_srg.py (cages and named TF graphs)
  4d — phase4/cat_4d_cayley.py (Cayley graphs of PSL, S_n, A_n)
  4e — phase4/cat_4e_quasi_random.py (folded cubes, blowups, Hamming)

Master log: phase4_logs/all_graphs.tsv (one row per graph tested).

Usage:
  python3 phase4_broad_search.py                # full sweep
  python3 phase4_broad_search.py --skip-4b      # skip the long random-walk
  python3 phase4_broad_search.py --tsv path.tsv # override TSV destination
"""

from __future__ import annotations

import argparse
import os
import sys
import time

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
PHASE4_DIR = os.path.join(THIS_DIR, "phase4")
LOG_DIR = os.path.join(THIS_DIR, "phase4_logs")
DEFAULT_TSV = os.path.join(LOG_DIR, "all_graphs.tsv")

sys.path.insert(0, PHASE4_DIR)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tsv", default=DEFAULT_TSV)
    ap.add_argument("--skip-4a", action="store_true")
    ap.add_argument("--skip-4b", action="store_true")
    ap.add_argument("--skip-4c", action="store_true")
    ap.add_argument("--skip-4d", action="store_true")
    ap.add_argument("--skip-4e", action="store_true")
    ap.add_argument("--b-samples", type=int, default=30,
                    help="samples per (D, n) slice for 4b")
    ap.add_argument("--d-samples", type=int, default=5,
                    help="samples per (group, degree) for 4d")
    ap.add_argument("--fresh", action="store_true",
                    help="overwrite existing TSV instead of appending")
    args = ap.parse_args()

    os.makedirs(LOG_DIR, exist_ok=True)
    if args.fresh and os.path.exists(args.tsv):
        os.remove(args.tsv)

    print(f"=" * 70)
    print(f"PHASE 4 — broad construction sweep")
    print(f"=" * 70)
    print(f"Master TSV: {args.tsv}")
    print(f"Started: {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print()

    overall_results = []
    cat_times = {}

    if not args.skip_4a:
        from cat_4a_finite_geometries import run as run_4a
        t0 = time.time()
        print("-" * 70)
        print("4a — finite-geometry constructions")
        print("-" * 70)
        r = run_4a(args.tsv)
        cat_times["4a"] = time.time() - t0
        overall_results.append(("4a", r))

    if not args.skip_4b:
        from cat_4b_random_regular import run as run_4b
        t0 = time.time()
        print()
        print("-" * 70)
        print(f"4b — random Δ-regular sampling ({args.b_samples} samples/slice)")
        print("-" * 70)
        r = run_4b(args.tsv, samples_per_slice=args.b_samples)
        cat_times["4b"] = time.time() - t0
        overall_results.append(("4b", r))

    if not args.skip_4c:
        from cat_4c_sporadic_srg import run as run_4c
        t0 = time.time()
        print()
        print("-" * 70)
        print("4c — sporadic and named graphs")
        print("-" * 70)
        r = run_4c(args.tsv)
        cat_times["4c"] = time.time() - t0
        overall_results.append(("4c", r))

    if not args.skip_4d:
        from cat_4d_cayley import run as run_4d
        t0 = time.time()
        print()
        print("-" * 70)
        print(f"4d — Cayley graphs ({args.d_samples} samples/group/degree)")
        print("-" * 70)
        r = run_4d(args.tsv, samples_per_group=args.d_samples)
        cat_times["4d"] = time.time() - t0
        overall_results.append(("4d", r))

    if not args.skip_4e:
        from cat_4e_quasi_random import run as run_4e
        t0 = time.time()
        print()
        print("-" * 70)
        print("4e — quasi-random constructions (folded cubes, blowups)")
        print("-" * 70)
        r = run_4e(args.tsv)
        cat_times["4e"] = time.time() - t0
        overall_results.append(("4e", r))

    print()
    print("=" * 70)
    print("PHASE 4 — final summary")
    print("=" * 70)
    print(f"Times: {cat_times}")

    # Re-read the TSV and compute global champion.
    import csv
    from fractions import Fraction
    rows = []
    with open(args.tsv) as f:
        rdr = csv.DictReader(f, delimiter="\t")
        for row in rdr:
            try:
                n = int(row["n"]); D = int(row["Delta"]); P = int(row["P"])
                tf = int(row["TF"])
                ratio_f = float(row["ratio_float"])
            except (KeyError, ValueError):
                continue
            if not tf:
                continue
            rows.append((ratio_f, row["source"], row["name"], n, D, P))
    rows.sort(reverse=True)
    print(f"\nTotal TF graphs in master TSV: {len(rows)}")
    print(f"\nTop 15 ratios:")
    for r in rows[:15]:
        print(f"  ratio={r[0]:.6f}  [{r[1]}] {r[2]}  (n={r[3]}, Δ={r[4]}, P={r[5]})")
    if rows:
        champion = rows[0]
        print(f"\nCHAMPION: ratio={champion[0]:.6f} at [{champion[1]}] {champion[2]}")
        print(f"   Clebsch ratio: {12/625:.6f}")
        if champion[0] > 12 / 625:
            print(f"  *** EXCEEDS CLEBSCH ***")
        elif abs(champion[0] - 12 / 625) < 1e-9:
            print(f"  matches Clebsch (Clebsch family / equivalent)")
        else:
            print(f"  below Clebsch — Clebsch remains champion")

    print(f"\nFinished: {time.strftime('%Y-%m-%d %H:%M:%S')}")


if __name__ == "__main__":
    main()
