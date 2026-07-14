#!/usr/bin/env python3
"""
Phase 2 of the HoG pentagon sweep: compute P(G) / (|G| * Delta^4) for
every cached HoG triangle-free graph.

Reads paired (.g6, .json) sidecars from
`pentagon_search/hog/g6_cache/`, iterates over every entry, counts
induced 5-cycles, and writes:

  * `hog_results.tsv` — full per-graph ratio table.
  * `hog_top50.tsv`   — top-50 ratios by descending order.

Optimisation: any graph with `girth` in {None, 0} or `girth >= 6` has
no induced 5-cycle, so we fast-path to P=0 without running the
counter. (`girth == 0` / `None` are HoG's encoding for acyclic.)

Streaming: the counter runs entry-by-entry; only the top-50 heap and
the open TSV file are held in memory.
"""

from __future__ import annotations

import argparse
import heapq
import itertools
import json
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Iterator, Optional, Tuple

import networkx as nx


CACHE_DIR = Path(__file__).resolve().parent / "g6_cache"
OUT_DIR = Path(__file__).resolve().parent
RESULTS_TSV = OUT_DIR / "hog_results.tsv"
TOP_TSV = OUT_DIR / "hog_top50.tsv"


def parse_graph6(g6: str) -> Optional[nx.Graph]:
    g6 = g6.strip()
    if not g6 or g6.startswith(">"):
        return None
    try:
        return nx.from_graph6_bytes(g6.encode("ascii"))
    except Exception:
        return None


def count_induced_5cycles(G: nx.Graph) -> int:
    """Canonical-orientation induced-C_5 counter (matches pentagon_counter.py)."""
    nodes = list(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    adj = {v: set(G.neighbors(v)) for v in nodes}
    cnt = 0
    for v0 in nodes:
        i0 = idx[v0]
        Nv0 = [u for u in adj[v0] if idx[u] > i0]
        for v1, v4 in itertools.combinations(Nv0, 2):
            if v4 in adj[v1]:
                continue
            for v2 in adj[v1]:
                if idx[v2] <= i0 or v2 == v4:
                    continue
                if v2 in adj[v0] or v2 in adj[v4]:
                    continue
                for v3 in adj[v2] & adj[v4]:
                    if idx[v3] <= i0 or v3 == v1 or v3 == v2:
                        continue
                    if v3 in adj[v0] or v3 in adj[v1]:
                        continue
                    cnt += 1
    return cnt


def iter_entries(cache_dir: Path) -> Iterator[Tuple[dict, str]]:
    """Yield (metadata_entry, g6_string) pairs from every paired sidecar.

    The g6 line ordering in the .g6 file is guaranteed (by Phase 1's
    download.py) to match the entry ordering in the .json sidecar.
    """
    g6_files = sorted(p for p in cache_dir.glob("*.g6"))
    for g6f in g6_files:
        jsf = g6f.with_suffix(".json")
        if not jsf.exists():
            print(f"WARN: missing sidecar for {g6f.name}", file=sys.stderr)
            continue
        meta = json.loads(jsf.read_text())
        with g6f.open("r", encoding="ascii") as fh:
            lines = [ln.strip() for ln in fh if ln.strip() and not ln.startswith(">")]
        if len(lines) != len(meta):
            print(
                f"WARN: length mismatch in {g6f.name}: "
                f"g6 lines={len(lines)} json entries={len(meta)}",
                file=sys.stderr,
            )
        for entry, g6 in zip(meta, lines):
            yield entry, g6


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--top-k", type=int, default=50)
    ap.add_argument("--cache-dir", type=Path, default=CACHE_DIR)
    ap.add_argument("--results-tsv", type=Path, default=RESULTS_TSV)
    ap.add_argument("--top-tsv", type=Path, default=TOP_TSV)
    ap.add_argument("--progress-every", type=int, default=1000)
    args = ap.parse_args()

    clebsch_threshold = Fraction(12, 625)
    petersen_threshold = Fraction(2, 135)
    original_threshold = Fraction(1, 80)

    start = time.time()
    n_total = 0
    n_with_pent = 0
    n_fastpath = 0
    n_beat_clebsch = 0
    n_tie_clebsch = 0
    n_beat_petersen = 0
    n_beat_original = 0
    max_ratio = Fraction(0)
    max_entry = None
    top_heap: list = []  # min-heap of (ratio, idx, hog_id, n, delta, m, girth, P, g6)
    counterexamples: list = []

    args.results_tsv.parent.mkdir(parents=True, exist_ok=True)
    with args.results_tsv.open("w", encoding="utf-8") as out:
        out.write("hog_id\tname\tn\tdelta\tm\tgirth\tP\tratio_num\tratio_den\tratio_float\n")
        for entry, g6 in iter_entries(args.cache_dir):
            n_total += 1
            hog_id = entry.get("hog_id")
            name = entry.get("name") or ""
            # Sanitise tabs/newlines in name for TSV.
            name = name.replace("\t", " ").replace("\n", " ")
            n = entry.get("n")
            delta = entry.get("delta")
            m = entry.get("m")
            girth = entry.get("girth")

            fastpath = (girth is None) or (girth == 0) or (girth >= 6)
            if fastpath:
                P = 0
                n_fastpath += 1
            else:
                G = parse_graph6(g6)
                if G is None:
                    print(
                        f"WARN: parse failure hog_id={hog_id}", file=sys.stderr
                    )
                    continue
                # Use metadata n/delta if available; else recompute.
                if n is None:
                    n = G.number_of_nodes()
                if delta is None:
                    degs = [d for _, d in G.degree()]
                    delta = max(degs) if degs else 0
                P = count_induced_5cycles(G)

            if delta == 0 or n == 0:
                ratio = Fraction(0)
            else:
                ratio = Fraction(P, n * delta ** 4)

            ratio_float = float(ratio)
            out.write(
                f"{hog_id}\t{name}\t{n}\t{delta}\t{m}\t"
                f"{girth if girth is not None else 'None'}\t{P}\t"
                f"{ratio.numerator}\t{ratio.denominator}\t{ratio_float:.10g}\n"
            )

            if P > 0:
                n_with_pent += 1
                if ratio > clebsch_threshold:
                    n_beat_clebsch += 1
                    counterexamples.append(
                        (ratio, hog_id, name, n, delta, m, girth, P, g6)
                    )
                elif ratio == clebsch_threshold:
                    n_tie_clebsch += 1
                if ratio > petersen_threshold:
                    n_beat_petersen += 1
                if ratio > original_threshold:
                    n_beat_original += 1
            if ratio > max_ratio:
                max_ratio = ratio
                max_entry = (hog_id, name, n, delta, m, girth, P, g6)

            entry_tuple = (
                ratio, n_total, hog_id, n, delta, m, girth, P, g6, name
            )
            if len(top_heap) < args.top_k:
                heapq.heappush(top_heap, entry_tuple)
            elif ratio > top_heap[0][0]:
                heapq.heapreplace(top_heap, entry_tuple)

            if n_total % args.progress_every == 0:
                elapsed = time.time() - start
                rate = n_total / elapsed if elapsed > 0 else 0
                print(
                    f"... {n_total} graphs in {elapsed:.1f}s "
                    f"({rate:.1f}/s, fastpath={n_fastpath}, "
                    f"with_pent={n_with_pent}, max_ratio={float(max_ratio):.6f})",
                    file=sys.stderr,
                )

    elapsed = time.time() - start

    # Top-K table.
    rows = sorted(top_heap, key=lambda r: (-r[0], r[2]))
    with args.top_tsv.open("w", encoding="utf-8") as out:
        out.write(
            "rank\thog_id\tname\tn\tdelta\tm\tgirth\tP\tratio_num\tratio_den\t"
            "ratio_float\tg6\n"
        )
        for rank, (ratio, _idx, hog_id, n, delta, m, girth, P, g6, name) in enumerate(
            rows, start=1
        ):
            name_clean = name.replace("\t", " ").replace("\n", " ")
            out.write(
                f"{rank}\t{hog_id}\t{name_clean}\t{n}\t{delta}\t{m}\t"
                f"{girth if girth is not None else 'None'}\t{P}\t"
                f"{ratio.numerator}\t{ratio.denominator}\t"
                f"{float(ratio):.10g}\t{g6}\n"
            )

    # Counterexamples report (sorted by ratio desc, then by hog_id).
    counterexamples.sort(key=lambda r: (-r[0], r[1]))

    print("=" * 78, file=sys.stderr)
    print(f"Phase 2 sweep complete: {n_total} graphs in {elapsed:.1f}s", file=sys.stderr)
    print(f"  fast-path (P=0, girth>=6 or acyclic): {n_fastpath}", file=sys.stderr)
    print(f"  pentagon-counted: {n_total - n_fastpath}", file=sys.stderr)
    print(f"  graphs with P>0: {n_with_pent}", file=sys.stderr)
    print(
        f"  beat Clebsch 12/625 (~{float(clebsch_threshold):.6f}): {n_beat_clebsch}",
        file=sys.stderr,
    )
    print(f"  tie Clebsch: {n_tie_clebsch}", file=sys.stderr)
    print(
        f"  beat Petersen 2/135 (~{float(petersen_threshold):.6f}): {n_beat_petersen}",
        file=sys.stderr,
    )
    print(
        f"  beat original 1/80 (~{float(original_threshold):.6f}): {n_beat_original}",
        file=sys.stderr,
    )
    if max_entry is not None:
        hog_id, name, n, delta, m, girth, P, g6 = max_entry
        print(
            f"  max ratio: {max_ratio} (~{float(max_ratio):.6f}) "
            f"at HoG #{hog_id} ({name}) n={n} delta={delta} P={P} girth={girth}",
            file=sys.stderr,
        )
    if counterexamples:
        print("  --- COUNTEREXAMPLES (ratio > 12/625) ---", file=sys.stderr)
        for ratio, hog_id, name, n, delta, m, girth, P, g6 in counterexamples[:20]:
            print(
                f"    HoG #{hog_id} ({name}): ratio={ratio} (~{float(ratio):.6f}) "
                f"n={n} delta={delta} P={P} girth={girth}",
                file=sys.stderr,
            )
        if len(counterexamples) > 20:
            print(
                f"    ... and {len(counterexamples) - 20} more",
                file=sys.stderr,
            )
    print(f"  results: {args.results_tsv}", file=sys.stderr)
    print(f"  top-{args.top_k}: {args.top_tsv}", file=sys.stderr)


if __name__ == "__main__":
    main()
