#!/usr/bin/env python3
"""
House of Graphs (HoG) downloader + pentagon-ratio prototype.

Phase 0 status: SKELETON / prototype. Implements:
  - Search via the HoG `/api/enquiry` endpoint (returns paginated metadata).
  - Bulk g6 download via `/api/download_graph` (≤ max_download=2000 graphs per call).
  - Pentagon-ratio computation via the existing `pentagon_counter.py`.
  - Smoke test: Petersen graph (HoG id 660, g6 = IsP@OkWHG).

Phase 1 will extend this with:
  - Δ-banded batching to stay under the 2000-per-call cap and avoid timeouts.
  - Local g6 caching (one file per Δ-band).
  - Streaming pentagon-ratio computation + master TSV log.

API spec (reverse-engineered from the React bundle, 2026-05-21):

  Base URL:  https://houseofgraphs.org/api

  Endpoints used:
    GET  /invariants                 — list invariant IDs/names
    POST /enquiry                    — paginated search (returns metadata + canonicalForm)
                                       query params: page, size, sort, sortDir, fullSearch=true
    POST /download_graph             — bulk download (returns newline-separated g6 blob)
                                       body: { graphId: -1, format: "Graph6", searchConditions: {...} }
    GET  /graphs/{id}                — single-graph full metadata
    GET  /max_download               — 2000 (cap on bulk download per call)

  Search-conditions body schema:
    {
      "invariantEnquiries":           [{ "invariantId": int, "operator": "EQ|NE|LT|LE|GT|GE", "value": num }],
      "invariantRangeEnquiries":      [],
      "interestingInvariantEnquiries":[],
      "graphClassEnquiries":          [],
      "invariantParityEnquiries":     [],
      "graphIdEnquiry":               null,
      "canonicalFormEnquiry":         null,
      "textEnquiries":                [],
      "formulaEnquiries":             [],
      "mostRecent":                   -1,
      "mostPopular":                  -1,
      "subgraphEnquiries":            []
    }

  Key invariant IDs (from GET /api/invariants):
    9  = Girth
    10 = Maximum Degree
    12 = Minimum Degree
    15 = Number of Vertices
    27 = Number of Triangles   (TF iff value == 0)

  Triangle-free filter:   {"invariantId": 27, "operator": "EQ", "value": 0}
  Δ ∈ [a,b]:              two enquiries with invariantId=10, GE/LE
  n ∈ [a,b]:              two enquiries with invariantId=15, GE/LE

  Authentication: none required for read-only search + download (no Authorization header).
  Rate limits:    not advertised; the `timeout` query param caps server-side enquiry cost.
                  Bulk-download cap = 2000 graphs/call (max_download).
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Optional

import requests
import networkx as nx

# Make the existing pentagon counter importable.
_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent))
from pentagon_counter import count_induced_5cycles, girth  # noqa: E402


HOG_BASE = "https://houseofgraphs.org/api"

# Invariant IDs (as of 2026-05-21).
INV_GIRTH = 9
INV_MAX_DEG = 10
INV_MIN_DEG = 12
INV_NUM_VERTICES = 15
INV_NUM_TRIANGLES = 27


def empty_conditions() -> dict:
    """Return an empty search-conditions object matching the HoG schema."""
    return {
        "invariantEnquiries": [],
        "invariantRangeEnquiries": [],
        "interestingInvariantEnquiries": [],
        "graphClassEnquiries": [],
        "invariantParityEnquiries": [],
        "graphIdEnquiry": None,
        "canonicalFormEnquiry": None,
        "textEnquiries": [],
        "formulaEnquiries": [],
        "mostRecent": -1,
        "mostPopular": -1,
        "subgraphEnquiries": [],
    }


def tf_conditions(n_min: int, n_max: int, d_min: int, d_max: int) -> dict:
    """Triangle-free graphs with n ∈ [n_min, n_max] and Δ ∈ [d_min, d_max]."""
    c = empty_conditions()
    c["invariantEnquiries"] = [
        {"invariantId": INV_NUM_TRIANGLES, "operator": "EQ", "value": 0},
        {"invariantId": INV_NUM_VERTICES, "operator": "GE", "value": n_min},
        {"invariantId": INV_NUM_VERTICES, "operator": "LE", "value": n_max},
        {"invariantId": INV_MAX_DEG, "operator": "GE", "value": d_min},
        {"invariantId": INV_MAX_DEG, "operator": "LE", "value": d_max},
    ]
    return c


def count_matching(conditions: dict, timeout: int = 60) -> int:
    """Return totalElements for the given conditions (no graph data fetched)."""
    r = requests.post(
        f"{HOG_BASE}/enquiry",
        json=conditions,
        params={"page": 0, "size": 1, "fullSearch": "true"},
        timeout=timeout,
    )
    r.raise_for_status()
    return r.json().get("page", {}).get("totalElements", 0)


def bulk_download_g6(conditions: dict, timeout: int = 300) -> list[str]:
    """Bulk download g6 strings for all graphs matching conditions.

    NOTE: the server caps bulk downloads at 2000 graphs per call
    (GET /api/max_download). Callers must batch by Δ-band or n-band if the
    matching set exceeds 2000.
    """
    body = {"graphId": -1, "format": "Graph6", "searchConditions": conditions}
    r = requests.post(
        f"{HOG_BASE}/download_graph",
        json=body,
        params={"timeout": timeout},
        timeout=timeout + 30,
    )
    r.raise_for_status()
    # The blob is newline-separated g6 strings.
    text = r.text if isinstance(r.text, str) else r.content.decode("ascii", errors="replace")
    return [ln.strip() for ln in text.splitlines() if ln.strip()]


def fetch_single_graph(graph_id: int, timeout: int = 30) -> dict:
    """Fetch full metadata for a single HoG graph by its ID."""
    r = requests.get(f"{HOG_BASE}/graphs/{graph_id}", timeout=timeout)
    r.raise_for_status()
    return r.json()


def pentagon_ratio(g6: str) -> tuple[int, int, int, Fraction, int]:
    """Compute (n, Δ, P, ratio, girth) for a graph given by g6."""
    G = nx.from_graph6_bytes(g6.encode("ascii"))
    n = G.number_of_nodes()
    D = max((d for _, d in G.degree()), default=0)
    P = count_induced_5cycles(G)
    g = girth(G) if P > 0 else 0
    ratio = Fraction(P, n * D ** 4) if (n > 0 and D > 0) else Fraction(0)
    return n, D, P, ratio, g


def bulk_enquiry_metadata(conditions: dict, page_size: int = 2000,
                          timeout: int = 120, sleep: float = 0.5) -> list[dict]:
    """Paginated POST /enquiry to fetch metadata (HoG id, n, Δ, m, girth) for all
    graphs matching ``conditions``.

    Uses ``size=page_size`` per call (default 2000, the same cap as bulk download)
    and walks through pages until ``last == true``.

    Returns a list of dicts, one per graph, with the fields HoG returns plus the
    canonical g6 string.
    """
    out: list[dict] = []
    page = 0
    while True:
        r = requests.post(
            f"{HOG_BASE}/enquiry",
            json=conditions,
            params={"page": page, "size": page_size, "fullSearch": "true"},
            timeout=timeout,
        )
        r.raise_for_status()
        body = r.json()
        embedded = body.get("_embedded", {}) or {}
        # HAL+JSON list endpoints expose the items under a key whose exact name
        # depends on the resource. HoG names this list "graphSearchModelList".
        items = (
            embedded.get("graphSearchModelList")
            or embedded.get("graphSearchModels")
            or embedded.get("graphs")
            or []
        )
        out.extend(items)
        page_info = body.get("page", {})
        total_pages = page_info.get("totalPages", 1)
        page += 1
        if page >= total_pages:
            break
        if sleep > 0:
            time.sleep(sleep)
    return out


# --------------------------------------------------------------------------
# Phase 1: Δ-banded bulk download
# --------------------------------------------------------------------------

# Fixed banding plan for the Δ values that exceed the 2000-per-call cap.
# Determined by per-n count probing (2026-05-21). Each band is kept below
# 1800 graphs so the 2000-cap has headroom for graphs added later.
N_BANDS_PER_DELTA: dict[int, list[tuple[int, int]]] = {
    3: [(10, 31), (32, 36), (38, 82), (84, 166), (168, 200)],
    6: [(10, 26), (27, 192)],
    7: [(10, 28), (29, 29), (30, 128)],
}


def invariant_dict(item: dict) -> dict[int, float]:
    """Index ``invariantValues`` by ``invariantId`` → numeric value."""
    return {
        iv["invariantId"]: iv["invariantValue"]
        for iv in item.get("invariantValues", [])
    }


def phase1_download(
    out_dir: Path,
    d_min: int = 3,
    d_max: int = 50,
    n_min_global: int = 10,
    n_max_global: int = 200,
    sleep_between_calls: float = 1.0,
    timeout: int = 600,
) -> dict:
    """Δ-band the TF subset and bulk-download each band to ``out_dir``.

    Writes one ``d{Δ}[_n{lo}_{hi}].g6`` g6 file + a ``.json`` sidecar per band.
    Returns a manifest dict summarising the download.
    """
    out_dir.mkdir(parents=True, exist_ok=True)
    manifest: dict = {
        "n_min_global": n_min_global,
        "n_max_global": n_max_global,
        "d_min": d_min,
        "d_max": d_max,
        "bands": [],
        "total_graphs": 0,
        "total_calls": 0,
        "wall_seconds": 0.0,
    }
    t_start = time.time()

    for d in range(d_min, d_max + 1):
        # Skip Δ values with known-zero counts (probed in Phase 0): Δ ≥ 47.
        # The first probe will detect any miscount but we save round-trips here.
        sub_bands = N_BANDS_PER_DELTA.get(d, [(n_min_global, n_max_global)])
        for (n_lo, n_hi) in sub_bands:
            conds = tf_conditions(n_lo, n_hi, d, d)
            # Cheap totalElements probe first.
            expected = count_matching(conds, timeout=60)
            if expected == 0:
                manifest["bands"].append({
                    "delta": d,
                    "n_lo": n_lo,
                    "n_hi": n_hi,
                    "expected": 0,
                    "downloaded": 0,
                    "g6_file": None,
                    "json_file": None,
                    "elapsed_s": 0.0,
                })
                continue
            band_name = f"d{d}"
            if d in N_BANDS_PER_DELTA:
                band_name = f"d{d}_n{n_lo:03d}_{n_hi:03d}"
            g6_path = out_dir / f"{band_name}.g6"
            json_path = out_dir / f"{band_name}.json"

            t0 = time.time()
            # Two parallel routes:
            #  1. /download_graph → newline-separated g6 (fast, no metadata)
            #  2. /enquiry  → paginated metadata + canonicalForm (slow, has IDs)
            # We use /enquiry as the single source so the sidecar JSON carries
            # the (HoG id, n, Δ, m, girth) tuple and we don't have to merge.
            items = bulk_enquiry_metadata(conds, page_size=2000, timeout=timeout,
                                          sleep=0.0)
            elapsed = time.time() - t0

            # Build sidecar metadata: HoG id, n, Δ, m, girth, canonical g6.
            def _as_int(v):
                if v is None:
                    return None
                try:
                    return int(v)
                except (TypeError, ValueError):
                    return None
            sidecar: list[dict] = []
            g6_lines: list[str] = []
            for it in items:
                g6 = it.get("canonicalForm")
                if not g6:
                    continue
                inv = invariant_dict(it)
                sidecar.append({
                    "hog_id": it.get("graphId"),
                    "name": it.get("graphName"),
                    "g6": g6,
                    "n": _as_int(inv.get(INV_NUM_VERTICES)),
                    "delta": _as_int(inv.get(INV_MAX_DEG)),
                    "m": _as_int(inv.get(14)),  # 14 = Number of Edges
                    "girth": _as_int(inv.get(INV_GIRTH)),
                })
                g6_lines.append(g6)
            g6_path.write_text("\n".join(g6_lines) + ("\n" if g6_lines else ""))
            json_path.write_text(json.dumps(sidecar, indent=2))

            manifest["bands"].append({
                "delta": d,
                "n_lo": n_lo,
                "n_hi": n_hi,
                "expected": expected,
                "downloaded": len(g6_lines),
                "g6_file": g6_path.name,
                "json_file": json_path.name,
                "elapsed_s": round(elapsed, 2),
            })
            manifest["total_graphs"] += len(g6_lines)
            manifest["total_calls"] += 1
            print(f"  Δ={d:2d}  n=[{n_lo:3d}..{n_hi:3d}]  expected={expected}  "
                  f"downloaded={len(g6_lines)}  {elapsed:.1f}s", flush=True)
            if sleep_between_calls > 0:
                time.sleep(sleep_between_calls)

    manifest["wall_seconds"] = round(time.time() - t_start, 2)
    return manifest


def smoke_test_petersen() -> None:
    """Phase-0 smoke test: download Petersen, verify expected pentagon stats."""
    data = fetch_single_graph(660)
    e = data["entity"]
    g6 = e["canonicalForm"]
    print(f"HoG #{e['graphId']}: {e['graphName']}  g6={g6}")
    n, D, P, ratio, g = pentagon_ratio(g6)
    print(f"  n={n}  Delta={D}  P={P}  ratio={ratio} ({float(ratio):.6f})  girth={g}")
    # Expected: n=10, Δ=3, P=12 (Petersen has 12 induced C_5's), ratio = 12/(10*81) = 2/135.
    assert (n, D, P, ratio, g) == (10, 3, 12, Fraction(2, 135), 5), \
        f"Petersen smoke test FAILED: got {(n, D, P, ratio, g)}"
    print("  Petersen smoke test PASS (n=10, Δ=3, P=12, ratio=2/135, girth=5)")


def main() -> None:
    ap = argparse.ArgumentParser(description="HoG downloader + pentagon-ratio prototype")
    sub = ap.add_subparsers(dest="cmd", required=True)

    sub.add_parser("smoke", help="run Petersen smoke test")

    p_count = sub.add_parser("count", help="count TF graphs matching n/Δ filter")
    p_count.add_argument("--n-min", type=int, default=10)
    p_count.add_argument("--n-max", type=int, default=200)
    p_count.add_argument("--d-min", type=int, default=3)
    p_count.add_argument("--d-max", type=int, default=50)

    p_dl = sub.add_parser("download", help="bulk-download TF subset to a g6 file")
    p_dl.add_argument("--n-min", type=int, default=10)
    p_dl.add_argument("--n-max", type=int, default=200)
    p_dl.add_argument("--d-min", type=int, default=3)
    p_dl.add_argument("--d-max", type=int, default=50)
    p_dl.add_argument("--out", type=str, required=True, help="output g6 file path")

    p_p1 = sub.add_parser("phase1", help="Phase 1: full Δ-banded TF sweep")
    p_p1.add_argument("--out-dir", type=str,
                      default="local-flags-certificates/pentagon_search/hog/g6_cache",
                      help="output cache directory")
    p_p1.add_argument("--n-min", type=int, default=10)
    p_p1.add_argument("--n-max", type=int, default=200)
    p_p1.add_argument("--d-min", type=int, default=3)
    p_p1.add_argument("--d-max", type=int, default=50)
    p_p1.add_argument("--sleep", type=float, default=1.0,
                      help="seconds to sleep between API calls")

    args = ap.parse_args()

    if args.cmd == "smoke":
        smoke_test_petersen()
        return

    if args.cmd == "count":
        c = tf_conditions(args.n_min, args.n_max, args.d_min, args.d_max)
        n = count_matching(c)
        print(f"TF graphs in HoG with n ∈ [{args.n_min}, {args.n_max}], "
              f"Δ ∈ [{args.d_min}, {args.d_max}]: {n}")
        return

    if args.cmd == "download":
        # Phase 0: single-call download; Phase 1 will Δ-band to stay under 2000.
        c = tf_conditions(args.n_min, args.n_max, args.d_min, args.d_max)
        total = count_matching(c)
        if total > 2000:
            print(f"WARNING: matching set size {total} > 2000 (max_download cap). "
                  f"Phase 1 should batch by Δ.", file=sys.stderr)
        g6s = bulk_download_g6(c)
        Path(args.out).write_text("\n".join(g6s) + "\n")
        print(f"Wrote {len(g6s)} g6 strings to {args.out}")
        return

    if args.cmd == "phase1":
        out_dir = Path(args.out_dir)
        print(f"Phase 1 bulk download → {out_dir}")
        print(f"  Δ ∈ [{args.d_min}, {args.d_max}]   n ∈ [{args.n_min}, {args.n_max}]")
        manifest = phase1_download(
            out_dir,
            d_min=args.d_min, d_max=args.d_max,
            n_min_global=args.n_min, n_max_global=args.n_max,
            sleep_between_calls=args.sleep,
        )
        (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2))
        print(f"DONE.  total_graphs={manifest['total_graphs']}  "
              f"calls={manifest['total_calls']}  "
              f"wall={manifest['wall_seconds']:.1f}s")
        return


if __name__ == "__main__":
    main()
