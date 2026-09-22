#!/usr/bin/env python3
"""Extract the rational multiplier certificate from the size-8 pentagon run.

`verify_exact_certificate.py` proves the universal bound

    sum_k r_k^+ y_k  <=  T        for every feasible y

by exhibiting nonnegative rational multipliers `mu` over the program's own
linear rows -- but it discards `mu` and returns only `T`, and persists nothing.
So the certificate itself is not recoverable from a verifier run.

This script recomputes it and writes it out, so that the universal bound can be
checked by `check_multipliers.py` in seconds with the standard library alone,
instead of re-derived in a 647 s run needing scipy and HiGHS.  Only `X >= 0`
then still needs that run.

It does NOT modify the verifier, whose sha256 is pinned in three provenance
records; it imports the two parsers and re-implements the rest of the pipeline.
The re-implementation is gated on reproducing ten archived numbers, to the
printed precision of each: both input sha256s, the repair's touched count 5729,
absorbed mass 2.403e-11 and remainder 17, the multiplier count 5176, T,
-tr(F_0 X), V and the rescale factor 1.  The provenance record's residual
extremes are not gated.  The gates are asserts, so the script refuses to run
under `python3 -O`.

    python3 extract_multipliers.py <sdpa> <cert> -o <out.json>
"""
from __future__ import annotations
import argparse, hashlib, importlib.util, json, sys, time
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

# --- archived expectations; the extraction is worthless if these drift -------
EXPECT = {"touched": 5729, "absorbed": "2.403e-11", "remainder": 17,
          "multipliers": 5176,
          "T": "4.783111e-06", "negtrF0": "0.414584635843",
          "V": "0.414589418954", "factor": 1,
          "sdpa_sha256": "b46467ab2d34b672c122f4ebbd372d75aff808f63b336c873b56859ca24ca6ad",
          "cert_sha256": "650958f2b69d0800dab31b32de8803013c88d274b8d465d14ec24d1ddfb7e6fe"}

DENOM_EXP, LAMBDA_EXP, SOLVE_SCALE, BUFFER_EXP = 16, 16, 10**12, 12


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def load_verifier():
    path = Path(__file__).resolve().parent / "verify_exact_certificate.py"
    spec = importlib.util.spec_from_file_location("vec", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)          # main() is guarded; import is safe
    return mod


def main() -> int:
    if not __debug__:
        raise SystemExit(
            "extract_multipliers.py: refusing to run under `python3 -O`. Its "
            "reproduction gates are asserts, which -O removes; it would then "
            "overwrite the certificate without checking a single archived "
            "number. Run it without -O.")
    ap = argparse.ArgumentParser()
    ap.add_argument("sdpa", type=Path)
    ap.add_argument("cert", type=Path)
    ap.add_argument("-o", "--out", type=Path, required=True)
    args = ap.parse_args()
    # authenticate the inputs before the minute of LP, not after it
    assert sha256(args.sdpa) == EXPECT["sdpa_sha256"], "unexpected .sdpa"
    assert sha256(args.cert) == EXPECT["cert_sha256"], "unexpected .cert"

    vec = load_verifier()
    DEN, LAM = 10**DENOM_EXP, F(1, 10**LAMBDA_EXP)
    t0 = time.time()

    m, sizes, c, entries = vec.parse_sdpa(args.sdpa)
    f0_rows = {(blk, i): F(v) for (k, blk, i, j, v) in entries
               if k == 0 and sizes[blk - 1] < 0 and i == j}

    Xf = vec.parse_cert_X(args.cert)
    X = {}
    for idx, sz in enumerate(sizes, 1):
        blk, d = Xf.get(idx, {}), {}
        if sz < 0:
            for (i, j), v in blk.items():
                q = F(round(v * DEN), DEN)
                d[(i, i)] = q if q > 0 else F(0)
        else:
            for (i, j), v in blk.items():
                q = F(round(v * DEN), DEN)
                d[(i, j)] = q; d[(j, i)] = q
            for i in range(sz):
                d[(i, i)] = d.get((i, i), F(0)) + LAM
        X[idx] = d

    r, trF0 = [F(0)] * (m + 1), F(0)
    for (k, blk, i, j, v) in entries:
        if v == 0:
            continue
        z = X[blk].get((i, j))
        if z is None or z == 0:
            continue
        contrib = v * z if (i == j or sizes[blk - 1] < 0) else 2 * v * z
        if k == 0:
            trF0 += contrib
        else:
            r[k] += contrib
    for k in range(1, m + 1):
        r[k] -= c[k - 1]

    assert sizes[0] == -m, "block 1 is not the coordinate nonnegativity block"
    touched, absorbed = 0, F(0)
    for k in range(1, m + 1):
        if r[k] <= 0:
            continue
        key = (k - 1, k - 1)
        delta = min(r[k], X[1].get(key, F(0)))
        if delta:
            X[1][key] = X[1][key] - delta; r[k] -= delta
            touched += 1; absorbed += delta
    remainder = sum(1 for k in range(1, m + 1) if r[k] > 0)
    assert touched == EXPECT["touched"], f"repair touched {touched}"
    assert remainder == EXPECT["remainder"], f"remainder {remainder}"
    assert f"{float(absorbed):.3e}" == EXPECT["absorbed"], \
        f"absorbed {float(absorbed):.3e}"

    weights = [F(0)] + [max(r[k], F(0)) for k in range(1, m + 1)]

    rows = {}
    for (k, blk, i, j, v) in entries:
        if k == 0 or blk == 1 or not (sizes[blk - 1] < 0 and i == j):
            continue
        row = rows.setdefault((blk, i), {})
        row[k] = row.get(k, 0) + v
    keys = sorted(rows)
    data, ri, ci = [], [], []
    for cidx, key in enumerate(keys):
        for k, a in rows[key].items():
            ri.append(k - 1); ci.append(cidx); data.append(float(a))
    A = coo_matrix((data, (ri, ci)), shape=(m, len(keys)))
    obj = np.array([-float(f0_rows.get(key, 0)) for key in keys])
    eps = F(1, 10**BUFFER_EXP)
    rhs = -np.array([float((weights[k] + eps) * SOLVE_SCALE)
                     for k in range(1, m + 1)])
    res = linprog(obj, A_ub=A.tocsr(), b_ub=rhs,
                  bounds=[(0, None)] * len(keys), method="highs-ipm")
    assert res.status == 0, res.message

    D = 10**12
    mu = {key: F(round(res.x[i] * D), D * SOLVE_SCALE)
          for i, key in enumerate(keys) if res.x[i] > 0}
    col = [F(0)] * (m + 1)
    for key, muv in mu.items():
        assert muv >= 0
        for k, a in rows[key].items():
            col[k] += muv * a
    assert not [k for k in range(1, m + 1)
                if not (col[k] < 0 if weights[k] > 0 else col[k] <= 0)]
    factor = max([F(1)] + [weights[k] / (-col[k]) for k in range(1, m + 1)])
    if factor > 1:
        mu = {k_: v * factor for k_, v in mu.items()}
        col = [v * factor for v in col]
    assert all(col[k] <= -weights[k] for k in range(1, m + 1))
    T = -sum(muv * f0_rows.get(key, F(0)) for key, muv in mu.items())

    assert len(mu) == EXPECT["multipliers"], f"{len(mu)} multipliers"
    assert f"{float(T):.6e}" == EXPECT["T"], f"T={float(T):.6e}"
    assert f"{float(-trF0):.12f}" == EXPECT["negtrF0"]
    assert f"{float(-trF0 + T):.12f}" == EXPECT["V"]
    assert factor == EXPECT["factor"], f"factor={factor}"

    def fr(x): return [str(x.numerator), str(x.denominator)]
    doc = {
        "certificate": "bounded_pentagon_alt",
        "what": ("nonnegative rational multipliers mu over the program's linear rows "
                 "certifying sum_k r_k^+ y_k <= T for EVERY feasible y"),
        "sdpa_sha256": sha256(args.sdpa),
        "cert_sha256": sha256(args.cert),
        "key_convention": "[block, i] with block 1-based and i 0-based; coefficients accumulate across lines",
        "m": m, "T": fr(T), "target": ["2073", "5000"],
        "denom_exp": DENOM_EXP, "lambda_exp": LAMBDA_EXP,
        "mu": {f"{b},{i}": fr(v) for (b, i), v in sorted(mu.items())},
        "weights_positive": {str(k): fr(weights[k]) for k in range(1, m + 1) if weights[k] > 0},
        "f0_rows_used": {f"{b},{i}": fr(f0_rows[(b, i)]) for (b, i) in sorted(mu) if (b, i) in f0_rows},
        "scope": ("check_multipliers.py verifies these multipliers against the .sdpa and "
                  "the .cert in exact rational arithmetic: it recomputes r^+ and "
                  "-tr(F_0 X) = 0.414584635843 and confirms the safe value 0.414589418954 "
                  "<= 2073/5000. What it does NOT verify is X >= 0 -- the 278 exact "
                  "rational LDL^T block factorisations, which need the full verifier run."),
    }
    args.out.write_text(json.dumps(doc, indent=1) + "\n")
    print(f"wrote {args.out} : {len(mu)} multipliers, T={float(T):.6e}, "
          f"{time.time()-t0:.0f}s  -- all archived numbers reproduced")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
