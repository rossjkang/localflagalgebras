#!/usr/bin/env python3
"""Independent exact-rational verifier for pentagon SDP bound certificates.

Convention (validated against the repo audit script): the SDPA problem is
  min c^T y  s.t.  S(y) := sum_k y_k F_k - F_0  is blockwise PSD,
graphs induce feasible y (standard bridge), and the functional value is
-c^T y.  The bound certificate is the csdp PRIMAL matrix X (matrix 2 of the
.cert):  for every feasible y,

  c^T y - tr(F_0 X) = tr(S(y) X) - sum_k y_k r_k,   r_k := tr(F_k X) - c_k,

so if X is PSD then   -c^T y <= -tr(F_0 X) + sum_k y_k max(r_k, 0).

The final repair constructs rational nonnegative multipliers over the file's
own linear rows that certify the *weighted* universal bound

  sum_k y_k max(r_k, 0) <= T.

For diagnosis, the verifier also constructs an exact bound S on sum_k y_k.
The crude product S * max(r_k,0) is generally far too weak and is never used
for the final assertion.

Everything in the final inequality is exact rational arithmetic:
* F entries verified integral; c parsed as exact decimal literals;
* X rationalised at 10^-P (default P=14), lambda = 10^-11 added on PSD
  blocks (its residual cost lambda*tr(F_k|psd-diag) is included in r_k
  exactly); scalar diagonal blocks clipped up to 0 where
  negative-by-rounding, after which every residual and objective term is
  recomputed exactly (so no monotonicity claim about an individual residual
  is needed);
* every PSD block of X verified PSD by exact rational LDL (own code);
* r_k computed exactly; weighted residual and Sigma-y bounds certified by
  exact multiplier checks.

Output: exact rational safe bound V = -tr(F_0 X) + T, compared to
the target.  For the scaled reweighted file, raw phi <= V/scale.

Usage: verify_exact_certificate.py <sdpa> <cert> [--denom-exp 14]
  [--lambda-exp 11] [--target-numer 1659] [--target-denom 200]
  [--raw-scale 21]
"""
from __future__ import annotations
import argparse, hashlib, json, time, pickle, os
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix


def log(m):
    print(m, flush=True)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def parse_sdpa(path: Path):
    ds = 0
    m = nblocks = None
    sizes = []
    c = []
    entries = []
    with path.open() as f:
        for line in f:
            if line.startswith("*") or not line.strip():
                continue
            ds += 1
            if ds == 1:
                m = int(line.split()[0])
            elif ds == 2:
                nblocks = int(line.split()[0])
            elif ds == 3:
                sizes = [int(v) for v in line.split()]
            elif ds == 4:
                c = [F(v) for v in line.split()]
            else:
                p = line.split()
                if len(p) != 5:
                    continue
                v = F(p[4])
                assert v.denominator == 1, f"non-integer F entry {p}"
                entries.append((int(p[0]), int(p[1]), int(p[2]) - 1,
                                int(p[3]) - 1, int(v)))
    assert len(sizes) == nblocks and len(c) == m
    return m, sizes, c, entries


def parse_cert_X(path: Path):
    """csdp primal matrix X = matrix 2 of the .cert."""
    X = {}
    with path.open() as f:
        next(f)
        for line in f:
            p = line.split()
            if len(p) != 5:
                continue
            if int(p[0]) != 2:
                continue
            X.setdefault(int(p[1]), {})[(int(p[2]) - 1, int(p[3]) - 1)] = float(p[4])
    return X


def rational_ldl_psd(A, dim):
    """Exact unpivoted LDL test, followed by an entrywise identity check.

    The matrices tested here have already received a positive diagonal shift,
    so strict positive definiteness (and hence nonzero unpivoted pivots) is
    expected.  Keeping an explicit lower factor avoids the easy-to-miss bug
    in one-triangle in-place elimination: after updating the upper triangle,
    later steps must not read stale entries from the lower triangle.
    """
    def get(i, j):
        return A.get((i, j), A.get((j, i), F(0)))

    matrix = [[get(i, j) for j in range(dim)] for i in range(dim)]
    assert all(matrix[i][j] == matrix[j][i]
               for i in range(dim) for j in range(dim))
    lower = [[F(0)] * dim for _ in range(dim)]
    diagonal = [F(0)] * dim
    for j in range(dim):
        lower[j][j] = F(1)
        pivot = matrix[j][j] - sum(
            lower[j][k] * lower[j][k] * diagonal[k]
            for k in range(j))
        if pivot <= 0:
            return False, j, pivot
        diagonal[j] = pivot
        for i in range(j + 1, dim):
            numerator = matrix[i][j] - sum(
                lower[i][k] * lower[j][k] * diagonal[k]
                for k in range(j))
            lower[i][j] = numerator / pivot

    for i in range(dim):
        for j in range(dim):
            reconstructed = sum(
                lower[i][k] * diagonal[k] * lower[j][k]
                for k in range(min(i, j) + 1))
            if reconstructed != matrix[i][j]:
                return False, (i, j), reconstructed - matrix[i][j]
    return True, None, min(diagonal, default=F(0))


def audit_ldl_implementation():
    """Tripwires for the exact factorization code itself.

    The indefinite example is deliberately chosen so that the former
    one-triangle in-place routine returned a false positive.
    """
    positive = {(0, 0): F(2), (0, 1): F(1), (1, 0): F(1), (1, 1): F(2)}
    assert rational_ldl_psd(positive, 2)[0]
    indefinite_rows = ((0, -1, -5), (-1, 1, 2), (-5, 2, 5))
    indefinite = {(i, j): F(indefinite_rows[i][j])
                  for i in range(3) for j in range(3)}
    assert not rational_ldl_psd(indefinite, 3)[0]


def certify_sum_y_bound(m, sizes, entries, f0_rows):
    """Exact multipliers mu >= 0 over the linear rows (diag coords of blocks
    >= 2) with  sum_rows mu * a_{row,k} <= -1  for every k, certifying
    sum_k y_k <= S := -sum mu * f0.  Found by float LP, verified over Q."""
    rows = {}            # (blk,i) -> {k: int coeff}
    for (k, blk, i, j, v) in entries:
        if k == 0 or blk == 1:
            continue
        if sizes[blk - 1] < 0 and i == j:
            rows.setdefault((blk, i), {})[k] = rows.setdefault((blk, i), {}).get(k, 0) + v
    keys = sorted(rows)
    nr = len(keys)
    log(f"  sum-y certificate: {nr} linear rows available")
    # float LP: min sum mu*(-f0)  s.t.  A^T mu <= -1,  mu >= 0
    data, ri, ci = [], [], []
    for cidx, key in enumerate(keys):
        for k, a in rows[key].items():
            ri.append(k - 1); ci.append(cidx); data.append(float(a))
    A = coo_matrix((data, (ri, ci)), shape=(m, nr))
    obj = np.array([-float(f0_rows.get(key, 0)) for key in keys])
    res = linprog(obj, A_ub=A.tocsr(), b_ub=-np.ones(m),
                  bounds=[(0, None)] * nr, method="highs")
    assert res.status == 0, f"sum-y LP failed: {res.message}"
    S_float = res.fun
    log(f"  float sum-y bound = {S_float:.6f}")
    # rationalise mu conservatively and verify exactly
    DEN = 10 ** 9
    mu = {key: F(round(res.x[idx] * DEN), DEN) for idx, key in enumerate(keys)
          if res.x[idx] > 0}
    # exact check: for every k, sum mu*a_{row,k} <= -1
    col = [F(0)] * (m + 1)
    for key, muv in mu.items():
        for k, a in rows[key].items():
            col[k] += muv * a
    worst = max(col[1:])
    if worst > -1:
        # scale mu up slightly so the inequality holds exactly
        factor = F(-1) / worst if worst != 0 else None
        assert worst < 0, "mu certificate unusable (worst >= 0)"
        mu = {key: muv * factor for key, muv in mu.items()}
        col = [v * factor for v in col]
        assert max(col[1:]) <= -1
    S = -sum(muv * f0_rows.get(key, F(0)) for key, muv in mu.items())
    log(f"  EXACT certified: sum_k y_k <= {float(S):.9f} (rational S, "
        f"{len(mu)} multipliers)")
    return S


def certify_weighted_y_bound(m, sizes, entries, f0_rows, weights,
                             solve_scale=10**12, method="highs",
                             buffer_exp=None, strict_zero_buffer=False):
    """Certify sum_k weights[k] * y_k <= T over the linear rows.

    This is much sharper than max(weights) * sum(y).  The latter loses a
    factor of hundreds of thousands on the pentagon files because the
    normalization permits a very large unweighted sum of coordinates even
    though the residual is supported and signed very unevenly.

    We solve for nonnegative multipliers mu with

        sum_rows mu[row] * a[row,k] <= -weights[k]

    for every column.  The row inequalities then imply
    weights . y <= -mu . f0.  A small uniform buffer in the floating LP
    makes exact rationalization stable; an exact final rescaling repairs any
    remaining multiplicative loss.
    """
    rows = {}
    for (k, blk, i, j, v) in entries:
        if k == 0 or blk == 1:
            continue
        if sizes[blk - 1] < 0 and i == j:
            row = rows.setdefault((blk, i), {})
            row[k] = row.get(k, 0) + v
    keys = sorted(rows)
    nr = len(keys)
    data, ri, ci = [], [], []
    for cidx, key in enumerate(keys):
        for k, a in rows[key].items():
            ri.append(k - 1)
            ci.append(cidx)
            data.append(float(a))
    A = coo_matrix((data, (ri, ci)), shape=(m, nr))
    obj = np.array([-float(f0_rows.get(key, 0)) for key in keys])

    # HiGHS' absolute feasibility tolerance is too coarse for 10^-7-sized
    # residuals.  Scale the entire requested column domination to integer
    # scale before solving, then divide the multipliers back exactly.
    if buffer_exp is None:
        buffer_exp = len(str(solve_scale)) - 1
    eps = F(1, 10 ** buffer_exp)
    # A strict buffer on zero-target columns is optional.  It is unnecessary
    # mathematically, but can protect their exact signs from independent
    # coordinatewise rationalisation.  Keeping its size independent of the
    # numerical solve scale lets a moderately scaled LP use a much smaller
    # proof buffer.
    rhs = -np.array([
        float((weights[k] + eps) * solve_scale)
        if weights[k] > 0 or strict_zero_buffer else 0.0
        for k in range(1, m + 1)
    ])
    log(f"  weighted-residual LP: {m} columns, {nr} row multipliers, "
        f"{sum(weight > 0 for weight in weights[1:])} positive targets; "
        f"solve_scale={solve_scale}, buffer=1e-{buffer_exp}, "
        f"strict_zero={strict_zero_buffer}, method={method}")
    res = linprog(obj, A_ub=A.tocsr(), b_ub=rhs,
                  bounds=[(0, None)] * nr, method=method)
    assert res.status == 0, f"weighted residual LP failed: {res.message}"
    log(f"  float weighted-residual bound = "
        f"{res.fun / solve_scale:.12f}")

    DEN = 10**12
    mu = {key: F(round(res.x[idx] * DEN), DEN * solve_scale)
          for idx, key in enumerate(keys) if res.x[idx] > 0}
    col = [F(0)] * (m + 1)
    for key, muv in mu.items():
        assert muv >= 0
        for k, a in rows[key].items():
            col[k] += muv * a
    bad_sign = [k for k in range(1, m + 1)
                if not (col[k] < 0 if weights[k] > 0 else col[k] <= 0)]
    if bad_sign:
        bad_positive = sum(weights[k] > 0 for k in bad_sign)
        log(f"  rationalized weighted multiplier has {len(bad_sign)} "
            f"bad column signs ({bad_positive} on positive-weight columns); "
            f"worst col={float(max(col[k] for k in bad_sign)):.3e}")
    assert not bad_sign, \
        "weighted multipliers lost a required column sign under rationalization"
    factor = max(
        [F(1)] + [weights[k] / (-col[k]) for k in range(1, m + 1)]
    )
    if factor > 1:
        mu = {key: value * factor for key, value in mu.items()}
        col = [value * factor for value in col]
    assert all(col[k] <= -weights[k] for k in range(1, m + 1))
    T = -sum(muv * f0_rows.get(key, F(0))
             for key, muv in mu.items())
    log(f"  EXACT certified: sum_k r_k^+ y_k <= {float(T):.12f} "
        f"(rational T, {len(mu)} multipliers, rescale {float(factor):.9f})")
    return T


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("sdpa", type=Path)
    ap.add_argument("cert", type=Path)
    ap.add_argument("--denom-exp", type=int, default=14)
    ap.add_argument("--lambda-exp", type=int, default=11)
    ap.add_argument("--target-numer", type=int, default=1659)
    ap.add_argument("--target-denom", type=int, default=200)
    ap.add_argument("--raw-scale", type=int, default=21)
    ap.add_argument(
        "--graph-divisor", type=int, default=20,
        help=("Combinatorial divisor converting the unscaled flag objective "
              "to the graph density; use 24 for the Q6 objective and 14 "
              "for the heptagon objective."),
    )
    ap.add_argument("--stage", choices=["prep", "psd", "final", "all"], default="all")
    ap.add_argument(
        "--skip-sum-y",
        action="store_true",
        help=("Skip the coarse sum(y) certificate.  That bound is diagnostic "
              "only; the theorem uses the separate weighted-residual dual."),
    )
    ap.add_argument(
        "--repair-with-flag-block",
        action="store_true",
        help=("First absorb as much positive residual as possible by reducing "
              "the existing block-1 flag-nonnegativity multipliers.  This is "
              "an exact zero-objective repair; any remainder still goes to "
              "the universal weighted-residual dual."),
    )
    ap.add_argument(
        "--residual-solve-scale", type=int, default=10**12,
        help=("Integer scaling used by the floating weighted-residual LP. "
              "The exact rational post-check, not this numerical scale, is "
              "the proof."),
    )
    ap.add_argument(
        "--residual-method", choices=("highs", "highs-ds", "highs-ipm"),
        default="highs",
        help="SciPy/HiGHS method for the auxiliary weighted-residual LP.",
    )
    ap.add_argument(
        "--residual-buffer-exp", type=int,
        help=("Use the exact positive buffer 10^(-EXP), independently of "
              "--residual-solve-scale.  By default its exponent is inferred "
              "from the solve scale."),
    )
    ap.add_argument(
        "--strict-zero-residual-buffer", action="store_true",
        help=("Also impose the numerical buffer on zero-weight columns; the "
              "subsequent rational sign audit remains mandatory."),
    )
    ap.add_argument("--block-lo", type=int, default=0)
    ap.add_argument("--block-hi", type=int, default=10**9)
    ap.add_argument("--ckpt", type=Path, default=Path("/private/tmp/pentagon_verify_ckpt"))
    args = ap.parse_args()
    audit_ldl_implementation()
    DEN = 10 ** args.denom_exp
    LAM = F(1, 10 ** args.lambda_exp)
    target = F(args.target_numer, args.target_denom)

    t0 = time.time()
    m, sizes, c, entries = parse_sdpa(args.sdpa)
    log(f"parsed sdpa: m={m} blocks={len(sizes)} entries={len(entries)} "
        f"({time.time()-t0:.0f}s); all F integral, c exact")

    f0_rows = {}
    for (k, blk, i, j, v) in entries:
        if k == 0 and sizes[blk - 1] < 0 and i == j:
            f0_rows[(blk, i)] = F(v)

    Xf = parse_cert_X(args.cert)
    X = {}
    clip_raise = F(0)
    for idx, sz in enumerate(sizes, 1):
        blk = Xf.get(idx, {})
        if sz < 0:
            d = {}
            for (i, j), v in blk.items():
                assert i == j
                q = F(round(v * DEN), DEN)
                if q < 0:
                    q = F(0)                       # conservative clip
                d[(i, i)] = q
            X[idx] = d
        else:
            d = {}
            for (i, j), v in blk.items():
                q = F(round(v * DEN), DEN)
                d[(i, j)] = q
                d[(j, i)] = q
            for i in range(sz):
                d[(i, i)] = d.get((i, i), F(0)) + LAM
            X[idx] = d
    log(f"rationalised X at 10^-{args.denom_exp}, lambda=10^-{args.lambda_exp} "
        f"on PSD blocks, diag clipped at 0")

    # exact residuals and tr(F_0 X)
    r = [F(0)] * (m + 1)
    trF0 = F(0)
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
    if args.repair_with_flag_block:
        assert sizes[0] == -m, "block 1 is not the coordinate nonnegativity block"
        block_one_entries = [row for row in entries if row[1] == 1]
        assert len(block_one_entries) == m
        assert all(k > 0 and i == j == k - 1 and v == 1
                   for k, _, i, j, v in block_one_entries)
        absorbed = F(0)
        absorbed_coordinates = 0
        for k in range(1, m + 1):
            if r[k] <= 0:
                continue
            key = (k - 1, k - 1)
            available = X[1].get(key, F(0))
            delta = min(r[k], available)
            if delta:
                X[1][key] = available - delta
                r[k] -= delta
                absorbed += delta
                absorbed_coordinates += 1
        assert all(value >= 0 for value in X[1].values())
        log(f"flag-block residual repair: touched {absorbed_coordinates} "
            f"coordinates; absorbed {float(absorbed):.3e}; "
            f"positive remainder on {sum(value > 0 for value in r[1:])}")
    rmax = max(r[1:])
    rpos = sum(1 for k in range(1, m + 1) if r[k] > 0)
    log(f"residuals: {rpos} positive of {m}; max r = {float(rmax):.3e}; "
        f"min r = {float(min(r[1:])):.3e}")

    ck = args.ckpt
    ck.mkdir(exist_ok=True)
    checkpoint_meta = {
        "sdpa_sha256": sha256_file(args.sdpa),
        "cert_sha256": sha256_file(args.cert),
        "denom_exp": args.denom_exp,
        "lambda_exp": args.lambda_exp,
    }
    meta_file = ck / "metadata.json"
    if meta_file.exists():
        stored_meta = json.loads(meta_file.read_text())
        assert stored_meta == checkpoint_meta, (
            "checkpoint belongs to different inputs/rationalisation: ",
            stored_meta, checkpoint_meta,
        )
    else:
        assert not list(ck.glob("blk*.ok")), (
            "legacy checkpoint has block markers but no metadata; use a new "
            "checkpoint directory"
        )
        meta_file.write_text(json.dumps(checkpoint_meta, indent=2) + "\n")
    s_file = ck / "prep.pkl"
    if args.skip_sum_y:
        S = None
        log("skipping diagnostic sum-y certificate")
    elif args.stage in ("prep", "all"):
        S = certify_sum_y_bound(m, sizes, entries, f0_rows)
        with s_file.open("wb") as fh:
            pickle.dump({"S": S, "rmax": rmax, "trF0": trF0}, fh)
        log(f"checkpoint: prep saved to {s_file}")
        if args.stage == "prep":
            return
    else:
        with s_file.open("rb") as fh:
            d = pickle.load(fh)
        S, rmax, trF0 = d["S"], d["rmax"], d["trF0"]
        log(f"checkpoint: prep loaded (S={float(S):.6f})")

    # exact PSD of every X block
    t1 = time.time()
    nps = 0
    psd_indices = [idx for idx, sz in enumerate(sizes, 1) if sz > 0]
    if args.stage in ("psd", "all"):
        todo = [i for i in psd_indices
                if args.block_lo <= psd_indices.index(i) < args.block_hi
                and not (ck / f"blk{i}.ok").exists()]
        # smallest blocks first for fast progress
        todo.sort(key=lambda i: sizes[i - 1])
        for idx in todo:
            sz = sizes[idx - 1]
            tb = time.time()
            ok, at, piv = rational_ldl_psd(X.get(idx, {}), sz)
            assert ok, f"PSD FAILS block {idx} dim={sz} pivot#{at}={piv}"
            (ck / f"blk{idx}.ok").write_text("ok")
            nps += 1
            if nps % 20 == 0 or time.time() - tb > 30:
                done_n = sum(1 for i in psd_indices if (ck / f"blk{i}.ok").exists())
                log(f"  ... block {idx} (dim {sz}) ok in {time.time()-tb:.0f}s; "
                    f"{done_n}/{len(psd_indices)} total ({time.time()-t1:.0f}s)")
        if args.stage == "psd":
            done_n = sum(1 for i in psd_indices if (ck / f"blk{i}.ok").exists())
            log(f"psd stage done for range: {done_n}/{len(psd_indices)} verified")
            return
    missing = [i for i in psd_indices if not (ck / f"blk{i}.ok").exists()]
    assert not missing, f"{len(missing)} PSD blocks unverified: {missing[:5]}"
    nps = len(psd_indices)
    log(f"exact PSD verified for all {nps} Cauchy-Schwarz blocks "
        f"({time.time()-t1:.0f}s)")

    residual_weights = [F(0)] + [max(r[k], F(0)) for k in range(1, m + 1)]
    if not any(residual_weights):
        T = F(0)
        log("exact: no positive residual remains; weighted absorb term is 0")
    else:
        T = certify_weighted_y_bound(
            m, sizes, entries, f0_rows, residual_weights,
            solve_scale=args.residual_solve_scale, method=args.residual_method,
            buffer_exp=args.residual_buffer_exp,
            strict_zero_buffer=args.strict_zero_residual_buffer)
    V = -trF0 + T
    log(f"exact: -tr(F_0 X) = {float(-trF0):.12f}")
    log(f"exact: weighted residual absorb term = {float(T):.3e}")
    if S is not None:
        log(f"diagnostic only: crude S*max(r,0) = "
            f"{float(S*max(rmax,F(0))):.3e}")
    log(f"exact safe bound V = {float(V):.12f}  vs target "
        f"{target} = {float(target):.12f}")
    assert V <= target, "certificate exceeds the safe target"
    log(f"margin = {float(target - V):.3e}")
    sc = args.raw_scale
    log(f"THEOREM-GRADE (mod standard bridge): raw phi <= V/{sc} <= "
        f"{float(target/sc):.10f}; graph density <= "
        f"{float(target/sc/args.graph_divisor):.10f} "
        f"(divisor={args.graph_divisor})")
    log("VERIFIED")


if __name__ == "__main__":
    main()
