#!/usr/bin/env python3
"""Read an SDPA file and solve via SCS (open-source first-order solver).

This is a second-solver cross-check for the SEC SDP bounds — independent of
SDPA-LR (which generated the cert) and CSDP (which failed at general scale).

Solves the SDPA-primal form in CSDP's convention:

    min  c^T y
    s.t. Σ_i y_i F_i - F_0 ⪰ 0  (per block; PSD or nonneg-orthant)

CSDP reports both:
    "Primal objective value" = max tr(F_0 X)  s.t. tr(F_i X) = c_i, X ⪰ 0
    "Dual objective value"   = min c^T y      s.t. Σ y_i F_i - F_0 ⪰ 0
By strong duality these match (≈-4.0928 bipartite, ≈-10.6444 general).

Direct SCS encoding (bypassing CVXPY's heavy compilation):
- Variables y ∈ ℝ^m
- For each block b: build A_block y = Σ_i y_i vec(F_i^b)
  Then s_block = b_block - A_block y = vec(-F_0^b + Σ y_i F_i^b) = vec(F(y)^b).
  Constraining s_block ∈ K_b (PSD vec cone or nonneg vec) enforces F(y)^b ⪰ 0.

SCS PSD vec convention: column-major lower-triangular with √2 off-diag scale.
"""

import sys
import time
from pathlib import Path
import numpy as np
import scipy.sparse as sp
import scs


def parse_sdpa(path: Path):
    m = nblocks = sizes = c = None
    entries = []
    state = 0
    with path.open() as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('*') or line.startswith('"'):
                continue
            if state == 0:
                m = int(line.split()[0]); state = 1
            elif state == 1:
                nblocks = int(line.split()[0]); state = 2
            elif state == 2:
                parts = line.replace(',', ' ').replace('(', ' ').replace(')', ' ').split()
                sizes = [int(p) for p in parts][:nblocks]; state = 3
            elif state == 3:
                parts = line.replace(',', ' ').replace('{', ' ').replace('}', ' ').split()
                c = np.array([float(p) for p in parts][:m]); state = 4
            elif state == 4:
                parts = line.split()
                if len(parts) >= 5:
                    k = int(parts[0]); b = int(parts[1])
                    i = int(parts[2]); j = int(parts[3])
                    v = float(parts[4])
                    entries.append((k, b, i, j, v))
    return m, nblocks, sizes, c, entries


def build_scs(m, sizes, c, entries):
    """Convert SDPA → SCS form for SDPA-primal: min c^T y, Σ y_i F_i - F_0 ⪰ 0.

    SCS form: min c^T y  s.t. A y + s = b, s ∈ K.
    With A_block y = -Σ_i y_i vec(F_i^b) and b_block = vec(-F_0^b), we get
    s = b - A y = vec(-F_0 + Σ y_i F_i) ∈ K, encoding F(y) ⪰ 0.

    Variable order in y: y[k] = y_{k+1} for k=0..m-1.
    Constraint row order: diag (nonneg) blocks first, then PSD blocks
    (matches SCS cone order: l, then s).
    """
    n_blocks = len(sizes)
    block_dim = [abs(s) for s in sizes]
    block_psd = [s > 0 for s in sizes]
    block_vec_len = [(d * (d + 1) // 2) if psd else d
                     for d, psd in zip(block_dim, block_psd)]

    # Constraint-row order: diag blocks first (cone l), then PSD blocks (cone s)
    diag_blks = [b for b in range(n_blocks) if not block_psd[b]]
    psd_blks = [b for b in range(n_blocks) if block_psd[b]]
    ordered = diag_blks + psd_blks
    block_row_offset = [0] * n_blocks
    cur = 0
    for b in ordered:
        block_row_offset[b] = cur
        cur += block_vec_len[b]
    n_rows = cur

    def local_vec_idx(b, i, j):
        """SCS column-major lower-triangular index inside block b for 1-indexed (i,j)."""
        if block_psd[b]:
            n = block_dim[b]
            ip = max(i, j) - 1
            jp = min(i, j) - 1
            return jp * n - jp * (jp - 1) // 2 + (ip - jp)
        assert i == j
        return i - 1

    # Build A (rows: constraint rows, cols: y variables) and b vector.
    # F_0 contributes to b (with sign): b[row] = -F_0[entry] (√2 if off-diag).
    # F_k (k≥1) contributes to A: A[row, k-1] += F_k[entry] (√2 if off-diag),
    # but with overall sign so that s = b - Ay = vec(-F_0 + Σ y_i F_i):
    #   Ay row = (Ay)[row] should equal vec(F_0 - Σ y_i F_i)[row]? No, let's redo.
    # SCS:  s = b - A y. We want s = vec(Σ y_i F_i - F_0).
    # So  b - A y = vec(Σ y_i F_i - F_0)
    #     b = -vec(F_0)  ⟹  -A y = vec(Σ y_i F_i)  ⟹  A[:, k-1] = -vec(F_k).
    A_rows, A_cols, A_vals = [], [], []
    b_vec = np.zeros(n_rows)

    for k, blk_1, i, j, val in entries:
        b = blk_1 - 1
        local = local_vec_idx(b, i, j)
        row = block_row_offset[b] + local
        if block_psd[b] and i != j:
            v = val * np.sqrt(2.0)
        else:
            v = val
        if k == 0:
            b_vec[row] += -v
        else:
            A_rows.append(row); A_cols.append(k - 1); A_vals.append(-v)

    A = sp.csc_matrix((A_vals, (A_rows, A_cols)), shape=(n_rows, m))

    cone = {
        'l': sum(block_vec_len[b] for b in diag_blks),
        's': [block_dim[b] for b in psd_blks],
    }
    return c, A, b_vec, cone


def main():
    sdpa_path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(
        "local-flags-certificates/certificates/bipartite_strong_edge_colouring.sdpa"
    )
    max_iters = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
    eps = float(sys.argv[3]) if len(sys.argv) > 3 else 1e-5

    print(f"Parsing {sdpa_path}...")
    t0 = time.time()
    m, nblocks, sizes, c, entries = parse_sdpa(sdpa_path)
    print(f"  m={m}, nblocks={nblocks}, {len(entries)} nz. {time.time()-t0:.1f}s")
    print(f"  PSD: {sum(1 for s in sizes if s>0)}, diag: {sum(1 for s in sizes if s<0)}")

    print(f"Building SCS form (SDPA-primal: min c^T y, Σ y_i F_i - F_0 ⪰ 0)...")
    t0 = time.time()
    c_scs, A, b, cone = build_scs(m, sizes, c, entries)
    print(f"  vars: {m}, rows: {A.shape[0]}, nnz: {A.nnz}. Built in {time.time()-t0:.1f}s")
    print(f"  cone: l={cone['l']}, #PSD={len(cone['s'])}, PSD dims head={cone['s'][:5]}")

    print(f"Solving with SCS (max_iters={max_iters}, eps={eps})...")
    t0 = time.time()
    solver = scs.SCS(
        {'P': sp.csc_matrix((m, m)), 'c': c_scs, 'A': A, 'b': b},
        cone,
        max_iters=max_iters,
        eps_abs=eps,
        eps_rel=eps,
        verbose=True,
    )
    sol = solver.solve()
    elapsed = time.time() - t0
    print(f"\n  Solved in {elapsed:.1f}s")
    print(f"  Status: {sol['info']['status']}")
    print(f"  min c^T y (= CSDP 'Dual obj' = SDPA-primal value): {sol['info']['pobj']:.6f}")
    print(f"  Dual: {sol['info']['dobj']:.6f}")
    print(f"  Primal residual: {sol['info']['res_pri']:.3e}")
    print(f"  Dual residual: {sol['info']['res_dual']:.3e}")
    print(f"  Iter: {sol['info']['iter']}")


if __name__ == "__main__":
    main()
