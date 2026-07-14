#!/usr/bin/env python3
"""Solve an SDPA-format file via CVXPY (open-source ipm/splitting solvers).

Second-solver cross-check for the SEC SDP bounds — independent of SDPA-LR
(which generated the original cert) and CSDP (which failed at the general
SEC scale).

SDPA's primal form (what CSDP and SDPA-LR report as `Dual objective`, but
equivalent to the primal optimum under strong duality):

    min  c^T y
    s.t. F_0 + sum_i y_i F_i ⪰ 0  (per block, summed over blocks)

Equivalently (CSDP's reported "Primal objective", the dual of the above):
    max tr(F_0 X)  s.t. tr(F_i X) = c_i, X ⪰ 0

We solve the primal `min c^T y` form: variables y ∈ ℝ^m (m = #constraints,
~3.8k for bipartite, ~17.9k for general). Constraints: per-block PSD
(or nonneg-vector) of F_0^b + Σ y_i F_i^b.

Expected outputs:
- Bipartite: ≈ -4.0928
- General:   ≈ -10.6444
"""

import sys
import time
from pathlib import Path
import numpy as np
import scipy.sparse as sp
import cvxpy as cp


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


def build_block_data(entries, sizes, m):
    """Per block b (0-indexed), build sparse coefficient storage.

    For a block of dim d:
      If PSD (size>0): F_k^b is a symmetric d×d sparse matrix.
        Storage: dict k → csr_matrix (or coo_matrix).
      If diag (size<0): F_k^b is a d-vector (the diagonal).
        Storage: dict k → np.array of length d.
    """
    n_blocks = len(sizes)
    block_data = [None] * n_blocks
    # Accumulate per (b, k) entries
    blk_entries = [dict() for _ in range(n_blocks)]
    for k, b1, i, j, v in entries:
        b = b1 - 1
        d = blk_entries[b].setdefault(k, {})
        if sizes[b] > 0:
            # Symmetric: add (i-1,j-1) and (j-1,i-1)
            key1 = (i - 1, j - 1)
            d[key1] = d.get(key1, 0.0) + v
            if i != j:
                key2 = (j - 1, i - 1)
                d[key2] = d.get(key2, 0.0) + v
        else:
            assert i == j
            d[i - 1] = d.get(i - 1, 0.0) + v
    # Convert to sparse matrices / dense vectors
    for b in range(n_blocks):
        dim = abs(sizes[b])
        if sizes[b] > 0:
            block_data[b] = {}
            for k, d in blk_entries[b].items():
                if d:
                    rows = [r for (r, _) in d.keys()]
                    cols = [c for (_, c) in d.keys()]
                    vals = list(d.values())
                    block_data[b][k] = sp.csr_matrix((vals, (rows, cols)), shape=(dim, dim))
        else:
            block_data[b] = {}
            for k, d in blk_entries[b].items():
                arr = np.zeros(dim)
                for r, v in d.items():
                    arr[r] = v
                block_data[b][k] = arr
    return block_data


def main():
    sdpa_path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(
        "local-flags-certificates/certificates/bipartite_strong_edge_colouring.sdpa"
    )
    solver_name = sys.argv[2].upper() if len(sys.argv) > 2 else "SCS"

    print(f"Parsing {sdpa_path}...")
    t0 = time.time()
    m, nblocks, sizes, c, entries = parse_sdpa(sdpa_path)
    print(f"  m={m}, nblocks={nblocks}, {len(entries)} nz. {time.time()-t0:.1f}s")
    n_psd = sum(1 for s in sizes if s > 0)
    n_diag = sum(1 for s in sizes if s < 0)
    print(f"  PSD blocks: {n_psd}, diag blocks: {n_diag}")

    print(f"Building per-block coefficient data...")
    t0 = time.time()
    block_data = build_block_data(entries, sizes, m)
    print(f"  Built in {time.time()-t0:.1f}s")

    print(f"Building CVXPY problem in SDPA-primal form (min c^T y, sum y_i F_i - F_0 ⪰ 0)...")
    t0 = time.time()
    y = cp.Variable(m)
    constraints = []
    for b in range(nblocks):
        dim = abs(sizes[b])
        if sizes[b] > 0:
            # PSD: sum_i y_i F_i^b - F_0^b ⪰ 0 (CSDP convention)
            if 0 in block_data[b]:
                F0_arr = block_data[b][0].toarray()
            else:
                F0_arr = np.zeros((dim, dim))
            terms = [cp.Constant(-F0_arr)]
            for k in range(1, m + 1):
                if k in block_data[b]:
                    Fk = block_data[b][k]
                    terms.append(y[k - 1] * cp.Constant(Fk.toarray()))
            S = cp.sum(terms) if len(terms) > 1 else terms[0]
            constraints.append(S >> 0)
        else:
            # diag: sum_i y_i F_i^b - F_0^b ≥ 0 (entrywise)
            v0 = block_data[b].get(0, np.zeros(dim))
            terms = [cp.Constant(-v0)]
            for k in range(1, m + 1):
                if k in block_data[b]:
                    terms.append(y[k - 1] * cp.Constant(block_data[b][k]))
            v = cp.sum(terms) if len(terms) > 1 else terms[0]
            constraints.append(v >= 0)
    objective = cp.Minimize(c @ y)

    prob = cp.Problem(objective, constraints)
    print(f"  Built in {time.time()-t0:.1f}s. {len(constraints)} block constraints, {m} variables.")

    print(f"Solving with {solver_name}...")
    t0 = time.time()
    kwargs = {'verbose': True}
    if solver_name == "SCS":
        kwargs.update(max_iters=50000, eps=1e-6)
    prob.solve(solver=getattr(cp, solver_name), **kwargs)
    print(f"\n  Solved in {time.time()-t0:.1f}s")
    print(f"  Status: {prob.status}")
    print(f"  Optimal value (= min c^T y, matches CSDP 'Dual objective'): {prob.value}")


if __name__ == "__main__":
    main()
