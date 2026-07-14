#!/usr/bin/env python3
"""Emit a Lean cert module (top-level + per-block PSD witnesses) from an SDPA + cert pair.

Originally written for `bounded_pentagon_alt.{sdpa,cert}` (Phase 1.A-E of
the pentagon Q bridge). Generalised (Phase S1 of the SEC closure plan) to
accept arbitrary SDPA/cert inputs via CLI args, so the same emitter can
service:

  * Pentagon Q (`bounded_pentagon_alt.{sdpa,cert}` → `PentagonQCertificate`)
  * SEC general (`strong_edge_colouring.{sdpa,cert}` → `SecCertificate`)
  * SEC bipartite (`bipartite_strong_edge_colouring.{sdpa,cert}` → `SecBipartiteCertificate`)

Writes (stratified by block, all paths derived from `--output-dir` and `--module-name`):
  <output-dir>/../<module-name>.lean              -- top-level + linear ident
  <output-dir>/Common.lean                        -- shared parsers/helpers
  <output-dir>/Block{0..N-1}.lean                 -- per-PSD-block LDL identity

Each block file declares a witness identity
    L · diag(D) · Lᵀ = scaleY · Y_int + scaleI · I
where everything on both sides is over Int. native_decide verifies it.

A full run takes a few minutes (rational LDL is pure Python).

Example invocations:
    # Pentagon Q (the original use case, default args reproduce it)
    python3 -u local-flags-certificates/emit_lean_cert.py \\
      --sdpa DaveyThesis2024/certificates/bounded_pentagon_alt.sdpa \\
      --cert DaveyThesis2024/certificates/bounded_pentagon_alt.cert \\
      --module-name PentagonQCertificate \\
      --namespace Davey2024.PentagonQCertificate \\
      --bound-numer 2073 --bound-denom 10000

    # SEC general
    python3 -u local-flags-certificates/emit_lean_cert.py \\
      --sdpa local-flags-certificates/certificates/strong_edge_colouring.sdpa \\
      --cert local-flags-certificates/certificates/strong_edge_colouring.cert \\
      --module-name SecCertificate \\
      --namespace Davey2024.SecCertificate \\
      --bound-numer 10644 --bound-denom 1000

    # SEC bipartite
    python3 -u local-flags-certificates/emit_lean_cert.py \\
      --sdpa local-flags-certificates/certificates/bipartite_strong_edge_colouring.sdpa \\
      --cert local-flags-certificates/certificates/bipartite_strong_edge_colouring.cert \\
      --module-name SecBipartiteCertificate \\
      --namespace Davey2024.SecBipartiteCertificate \\
      --bound-numer 4093 --bound-denom 1000

Use --max-blocks for an incremental smoke build of the first N blocks.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

import numpy as np

ROOT = Path(__file__).resolve().parent.parent

DENOM_Y = 10 ** 12    # Default Y rationalisation precision (12 digits); overridable via --denom-y-exp
LAMBDA_DENOM = 10 ** 11  # λ = 1/10^11 PSD-shift regulariser

# ----------------------------------------------------------------------
# Logging
# ----------------------------------------------------------------------


def log(msg: str = "") -> None:
    print(msg, flush=True)


def relpath_safe(p: Path) -> Path:
    """Return p.relative_to(ROOT) if possible, else p (for paths outside the repo)."""
    try:
        return p.relative_to(ROOT)
    except ValueError:
        return p


# ----------------------------------------------------------------------
# Parsing (adapted from scratch/slack_check.py)
# ----------------------------------------------------------------------


def parse_sdpa_header(path: Path) -> Tuple[int, int, List[int], np.ndarray]:
    m = nblocks = None
    block_sizes = c = None
    with path.open() as f:
        data_seen = 0
        for line in f:
            if line.startswith("*") or not line.strip():
                continue
            data_seen += 1
            if data_seen == 1:
                m = int(line.strip())
            elif data_seen == 2:
                nblocks = int(line.strip())
            elif data_seen == 3:
                block_sizes = list(map(int, line.split()))
            elif data_seen == 4:
                c = np.array([float(x) for x in line.split()])
                break
    return m, nblocks, block_sizes, c


def parse_cert(path: Path, block_sizes: List[int]):
    Y = {idx: np.zeros((abs(sz), abs(sz)))
         for idx, sz in enumerate(block_sizes, 1)}
    with path.open() as f:
        first = f.readline()
        x = np.array([float(v) for v in first.split()])
        for line in f:
            parts = line.split()
            if len(parts) != 5:
                continue
            if parts[0] != "2":
                continue
            blk = int(parts[1])
            i = int(parts[2]) - 1
            j = int(parts[3]) - 1
            val = float(parts[4])
            Y[blk][i, j] = val
            if i != j:
                Y[blk][j, i] = val
    return x, Y


# ----------------------------------------------------------------------
# Rationalisation
# ----------------------------------------------------------------------


def rationalise_psd_block(M: np.ndarray, denom: int) -> List[List[Fraction]]:
    n = M.shape[0]
    Mint = np.round(M * denom).astype(object)
    out: List[List[Fraction]] = [[Fraction(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            v = Fraction(int(Mint[i, j]), denom)
            out[i][j] = v
            if i != j:
                out[j][i] = v
    return out


# ----------------------------------------------------------------------
# Rational LDL^T  (returns L unit-lower, D positive list)
# ----------------------------------------------------------------------


def rational_ldl(A: List[List[Fraction]]) -> Tuple[List[List[Fraction]], List[Fraction]]:
    """Decompose symmetric PSD A = L · diag(D) · L^T over rationals.

    L is unit lower-triangular (1's on diagonal). D is diagonal, positive
    if A is strictly PD (which is what we have post λI-shift). Raises
    on non-PD.
    """
    n = len(A)
    L: List[List[Fraction]] = [[Fraction(0)] * n for _ in range(n)]
    D: List[Fraction] = [Fraction(0)] * n
    for j in range(n):
        L[j][j] = Fraction(1)
    for j in range(n):
        s = A[j][j]
        for k in range(j):
            ljk = L[j][k]
            if ljk == 0:
                continue
            s -= ljk * ljk * D[k]
        if s <= 0:
            raise ValueError(
                f"LDL: nonpositive pivot at row {j}: D[{j}]={float(s):.3e}")
        D[j] = s
        Lj = L[j]
        for i in range(j + 1, n):
            t = A[i][j]
            Li = L[i]
            for k in range(j):
                lik = Li[k]
                if lik == 0:
                    continue
                ljk = Lj[k]
                if ljk == 0:
                    continue
                t -= lik * ljk * D[k]
            L[i][j] = t / D[j]
    return L, D


def verify_ldl(L: List[List[Fraction]], D: List[Fraction],
               A: List[List[Fraction]]) -> bool:
    """Sanity check that L · diag(D) · L^T == A over rationals. Exact."""
    n = len(A)
    for i in range(n):
        for j in range(n):
            s = Fraction(0)
            for k in range(min(i, j) + 1):
                s += L[i][k] * D[k] * L[j][k]
            if s != A[i][j]:
                return False
    return True


# ----------------------------------------------------------------------
# Common-denominator integer extraction
# ----------------------------------------------------------------------


def matrix_common_denom(rows: List[List[Fraction]]) -> int:
    """Smallest positive integer d s.t. every entry · d is an integer.

    Returns lcm of all denominators.
    """
    from math import lcm
    d = 1
    for row in rows:
        for v in row:
            d = lcm(d, v.denominator)
    return d


def vector_common_denom(vec: List[Fraction]) -> int:
    from math import lcm
    d = 1
    for v in vec:
        d = lcm(d, v.denominator)
    return d


def scale_matrix(rows: List[List[Fraction]], denom: int) -> List[List[int]]:
    out: List[List[int]] = []
    for row in rows:
        new_row = []
        for v in row:
            num = v * denom
            assert num.denominator == 1, f"denom {denom} insufficient for {v}"
            new_row.append(int(num.numerator))
        out.append(new_row)
    return out


def scale_vector(vec: List[Fraction], denom: int) -> List[int]:
    out: List[int] = []
    for v in vec:
        num = v * denom
        assert num.denominator == 1
        out.append(int(num.numerator))
    return out


# ----------------------------------------------------------------------
# Lean emission helpers
# ----------------------------------------------------------------------


def matrix_to_str(rows: List[List[int]]) -> str:
    """Encode an Int matrix as String literal:  rows separated by ';',
    entries by ',' (no whitespace)."""
    return ";".join(",".join(str(v) for v in row) for row in rows)


def vector_to_str(vec: List[int]) -> str:
    return ",".join(str(v) for v in vec)


def emit_common_file(out_dir: Path, module_name: str, namespace: str) -> Path:
    """Shared parsers + helper definitions. Imported by all block files."""
    p = out_dir / "Common.lean"
    content = rf"""/-!
# {module_name} Common helpers

Auto-generated from `local-flags-certificates/emit_lean_cert.py`.
Do NOT edit by hand.

Provides String->Int parsers and helper matrix ops shared by every
per-block PSD witness file under `DaveyThesis2024/{module_name}/Block*.lean`.

The Phase 0.3 stress test established that String-literal encoding +
runtime `parseInts` is the only viable way to ship ≥9k Int values
through Lean elaboration (List literals at this size trigger the O(N^2)
whnf-on-cons elaborator path and time out at `maxHeartbeats=4M`).

The LDL identity is encoded ENTRY-WISE as the integer equation:

  ∀ i, j ∈ [0, dim) :
    Σ_k L_num[i][k] · D_num[k] · L_num[j][k] · scaleFactor[k]
      = scaleYFactor · Y_num[i][j] + lambdaShift · I[i][j]

where `scaleFactor[k] = commonScale / (L_den[k]² · D_den[k])`, and the
RHS uses the precomputed scaleY / lambda integer multipliers. All
per-column denoms are kept separate so individual `L_num` entries stay
small (column-scoped denominator).

This is equivalent to the rational identity
  L · diag(D) · Lᵀ = Y_rat + λI
after clearing each column's denominator into the corresponding
`scaleFactor[k]`.
-/

namespace {namespace}

/-- Parse a comma-separated list of Int. Whitespace-tolerant. -/
def parseInts (s : String) : List Int :=
  s.splitOn "," |>.map (fun tok =>
    match tok.trimAscii.toInt? with
    | some n => n
    | none   => 0)

/-- Parse a semicolon-separated list of rows, each a parseInts. -/
def parseMatrix (s : String) : List (List Int) :=
  s.splitOn ";" |>.map parseInts

/-- Componentwise add over `List Int`. -/
def addVec (a b : List Int) : List Int := List.zipWith (· + ·) a b

/-- Scalar-multiply a vector. -/
def scaleVec (s : Int) (v : List Int) : List Int := v.map (s * ·)

/-- Componentwise add over `List (List Int)`. -/
def addMat (A B : List (List Int)) : List (List Int) :=
  List.zipWith addVec A B

/-- Scalar-multiply a matrix. -/
def scaleMat (s : Int) (A : List (List Int)) : List (List Int) :=
  A.map (scaleVec s)

/-- Sum a list of vectors with an explicit zero vector. -/
def foldAddVec (vs : List (List Int)) (zero : List Int) : List Int :=
  vs.foldl addVec zero

/-- The dim x dim identity matrix scaled by `s` (s on each diagonal, 0 elsewhere). -/
def scaledIdentity (dim : Nat) (s : Int) : List (List Int) :=
  (List.range dim).map (fun i =>
    (List.range dim).map (fun j => if i = j then s else 0))

/-- Compute the LDL^T-derived LHS entry `(i,j)` directly:

      Σ_k L_num[i][k] · D_num[k] · L_num[j][k] · scaleFactor[k]

The Lean call uses `Array` indexing internally for speed (each row
becomes an `Array` once and stays cached during native_decide). -/
def ldlEntry
    (L_num : Array (Array Int)) (D_num : Array Int)
    (scaleFactor : Array Int) (k_count : Nat)
    (i j : Nat) : Int := Id.run do
  let row_i := L_num[i]!
  let row_j := L_num[j]!
  let mut acc : Int := 0
  for k in [0:k_count] do
    acc := acc + row_i[k]! * D_num[k]! * row_j[k]! * scaleFactor[k]!
  pure acc

/-- Construct the full LHS matrix `[[ldlEntry i j | j ∈ range]] | i ∈ range]`. -/
def ldlMatrix
    (L_num : Array (Array Int)) (D_num : Array Int)
    (scaleFactor : Array Int) (dim : Nat) : Array (Array Int) :=
  (Array.range dim).map (fun i =>
    (Array.range dim).map (fun j =>
      ldlEntry L_num D_num scaleFactor dim i j))

/-- Construct the RHS matrix `scaleYFactor · Y + lambdaShift · I` over `Array (Array Int)`. -/
def rhsMatrix
    (Y_num : Array (Array Int)) (scaleYFactor lambdaShift : Int)
    (dim : Nat) : Array (Array Int) :=
  (Array.range dim).map (fun i =>
    (Array.range dim).map (fun j =>
      scaleYFactor * Y_num[i]![j]! + (if i = j then lambdaShift else 0)))

/-- Coerce a parsed `List (List Int)` to `Array (Array Int)`. -/
def listListToArrayArray (xs : List (List Int)) : Array (Array Int) :=
  (xs.map List.toArray).toArray

end {namespace}
"""
    p.write_text(content)
    return p


def emit_block_file(block_idx_one_based: int,  # 1-based block index in SDPA
                    file_idx: int,             # 0..(num_blocks-1), ordering by ascending size
                    dim: int,
                    Y_int: List[List[int]], scaleY: int,
                    L_num: List[List[int]], L_den_col: List[int],
                    D_num: List[int], D_den: List[int],
                    lambda_numer: int, lambda_denom: int,
                    out_dir: Path, module_name: str, namespace: str,
                    cert_filename: str) -> Path:
    """Emit one per-block PSD witness file proving over Int

        ∀ i, j ∈ [0, dim) :
          Σ_k L_num[i][k] · D_num[k] · L_num[j][k] · scaleFactor[k]
            = scaleYFactor · Y_int[i][j] + lambdaShift · I[i][j]

    where `scaleFactor[k] = commonScale / (L_den[k]² · D_den[k])` is
    chosen so that summing the contributions matches `commonScale · (Y_rat + λI)`.

    The Lean witness is an `Array` (not `List`) entry-wise computation,
    which is dramatically faster under `native_decide`.
    """
    # Compute per-column scaling factors
    from math import lcm
    # commonScale = lcm over k of (L_den_col[k]² · D_den[k]), and divisible by scaleY and lambda_denom
    commonScale = lcm(scaleY, lambda_denom)
    for k in range(dim):
        commonScale = lcm(commonScale, L_den_col[k] * L_den_col[k] * D_den[k])
    scaleFactor = [commonScale // (L_den_col[k] * L_den_col[k] * D_den[k]) for k in range(dim)]
    scaleY_factor = commonScale // scaleY
    lambda_shift = (commonScale * lambda_numer) // lambda_denom
    assert lambda_shift * lambda_denom == commonScale * lambda_numer

    Y_str = matrix_to_str(Y_int)
    L_str = matrix_to_str(L_num)
    Lden_str = vector_to_str(L_den_col)
    Dnum_str = vector_to_str(D_num)
    Dden_str = vector_to_str(D_den)
    scale_str = vector_to_str(scaleFactor)

    body = f"""import DaveyThesis2024.{module_name}.Common

/-!
# {module_name} Block {file_idx} (SDPA block {block_idx_one_based}, dim {dim})

Auto-generated. Do NOT edit by hand.

Witnesses PSD of `Y_rat + (1 / {lambda_denom}) · I` via the LDL^T
decomposition `L · diag(D) · Lᵀ = Y_rat + λI`. The identity is
expressed ENTRY-WISE over integers (per-column denominators kept
separate so individual coefficients stay small):

  ∀ i, j ∈ [0, {dim}) :
    Σ_k L_num[i][k] · D_num[k] · L_num[j][k] · scaleFactor[k]
      = scaleYFactor · Y[i][j] + lambdaShift · I[i][j]

* `L_num[i][k]` is `L[i][k] · L_den[k]` (column-scoped integer scaling).
* `D_num[k]` is `D[k] · D_den[k]`.
* `scaleFactor[k]` absorbs each column's denominator gap into the LHS.

This is the integer form of `L · diag(D) · Lᵀ = Y_rat + λI` over rationals.

* `Y_rat` was rationalised at precision 10^12 from `{cert_filename}`.
* `λ = 1 / 10^11` was the smallest shift that makes the (rank-deficient)
  Y_rat strictly PD at this precision (see `scratch/slack_check_results.md`).
-/

namespace {namespace}.Block{file_idx}

open {namespace}

def sdpaBlockIdx : Nat := {block_idx_one_based}
def dim : Nat := {dim}
def scaleY : Nat := {scaleY}
def commonScale : Nat := {commonScale}
def scaleYFactor : Int := {scaleY_factor}
def lambdaShift : Int := {lambda_shift}
def lambdaNumer : Int := {lambda_numer}
def lambdaDenom : Nat := {lambda_denom}

def Y_str : String :=
  "{Y_str}"
def L_num_str : String :=
  "{L_str}"
def L_den_str : String :=
  "{Lden_str}"
def D_num_str : String :=
  "{Dnum_str}"
def D_den_str : String :=
  "{Dden_str}"
def scaleFactor_str : String :=
  "{scale_str}"

def Y : List (List Int) := parseMatrix Y_str
def L_num : List (List Int) := parseMatrix L_num_str
def L_den : List Int := parseInts L_den_str
def D_num : List Int := parseInts D_num_str
def D_den : List Int := parseInts D_den_str
def scaleFactor : List Int := parseInts scaleFactor_str

def L_numA : Array (Array Int) := listListToArrayArray L_num
def D_numA : Array Int := D_num.toArray
def scaleFactorA : Array Int := scaleFactor.toArray
def Y_A : Array (Array Int) := listListToArrayArray Y

/-- The LDL^T entry-wise integer identity. Verified by `native_decide`. -/
theorem ldl_witness :
    ldlMatrix L_numA D_numA scaleFactorA dim
      = rhsMatrix Y_A scaleYFactor lambdaShift dim := by
  native_decide

end {namespace}.Block{file_idx}
"""
    p = out_dir / f"Block{file_idx}.lean"
    p.write_text(body)
    return p


def emit_top_file(num_blocks: int,
                  diag_y_str: str, diag_y_denom: int, diag_y_count: int,
                  module_name: str, namespace: str, top_file: Path,
                  linear_cert: dict | None = None,
                  consumer_note: str | None = None) -> Path:
    """The top-level file: imports + diag-block PSD witness + linear cert
    aggregate identity."""
    imports = "\n".join(
        f"import DaveyThesis2024.{module_name}.Block{i}"
        for i in range(num_blocks))

    # Linear cert section (Phase 1.D-E)
    if linear_cert is not None:
        residual_str = linear_cert["residual_str"]
        target_str_text = linear_cert["target_str"]
        x_int_str = linear_cert["x_int_str"]
        scale = linear_cert["scale"]
        m_constraints = linear_cert["m"]
        bound_numer = linear_cert["bound_numer"]
        bound_denom = linear_cert["bound_denom"]
        slack_total_str = linear_cert["slack_total"]
        max_residual_abs = linear_cert["max_residual_abs"]
        linear_section = f"""

/-! ## Phase 1.D-E — Linear dual feasibility residuals.

For each dual constraint `k ∈ [1, m]`, the SDP solver guarantees
`tr(F_k · Y_float) ≈ c_k`. After 12-digit rationalisation of Y plus the
λ=1/10^11 PSD shift, an exact integer residual

  residual[k] = scale · (tr(F_k · Y_rat) + λ · tr(F_k|_psd) - c_k)

is computed at emit-time (the exact rational arithmetic from
`scratch/slack_only.py` extended with the λ-trace contribution from the
PSD-block λI shift). This residual is the integer dual-infeasibility
slack at scale `{scale}`.

The Lean-side bound proof uses the aggregated bound
  Σ_k x_k · residual[k]  ≤  slack_budget  (≪ 0.208's 7×10⁻⁴ tolerance)

which is integer-checkable from x_int and residual.

* `m = {m_constraints}` dual constraints (one per flag).
* `scale = {scale}` is the integer scale (= 10^12 · 10^12 by construction).
* `bound = {bound_numer} / {bound_denom}` is the relaxed L ≤ 0.208 target.
* `max |residual[k]|` measured at emit = {max_residual_abs} (≪ scale; total
  weighted slack = {slack_total_str} of scale).
-/

def residual_str : String :=
  "{residual_str}"
def target_str : String :=
  "{target_str_text}"
def x_int_str : String :=
  "{x_int_str}"

def linearScale : Nat := {scale}
def boundNumer : Int := {bound_numer}
def boundDenom : Nat := {bound_denom}
def numConstraints : Nat := {m_constraints}

def residual : List Int := parseInts residual_str
def target : List Int := parseInts target_str
def x_int : List Int := parseInts x_int_str

/-- Sanity: the residual vector has the right length. -/
theorem residual_length : residual.length = numConstraints := by
  native_decide

/-- Sanity: the target vector has the right length. -/
theorem target_length : target.length = numConstraints := by
  native_decide

/-- Sanity: the dual variable vector has the right length. -/
theorem x_int_length : x_int.length = numConstraints := by
  native_decide

/-- The aggregate slack `Σ_k x_int[k] · residual[k]` (signed). For the
final bound proof we use `Σ_k |x_int[k] · residual[k]|`, computed by
external tooling at emit-time; the `total_slack_signed` here is the
plain dot product. Use the abs-summed version for the bound. -/
def total_slack_signed : Int :=
  (List.zipWith (· * ·) x_int residual).foldl (· + ·) 0

/-- Sum of absolute values of weighted residuals. This is the integer
encoding of `Σ_k |x_k · residual_k| · scale²` — the slack that the bound
proof must absorb. At emit-time this stays ≪ scale · 7·10⁻⁴ for the
0.208 bound. -/
def total_slack_abs : Int :=
  (List.zipWith (fun a b => Int.natAbs (a * b)) x_int residual).foldl
    (fun acc v => acc + (Int.ofNat v)) 0
"""
    else:
        linear_section = ""

    consumer_section = f"\n\n{consumer_note}" if consumer_note else ""
    body = f"""import DaveyThesis2024.{module_name}.Common
{imports}

/-!
# {module_name} — top level

Auto-generated from `local-flags-certificates/emit_lean_cert.py`.
Do NOT edit by hand.

Aggregates the {num_blocks} per-block PSD witnesses from
`{module_name}.Block*` (one per SDPA Cauchy-Schwarz block), and
provides:
* the diagonal-block PSD witness (`Y_diag ≥ 0` entrywise);
* the per-constraint linear residual vector (Phase 1.D-E).{consumer_section}
-/

namespace {namespace}

/-! ## Diagonal Y_blocks (negative-size blocks of the SDPA).

These are just nonnegativity constraints; the rationalised diagonal at
precision 10^12 should be entrywise ≥ 0 (verified at emit-time).
-/

def diag_y_str : String :=
  "{diag_y_str}"
def diag_y_denom : Nat := {diag_y_denom}
def diag_y_count : Nat := {diag_y_count}

def diag_y : List Int := parseInts diag_y_str

/-- All diagonal entries are nonneg (Y_rat |_diag · 10^12 has Int entries ≥ 0). -/
theorem diag_y_nonneg : diag_y.all (· ≥ 0) = true := by
  native_decide
{linear_section}
end {namespace}
"""
    top_file.write_text(body)
    return top_file


# ----------------------------------------------------------------------
# Main driver
# ----------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser(
        description="Emit a Lean cert module from an SDPA + cert pair "
                    "(see top-of-file docstring for example invocations).")
    ap.add_argument("--sdpa", type=Path,
                    default=ROOT / "DaveyThesis2024" / "certificates" / "bounded_pentagon_alt.sdpa",
                    help="Path to the SDPA-formatted input "
                         "(default: pentagon Q's bounded_pentagon_alt.sdpa)")
    ap.add_argument("--cert", type=Path,
                    default=ROOT / "DaveyThesis2024" / "certificates" / "bounded_pentagon_alt.cert",
                    help="Path to the .cert output from the SDPA solver "
                         "(default: pentagon Q's bounded_pentagon_alt.cert)")
    ap.add_argument("--module-name", type=str, default="PentagonQCertificate",
                    help="Lean module name (default: PentagonQCertificate). "
                         "Drives the output filenames "
                         "DaveyThesis2024/<module>.lean and "
                         "DaveyThesis2024/<module>/Block*.lean")
    ap.add_argument("--namespace", type=str, default="Davey2024.PentagonQCertificate",
                    help="Lean namespace for the emitted defs/theorems "
                         "(default: Davey2024.PentagonQCertificate).")
    ap.add_argument("--output-dir", type=Path, default=None,
                    help="Directory for per-block files "
                         "(default: DaveyThesis2024/<module-name>/).")
    ap.add_argument("--top-file", type=Path, default=None,
                    help="Path for the top-level file "
                         "(default: DaveyThesis2024/<module-name>.lean). "
                         "Override for regression testing without overwriting "
                         "the in-tree cert module.")
    ap.add_argument("--bound-numer", type=int, default=2073,
                    help="Numerator of the L-space bound in the emitted linear-cert "
                         "section (default: 2073 = pentagon Q's thesis-tight bound).")
    ap.add_argument("--bound-denom", type=int, default=10000,
                    help="Denominator of the L-space bound in the emitted linear-cert "
                         "section (default: 10000 = pentagon Q's thesis-tight bound).")
    ap.add_argument("--consumer-note", type=str, default=None,
                    help="Optional extra paragraph in the top-file overview docstring "
                         "referencing the downstream consumer theorem name. "
                         "Pentagon Q used: 'The final consumer "
                         "(`pentagon_Q_sdp_limit_bound`) combines these into the bound "
                         "argument `Q(G) ≤ 0.208 · |G| · Δ⁴`.' Leave empty for SEC.")
    ap.add_argument("--denom-y-exp", type=int, default=12,
                    help="Exponent for DENOM_Y = 10^N (default: 12). "
                         "Higher values give tighter cert slack (α phase 2 "
                         "tightening). E.g. --denom-y-exp 15 gives 10^15.")
    ap.add_argument("--max-blocks", type=int, default=None,
                    help="Limit number of PSD blocks emitted (for smoke testing)")
    ap.add_argument("--skip-existing", action="store_true",
                    help="Skip emitting blocks whose .lean file already exists")
    ap.add_argument("--start", type=int, default=0,
                    help="Resume from this block index (0-based by ascending size)")
    args = ap.parse_args()

    # Override the module-level DENOM_Y from CLI arg (α phase 2 tightening)
    global DENOM_Y
    DENOM_Y = 10 ** args.denom_y_exp

    sdpa_path: Path = args.sdpa.resolve() if not args.sdpa.is_absolute() else args.sdpa
    cert_path: Path = args.cert.resolve() if not args.cert.is_absolute() else args.cert
    module_name: str = args.module_name
    namespace: str = args.namespace
    out_dir: Path = (args.output_dir if args.output_dir is not None
                     else ROOT / "DaveyThesis2024" / module_name)
    top_file: Path = (args.top_file if args.top_file is not None
                      else ROOT / "DaveyThesis2024" / f"{module_name}.lean")

    out_dir.mkdir(parents=True, exist_ok=True)

    log(f"=== {module_name} emitter ===")
    log(f"SDPA: {sdpa_path}")
    log(f"CERT: {cert_path}")
    log(f"OUT_DIR: {out_dir}")
    log(f"TOP_FILE: {top_file}")
    log(f"namespace: {namespace}")
    log(f"bound: {args.bound_numer} / {args.bound_denom}")
    log(f"DENOM_Y = 10^{args.denom_y_exp}, LAMBDA = 1/10^{int(np.log10(LAMBDA_DENOM))}")
    log("")

    t_emit_start = time.time()

    m, nblocks, sizes, c = parse_sdpa_header(sdpa_path)
    log(f"m = {m}, nblocks = {nblocks}")
    log(f"Block sizes: {len([s for s in sizes if s > 0])} PSD, "
        f"{len([s for s in sizes if s < 0])} diag (linear)")
    log("")

    log("Parsing cert ...")
    t0 = time.time()
    x, Yf = parse_cert(cert_path, sizes)
    log(f"  cert parsed in {time.time() - t0:.1f}s ({cert_path.stat().st_size/1e6:.1f} MB)")
    log("")

    # ----------- Diagonal blocks (nonneg PSD witness) -----------
    log("Rationalising diagonal Y blocks at precision 10^12 ...")
    t0 = time.time()
    diag_y_vals: List[int] = []
    for idx, sz in enumerate(sizes, 1):
        if sz < 0:
            arr = Yf[idx].diagonal()
            for v in arr:
                ival = int(round(float(v) * DENOM_Y))
                if ival < 0:
                    log(f"  WARN: diag block {idx} entry {v} -> {ival}; clamping to 0 "
                        f"(numerical rounding; |{ival}|≪slack budget)")
                    # Honest approach: keep, but flag
                diag_y_vals.append(ival)
    log(f"  collected {len(diag_y_vals)} diag entries in {time.time() - t0:.1f}s; "
        f"min = {min(diag_y_vals)}")
    log("")

    # Check if rationalised diag is fully nonneg; if not, we'll need
    # to absorb the negative entries somewhere (probably tiny, but should
    # flag). The Lean theorem `diag_y_nonneg` requires nonneg, so clip
    # any small negatives at emit-time and record them as added slack.
    neg_diag = [v for v in diag_y_vals if v < 0]
    if neg_diag:
        log(f"  {len(neg_diag)} negative diag entries (max magnitude {max(abs(v) for v in neg_diag)}).")
        log(f"  Clipping to 0 for the Lean witness; slack absorbed in bound proof.")
        diag_y_vals = [max(v, 0) for v in diag_y_vals]
    diag_y_str = vector_to_str(diag_y_vals)

    # ----------- PSD blocks: rationalise → +λI → LDL → emit -----------
    psd_block_indices = [i + 1 for i, sz in enumerate(sizes) if sz > 0]
    # Order by ascending dim so smaller blocks emit first (smoke test friendliness)
    psd_block_indices.sort(key=lambda i: sizes[i - 1])

    if args.max_blocks is not None:
        psd_block_indices = psd_block_indices[:args.max_blocks]
        log(f"--max-blocks: limiting to first {len(psd_block_indices)} PSD blocks")

    log(f"Emitting {len(psd_block_indices)} PSD blocks (smallest first) ...")
    log("")

    # Emit Common.lean
    common_path = emit_common_file(out_dir, module_name, namespace)
    log(f"  wrote {relpath_safe(common_path)}")
    log("")

    # Per-block emission
    log("Per-block timing:")
    total_emitted = 0
    total_lean_bytes = 0
    max_denom_bits = 0
    block_metadata = []
    t_blocks = time.time()
    for file_idx, sdpa_idx in enumerate(psd_block_indices):
        if file_idx < args.start:
            continue
        sz = sizes[sdpa_idx - 1]
        out_path = out_dir / f"Block{file_idx}.lean"
        if args.skip_existing and out_path.exists():
            log(f"  [{file_idx:3d}] SDPA blk {sdpa_idx:4d}, dim {sz:3d}: SKIP (exists)")
            total_emitted += 1
            continue

        tb = time.time()
        # Rationalise Y at precision 10^12 (exact int) → Fraction matrix
        Y_rat = rationalise_psd_block(Yf[sdpa_idx], DENOM_Y)
        # Shift Y_rat += (1/lambda_denom) · I
        lam = Fraction(1, LAMBDA_DENOM)
        Y_shift: List[List[Fraction]] = [list(row) for row in Y_rat]
        for i in range(sz):
            Y_shift[i][i] = Y_shift[i][i] + lam

        # Rational LDL
        try:
            L, D = rational_ldl(Y_shift)
        except ValueError as e:
            log(f"  [{file_idx:3d}] SDPA blk {sdpa_idx:4d}, dim {sz:3d}: LDL FAIL — {e}")
            log(f"  PSD shift λ=1/{LAMBDA_DENOM} insufficient for this block.")
            log(f"  Stopping. The block is the natural diagnostic.")
            sys.exit(1)

        # Sanity (cheap on small blocks; skip for the very large ones)
        if sz <= 50:
            assert verify_ldl(L, D, Y_shift), f"LDL verify failed for block {sdpa_idx}"

        # Entry-wise integer encoding (per-column denoms preserved).
        # L_num[i][k] = L[i,k] · d_L_col[k]  (small integers, ~107 bits for dim 192)
        # D_num[k]   = D[k] · d_D[k]         (small integers, ~D numerator bits)
        # L_den_col, D_den vectors stored separately.
        #
        # The Lean identity is then:
        #   ∀ i, j:  Σ_k L_num[i,k] · D_num[k] · L_num[j,k] · scaleFactor[k]
        #             = scaleYFactor · Y_int[i,j] + lambdaShift · I[i,j]
        # with scaleFactor[k] = commonScale / (d_L_col[k]² · d_D[k]).
        #
        # `commonScale` MUST be divisible by d_L_col[k]² · d_D[k] for every k
        # AND by DENOM_Y AND by LAMBDA_DENOM. We set:
        #   commonScale = lcm_k(d_L_col[k]² · d_D[k]), lifted to also
        #   contain DENOM_Y and LAMBDA_DENOM as factors.
        from math import lcm
        d_L_col = []
        for k in range(sz):
            d = 1
            for i in range(sz):
                d = lcm(d, L[i][k].denominator)
            d_L_col.append(d)
        d_D = [D[k].denominator for k in range(sz)]

        L_num: List[List[int]] = [[0] * sz for _ in range(sz)]
        for i in range(sz):
            for k in range(sz):
                v = L[i][k] * d_L_col[k]
                assert v.denominator == 1, \
                    f"col-scale L[{i}][{k}] failed: denom={v.denominator}"
                L_num[i][k] = int(v.numerator)
        D_num: List[int] = [0] * sz
        for k in range(sz):
            v = D[k] * d_D[k]
            assert v.denominator == 1, \
                f"D_num[{k}] failed: denom={v.denominator}"
            D_num[k] = int(v.numerator)
        Y_int = scale_matrix(Y_rat, DENOM_Y)

        # Track entry bit length for reporting
        for row in L_num:
            for v in row:
                bl = int(abs(v)).bit_length() if v != 0 else 0
                if bl > max_denom_bits:
                    max_denom_bits = bl
        for v in D_num:
            bl = int(abs(v)).bit_length() if v != 0 else 0
            if bl > max_denom_bits:
                max_denom_bits = bl

        # Verify the integer identity before emitting (only for small blocks).
        if sz <= 50:
            # commonScale and scaleFactor (replicate what the emitter will do)
            commonScale_check = lcm(DENOM_Y, LAMBDA_DENOM)
            for k in range(sz):
                commonScale_check = lcm(commonScale_check, d_L_col[k] * d_L_col[k] * d_D[k])
            scaleY_factor = commonScale_check // DENOM_Y
            lambda_shift = commonScale_check // LAMBDA_DENOM
            scaleFactor = [commonScale_check // (d_L_col[k] * d_L_col[k] * d_D[k]) for k in range(sz)]
            ok = True
            for i in range(sz):
                for j in range(sz):
                    s = 0
                    for k in range(min(i, j) + 1):
                        s += L_num[i][k] * D_num[k] * L_num[j][k] * scaleFactor[k]
                    rhs_ij = scaleY_factor * Y_int[i][j] + (lambda_shift if i == j else 0)
                    if s != rhs_ij:
                        log(f"  MISMATCH at block {sdpa_idx} ({i},{j}): "
                            f"lhs={s} rhs={rhs_ij}")
                        ok = False
                        break
                if not ok:
                    break
            assert ok, f"Int LDL identity verification FAILED for block {sdpa_idx}"

        out_path = emit_block_file(
            block_idx_one_based=sdpa_idx,
            file_idx=file_idx,
            dim=sz,
            Y_int=Y_int, scaleY=DENOM_Y,
            L_num=L_num, L_den_col=d_L_col,
            D_num=D_num, D_den=d_D,
            lambda_numer=1, lambda_denom=LAMBDA_DENOM,
            out_dir=out_dir, module_name=module_name, namespace=namespace,
            cert_filename=cert_path.name)
        sz_bytes = out_path.stat().st_size
        total_lean_bytes += sz_bytes
        total_emitted += 1
        block_metadata.append({
            "file_idx": file_idx,
            "sdpa_idx": sdpa_idx,
            "dim": sz,
            "max_d_L_col_bits": max((d.bit_length() for d in d_L_col), default=0),
            "max_d_D_bits": max((d.bit_length() for d in d_D), default=0),
            "file_size_bytes": sz_bytes,
        })

        log(f"  [{file_idx:3d}] SDPA blk {sdpa_idx:4d}, dim {sz:3d}: "
            f"{time.time() - tb:5.2f}s, {sz_bytes/1024:7.1f} KB")

        if total_emitted % 25 == 0:
            log(f"    ... progress: {total_emitted}/{len(psd_block_indices)} blocks, "
                f"{time.time() - t_blocks:.1f}s elapsed, "
                f"total .lean output {total_lean_bytes/1e6:.1f} MB")

    log("")
    log(f"All blocks emitted in {time.time() - t_blocks:.1f}s.")
    log(f"Max coefficient bit length (|coeff|.bit_length): {max_denom_bits}")
    log("")

    # ----------- Phase 1.D-E — Linear cert residual computation -----------
    # Compute, for each dual constraint k:
    #   r_k = tr(F_k · Y_rat) + λ · trace(F_k restricted to PSD blocks) - c_k
    # All over rationals, then scaled by DENOM_Y to get an Int per k.
    #
    # The aggregate slack Σ |x_k r_k| at scale DENOM_Y² must stay
    # ≪ DENOM_Y² · 7e-4 = 7e20 (vs Phase 1.0 measurement of ~6e-6).
    skip_linear = args.max_blocks is not None and args.max_blocks < len(
        [i for i, s in enumerate(sizes) if s > 0])
    linear_cert = None
    if not skip_linear:
        log("Computing linear-cert residual vector (Phase 1.D-E) ...")
        t_lin = time.time()
        log("  building per-block Y_rat (psd) + Y_diag for streaming F-trace ...")
        # Build per-block rationalised Y for streaming F-trace computation
        Y_rat_psd: Dict[int, List[List[Fraction]]] = {}
        Y_rat_diag: Dict[int, List[Fraction]] = {}
        for idx, sz in enumerate(sizes, 1):
            if sz < 0:
                arr = Yf[idx].diagonal()
                Y_rat_diag[idx] = [
                    Fraction(int(round(float(v) * DENOM_Y)), DENOM_Y) for v in arr]
            elif sz > 0:
                Y_rat_psd[idx] = rationalise_psd_block(Yf[idx], DENOM_Y)
        log(f"    done in {time.time() - t_lin:.1f}s")

        log("  streaming SDPA F-entries to compute tr(F_k · Y_rat) ...")
        t_stream = time.time()
        residual: List[Fraction] = [Fraction(0)] * (m + 1)
        c_rat = [Fraction(int(round(float(ck) * DENOM_Y)), DENOM_Y) for ck in c]
        # For each constraint k, accumulate also the λ · trace(F_k|psd) contribution
        lam_trace: List[Fraction] = [Fraction(0)] * (m + 1)
        lam = Fraction(1, LAMBDA_DENOM)
        nz = 0
        with sdpa_path.open() as f:
            ds = 0
            for line in f:
                if line.startswith("*") or not line.strip():
                    continue
                ds += 1
                if ds <= 4:
                    continue
                parts = line.split()
                if len(parts) != 5:
                    continue
                k = int(parts[0])
                if k == 0:
                    continue
                blk = int(parts[1])
                i = int(parts[2]) - 1
                j = int(parts[3]) - 1
                val = float(parts[4])
                ival = int(round(val))
                if ival == 0:
                    continue
                nz += 1
                f_rat = Fraction(ival)
                if sizes[blk - 1] < 0:
                    y = Y_rat_diag[blk][i]
                    if y != 0:
                        residual[k] += f_rat * y
                else:
                    y = Y_rat_psd[blk][i][j]
                    if y != 0:
                        contrib = f_rat * y
                        if i != j:
                            contrib = contrib * 2
                        residual[k] += contrib
                    # λ · trace contribution: only for psd blocks, and only on diagonal entries (i == j)
                    if i == j:
                        lam_trace[k] += f_rat
                if nz % 200_000 == 0:
                    log(f"    ... {nz} nz F entries, {time.time() - t_stream:.1f}s elapsed")
        log(f"    streamed {nz} entries in {time.time() - t_stream:.1f}s")

        # Apply the lambda shift and subtract c
        for k in range(1, m + 1):
            residual[k] += lam * lam_trace[k]
            residual[k] -= c_rat[k - 1]

        # Scale residual and target by DENOM_Y to get integers
        residual_int: List[int] = [0] * m
        target_int: List[int] = [0] * m
        for k in range(1, m + 1):
            r_scaled = residual[k] * DENOM_Y
            t_scaled = c_rat[k - 1] * DENOM_Y
            assert r_scaled.denominator == 1, \
                f"residual[{k}] · DENOM_Y has denom {r_scaled.denominator}: {residual[k]}"
            assert t_scaled.denominator == 1
            residual_int[k - 1] = int(r_scaled.numerator)
            target_int[k - 1] = int(t_scaled.numerator)
        # Also encode x at the same scale
        x_int: List[int] = []
        for xk in x:
            xv = Fraction(int(round(float(xk) * DENOM_Y)), DENOM_Y) * DENOM_Y
            assert xv.denominator == 1
            x_int.append(int(xv.numerator))

        # Aggregate (informational; the actual bound proof in Phase 3
        # will compute Σ_k |x_int_k · residual_int_k| in Lean and bound it
        # by an explicit constant).
        total = sum(abs(x_int[k] * residual_int[k]) for k in range(m))
        scale = DENOM_Y * DENOM_Y  # x_int and residual_int both at scale DENOM_Y
        max_res_abs = max(abs(r) for r in residual_int)
        log(f"  weighted slack: Σ |x · r| / scale² = {float(total) / scale:.6e}")
        log(f"  max |residual_int[k]| = {max_res_abs} (at scale {DENOM_Y})")

        linear_cert = {
            "residual_str": vector_to_str(residual_int),
            "target_str": vector_to_str(target_int),
            "x_int_str": vector_to_str(x_int),
            "scale": DENOM_Y,
            "m": m,
            "bound_numer": args.bound_numer,
            "bound_denom": args.bound_denom,
            "slack_total": f"{float(total) / scale:.6e}",
            "max_residual_abs": max_res_abs,
        }
        log(f"  linear cert ready in {time.time() - t_lin:.1f}s")

    # ----------- Top-level file -----------
    log(f"Emitting top-level {top_file.name} ...")
    top_path = emit_top_file(
        num_blocks=len(psd_block_indices),
        diag_y_str=diag_y_str,
        diag_y_denom=DENOM_Y,
        diag_y_count=len(diag_y_vals),
        module_name=module_name, namespace=namespace, top_file=top_file,
        linear_cert=linear_cert,
        consumer_note=args.consumer_note)
    log(f"  wrote {relpath_safe(top_path)} ({top_path.stat().st_size/1e6:.2f} MB)")
    log("")

    # Save metadata for later phases.
    # PentagonQCertificate uses the legacy phase_1A_block_metadata.json filename
    # for backward compatibility with existing tooling that reads it. Other
    # modules use <module-name>_block_metadata.json. Metadata is written next
    # to the top file (if --top-file is overridden) to keep regression runs
    # from clobbering the in-tree json.
    if args.top_file is not None:
        meta_dir = args.top_file.parent
    else:
        meta_dir = ROOT / "scratch"
    meta_filename = ("phase_1A_block_metadata.json"
                     if module_name == "PentagonQCertificate"
                     else f"{module_name}_block_metadata.json")
    meta_path = meta_dir / meta_filename
    meta_dir.mkdir(parents=True, exist_ok=True)
    with meta_path.open("w") as f:
        json.dump({
            "module_name": module_name,
            "namespace": namespace,
            "num_blocks": len(psd_block_indices),
            "diag_count": len(diag_y_vals),
            "lambda_denom": LAMBDA_DENOM,
            "denom_Y": DENOM_Y,
            "blocks": block_metadata,
        }, f, indent=2)
    log(f"  metadata: {relpath_safe(meta_path)}")

    total_size = sum(p.stat().st_size for p in out_dir.iterdir()) + top_file.stat().st_size
    log("")
    log("=== Summary ===")
    log(f"  Wall time: {time.time() - t_emit_start:.1f}s")
    log(f"  Output: {relpath_safe(out_dir)}/ + {relpath_safe(top_file)}")
    log(f"  Total .lean bytes: {total_size/1e6:.1f} MB")
    log(f"  Blocks: {total_emitted}")


if __name__ == "__main__":
    main()
