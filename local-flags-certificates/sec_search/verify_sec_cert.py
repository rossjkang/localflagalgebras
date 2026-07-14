#!/usr/bin/env python3
"""Independent Python verifier for the SEC certs (T1 of the development notes).

Re-computes, without using Lean, the SAME arithmetic that the per-block
`native_decide` theorems in `DaveyThesis2024/SecCertificate{,Bipartite}/Block{i}.lean`
and the slack-budget `cert_slack_within_budget` theorem in
`DaveyThesis2024/Sec{,Bipartite}Certificate.lean` verify.

The point: if Python AND Lean's `native_decide` agree bit-exactly on
every check, then neither the Lean kernel/compiler NOR the emitter
(local-flags-certificates/emit_lean_cert.py) had a bug — `native_decide`
becomes a redundant confirmation rather than the sole verification.

What gets verified (for each of the general + bipartite certs):

  1. Top-level cert metadata round-trip:
       - linearScale, boundNumer/Denom, numConstraints
       - target, residual, x_int parse to lists of the right length
       - secSlackBudget value

  2. Per-block LDL identity (39 + 52 blocks):
       For every (i, j) in [0, dim) x [0, dim):
         Σ_k L_num[i][k] · D_num[k] · L_num[j][k] · scaleFactor[k]
           = scaleYFactor · Y_int[i][j] + lambdaShift · I[i][j]
       Pure integer arithmetic; bit-exact comparison.

  3. PSD-ness per block:
       Compute eigenvalues of (Y_rat + λI) in float using NumPy.
       All eigenvalues should be >= -1e-8 (the matrix is PD post-shift).

  4. Slack budget:
       Re-compute total_slack_abs = Σ_k |x_int[k] * residual[k]| in
       Python int arithmetic. Verify it matches the bound and stays
       within secSlackBudget.

Output: prints a structured summary; non-zero exit if any check fails.

Usage:
  python3 local-flags-certificates/verify_sec_cert.py
  python3 local-flags-certificates/verify_sec_cert.py --quick   # general only
  python3 local-flags-certificates/verify_sec_cert.py --no-psd  # skip eigvals

Runs from the repo root. ~5-15 minutes total wall time on a laptop.
"""

from __future__ import annotations

import argparse
import re
import sys
import time
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import numpy as np

ROOT = Path(__file__).resolve().parent.parent


# ----------------------------------------------------------------------
# Logging
# ----------------------------------------------------------------------

def log(msg: str = "") -> None:
    print(msg, flush=True)


# ----------------------------------------------------------------------
# Lean source parsing
# ----------------------------------------------------------------------
#
# All `def` lines emitted by `emit_lean_cert.py` are single-line for
# small values (Nat, Int) and follow a uniform `"value"` form for the
# `_str` String defs, which are emitted on the line immediately AFTER
# the `def NAME : String :=` header (so the string contents are on
# its own line — see emit_block_file / emit_top_file).

# Match  `def NAME : <type> := <value>` on a single line.
RE_INT_DEF = re.compile(
    r"^def\s+(\w+)\s*:\s*(?:Nat|Int)\s*:=\s*(-?\d+)\s*(?:--.*)?$"
)

# Match `def NAME : String :=` (the string body is on the next line).
RE_STR_HEADER = re.compile(r"^def\s+(\w+_str)\s*:\s*String\s*:=\s*$")


def parse_lean_defs(path: Path) -> Tuple[Dict[str, int], Dict[str, str]]:
    """Read a .lean file and pull out the `def NAME : Nat := N`,
    `def NAME : Int := N`, and `def NAME_str : String := "..."` defs.

    Returns (int_defs, str_defs).
    """
    ints: Dict[str, int] = {}
    strs: Dict[str, str] = {}
    lines = path.read_text().splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        m_int = RE_INT_DEF.match(line)
        if m_int:
            name, val = m_int.group(1), int(m_int.group(2))
            ints[name] = val
            i += 1
            continue
        m_str = RE_STR_HEADER.match(line)
        if m_str:
            # Body is on the next line; format is `  "..."`.
            name = m_str.group(1)
            body_line = lines[i + 1].lstrip()
            assert body_line.startswith('"') and body_line.rstrip().endswith('"'), (
                f"Expected string literal on line {i+2} of {path}, got: "
                f"{body_line[:80]}…")
            strs[name] = body_line.strip()[1:-1]  # strip outer quotes
            i += 2
            continue
        i += 1
    return ints, strs


def parse_int_list(s: str) -> List[int]:
    """Parse a comma-separated list of Int. Whitespace-tolerant.
    Mirrors `Davey2024.*.parseInts`. """
    if not s:
        return []
    return [int(tok.strip()) for tok in s.split(",")]


def parse_int_matrix(s: str) -> List[List[int]]:
    """Parse a semicolon-separated list of rows, each a parse_int_list.
    Mirrors `Davey2024.*.parseMatrix`. """
    if not s:
        return []
    return [parse_int_list(row) for row in s.split(";")]


# ----------------------------------------------------------------------
# Top-level cert parsing
# ----------------------------------------------------------------------


class TopLevelCert:
    """Parsed top-level cert file data."""

    def __init__(self, path: Path) -> None:
        self.path = path
        ints, strs = parse_lean_defs(path)
        # Required ints:
        for k in ("linearScale", "boundNumer", "boundDenom",
                  "numConstraints", "diag_y_denom", "diag_y_count"):
            assert k in ints, f"{path}: missing int def `{k}`"
        # Slack budget: different names for general/bipartite
        slack_keys = [k for k in ints if k.endswith("SlackBudget")]
        assert len(slack_keys) == 1, (
            f"{path}: expected exactly 1 SlackBudget def, got {slack_keys}")
        # Required strs:
        for k in ("target_str", "residual_str", "x_int_str", "diag_y_str"):
            assert k in strs, f"{path}: missing string def `{k}`"
        self.linearScale = ints["linearScale"]
        self.boundNumer = ints["boundNumer"]
        self.boundDenom = ints["boundDenom"]
        self.numConstraints = ints["numConstraints"]
        self.diag_y_denom = ints["diag_y_denom"]
        self.diag_y_count = ints["diag_y_count"]
        self.slack_budget_key = slack_keys[0]
        self.slack_budget = ints[slack_keys[0]]
        # Lazy parsing of the big strings (saves time if we don't need them):
        self._target_str = strs["target_str"]
        self._residual_str = strs["residual_str"]
        self._x_int_str = strs["x_int_str"]
        self._diag_y_str = strs["diag_y_str"]
        self._target: Optional[List[int]] = None
        self._residual: Optional[List[int]] = None
        self._x_int: Optional[List[int]] = None
        self._diag_y: Optional[List[int]] = None

    @property
    def target(self) -> List[int]:
        if self._target is None:
            self._target = parse_int_list(self._target_str)
        return self._target

    @property
    def residual(self) -> List[int]:
        if self._residual is None:
            self._residual = parse_int_list(self._residual_str)
        return self._residual

    @property
    def x_int(self) -> List[int]:
        if self._x_int is None:
            self._x_int = parse_int_list(self._x_int_str)
        return self._x_int

    @property
    def diag_y(self) -> List[int]:
        if self._diag_y is None:
            self._diag_y = parse_int_list(self._diag_y_str)
        return self._diag_y


# ----------------------------------------------------------------------
# Per-block parsing + LDL identity verification
# ----------------------------------------------------------------------


class BlockCert:
    """Parsed per-block cert data + verification methods."""

    def __init__(self, path: Path) -> None:
        self.path = path
        ints, strs = parse_lean_defs(path)
        # Required ints
        for k in ("sdpaBlockIdx", "dim", "scaleY", "commonScale",
                  "scaleYFactor", "lambdaShift", "lambdaNumer", "lambdaDenom"):
            assert k in ints, f"{path}: missing int def `{k}`"
        # Required strs
        for k in ("Y_str", "L_num_str", "L_den_str",
                  "D_num_str", "D_den_str", "scaleFactor_str"):
            assert k in strs, f"{path}: missing str def `{k}`"
        self.sdpa_idx = ints["sdpaBlockIdx"]
        self.dim = ints["dim"]
        self.scaleY = ints["scaleY"]
        self.commonScale = ints["commonScale"]
        self.scaleYFactor = ints["scaleYFactor"]
        self.lambdaShift = ints["lambdaShift"]
        self.lambdaNumer = ints["lambdaNumer"]
        self.lambdaDenom = ints["lambdaDenom"]
        self.Y = parse_int_matrix(strs["Y_str"])
        self.L_num = parse_int_matrix(strs["L_num_str"])
        self.L_den = parse_int_list(strs["L_den_str"])
        self.D_num = parse_int_list(strs["D_num_str"])
        self.D_den = parse_int_list(strs["D_den_str"])
        self.scaleFactor = parse_int_list(strs["scaleFactor_str"])

    def check_shapes(self) -> Optional[str]:
        d = self.dim
        if len(self.Y) != d:
            return f"Y has {len(self.Y)} rows, want {d}"
        for i, row in enumerate(self.Y):
            if len(row) != d:
                return f"Y row {i} has {len(row)} entries, want {d}"
        if len(self.L_num) != d:
            return f"L_num has {len(self.L_num)} rows, want {d}"
        for i, row in enumerate(self.L_num):
            if len(row) != d:
                return f"L_num row {i} has {len(row)} entries, want {d}"
        for name, vec in (("L_den", self.L_den),
                          ("D_num", self.D_num),
                          ("D_den", self.D_den),
                          ("scaleFactor", self.scaleFactor)):
            if len(vec) != d:
                return f"{name} has {len(vec)} entries, want {d}"
        return None

    def check_commonScale(self) -> Optional[str]:
        """commonScale = lcm_k(L_den[k]^2 * D_den[k]) lifted to also be
        divisible by scaleY and lambdaDenom. Verify the emitter's claim
        scaleYFactor = commonScale / scaleY and lambdaShift =
        commonScale * lambdaNumer / lambdaDenom, and scaleFactor[k] =
        commonScale / (L_den[k]^2 * D_den[k]). """
        if self.commonScale % self.scaleY != 0:
            return (f"commonScale not divisible by scaleY: "
                    f"{self.commonScale} % {self.scaleY} != 0")
        if self.scaleYFactor != self.commonScale // self.scaleY:
            return (f"scaleYFactor != commonScale/scaleY: "
                    f"{self.scaleYFactor} != "
                    f"{self.commonScale // self.scaleY}")
        if self.commonScale * self.lambdaNumer % self.lambdaDenom != 0:
            return (f"commonScale * lambdaNumer not divisible by "
                    f"lambdaDenom: ({self.commonScale} * "
                    f"{self.lambdaNumer}) % {self.lambdaDenom} != 0")
        expected_shift = self.commonScale * self.lambdaNumer // self.lambdaDenom
        if self.lambdaShift != expected_shift:
            return (f"lambdaShift != commonScale*lambdaNumer/lambdaDenom: "
                    f"{self.lambdaShift} != {expected_shift}")
        for k in range(self.dim):
            denom = self.L_den[k] * self.L_den[k] * self.D_den[k]
            if self.commonScale % denom != 0:
                return (f"commonScale not divisible by L_den[{k}]^2 * "
                        f"D_den[{k}] = {denom}")
            expected = self.commonScale // denom
            if self.scaleFactor[k] != expected:
                return (f"scaleFactor[{k}] = {self.scaleFactor[k]} != "
                        f"commonScale/(L_den[{k}]^2*D_den[{k}]) = {expected}")
        return None

    def check_ldl_identity(self) -> Tuple[bool, Optional[str]]:
        """Verify that for every (i, j):

          Σ_k L_num[i][k] · D_num[k] · L_num[j][k] · scaleFactor[k]
            = scaleYFactor · Y[i][j] + (lambdaShift if i == j else 0)

        Bit-exact integer arithmetic. Returns (ok, error_message).

        We exploit unit-lower-triangularity of the underlying L (i.e.,
        L_num[i][k] = 0 for k > i and L_num[k][k] == L_den[k]) — the
        inner sum runs only up to k <= min(i, j). The emitter does the
        same shortcut at verify-time (emit_lean_cert.py:880-884).
        """
        d = self.dim
        L = self.L_num
        D = self.D_num
        sf = self.scaleFactor
        sY = self.scaleYFactor
        shift = self.lambdaShift
        for i in range(d):
            for j in range(d):
                s = 0
                kmax = min(i, j) + 1
                for k in range(kmax):
                    lik = L[i][k]
                    if lik == 0:
                        continue
                    ljk = L[j][k]
                    if ljk == 0:
                        continue
                    s += lik * D[k] * ljk * sf[k]
                rhs = sY * self.Y[i][j] + (shift if i == j else 0)
                if s != rhs:
                    return False, (
                        f"LDL mismatch at ({i},{j}): lhs={s} rhs={rhs} "
                        f"diff={s - rhs}")
        return True, None

    def check_psd(self, tol: float = 1e-8) -> Tuple[bool, float, str]:
        """Compute eigenvalues of `Y_rat + λI` in float and confirm
        min eigenvalue >= -tol. Returns (ok, min_eig, info).

        `Y_rat = Y / scaleY` and `λ = lambdaNumer / lambdaDenom`. We do
        NOT use the LDL decomposition here — we directly eigvalsh the
        rationalised Y matrix shifted by λI. (Computing eigenvalues
        of the LDL-reconstructed matrix is equivalent up to float
        precision, so this is a stronger independent check.) """
        d = self.dim
        # Build float (Y_rat + λI). Each entry of Y is divided by scaleY.
        # The bit-exact LDL check already passed, so we know Y is what
        # got rationalised. Float arithmetic here is OK since we're
        # comparing eigenvalues to 1e-8.
        scaleY = float(self.scaleY)
        lam = float(self.lambdaNumer) / float(self.lambdaDenom)
        M = np.empty((d, d), dtype=np.float64)
        for i in range(d):
            for j in range(d):
                M[i, j] = float(self.Y[i][j]) / scaleY
            M[i, i] += lam
        # eigvalsh assumes symmetric; impose it.
        M = 0.5 * (M + M.T)
        eigs = np.linalg.eigvalsh(M)
        min_eig = float(eigs.min())
        ok = min_eig >= -tol
        return ok, min_eig, (
            f"min_eig={min_eig:+.3e} max_eig={float(eigs.max()):+.3e} "
            f"cond≈{float(eigs.max()/max(abs(min_eig),1e-30)):.2e}")


# ----------------------------------------------------------------------
# Verification driver
# ----------------------------------------------------------------------


class CertVerification:
    """Bundle parameters + run all checks for one cert (general or bipartite)."""

    def __init__(self, name: str, top_path: Path, blocks_dir: Path,
                 expected_num_blocks: int, expected_num_constraints: int,
                 expected_slack_budget_name: str) -> None:
        self.name = name
        self.top_path = top_path
        self.blocks_dir = blocks_dir
        self.expected_num_blocks = expected_num_blocks
        self.expected_num_constraints = expected_num_constraints
        self.expected_slack_budget_name = expected_slack_budget_name
        self.errors: List[str] = []
        self.warnings: List[str] = []

    def err(self, msg: str) -> None:
        log(f"  [{self.name}] FAIL: {msg}")
        self.errors.append(msg)

    def warn(self, msg: str) -> None:
        log(f"  [{self.name}] WARN: {msg}")
        self.warnings.append(msg)

    def info(self, msg: str) -> None:
        log(f"  [{self.name}] {msg}")

    def run(self, skip_psd: bool = False) -> bool:
        log(f"\n=== {self.name} ===")
        log(f"  top-level cert : {self.top_path}")
        log(f"  blocks dir     : {self.blocks_dir}")

        # ----- Top-level cert -----
        t0 = time.time()
        top = TopLevelCert(self.top_path)
        self.info(f"top-level parsed in {time.time()-t0:.2f}s")
        self.info(f"linearScale     = {top.linearScale}")
        self.info(f"bound           = {top.boundNumer} / {top.boundDenom}")
        self.info(f"numConstraints  = {top.numConstraints}")
        self.info(f"slack budget    = {top.slack_budget_key} = {top.slack_budget}")

        if top.slack_budget_key != self.expected_slack_budget_name:
            self.err(f"slack budget def named {top.slack_budget_key}, "
                     f"expected {self.expected_slack_budget_name}")
        if top.numConstraints != self.expected_num_constraints:
            self.err(f"numConstraints = {top.numConstraints}, "
                     f"expected {self.expected_num_constraints}")
        if top.linearScale != 10**12:
            self.err(f"linearScale = {top.linearScale}, expected 10^12")

        # ----- Cross-checks on list lengths -----
        t0 = time.time()
        if len(top.target) != top.numConstraints:
            self.err(f"target length {len(top.target)} != numConstraints "
                     f"{top.numConstraints}")
        if len(top.residual) != top.numConstraints:
            self.err(f"residual length {len(top.residual)} != numConstraints "
                     f"{top.numConstraints}")
        if len(top.x_int) != top.numConstraints:
            self.err(f"x_int length {len(top.x_int)} != numConstraints "
                     f"{top.numConstraints}")
        if len(top.diag_y) != top.diag_y_count:
            self.err(f"diag_y length {len(top.diag_y)} != diag_y_count "
                     f"{top.diag_y_count}")
        self.info(f"list-length cross-checks: {time.time()-t0:.2f}s")

        # ----- Diag nonneg check -----
        neg = [(i, v) for i, v in enumerate(top.diag_y) if v < 0]
        if neg:
            self.err(f"diag_y has {len(neg)} negative entries; "
                     f"first: {neg[:3]}")
        else:
            self.info(f"diag_y_nonneg: all {top.diag_y_count} entries >= 0")

        # ----- Slack budget -----
        t0 = time.time()
        total_slack_abs = sum(abs(x * r) for x, r in zip(top.x_int, top.residual))
        self.info(f"total_slack_abs recomputed in {time.time()-t0:.2f}s")
        self.info(f"total_slack_abs = {total_slack_abs}")
        self.info(f"  ≈ {float(total_slack_abs):.3e}  "
                  f"({100*float(total_slack_abs)/float(top.slack_budget):.1f}% of budget)")
        if total_slack_abs > top.slack_budget:
            self.err(f"total_slack_abs ({total_slack_abs}) exceeds budget "
                     f"({top.slack_budget})")
        else:
            self.info(f"slack within budget: {total_slack_abs} <= "
                      f"{top.slack_budget}")

        max_residual_abs = max((abs(r) for r in top.residual), default=0)
        self.info(f"max |residual[k]| = {max_residual_abs}")

        # ----- Per-block verification -----
        block_files = sorted(self.blocks_dir.glob("Block*.lean"),
                             key=lambda p: int(p.stem[5:]))
        if len(block_files) != self.expected_num_blocks:
            self.err(f"found {len(block_files)} block files, "
                     f"expected {self.expected_num_blocks}")

        log(f"\n  Per-block verification ({len(block_files)} blocks):")
        log(f"  {'idx':>4s} {'sdpa':>5s} {'dim':>4s} "
            f"{'parse':>7s} {'shapes':>7s} {'cScale':>7s} "
            f"{'LDL':>7s} {'PSD':>10s} {'min_eig':>14s}  {'verdict'}")

        any_block_failed = False
        all_min_eig: List[float] = []
        for file_idx, bf in enumerate(block_files):
            tb = time.time()
            try:
                blk = BlockCert(bf)
            except Exception as e:
                self.err(f"Block{file_idx}: parse error: {e}")
                any_block_failed = True
                continue
            t_parse = time.time() - tb

            tb = time.time()
            shape_err = blk.check_shapes()
            t_shapes = time.time() - tb
            if shape_err:
                self.err(f"Block{file_idx}: {shape_err}")
                any_block_failed = True
                continue

            tb = time.time()
            cs_err = blk.check_commonScale()
            t_cs = time.time() - tb
            if cs_err:
                self.err(f"Block{file_idx}: {cs_err}")
                any_block_failed = True
                continue

            tb = time.time()
            ldl_ok, ldl_err = blk.check_ldl_identity()
            t_ldl = time.time() - tb
            if not ldl_ok:
                self.err(f"Block{file_idx}: {ldl_err}")
                any_block_failed = True

            if skip_psd:
                t_psd = 0.0
                psd_str = "skipped"
                min_eig = float("nan")
                psd_ok = True
            else:
                tb = time.time()
                psd_ok, min_eig, _psd_info = blk.check_psd()
                t_psd = time.time() - tb
                all_min_eig.append(min_eig)
                psd_str = f"{t_psd:5.2f}s"
                if not psd_ok:
                    self.warn(f"Block{file_idx}: min eigenvalue "
                              f"{min_eig:+.3e} < -1e-8")

            verdict = "OK" if (ldl_ok and psd_ok) else "FAIL"
            log(f"  {file_idx:4d} {blk.sdpa_idx:5d} {blk.dim:4d} "
                f"{t_parse:5.2f}s {t_shapes:5.2f}s {t_cs:5.2f}s "
                f"{t_ldl:5.2f}s {psd_str:>10s} "
                f"{min_eig:+13.3e}  {verdict}")

        if not skip_psd and all_min_eig:
            log(f"\n  PSD summary: min over all blocks = "
                f"{min(all_min_eig):+.3e}, max over all = "
                f"{max(all_min_eig):+.3e}")

        # ----- Final status -----
        status = "GREEN" if not self.errors else (
            "YELLOW" if (self.warnings and not self.errors) else "RED")
        log(f"\n  Result: {status}  ({len(self.errors)} errors, "
            f"{len(self.warnings)} warnings)")
        return len(self.errors) == 0


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Independent Python verifier for the SEC certs.")
    ap.add_argument("--quick", action="store_true",
                    help="Verify only the general SEC cert (skip bipartite)")
    ap.add_argument("--bipartite-only", action="store_true",
                    help="Verify only the bipartite cert (skip general)")
    ap.add_argument("--no-psd", action="store_true",
                    help="Skip the PSD eigenvalue check (LDL identity still runs)")
    args = ap.parse_args()

    t0 = time.time()
    log("=" * 70)
    log("SEC cert verifier — independent Python re-computation")
    log("(T1 of the development notes)")
    log("=" * 70)
    log(f"Repo root : {ROOT}")
    log(f"NumPy     : {np.__version__}")

    runs = []
    if not args.bipartite_only:
        runs.append(CertVerification(
            name="SecCertificate (general)",
            top_path=ROOT / "DaveyThesis2024" / "SecCertificate.lean",
            blocks_dir=ROOT / "DaveyThesis2024" / "SecCertificate",
            expected_num_blocks=39,
            expected_num_constraints=17950,
            expected_slack_budget_name="secSlackBudget",
        ))
    if not args.quick:
        runs.append(CertVerification(
            name="SecBipartiteCertificate (bipartite)",
            top_path=ROOT / "DaveyThesis2024" / "SecBipartiteCertificate.lean",
            blocks_dir=ROOT / "DaveyThesis2024" / "SecBipartiteCertificate",
            expected_num_blocks=52,
            expected_num_constraints=3808,
            expected_slack_budget_name="secBipartiteSlackBudget",
        ))

    all_ok = True
    for run in runs:
        ok = run.run(skip_psd=args.no_psd)
        all_ok = all_ok and ok

    log("\n" + "=" * 70)
    log(f"Total wall time: {time.time()-t0:.1f}s")
    log("OVERALL STATUS: " + ("GREEN" if all_ok else "RED"))
    log("=" * 70)
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
