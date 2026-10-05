#!/usr/bin/env python3
"""Check the rational multiplier certificate. Standard library only.

Verifies, in exact rational arithmetic, that the published multipliers really
do certify

    sum_k r_k^+ y_k  <=  T        for EVERY feasible y

and that the resulting safe value clears the paper's target -- which is the
step Section 6 of the paper rests on.  Seven checks:

  1. The .sdpa and the .cert are the paper's size-8 pentagon problem and the
     archived solution: both sha256 are constants of this script, not fields
     read from the certificate under test.  The .cert matters as much as the
     .sdpa, because the positive semidefiniteness of X is the link left to
     the archived verifier run and that run factorised this X.  The
     certificate must also name the rationalisation exponents this script
     recomputes at.

     Checks 2 and 7 are therefore lemmas about a fixed pair of files rather
     than defences against an adversary: with the pins in place they have one
     possible outcome.  They earn their keep by not depending on the pins --
     m, nblocks, the block sizes and the objective are pinned separately, so
     the structural checks stand on a frame that does not come out of the
     file they are checking.
  2. y >= 0 -- block 1 really is the -m coordinate-nonnegativity block: each
     k in 1..m appears exactly once, as a unit diagonal entry, and block 1
     carries nothing else.  Checks 3-5 prove nothing without this: the
     passage from column domination to the weighted bound uses y_k >= 0.
  3. mu >= 0.
  4. sum_rows mu[row] * a[row,k] <= -weights[k] for every column k.
  5. T = -mu . f0, with f0 recomputed FROM THE .sdpa (reading it from the
     JSON would make the identity self-referential).
  6. The weights really are r^+, and the safe value clears the target:
     r and tr(F_0 X) are recomputed from the .sdpa and the .cert at the
     archived rationalisation, the published weights_positive must match
     exactly, and V = -tr(F_0 X) + T must be <= TARGET, which is this
     script's own constant and is NOT read from the certificate.
  7. The .sdpa parses cleanly: every entry line carries exactly five tokens
     and an integer F value, names a block and a coordinate that exist, sits
     in the upper triangle (on the diagonal, for a diagonal block), and is
     not a duplicate.  Each of those has a way of hiding a bound-breaking
     F_0 entry or manufacturing a linear row that is not in the program.
     The .cert parses cleanly too: five tokens per entry line after the
     leading y-vector line, coordinates inside their block, finite values,
     no duplicates; an appended token would otherwise drop the line and
     zero that entry of X.

What this does NOT do: verify X >= 0 -- the 278 exact rational LDL^T block
factorisations, which are the dominant cost of the pipeline and need the full
verifier run.  That is the one link in the chain this script leaves open, and
the safe value does depend on it.  Beyond the SDP, the step to a statement
about graphs (raw scale, divisor, and the flag-to-graph bridge) is the
paper's, not this script's.

Needs Python 3.8 or later; on 3.11 and later an absurdly long integer literal
in the .sdpa is rejected by the interpreter rather than parsed.

    python3 check_multipliers.py bounded_pentagon_alt.sdpa \
                                 bounded_pentagon_alt.cert \
                                 bounded_pentagon_alt.multipliers.json

Every failure path returns a nonzero exit code, and the parser raises rather
than asserts, so `python3 -O` cannot weaken any of the seven checks.
"""
from __future__ import annotations
import hashlib, json, sys
from fractions import Fraction as F
from pathlib import Path

class ParseError(ValueError):
    """A defect in the .sdpa or the .cert, i.e. a check-7 failure.

    Distinguished from a plain ValueError so that a fault in the certificate
    JSON is not reported against the .sdpa, and so that an unrelated
    ValueError regression is not swallowed under a check-7 label.
    """


# The archived run's rationalisation: --denom-exp 16 --lambda-exp 16.  The
# certificate records the exponents it was built at, and check 1 requires
# them to be these, so a certificate rationalised differently is rejected
# rather than silently recomputed against the wrong X.
DENOM_EXP = LAMBDA_EXP = 16
DEN, LAM = 10**DENOM_EXP, F(1, 10**LAMBDA_EXP)
# The paper's constant, held here so that it is never read from the
# certificate under test: phi(O_Q) <= 2073/5000 = 0.4146.
TARGET = F(2073, 5000)
# Likewise the problem itself.  Without this the checker binds a certificate
# to its own inputs but neither to the paper: hand it the C6 problem with a
# certificate built for that problem and it would certify the wrong theorem
# against the pentagon's target.  splice_pentagon_sdpa.py and
# extract_multipliers.py already pin this hash; so does the provenance record.
SDPA_SHA256 = "b46467ab2d34b672c122f4ebbd372d75aff808f63b336c873b56859ca24ca6ad"
# The .cert is pinned for the same reason and one more: X >= 0 is the link this
# script leaves to the archived verifier run, and that run factorised THIS
# matrix.  Read the hash from the certificate under test instead and a one-line
# edit to the .cert gives an X that is not PSD, passes every check, and prints
# the published headline verbatim.
CERT_SHA256 = "650958f2b69d0800dab31b32de8803013c88d274b8d465d14ec24d1ddfb7e6fe"
# The header too, separately, so that the structural checks have a frame that
# does not come out of the file they are checking.  Every coordinate in check 7
# is validated against m, nblocks and the block sizes -- all read from the
# .sdpa -- so without this, editing the block-structure line moves the frame
# and manufactures a linear row that check 7 then blesses.  The objective is
# pinned for a related reason: it enters r_k, but the block-1 repair absorbs a
# change to it, so the whole objective can be replaced without moving a single
# printed digit.  (Whitespace-normalised, so respacing is not a failure -- but
# only respacing: `-09295` for `-9295`, or `+5` for `5`, is a different digest.)
M, NBLOCKS = 9295, 9392
SIZES_SHA256 = "426589588e7c303aa1c798a7c5db9d335f8b7628318e4e0857bc611b05c2740d"
C_SHA256 = "7af85e1732e62be37093ca48fece59e7c355e187e9ea7ca254ae3e79a139b464"


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def as_parse_errors(path):
    """Re-raise anything the parsers throw as a ParseError.

    int(), Fraction() and float() raise bare ValueError, so without this a
    malformed token in the .sdpa or the .cert is reported under the label
    reserved for faults in the certificate JSON -- pointing a reader at the
    wrong file.  OverflowError is caught too: float() accepts `inf`.
    """
    class _Ctx:
        def __enter__(self): return self
        def __exit__(self, exc_type, exc, tb):
            if exc_type is None or issubclass(exc_type, ParseError):
                return False
            if issubclass(exc_type, (ValueError, OverflowError, IndexError)):
                raise ParseError(f"{path}: {exc}") from exc
            return False
    return _Ctx()


def parse_sdpa(path: Path):
    """m, block sizes, objective c, and the integer F entries.

    Strict on purpose (check 7).  A reader that drops a malformed entry line
    in silence will accept a problem whose true safe value breaks the target:
    append one extra token to a bound-breaking `F_0` line and the line
    vanishes, while a conforming SDPA reader still reads the entry.
    """
    ds, m, nblocks, sizes, c, entries = 0, None, None, [], [], []
    seen = set()
    digest = lambda line: hashlib.sha256(" ".join(line.split()).encode()).hexdigest()
    with as_parse_errors(path), path.open(encoding="utf-8") as f:
        for lineno, line in enumerate(f, 1):
            # SDPA admits both `*` and `"` as comment markers
            # `*` only.  The archived verifier drops a `"` line in the entry
            # section as a short entry, but one *before* the four header lines
            # shifts its data-line count and corrupts the header, so accepting
            # `"` here would let such a file through.
            if line.startswith("*") or not line.strip():
                continue
            ds += 1
            if ds == 1:
                m = int(line.split()[0])
                if m != M:
                    raise ParseError(f"{path}:{lineno}: m is {m}, expected {M}")
            elif ds == 2:
                nblocks = int(line.split()[0])
                if nblocks != NBLOCKS:
                    raise ParseError(f"{path}:{lineno}: nblocks is {nblocks}, "
                                     f"expected {NBLOCKS}")
            elif ds == 3:
                if digest(line) != SIZES_SHA256:
                    raise ParseError(f"{path}:{lineno}: the block-structure "
                                     f"line is not the pentagon program's; it "
                                     f"is the frame every coordinate below is "
                                     f"checked against")
                sizes = [int(v) for v in line.split()]
            elif ds == 4:
                if digest(line) != C_SHA256:
                    raise ParseError(f"{path}:{lineno}: the objective vector "
                                     f"is not the pentagon program's")
                c = [F(v) for v in line.split()]
                # the header is complete here, and the entry loop below
                # indexes `sizes`, so check it once, now
                if len(sizes) != nblocks or len(c) != m:
                    raise ParseError(
                        f"{path}: header says {nblocks} blocks and m={m}, "
                        f"found {len(sizes)} sizes and {len(c)} objective "
                        f"coefficients")
            else:
                p = line.split()
                if len(p) != 5:
                    raise ParseError(
                        f"{path}:{lineno}: entry line has {len(p)} tokens, "
                        f"expected 5: {line.strip()!r}")
                v = F(p[4])
                if v.denominator != 1:
                    raise ParseError(f"{path}:{lineno}: non-integer F entry {p}")
                k, blk, i, j = int(p[0]), int(p[1]), int(p[2]) - 1, int(p[3]) - 1
                # Indices must name a coordinate that exists.  Without this an
                # added line naming a coordinate outside a diagonal block's
                # declared size manufactures a linear row that is not in the
                # program, and a multiplier placed on it certifies anything.
                if not 0 <= k <= m:
                    raise ParseError(f"{path}:{lineno}: matrix index {k} "
                                     f"outside 0..{m}")
                if not 1 <= blk <= nblocks:
                    raise ParseError(f"{path}:{lineno}: block {blk} outside "
                                     f"1..{nblocks}")
                dim = abs(sizes[blk - 1])
                if not 0 <= i <= j < dim:
                    raise ParseError(
                        f"{path}:{lineno}: entry ({i + 1},{j + 1}) is not in "
                        f"the upper triangle of block {blk}, which has size "
                        f"{dim}. SDPA requires i <= j, and the residual "
                        f"computation doubles off-diagonal entries on that "
                        f"assumption")
                if sizes[blk - 1] < 0 and i != j:
                    raise ParseError(
                        f"{path}:{lineno}: off-diagonal entry "
                        f"({i + 1},{j + 1}) in diagonal block {blk}")
                if (k, blk, i, j) in seen:
                    # legal SDPA (records sum), but the verifier and the
                    # extractor take the last F_0 entry and sum the rest, so
                    # a file with duplicates would mean different things to
                    # the two runs
                    raise ParseError(f"{path}:{lineno}: duplicate entry for "
                                     f"({k},{blk},{i + 1},{j + 1})")
                seen.add((k, blk, i, j))
                entries.append((k, blk, i, j, int(v)))
    if ds < 4:
        raise ParseError(f"{path}: only {ds} data lines; the header needs 4 "
                         f"(m, nblocks, block sizes, objective)")
    return m, sizes, c, entries


def parse_cert_X(path: Path, sizes=None):
    """The csdp primal matrix X, which is matrix 2 of the .cert.

    `sizes` enables the verifier's check that an entry of a diagonal block is
    on the diagonal.  Without it a bundle can pass here and then abort the
    full verifier run, which asserts exactly that.
    """
    X = {}
    with as_parse_errors(path), path.open(encoding="utf-8") as f:
        try:
            next(f)
        except StopIteration:
            raise ParseError(f"{path}: empty")
        for lineno, line in enumerate(f, 2):
            p = line.split()
            if not p:
                continue
            if len(p) != 5:
                # the same rule as parse_sdpa, for the same reason: appending
                # one token to an X line drops it, which zeroes that entry of
                # X and can turn a PSD matrix into one that is not
                raise ParseError(
                    f"{path}:{lineno}: line has {len(p)} tokens, expected 5: "
                    f"{line.strip()[:60]!r}")
            if int(p[0]) != 2:
                continue
            blk, i, j = int(p[1]), int(p[2]) - 1, int(p[3]) - 1
            if sizes is not None:
                if not 1 <= blk <= len(sizes):
                    raise ParseError(f"{path}:{lineno}: block {blk} outside "
                                     f"1..{len(sizes)}")
                dim = abs(sizes[blk - 1])
                if not 0 <= i < dim or not 0 <= j < dim:
                    raise ParseError(
                        f"{path}:{lineno}: entry ({i + 1},{j + 1}) outside "
                        f"block {blk}, which has size {dim}")
                if sizes[blk - 1] < 0 and i != j:
                    raise ParseError(
                        f"{path}:{lineno}: off-diagonal entry ({i + 1},"
                        f"{j + 1}) in diagonal block {blk}")
            key = (min(i, j), max(i, j))
            if key in X.get(blk, {}):
                raise ParseError(f"{path}:{lineno}: duplicate entry for "
                                 f"block {blk} ({i + 1},{j + 1}); a "
                                 f"transposed repeat counts as one")
            v = float(p[4])
            if v != v or v in (float("inf"), float("-inf")):
                raise ParseError(f"{path}:{lineno}: entry value {p[4]!r} is "
                                 f"not a finite number")
            X.setdefault(blk, {})[key] = v
    return X


def no_duplicate_keys(pairs):
    """`json.loads` keeps the last of two equal keys; a certificate listing a
    row twice would then be checked on one value while displaying another."""
    d = {}
    for k, v in pairs:
        if k in d:
            raise ValueError(f"duplicate key {k!r}")
        d[k] = v
    return d


def main() -> int:
    if len(sys.argv) != 4:
        print(__doc__); return 2
    sdpa, certp, mult = (Path(a) for a in sys.argv[1:4])
    try:
        doc = json.loads(mult.read_text(encoding="utf-8"),
                         object_pairs_hook=no_duplicate_keys)
    except ValueError as e:
        print(f"FAIL: {mult} is not valid JSON: {e}"); return 1
    missing = [k for k in ("mu", "m", "T", "target", "weights_positive",
                           "sdpa_sha256", "cert_sha256", "denom_exp",
                           "lambda_exp") if k not in doc]
    if missing:
        print(f"FAIL: the certificate is missing {', '.join(missing)}"); return 1

    def fr(p):
        if not isinstance(p, (list, tuple)) or len(p) != 2:
            raise ValueError(f"malformed rational {p!r} in {mult}: expected a "
                             f"[numerator, denominator] pair")
        if any(isinstance(x, bool) or not isinstance(x, (int, str)) for x in p):
            raise ValueError(f"malformed rational {p!r} in {mult}: numerator and "
                             f"denominator must be integers or decimal strings, "
                             f"not floats or booleans")
        try:
            num, den = int(p[0]), int(p[1])
        except (TypeError, ValueError):
            raise ValueError(f"malformed rational {p!r} in {mult}")
        if den <= 0:
            raise ValueError(f"non-positive denominator in {p!r} in {mult}")
        return F(num, den)

    if not isinstance(doc["mu"], dict) or not isinstance(
            doc["weights_positive"], dict):
        print("FAIL: mu and weights_positive must be objects"); return 1
    mu = {}
    for key, val in doc["mu"].items():
        t = tuple(int(x) for x in key.split(","))
        if t in mu:
            print(f"FAIL check 3: two mu keys name the same row {t}"); sys.exit(1)
        mu[t] = fr(val)
    m = doc["m"]
    if not isinstance(m, int):
        print(f"FAIL: the certificate's m is {m!r}, not an integer"); return 1
    weights_pub = {}
    for key, val in doc["weights_positive"].items():
        k = int(key)
        if k in weights_pub:
            print(f"FAIL check 3: two weight keys name the same column {k}")
            return 1
        weights_pub[k] = fr(val)
    T_pub = fr(doc["T"])
    if fr(doc["target"]) != TARGET:
        print(f"FAIL: the certificate names target {fr(doc['target'])}, but "
              f"this script checks against {TARGET}"); return 1

    # (1) the .sdpa is the paper's problem, the inputs are the ones the
    # certificate was built for, and the rationalisation is the archived one
    for label, path, pinned in (("sdpa", sdpa, SDPA_SHA256),
                                ("cert", certp, CERT_SHA256)):
        got = sha256(path)
        if got != pinned:
            print(f"FAIL check 1: .{label} sha256 {got}\n"
                  f"              this script checks the pentagon problem's "
                  f"{label}, {pinned}"); return 1
    for label, field, pinned in (("sdpa", "sdpa_sha256", SDPA_SHA256),
                                 ("cert", "cert_sha256", CERT_SHA256)):
        want = doc.get(field)
        if want != pinned:
            print(f"FAIL check 1: the certificate names {field} {want}, "
                  f"this script checks {pinned}"); return 1
    for field, have in (("denom_exp", DENOM_EXP), ("lambda_exp", LAMBDA_EXP)):
        if not isinstance(doc.get(field), int) or doc[field] != have:
            print(f"FAIL check 1: certificate was built at {field}="
                  f"{doc.get(field)}, this script recomputes at {have}")
            return 1
    print(f"check 1 OK: .sdpa is the pentagon problem {SDPA_SHA256[:16]}... "
          f"and .cert is {CERT_SHA256[:16]}...,\n"
          f"            both pinned by this script, and the certificate is "
          f"for them, at 10^-{DENOM_EXP}")

    # (7) the .sdpa parses cleanly -- parse_sdpa raises on a malformed entry
    # line or a non-integer F value rather than skipping it
    m_f, sizes, c, entries = parse_sdpa(sdpa)
    if m_f != m:
        print(f"FAIL: m mismatch: .sdpa says {m_f}, certificate says {m}"); return 1
    print(f"check 7 OK: all {len(entries)} entry lines of the .sdpa are "
          f"well-formed, with integer F values")

    # (2) y >= 0 : block 1 is exactly the -m coordinate-nonnegativity block
    if sizes[0] != -m:
        print(f"FAIL check 2: block 1 has size {sizes[0]}, expected {-m}"); return 1
    seen = {}
    for (k, blk, i, j, v) in entries:
        if blk != 1:
            continue
        if k == 0:
            # Even v == 0 is rejected: the verifier counts block-1 entries
            # without looking at their values and asserts the count is m, so
            # a zero F_0 entry here would pass this check and abort the full
            # run.  A bundle that passes must stay full-verifiable.
            print(f"FAIL check 2: block 1 carries an F_0 entry "
                  f"({i + 1},{j + 1})={v}; block 1 must hold nothing but the m "
                  f"coordinate-nonnegativity rows")
            return 1
        if not (i == j == k - 1 and v == 1):
            print(f"FAIL check 2: unexpected block-1 entry "
                  f"k={k} ({i + 1},{j + 1})={v}"); return 1
        if k in seen:
            print(f"FAIL check 2: block-1 row for k={k} appears twice"); return 1
        seen[k] = True
    missing = [k for k in range(1, m + 1) if k not in seen]
    if missing:
        print(f"FAIL check 2: {len(missing)} of {m} coordinates have no "
              f"nonnegativity row (first: {missing[:5]})"); return 1
    print(f"check 2 OK: block 1 is the {-m} coordinate-nonnegativity block, "
          f"each of the {m} coordinates bounded below exactly once, so y >= 0")

    # the linear rows the multipliers act on, and their F_0 side
    rows, f0 = {}, {}
    for (k, blk, i, j, v) in entries:
        if blk == 1 or not (sizes[blk - 1] < 0 and i == j):
            continue
        if k == 0:
            # check 7 rejects duplicates, so this is an assignment in all but
            # form; written as a sum because SDPA's own semantics is to sum
            f0[(blk, i)] = f0.get((blk, i), F(0)) + v
        else:
            row = rows.setdefault((blk, i), {})
            row[k] = row.get(k, 0) + v

    # (3) mu >= 0, and every multiplier names a row that exists
    neg = [k for k, v in mu.items() if v < 0]
    if neg:
        print(f"FAIL check 3: {len(neg)} negative multipliers"); return 1
    # `k in f0` is NOT enough: a key in f0 but not in rows is a constant row
    # `0 >= f0`, which check 4 never constrains while check 5 gives it
    # unlimited weight in T
    orphan = [k for k in mu if k not in rows]
    if orphan:
        print(f"FAIL check 3: {len(orphan)} multipliers name no linear row "
              f"(first: {sorted(orphan)[:5]}); they would be counted in the "
              f"headline and contribute to nothing"); return 1
    print(f"check 3 OK: all {len(mu)} multipliers are nonnegative and name "
          f"a linear row")

    # (4) column domination
    col = {}
    for key, muv in mu.items():
        for k, a in rows.get(key, {}).items():
            col[k] = col.get(k, F(0)) + muv * a
    bad = [k for k in range(1, m + 1)
           if col.get(k, F(0)) > -weights_pub.get(k, F(0))]
    if bad:
        print(f"FAIL check 4: {len(bad)} columns not dominated"); return 1
    print(f"check 4 OK: all {m} columns dominated "
          f"({len(weights_pub)} with positive weight)")

    # (5) T = -mu . f0, f0 from the .sdpa
    T = -sum(muv * f0.get(key, F(0)) for key, muv in mu.items())
    if T != T_pub:
        print(f"FAIL check 5: recomputed T={T} != published {T_pub}"); return 1
    print(f"check 5 OK: T = -mu.f0 = {float(T):.6e}, recomputed from the .sdpa")

    # (6) the weights really are r^+, and the safe value clears the target
    Xf = parse_cert_X(certp, sizes)
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
    # The flag-block repair: absorb positive residual into the slack of block 1.
    # This is self-neutralising, which is why inflating block-1 slack in the
    # .cert buys nothing: check 2 pins F_k's block-1 contribution to exactly
    # X[1][(k-1,k-1)], so the repair leaves r'_k = max(0, r_k - X[1][kk])
    # however large that slack is.
    for k in range(1, m + 1):
        if r[k] <= 0:
            continue
        delta = min(r[k], X[1].get((k - 1, k - 1), F(0)))
        if delta:
            X[1][(k - 1, k - 1)] -= delta; r[k] -= delta
    weights = {k: r[k] for k in range(1, m + 1) if r[k] > 0}
    if weights != weights_pub:
        only_pub = set(weights_pub) - set(weights)
        only_new = set(weights) - set(weights_pub)
        diff = [k for k in set(weights) & set(weights_pub)
                if weights[k] != weights_pub[k]]
        print(f"FAIL check 6: recomputed r^+ does not match the published "
              f"weights ({len(only_new)} extra, {len(only_pub)} missing, "
              f"{len(diff)} differing)"); return 1
    V = -trF0 + T
    if V > TARGET:
        print(f"FAIL check 6: safe value {float(V):.12f} exceeds target "
              f"{float(TARGET):.12f}"); return 1
    print(f"check 6 OK: r^+ recomputed from the .cert matches all "
          f"{len(weights)} published weights; -tr(F_0 X) = "
          f"{float(-trF0):.12f}")

    print(f"\nVERIFIED: sum_k r_k^+ y_k <= {float(T):.12e} for every feasible y,")
    print(f"          so phi <= {float(V):.12f} <= {float(TARGET):.12f} "
          f"= {TARGET.numerator}/{TARGET.denominator}, margin "
          f"{float(TARGET - V):.3e}.")
    print("Scope: the 278 Cauchy-Schwarz blocks of X are NOT shown positive\n"
          "       semidefinite here -- that is the exact rational LDL^T of the\n"
          "       full verifier run.  (X's 9114 diagonal blocks ARE made\n"
          "       nonnegative above, by the clip at rationalisation.)  Two\n"
          "       further things this script cannot attest, and takes from the\n"
          "       provenance record: that the full run happened and passed on\n"
          "       this .cert, and that this .sdpa is the program Paper 1\n"
          "       describes.  Beyond the SDP, the step to a statement about\n"
          "       graphs is the paper's, not this script's.")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except SystemExit:
        raise
    except ParseError as e:
        # raised only by parse_sdpa and parse_cert_X, which are check 7
        print(f"FAIL check 7: {e}")
        raise SystemExit(1)
    except Exception as e:                       # noqa: BLE001
        # the certificate JSON, or a missing file.  Named, not a traceback;
        # this script has no failure path that should reach a reader as one.
        print(f"FAIL: {type(e).__name__}: {e}")
        raise SystemExit(1)
