#!/usr/bin/env python3
"""Rebuild bounded_pentagon_alt.sdpa from the published hexagon .sdpa.

The pentagon and hexagon size-8 programs are the SAME constraint system with
two different objectives: their F_0 and F_k entry blocks are byte-identical
(1,252,263 lines: 1,252,260 entries and three blank lines).  They differ only in the comment header, 278 Cauchy-Schwarz
comment lines, and the objective vector -- all inside the first 9407 lines.

So the bundle ships lines 1-9407 of the pentagon file and reconstructs the rest
from the hexagon file that is already published beside it.

    python3 splice_pentagon_sdpa.py            # uses the files in this directory

Writes bounded_pentagon_alt.sdpa and asserts its sha256.  Stdlib only.
"""
from __future__ import annotations
import gzip, hashlib, sys
from pathlib import Path

PREFIX_GZ = "bounded_pentagon_alt.sdpa.prefix.gz"
HEXAGON_GZ = "bounded_hexagon_alt.sdpa.gz"
OUT = "bounded_pentagon_alt.sdpa"
SHA_HEXAGON = "1f190f413154357fbc0fad4b95ebe3a9c3c82accfce61ce243a0fea868cdae5b"
SHA_OUT = "b46467ab2d34b672c122f4ebbd372d75aff808f63b336c873b56859ca24ca6ad"
PREFIX_LINES = 9407


def _open(path: Path) -> bytes:
    return gzip.open(path, "rb").read() if path.suffix == ".gz" else path.read_bytes()


def main() -> int:
    here = Path(__file__).resolve().parent
    prefix = _open(here / PREFIX_GZ)
    hexagon = _open(here / HEXAGON_GZ)

    got = hashlib.sha256(hexagon).hexdigest()
    if got != SHA_HEXAGON:
        print(f"INPUT MISMATCH: {HEXAGON_GZ} gunzips to {got},\n"
              f"               expected {SHA_HEXAGON}.\n"
              "The splice is defined against the published hexagon problem; if that\n"
              "file has been regenerated, this reconstruction is not valid.", file=sys.stderr)
        return 2

    n = prefix.count(b"\n")
    assert n == PREFIX_LINES, f"prefix has {n} lines, expected {PREFIX_LINES}"

    tail = b"\n".join(hexagon.split(b"\n")[PREFIX_LINES:])
    out = prefix + tail
    got = hashlib.sha256(out).hexdigest()
    if got != SHA_OUT:
        print(f"OUTPUT MISMATCH: got {got}, expected {SHA_OUT}", file=sys.stderr)
        return 3

    (here / OUT).write_bytes(out)
    print(f"wrote {OUT} ({len(out)} bytes), sha256 {got}  OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
