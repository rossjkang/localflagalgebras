# Archived SDP certificates

The dual certificates behind three results of *Local flag algebras*:

| certificate | result | paper |
|---|---|---|
| `bounded_pentagon_alt` | `phi(O_Q) <= 4146/10000`, giving `P(G) <= 0.02073 \|G\| Delta^4` | Theorem 1.2 |
| `bounded_hexagon_alt` | `phi(O_Q6) <= 8/31`, giving `P_6(G) <= \|G\| Delta^5 / 93` | Theorem C.3 |
| `bounded_heptagon` | `phi(O_7) <= 1/9`, giving `P_7(G) <= \|G\| Delta^6 / 126` | Theorem C.3 |

All three are verified in exact rational arithmetic, independently of the
floating-point solver, by `verify_exact_certificate.py`.

**On Lean.** The C6/C7 certificates are not formalised in Lean. The pentagon
one **is**, as Lean-embedded rationalised data in
`DaveyThesis2024/PentagonQCertificate/` — but only at `10^-12`, whereas the
verification recorded here needs `10^-16`, which is why the raw `.cert` is
published too. The Lean copy and the `.cert` here are the same object
(matrix-id 2 of the solver output).

## Contents

| file | role |
|---|---|
| `*.sdpa.gz` | **load-bearing**: the whole problem (m, block sizes, objective, every `F_k`) |
| `bounded_pentagon_alt.sdpa.prefix.gz` | the pentagon problem's **first 9407 lines only** — see *Reconstructing the pentagon problem* |
| `*.cert.gz` | heuristic seeds; the verifier reads them as floats, rationalises, and never trusts them |
| `bounded_pentagon_alt.multipliers.json.gz` | **the certificate proper** for the pentagon's universal bound — see *The four-second check* |
| `*.provenance.json` | archival records: hashes, problem sizes, rationalisation exponents, repair counts, residuals, multipliers where used, safe value, divisor |
| `verify_exact_certificate.py` | the exact-rational verifier |
| `splice_pentagon_sdpa.py` | rebuilds the pentagon `.sdpa` |
| `extract_multipliers.py` | regenerates the multiplier certificate (needs numpy + scipy) |
| `check_multipliers.py` | checks it against the `.sdpa` and the `.cert` — standard library only |

Published here the directory is 20.1 MB. Following the instructions below —
`gunzip -k` and then the splice, both of which keep what they read — leaves
about 118 MB in it.
`verify_exact_certificate.py` and `extract_multipliers.py` need numpy and
scipy, which the repository-level `../../requirements.txt` provides (along
with packages for other parts of the repository). `check_multipliers.py` needs
neither, nor anything else outside the standard library.

## Reconstructing the pentagon problem

The pentagon and hexagon size-8 programs are the **same constraint system with
two objectives**: their `F_0` and `F_k` entry blocks are byte-identical,
1,252,263 lines (1,252,260 entries and three blank lines). They differ only in the comment header, 278 Cauchy--Schwarz
comment lines, and the objective vector — all within the first 9407 lines. So
only that prefix is shipped (52 KB rather than 4.6 MB), and the rest is spliced
from the hexagon file already here. From this directory:

    cd DaveyThesis2024/certificates      # if you are at the clone root
    gunzip -kf *.gz            # also inflates the prefix; nothing reads that copy
    python3 splice_pentagon_sdpa.py

which writes `bounded_pentagon_alt.sdpa` and asserts both its input and output
`sha256`. Do this **before** verifying the pentagon.

## The four-second check

Section 6 of the paper rests on a universal bound: nonnegative rational
multipliers over the program's own linear rows certify
`sum_k r_k^+ y_k <= T` for **every feasible y**, not merely at the certificate's
own dual point. Those 5,176 multipliers are the certificate, and the verifier
does not emit them, so they are published here:

    python3 check_multipliers.py bounded_pentagon_alt.sdpa \
                                 bounded_pentagon_alt.cert \
                                 bounded_pentagon_alt.multipliers.json

About four seconds, standard library only — no numpy, no scipy, no solver.
Seven checks; the five that do arithmetic do it exactly, over rationals:

1. the `.sdpa` and the `.cert` are the paper's problem and the archived
   solution, by two `sha256` the script holds as its own constants rather
   than reads from the certificate under test — the `.cert` matters as much
   as the `.sdpa`, because `X >= 0` is the link left to the archived run and
   that run factorised this `X` — and the certificate names the
   rationalisation exponents the script recomputes at;
2. block 1 really is the coordinate-nonnegativity block — each of the 9,295
   coordinates bounded below exactly once, and nothing else in that block —
   without which `y >= 0` fails and checks 3 to 5 prove nothing;
3. `mu >= 0`, and every multiplier names a linear row that exists;
4. every column is dominated;
5. `T = -mu.f0`, with `f0` recomputed from the `.sdpa`;
6. the weights really are `r^+`, and the safe value clears the target: `r`
   and `tr(F_0 X)` are recomputed from the `.sdpa` and the `.cert` at the
   archived rationalisation, the published weights must match exactly, and
   `V = -tr(F_0 X) + T = 0.414589418954` must be at most `2073/5000` — which
   is the script's own constant, not a number it reads from the certificate;
7. the `.sdpa` and the `.cert` parse cleanly. For the `.sdpa`: `m`, the block
   count, the block-structure line and the objective vector are the pentagon
   program's, all four header lines are present, and every entry line carries
   exactly five tokens and an integer `F` value, names a block and a
   coordinate that exist, sits in the upper triangle (on the diagonal, for a
   diagonal block), and is not a duplicate. For the `.cert`: five tokens per
   entry line after the leading `y`-vector line, coordinates inside their block, finite values, no duplicates. In both
   files a line that does not conform raises rather than being skipped — one
   appended token on a `.cert` line would otherwise zero that entry of `X`,
   which can turn a positive semidefinite matrix into one that is not.

Checks 1, 2, 3, 6 and 7 exist because without them the rest is checkable
against a certificate or a problem that does not say what it claims. The
multipliers and `T` are read from the JSON, so a certificate with no weights
at all, or with `mu` and `T` scaled together by 1000 — which pushes the safe
value past the target — passes checks 4 and 5. A bound-breaking `F_0` entry
hides from any reader that skips malformed lines if you append one token to
it, and hides just as well off the diagonal of a diagonal block, while a
conforming SDPA reader sees it either way. And a coordinate outside a block's
declared size manufactures a linear row that is not in the program at all,
which a multiplier placed on it will then certify anything from.

Because both file hashes are pinned, checks 2 and 7 have one possible outcome
on the published bundle: they are lemmas about a fixed pair of files, not
defences against an adversary. They are written not to depend on the pins —
`m`, the block count, the block sizes and the objective are pinned separately,
so the coordinate checks stand on a frame that does not come out of the file
being checked. Without that, editing the block-structure line moves the frame
and manufactures a row the coordinate checks would then bless; and the entire
objective can be replaced without moving a printed digit, because the
block-1 repair absorbs the change.

To regenerate the multipliers rather than check them — one to three minutes,
depending on the machine, and this one does need numpy and scipy:

    python3 extract_multipliers.py bounded_pentagon_alt.sdpa \
                                   bounded_pentagon_alt.cert \
                                   -o bounded_pentagon_alt.multipliers.json

It re-implements the verifier's pipeline around the verifier's own two
parsers, and stops unless it reproduces the archived numbers it gates on, so a
silent drift fails rather than overwrites. Those gates are `assert`s, so the
script refuses to run under `python3 -O` rather than skipping them.

**Scope.** The **278 Cauchy–Schwarz blocks** of `X` are not shown positive
semidefinite here: that is the exact rational `LDL^T`, the dominant cost of the
pipeline, and the full run below is what establishes it — for the `.cert`
check 1 pins, which is why it pins it. It is the one link in the chain the fast
check leaves open, and the safe value does depend on it. (`X`'s 9,114 diagonal
blocks *are* made nonnegative here, by the clip at rationalisation, so "`X >= 0`
is unchecked" would overstate the gap.) The `native_decide` LDL witnesses in
`DaveyThesis2024/PentagonQCertificate/` are not a second, independent check
either: as noted above they carry the same matrix at `10^-12` with a `10^-11`
shift, and PSD there does not give PSD at the `10^-16` this verification uses.

Two further things no script here can attest, which come from the provenance
record and not from any check: that the full run happened and passed on this
`.cert`, and that this `.sdpa` is the program Paper 1 describes. Beyond the SDP,
what the paper needs on top is the step from the program to a statement about
graphs.

## Full verification

Each command is the `verification.flags` field of the corresponding provenance
record, **plus an explicit `--ckpt`** — except that the heptagon's `flags`
field ends with a prose parenthetical naming its two defaults, which argparse
rejects; drop it and pass the flags below. The `--ckpt` is not optional: the
verifier keys its checkpoint on `(sdpa, cert, denom_exp, lambda_exp)` and
asserts on a mismatch, so consecutive runs sharing the default directory fail.
The default is also `/private/tmp/...`, which does not exist on Linux, and the
`mkdir` has no `parents=True` — so on Linux the run dies, several minutes in,
after the parsing work. The verifier cannot be patched to fix this: its
`sha256` is pinned in all three provenance records.

    python3 verify_exact_certificate.py \
        bounded_pentagon_alt.sdpa bounded_pentagon_alt.cert \
        --ckpt ./ckpt-bounded_pentagon_alt \
        --denom-exp 16 --lambda-exp 16 --target-numer 4146 --target-denom 10000 --raw-scale 1 --graph-divisor 20 --skip-sum-y --repair-with-flag-block --residual-method highs-ipm --strict-zero-residual-buffer

    python3 verify_exact_certificate.py \
        bounded_hexagon_alt.sdpa bounded_hexagon_alt.cert \
        --ckpt ./ckpt-bounded_hexagon_alt \
        --denom-exp 16 --lambda-exp 16 --target-numer 8 --target-denom 31 --raw-scale 1 --graph-divisor 24 --skip-sum-y --repair-with-flag-block --residual-method highs-ipm --strict-zero-residual-buffer

    python3 verify_exact_certificate.py \
        bounded_heptagon.sdpa bounded_heptagon.cert \
        --ckpt ./ckpt-bounded_heptagon \
        --target-numer 1 --target-denom 9 --raw-scale 1 --graph-divisor 14 --skip-sum-y --repair-with-flag-block --residual-method highs-ipm --strict-zero-residual-buffer

The heptagon additionally relies on the defaults `--denom-exp 14 --lambda-exp 11`.
The pentagon run takes about 647 s, dominated by the exact rational `LDL^T`
over its 278 PSD blocks.

| | pentagon | `C_6` | `C_7` |
|---|---|---|---|
| bound on the limit functional | `phi(O_Q) <= 2073/5000` | `phi(O_Q6) <= 8/31` | `phi(O_7) <= 1/9` |
| safe value attained | `0.414589418954` | `0.257890799441` | `0.110518540052` |
| margin | `1.058e-05` | `1.737e-04` | `5.926e-04` |
| problem size (`m`, blocks, entries) | 9295, 9392, 1252260 | 9295, 9392, 1252260 | 1390, 1247, 68060 |
| PSD blocks certified by exact `LDL^T` | 278 | 278 | 64 |
| dual residuals | 17 positive of 9295, absorbed by 5176 multipliers | 0 positive of 9295 | 299 positive of 1390, absorbed by 763 multipliers |

## Regenerating this bundle

The `.gz` files are `gzip -9` of their sources. Re-gzipping will not reproduce
them byte-for-byte: six of the seven carry a stored filename and mtime; the
data files' mtimes are of the original runs, the prefix's and the multipliers'
of the splice and the extraction. Nothing depends on that. Every `sha256` and
`bytes` field in the provenance records refers to the **uncompressed** file —
so for `.cert` and the hexagon/heptagon `.sdpa`, `gunzip` and the hashes match;
for the pentagon `.sdpa` the hash matches only after the **splice** of the
9407-line prefix described above, and for the multipliers after gunzipping to
`.json`.

Do not run a path-rewriting pass over this directory: the provenance records are
archival and reproduced verbatim, and several of their fields name paths in the
authors' working repository rather than paths here. The `verification.verifier`
field of all three names `verify_exact_certificate.py` where it lives there;
the hexagon's `reproducibility.precision_sensitivity` names an
exponent-screening script that is not published; and the hexagon's and
heptagon's `regeneration.flag_basis_cache` name generated flag-basis
directories that are gitignored and so absent here. Those paths are
deliberately left as they were recorded. The `verifier_sha256` in all three
records pins the copy published here, and rewriting the verifier would break
it.

The pentagon problem can also be rebuilt from source: `cargo run --release
--example bounded_pentagon_alt_approach` regenerated this exact `.sdpa`
(`b46467ab...`) on 2026-09-20. Note it writes `bounded_pentagon.sdpa` — the same
filename `bounded_pentagon.rs` uses for an unrelated 4 KB size-5 program.

To check the bundle — every `sha256` and every `bytes` field of all three
records, against the published files:

```sh
python3 - <<'EOF'
import gzip, hashlib, json, subprocess
subprocess.run(["python3", "splice_pentagon_sdpa.py"], check=True)
for s in ["bounded_pentagon_alt", "bounded_hexagon_alt", "bounded_heptagon"]:
    p = json.load(open(f"{s}.provenance.json"))
    for role, info in p["files"].items():
        name = info["name"]
        data = (open(name, "rb").read() if name.endswith(".sdpa") and "reconstruction" in info
                else gzip.open(info.get("published_as", name + ".gz"), "rb").read())
        assert hashlib.sha256(data).hexdigest() == info["sha256"], (s, role)
        assert len(data) == info["bytes"], (s, role)
    v = hashlib.sha256(open("verify_exact_certificate.py", "rb").read()).hexdigest()
    assert v == p["verification"]["verifier_sha256"]
print("bundle OK")
EOF
```
