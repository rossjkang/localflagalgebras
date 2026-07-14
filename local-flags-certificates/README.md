# local-flags

This repository contains the software which was used to prove the results in my MSc Mathematics thesis:
(see thesis.pdf). It contains a Rust implementation of the semidefinite method on local flags. This
framework can be used to prove asymptotic bounds on subgraph densities relative to the maximum
degree Δ(G) for Δ(G) large.

In particular:
- `examples/strong_edge_colouring.rs`: Proves the best known bound on the Erdős and Nešetřil
  conjecture on strong edge colouring[^erdosnes].
- `examples/bipartite_strong_edge_colouring.rs`. Proves the best known bound for the
  bipartite special case conjectured by Faudree et al[^erdosnes].
- `examples/bounded_pentagon.rs`: Proves a decent upper bound on the number of pentagons in a
  triangle free Δ-regular graph.
- `examples/bounded_pentagon_alt_approach.rs`: Proves a stronger upper bound on the same problem.

You can find the certificates of these programs for reference in the `certificates/` directory.

### Additions for the DaveyThesis2024 Lean formalization

This repository was extended for use in the
[DaveyThesis2024](../) Lean 4 formalization. Project-specific
additions live in subdirectories so the upstream Rust crate stays
self-contained:

- [`sec_search/`](sec_search/) — small-graph counterexample sweeps for
  the Erdős–Nešetřil and Faudree(-asymmetric) strong-edge-colouring
  conjectures (nauty `geng`/`genbgL` + a C `fast_check`), plus the
  full SDP-cert verification harness (`verify_sec_cert.py`, the
  `second_solver_*` logs, and the master results doc
  `sec_counterexample_results.md`). ~711M graphs swept, 0 CEs.
- `emit_lean_cert.py` — Python emitter producing Lean source for the
  Theorem 3.1 size-8 SDP certificate (consumed by
  `DaveyThesis2024/PentagonQCertificate/`).
- `sec_basis_size5_{bipartite,general}.txt` — basis enumerations
  emitted by `examples/dump_sec_size5.rs` and embedded in
  `DaveyThesis2024/SecBasis.lean` / `SecBipartiteBasis.lean`.

[^erdosnes]: *Induced matchings in bipartite graphs*, Faudree, R. J., Gyárfas, A., Schelp, R. H., & Tuza, Zs. (1989). Discrete Mathematics, 78(1–2), 83–87. https://doi.org/10.1016/0012-365X(89)90163-5

## Dependencies

You need to have rust installed. I recommend installing via [rustup.rs](https://rustup.rs).

You need to have the `csdp` command line installed to solve semi-definite optimization problems.
```
sudo apt install cmake gfortran coinor-csdp
```

## Usage

To clone this repository run `git clone --recursive http://github.com/EoinDavey/local-flags`.
The `--recursive` flag is required to include the `rust-flag-algebras` submodule which is a
modification of [crates.io/crates/flag-algebra](https://crates.io/crates/flag-algebra).

To run one of the scripts in the `example/` folder, e.g. `example/bounded_pentagon.rs`
run
```
cargo run --release --example bounded_pentagon
```
The first compilation may be quite long. The first execution can also take time because the library needs to compute lists of graphs and the matrices of some flag operators. These later are stored in files for later computations. Eventually, the bottleneck is the SDP solver.

> [!warning]
> These programs can generate a lot of on-disk data, especially for high values of `n`
> (the standard flag size search parameter).
