//! Count untyped flags in the exact subclass used by the size-8 pentagon SDP.
//!
//! Usage: `cargo run --release --example count_bounded_pentagon_basis -- 9`.

use flag_algebra::flags::{Colored, Graph};
use flag_algebra::*;
use local_flags::Degree;
use std::time::Instant;

type G = Colored<Graph, 2>;

#[derive(Debug, Clone, Copy)]
pub enum TriangleFreeConnected {}

type F = SubClass<G, TriangleFreeConnected>;

impl SubFlag<G> for TriangleFreeConnected {
    const SUBCLASS_NAME: &'static str = "Triangle Free Connected 2-colored graphs";
    const HEREDITARY: bool = false;

    fn is_in_subclass(flag: &G) -> bool {
        if !flag.is_connected_to(|i| flag.color[i] == 0) {
            return false;
        }
        for (u, v) in flag.content.edges() {
            if flag.color[u] == 0 && flag.color[v] == 0 {
                return false;
            }
        }
        let n = flag.content.size();
        for u in 0..n {
            for v in (u + 1)..n {
                if !flag.content.edge(u, v) {
                    continue;
                }
                for w in (v + 1)..n {
                    if flag.content.edge(u, w) && flag.content.edge(v, w) {
                        return false;
                    }
                }
            }
        }
        true
    }
}

fn main() {
    init_default_log();
    let max_n: usize = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "9".to_owned())
        .parse()
        .expect("maximum order must be a nonnegative integer");

    for n in 0..=max_n {
        let start = Instant::now();
        let count = Basis::<F>::new(n).get().len();
        println!("order={n} flags={count} elapsed_seconds={:.3}", start.elapsed().as_secs_f64());
    }
}
