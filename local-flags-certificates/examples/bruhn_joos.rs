/// Reproduces the Bruhn–Joos sparsity bound (Combin. Probab. Comput. 27 (2018),
/// Lemma 2.1): for any graph of maximum degree Δ, the strong neighbourhood of an
/// edge (its neighbourhood in L(G)^2) induces at most (3/2)Δ^4 + 5Δ^3 edges in
/// L(G)^2. The size-4 SDP returns the leading constant 3/2.
/// NB: this is the EDGE COUNT in the neighbourhood, not the maximum degree of
/// L(G)^2 — the latter is ~2Δ^2 (Bruhn–Joos Lemma 3.1), so "max degree ≤ 3/2·Δ^2"
/// would be false.
extern crate flag_algebra;
extern crate local_flags;

use flag_algebra::flags::{Colored, Graph};
use flag_algebra::*;
use local_flags::Degree;


type G = Colored<Graph, 2>;
#[derive(Debug, Clone, Copy)]
pub enum Connected {}
type F = SubClass<G, Connected>;

type N = f64;
type V = QFlag<N, F>;

impl SubFlag<G> for Connected {
    const SUBCLASS_NAME: &'static str = "Connected 2-colored graphs";

    const HEREDITARY: bool = false;

    fn is_in_subclass(flag: &G) -> bool {
        // Each connected component contains a vertex colored 0
        flag.is_connected_to(|i| flag.color[i] == 0)
    }
}

fn connected_edges(g: &F, e1: &[usize; 2], e2: &[usize; 2]) -> bool {
    for &u1 in e1 {
        for &u2 in e2 {
            if g.content.content.edge(u1, u2) {
                return true;
            }
        }
    }
    false
}

// The three ways to split a 4-elements set into two parts of size 2
const SPLIT: [([usize; 2], [usize; 2]); 3] = [([0, 1], [2, 3]), ([0, 2], [1, 3]), ([0, 3], [1, 2])];

fn strong_density() -> V {
    Basis::new(4).qflag_from_coeff(|g: &F, _| {
        let mut res = 0;
        for (e1, e2) in &SPLIT {
            if g.content.content.edge(e1[0], e1[1])
                && g.content.content.edge(e2[0], e2[1])
                && (e1.iter().any(|&v| g.content.color[v] == 0))
                && (e2.iter().any(|&v| g.content.color[v] == 0))
                && connected_edges(g, e1, e2)
            {
                res += 1
            }
        }
        res as N / 24.
    })
}

fn ones(n: usize, k: usize) -> V {
    Degree::project(&Colored::new(Graph::empty(k), vec![0; k]).into(), n)
}

pub fn main() {
    init_default_log();
    let n = 4;
    let basis = Basis::new(n);
    let obj = strong_density();

    let mut ineqs = vec![
        flags_are_nonnegative(basis),
        ones(n, 1).untype().at_most(2.),
        ones(n, 2).untype().at_most(4.),
        ones(n, 3).untype().at_most(8.),
    ];

    ineqs.append(&mut Degree::regularity(basis));

    let pb = Problem::<N, _> {
        ineqs,
        cs: basis.all_cs(),
        obj: -obj,
    }
    .no_scale();

    let mut f = FlagSolver::new(pb, "maximum_strong_edge_degree");
    f.init();
    f.print_report(); // Write some informations in report.html

    let result = -f.optimal_value.expect("Failed to get optimal value");

    println!("Optimal value: {}", result); // The answer must be 1.5
}
