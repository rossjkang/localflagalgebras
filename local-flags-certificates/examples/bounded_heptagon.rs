/// Bound the number of induced copies of C7 containing any particular
/// vertex in a triangle-free Δ-regular graph.
///
/// Exact analog of bounded_pentagon.rs. By the same reduction (colour N(v)
/// black, the rest red, delete v), an induced hexagon through v corresponds to
/// a black-red-red-red-black (BRRRB) 5-path in the coloured graph, up to an
/// O(Δ^4) boundary correction. The size-6 SDP optimum λ gives
///     Q6(H,v)/Δ^5 ≲ λ/2      (each hexagon = 2 BRRRB paths)
/// hence  #C6 = (1/6) Σ_v Q6(H,v) ≤ |H| Δ^5 · λ/12,  i.e. ρ_C6 ≤ λ/12.
use flag_algebra::flags::{Colored, Graph};
use flag_algebra::*;
use itertools::iproduct;
use local_flags::Degree;

type G = Colored<Graph, 2>;
#[derive(Debug, Clone, Copy)]
pub enum HeptagonBoundGraphs {}
type F = SubClass<G, HeptagonBoundGraphs>;

type N = f64;
type V = QFlag<N, F>;

impl SubFlag<G> for HeptagonBoundGraphs {
    const SUBCLASS_NAME: &'static str = "Two-Coloured Heptagon Bound Graphs";

    const HEREDITARY: bool = false;

    fn is_in_subclass(flag: &G) -> bool {
        // Each connected component contains a vertex colored 0 (black anchor).
        if !flag.is_connected_to(|i| flag.color[i] == 0) {
            return false;
        }
        // No black-black edges (the black set N(v) is independent).
        if flag
            .content
            .edges()
            .any(|(u, v)| flag.color[u] == 0 && flag.color[v] == 0)
        {
            return false;
        }
        // No triangles.
        let n = flag.content.size();
        for (u, v, w) in iproduct!(0..n, 0..n, 0..n) {
            if u == v || u == w || v == w {
                continue;
            }
            if flag.content.edge(u, v) && flag.content.edge(u, w) && flag.content.edge(v, w) {
                return false;
            }
        }
        true
    }
}

fn ones(n: usize, k: usize) -> V {
    Degree::project(&Colored::new(Graph::empty(k), vec![0; k]).into(), n)
}

pub fn main() {
    init_default_log();
    let n = 7;
    let basis = Basis::new(n);

    // BRRRB 5-path: black(0)-red(1)-red(1)-red(1)-black(0).
    let c7_path: F = Colored::new(
        Graph::new(6, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]),
        vec![0, 1, 1, 1, 1, 0],
    )
    .into();
    let obj = Degree::project(&c7_path, n).untype();

    let mut ineqs = vec![flags_are_nonnegative(basis)];

    for i in 1..=n {
        ineqs.push(ones(n, i).untype().equal(1.));
    }

    ineqs.append(&mut Degree::regularity(basis));

    let pb = Problem::<N, _> {
        ineqs,
        cs: basis.all_cs(),
        obj: -obj,
    }
    .no_scale();

    let mut f = FlagSolver::new(pb, "bounded_heptagon");
    f.init();
    f.print_report();

    let result = -f.optimal_value.expect("Failed to get optimal value");

    println!("Optimal value (lambda7): {}", result);
    println!("=> rho_C7 <= lambda7/14 = {}", result / 14.0);
}
