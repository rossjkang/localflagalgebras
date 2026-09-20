/// Tighter bound on induced C6 through a vertex in a triangle-free Δ-regular
/// graph, via the hexagon analog of the pentagon Q-functional.
///
///   Q6(G,v) := Δ·Q6(G,v)_pervertex + Σ_{u∈N(v)} (#induced C6 through u).
///
/// Σ_v Q6(G,v) = 12 Δ #C6, so a bound Q6(G,v) ≲ c Δ^6 gives #C6 ≲ (c/12)|G|Δ^5,
/// i.e. ρ_C6 ≤ c/12 (same shape as the size-6 simple bound φ(O6)/12 = 1/81).
///
/// Objective (reduction: colour N(v) black, delete v):
///   * BRRRB open 5-path [0,1,1,1,0]           — Δ·(#hex through v)
///   * C6 with k black vertices (N(v) is independent, so blacks are pairwise
///     non-adjacent on the cycle), weighted by k, for the Σ_{u∈N(v)} term:
///       1 black  [0,1,1,1,1,1]                       weight 1
///       2 black  [0,1,0,1,1,1] (dist 2), [0,1,1,0,1,1] (dist 3)  weight 2 each
///       3 black  [0,1,0,1,0,1] (alternating)         weight 3
use flag_algebra::flags::{Colored, Graph};
use flag_algebra::*;
use itertools::iproduct;
use local_flags::Degree;

type G = Colored<Graph, 2>;
#[derive(Debug, Clone, Copy)]
pub enum TriangleFreeConnected {}
type F = SubClass<G, TriangleFreeConnected>;

type N = f64;
type V = QFlag<N, F>;

impl SubFlag<G> for TriangleFreeConnected {
    // Same subclass (and cached name) as bounded_pentagon_alt_approach.rs, so
    // the size-8 flag basis is reused from ./data.
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
        for (u, v, w) in iproduct!(0..n, 0..n, 0..n) {
            if u == v || u == w || v == w {
                continue;
            }
            if !flag.content.edge(u, v) || !flag.content.edge(u, w) || !flag.content.edge(v, w) {
                continue;
            }
            return false;
        }
        true
    }
}

fn extension_in_x(t: Type<F>) -> V {
    let b = Basis::new(t.size + 1).with_type(t);
    b.qflag_from_indicator(|g: &F, type_size| g.content.color[type_size] == 0)
        .named(format!("ext_in_x({{{}}})", t.print_concise()))
}

fn size_of_x(n: usize) -> Vec<Ineq<N, F>> {
    let mut res = Vec::new();
    for t in Type::types_with_size(n - 1) {
        let diff = Degree::extension(t, 0) - extension_in_x(t);
        res.push(diff.equal(0.).untype());
    }
    res
}

fn ones(n: usize, k: usize) -> V {
    Degree::project(&Colored::new(Graph::empty(k), vec![0; k]).into(), n)
}

fn obj(n: usize) -> V {
    let c6 = &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)];

    let path: F =
        Colored::new(Graph::new(5, &[(0, 1), (1, 2), (2, 3), (3, 4)]), vec![0, 1, 1, 1, 0]).into();
    let one_black: F = Colored::new(Graph::new(6, c6), vec![0, 1, 1, 1, 1, 1]).into();
    let two_black_d2: F = Colored::new(Graph::new(6, c6), vec![0, 1, 0, 1, 1, 1]).into();
    let two_black_d3: F = Colored::new(Graph::new(6, c6), vec![0, 1, 1, 0, 1, 1]).into();
    let three_black: F = Colored::new(Graph::new(6, c6), vec![0, 1, 0, 1, 0, 1]).into();

    Degree::project(&path, n).untype()
        + Degree::project(&one_black, n).untype()
        + Degree::project(&two_black_d2, n).untype() * 2.0
        + Degree::project(&two_black_d3, n).untype() * 2.0
        + Degree::project(&three_black, n).untype() * 3.0
}

pub fn main() {
    init_default_log();
    let n = 8;
    let basis = Basis::new(n);

    let mut ineqs = vec![flags_are_nonnegative(basis)];
    for i in 1..=n {
        ineqs.push(ones(n, i).untype().equal(1.));
    }
    ineqs.append(&mut Degree::regularity(basis));
    ineqs.append(&mut size_of_x(n));

    let pb = Problem::<N, _> {
        ineqs,
        cs: basis.all_cs(),
        obj: -obj(n),
    }
    .no_scale();

    let mut f = FlagSolver::new(pb, "bounded_hexagon_alt");
    f.init();
    f.print_report();

    let result = -f.optimal_value.expect("Failed to get optimal value");
    // Calibration ρ_C6 ≤ φ/24 = φ/(2·12): the "12" from Σ_v Q6 = 12Δ#C6, the "2"
    // the projection/reversal factor (validated: pentagon Q φ=0.41458 → /20 →
    // 0.02073). Cf. the size-6 simple bound φ/12 = 1/81.
    println!("Optimal value (phi_OQ6): {}", result);
    println!("=> rho_C6 <= phi/24 = {} (simple size-6 was 1/81 = {})",
        result / 24.0, 1.0 / 81.0);
}
