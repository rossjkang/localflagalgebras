// Parameter-sweep version of asymmetric_bipartite_strong_density.rs.
//
// Reads the side-degree ratio P from the env var BIPARTITE_DENSITY_P
// (default 0.5 to match the canonical file). Emits a CSV row
//   P,sprs,lambda,lambda_over_2P2,chi
// on stdout so a driver script can collect a grid sweep.
//
// Used by the development notes to test whether the
// empirical constant-lambda_r/(2r^2) phenomenon holds beyond the
// 10-point grid r in {0.1, ..., 1.0}.

use canonical_form::Canonize;
use flag_algebra::flags::{Colored, Graph};
use flag_algebra::*;
use local_flags::{vertex_orbits, Degree};
use num::pow::Pow;
use std::iter::once;
use std::sync::OnceLock;

type G = Colored<Graph, 4>;

const COMP: [u8; 4] = [0, 1, 0, 1];
const X_COLS: [u8; 2] = [0, 1];
const Y_COLS: [u8; 2] = [2, 3];

fn p_value() -> f64 {
    static CACHED: OnceLock<f64> = OnceLock::new();
    *CACHED.get_or_init(|| {
        std::env::var("BIPARTITE_DENSITY_P")
            .ok()
            .and_then(|s| s.parse::<f64>().ok())
            .unwrap_or(0.5)
    })
}

#[derive(Debug, Clone, Copy)]
pub enum BPStrongDensityFlag {}
type F = SubClass<G, BPStrongDensityFlag>;

impl SubFlag<G> for BPStrongDensityFlag {
    const SUBCLASS_NAME: &'static str = "Bipartite Strong Density graphs";
    const HEREDITARY: bool = false;

    fn is_in_subclass(flag: &G) -> bool {
        if !flag.is_connected_to(|i| X_COLS.contains(&flag.color[i])) {
            return false;
        }
        if flag
            .content
            .edges()
            .any(|(u, v)| COMP[flag.color[u] as usize] == COMP[flag.color[v] as usize])
        {
            return false;
        }
        true
    }
}

type N = f64;
type V = QFlag<N, F>;

#[allow(non_snake_case)]
fn connected_in_L2(g: &F, e1: &[usize; 2], e2: &[usize; 2]) -> bool {
    e1.iter().any(|u1| e2.iter().any(|u2| g.is_edge(*u1, *u2)))
}

fn degree_in_neighbourhood(t: Type<F>) -> V {
    assert_eq!(t.size, 2);
    let basis = Basis::new(4).with_type(t);
    basis.qflag_from_indicator(|g: &F, _| {
        (X_COLS.contains(&g.content.color[2]) || X_COLS.contains(&g.content.color[3]))
            && g.is_edge(2, 3)
            && connected_in_L2(g, &[0, 1], &[2, 3])
    })
}

fn edge_flag(color1: u8, color2: u8) -> F {
    let e: F = Colored::new(Graph::new(2, &[(0, 1)]), vec![color1, color2]).into();
    assert!(BPStrongDensityFlag::is_in_subclass(&e.content));
    return e;
}

fn edge_type(color1: u8, color2: u8) -> Type<F> {
    Type::from_flag(&edge_flag(color1, color2))
}

fn extension_in_color(t: Type<F>, color: u8) -> V {
    let b = Basis::new(t.size + 1).with_type(t);
    b.qflag_from_indicator(move |g: &F, type_size| g.content.color[type_size] == color)
}

fn extension_in_black(t: Type<F>) -> V {
    extension_in_color(t, 0).named(format!("ext_in_black({{{}}})", t.print_concise()))
}

fn extension_in_red(t: Type<F>) -> V {
    extension_in_color(t, 1).named(format!("ext_in_red({{{}}})", t.print_concise()))
}

fn unit_extension(t: Type<F>) -> V {
    let b: Basis<F> = Basis::new(t.size);
    let type_flag: &F = &b.get()[t.id].canonical();
    if COMP[type_flag.content.color[0] as usize] == 0 {
        return Degree::extension(t, 0);
    }
    assert!(COMP[type_flag.content.color[0] as usize] == 1);
    return Degree::extension(t, 0) * (1. / p_value());
}

fn objective(n: usize, xx_edge: Type<F>, xy_edges: [Type<F>; 2]) -> V {
    return xy_edges
        .into_iter()
        .chain(once(xx_edge))
        .map(|edge| (degree_in_neighbourhood(edge) * unit_extension(edge).pow(n - 4)).untype())
        .reduce(|a, b| a + b)
        .unwrap();
}

fn size_of_x(n: usize) -> Vec<Ineq<N, F>> {
    let mut res = Vec::new();
    for t in Type::types_with_size(n - 1) {
        let diff_b = unit_extension(t) - extension_in_black(t) * (1. / p_value());
        let diff_r = unit_extension(t) - extension_in_red(t);
        res.push(diff_b.untype().equal(0.));
        res.push(diff_r.untype().equal(0.));
    }
    res
}

fn ones(n: usize, k: usize, col: u8) -> V {
    let bk: F = Colored::new(Graph::empty(k), vec![col; k]).into();
    let t: Type<F> = Type::from_flag(&bk);
    let ext = unit_extension(t);
    flag_typed(&bk, k) * ext.pow(n - k)
}

fn asymmetric_regularity(n: usize) -> Vec<Ineq<f64, F>> {
    let b: Basis<F> = Basis::new(n - 1);
    let flags = b.get();
    let mut res = Vec::new();
    for (id, flag) in flags.iter().enumerate() {
        assert!(flag == &flag.canonical());
        let orbits = vertex_orbits(flag);
        if orbits.len() < 2 {
            continue;
        }
        let t: Type<F> = Type::new(n - 1, id);
        for i in 0..orbits.len() {
            for j in 0..i {
                let ext_i: V = Degree::extension(t, i);
                let coef_i = if COMP[flag.content.color[i] as usize] == 0 {
                    1.
                } else {
                    1. / p_value()
                };
                let ext_j: V = Degree::extension(t, j);
                let coef_j = if COMP[flag.content.color[j] as usize] == 0 {
                    1.
                } else {
                    1. / p_value()
                };
                res.push((ext_i * coef_i - ext_j * coef_j).untype().equal(0.));
            }
        }
    }
    res
}

fn solve(n: usize) -> N {
    let basis = Basis::<F>::new(n);

    let xx_edge = edge_type(X_COLS[0], X_COLS[1]);
    let xy_edges: [Type<F>; 2] = [
        edge_type(X_COLS[0], Y_COLS[1]),
        edge_type(X_COLS[1], Y_COLS[0]),
    ];

    let mut ineqs = vec![flags_are_nonnegative(basis)];

    ineqs.append(&mut asymmetric_regularity(n));
    ineqs.append(&mut size_of_x(n));
    ineqs.push(ones(n, 1, 0).untype().equal(p_value()));
    ineqs.push(ones(n, 1, 1).untype().equal(1.));

    let pb = Problem::<N, _> {
        ineqs,
        cs: basis.all_cs(),
        obj: -objective(n, xx_edge, xy_edges),
    }
    .no_scale();

    let mut f = FlagSolver::new(pb, "asymmetric_bipartite_bruhn_joos");
    f.init();
    f.print_report();

    let sprs = -f.optimal_value.unwrap();
    sprs
}

pub fn main() {
    init_default_log();
    let p = p_value();
    assert!(0. < p && p <= 1.);

    let n = 5;

    let sprs = solve(n);
    let lambda = sprs / 4.0;
    let lambda_over_2p2 = lambda / (2.0 * p * p);
    let bound = sprs / (8. * p * p);
    let sig = 1. - bound;
    let eps = sig / 2. - sig.pow(3. / 2.) / 6.;
    let chi_h = 1. - eps;
    let chi = 2. * chi_h;

    println!(
        "SWEEP_RESULT P={:.10} sprs={:.10} lambda={:.10} lambda_over_2P2={:.10} chi={:.10}",
        p, sprs, lambda, lambda_over_2p2, chi
    );
}
