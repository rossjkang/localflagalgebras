// Dumps the SDP objective and constraint coefficients at a given P value.
//
// Used by the development notes Phase 1 to test whether the
// asymmetric SDP's per-flag coefficients scale as monomials c_j · r^{e_j}
// — the cleanest possible mechanism for the empirical r^2 scaling of
// the SDP optimum.
//
// Reads P from env var BIPARTITE_DENSITY_P (default 0.5) and writes a
// CSV "j,coeff" of objective coefficients to stdout (prefix
// "OBJ_COEFF").

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

pub fn main() {
    init_default_log();
    let p = p_value();
    assert!(0. < p && p <= 1.);

    let n = 5;

    let xx_edge = edge_type(X_COLS[0], X_COLS[1]);
    let xy_edges: [Type<F>; 2] = [
        edge_type(X_COLS[0], Y_COLS[1]),
        edge_type(X_COLS[1], Y_COLS[0]),
    ];

    let obj = objective(n, xx_edge, xy_edges);

    eprintln!("=== Objective dump at P = {} ===", p);
    eprintln!("basis size = {}", obj.data.len());

    println!("# OBJ_COEFF_DUMP P={} n={}", p, n);
    println!("# basis_size = {}", obj.data.len());
    println!("j,coeff");
    for (j, c) in obj.data.iter().enumerate() {
        // Only print nonzero coefficients
        if c.abs() > 1e-15 {
            println!("OBJ_COEFF {} {} {:.18e}", p, j, c);
        }
    }
}
