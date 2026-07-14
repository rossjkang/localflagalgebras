// Dumps constraint LHS coefficients at a given P value.
//
// For Phase 1.5: classify each linear constraint (asymmetric_regularity,
// size_of_x, ones) by whether its nonzero coefficients are pure r^0,
// pure r^{-1}, or mixed.

use canonical_form::Canonize;
use flag_algebra::flags::{Colored, Graph};
use flag_algebra::*;
use local_flags::{vertex_orbits, Degree};
use num::pow::Pow;
use std::sync::OnceLock;

type G = Colored<Graph, 4>;

const COMP: [u8; 4] = [0, 1, 0, 1];
const X_COLS: [u8; 2] = [0, 1];

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

fn extension_in_color(t: Type<F>, color: u8) -> V {
    let b = Basis::new(t.size + 1).with_type(t);
    b.qflag_from_indicator(move |g: &F, type_size| g.content.color[type_size] == color)
}

fn extension_in_black(t: Type<F>) -> V {
    extension_in_color(t, 0)
}

fn extension_in_red(t: Type<F>) -> V {
    extension_in_color(t, 1)
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

// Return constraint LHS as V (QFlag) instead of Ineq so we can read .data.
fn size_of_x_v(n: usize) -> Vec<V> {
    let mut res = Vec::new();
    for t in Type::types_with_size(n - 1) {
        let diff_b = unit_extension(t) - extension_in_black(t) * (1. / p_value());
        let diff_r = unit_extension(t) - extension_in_red(t);
        res.push(diff_b.untype());
        res.push(diff_r.untype());
    }
    res
}

fn asymmetric_regularity_v(n: usize) -> Vec<V> {
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
                res.push((ext_i * coef_i - ext_j * coef_j).untype());
            }
        }
    }
    res
}

fn dump_v(name: &str, idx: usize, v: &V, p: f64) {
    for (j, c) in v.data.iter().enumerate() {
        if c.abs() > 1e-15 {
            println!("CONSTR {} {} {} {} {:.18e}", name, idx, p, j, c);
        }
    }
}

pub fn main() {
    init_default_log();
    let p = p_value();
    assert!(0. < p && p <= 1.);

    let n = 5;

    let regs = asymmetric_regularity_v(n);
    for (idx, v) in regs.iter().enumerate() {
        dump_v("REGULARITY", idx, v, p);
    }

    let sox = size_of_x_v(n);
    for (idx, v) in sox.iter().enumerate() {
        dump_v("SIZE_OF_X", idx, v, p);
    }

    eprintln!("dumped {} regularity constraints, {} size_of_x constraints",
              regs.len(), sox.len());
}
