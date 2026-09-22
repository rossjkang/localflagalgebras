//! Dump the two independently reweightable pieces of the size-8 pentagon
//! objective.  If `root` denotes the BRRB path term and `neighbour` the two
//! coloured-C5 terms, then `t*root + (2-t)*neighbour` has the same global
//! sum as the incumbent objective for every real `t`.

use flag_algebra::flags::{Colored, Graph};
use flag_algebra::*;
use itertools::iproduct;
use local_flags::Degree;

type G = Colored<Graph, 2>;

#[derive(Debug, Clone, Copy)]
pub enum TriangleFreeConnected {}

type F = SubClass<G, TriangleFreeConnected>;
type V = QFlag<f64, F>;

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
        for (u, v, w) in iproduct!(0..n, 0..n, 0..n) {
            if u == v || u == w || v == w {
                continue;
            }
            if flag.content.edge(u, v)
                && flag.content.edge(u, w)
                && flag.content.edge(v, w)
            {
                return false;
            }
        }
        true
    }
}

fn components(n: usize) -> (V, V) {
    let path: F = Colored::new(
        Graph::new(4, &[(0, 1), (1, 2), (2, 3)]),
        vec![0, 1, 1, 0],
    )
    .into();
    let one_black: F = Colored::new(
        Graph::new(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]),
        vec![0, 1, 1, 1, 1],
    )
    .into();
    let two_black: F = Colored::new(
        Graph::new(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]),
        vec![0, 1, 0, 1, 1],
    )
    .into();

    let root = Degree::project(&path, n).untype().no_scale();
    let neighbour = (Degree::project(&one_black, n).untype()
        + Degree::project(&two_black, n).untype() * 2.0)
        .no_scale();
    (root, neighbour)
}

fn main() {
    init_default_log();
    let (root, neighbour) = components(8);
    assert_eq!(root.basis, neighbour.basis);
    assert_eq!(root.scale, 1);
    assert_eq!(neighbour.scale, 1);
    println!("# index root neighbour");
    for (index, (a, b)) in root.data.iter().zip(neighbour.data.iter()).enumerate() {
        println!("{index} {a:.17e} {b:.17e}");
    }
}
