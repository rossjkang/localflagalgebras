//! Dump the C4 root/neighbour stationarity pair for the size-8 pentagon SDP.
//!
//! For f(v) = #C4 through v, the double count sum_v [Delta f(v) -
//! sum_{u~v} f(u)] = 0 gives a reweight direction with vanishing
//! (leading-order) global sum.  Delta-side: black-red-black path (a C4
//! through the implicit root), 5 star extras.  Neighbour side: the two
//! independent-black-set C4 colourings, coefficient = #black vertices,
//! 4 star extras.  Exactly parallel to dump_bounded_pentagon_components.

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
    let brb: F = Colored::new(Graph::new(3, &[(0, 1), (1, 2)]), vec![0, 1, 0]).into();
    let c4_one: F = Colored::new(
        Graph::new(4, &[(0, 1), (1, 2), (2, 3), (3, 0)]),
        vec![0, 1, 1, 1],
    )
    .into();
    let c4_two: F = Colored::new(
        Graph::new(4, &[(0, 1), (1, 2), (2, 3), (3, 0)]),
        vec![0, 1, 0, 1],
    )
    .into();

    let dside = Degree::project(&brb, n).untype().no_scale();
    // Corrected coefficients (1,1): the two-black C4 has twice the ordered
    // root-embeddings per copy, so weight 1 (not 2) restores the contact sum.
    let nside = (Degree::project(&c4_one, n).untype()
        + Degree::project(&c4_two, n).untype())
        .no_scale();
    (dside, nside)
}

fn main() {
    init_default_log();
    let (dside, nside) = components(8);
    assert_eq!(dside.basis, nside.basis);
    assert_eq!(dside.scale, 1);
    assert_eq!(nside.scale, 1);
    println!("# index c4_delta_side c4_neighbour_side");
    for (index, (a, b)) in dside.data.iter().zip(nside.data.iter()).enumerate() {
        println!("{index} {a:.17e} {b:.17e}");
    }
}
