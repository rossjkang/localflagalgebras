/// Dumps the size-5 (2,2)-coloured flag basis for both SEC subclasses to plain text.
///
/// The general SEC subclass uses `StrongEdgeColouringFlagNoRestrict` (i.e. the
/// `strong_edge_colouring.rs` predicate **without** the `RESTRICT_NON_F_EDGES`
/// optimisation). This is the subclass that matches the older SDPA cert in
/// `certificates/strong_edge_colouring.{sdpa,cert}` which advertises "17950
/// flags" (the newer `RESTRICT_NON_F_EDGES = true` predicate gives only 2,944
/// flags and breaks the cert correspondence).
///
/// Output files (written into the crate root):
///   sec_basis_size5_general.txt   — 17,950 flags
///   sec_basis_size5_bipartite.txt —  3,808 flags
///
/// Line format (skipping the `##` header):
///   <idx>;<size=5>;<edges as csv u8>;<colors as csv u8>
///
/// Edges: 10 entries, SymNonRefl<u8> flat order
///   (index for (u,v) with u<v is `v*(v-1)/2 + u`).
///   Values: 0=non-edge, 1=F_EDGE, 2=NON_F_EDGE.
/// Colours: 5 entries.
///   General SEC: values in {0,1} (X=0, Y=1).
///   Bipartite SEC: values in {0,1,2,3} (X_COLS={0,1}, Y_COLS={2,3}).
extern crate flag_algebra;
extern crate local_flags;

use flag_algebra::flags::{CGraph, Colored};
use flag_algebra::*;
use local_flags::Degree as _;
use std::fmt::Write;

// ---- General SEC subclass (no RESTRICT_NON_F_EDGES) ----
// Matches the basis ordering of the older
// `certificates/strong_edge_colouring.{sdpa,cert}` (17,950 flags).
type GG = Colored<CGraph<3>, 2>;

const X_G: u8 = 0;

#[derive(Debug, Clone, Copy)]
pub enum StrongEdgeColouringFlagNoRestrict {}
type FG = SubClass<GG, StrongEdgeColouringFlagNoRestrict>;

impl SubFlag<GG> for StrongEdgeColouringFlagNoRestrict {
    const SUBCLASS_NAME: &'static str = "Strong Edge Colouring Graphs No Restrict";
    const HEREDITARY: bool = false;
    fn is_in_subclass(flag: &GG) -> bool {
        flag.is_connected_to(|i| flag.color[i] == X_G)
    }
}

// ---- Bipartite SEC subclass (mirrors examples/bipartite_strong_edge_colouring.rs) ----
type GB = Colored<CGraph<3>, 4>;

const COMPS_B: [[u8; 2]; 2] = [[0, 2], [1, 3]];
const X_COLS_B: [u8; 2] = [0, 1];

#[derive(Debug, Clone, Copy)]
pub enum BipartSECFlag {}
type FB = SubClass<GB, BipartSECFlag>;

impl SubFlag<GB> for BipartSECFlag {
    const SUBCLASS_NAME: &'static str = "Bipartite SEC Graphs";
    const HEREDITARY: bool = false;
    fn is_in_subclass(flag: &GB) -> bool {
        if !flag.is_connected_to(|i| X_COLS_B.contains(&flag.color[i])) {
            return false;
        }
        for u in 0..flag.size() {
            for v in 0..u {
                if flag.edge(u, v) == 0 {
                    continue;
                }
                if COMPS_B.iter().any(|comp| comp.contains(&flag.color[u]) && comp.contains(&flag.color[v])) {
                    return false;
                }
            }
        }
        true
    }
}

fn dump_general() -> (usize, String) {
    let basis: Vec<FG> = Basis::<FG>::new(5).get();
    let mut out = String::new();
    writeln!(&mut out, "## {}: {} flags", <StrongEdgeColouringFlagNoRestrict as SubFlag<GG>>::SUBCLASS_NAME, basis.len()).unwrap();
    for (idx, f) in basis.iter().enumerate() {
        let inner = &f.content;
        let cg: &CGraph<3> = &inner.content;
        let n = cg.size;
        let mut edges = Vec::new();
        for j in 0..n {
            for i in 0..j {
                edges.push(cg.edge(i, j));
            }
        }
        let colors = &inner.color;
        let edge_str: String = edges.iter().map(|b| b.to_string()).collect::<Vec<_>>().join(",");
        let col_str: String = colors.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(",");
        writeln!(&mut out, "{};{};{};{}", idx, n, edge_str, col_str).unwrap();
    }
    (basis.len(), out)
}

fn dump_bipart() -> (usize, String) {
    let basis: Vec<FB> = Basis::<FB>::new(5).get();
    let mut out = String::new();
    writeln!(&mut out, "## {}: {} flags", <BipartSECFlag as SubFlag<GB>>::SUBCLASS_NAME, basis.len()).unwrap();
    for (idx, f) in basis.iter().enumerate() {
        let inner = &f.content;
        let cg: &CGraph<3> = &inner.content;
        let n = cg.size;
        let mut edges = Vec::new();
        for j in 0..n {
            for i in 0..j {
                edges.push(cg.edge(i, j));
            }
        }
        let colors = &inner.color;
        let edge_str: String = edges.iter().map(|b| b.to_string()).collect::<Vec<_>>().join(",");
        let col_str: String = colors.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(",");
        writeln!(&mut out, "{};{};{};{}", idx, n, edge_str, col_str).unwrap();
    }
    (basis.len(), out)
}

pub fn main() {
    init_default_log();

    let (cg, txt_g) = dump_general();
    println!("General (StrongEdgeColouringFlagNoRestrict): {} flags", cg);
    assert_eq!(cg, 17950, "expected 17950 general-SEC size-5 flags (cert correspondence)");

    let (cb, txt_b) = dump_bipart();
    println!("Bipartite (BipartSECFlag): {} flags", cb);
    assert_eq!(cb, 3808, "expected 3808 bipartite-SEC size-5 flags (cert correspondence)");

    std::fs::write("sec_basis_size5_general.txt", &txt_g).expect("write general");
    std::fs::write("sec_basis_size5_bipartite.txt", &txt_b).expect("write bipartite");
    println!("Wrote sec_basis_size5_general.txt ({} bytes)", txt_g.len());
    println!("Wrote sec_basis_size5_bipartite.txt ({} bytes)", txt_b.len());
}
