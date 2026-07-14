// Dumps the size-5 basis flag colour signatures.
//
// For Phase 2: compute κ_j = (count of low-side vertices) mod 2 from
// each flag's colour vector. Output format:
//   FLAG <j> <colour_0> <colour_1> ... <colour_{n-1}>

use flag_algebra::flags::{Colored, Graph};
use flag_algebra::*;
use local_flags::Degree;

type G = Colored<Graph, 4>;

const COMP: [u8; 4] = [0, 1, 0, 1];
const X_COLS: [u8; 2] = [0, 1];

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

pub fn main() {
    init_default_log();
    let n = 5;
    let b: Basis<F> = Basis::new(n);
    let flags = b.get();

    eprintln!("Basis size at n={}: {}", n, flags.len());

    for (j, flag) in flags.iter().enumerate() {
        let colours: Vec<u8> = flag.content.color.iter().copied().collect();
        let low_side_count: usize = colours.iter().filter(|&&c| COMP[c as usize] == 1).count();
        let kappa = low_side_count % 2;
        // Also report edge count for context
        let edges: Vec<(usize, usize)> = flag.content.content.edges().collect();
        print!("FLAG {} colours=", j);
        for c in &colours {
            print!("{}", c);
        }
        print!(" low_count={} kappa={} edges=[", low_side_count, kappa);
        for (i, (u, v)) in edges.iter().enumerate() {
            if i > 0 {
                print!(",");
            }
            print!("{}-{}", u, v);
        }
        println!("]");
    }
}
