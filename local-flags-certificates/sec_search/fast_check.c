/* fast_check.c — fast greedy χ'_s ≤ bound check via DSATUR.
 *
 * Reads graph6-encoded graphs from stdin (one per line), runs the
 * same pipeline as fast_check.py:
 *   1. L²(G)-complete shortcut → χ'_s = |E|.
 *   2. DSATUR greedy with degree-saturation + multi-shot random orderings.
 *      If colouring ≤ bound exists, PASS.
 *   3. Otherwise: report CANDIDATE g6=... (left to SAT downstream).
 *
 * Writes per-graph status to stdout in CSV:
 *   graph6,n,m,delta,girth_dummy,chi_s_le_bound,decision_path
 *
 * Aggregate stats to stderr.
 *
 * Compile: clang -O3 -march=native -o fast_check fast_check.c
 * Use:     geng -d4 -D4 -c 16 | ./fast_check 20
 *
 * Supports graphs with up to 64 edges (i.e. |V(L²)| ≤ 64), which
 * covers all 4-regular n ≤ 32 (|E|=64), 5-regular n ≤ 25 (|E|=62.5).
 * For larger graphs, fall back to Python (fast_check.py) or extend to
 * multi-word bitsets.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAX_N 64       /* graph vertices */
#define MAX_M 512      /* edges / colours — 8-word bitset for Δ up to ~22 */
#define MAX_SHOTS 32   /* DSATUR random restarts (cap) */
#define EBS_WORDS 8    /* 8 * 64 = 512 bits */

/* Vertex bitsets (over n ≤ 64 vertices) — single word. */
typedef uint64_t bitset_t;

/* Edge / colour bitsets — 256-bit (4 × uint64_t). */
typedef struct {
    uint64_t w[EBS_WORDS];
} ebitset_t;

static inline ebitset_t ebs_zero(void) {
    ebitset_t r;
    for (int i = 0; i < EBS_WORDS; i++) r.w[i] = 0;
    return r;
}
static inline ebitset_t ebs_singleton(int bit) {
    ebitset_t r = ebs_zero();
    r.w[bit >> 6] = (uint64_t)1 << (bit & 63);
    return r;
}
static inline ebitset_t ebs_or(ebitset_t a, ebitset_t b) {
    for (int i = 0; i < EBS_WORDS; i++) a.w[i] |= b.w[i];
    return a;
}
static inline void ebs_or_inplace(ebitset_t *a, ebitset_t b) {
    for (int i = 0; i < EBS_WORDS; i++) a->w[i] |= b.w[i];
}
static inline ebitset_t ebs_not(ebitset_t a) {
    for (int i = 0; i < EBS_WORDS; i++) a.w[i] = ~a.w[i];
    return a;
}
static inline int ebs_is_zero(ebitset_t a) {
    uint64_t x = 0;
    for (int i = 0; i < EBS_WORDS; i++) x |= a.w[i];
    return x == 0;
}
static inline int ebs_test(ebitset_t a, int bit) {
    return (a.w[bit >> 6] >> (bit & 63)) & 1;
}
static inline int ebs_popcount(ebitset_t a) {
    int s = 0;
    for (int i = 0; i < EBS_WORDS; i++) s += __builtin_popcountll(a.w[i]);
    return s;
}
static inline int ebs_ctz(ebitset_t a) {
    for (int i = 0; i < EBS_WORDS; i++) {
        if (a.w[i]) return i * 64 + __builtin_ctzll(a.w[i]);
    }
    return EBS_WORDS * 64;
}
/* Clear the lowest set bit (equivalent to a &= a - 1). */
static inline ebitset_t ebs_clear_lowest(ebitset_t a) {
    for (int i = 0; i < EBS_WORDS; i++) {
        if (a.w[i]) { a.w[i] &= a.w[i] - 1; return a; }
    }
    return a;
}
/* Test whether two edges (vertex-side) intersect: any common bit. */
static inline int bs_intersects(bitset_t a, bitset_t b) { return (a & b) != 0; }

/* ---------------- graph6 parser ---------------- */

/* Parse graph6 line into adj[]: adj[v] is a bitset of v's neighbours
 * (assuming n ≤ MAX_N). Returns n on success, -1 on parse failure. */
static int parse_graph6(const char *line, bitset_t adj[MAX_N]) {
    if (!line || !*line) return -1;
    int n;
    const char *p = line;
    if ((unsigned char)*p < 63) return -1;
    /* n encoding */
    if (*p < 126) {
        n = *p - 63;
        p++;
    } else {
        /* multi-byte n encoding — not supported here (n>62) */
        return -1;
    }
    if (n < 0 || n > MAX_N) return -1;

    for (int v = 0; v < n; v++) adj[v] = 0;

    /* Edges encoded column-major: for j = 1..n-1, for i = 0..j-1,
     * one bit. Each char = 6 bits (high bit first). */
    int bit_idx = 0;
    int total_bits = n * (n - 1) / 2;
    int byte_bits = 0;
    int byte_val = 0;
    for (int j = 1; j < n; j++) {
        for (int i = 0; i < j; i++) {
            if (byte_bits == 0) {
                if (*p < 63) return -1;
                byte_val = *p - 63;
                p++;
                byte_bits = 6;
            }
            byte_bits--;
            int b = (byte_val >> byte_bits) & 1;
            if (b) {
                adj[i] |= ((bitset_t)1) << j;
                adj[j] |= ((bitset_t)1) << i;
            }
            bit_idx++;
        }
    }
    (void)bit_idx;
    (void)total_bits;
    return n;
}

/* ---------------- enumerate edges ---------------- */

/* Fill edges[].u and edges[].v (canonical u<v) from adj[]. Returns m. */
typedef struct { int u, v; } edge_t;

static int extract_edges(int n, const bitset_t adj[MAX_N], edge_t edges[MAX_M]) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        bitset_t hi = adj[u] & ~((((bitset_t)1) << (u + 1)) - 1);
        while (hi) {
            int v = __builtin_ctzll(hi);
            hi &= hi - 1;
            if (m >= MAX_M) return -1;
            edges[m].u = u;
            edges[m].v = v;
            m++;
        }
    }
    return m;
}

/* ---------------- build L²(G) adjacency (bitset) ---------------- */

/* sadj[e] = bitmask of edges strong-adjacent to e (over up to MAX_M edges). */
static void build_L_squared(int n, const bitset_t adj[MAX_N],
                            int m, const edge_t edges[MAX_M],
                            ebitset_t sadj[MAX_M]) {
    bitset_t reach[MAX_M];
    for (int e = 0; e < m; e++) {
        int u = edges[e].u, v = edges[e].v;
        reach[e] = adj[u] | adj[v] | (((bitset_t)1) << u) | (((bitset_t)1) << v);
        sadj[e] = ebs_zero();
    }
    for (int e = 0; e < m; e++) {
        for (int f = e + 1; f < m; f++) {
            int x = edges[f].u, y = edges[f].v;
            bitset_t fmask = (((bitset_t)1) << x) | (((bitset_t)1) << y);
            if (reach[e] & fmask) {
                ebs_or_inplace(&sadj[e], ebs_singleton(f));
                ebs_or_inplace(&sadj[f], ebs_singleton(e));
            }
        }
    }
}

/* ---------------- DSATUR ---------------- */

/* DSATUR greedy with saturation-degree ordering. Returns the number
 * of colours used, or -1 if would exceed max_colours.
 * Operates on a graph of m vertices with adjacency sadj[i] (bitset). */
static int dsatur_colour(int m, const ebitset_t sadj[MAX_M], int max_colours) {
    int colour[MAX_M];
    ebitset_t sat[MAX_M];     /* forbidden COLOUR-bitset (up to 256 colours) */
    int sat_count[MAX_M];
    int deg[MAX_M];
    for (int v = 0; v < m; v++) {
        colour[v] = -1;
        sat[v] = ebs_zero();
        sat_count[v] = 0;
        deg[v] = ebs_popcount(sadj[v]);
    }
    int used = 0;
    for (int round = 0; round < m; round++) {
        int best = -1, best_sat = -1, best_deg = -1;
        for (int v = 0; v < m; v++) {
            if (colour[v] >= 0) continue;
            if (sat_count[v] > best_sat ||
                (sat_count[v] == best_sat && deg[v] > best_deg)) {
                best = v;
                best_sat = sat_count[v];
                best_deg = deg[v];
            }
        }
        ebitset_t inverted = ebs_not(sat[best]);
        if (ebs_is_zero(inverted)) return -1;  /* all 256 colours forbidden */
        int c = ebs_ctz(inverted);
        if (c >= max_colours) return -1;
        colour[best] = c;
        if (c + 1 > used) used = c + 1;
        ebitset_t nbrs = sadj[best];
        while (!ebs_is_zero(nbrs)) {
            int w = ebs_ctz(nbrs);
            nbrs = ebs_clear_lowest(nbrs);
            if (colour[w] < 0) {
                if (!ebs_test(sat[w], c)) {
                    ebs_or_inplace(&sat[w], ebs_singleton(c));
                    sat_count[w]++;
                }
            }
        }
    }
    return used;
}

/* First-fit greedy with explicit order. Returns colours used or -1. */
static int firstfit_colour(int m, const ebitset_t sadj[MAX_M],
                            const int order[MAX_M], int max_colours) {
    int colour[MAX_M];
    for (int i = 0; i < m; i++) colour[i] = -1;
    int used = 0;
    for (int idx = 0; idx < m; idx++) {
        int v = order[idx];
        ebitset_t forbidden = ebs_zero();
        ebitset_t nbrs = sadj[v];
        while (!ebs_is_zero(nbrs)) {
            int w = ebs_ctz(nbrs);
            nbrs = ebs_clear_lowest(nbrs);
            if (colour[w] >= 0) ebs_or_inplace(&forbidden, ebs_singleton(colour[w]));
        }
        ebitset_t inv = ebs_not(forbidden);
        if (ebs_is_zero(inv)) return -1;
        int c = ebs_ctz(inv);
        if (c >= max_colours) return -1;
        colour[v] = c;
        if (c + 1 > used) used = c + 1;
    }
    return used;
}

/* xorshift64 fast PRNG */
static uint64_t rng_state = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rng_next() {
    uint64_t x = rng_state;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    rng_state = x;
    return x;
}

/* Multi-shot greedy: DSATUR first, then up to (shots-1) random first-fit.
 * Returns min colours used across attempts that succeed at ≤ max_colours,
 * or -1 if none succeed. */
static int multi_shot_greedy(int m, const ebitset_t sadj[MAX_M],
                              int max_colours, int shots) {
    int best = dsatur_colour(m, sadj, max_colours);
    if (best > 0 && best <= max_colours) return best;
    int order[MAX_M];
    for (int s = 1; s < shots; s++) {
        for (int i = 0; i < m; i++) order[i] = i;
        /* Fisher-Yates */
        for (int i = m - 1; i > 0; i--) {
            int j = (int)(rng_next() % (uint64_t)(i + 1));
            int tmp = order[i]; order[i] = order[j]; order[j] = tmp;
        }
        int r = firstfit_colour(m, sadj, order, max_colours);
        if (r > 0 && (best < 0 || r < best)) {
            best = r;
            if (best <= max_colours) return best;
        }
    }
    return best;
}

/* ---------------- main loop ---------------- */

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr,
            "Usage: %s <bound> [--csv] [--every N] [--shots N]\n"
            "Reads graph6 from stdin. Writes CSV/log to stdout/stderr.\n",
            argv[0]);
        return 1;
    }
    int bound = atoi(argv[1]);
    int csv = 0, shots = 20;
    long every = 100000;
    for (int i = 2; i < argc; i++) {
        if (strcmp(argv[i], "--csv") == 0) csv = 1;
        else if (strcmp(argv[i], "--every") == 0 && i + 1 < argc)
            every = atol(argv[++i]);
        else if (strcmp(argv[i], "--shots") == 0 && i + 1 < argc)
            shots = atoi(argv[++i]);
    }
    if (csv) {
        printf("graph6,n,m,bound,passed_path\n");
        fflush(stdout);
    }

    char line[8192];
    long count = 0;
    long candidates = 0;
    long path_shortcut = 0, path_greedy = 0, path_unresolved = 0;
    bitset_t adj[MAX_N];
    edge_t edges[MAX_M];
    ebitset_t sadj[MAX_M];

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    while (fgets(line, sizeof(line), stdin)) {
        /* strip trailing newline */
        size_t L = strlen(line);
        while (L > 0 && (line[L-1] == '\n' || line[L-1] == '\r'))
            line[--L] = '\0';
        if (L == 0) continue;

        int n = parse_graph6(line, adj);
        if (n < 0) {
            fprintf(stderr, "# parse error: %s\n", line);
            continue;
        }
        int m = extract_edges(n, adj, edges);
        if (m < 0) {
            fprintf(stderr, "# too many edges (%d > %d): %s\n",
                    m, MAX_M, line);
            continue;
        }
        const char *path;
        int passed;
        if (m == 0) {
            passed = 1; path = "empty"; path_shortcut++;
        } else {
            build_L_squared(n, adj, m, edges, sadj);
            /* count strong-pairs */
            long s_pairs = 0;
            for (int e = 0; e < m; e++)
                s_pairs += ebs_popcount(sadj[e]);
            s_pairs /= 2;
            long all_pairs = (long)m * (m - 1) / 2;
            if (s_pairs == all_pairs) {
                /* L²(G) complete → χ'_s = m */
                passed = (m <= bound);
                path = "shortcut";
                path_shortcut++;
            } else {
                int r = multi_shot_greedy(m, sadj, bound, shots);
                if (r > 0 && r <= bound) {
                    passed = 1; path = "greedy"; path_greedy++;
                } else {
                    passed = 0; path = "unresolved"; path_unresolved++;
                }
            }
        }
        if (csv) {
            printf("%s,%d,%d,%d,%s\n", line, n, m, bound,
                   passed ? path : "FAIL_unresolved");
        }
        if (!passed) {
            candidates++;
            fprintf(stderr, "!!! CANDIDATE COUNTEREXAMPLE: g6=%s n=%d m=%d "
                    "(χ'_s > %d via path=%s) !!!\n", line, n, m, bound, path);
        }
        count++;
        if (count % every == 0) {
            clock_gettime(CLOCK_MONOTONIC, &t1);
            double dt = (t1.tv_sec - t0.tv_sec)
                      + (t1.tv_nsec - t0.tv_nsec) / 1e9;
            fprintf(stderr, "# %ld graphs done, %ld candidates, "
                    "elapsed=%.1fs, rate=%.0fg/s\n",
                    count, candidates, dt, count / (dt > 0 ? dt : 1));
        }
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double dt = (t1.tv_sec - t0.tv_sec) + (t1.tv_nsec - t0.tv_nsec) / 1e9;
    fprintf(stderr, "# done: %ld graphs in %.1fs (rate %.0fg/s)\n",
            count, dt, count / (dt > 0 ? dt : 1));
    fprintf(stderr, "# decision paths: shortcut=%ld greedy=%ld unresolved=%ld\n",
            path_shortcut, path_greedy, path_unresolved);
    if (candidates > 0)
        fprintf(stderr, "# %ld CANDIDATE COUNTEREXAMPLES (chi_s > %d)\n",
                candidates, bound);
    else
        fprintf(stderr, "# NO counterexamples found (all chi_s ≤ %d)\n", bound);
    return candidates > 0 ? 0 : 0;
}
