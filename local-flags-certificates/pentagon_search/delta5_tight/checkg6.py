import sys, itertools
def parse_graph6(line):
    line = line.strip()
    data = [ord(c) - 63 for c in line]
    n = data[0]
    bits = []
    for b in data[1:]:
        bits += [(b >> i) & 1 for i in range(5, -1, -1)]
    adj = [0]*n
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i] |= 1 << j; adj[j] |= 1 << i
            k += 1
    return n, adj
for line in sys.stdin:
    n, adj = parse_graph6(line)
    pv = [0]*n
    P = 0
    for S in itertools.combinations(range(n), 5):
        mask = 0
        for u in S: mask |= 1 << u
        if all(bin(adj[u] & mask).count('1') == 2 for u in S):
            P += 1
            for u in S: pv[u] += 1
    degs = sorted(bin(a).count('1') for a in adj)
    print(f"{line.strip()}: n={n} P={P} maxP(v)={max(pv)} pv={sorted(pv)} degs={degs[0]}..{degs[-1]}")
