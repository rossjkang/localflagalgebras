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
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            k += 1
    return n, adj

best = 0
best_g = None
for line in sys.stdin:
    n, adj = parse_graph6(line)
    pv = [0]*n
    for S in itertools.combinations(range(n), 5):
        mask = 0
        for u in S: mask |= 1 << u
        # induced C5 <=> every vertex of S has induced degree exactly 2 and connected;
        # 5 vertices all degree 2 => disjoint cycles covering 5 vertices => single C5 (no C3 since TF, C3+C2 impossible anyway as parts)
        ok = True
        for u in S:
            if bin(adj[u] & mask).count('1') != 2:
                ok = False; break
        if ok:
            for u in S: pv[u] += 1
    m = max(pv) if n else 0
    if m > best:
        best = m
        best_g = line.strip()
print("max P(v) =", best, "attained by", best_g)
