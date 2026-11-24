"""Brute-force counterexample search for the 8 open WOWII conjectures in
google-deepmind/formal-conjectures. Invariants follow the Lean definitions in
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/*. Graphs: all connected
graphs on n vertices from nauty-geng (graph6 on stdin).

Usage: nauty-geng -c N -q | python3 wow_search.py N
"""
import sys
from fractions import Fraction as F
from math import ceil


def parse_g6(line):
    s = line.strip()
    data = [ord(c) - 63 for c in s]
    n = data[0]
    bits = []
    for d in data[1:]:
        for k in range(5, -1, -1):
            bits.append((d >> k) & 1)
    adj = [0] * n
    idx = 0
    for j in range(1, n):
        for i in range(j):
            if bits[idx]:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            idx += 1
    return n, adj


def popcount(x):
    return bin(x).count("1")


def bfs_dist(n, adj, s):
    dist = [-1] * n
    dist[s] = 0
    frontier = 1 << s
    seen = frontier
    d = 0
    while frontier:
        d += 1
        nxt = 0
        f = frontier
        while f:
            v = (f & -f).bit_length() - 1
            f &= f - 1
            nxt |= adj[v]
        nxt &= ~seen
        seen |= nxt
        f = nxt
        while f:
            v = (f & -f).bit_length() - 1
            f &= f - 1
            dist[v] = d
        frontier = nxt
    return dist


def induced_connected(adj, S):
    if S == 0:
        return False
    start = S & -S
    seen = start
    frontier = start
    while frontier:
        v = (frontier & -frontier).bit_length() - 1
        frontier &= frontier - 1
        new = adj[v] & S & ~seen
        seen |= new
        frontier |= new
    return seen == S


def induced_edges(adj, S):
    e = 0
    f = S
    while f:
        v = (f & -f).bit_length() - 1
        f &= f - 1
        e += popcount(adj[v] & S)
    return e // 2


def is_independent(adj, S):
    f = S
    while f:
        v = (f & -f).bit_length() - 1
        f &= f - 1
        if adj[v] & S:
            return False
    return True


def components(adj, S):
    comps = []
    rem = S
    while rem:
        start = rem & -rem
        seen = start
        frontier = start
        while frontier:
            v = (frontier & -frontier).bit_length() - 1
            frontier &= frontier - 1
            new = adj[v] & S & ~seen
            seen |= new
            frontier |= new
        comps.append(seen)
        rem &= ~seen
    return comps


def is_forest(adj, S):
    # acyclic iff edges = |S| - #components
    return induced_edges(adj, S) == popcount(S) - len(components(adj, S))


def is_bipartite(adj, S):
    color = {}
    f = S
    while f:
        s = (f & -f).bit_length() - 1
        f &= f - 1
        if s in color:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            v = stack.pop()
            nb = adj[v] & S
            while nb:
                w = (nb & -nb).bit_length() - 1
                nb &= nb - 1
                if w not in color:
                    color[w] = 1 - color[v]
                    stack.append(w)
                elif color[w] == color[v]:
                    return False
    return True


def indep_num_of(adj, S):
    # max independent subset of S
    best = 0
    sub = S
    while True:
        if is_independent(adj, sub):
            best = max(best, popcount(sub))
        if sub == 0:
            break
        sub = (sub - 1) & S
    return best


def ham_path_table(n, adj):
    """hp[S] = True iff induced-on-S subgraph (non-induced edges allowed among S) has a
    Hamiltonian path, i.e. S is the vertex set of some path in G."""
    full = 1 << n
    # end[S] = bitmask of vertices v in S such that a path covering S ends at v
    end = [0] * full
    for v in range(n):
        end[1 << v] = 1 << v
    for S in range(1, full):
        e = end[S]
        if not e:
            continue
        f = e
        while f:
            v = (f & -f).bit_length() - 1
            f &= f - 1
            nb = adj[v] & ~S
            while nb:
                w = (nb & -nb).bit_length() - 1
                nb &= nb - 1
                end[S | (1 << w)] |= 1 << w
    return [x != 0 for x in end]


def path_cover_number(n, hp):
    full = (1 << n) - 1
    INF = 99
    f = [INF] * (1 << n)
    f[0] = 0
    for S in range(1, 1 << n):
        low = S & -S
        best = INF
        sub = S
        while sub:
            if sub & low and hp[sub]:
                c = f[S & ~sub] + 1
                if c < best:
                    best = c
            sub = (sub - 1) & S
        f[S] = best
    return f[full]


def is_induced_path(adj, S):
    k = popcount(S)
    if k == 1:
        return True
    if not induced_connected(adj, S):
        return False
    if induced_edges(adj, S) != k - 1:
        return False
    f = S
    while f:
        v = (f & -f).bit_length() - 1
        f &= f - 1
        if popcount(adj[v] & S) > 2:
            return False
    return True


def has_c4(n, adj):
    # not necessarily induced 4-cycle: two vertices a,c with >=2 common neighbours
    for a in range(n):
        for c in range(a + 1, n):
            if popcount(adj[a] & adj[c]) >= 2:
                return True
    return False


def vertex_connectivity(n, adj):
    if n <= 1:
        return 0
    full = (1 << n) - 1
    best = n - 1
    for S in range(1 << n):
        k = popcount(S)
        if k >= best:
            continue
        comp = full & ~S
        if not induced_connected(adj, comp):
            best = k
    return best


def residue(degs):
    s = sorted(degs, reverse=True)
    while True:
        if not s:
            return 0
        if s[0] == 0:
            return len(s)
        d, rest = s[0], s[1:]
        dec = [x - 1 for x in rest[:d]]
        # Lean uses Nat subtraction: 0 - 1 = 0
        dec = [max(x, 0) for x in dec]
        s = sorted(dec + rest[d:], reverse=True)


def check(n, adj):
    full = (1 << n) - 1
    dists = [bfs_dist(n, adj, s) for s in range(n)]
    ecc = [max(d) for d in dists]
    rad = min(ecc)
    diam = max(ecc)
    degs = [popcount(a) for a in adj]
    mindeg = min(degs)
    sigma = sorted(degs)[1]
    dist_even = [sum(1 for x in dists[v] if x % 2 == 0) for v in range(n)]
    lv = [indep_num_of(adj, adj[v]) for v in range(n)]
    max_l = max(lv)
    avg_l = F(sum(lv), n)

    tree = forest = bip = alpha = pth = 0
    for S in range(1, 1 << n):
        k = popcount(S)
        if k > forest and is_forest(adj, S):
            forest = k
            if k > tree and induced_connected(adj, S):
                tree = k
        elif k > tree and induced_connected(adj, S) and is_forest(adj, S):
            tree = k
        if k > bip and is_bipartite(adj, S):
            bip = k
        if k > alpha and is_independent(adj, S):
            alpha = k
        if k > pth and is_induced_path(adj, S):
            pth = k
    hp = ham_path_table(n, adj)
    ham = hp[full]
    pc = path_cover_number(n, hp)
    kappa = vertex_connectivity(n, adj)
    res = residue(degs)
    avg_ecc = F(sum(ecc), n)
    c4 = has_c4(n, adj)

    fails = []
    # 40: ceil((pc + b + 1)/2) <= forest
    if ceil(F(pc + bip + 1, 2)) > forest:
        fails.append("C40")
    # 61: residue + ceil(diam/3) <= forest
    if res + ceil(F(diam, 3)) > forest:
        fails.append("C61")
    # 72: ceil(avgEcc + maxL/3) <= tree
    if ceil(avg_ecc + F(max_l, 3)) > tree:
        fails.append("C72")
    # 84: 2 rad / mindeg <= tree
    if F(2 * rad, mindeg) > tree:
        fails.append("C84")
    # 96: alpha <= 1 + minDistEven * (maxL - 1)
    if alpha > 1 + min(dist_even) * (max_l - 1):
        fails.append("C96")
    # 133: rad + l^cC4 <= path   (0^0 = 1)
    rhs = 1 if c4 else avg_l
    if rad + rhs > pth:
        fails.append("C133")
    # 189: max distEven <= 1 + sigma -> ham path
    if max(dist_even) <= 1 + sigma and not ham:
        fails.append("C189")
    # 199: tree - 2 <= kappa (Nat subtraction) -> ham path
    if max(tree - 2, 0) <= kappa and not ham:
        fails.append("C199")
    return fails, dict(rad=rad, diam=diam, tree=tree, forest=forest, b=bip, alpha=alpha,
                       path=pth, pc=pc, kappa=kappa, residue=res, maxL=max_l,
                       avgL=str(avg_l), c4=c4, ham=ham, sigma=sigma,
                       distEven=dist_even, degs=degs)


def main():
    nlabel = sys.argv[1] if len(sys.argv) > 1 else "?"
    counts = {}
    examples = {}
    total = 0
    for line in sys.stdin:
        if not line.strip():
            continue
        n, adj = parse_g6(line)
        if n < 2:
            continue
        total += 1
        fails, inv = check(n, adj)
        for c in fails:
            counts[c] = counts.get(c, 0) + 1
            if c not in examples:
                examples[c] = (line.strip(), inv)
    print(f"n={nlabel} graphs={total} failures={counts}")
    for c, (g6, inv) in sorted(examples.items()):
        print(f"  {c} first counterexample g6={g6} inv={inv}")
    sys.stdout.flush()


if __name__ == "__main__":
    main()
