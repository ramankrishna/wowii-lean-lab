"""In 'critical' leaf graphs (some leaf x such that every non-cut v != x has
rad(G-v) < r), test Chung's construction for EVERY choice of
  v (non-cut, != x), centre c of G-v, w with d(v2,w) >= r, canonical geodesics,
and record whether the Chung path Q (2r vertices in case a, 2r-1 in b/c) has
|Q| >= 2r or a private neighbour (vertex outside Q with exactly one neighbour in Q).
Reports: per sub-case, #instances and #failures. 'any' = some choice works per graph.
"""
import sys
import wow_search as W


def geodesic(n, adj, D, a, b):
    path = [a]
    cur = a
    while cur != b:
        nb = adj[cur]
        cur = next(u for u in range(n) if nb >> u & 1 and D[u][b] == D[cur][b] - 1)
        path.append(cur)
    return path


def radius_without(n, adj, v):
    full = ((1 << n) - 1) & ~(1 << v)
    best = 10 ** 9
    for s in range(n):
        if s == v:
            continue
        # BFS inside G - v
        dist = {s: 0}
        fr = [s]
        while fr:
            nx = []
            for a in fr:
                nb = adj[a] & full
                while nb:
                    u = (nb & -nb).bit_length() - 1
                    nb &= nb - 1
                    if u not in dist:
                        dist[u] = dist[a] + 1
                        nx.append(u)
            fr = nx
        best = min(best, max(dist.values()))
    return best


def centres_without(n, adj, v):
    full = ((1 << n) - 1) & ~(1 << v)
    eccs = {}
    for s in range(n):
        if s == v:
            continue
        dist = {s: 0}
        fr = [s]
        while fr:
            nx = []
            for a in fr:
                nb = adj[a] & full
                while nb:
                    u = (nb & -nb).bit_length() - 1
                    nb &= nb - 1
                    if u not in dist:
                        dist[u] = dist[a] + 1
                        nx.append(u)
            fr = nx
        eccs[s] = max(dist.values())
    m = min(eccs.values())
    return [s for s, e in eccs.items() if e == m]


def main():
    lbl = sys.argv[1]
    stats = {"critical_graphs": 0, "graph_any_fail": 0}
    sub = {"a": [0, 0], "b": [0, 0], "c": [0, 0]}
    ex = None
    for line in sys.stdin:
        n, adj = W.parse_g6(line)
        degs = [W.popcount(a) for a in adj]
        leaves = [v for v in range(n) if degs[v] == 1]
        if n < 4 or not leaves:
            continue
        full = (1 << n) - 1
        D = [W.bfs_dist(n, adj, s) for s in range(n)]
        r = min(max(d) for d in D)
        if r < 3:
            continue
        noncut = [v for v in range(n) if W.induced_connected(adj, full & ~(1 << v))]
        crit_leaf = None
        for x in leaves:
            if all(radius_without(n, adj, v) < r for v in noncut if v != x):
                crit_leaf = x
                break
        if crit_leaf is None:
            continue
        stats["critical_graphs"] += 1
        x = crit_leaf
        graph_ok = False
        for v in noncut:
            if v == x:
                continue
            for c in centres_without(n, adj, v):
                if D[c][v] != r:
                    continue
                V = geodesic(n, adj, D, c, v)  # v0=c ... vr=v
                v1, v2 = V[1], V[2]
                for w in range(n):
                    if D[v2][w] < r or w == v:
                        continue
                    P = geodesic(n, adj, D, c, w)  # u0=c ... w
                    if D[c][w] == r - 1:
                        chord = adj[v1] >> P[1] & 1
                        case = "b" if chord else "a"
                    else:
                        case = "c"
                    Q = V[::-1] + P[1:]
                    if case == "b":
                        Q = [q for q in Q if q != c]
                    S = 0
                    for q in Q:
                        S |= 1 << q
                    assert W.is_induced_path(adj, S), (line, v, c, w, case)
                    ok = len(Q) >= 2 * r or any(
                        W.popcount(adj[z] & S) == 1 for z in range(n) if not S >> z & 1)
                    sub[case][0] += 1
                    if not ok:
                        sub[case][1] += 1
                        if ex is None:
                            ex = (line.strip(), r, x, v, c, w, case, Q)
                    graph_ok = graph_ok or ok
        if not graph_ok:
            stats["graph_any_fail"] += 1
    print(f"n={lbl} {stats} subcases(instances,fails)={sub}", flush=True)
    if ex:
        print("  first failing instance:", ex)


if __name__ == "__main__":
    main()
