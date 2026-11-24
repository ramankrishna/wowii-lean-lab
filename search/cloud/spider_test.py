"""K1: exists a leaf x (neighbour y) and an induced tree S with |S| >= 2r such that
S = {x} + Gamma + B where Gamma is a G-geodesic starting at y, and B is an induced path
(possibly empty) hanging off ONE vertex of Gamma by a single edge.
K2: K1 with B attached at an interior/any vertex AND Gamma ending at a vertex farthest
from y (i.e. |Gamma| = ecc(y)+1).
Usage: nauty-geng -c -q N | python3 spider_test.py N
"""
import sys
import wow_search as W


def tree_edges(adj, S):
    vs = [v for v in range(len(adj)) if S >> v & 1]
    return {v: [u for u in vs if adj[v] >> u & 1] for v in vs}


def check_spider(adj, D, S, x, y, need_far):
    T = tree_edges(adj, S)
    if y not in T:
        return False
    degs = {v: len(nb) for v, nb in T.items()}
    if sum(1 for d in degs.values() if d >= 3) > 1 or max(degs.values()) > 3:
        return False
    leaves = [v for v, d in degs.items() if d == 1 and v != x]
    # tree path x -> l ; the part after x must be a geodesic from y
    for l in leaves:
        # BFS in tree from x
        par = {x: None}
        order = [x]
        for v in order:
            for u in T[v]:
                if u not in par:
                    par[u] = v
                    order.append(u)
        path = []
        v = l
        while v is not None:
            path.append(v)
            v = par[v]
        path.reverse()  # x, y, ..., l
        gam = path[1:]
        if D[y][l] != len(gam) - 1:
            continue
        if need_far and D[y][l] != max(D[y]):
            continue
        rest = set(T) - set(path)
        # rest must be a path attached by one edge (automatic: tree with <=1 deg-3 vertex)
        return True
    return False


def main():
    lbl = sys.argv[1]
    c = {"graphs": 0, "K1": 0, "K2": 0}
    ex = {}
    for line in sys.stdin:
        n, adj = W.parse_g6(line)
        degs = [W.popcount(a) for a in adj]
        leaves = [v for v in range(n) if degs[v] == 1]
        if n < 3 or not leaves:
            continue
        c["graphs"] += 1
        D = [W.bfs_dist(n, adj, s) for s in range(n)]
        r = min(max(d) for d in D)
        k1 = k2 = False
        for S in range(1, 1 << n):
            if W.popcount(S) < 2 * r:
                continue
            if not (W.induced_connected(adj, S) and W.is_forest(adj, S)):
                continue
            for x in leaves:
                if not S >> x & 1:
                    continue
                y = (adj[x] & -adj[x]).bit_length() - 1
                if not k1 and check_spider(adj, D, S, x, y, False):
                    k1 = True
                if not k2 and check_spider(adj, D, S, x, y, True):
                    k2 = True
            if k1 and k2:
                break
        for name, ok in (("K1", k1), ("K2", k2)):
            if not ok:
                c[name] += 1
                ex.setdefault(name, (line.strip(), r))
    print(f"n={lbl} {c}", flush=True)
    for k, v in ex.items():
        print(f"  {k} fail g6={v[0]} r={v[1]}")


if __name__ == "__main__":
    main()
