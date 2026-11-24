"""Which tree SHAPES suffice for the C84 leaf case?
T1: exists induced path Q with |Q| >= 2r-1 and a vertex z not in Q with exactly one
    neighbour in Q  (so Q+z is an induced tree with >= 2r vertices).
T2: same, but |Q| = 2r-1 exactly is allowed only via such a z OR |Q| >= 2r.  (= T1)
T3: T1 where Q is an ESS/Chung-type path: Q contains a geodesic of length r.
Usage: nauty-geng -c -q N | python3 shape_test.py N
"""
import sys
import wow_search as W


def main():
    lbl = sys.argv[1]
    c = {"graphs": 0, "T1": 0, "T3": 0}
    ex = {}
    for line in sys.stdin:
        n, adj = W.parse_g6(line)
        degs = [W.popcount(a) for a in adj]
        if n < 3 or 1 not in degs:
            continue
        c["graphs"] += 1
        D = [W.bfs_dist(n, adj, s) for s in range(n)]
        r = min(max(d) for d in D)
        full = (1 << n) - 1
        t1 = t3 = False
        for S in range(1, 1 << n):
            k = W.popcount(S)
            if k < 2 * r - 1 or not W.is_induced_path(adj, S):
                continue
            vs = [v for v in range(n) if S >> v & 1]
            has_geo = any(D[a][b] >= r for a in vs for b in vs)
            if k >= 2 * r:
                good = True
            else:
                good = any(W.popcount(adj[z] & S) == 1 for z in range(n) if not S >> z & 1)
            if good:
                t1 = True
                if has_geo:
                    t3 = True
            if t1 and t3:
                break
        for name, ok in (("T1", t1), ("T3", t3)):
            if not ok:
                c[name] += 1
                ex.setdefault(name, (line.strip(), r))
    print(f"n={lbl} {c}", flush=True)
    for k, v in ex.items():
        print(f"  {k} fail g6={v[0]} r={v[1]}")


if __name__ == "__main__":
    main()
