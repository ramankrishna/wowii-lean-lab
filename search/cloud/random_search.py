"""Random/structured search on larger graphs (n=10..14) for the WOWII conjectures
whose invariants stay cheap (skips C40, which needs the 3^n path-cover DP).
Usage: python3 random_search.py SEED SECONDS
"""
import random
import sys
import time

import wow_search as W


def rand_graph(rng):
    n = rng.randint(10, 14)
    kind = rng.choice(["gnp", "tree+", "cycle+pend", "bip+"])
    adj = [0] * n

    def add(a, b):
        if a != b:
            adj[a] |= 1 << b
            adj[b] |= 1 << a

    if kind == "gnp":
        p = rng.uniform(0.12, 0.6)
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < p:
                    add(i, j)
    elif kind == "tree+":
        for v in range(1, n):
            add(v, rng.randrange(v))
        for _ in range(rng.randint(0, n)):
            add(rng.randrange(n), rng.randrange(n))
    elif kind == "cycle+pend":
        c = rng.randint(4, n - 1)
        for i in range(c):
            add(i, (i + 1) % c)
        for v in range(c, n):
            add(v, rng.randrange(v))
        for _ in range(rng.randint(0, 3)):
            add(rng.randrange(c), rng.randrange(c))
    else:
        a = rng.randint(2, n - 2)
        for i in range(a):
            for j in range(a, n):
                if rng.random() < 0.7:
                    add(i, j)
        for _ in range(rng.randint(0, 3)):
            add(rng.randrange(n), rng.randrange(n))
    return n, adj, kind


def connected(n, adj):
    return W.induced_connected(adj, (1 << n) - 1)


def check_cheap(n, adj):
    full = (1 << n) - 1
    dists = [W.bfs_dist(n, adj, s) for s in range(n)]
    ecc = [max(d) for d in dists]
    rad, diam = min(ecc), max(ecc)
    degs = [W.popcount(a) for a in adj]
    mindeg, sigma = min(degs), sorted(degs)[1]
    dist_even = [sum(1 for x in dists[v] if x % 2 == 0) for v in range(n)]
    lv = [W.indep_num_of(adj, adj[v]) for v in range(n)]
    max_l = max(lv)
    avg_l = W.F(sum(lv), n)
    tree = forest = alpha = pth = 0
    for S in range(1, 1 << n):
        k = W.popcount(S)
        if k > forest and W.is_forest(adj, S):
            forest = k
        if k > tree and W.induced_connected(adj, S) and W.is_forest(adj, S):
            tree = k
        if k > alpha and W.is_independent(adj, S):
            alpha = k
        if k > pth and W.is_induced_path(adj, S):
            pth = k
    ham = W.ham_path_table(n, adj)[full]
    kappa = W.vertex_connectivity(n, adj)
    res = W.residue(degs)
    fails = []
    if res + W.ceil(W.F(diam, 3)) > forest:
        fails.append("C61")
    if W.ceil(W.F(sum(ecc), n) + W.F(max_l, 3)) > tree:
        fails.append("C72")
    if W.F(2 * rad, mindeg) > tree:
        fails.append("C84")
    if alpha > 1 + min(dist_even) * (max_l - 1):
        fails.append("C96")
    if rad + (1 if W.has_c4(n, adj) else avg_l) > pth:
        fails.append("C133")
    if max(dist_even) <= 1 + sigma and not ham:
        fails.append("C189")
    if max(tree - 2, 0) <= kappa and not ham:
        fails.append("C199")
    return fails, dict(n=n, rad=rad, diam=diam, mindeg=mindeg, tree=tree, forest=forest,
                       ham=ham, kappa=kappa, sigma=sigma, maxL=max_l)


def to_edges(n, adj):
    return [(i, j) for i in range(n) for j in range(i + 1, n) if adj[i] >> j & 1]


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]))
    stop = time.time() + float(sys.argv[2])
    tested, found = 0, {}
    while time.time() < stop:
        n, adj, kind = rand_graph(rng)
        if not connected(n, adj):
            continue
        tested += 1
        fails, inv = check_cheap(n, adj)
        for c in fails:
            if c not in found:
                found[c] = (kind, inv, to_edges(n, adj))
                print("FOUND", c, kind, inv, to_edges(n, adj), flush=True)
    print(f"seed={sys.argv[1]} tested={tested} found={sorted(found)}", flush=True)
