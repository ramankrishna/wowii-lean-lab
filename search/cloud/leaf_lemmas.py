"""Test candidate strengthenings of the C84 leaf case on all connected graphs with a leaf.
L0 (target):  leaf => tree >= 2r
L1: leaf => induced PATH with >= 2r vertices
L2: for EVERY leaf x: induced path with >= 2r vertices having x as an endpoint
L3: for EVERY leaf x: induced tree with >= 2r vertices containing x
Usage: nauty-geng -c -q N | python3 leaf_lemmas.py N
"""
import sys
import wow_search as W


def main():
    n_lbl = sys.argv[1]
    cnt = {k: 0 for k in ["graphs", "L0", "L1", "L2", "L3"]}
    ex = {}
    for line in sys.stdin:
        n, adj = W.parse_g6(line)
        degs = [W.popcount(a) for a in adj]
        leaves = [v for v in range(n) if degs[v] == 1]
        if n < 3 or not leaves:
            continue
        cnt["graphs"] += 1
        r = min(max(W.bfs_dist(n, adj, s)) for s in range(n))
        tree = path = 0
        best_path_with = {x: 0 for x in leaves}
        best_tree_with = {x: 0 for x in leaves}
        for S in range(1, 1 << n):
            k = W.popcount(S)
            ip = W.is_induced_path(adj, S)
            it = ip or (W.induced_connected(adj, S) and W.is_forest(adj, S))
            if it:
                tree = max(tree, k)
                for x in leaves:
                    if S >> x & 1:
                        best_tree_with[x] = max(best_tree_with[x], k)
            if ip:
                path = max(path, k)
                for x in leaves:
                    # x endpoint: degree <= 1 inside S
                    if S >> x & 1 and W.popcount(adj[x] & S) <= 1:
                        best_path_with[x] = max(best_path_with[x], k)
        fails = []
        if tree < 2 * r: fails.append("L0")
        if path < 2 * r: fails.append("L1")
        if any(best_path_with[x] < 2 * r for x in leaves): fails.append("L2")
        if any(best_tree_with[x] < 2 * r for x in leaves): fails.append("L3")
        for f in fails:
            cnt[f] += 1
            ex.setdefault(f, (line.strip(), r, tree, path))
    print(f"n={n_lbl} {cnt}")
    for f, e in sorted(ex.items()):
        print(f"  {f} first fail g6={e[0]} r={e[1]} tree={e[2]} path={e[3]}")


if __name__ == "__main__":
    main()
