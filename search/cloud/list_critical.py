import sys, wow_search as W
from chung_test import radius_without
for line in sys.stdin:
    n, adj = W.parse_g6(line)
    degs=[W.popcount(a) for a in adj]; leaves=[v for v in range(n) if degs[v]==1]
    if n<4 or not leaves: continue
    full=(1<<n)-1; D=[W.bfs_dist(n,adj,s) for s in range(n)]; r=min(max(d) for d in D)
    if r<3: continue
    noncut=[v for v in range(n) if W.induced_connected(adj, full&~(1<<v))]
    for x in leaves:
        if all(radius_without(n,adj,v)<r for v in noncut if v!=x):
            E=[(i,j) for i in range(n) for j in range(i+1,n) if adj[i]>>j&1]
            # cycle structure: number of edges - n + 1
            print(f"n={n} r={r} leaf={x} m={len(E)} cyclomatic={len(E)-n+1} deg={degs} edges={E}")
            break
