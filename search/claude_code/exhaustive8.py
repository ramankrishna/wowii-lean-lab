"""Exhaustive check over all connected 8-vertex graphs (with isomorphic duplicates).
Every 8-vertex graph G is (G - v) + v for a 7-vertex graph G - v, so extending every
7-vertex atlas graph by a new vertex with every neighbour subset covers all of them."""
import multiprocessing as mp
import networkx as nx
import check

def work(idx):
    base = nx.graph_atlas(idx)
    out = []
    for mask in range(1, 1 << 7):
        G = nx.Graph(base); G.add_node(7)
        for i in range(7):
            if mask >> i & 1: G.add_edge(i, 7)
        if not nx.is_connected(G): continue
        I = check.invariants(G)
        for k, f in check.CHECKS:
            ok, det = f(I)
            if det == "hyp false": out.append((k, "skip", None)); continue
            out.append((k, ok, None if ok else (sorted(G.edges()), det)))
    return out

if __name__ == "__main__":
    idxs = [i for i, G in enumerate(nx.graph_atlas_g()) if G.number_of_nodes() == 7]
    stats = {k: [0, 0] for k, _ in check.CHECKS}; examples = {k: [] for k, _ in check.CHECKS}
    total = 0
    with mp.Pool() as pool:
        for res in pool.imap_unordered(work, idxs, chunksize=4):
            total += len(res) // len(check.CHECKS)
            for k, ok, ex in res:
                if ok == "skip": continue
                stats[k][0] += 1
                if not ok:
                    stats[k][1] += 1
                    if len(examples[k]) < 3: examples[k].append(ex)
    print("connected 8-vertex labelled extensions checked:", total)
    for k, _ in check.CHECKS:
        print(f"{k}: hypothesis-satisfying={stats[k][0]} violations={stats[k][1]}", examples[k])
