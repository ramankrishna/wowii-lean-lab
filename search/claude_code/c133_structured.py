"""C133 hunt on structured C4-free graphs: need an induced path with >= rad + l vertices."""
import itertools, sys
from fractions import Fraction as F
import networkx as nx

def pg2_points(q):
    pts = []
    for a in range(q):
        for b in range(q):
            pts.append((1, a, b))
    for b in range(q):
        pts.append((0, 1, b))
    pts.append((0, 0, 1))
    return pts

def incidence_graph(q):
    P = pg2_points(q); G = nx.Graph()
    for i, p in enumerate(P):
        for j, L in enumerate(P):
            if sum(x * y for x, y in zip(p, L)) % q == 0:
                G.add_edge(("p", i), ("L", j))
    return nx.convert_node_labels_to_integers(G)

def polarity_graph(q):
    P = pg2_points(q); G = nx.Graph(); G.add_nodes_from(range(len(P)))
    for i, j in itertools.combinations(range(len(P)), 2):
        if sum(x * y for x, y in zip(P[i], P[j])) % q == 0:
            G.add_edge(i, j)
    return G

def has_c4(G):
    for u in G:
        for v in G:
            if u < v and len(set(G[u]) & set(G[v])) >= 2: return True
    return False

def alpha_small(H):
    # exact independence number of a small graph via complement clique
    if H.number_of_nodes() == 0: return 0
    return max(len(c) for c in nx.find_cliques(nx.complement(H)))

def find_induced_path(G, target):
    """DFS for an induced path with `target` vertices; returns it or None."""
    adj = {u: set(G[u]) for u in G}
    order = sorted(G, key=lambda u: len(adj[u]))
    def ext(path, blocked):
        if len(path) == target: return list(path)
        end = path[-1]
        for w in adj[end]:
            if w in blocked: continue
            # w must not be adjacent to any path vertex except `end`
            nb = blocked | adj[end] | {end}
            path.append(w)
            r = ext(path, nb)
            if r: return r
            path.pop()
        return None
    for s in order:
        r = ext([s], {s})
        if r: return r
    return None

def check(name, G):
    G = nx.convert_node_labels_to_integers(G)
    rad = nx.radius(G); n = G.number_of_nodes()
    lv = [alpha_small(G.subgraph(G[u])) for u in G]
    c4 = has_c4(G)
    need = rad + (1 if c4 else F(sum(lv), n))
    import math
    target = math.ceil(need)
    p = find_induced_path(G, target)
    print(f"{name}: n={n} rad={rad} C4={'yes' if c4 else 'no'} l={float(F(sum(lv), n)):.3f} "
          f"need path>={need} -> induced path of {target}: {'FOUND' if p else 'NOT FOUND'}", flush=True)

if __name__ == "__main__":
    check("Petersen", nx.petersen_graph())
    check("Hoffman-Singleton", nx.hoffman_singleton_graph())
    for q in [2, 3, 5, 7, 11, 13]:
        check(f"PG(2,{q}) incidence", incidence_graph(q))
    for q in [2, 3, 5, 7, 11, 13, 17, 19]:
        check(f"ER_{q} polarity", polarity_graph(q))
