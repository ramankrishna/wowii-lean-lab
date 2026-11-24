"""Brute-force counterexample search for the 8 open WOWII conjectures.

Invariants mirror the Lean definitions in FormalConjecturesForMathlib (see notes per function).
Graphs: all connected graphs on 2..7 vertices (networkx atlas), plus random / structured
connected graphs on 8..11 vertices.
"""
import itertools, math, random, sys
from fractions import Fraction as F
import networkx as nx

def adjmask(G, n):
    A = [0] * n
    for u, v in G.edges():
        A[u] |= 1 << v; A[v] |= 1 << u
    return A

def popc(x): return bin(x).count("1")

def bits(x):
    i = 0
    while x:
        if x & 1: yield i
        x >>= 1; i += 1

def connected_mask(A, S):
    if S == 0: return False  # Lean: Connected requires Nonempty
    start = S & -S
    seen = start; frontier = start
    while frontier:
        nxt = 0
        for v in bits(frontier): nxt |= A[v]
        nxt &= S & ~seen
        seen |= nxt; frontier = nxt
    return seen == S

def edges_in(A, S): return sum(popc(A[v] & S) for v in bits(S)) // 2

def acyclic_mask(A, S):
    # forest iff |E| = |V| - #components
    comps = 0; rem = S
    while rem:
        start = rem & -rem; seen = start; fr = start
        while fr:
            nxt = 0
            for v in bits(fr): nxt |= A[v]
            nxt &= S & ~seen; seen |= nxt; fr = nxt
        rem &= ~seen; comps += 1
    return edges_in(A, S) == popc(S) - comps

def bipartite_mask(A, S):
    color = {}
    for s in bits(S):
        if s in color: continue
        color[s] = 0; stack = [s]
        while stack:
            u = stack.pop()
            for w in bits(A[u] & S):
                if w not in color: color[w] = 1 - color[u]; stack.append(w)
                elif color[w] == color[u]: return False
    return True

def indep_num_mask(A, S):
    best = 0; vs = list(bits(S))
    def rec(i, cur, size):
        nonlocal best
        if size + (len(vs) - i) <= best: return
        if i == len(vs): best = max(best, size); return
        v = vs[i]
        if not (A[v] & cur): rec(i + 1, cur | (1 << v), size + 1)
        rec(i + 1, cur, size)
    rec(0, 0, 0)
    return best

def dists(A, n):
    D = []
    for s in range(n):
        d = [None] * n; d[s] = 0; q = [s]
        for u in q:
            for w in bits(A[u]):
                if d[w] is None: d[w] = d[u] + 1; q.append(w)
        D.append(d)
    return D

def path_sets(A, n):
    """P[S] = True iff G[S] contains a spanning path (Held-Karp)."""
    full = 1 << n
    end = [0] * full  # end[S] = bitmask of v such that a path covering S ends at v
    for v in range(n): end[1 << v] = 1 << v
    for S in range(1, full):
        e = end[S]
        if not e: continue
        for v in bits(e):
            ext = A[v] & ~S
            for w in bits(ext): end[S | (1 << w)] |= 1 << w
    return [end[S] != 0 for S in range(full)]

def invariants(G):
    n = G.number_of_nodes()
    A = adjmask(G, n)
    full = (1 << n) - 1
    D = dists(A, n)
    ecc = [max(r) for r in D]
    rad, diam = min(ecc), max(ecc)
    deg = [popc(a) for a in A]
    tree = forest = bip = pathnum = 0
    for S in range(1, full + 1):
        k = popc(S)
        acyc = acyclic_mask(A, S)
        if acyc: forest = max(forest, k)
        conn = connected_mask(A, S)
        if acyc and conn:
            tree = max(tree, k)
            if all(popc(A[v] & S) <= 2 for v in bits(S)): pathnum = max(pathnum, k)
        if k > bip and bipartite_mask(A, S): bip = k
    # vertex connectivity (Lean def: min |S| with G - S disconnected/empty, or |S| = n-1)
    kappa = n - 1
    for S in range(0, full + 1):
        k = popc(S)
        if k >= kappa: continue
        if not connected_mask(A, full & ~S): kappa = k
    # path cover number via set-partition DP over path-coverable sets
    P = path_sets(A, n)
    INF = 10 ** 9; pc = [INF] * (full + 1); pc[0] = 0
    for S in range(1, full + 1):
        low = S & -S; rest = S & ~low; sub = rest
        while True:
            T = sub | low
            if P[T] and pc[S & ~T] + 1 < pc[S]: pc[S] = pc[S & ~T] + 1
            if sub == 0: break
            sub = (sub - 1) & rest
    hampath = P[full]
    indep = indep_num_mask(A, full)
    lv = [indep_num_mask(A, A[v]) for v in range(n)]
    distEven = [sum(1 for w in range(n) if D[v][w] % 2 == 0) for v in range(n)]
    sigma = sorted(deg)[1] if n >= 2 else 0
    hasC4 = any(
        (A[a] >> b & 1) and (A[b] >> c & 1) and (A[c] >> d & 1) and (A[d] >> a & 1)
        for a, b, c, d in itertools.permutations(range(n), 4))
    return dict(n=n, A=A, rad=rad, diam=diam, ecc=ecc, deg=deg, tree=tree, forest=forest,
                bip=bip, path=pathnum, kappa=kappa, pc=pc[full], hampath=hampath,
                indep=indep, lv=lv, distEven=distEven, sigma=sigma, hasC4=hasC4,
                residue=residue(deg))

def residue(deg):
    s = sorted(deg, reverse=True)
    while True:
        if not s: return 0
        d = s[0]
        if d == 0: return len(s)
        rest = s[1:]
        dec = [x - 1 for x in rest[:d]] + rest[d:]  # x-1 is Nat subtraction in Lean; graphic => x>=1
        s = sorted([max(x, 0) for x in dec], reverse=True)

def ceil(fr): return math.ceil(fr)

# Each check returns (holds, detail).
def c40(I):
    lhs = ceil(F(I["pc"] + I["bip"] + 1, 2)); return lhs <= I["forest"], f"ceil((pc={I['pc']}+b={I['bip']}+1)/2)={lhs} vs forest={I['forest']}"
def c61(I):
    lhs = I["residue"] + ceil(F(I["diam"], 3)); return lhs <= I["forest"], f"residue={I['residue']}+ceil(diam={I['diam']}/3)={lhs} vs forest={I['forest']}"
def c199(I):
    if not (max(I["tree"] - 2, 0) <= I["kappa"]): return True, "hyp false"
    return I["hampath"], f"tree={I['tree']} kappa={I['kappa']} hampath={I['hampath']}"
def c84(I):
    lhs = F(2 * I["rad"], min(I["deg"])); return lhs <= I["tree"], f"2rad/δ={lhs} vs tree={I['tree']}"
def c189(I):
    if not (max(I["distEven"]) <= 1 + I["sigma"]): return True, "hyp false"
    return I["hampath"], f"maxDE={max(I['distEven'])} σ={I['sigma']} hampath={I['hampath']}"
def c72(I):
    lhs = ceil(F(sum(I["ecc"]), I["n"]) + F(max(I["lv"]), 3)); return lhs <= I["tree"], f"ceil(avgEcc+maxL/3)={lhs} vs tree={I['tree']}"
def c96(I):
    rhs = 1 + min(I["distEven"]) * (max(I["lv"]) - 1); return I["indep"] <= rhs, f"α={I['indep']} vs 1+minDE*(maxL-1)={rhs}"
def c133(I):
    lavg = F(sum(I["lv"]), I["n"])
    term = 1 if I["hasC4"] else lavg
    lhs = I["rad"] + term; return lhs <= I["path"], f"rad={I['rad']}+l^cC4={term} = {lhs} vs path={I['path']}"

CHECKS = [("C40", c40), ("C61", c61), ("C199", c199), ("C84", c84), ("C189", c189),
          ("C72", c72), ("C96", c96), ("C133", c133)]

def graphs():
    for G in nx.graph_atlas_g():
        if G.number_of_nodes() >= 2 and nx.is_connected(G):
            yield "atlas", G
    rng = random.Random(12345)
    fams = []
    for n in range(8, 12):
        fams += [nx.cycle_graph(n), nx.path_graph(n), nx.complete_graph(n), nx.star_graph(n - 1),
                 nx.wheel_graph(n), nx.ladder_graph(n // 2)]
        for a in range(1, n // 2 + 1): fams.append(nx.complete_bipartite_graph(a, n - a))
    fams += [nx.petersen_graph(), nx.hypercube_graph(3), nx.circular_ladder_graph(5),
             nx.moebius_kantor_graph() if False else nx.heawood_graph()]
    for G in fams:
        yield "family", nx.convert_node_labels_to_integers(G)
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    for _ in range(N):
        n = rng.randint(8, 10)
        p = rng.choice([0.15, 0.2, 0.25, 0.3, 0.4, 0.5, 0.6, 0.75])
        G = nx.gnp_random_graph(n, p, seed=rng.randrange(1 << 30))
        if nx.is_connected(G): yield "random", G
    for _ in range(N // 10):  # random trees / sparse
        n = rng.randint(8, 11)
        T = nx.random_labeled_tree(n, seed=rng.randrange(1 << 30))
        for _ in range(rng.randint(0, 3)):
            u, v = rng.sample(range(n), 2); T.add_edge(u, v)
        yield "sparse", T

if __name__ == "__main__":
    fails = {k: [] for k, _ in CHECKS}; count = {k: 0 for k, _ in CHECKS}; hyp = {k: 0 for k, _ in CHECKS}
    total = 0
    for src, G in graphs():
        total += 1
        I = invariants(G)
        for k, f in CHECKS:
            ok, det = f(I)
            if det == "hyp false": continue
            hyp[k] += 1
            if not ok:
                count[k] += 1
                if len(fails[k]) < 3:
                    fails[k].append((src, I["n"], sorted(G.edges()), det))
    print("graphs checked:", total)
    for k, _ in CHECKS:
        print(f"{k}: hypothesis-satisfying graphs={hyp[k]} violations={count[k]}")
        for x in fails[k]: print("   ", x)
