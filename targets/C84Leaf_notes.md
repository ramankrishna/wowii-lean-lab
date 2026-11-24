# C84 leaf case: proof notes (2026-11-23)

Target: G connected, minDegree 1, rad(G) = r  =>  tree(G) >= 2r.

## Proved (informal, not yet in Lean)

**Base r <= 2.** r = 1: any edge. r = 2: leaf x with neighbour y; y is not dominating
(else rad <= 1), so some u has d(y,u) = 2 via y-m-u. Then x-y-m-u is an induced path on 4 vertices.

**Lemma R (radius drop).** For a non-cut vertex v: rad(G - v) >= rad(G) - 1.
(A centre c of G-v has d_G(c,u) <= d_{G-v}(c,u) for every u != v, and d(c,v) <= ecc_{G-v}(c) + 1.)

**Reduction to critical graphs.** Let G be a smallest counterexample with leaf x and neighbour y.
For any non-cut v != x: v != y (y is a cut vertex), so G - v is connected and still has the leaf x.
If rad(G - v) >= r, minimality gives an induced tree of size >= 2 rad(G - v) >= 2r in G - v,
which is also induced in G. Contradiction. So **every non-cut v != x has rad(G - v) = r - 1**.
Equivalently, each such v is the unique vertex at distance r from some centre c_v of G.

## Observed (brute force, not proof)

| Statement | Result |
|---|---|
| Target, all connected leaf graphs n <= 9 | 67,394 graphs (63,308 of them at n = 9), 0 failures |
| Induced PATH >= 2r | false (n=8: C4 with a pendant at each vertex) |
| T1: induced path of >= 2r-1 vertices + a vertex touching it exactly once | holds n <= 9 |
| Leaf + geodesic + one branch (K1) | false (n=8, G?qacg) |
| Critical leaf graphs, r >= 3, n <= 10 | only 11 exist; every one is a tree or unicyclic |
| Chung's ESS construction + one private neighbour, every choice | fails for some choices (n=8 sub-case b, n=10 sub-case c), but every critical graph has a working choice |

## Gap

Show a critical leaf graph has tree >= 2r. The data suggests critical leaf graphs have
cyclomatic number <= 1. Trees are immediate (diam >= 2r - 1 gives a path on 2r vertices).
A proof would need (i) critical => at most one cycle, and (ii) the unicyclic case.
Neither is done.

## Erratum
The frozen prereg JSON and an earlier chat message say "63,308 leaf graphs n <= 9". That is the n = 9 count only;
the total for 3 <= n <= 9 is 67,394. The prereg file is left unchanged because its hash is the registration.
