# Results: verified attempts on open WrittenOnTheWallII conjectures

## Pre-registered targets (written before any attempt)

Repo: google-deepmind/formal-conjectures (shallow clone, 2026-11-23), toolchain leanprover/lean4:v4.33.1.

**Protocol deviation (forced):** the protocol asks for 10 OPEN conjectures, but only **8** theorems in
`FormalConjectures/WrittenOnTheWallII/` carry `@[category research open]` (55 are `research solved`,
the rest are `test`). All 8 are targeted; no solved conjectures were substituted.

Ordered by length of the theorem statement (characters from `theorem` to `:= by`, whitespace collapsed):

| # | Conjecture | Statement length |
|---|-----------|------------------|
| 1 | GraphConjecture40  | 164 |
| 2 | GraphConjecture61  | 167 |
| 3 | GraphConjecture199 | 175 |
| 4 | GraphConjecture84  | 193 |
| 5 | GraphConjecture189 | 221 |
| 6 | GraphConjecture72  | 227 |
| 7 | GraphConjecture96  | 278 |
| 8 | GraphConjecture133 | 348 |

## Setup outcome

- elan installed; `formal-conjectures` cloned (shallow); `lake exe cache get` OK (8690 Mathlib files);
  `lake build` **completed successfully (10867 jobs, 0 errors)**.

## Results

| Conjecture | Status | Iterations | Notes |
|---|---|---|---|
| GraphConjecture40  | failed | 1 | No counterexample (see search below). No proof strategy found for 2·f ≥ pc + b + 1; Lean file is statement + `sorry` only. |
| GraphConjecture61  | failed | 1 | No counterexample. Would need at least α ≥ residue (Favaron–Mahéo–Saclé) strengthened inside an induced forest; not in Mathlib, no argument found. Statement + `sorry` only. |
| GraphConjecture199 | failed | 1 | No counterexample (4,564 + 27,040 hypothesis-satisfying graphs). Natural route (Chvátal–Erdős) needs Menger-type machinery absent from Mathlib. Statement + `sorry` only. |
| GraphConjecture84  | failed | 3 | No counterexample. **Partial (does not count):** the δ ≥ 2 case is proved in Lean (a geodesic of length rad induces a tree, so 2·rad/δ ≤ rad < tree). The δ = 1 case needs tree ≥ 2·rad whenever a leaf exists; that is unproven. Computationally it is tight: tree − 2·rad = 0 on many graphs with δ = 1. |
| GraphConjecture189 | failed | 1 | No counterexample (3,483 + 16,205 hypothesis-satisfying graphs). Needs a Dirac/Ore-type Hamiltonian-path theorem; none available, none derived. Statement + `sorry` only. |
| GraphConjecture72  | failed | 1 | No counterexample (min slack observed 1/3). **Partial (does not count):** the case maxL ≤ 3 is proved in Lean via tree ≥ ecc(u)+1 for every u. The case maxL ≥ 4 is open. Two candidate lemmas I tested (tree ≥ ecc(v)+L−1; tree ≥ avgEcc+1+(L−1)/3) are both false, and the diameter version of the bound is also false, by 1/3. |
| GraphConjecture96  | **proved** | 3 | Compiles; `#print axioms` → `[propext, Classical.choice, Quot.sound]`; no `sorry`. The statement is byte-identical to the repo's. It was also spliced into a copy of the original repo file (same `module` header, imports, attributes, docstring); that copy compiles and differs from the original only by the removed `sorry` line. Saved as `proofs/GraphConjecture96.lean`. **Literature still needs checking before calling this new**: the conjecture is tagged `research open` in formal-conjectures, but I made no literature or WOWII-status check (network use was restricted to setup). |
| GraphConjecture133 | failed | 1 | No counterexample, including structured C4-free families (Petersen, Hoffman–Singleton, PG(2,q) incidence graphs for q ≤ 13, ER_q polarity graphs for q ≤ 19: the required induced path was found every time). The C4 case reduces to rad+1 ≤ path, but the C4-free case rad + l ≤ path has no argument. Statement + `sorry` only. |

**Summary: 1 / 8 proved (C96), 0 disproved, 0 counterexamples found, 7 failed.**
(The target count is 8, not 10; see the protocol deviation above.)

"Iterations" counts compile runs of the attempt file. For C96, the separate compile of the
spliced in-repo copy was a verification run and is not counted.

## Computational search (done before any Lean attempt)

Python brute force (`search/check.py`). Every invariant re-implements the Lean definition,
including its conventions: `secondSmallestDegree` = 2nd entry of the ascending degree sequence;
`vertexConnectivity` with the complete-graph convention n−1; `l` = average α(G[N(v)]); `distEven`
counts v itself; Havel–Hakimi `residue`; `path` = largest induced path; `cC4` uses not-necessarily-induced C4.
I sanity-checked the invariants by hand on Petersen, C6, K4, K2,3, a star, and P5.

| Graph set | Count | Violations (all 8 conjectures) |
|---|---|---|
| All connected graphs on 2–7 vertices (networkx atlas) | 995 | 0 |
| Structured families on 8–14 vertices (cycles, paths, wheels, K_{a,b}, ladders, Petersen, Q3, Heawood, …) | 46 | 0 |
| Random G(n,p), n = 8–10, connected | 12,508 | 0 |
| Random sparse (tree + ≤3 edges), n = 8–11 | 2,000 | 0 |
| **Exhaustive n = 8**: each 7-vertex atlas graph + a new vertex with every neighbour subset (covers every connected 8-vertex graph, with isomorphic duplicates) | 119,980 | 0 |
| C133 only: structured C4-free graphs up to 381 vertices | 16 | 0 |

I tried to install nauty (`geng`) via Homebrew for larger exhaustive runs; the permission system
blocked it, and I did not pursue it further.

## C96 proof sketch (as formalized)

Pick v minimising distEven(v) and let E = the vertices at even distance from v, so |E| = minDistEven.
Let S be a maximum independent set. Map each w ∈ S to w itself if w ∈ E, otherwise to a BFS parent
of w (one layer closer to v, so in E). Bound the fibres:
- The fibre of v has size ≤ maxL. If v ∈ S, it is just {v}; otherwise it is an independent subset of N(v).
- The fibre of any other u ∈ E has size ≤ maxL − 1. If u ∈ S, it is {u}, and maxL ≥ 2 because
  u and its BFS grandparent are non-adjacent neighbours of u's parent. If u ∉ S, the fibre is
  an independent subset of N(u) at distance d(u)+1, and u's own parent (at distance d(u)−1) can be
  added to it while staying independent.

Summing: α(G) ≤ maxL + (|E| − 1)(maxL − 1) = 1 + minDistEven·(maxL − 1).

## Files

- `proofs/GraphConjecture96.lean`: the successful proof (repo file with `sorry` replaced, plus helper lemmas).
- `attempts/C*.lean`: every Lean attempt, including the partial C84/C72 reductions (these still contain `sorry`).
- `search/`: brute-force scripts and their outputs (`full_run.txt`, `exhaustive8.txt`, `c133_structured.txt`).
- `build.log`: full `lake build` log.
