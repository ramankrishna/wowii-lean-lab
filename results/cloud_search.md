# Cloud counterexample search (2026-11-23)

Invariants mirror the Lean definitions in FormalConjecturesForMathlib.

| Sweep | Graphs | Conjectures | Counterexamples |
|---|---|---|---|
| All connected graphs, n=2..9 (nauty geng) | 273,192 | all 8 | 0 |
| geng slices 0/200 and 1/200, n=10 | 32,181 | all 8 | 0 |
| Random + structured (gnp, tree+edges, cycle+pendants, near-bipartite), n=10..14 | 62,707 | 7 (no C40) | 0 |

## C96 status
Proved on the Mac run (proofs/GraphConjecture96.lean). My cloud-side checks:
- statement lock: identical to upstream
- prefix lock: only helper lemmas inserted
- no sorry / native_decide / new axioms
- compile + #print axioms: still has to be confirmed on the Mac with verifier.py

Not new: PR #7665 (opened 2026-10-28, approved twice, not merged yet) and issue #7664
already give a BFS-layer proof of WOWII 96. Ours is an independent rediscovery.
