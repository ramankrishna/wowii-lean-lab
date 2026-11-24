import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture40

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α] (G : SimpleGraph α)

/--
WOWII [Conjecture 40](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a nontrivial connected graph `G` the size `f(G)` of a largest induced forest
satisfies `f(G) ≥ ceil((p(G) + b(G) + 1)/2)` where `p(G)` is the path cover
number and `b(G)` is the largest induced bipartite subgraph size.
-/
theorem conjecture40 (h_conn : G.Connected) (h_nontrivial : 1 < Fintype.card α) :
    ⌈(((pathCoverNumber G : ℝ) + b G + 1) / 2)⌉ ≤  G.largestInducedForestSize := by
  -- No proof strategy found: needs 2·f(G) ≥ pc(G) + b(G) + 1; no relation between
  -- path cover number and induced forests/bipartite subgraphs available or derived.
  sorry

end WrittenOnTheWallII.GraphConjecture40

#print axioms WrittenOnTheWallII.GraphConjecture40.conjecture40
