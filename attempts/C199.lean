import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture199

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 199](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`, if `tree(G) - 2 ≤ κ(G)`, then `G` has a Hamiltonian path.
The nontrivial vertex type encodes the source assumption $n > 1$.
Here `tree(G)` is the number of vertices in a largest induced tree and
`κ(G) = vertexConnectivity G` is the vertex connectivity of `G`.
-/
theorem conjecture199 (G : SimpleGraph α) (h : G.Connected)
    (hκ : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  -- Blocked: natural route is Chvátal–Erdős (κ ≥ α - 1 ⇒ traceable) plus tree(G) ≥ α(G)+1;
  -- Chvátal–Erdős needs Menger-type fan lemmas, absent from Mathlib.
  sorry

end WrittenOnTheWallII.GraphConjecture199

#print axioms WrittenOnTheWallII.GraphConjecture199.conjecture199
