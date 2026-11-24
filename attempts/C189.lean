import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture189

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 189](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj189)
(status O):

For a simple connected graph `G`, if `max_v distEven(v) ≤ 1 + σ(G)`,
then `G` has a Hamiltonian path.

Here `distEven(v)` is the number of vertices at even distance from `v`, and
`σ(G)` is the **second-smallest degree** of `G`'s degree sequence (per
WOWII defEntry 65).
-/
theorem conjecture189 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  -- Blocked: requires a Dirac/Ore-type Hamiltonian-path theorem; none in Mathlib,
  -- and no direct argument from the distEven hypothesis was found.
  sorry

end WrittenOnTheWallII.GraphConjecture189

#print axioms WrittenOnTheWallII.GraphConjecture189.conjecture189
