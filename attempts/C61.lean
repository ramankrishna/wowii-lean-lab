import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture61

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 61](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$, the size $f(G)$ of a largest induced forest
satisfies $f(G) \ge \mathrm{residue}(G) + \lceil \mathrm{diam}(G) / 3 \rceil$,
where $\mathrm{residue}(G)$ is the Havel-Hakimi residue and $\mathrm{diam}(G)$
is the diameter of $G$.

See: Favaron, Mahéo, Saclé (1991) for the residue; DeLaVina's Graffiti.pc for the conjecture.
-/
theorem conjecture61 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (residue G : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  -- Blocked: would need (at least) the Favaron–Mahéo–Saclé bound α(G) ≥ residue(G)
  -- strengthened by ⌈diam/3⌉ inside an induced forest; not in Mathlib, no argument found.
  sorry

end WrittenOnTheWallII.GraphConjecture61

#print axioms WrittenOnTheWallII.GraphConjecture61.conjecture61
