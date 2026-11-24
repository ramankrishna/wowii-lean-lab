import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture133

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 133](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/):

For a simple connected graph $G$,
$\operatorname{path}(G) \ge \operatorname{rad}(G) +
(\mathrm{avg}_v\, l(v))^{cC_4(G)}$,
where $\operatorname{path}(G)$ is the path number of the graph (number of vertices of a largest induced path),
$\operatorname{rad}(G)$ is the radius (minimum eccentricity, as a natural number),
$\mathrm{avg}_v\, l(v) = l(G)$ is the average independence number of vertex
neighbourhoods, and $cC_4(G)$ is the $C_4$-free characteristic function
(1 if $G$ is $C_4$-free, not necessarily induced, and 0 otherwise).
-/
theorem conjecture133 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let rad := G.radius.toNat
    let hasC4 := ∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a
    let cC4 : ℕ := if hasC4 then 0 else 1
    (rad : ℝ) + l G ^ cC4 ≤ (path G : ℝ) := by
  -- C4 case reduces to rad+1 ≤ path (geodesic is an induced path); the C4-free case
  -- rad + l(G) ≤ path(G) has no argument found.
  sorry

end WrittenOnTheWallII.GraphConjecture133

#print axioms WrittenOnTheWallII.GraphConjecture133.conjecture133
