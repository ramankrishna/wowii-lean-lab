/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 84

**Verbatim statement (WOWII #84, status O):**
> If G is a simple connected graph, then tree(G) ≥ 2 rad(G) / δ(G)

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj84

Here `δ(G)` is the **minimum degree** of `G` (lowercase delta in the WOWII
HTML, rendered as `<font face="Symbol">d</font>`), not the average distance.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture84

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
C84 leaf case (pre-registered sub-target, not a repo statement).

If a connected graph has minimum degree 1, it has an induced tree on at least
2·rad(G) vertices. Together with the minimum-degree ≥ 2 case (already proved in Lean in
attempts/C84.lean), this gives WOWII Conjecture 84.

Brute force: holds on all 63,308 connected graphs with a leaf on ≤ 9 vertices.
The induced-PATH version is false (n = 8), so a proof must build a branching tree.
-/
theorem conjecture84_leaf (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hδ : G.minDegree = 1) :
    2 * G.radius.toNat ≤ largestInducedTreeSize G := by
  sorry

-- Sanity checks

/-- The `largestInducedTreeSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ largestInducedTreeSize G := Nat.zero_le _

/-- The largest induced tree size is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (largestInducedTreeSize G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphConjecture84
