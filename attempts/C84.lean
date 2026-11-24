import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture84

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Any geodesic gives an induced tree: `dist u v + 1 ≤ tree(G)`. -/
lemma dist_succ_le_tree (G : SimpleGraph α) (h : G.Connected) (u v : α) :
    G.dist u v + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist u v
  have hpath : p.IsPath := p.isPath_of_length_eq_dist hp
  have hT := Walk.induce_support_isTree_of_length_eq_dist p hp
  have hcard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hpath.support_nodup, Walk.length_support]
  have := card_le_largestInducedTreeSize hT
  omega

/-- `rad(G) + 1 ≤ tree(G)` for connected `G`. -/
lemma radius_succ_le_tree (G : SimpleGraph α) (h : G.Connected) :
    G.radius.toNat + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_radius_of_finite
  have hne : G.edist u v ≠ ⊤ := by
    rw [edist_ne_top_iff_reachable]; exact h.preconnected u v
  have : G.radius.toNat = G.dist u v := by
    rw [← huv]; rfl
  rw [this]
  exact dist_succ_le_tree G h u v

theorem conjecture84 (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) (hδ : 0 < G.minDegree) :
    2 * (G.radius.toNat : ℝ) / (G.minDegree : ℝ) ≤ (largestInducedTreeSize G : ℝ) := by
  have hr := radius_succ_le_tree G h
  have hδR : (0 : ℝ) < G.minDegree := by exact_mod_cast hδ
  rw [div_le_iff₀ hδR]
  rcases Nat.lt_or_ge G.minDegree 2 with h1 | h2
  · -- δ = 1: need 2·rad ≤ tree(G). This is the open part.
    have hδ1 : G.minDegree = 1 := by omega
    rw [hδ1]
    sorry
  · have h2R : (2 : ℝ) ≤ G.minDegree := by exact_mod_cast h2
    have hrR : (G.radius.toNat : ℝ) + 1 ≤ largestInducedTreeSize G := by exact_mod_cast hr
    have h0 : (0 : ℝ) ≤ G.radius.toNat := by positivity
    nlinarith

end WrittenOnTheWallII.GraphConjecture84

#print axioms WrittenOnTheWallII.GraphConjecture84.conjecture84
