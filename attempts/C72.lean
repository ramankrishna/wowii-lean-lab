import FormalConjecturesUtil

namespace WrittenOnTheWallII.GraphConjecture72

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

omit [Nontrivial α] in
lemma dist_succ_le_tree (G : SimpleGraph α) (h : G.Connected) (u v : α) :
    G.dist u v + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist u v
  have hpath : p.IsPath := p.isPath_of_length_eq_dist hp
  have hT := Walk.induce_support_isTree_of_length_eq_dist p hp
  have hcard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hpath.support_nodup, Walk.length_support]
  have := card_le_largestInducedTreeSize hT
  omega

omit [Nontrivial α] in
lemma eccent_succ_le_tree (G : SimpleGraph α) (h : G.Connected) (u : α) :
    (G.eccent u).toNat + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite u
  have : (G.eccent u).toNat = G.dist u w := by rw [← hw]; rfl
  rw [this]; exact dist_succ_le_tree G h u w

lemma averageEccentricity_add_one_le (G : SimpleGraph α) (h : G.Connected) :
    averageEccentricity G + 1 ≤ (largestInducedTreeSize G : ℝ) := by
  unfold averageEccentricity
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [div_add_one hn.ne', div_le_iff₀ hn]
  have : ∀ u ∈ (Finset.univ : Finset α),
      ((G.eccent u).toNat : ℝ) + 1 ≤ largestInducedTreeSize G := fun u _ => by
    exact_mod_cast eccent_succ_le_tree G h u
  have := Finset.sum_le_sum this
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at this
  push_cast
  linarith

theorem conjecture72 (G : SimpleGraph α) (h : G.Connected) :
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    ⌈averageEccentricity G + (maxL : ℝ) / 3⌉ ≤ (largestInducedTreeSize G : ℝ) := by
  intro maxL
  have hA := averageEccentricity_add_one_le G h
  have key : averageEccentricity G + (maxL : ℝ) / 3 ≤ (largestInducedTreeSize G : ℤ) := by
    rcases le_or_gt maxL 3 with h3 | h3
    · have : (maxL : ℝ) ≤ 3 := by exact_mod_cast h3
      push_cast; linarith
    · -- maxL ≥ 4: needs an induced tree combining a long geodesic with many
      -- independent neighbours; no argument found.
      sorry
  have := Int.ceil_le.mpr key
  exact_mod_cast this

end WrittenOnTheWallII.GraphConjecture72

#print axioms WrittenOnTheWallII.GraphConjecture72.conjecture72
