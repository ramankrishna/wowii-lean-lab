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
# Written on the Wall II - Conjecture 96

**Verbatim statement (WOWII #96, status O):**
> If G is a simple connected graph, then α(G) ≤ 1 + minimum dist_even(v)*(maximum of λ(v) -1)

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj96


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture96

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

omit [Fintype α] [DecidableEq α] [Nontrivial α] in
/-- Every vertex other than the root has a BFS parent. -/
lemma exists_parent {G : SimpleGraph α} (h : G.Connected) (v w : α) (hw : w ≠ v) :
    ∃ p, G.Adj w p ∧ G.dist v p + 1 = G.dist v w := by
  obtain ⟨q, hq⟩ := h.exists_walk_length_eq_dist v w
  obtain ⟨p, hadj, q', hq'⟩ := Walk.exists_eq_cons_of_ne hw q.reverse
  refine ⟨p, hadj, ?_⟩
  have hlen : q.reverse.length = q'.length + 1 := by rw [hq']; rfl
  rw [Walk.length_reverse] at hlen
  have h1 : G.dist p v ≤ q'.length := dist_le q'
  have h2 : G.dist v w ≤ G.dist v p + G.dist p w := h.dist_triangle
  have h3 : G.dist p w = 1 := dist_eq_one_iff_adj.mpr hadj.symm
  rw [dist_comm] at h1
  omega

omit [Fintype α] [DecidableEq α] [Nontrivial α] in
/-- Vertices whose distances from `v` differ by two are not adjacent. -/
lemma not_adj_of_dist_add_two {G : SimpleGraph α} (v a b : α)
    (hab : G.dist v a + 2 = G.dist v b) : ¬ G.Adj a b := by
  intro hadj
  rcases hadj.diff_dist_adj (u := v) with h1 | h1 | h1 <;> omega

omit [DecidableEq α] [Nontrivial α] in
/-- An independent set inside `N(u)` bounds the local independence number from below. -/
lemma card_le_indepNeighborsCard {G : SimpleGraph α} (u : α) (T : Finset α)
    (hT : ∀ x ∈ T, G.Adj u x) (hI : G.IsIndepSet (T : Set α)) :
    T.card ≤ indepNeighborsCard G u := by
  classical
  unfold indepNeighborsCard
  let T' : Finset (G.neighborSet u) := T.subtype (fun x => x ∈ G.neighborSet u)
  have hcard : T'.card = T.card := by
    rw [Finset.card_subtype]
    congr 1
    apply Finset.filter_true_of_mem
    intro x hx
    exact hT x hx
  rw [← hcard]
  apply IsIndepSet.card_le_indepNum
  intro a ha b hb hab hadj
  have ha' : (a : α) ∈ T := by simpa [T'] using ha
  have hb' : (b : α) ∈ T := by simpa [T'] using hb
  exact hI ha' hb' (fun h => hab (Subtype.ext h)) hadj

/--
WOWII [Conjecture 96](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G` on at least two vertices,
`α(G) ≤ 1 + min_v distEven(v) · (max_v l(v) - 1)`
where `α(G) = G.indepNum` is the independence number,
`distEven(v)` is the number of vertices at even distance from `v`, and
`max_v l(v)` is the maximum independence number of a vertex neighbourhood.

We record the nontrivial-graph version: the literal source inequality fails on $K_1$,
where the independence number and even-distance count are both one, but the maximum
local independence number is zero, giving $1 ≤ 0$.
-/
@[category research open, AMS 5]
theorem conjecture96 (G : SimpleGraph α) (h : G.Connected) :
    let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    (G.indepNum : ℝ) ≤ 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1) := by
  classical
  intro minDistEven maxL
  obtain ⟨v, -, hv⟩ := Finset.mem_image.mp
    (Finset.min'_mem (Finset.univ.image (distEven G)) (by simp))
  have hL : ∀ u, indepNeighborsCard G u ≤ maxL := fun u =>
    Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  set L := maxL with hLdef
  set E := Finset.univ.filter (fun w => Even (G.dist v w)) with hE
  have hEcard : E.card = minDistEven := hv
  have hvE : v ∈ E := by simp [E]
  obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
  have hSI : G.IsIndepSet (S : Set α) := hS.isIndepSet
  have hdist0 : ∀ w, G.dist v w = 0 → w = v := fun w hw =>
    ((h.dist_eq_zero_iff).mp hw).symm
  have hpar : ∀ w, w ≠ v → ∃ p, G.Adj w p ∧ G.dist v p + 1 = G.dist v w :=
    fun w hw => exists_parent h v w hw
  choose! par hparAdj hparDist using hpar
  -- L ≥ 1
  obtain ⟨w0, hw0⟩ := exists_ne v
  have hL1 : 1 ≤ L := by
    have := card_le_indepNeighborsCard (G := G) (par w0) {w0}
      (by simpa using (hparAdj w0 hw0).symm) (by simp)
    simpa using this.trans (hL (par w0))
  -- charging map
  let f : α → α := fun w => if Even (G.dist v w) then w else par w
  have hfE : ∀ w ∈ S, f w ∈ E := by
    intro w _
    by_cases he : Even (G.dist v w)
    · simp [f, he, E]
    · have hw : w ≠ v := by rintro rfl; simp at he
      have hd := hparDist w hw
      simp only [f, he, if_false, E, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hd] at he
      simpa [Nat.even_add_one] using he
  have hcardS : S.card = ∑ u ∈ E, (S.filter fun w => f w = u).card :=
    Finset.card_eq_sum_card_fiberwise hfE
  -- members of a fiber
  have hfib : ∀ u w, w ∈ S.filter (fun w => f w = u) →
      w ∈ S ∧ (w = u ∨ (¬ Even (G.dist v w) ∧ w ≠ v ∧ G.Adj w u ∧
        G.dist v u + 1 = G.dist v w)) := by
    intro u w hw
    rw [Finset.mem_filter] at hw
    refine ⟨hw.1, ?_⟩
    by_cases he : Even (G.dist v w)
    · left; simpa [f, he] using hw.2
    · right
      have hwv : w ≠ v := by rintro rfl; simp at he
      have hfu : par w = u := by simpa [f, he] using hw.2
      exact ⟨he, hwv, hfu ▸ hparAdj w hwv, hfu ▸ hparDist w hwv⟩
  -- fiber of a vertex of S is at most a singleton
  have hboundS : ∀ u ∈ S, (S.filter fun w => f w = u).card ≤ 1 := by
    intro u hu
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have key : ∀ w ∈ S.filter (fun w => f w = u), w = u := by
      intro w hw
      rcases hfib u w hw with ⟨hwS, rfl | ⟨-, -, hadj, -⟩⟩
      · rfl
      · exact absurd hadj (hSI hwS hu (G.ne_of_adj hadj))
    rw [key a ha, key b hb]
  -- fiber of a vertex outside S lies in its neighbourhood and is independent
  have hfibN : ∀ u ∉ S, ∀ w ∈ S.filter (fun w => f w = u),
      G.Adj u w ∧ G.dist v u + 1 = G.dist v w := by
    intro u hu w hw
    rcases hfib u w hw with ⟨hwS, rfl | ⟨-, -, hadj, hd⟩⟩
    · exact absurd hwS hu
    · exact ⟨hadj.symm, hd⟩
  have hfibI : ∀ u, G.IsIndepSet ((S.filter fun w => f w = u : Finset α) : Set α) := by
    intro u
    exact hSI.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)
  -- bound at the root
  have hroot : (S.filter fun w => f w = v).card ≤ L := by
    by_cases hv' : v ∈ S
    · exact (hboundS v hv').trans hL1
    · exact (card_le_indepNeighborsCard v _ (fun w hw => (hfibN v hv' w hw).1)
        (hfibI v)).trans (hL v)
  -- bound away from the root
  have hother : ∀ u ∈ E.erase v, (S.filter fun w => f w = u).card ≤ L - 1 := by
    intro u hu
    obtain ⟨huv, huE⟩ := Finset.mem_erase.mp hu
    have hev : Even (G.dist v u) := (Finset.mem_filter.mp huE).2
    have hpos : G.dist v u ≠ 0 := fun h0 => huv (hdist0 u h0)
    have hdu := hparDist u huv
    set p := par u
    have hp_ne : p ≠ v := by
      intro hpv
      rw [hpv, dist_self] at hdu
      rw [← hdu] at hev
      exact absurd hev (by decide)
    have hdp := hparDist p hp_ne
    -- L ≥ 2 via {u, par p} ⊆ N(p)
    have hL2 : 2 ≤ L := by
      have hq_ne : par p ≠ u := by
        intro hq; rw [hq] at hdp; omega
      have hI : G.IsIndepSet (({u, par p} : Finset α) : Set α) := by
        rw [Finset.coe_pair]
        refine Set.pairwise_pair.mpr fun _ => ⟨?_, ?_⟩
        · exact fun hadj => not_adj_of_dist_add_two v (par p) u (by omega) hadj.symm
        · exact not_adj_of_dist_add_two v (par p) u (by omega)
      have := card_le_indepNeighborsCard (G := G) p {u, par p}
        (by
          intro x hx
          rcases Finset.mem_insert.mp hx with hx | hx
          · rw [hx]; exact (hparAdj u huv).symm
          · rw [Finset.mem_singleton.mp hx]; exact hparAdj p hp_ne) hI
      rw [Finset.card_pair hq_ne.symm] at this
      exact this.trans (hL p)
    by_cases huS : u ∈ S
    · exact (hboundS u huS).trans (by omega)
    · have hp_nmem : p ∉ S.filter (fun w => f w = u) := by
        intro hpm
        have := (hfibN u huS p hpm).2
        omega
      have hT := card_le_indepNeighborsCard (G := G) u
        (insert p (S.filter fun w => f w = u))
        (by
          intro x hx
          rcases Finset.mem_insert.mp hx with hx | hx
          · rw [hx]; exact hparAdj u huv
          · exact (hfibN u huS x hx).1)
        (by
          rw [Finset.coe_insert]
          refine (hfibI u).insert fun w hw _ => ⟨?_, ?_⟩
          · have := (hfibN u huS w hw).2
            exact not_adj_of_dist_add_two v p w (by omega)
          · have := (hfibN u huS w hw).2
            exact fun hadj => not_adj_of_dist_add_two v p w (by omega) hadj.symm)
      rw [Finset.card_insert_of_notMem hp_nmem] at hT
      have := hT.trans (hL u)
      omega
  -- sum up
  have hsum : S.card ≤ L + (E.card - 1) * (L - 1) := by
    rw [hcardS, ← Finset.add_sum_erase E _ hvE]
    have := Finset.sum_le_card_nsmul (E.erase v) _ (L - 1) hother
    rw [Finset.card_erase_of_mem hvE, smul_eq_mul] at this
    omega
  have hE1 : 1 ≤ E.card := Finset.card_pos.mpr ⟨v, hvE⟩
  rw [← hS.card_eq, ← hEcard]
  have hR : ((S.card : ℕ) : ℝ) ≤ ((L + (E.card - 1) * (L - 1) : ℕ) : ℝ) := by
    exact_mod_cast hsum
  push_cast [Nat.cast_sub hL1, Nat.cast_sub hE1] at hR
  linarith

-- Sanity checks

/-- The independence number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.indepNum := Nat.zero_le _

/-- The independence number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.indepNum := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture96

#print axioms WrittenOnTheWallII.GraphConjecture96.conjecture96
