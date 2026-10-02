import SubdiffusiveProcess.Section10.InitialSimplexPackingGeometryOrder

/-! The discrete equality layers are actual thin slabs along simplex facets. -/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

theorem equal_indices_cube_subset_slab {Q : TriadicCube d} {a b : Fin d}
    (heq : Q.index a = Q.index b) :
    cubeSet Q ⊆ {x | |x a - x b| < cubeScaleFactor Q} := by
  intro x hx
  have ha := hx a
  have hb := hx b
  rw [← heq] at hb
  change |x a - x b| < cubeScaleFactor Q
  rw [abs_lt]
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

/-- An unresolved cube's center belongs to the closed simplex. -/
theorem unresolved_initialSimplex_center_mem_closed {ell n : ℕ}
    {pi : Equiv.Perm (Fin d)} {Q : TriadicCube d}
    (hQ : Q ∈ initialSimplexUnresolved ell pi n) :
    cubeCenter Q ∈ (initialSimplex ell pi).closedCarrier := by
  obtain ⟨hQR, hinter, -⟩ := mem_unresolvedAtDepth.mp hQ
  have hc : cubeCenter Q ∈ openCubeSet Q := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos Q)
  have hroot := openCubeSet_subset_of_mem_descendantsAtDepth hQR hc
  refine ⟨cubeSet_subset_closedBall _ (openCubeSet_subset_cubeSet _ hroot), ?_⟩
  intro i j hij
  change cubeCenter Q (pi i) - (0 : ℤ) * cubeScaleFactor (originCube d (ell : ℤ)) ≤
    cubeCenter Q (pi j) - (0 : ℤ) * cubeScaleFactor (originCube d (ell : ℤ))
  simp only [Int.cast_zero, zero_mul, sub_zero]
  rcases eq_or_lt_of_le hij with heq | hlt
  · have heq' : i = j := Fin.ext heq
    rw [heq']
  · have hidx : (Q.index (pi i) : ℝ) ≤ Q.index (pi j) := by
      exact_mod_cast index_le_of_inter_initialSimplex hinter i j hlt
    exact mul_le_mul_of_nonneg_right hidx (zpow_pos (by norm_num) Q.scale).le

/-- Each unresolved cube meets a genuine coordinate-order facet, at its
center, and its entire support lies in the corresponding side-length slab. -/
theorem unresolved_initialSimplex_meets_facet {ell n : ℕ}
    {pi : Equiv.Perm (Fin d)} {Q : TriadicCube d}
    (hQ : Q ∈ initialSimplexUnresolved ell pi n) :
    ∃ i j : Fin d, i.val < j.val ∧
      cubeCenter Q ∈ cubeSet Q ∩ (initialSimplex ell pi).closedCarrier ∧
      cubeCenter Q (pi i) = cubeCenter Q (pi j) ∧
      cubeSet Q ⊆ {x | |x (pi i) - x (pi j)| < cubeScaleFactor Q} := by
  obtain ⟨i, j, hij, heq⟩ := unresolved_initialSimplex_has_equal_indices hQ
  have hc : cubeCenter Q ∈ openCubeSet Q := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos Q)
  exact ⟨i, j, hij, ⟨openCubeSet_subset_cubeSet _ hc,
      unresolved_initialSimplex_center_mem_closed hQ⟩,
    by simp [cubeCenter, heq], equal_indices_cube_subset_slab heq⟩

/-- Literal facet witness for an admitted depth-(n+1) cube's parent. -/
theorem maximalContained_initialSimplex_parent_meets_facet {ell n : ℕ}
    {pi : Equiv.Perm (Fin d)} {Q : TriadicCube d}
    (hQ : Q ∈ maximalContainedAtDepth (originCube d (ell : ℤ))
      (initialSimplex ell pi).openCarrier (n + 1)) :
    ∃ i j : Fin d, i.val < j.val ∧
      cubeCenter (parentCube Q) ∈ cubeSet (parentCube Q) ∩ (initialSimplex ell pi).closedCarrier ∧
      cubeCenter (parentCube Q) (pi i) = cubeCenter (parentCube Q) (pi j) ∧
      cubeSet (parentCube Q) ⊆
        {x | |x (pi i) - x (pi j)| < cubeScaleFactor (parentCube Q)} := by
  have hchild := maximalContainedAtDepth_subset_children_unresolved
    (originCube d (ell : ℤ)) (initialSimplex ell pi).openCarrier n hQ
  obtain ⟨P, hP, hQP⟩ := Finset.mem_biUnion.mp hchild
  rw [parent_eq_of_mem_childCubes hQP]
  exact unresolved_initialSimplex_meets_facet hP

end
end SubdiffusiveProcess.Section10
