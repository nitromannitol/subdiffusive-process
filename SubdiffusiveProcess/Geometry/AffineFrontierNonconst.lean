import SubdiffusiveProcess.Geometry.Cube




open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

/-- For any nonzero slope `u`, the affine function `x ↦ ∑ u i * x i` takes two different values
on the frontier of any centered cube. -/
theorem affine_frontier_nonconst {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : Fin d → ℝ) (hu : u ≠ 0) :
    ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
        (∑ i : Fin d, u i * x i) ≠ ∑ i : Fin d, u i * y i := by
  have hcube : (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) := rfl
  have hfr : frontier (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Metric.sphere z (r / 2) := by
    rw [hcube]; exact frontier_ball z (half_pos hr).ne'
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hu
  simp only [Pi.zero_apply] at hi0
  set p : SpatialCoordinates d := fun i => z i + (if i = i0 then r / 2 else 0) with hpdef
  set q : SpatialCoordinates d := fun i => z i - (if i = i0 then r / 2 else 0) with hqdef
  have hmemsphere : ∀ s : SpatialCoordinates d, (∀ i, dist (s i) (z i) ≤ r / 2) →
      dist (s i0) (z i0) = r / 2 → s ∈ Metric.sphere z (r / 2) := by
    intro s hall heq
    rw [sphere_pi z (Or.inl (half_pos hr))]
    exact ⟨Set.mem_iUnion.mpr ⟨i0, heq⟩, (Metric.mem_closedBall).mpr
      ((dist_pi_le_iff (half_pos hr).le).mpr hall)⟩
  have hdist_pos : dist (p i0) (z i0) = r / 2 := by
    have heq : p i0 - z i0 = r / 2 := by
      show z i0 + (if i0 = i0 then r / 2 else 0) - z i0 = r / 2
      rw [if_pos rfl]; ring
    rw [Real.dist_eq, heq, abs_of_nonneg (half_pos hr).le]
  have hdist_neg : dist (q i0) (z i0) = r / 2 := by
    have heq : q i0 - z i0 = -(r / 2) := by
      show z i0 - (if i0 = i0 then r / 2 else 0) - z i0 = -(r / 2)
      rw [if_pos rfl]; ring
    rw [Real.dist_eq, heq, abs_neg, abs_of_nonneg (half_pos hr).le]
  have hbound_p : ∀ i, dist (p i) (z i) ≤ r / 2 := by
    intro i
    by_cases hi : i = i0
    · rw [hi, hdist_pos]
    · have heq : p i - z i = 0 := by
        show z i + (if i = i0 then r / 2 else 0) - z i = 0
        rw [if_neg hi]; ring
      rw [Real.dist_eq, heq, abs_zero]; exact (half_pos hr).le
  have hbound_q : ∀ i, dist (q i) (z i) ≤ r / 2 := by
    intro i
    by_cases hi : i = i0
    · rw [hi, hdist_neg]
    · have heq : q i - z i = 0 := by
        show z i - (if i = i0 then r / 2 else 0) - z i = 0
        rw [if_neg hi]; ring
      rw [Real.dist_eq, heq, abs_zero]; exact (half_pos hr).le
  refine ⟨p, ?_, q, ?_, ?_⟩
  · rw [hfr]; exact hmemsphere p hbound_p hdist_pos
  · rw [hfr]; exact hmemsphere q hbound_q hdist_neg
  · have hsum : (∑ i : Fin d, u i * p i) - ∑ i : Fin d, u i * q i =
        ∑ i : Fin d, u i * (p i - q i) := by
      rw [← Finset.sum_sub_distrib]; congr 1; funext i; ring
    have hpq : ∀ i : Fin d, p i - q i = if i = i0 then r else 0 := by
      intro i
      by_cases hi : i = i0
      · rw [hi]
        show p i0 - q i0 = if i0 = i0 then r else 0
        rw [if_pos rfl]
        show z i0 + (if i0 = i0 then r / 2 else 0) -
          (z i0 - (if i0 = i0 then r / 2 else 0)) = r
        rw [if_pos rfl]; ring
      · show z i + (if i = i0 then r / 2 else 0) -
          (z i - (if i = i0 then r / 2 else 0)) = if i = i0 then r else 0
        rw [if_neg hi, if_neg hi]; ring
    have hval : (∑ i : Fin d, u i * p i) - ∑ i : Fin d, u i * q i = u i0 * r := by
      rw [hsum]
      simp only [hpq, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ i0 (fun i : Fin d => u i * r)]
      simp
    intro hcontra
    rw [hcontra, sub_self] at hval
    exact (mul_ne_zero hi0 hr.ne') hval.symm

end SubdiffusiveProcess
