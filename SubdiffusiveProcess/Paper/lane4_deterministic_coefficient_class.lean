import SubdiffusiveProcess.Lane4.Carriers

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lane4_deterministic_coefficient_class :
  ∀ (d : ℕ) (a : SpatialCoordinates d → ℝ), Continuous a → (∀ x, 0 < a x) →
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    ∃ c C : ℝ, 0 < c ∧
      (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), c ≤ a x ∧ a x ≤ C) ∧
      (∀ (I P : Finset (Fin d)),
        ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
          c ≤ a (coordinateFold z I P x) ∧ a (coordinateFold z I P x) ≤ C) := by
  intro d a ha hpos z r hr
  have hcpt : IsCompact (closedCube z r hr : Set (SpatialCoordinates d)) :=
    (closedCube z r hr).isCompact
  have hne : (closedCube z r hr : Set (SpatialCoordinates d)).Nonempty := by
    refine ⟨z, ?_⟩
    show z ∈ Metric.closedBall z (r / 2)
    exact Metric.mem_closedBall_self (by positivity)
  obtain ⟨x0, _hx0, hmin⟩ := hcpt.exists_isMinOn hne ha.continuousOn
  obtain ⟨x1, _hx1, hmax⟩ := hcpt.exists_isMaxOn hne ha.continuousOn
  refine ⟨a x0, a x1, hpos x0, fun x hx => ⟨hmin hx, hmax hx⟩, fun I P x hx => ?_⟩
  have hfold : coordinateFold z I P x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) :=
    coordinateFold_mem_closedCube z hr I P hx
  exact ⟨hmin hfold, hmax hfold⟩

end Paper
