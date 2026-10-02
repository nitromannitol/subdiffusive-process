import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.Numeric
import SubdiffusiveProcess.Analysis.PrimitiveHolderControl

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lem_primitive_holder_upgrade :
  ∀ (d : ℕ), 2 ≤ d →
  ∀ (C_log : ℝ), 0 < C_log →
  ∃ C_holder C_cube : ℝ, 0 < C_holder ∧ 0 < C_cube ∧
  ∀ (R : ℝ) (hR : 0 < R) (z : SpatialCoordinates d)
    (Kf : ℝ) (g : SpatialCoordinates d → Fin d → ℝ), 0 ≤ Kf →
    (∀ x y : SpatialCoordinates d,
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
      Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
        C_log * Kf * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) *
          (1 + Real.log (R / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)))) →
    (∀ x y : SpatialCoordinates d,
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
      C_log * Kf * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) *
          (1 + Real.log (R / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ≤
        C_holder * Real.sqrt R * Kf *
          Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ∧
      Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
        C_holder * Real.sqrt R * Kf *
          Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ∧
    (∀ x ∈ (closedCube z R hR : Set (SpatialCoordinates d)),
          ∀ y ∈ (closedCube z R hR : Set (SpatialCoordinates d)),
            Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
              C_cube * Real.sqrt R * Kf *
                Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ∧
        BddAbove {v : ℝ | ∃ x ∈ (closedCube z R hR : Set (SpatialCoordinates d)),
          ∃ y ∈ (closedCube z R hR : Set (SpatialCoordinates d)), x ≠ y ∧
            v = Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) /
              Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))} ∧
        halfHolderSeminorm (closedCube z R hR : Set (SpatialCoordinates d)) g ≤
      C_cube * Real.sqrt R * Kf := by
  exact SubdiffusiveProcess.Analysis.primitiveHolderControl

end Paper
