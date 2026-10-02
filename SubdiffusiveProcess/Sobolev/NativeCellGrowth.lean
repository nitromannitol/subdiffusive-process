import SubdiffusiveProcess.Sobolev.NativeBoundaryMinimizer

/-! Convert a native cell's radius-one gradient bound to its full energy bound.
The coefficient and function are fixed; no probabilistic or limiting estimate is asserted. -/

open MeasureTheory Set TopologicalSpace Homogenization SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
namespace SubdiffusiveProcess
noncomputable section

/-- A radius-one gradient bound controls the native energy on a cell of side at most one. -/
theorem native_energy_le_of_unit_growth
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (a : PositiveCoefficient (centeredCube z r hr)) (c : SpatialCoordinates d → ℝ)
    (hc : (fun x => a.val x) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c)
    (v : H1Function (centeredCube z r hr : Set (SpatialCoordinates d))) (B : ℝ)
    (hB : localGradientEnergy a
      (s := Metric.ball z 1 ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
      (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
      (sobolevGradient (sobolevDataOfH1 v)) ≤ B) :
    energy c (centeredCube z r hr : Set (SpatialCoordinates d)) v ≤ B := by
  rw [energy_eq_sobolevCoefficientForm a c hc]
  simpa only [centeredCube_unit_ball_inter z hr hr1,
    localGradientEnergy_domain_eq_sobolevCoefficientForm] using hB

end
end SubdiffusiveProcess
