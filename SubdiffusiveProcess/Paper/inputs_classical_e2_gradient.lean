import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Meyers.Final
import SubdiffusiveProcess.Paper.classical_meyers_gradient

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false




noncomputable section
namespace Paper

/-- E2: the classical interior W1p estimate for small scalar perturbations. -/
theorem inputs_classical_e2_gradient (d : ℕ) (p : ℝ) (hp : 2 ≤ p) :
    ∃ epsilon C : ℝ, 0 < epsilon ∧ epsilon ≤ 1 / 2 ∧ 0 < C ∧
      ∀ (x0 : Vec d) (l : ℝ), 0 < l →
      ∀ (a : Vec d → ℝ) (a0 : ℝ), 0 < a0 →
        AEMeasurable a (volume.restrict (Metric.ball x0 (2 * l))) →
        (∀ᵐ x ∂volume.restrict (Metric.ball x0 (2 * l)), |a x - a0| ≤ epsilon * a0) →
      ∀ (F : Vec d → ℝ) (Kf : ℝ),
        AEMeasurable F (volume.restrict (Metric.ball x0 (2 * l))) → 0 ≤ Kf →
        (∀ᵐ x ∂volume.restrict (Metric.ball x0 (2 * l)), |F x| ≤ Kf) →
      ∀ u : H1Function (Metric.ball x0 (2 * l)),
        (∀ phi : H10Function (Metric.ball x0 (2 * l)),
          (∫ x in Metric.ball x0 (2 * l),
            a x * (∑ i : Fin d, u.grad x i * phi.toH1Function.grad x i)) =
          ∫ x in Metric.ball x0 (2 * l), F x * phi.toH1Function.toFun x) →
        MemLp (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2))
          (ENNReal.ofReal p) (volume.restrict (Metric.ball x0 l)) ∧
        (eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2))
          (ENNReal.ofReal p) (volume.restrict (Metric.ball x0 l))).toReal /
          (volume.real (Metric.ball x0 l)) ^ (1 / p) ≤
        C * ((eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2))
          2 (volume.restrict (Metric.ball x0 (2 * l)))).toReal /
          (volume.real (Metric.ball x0 (2 * l))) ^ (1 / 2 : ℝ)) + C * l * a0⁻¹ * Kf := by
  by_cases hd : 2 ≤ d
  · exact SubdiffusiveProcess.Meyers.e2_from_leaf hd hp (classical_meyers_gradient d hd p hp)
  · exact SubdiffusiveProcess.Meyers.e2_lowdim (by omega) hp

end Paper
