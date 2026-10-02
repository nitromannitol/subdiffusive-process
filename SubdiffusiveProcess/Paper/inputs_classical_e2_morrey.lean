import SubdiffusiveProcess.Morrey.Transport
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.NativeBridge

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- E2: Morrey on a cube, stated by the actual difference bound. -/
theorem inputs_classical_e2_morrey (d : ℕ) (p alpha : ℝ)
    (hp : 2 ≤ p) (halpha : 0 < alpha) (hpa : alpha < 1 - (d : ℝ) / p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x0 : Vec d) (l : ℝ), 0 < l →
      ∀ u : H1Function (Metric.ball x0 l),
        MemLp (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i) ^ 2))
          (ENNReal.ofReal p) (volume.restrict (Metric.ball x0 l)) →
        ∃ U : Vec d → ℝ, Continuous U ∧
          (u.toFun =ᵐ[volume.restrict (Metric.ball x0 l)] U) ∧
          ∀ x ∈ Metric.closedBall x0 l, ∀ y ∈ Metric.closedBall x0 l,
            |U x - U y| ≤ C * l ^ (1 - alpha) *
              ((eLpNorm (fun q => Real.sqrt (∑ i : Fin d, (u.grad q i) ^ 2))
                (ENNReal.ofReal p) (volume.restrict (Metric.ball x0 l))).toReal /
                (volume.real (Metric.ball x0 l)) ^ (1 / p)) * ‖x - y‖ ^ alpha := by
  simpa only [euclideanNorm, vecNormSq, vecDot, pow_two] using
    (SubdiffusiveProcess.Morrey.morrey_cube d p alpha hp halpha hpa)

end Paper
