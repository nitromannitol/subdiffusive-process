import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli
import SubdiffusiveProcess.Besov.KilledMain

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_poincare_killed_endpoint {d : ℕ}
    [NeZero d] :
    (∃ K : ℝ, 0 < K ∧
      ∀ u : Homogenization.H10Function
        (Homogenization.openCubeSet (Homogenization.originCube d 0)),
        Homogenization.cubeLpNorm (Homogenization.originCube d 0) (2 : ℝ≥0∞)
            u.toH1Function.toFun ≤
          K * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
            (Homogenization.originCube d 0) 1 (.finite 1) u.toH1Function.grad) := by
  exact SubdiffusiveProcess.Besov.Detach.killed_endpoint_main

end Paper

