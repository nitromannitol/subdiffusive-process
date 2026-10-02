import SubdiffusiveProcess.Section10.ExitLowerMomentsPaley
import MarkovProcess.Path.ExitTime

open MeasureTheory ProbabilityTheory Topology Set MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.ExitLowerMoments

/-- Literal continuous-law consumer of the killed-semigroup second moment.
Only the mean bounds are premises; the positive-moment lower bound is proved. -/
theorem continuous_moment_lower_of_mean_bounds {d : ℕ}
    (law : Kernel (Homogenization.Vec d) (DiffusionPath d)) [IsMarkovKernel law]
    (hSM : SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov
      (law.map LifetimePath.ofContinuousPath))
    (U : Set (Homogenization.Vec d)) (hU : IsOpen U) (K : ℝ≥0) (hK : 1 ≤ K)
    (hupper : ∀ y ∈ U, (∫⁻ w, ContinuousPath.exitTime U w ∂law y) ≤ (K : ℝ≥0∞))
    (A : ℝ) (hA : 0 < A) (x : Homogenization.Vec d)
    (hlower : ENNReal.ofReal A ≤ ∫⁻ w, ContinuousPath.exitTime U w ∂law x)
    (p : ℝ) (hp : 0 < p) :
    ENNReal.ofReal ((A/4)^p *
      (A^2/(4*(SubdiffusiveProcess.Section10.ExitTailMoments.upperMomentConstant 2 * (K : ℝ)^2)))) ≤
        ∫⁻ w, ContinuousPath.exitTime U w ^ p ∂law x := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hK)
  have hB : 0 < SubdiffusiveProcess.Section10.ExitTailMoments.upperMomentConstant 2 * (K : ℝ)^2 :=
    mul_pos (SubdiffusiveProcess.Section10.ExitTailMoments.upperMomentConstant_pos 2 (by norm_num))
      (pow_pos hKpos _)
  have hs : (∫⁻ w, ContinuousPath.exitTime U w ^ (2 : ℕ) ∂law x) ≤
      ENNReal.ofReal (SubdiffusiveProcess.Section10.ExitTailMoments.upperMomentConstant 2 * (K : ℝ)^2) := by
    have hu := SubdiffusiveProcess.Section10.ExitTailMoments.lifetime_upper_moment
      (law.map LifetimePath.ofContinuousPath) hSM U hU K hK
      (fun y hy => by rw [SubdiffusiveProcess.Section10.ExitTailMoments.continuous_meanExit_transport law U hU y]
                      exact hupper y hy) 2 (by norm_num) x
    change (∫⁻ w, LifetimePath.exitTime U w ^ (2 : ℝ)
      ∂(law.map LifetimePath.ofContinuousPath) x) ≤ _ at hu
    rw [SubdiffusiveProcess.Section10.ExitTailMoments.continuous_exitMoment_transport law U hU 2 x] at hu
    simpa only [ENNReal.rpow_two, Real.rpow_two] using hu
  exact moment_lower_of_mean_and_second_moment (law x) (ContinuousPath.exitTime U)
    (ContinuousPath.isStoppingTime_exitTime U hU).measurable' A
    (SubdiffusiveProcess.Section10.ExitTailMoments.upperMomentConstant 2 * (K : ℝ)^2) p hA hB hp hlower hs

end SubdiffusiveProcess.Section10.ExitLowerMoments
