import Homogenization.Sobolev.Foundations.AxisCube
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
import SubdiffusiveProcess.Providers.Section8.LocalResolventExitUpper
set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section

set_option linter.unusedVariables false in

theorem SubdiffusiveProcess.Frozen.Section8.local_resolvent_exit_upper (p0 : ℝ) (hp0 : 2 < p0) :
    ∃ c0 C : ℝ, 0 < c0 ∧ 0 < C ∧
      ∀ d : ℕ, ∀ hd : 2 ≤ d, ∀ c rho : Vec d → ℝ, ∀ law : Kernel (Vec d) (Path d),
        LocalDiffusion c rho law → ∀ y : Vec d, ∀ side : ℝ, 0 < side →
        let U := Homogenization.axisCube y side
        ∀ A F : ℝ, 1 ≤ A → 0 < F →
          ((SobolevAssumption c rho U p0 A F ∧ PoincareAssumption c rho U A F) →
            ∀ p : ℝ → Vec d → Vec d → ℝ, IsKilledDensity law rho U p →
              ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2)
                (Ioi 0 ×ˢ U ×ˢ U) →
              (∀ t : ℝ, 0 < t → ∀ x ∈ U,
                law x {w | ENNReal.ofReal t < LifetimePath.exitTime U w} ≤
                  ENNReal.ofReal (C * A ^ C * Real.exp (-c0 * t / (A * F)))) ∧
              (∀ x ∈ U, meanExit law U x ≤ ENNReal.ofReal (C * A ^ C * F))) ∧
          ((∀ f : H10Function U,
            lpSq rho U p0 f.toH1Function.toFun ≤
              ENNReal.ofReal (A * (((weightedMeasure rho) U).toReal) ^ (-(1 - 2 / p0)) *
                F * energy c U f.toH1Function)) →
            SobolevAssumption c rho U p0 A F ∧ PoincareAssumption c rho U A F)

:= SubdiffusiveProcess.Providers.Section8.local_resolvent_exit_upper p0 hp0
