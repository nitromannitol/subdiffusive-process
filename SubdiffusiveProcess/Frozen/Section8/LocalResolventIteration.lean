import Homogenization.Sobolev.Foundations.AxisCube
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
import SubdiffusiveProcess.Providers.Section8.LocalResolventIteration
set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section

set_option linter.unusedVariables false in

theorem SubdiffusiveProcess.Frozen.Section8.local_resolvent_iteration (p0 : ℝ) (hp0 : 2 < p0) :
    ∃ N0 : ℕ, ∃ C : ℝ, 0 < N0 ∧ 0 < C ∧
      ∀ d : ℕ, ∀ hd : 2 ≤ d, ∀ c rho : Vec d → ℝ, ∀ law : Kernel (Vec d) (Path d),
        LocalDiffusion c rho law → ∀ y : Vec d, ∀ side : ℝ, 0 < side →
        let U := Homogenization.axisCube y side
        let mu := (weightedMeasure rho).restrict U
        let mass := ((weightedMeasure rho) U).toReal
        ∀ A F : ℝ, 1 ≤ A → 0 < F → SobolevAssumption c rho U p0 A F →
          (∀ s : ℝ, 0 < s → ∀ f : Vec d → ℝ, MemLp f 1 mu →
            eLpNorm ((killedResolvent law U s)^[N0] f) ∞ mu ≤
              ENNReal.ofReal (C * A ^ C / mass * (1 + F / s) ^ ((1 - 2 / p0)⁻¹)) *
                eLpNorm f 1 mu) ∧
          (∀ p : ℝ → Vec d → Vec d → ℝ, IsKilledDensity law rho U p →
            (∀ t : ℝ, 0 < t →
              ∀ᵐ z ∂(mu.prod mu),
                p t z.1 z.2 ≤ C * A ^ C / mass * (1 + F / t) ^ ((1 - 2 / p0)⁻¹)) ∧
            (ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2)
                (Ioi 0 ×ˢ U ×ˢ U) →
              ∀ t : ℝ, 0 < t → ∀ x ∈ U,
                p t x x ≤ C * A ^ C / mass * (1 + F / t) ^ ((1 - 2 / p0)⁻¹)))

:= SubdiffusiveProcess.Providers.Section8.local_resolvent_iteration p0 hp0
