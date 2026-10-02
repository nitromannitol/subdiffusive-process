import Homogenization.Sobolev.Foundations.AxisCube
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
import SubdiffusiveProcess.Providers.Section8.LocalTorsionSurvival
set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section

set_option linter.unusedVariables false in

theorem SubdiffusiveProcess.Frozen.Section8.local_torsion_survival (kappa A : ℝ)
    (hkappa : 0 < kappa) (hkappaA : kappa ≤ A) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ d : ℕ, ∀ hd : 2 ≤ d, ∀ law : Kernel (Vec d) (Path d),
      StrongMarkov law → ∀ U V : Set (Vec d), IsOpen U → Bornology.IsBounded U →
      V ⊆ U → ∀ F : ℝ, 0 < F →
      (∀ x ∈ V, ENNReal.ofReal (kappa * F) ≤ meanExit law U x) →
      (∀ x ∈ U, meanExit law U x ≤ ENNReal.ofReal (A * F)) →
        ∀ x ∈ V,
          ENNReal.ofReal c0 ≤
            law x {w | ENNReal.ofReal (kappa * F / 2) ≤ LifetimePath.exitTime U w} ∧
          (∫⁻ w, (if LifetimePath.exitTime U w = ∞ then 0 else
            ENNReal.ofReal (Real.exp (-(LifetimePath.exitTime U w).toReal / F))) ∂law x) ≤
              ENNReal.ofReal (1 - c0)

:= SubdiffusiveProcess.Providers.Section8.local_torsion_survival kappa A hkappa hkappaA
