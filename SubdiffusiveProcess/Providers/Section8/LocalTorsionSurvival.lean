module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalTorsionSurvival

@[expose] public section

set_option autoImplicit false

noncomputable section

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
open MarkovProcess.LifetimePath
open scoped ENNReal NNReal


set_option linter.unusedVariables false in
/-- Uniform survival and exponential bounds from lower and upper mean exit times. -/

theorem SubdiffusiveProcess.Providers.Section8.local_torsion_survival (kappa A : ℝ)
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

:= by
  let a : ℝ := kappa / (2 * A)
  let e : ℝ := Real.exp (-kappa / 2)
  let c0 : ℝ := a * (1 - e)
  obtain ⟨hc0, hc0a, ha, heNonneg, heOne⟩ := localTorsion_constants hkappa hkappaA
  refine ⟨c0, hc0, ?_⟩
  intro d _hd law hMarkov U V hU _hBounded _hVU F hF hLower hUpper x hx
  letI : IsProbabilityMeasure (law x) := localTorsion_probability_instance law hMarkov x
  let t : ℝ≥0 := ⟨kappa * F / 2,
    (localTorsion_coefficients_nonneg hkappa.le (hkappa.trans_le hkappaA) hF).2.1⟩
  have ht : (t : ℝ≥0∞) = ENNReal.ofReal (kappa * F / 2) :=
    localTorsion_time_coe rfl
  let B : Set (Path d) := {w | (t : ℝ≥0∞) < exitTime U w}
  have hB : MeasurableSet B := localTorsion_survival_measurable U hU t
  have hmean := localTorsion_mean_comparison law hMarkov U hU hUpper x t
  have hbound : ENNReal.ofReal (kappa * F) ≤ ENNReal.ofReal (kappa * F / 2) +
      ENNReal.ofReal (A * F) * law x B := by
    rw [← ht]
    exact (hLower x hx).trans hmean
  have hprob : ENNReal.ofReal a ≤ law x B := localTorsion_survival_probability
    (law x) B hkappa.le (hkappa.trans_le hkappaA) hF hbound
  have hcprob : ENNReal.ofReal c0 ≤ law x B :=
    (ENNReal.ofReal_le_ofReal hc0a).trans hprob
  constructor
  · have hsurvival := localTorsion_survival_mono (law x) (exitTime U) hcprob
    simpa only [ht] using hsurvival
  · have htail : ∀ w ∈ B,
        (if exitTime U w = ∞ then 0 else
          ENNReal.ofReal (Real.exp (-(exitTime U w).toReal / F))) ≤ ENNReal.ofReal e := by
      intro w hw
      apply localTorsion_laplace_tail hkappa hF
      rw [← ht]
      exact hw.le
    exact (localTorsion_two_piece_integral (law x) hB htail
      (fun w ↦ localTorsion_laplace_one (exitTime U w) hF)).trans
        (localTorsion_weighted_bound (law x) hB ha.le heNonneg heOne hprob)
