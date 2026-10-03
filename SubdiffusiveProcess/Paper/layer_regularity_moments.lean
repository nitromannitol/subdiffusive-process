module

public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.OrliczLpNorm
public import SubdiffusiveProcess.Frozen.Assumptions.G2Observable
public import SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess
open scoped ENNReal

namespace Paper



theorem layer_regularity_moments {d : Nat} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ p : ℝ, 1 ≤ p →
        eLpNorm (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable (d := d))
          (ENNReal.ofReal p)
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure ≤
        ENNReal.ofReal (C * M.delta * Real.sqrt p) := by
  obtain ⟨C₀, hC₀, hC₀_bound⟩ :=
    SubdiffusiveProcess.exists_universal_orlicz_eLpNorm_constant
  have hsqrt_two_pos : 0 < Real.sqrt (2 : ℝ) := by positivity
  refine ⟨C₀ * Real.sqrt 2, mul_pos hC₀ hsqrt_two_pos, ?_⟩
  intro M p hp
  let X : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
  let μ : Measure (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
    (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
  have hδ : 0 < M.delta := M.shellPrefix.delta_pos
  have hXmeas : Measurable X := by
    dsimp [X]
    exact SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_measurable
  have hX0 : ∀ g, 0 ≤ X g := by
    intro g
    dsimp [X]
    exact SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg g
  have hreg : SubdiffusiveProcess.OGammaLE μ 2 M.delta X := by
    simpa [X, μ] using M.G2.regularity_expectation
  rw [SubdiffusiveProcess.OGammaLE] at hreg
  have hExp : (∫⁻ g, ENNReal.ofReal (Real.exp ((X g / M.delta) ^ (2 : ℕ))) ∂μ) ≤ 2 := by
    have hInt : Integrable (fun g => Real.exp ((X g / M.delta) ^ (2 : ℕ))) μ := by
      convert hreg.1 using 1
      funext g
      rw [max_eq_left (hX0 g)]
      dsimp [X]
      congr 1
      simp [div_eq_mul_inv, mul_comm]
    have hBound : (∫ g, Real.exp ((X g / M.delta) ^ (2 : ℕ)) ∂μ) ≤ 2 := by
      convert hreg.2 using 1
      congr 1
      funext g
      rw [max_eq_left (hX0 g)]
      dsimp [X]
      congr 1
      simp [div_eq_mul_inv, mul_comm]
    have hEq := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun g => (Real.exp_pos _).le)
    calc
      (∫⁻ g, ENNReal.ofReal (Real.exp ((X g / M.delta) ^ (2 : ℕ))) ∂μ) =
          ENNReal.ofReal (∫ g, Real.exp ((X g / M.delta) ^ (2 : ℕ)) ∂μ) := hEq.symm
      _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hBound
      _ = 2 := by norm_num
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hsqrt_two : 1 ≤ Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hsqrt_p : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  by_cases hp2 : 2 ≤ p
  · have hlarge :
        eLpNorm X (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (C₀ * M.delta * Real.sqrt p) := by
      have h := hC₀_bound μ X M.delta hXmeas hX0 hδ hExp
        (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top
        (by simpa using ENNReal.ofReal_le_ofReal hp2)
      simpa [ENNReal.toReal_ofReal hp0] using h
    have hcoeff : C₀ * M.delta ≤ (C₀ * Real.sqrt 2) * M.delta := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      calc
        C₀ = C₀ * 1 := by ring
        _ ≤ C₀ * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_left hsqrt_two hC₀.le
    have hlarge' :
        ENNReal.ofReal (C₀ * M.delta * Real.sqrt p) ≤
          ENNReal.ofReal ((C₀ * Real.sqrt 2) * M.delta * Real.sqrt p) := by
      apply ENNReal.ofReal_mono
      exact mul_le_mul_of_nonneg_right hcoeff hsqrt_p
    exact hlarge.trans hlarge'
  · have hp_le_two : p ≤ 2 := le_of_not_ge hp2
    have htwo : eLpNorm X (2 : ℝ≥0∞) μ ≤
        ENNReal.ofReal (C₀ * M.delta * Real.sqrt 2) := by
      have h := hC₀_bound μ X M.delta hXmeas hX0 hδ hExp
        (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      simpa using h
    have hmono : eLpNorm X (ENNReal.ofReal p) μ ≤ eLpNorm X 2 μ := by
      exact MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
        (p := ENNReal.ofReal p) (q := 2) (μ := μ) (f := X)
        (by simpa using ENNReal.ofReal_le_ofReal hp_le_two)
    have hsmall :
        ENNReal.ofReal (C₀ * M.delta * Real.sqrt 2) ≤
          ENNReal.ofReal ((C₀ * Real.sqrt 2) * M.delta * Real.sqrt p) := by
      apply ENNReal.ofReal_mono
      have hsqrt_p_one : 1 ≤ Real.sqrt p := by
        nlinarith [Real.sq_sqrt hp0]
      calc
        C₀ * M.delta * Real.sqrt 2 =
            (C₀ * M.delta) * Real.sqrt 2 := by ring
        _ ≤ (C₀ * M.delta) * (Real.sqrt 2 * Real.sqrt p) := by
          have hmul : Real.sqrt 2 ≤ Real.sqrt 2 * Real.sqrt p := by
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hsqrt_p_one hsqrt_two_pos.le)
          exact mul_le_mul_of_nonneg_left hmul
            (mul_nonneg hC₀.le hδ.le)
        _ = (C₀ * Real.sqrt 2) * M.delta * Real.sqrt p := by ring
    exact hmono.trans (htwo.trans hsmall)

end Paper
