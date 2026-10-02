import SubdiffusiveProcess.Assumptions.OGammaBridge
import Homogenization.Probability.IndependentSums.GammaSigma.Basic

open MeasureTheory
open scoped ENNReal
open Homogenization IndependentSums
noncomputable section

namespace SubdiffusiveProcess

theorem exists_universal_orlicz_eLpNorm_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → ℝ) (A : ℝ),
        Measurable X →
        (∀ ω, 0 ≤ X ω) →
        0 < A →
        (∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / A) ^ (2 : ℕ))) ∂μ) ≤ 2 →
        ∀ p : ℝ≥0∞, p ≠ ∞ → 2 ≤ p →
          eLpNorm X p μ ≤
            ENNReal.ofReal (C * A * Real.sqrt p.toReal) := by
  let C : ℝ := gammaMomentConst 2 * Real.sqrt (1 + Real.log 2)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact mul_pos (gammaMomentConst_pos (by norm_num))
      (Real.sqrt_pos.mpr (by linarith))
  · intro Ω _ μ _ X A hXm hX0 hA hExp p hp_top hp2
    have hp0 : p ≠ 0 := by
      have : (0 : ℝ≥0∞) < p := lt_of_lt_of_le (by norm_num) hp2
      exact this.ne'
    have hq2 : 2 ≤ p.toReal := by
      have h := (ENNReal.toReal_le_toReal (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hp_top).2 hp2
      simpa using h
    have hq1 : 1 ≤ p.toReal := le_trans (by norm_num) hq2
    have hq0 : 0 < p.toReal := lt_of_lt_of_le (by norm_num) hq2
    have hphi_meas :
        Measurable (fun ω => Real.exp ((A⁻¹ * max (X ω) 0) ^ (2 : ℝ))) := by
      exact (measurable_const.mul (hXm.max measurable_const)).pow_const 2 |>.exp
    have hphi_lint :
        (∫⁻ ω, ENNReal.ofReal (Real.exp ((A⁻¹ * max (X ω) 0) ^ (2 : ℝ))) ∂μ) ≤ 2 := by
      refine (lintegral_congr_ae ?_).trans_le hExp
      filter_upwards [] with ω
      rw [max_eq_left (hX0 ω), Real.rpow_two]
      simp only [div_eq_mul_inv]
      ring
    have hphi_int :
        Integrable (fun ω => Real.exp ((A⁻¹ * max (X ω) 0) ^ (2 : ℝ))) μ := by
      apply (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        hphi_meas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).1
      exact ne_of_lt (lt_of_le_of_lt hphi_lint (by norm_num))
    have hphi_integral_le :
        (∫ ω, Real.exp ((A⁻¹ * max (X ω) 0) ^ (2 : ℝ)) ∂μ) ≤ 2 := by
      have hEq := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hphi_int
        (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
      have hle :
          ENNReal.ofReal (∫ ω, Real.exp ((A⁻¹ * max (X ω) 0) ^ (2 : ℝ)) ∂μ) ≤
            ENNReal.ofReal 2 := by
        rw [hEq]
        simpa using hphi_lint
      exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hle
    have hOG : SubdiffusiveProcess.OGammaLE μ 2 A X := by
      refine ⟨?_, ?_⟩
      · simpa [SubdiffusiveProcess.OGammaLE] using hphi_int
      · simpa [SubdiffusiveProcess.OGammaLE] using hphi_integral_le
    have hBig := SubdiffusiveProcess.OGammaBridge.isBigO_gammaSigma_of_ogammaLE
      (μ := μ) (σ := 2) (A := A) (X := X)
      (by norm_num) hA hX0 hOG
    let K : ℝ := (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * A
    have hBigWith : IsBigOWith μ (gammaSigma 2) X K := by
      rw [IsBigO] at hBig
      simpa [K, abs_of_nonneg (hX0 _)] using hBig
    have hraw :
        (∫⁻ ω, ENNReal.ofReal (X ω ^ p.toReal) ∂μ) ≤
          ENNReal.ofReal
            ((gammaMomentConst 2 * p.toReal ^ (2 : ℝ)⁻¹ * K) ^ p.toReal) := by
      exact lintegral_rpow_le_of_isBigOWith_gammaSigma
        (μ := μ) (Y := X) (K := K) (σ := 2) (p := p.toReal)
        (by norm_num) (by
          dsimp [K]
          positivity) hq1 hX0 hXm.aemeasurable hBigWith
    have hBpos :
        0 < gammaMomentConst 2 * p.toReal ^ (2 : ℝ)⁻¹ * K := by
      exact mul_pos
        (mul_pos (gammaMomentConst_pos (by norm_num))
          (Real.rpow_pos_of_pos hq0 _))
        (by
          dsimp [K]
          positivity)
    have hB_eq :
        gammaMomentConst 2 * p.toReal ^ (2 : ℝ)⁻¹ * K =
          C * A * Real.sqrt p.toReal := by
      dsimp [C, K]
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      ring
    rw [eLpNorm_eq_lintegral_rpow_enorm hp0 hp_top]
    calc
      (∫⁻ ω, ‖X ω‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) =
          (∫⁻ ω, ENNReal.ofReal (X ω ^ p.toReal) ∂μ) ^ (1 / p.toReal) := by
            congr 1
            apply lintegral_congr
            intro ω
            rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]
            exact ENNReal.ofReal_rpow_of_nonneg (hX0 ω) hq0.le
      _ ≤
          (ENNReal.ofReal
            ((gammaMomentConst 2 * p.toReal ^ (2 : ℝ)⁻¹ * K) ^ p.toReal)) ^
              (1 / p.toReal) :=
        ENNReal.rpow_le_rpow hraw (by positivity)
      _ = ENNReal.ofReal (C * A * Real.sqrt p.toReal) := by
        rw [← hB_eq]
        rw [← ENNReal.ofReal_rpow_of_nonneg hBpos.le hq0.le]
        rw [← ENNReal.rpow_mul]
        have hq_cancel : p.toReal * (1 / p.toReal) = 1 := by
          field_simp
        rw [hq_cancel, ENNReal.rpow_one]

end SubdiffusiveProcess
