import SubdiffusiveProcess.Section10.PhysicalSobolevBankBounds

open MeasureTheory Homogenization SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- The torsion cap pays two powers for Sobolev and at most one for mass. -/
def meanExitMomentOrder (q : ℝ) : ℝ := max 1 (3 * q)

def meanExitBankConstant (D k : ℝ) : ℝ := max 1 (D * k ^ 3)

theorem meanExitBankConstant_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {K : Ω → ℝ} {D C q : ℝ}
    (hK : Measurable K) (hKone : ∀ ω, 1 ≤ K ω) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hmoment : (∫⁻ ω, ENNReal.ofReal (K ω ^ meanExitMomentOrder q) ∂P) ≤
      ENNReal.ofReal C) :
    (∫⁻ ω, ENNReal.ofReal (meanExitBankConstant D (K ω) ^ q) ∂P) ≤
      ENNReal.ofReal (if 0 < q then 1 + D ^ q * C else 1) := by
  have hone : ∀ ω, 1 ≤ meanExitBankConstant D (K ω) := fun _ => le_max_left _ _
  split_ifs with hq
  · have hpow (ω) : meanExitBankConstant D (K ω) ^ q ≤
        1 + D ^ q * K ω ^ meanExitMomentOrder q := by
      have hk0 := zero_le_one.trans (hKone ω)
      have hp : (D * K ω ^ 3) ^ q = D ^ q * K ω ^ (3 * q) := by
        rw [Real.mul_rpow hD (pow_nonneg hk0 _), ← Real.rpow_natCast_mul hk0 3 q]
        norm_num
      rw [meanExitBankConstant, Real.rpow_max zero_le_one
        (mul_nonneg hD (pow_nonneg hk0 _)) hq.le, Real.one_rpow, hp]
      have he := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (hKone ω) (le_max_right 1 (3 * q)))
        (Real.rpow_nonneg hD q)
      exact max_le (le_add_of_nonneg_right (mul_nonneg
        (Real.rpow_nonneg hD q) (Real.rpow_nonneg hk0 _)))
        (he.trans (le_add_of_nonneg_left zero_le_one))
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal (1 + D ^ q * K ω ^ meanExitMomentOrder q) ∂P :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpow ω)
      _ = 1 + ENNReal.ofReal (D ^ q) *
          (∫⁻ ω, ENNReal.ofReal (K ω ^ meanExitMomentOrder q) ∂P) := by
        simp_rw [ENNReal.ofReal_add zero_le_one
          (mul_nonneg (Real.rpow_nonneg hD q)
            (Real.rpow_nonneg (zero_le_one.trans (hKone _)) _)),
          ENNReal.ofReal_mul (Real.rpow_nonneg hD q), ENNReal.ofReal_one]
        rw [lintegral_add_left measurable_const, lintegral_const_mul]
        · simp
        · exact ENNReal.measurable_ofReal.comp (hK.pow measurable_const)
      _ ≤ 1 + ENNReal.ofReal (D ^ q) * ENNReal.ofReal C := by gcongr
      _ = ENNReal.ofReal (1 + D ^ q * C) := by
        rw [ENNReal.ofReal_add zero_le_one (mul_nonneg (Real.rpow_nonneg hD q) hC),
          ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.rpow_nonneg hD q)]
  · calc
      _ ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂P := lintegral_mono fun ω => by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
          (Real.rpow_le_one_of_one_le_of_nonpos (hone ω) (le_of_not_gt hq))
      _ = ENNReal.ofReal 1 := by simp

/-- The actual upper mass projection bounds the unit-cube mass factor in the
torsion cap. No lower mass or cutoff-energy projection is required. -/
theorem PhysicalStaticBounds.unitCube_mass_power_le {d : ℕ} (hd : 2 ≤ d)
    {b A : SpatialCoordinates d → ℝ} {B K : ℝ}
    (h : PhysicalStaticBounds b A B K) (hK : 1 ≤ K) :
    (weightedMeasure b (Metric.ball (0 : SpatialCoordinates d) (1 / 2))).toReal ^
      (1 / (d : ℝ)) ≤ K := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hmass := h.1 0 (Metric.mem_ball_self (by norm_num)) (1 / 2)
    (by norm_num) (by norm_num)
  have hpow : (1 / 2 : ℝ) ^ ((d : ℝ) - 1 / 2) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
  have hmassLe := hmass.trans (ENNReal.ofReal_le_ofReal
    (mul_le_of_le_one_right (zero_le_one.trans hK) hpow))
  have hm := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmassLe
  rw [ENNReal.toReal_ofReal (zero_le_one.trans hK)] at hm
  have he : 1 / (d : ℝ) ≤ 1 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  exact (Real.rpow_le_rpow ENNReal.toReal_nonneg hm (by positivity)).trans
    (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hK he)


end SubdiffusiveProcess.Section10
