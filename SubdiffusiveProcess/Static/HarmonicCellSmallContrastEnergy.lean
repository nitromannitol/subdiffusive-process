import SubdiffusiveProcess.Static.CutoffHolderEnergyGrowth
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.InteriorGradient
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.CampanatoGeometry

/-! # Literal microscopic energy growth from the proved native small-contrast row -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section
namespace SubdiffusiveProcess.Static

/-- A native gradient Morrey row with exponent three quarters bounds the literal
weighted energy on every interior Euclidean ball. -/
theorem interior_energy_growth_of_gradient_row {d : ℕ} [NeZero d]
    (u : H1Function (smallContrastUnitBall d)) (a : Vec d → ℝ)
    {K Lam : ℝ} (hK : 0 ≤ K) (hLam : 0 ≤ Lam)
    (ha : ∀ x ∈ smallContrastUnitBall d, a x ≤ Lam)
    (hrow : HasInteriorSmallContrastGradientScaleBound (3 / 4 : ℝ) K u)
    (z : Vec d) (hz : z ∈ smallContrastBall d (1 / 2))
    (r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1 / 2) :
    ∫⁻ x in euclideanBall z r, ENNReal.ofReal (a x * vecDot (u.grad x) (u.grad x)) ≤
      ENNReal.ofReal (Lam * (volume (smallContrastUnitBall d)).toReal * K ^ 2 *
        r ^ ((d : ℝ) - 1 / 2)) := by
  have hsub : euclideanBall z r ⊆ smallContrastUnitBall d := by
    have hsubr : euclideanBall z r ⊆ euclideanBall z (1 / 2) := by
      rcases eq_or_lt_of_le hrhalf with heq | hlt
      · rw [heq]
      · exact euclideanBall_subset_euclideanBall hr.le hlt
    exact hsubr.trans (euclideanBall_half_subset_unit_of_mem_half hz)
  have hgr : MemVectorL2 (euclideanBall z r) u.grad :=
    u.grad_memVectorL2.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hint : IntegrableOn (fun x => (1 : ℝ) * vecNormSq (u.grad x))
      (euclideanBall z r) := by
    simpa only [one_mul] using integrableOn_vecDot_of_memVectorL2 hgr hgr
  have hnorm : vectorNormalizedL2On (euclideanBall z r) u.grad ≤ r ^ (-1 / 4 : ℝ) * K := by
    have h := hrow z hz r hr hrhalf
    norm_num only at h
    have hcancel : r ^ (1 / 4 : ℝ) * r ^ (-1 / 4 : ℝ) = 1 := by
      rw [← Real.rpow_add hr]
      norm_num
    have hmul := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hr.le (-1 / 4 : ℝ))
    rw [← mul_assoc, mul_comm (r ^ (-1 / 4 : ℝ)), hcancel, one_mul] at hmul
    exact hmul
  have hb : vectorNormalizedL2On (euclideanBall z r)
      (fun x => Real.sqrt (1 : ℝ) • u.grad x) ≤ r ^ (-1 / 4 : ℝ) * K := by
    simpa only [Real.sqrt_one, one_smul] using hnorm
  have hvol : 0 < (volume (euclideanBall z r)).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero z hr))
  have hraw := lintegral_energy_le_volume_mul_sq (euclideanBall z r)
    (fun _ => (1 : ℝ)) u.grad (fun _ => zero_le_one) hvol hint
    (mul_nonneg (Real.rpow_nonneg hr.le _) hK) hb
  simp only [one_mul] at hraw
  have hpowers : r ^ d * (r ^ (-1 / 4 : ℝ)) ^ 2 = r ^ ((d : ℝ) - 1 / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul_natCast hr.le, ← Real.rpow_add hr]
    congr 1
    ring
  calc
    (∫⁻ x in euclideanBall z r, ENNReal.ofReal (a x * vecDot (u.grad x) (u.grad x)))
        ≤ ∫⁻ x in euclideanBall z r,
          ENNReal.ofReal (Lam * vecDot (u.grad x) (u.grad x)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (isOpen_euclideanBall z r).measurableSet] with x hx
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (ha x (hsub hx))
        (Section6BoundaryL2.vecDot_self_nonneg _))
    _ = ENNReal.ofReal Lam * ∫⁻ x in euclideanBall z r,
          ENNReal.ofReal (vecDot (u.grad x) (u.grad x)) := by
      simp_rw [ENNReal.ofReal_mul hLam]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Lam * ENNReal.ofReal
        ((volume (euclideanBall z r)).toReal * (r ^ (-1 / 4 : ℝ) * K) ^ 2) :=
      mul_le_mul_right hraw _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hLam, volume_euclideanBall_toReal_eq_unit_mul_pow z hr,
        mul_pow]
      congr 1
      calc
        Lam * ((volume (smallContrastUnitBall d)).toReal * r ^ d *
            ((r ^ (-1 / 4 : ℝ)) ^ 2 * K ^ 2)) =
          Lam * (volume (smallContrastUnitBall d)).toReal * K ^ 2 *
            (r ^ d * (r ^ (-1 / 4 : ℝ)) ^ 2) := by ring
        _ = _ := by rw [hpowers]

/-- The proved perturbative estimate supplies the literal microscopic energy
row without a carried Meyers or Morrey theorem. -/
theorem interior_energy_growth_of_smallContrast {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (a : Vec d → ℝ) (u : H1Function (smallContrastUnitBall d))
    (F : Vec d → Vec d) {lam Lam delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d (3 / 4 : ℝ))
    (hEll : IsEllipticFieldOn lam Lam (smallContrastUnitBall d) (scalarCoeffField a))
    (hclose : CoefficientIdentityDistanceLE (smallContrastUnitBall d) (scalarCoeffField a) delta)
    (hu : IsMatrixDivFormWeakSolutionOn (scalarCoeffField a) (smallContrastUnitBall d) u F)
    (hF : MemVectorLpOn (smallContrastUnitBall d) (schauderSourceExponent d (3 / 4 : ℝ)) F)
    (hLam : 0 ≤ Lam) (ha : ∀ x ∈ smallContrastUnitBall d, a x ≤ Lam) :
    ∀ z ∈ smallContrastBall d (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      ∫⁻ x in euclideanBall z r, ENNReal.ofReal (a x * vecDot (u.grad x) (u.grad x)) ≤
        ENNReal.ofReal (Lam * (volume (smallContrastUnitBall d)).toReal *
          (smallContrastGradientConstant d * smallContrastDataSize d (3 / 4 : ℝ) u F) ^ 2 *
          r ^ ((d : ℝ) - 1 / 2)) := by
  have hrow := interiorGradientScaleBound_of_smallContrast hd (by norm_num)
    hdelta0 hdelta hEll hclose hu hF
  have hK : 0 ≤ smallContrastGradientConstant d * smallContrastDataSize d (3 / 4 : ℝ) u F := by
    apply mul_nonneg (smallContrastGradientConstant_nonneg d)
    unfold smallContrastDataSize vectorLpSizeOn
    exact add_nonneg ENNReal.toReal_nonneg
      (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
  exact fun z hz r hr hrhalf => interior_energy_growth_of_gradient_row u a hK hLam ha
    hrow z hz r hr hrhalf

end SubdiffusiveProcess.Static
