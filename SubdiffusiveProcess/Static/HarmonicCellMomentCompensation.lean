module

public import SubdiffusiveProcess.Static.HarmonicCellCoefficientBounds
public import SubdiffusiveProcess.Analysis.RawLp

@[expose] public section

/-! # Quarter-power radius compensation for polynomial microscopic prices -/
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- A nonnegative polynomial price transfers the higher moment to its natural power. -/
theorem eLpNorm_nonneg_nat_power {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (U : Omega → ℝ) (hU : ∀ omega, 0 ≤ U omega)
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (hn : 0 < n) :
    SubdiffusiveProcess.RawLp.eLpNorm (fun omega => U omega ^ n) (ENNReal.ofReal q) mu =
      SubdiffusiveProcess.RawLp.eLpNorm U (ENNReal.ofReal (q * (n : ℝ))) mu ^ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hq0 : q = 0
  · subst q
    simp [SubdiffusiveProcess.RawLp.eLpNorm, hn.ne']
  have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have hprod : 0 < q * (n : ℝ) := mul_pos hqpos hnR
  simp only [SubdiffusiveProcess.RawLp.eLpNorm, ENNReal.ofReal_eq_zero, not_le.mpr hqpos,
    not_le.mpr hprod, ENNReal.ofReal_ne_top, ↓reduceIte, ENNReal.toReal_ofReal hq,
    ENNReal.toReal_ofReal hprod.le]
  have h := eLpNorm'_norm_rpow (μ := mu) U q (n : ℝ) hnR
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hU _), Real.rpow_natCast,
    ENNReal.rpow_natCast] using! h

/-- The quarter-power scale gain absorbs any sufficiently small geometric
moment growth of a polynomial envelope. -/
theorem harmonicCell_compensated_power_norm_le {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (U : Omega → ℝ) (hU : ∀ omega, 0 ≤ U omega)
    (q : ℝ) (hq : 0 ≤ q) (n k : ℕ) (hn : 0 < n)
    {C eta : ℝ} (hC : 0 ≤ C) (hcost : eta * (n : ℝ) ≤ 1 / 4)
    (hNorm : SubdiffusiveProcess.RawLp.eLpNorm U (ENNReal.ofReal (q * (n : ℝ))) mu ≤
      ENNReal.ofReal (C * (3 : ℝ) ^ (eta * (k : ℝ)))) :
    SubdiffusiveProcess.RawLp.eLpNorm (fun omega => (((3 : ℝ) ^ k)⁻¹) ^ (1 / 4 : ℝ) * U omega ^ n)
      (ENNReal.ofReal q) mu ≤ ENNReal.ofReal (C ^ n) := by
  have hscale : 0 ≤ (((3 : ℝ) ^ k)⁻¹) ^ (1 / 4 : ℝ) := by positivity
  calc
    _ = ENNReal.ofReal ((((3 : ℝ) ^ k)⁻¹) ^ (1 / 4 : ℝ)) *
        SubdiffusiveProcess.RawLp.eLpNorm (fun omega => U omega ^ n) (ENNReal.ofReal q) mu := by
      by_cases hq0 : q = 0
      · subst q
        simp [SubdiffusiveProcess.RawLp.eLpNorm]
      have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
      simp only [SubdiffusiveProcess.RawLp.eLpNorm, ENNReal.ofReal_eq_zero, not_le.mpr hqpos,
        ENNReal.ofReal_ne_top, ↓reduceIte, ENNReal.toReal_ofReal hq]
      simpa only [Pi.smul_apply, smul_eq_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hscale]
        using! eLpNorm'_const_smul (μ := mu) (f := fun omega => U omega ^ n)
          ((((3 : ℝ) ^ k)⁻¹) ^ (1 / 4 : ℝ)) hqpos
    _ ≤ ENNReal.ofReal ((((3 : ℝ) ^ k)⁻¹) ^ (1 / 4 : ℝ)) *
        (ENNReal.ofReal (C * (3 : ℝ) ^ (eta * (k : ℝ)))) ^ n := by
      rw [eLpNorm_nonneg_nat_power mu U hU q hq n hn]
      gcongr
    _ = ENNReal.ofReal (C ^ n * (3 : ℝ) ^
        ((eta * (n : ℝ) - 1 / 4) * (k : ℝ))) := by
      rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hscale, mul_pow]
      apply congrArg ENNReal.ofReal
      have heq : (((3 : ℝ) ^ k)⁻¹) ^ (1 / 4 : ℝ) *
          ((3 : ℝ) ^ (eta * (k : ℝ))) ^ n =
          (3 : ℝ) ^ ((eta * (n : ℝ) - 1 / 4) * (k : ℝ)) := by
        rw [← Real.rpow_natCast 3 k, ← Real.rpow_neg (by norm_num),
          ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1
        ring
      calc
        _ = C ^ n * ((((3 : ℝ) ^ k)⁻¹) ^ (1 / 4 : ℝ) *
            ((3 : ℝ) ^ (eta * (k : ℝ))) ^ n) := by ring
        _ = _ := by rw [heq]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hg : (3 : ℝ) ^ ((eta * (n : ℝ) - 1 / 4) * (k : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg _))
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hg (pow_nonneg hC _))

/-- A product with total integer degree n is bounded by the sum envelope's n-th power. -/
theorem harmonicCell_polynomial_le_sum_power (d : ℕ) {R G T : ℝ}
    (hR : 0 ≤ R) (hG : 0 ≤ G) (hT : 0 ≤ T) :
    R ^ 5 * G * T ^ d ≤ (R + G + T) ^ (d + 6) := by
  have hU : 0 ≤ R + G + T := by positivity
  calc
    _ ≤ (R + G + T) ^ 5 * (R + G + T) * (R + G + T) ^ d := by
      gcongr <;> linarith
    _ = _ := by rw [← pow_succ, ← pow_add]; congr 1; omega

end SubdiffusiveProcess.Static
