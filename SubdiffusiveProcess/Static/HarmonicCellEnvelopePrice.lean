import SubdiffusiveProcess.Static.HarmonicCellMomentCompensation
import SubdiffusiveProcess.Static.HarmonicCellAllRadius

/-! # Polynomial measurable envelope and compensated moment price -/
open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- The positive small-contrast threshold used for all microscopic radii. -/
def harmonicCellContrast (d : ℕ) : ℝ := smallContrastThreshold d (3 / 4 : ℝ)

theorem harmonicCellContrast_pos (d : ℕ) : 0 < harmonicCellContrast d := by
  unfold harmonicCellContrast smallContrastThreshold
  positivity

theorem harmonicCellContrast_le_one (d : ℕ) : harmonicCellContrast d ≤ 1 := by
  have h := smallContrastThreshold_lt_half d (alpha := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
  unfold harmonicCellContrast
  linarith

/-- The cutoff modulus fixes the microscopic transition through a linear price. -/
def harmonicCellTransition (d : ℕ) (D : ℝ) : ℝ := 2 / harmonicCellContrast d * (D + 1)

theorem harmonicCellTransition_ge_two (d : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    2 ≤ harmonicCellTransition d D := by
  have hp := harmonicCellContrast_pos d
  have hle := harmonicCellContrast_le_one d
  unfold harmonicCellTransition
  have hc : 2 ≤ 2 / harmonicCellContrast d := (le_div_iff₀ hp).mpr (by linarith)
  nlinarith

theorem harmonicCellTransition_small_modulus (d k : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    2 * ((3 : ℝ) ^ k * D) * (((3 : ℝ) ^ k)⁻¹ / harmonicCellTransition d D) ≤
      harmonicCellContrast d := by
  have hp := harmonicCellContrast_pos d
  have hD1 : 0 < D + 1 := by linarith
  have heq : 2 * ((3 : ℝ) ^ k * D) *
      (((3 : ℝ) ^ k)⁻¹ / harmonicCellTransition d D) =
      harmonicCellContrast d * D / (D + 1) := by
    unfold harmonicCellTransition
    field_simp [(pow_pos (by norm_num : (0 : ℝ) < 3) k).ne', hp.ne', hD1.ne']
    <;> ring
  rw [heq]
  apply (div_le_iff₀ hD1).mpr
  nlinarith only [hp.le]

/-- A sum of the coefficient, macro budget and linear derivative price has
only the same geometric cost as its three higher-moment inputs. -/
theorem harmonicCell_sum_envelope_norm_le {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (R G D : Omega → ℝ)
    (hRm : Measurable R) (hGm : Measurable G) (hDm : Measurable D)
    {q c A B C growth : ℝ} (hq : 1 ≤ q) (hc : 0 ≤ c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hg : 1 ≤ growth)
    (hRn : eLpNorm R (ENNReal.ofReal q) mu ≤ ENNReal.ofReal (A * growth))
    (hGn : eLpNorm G (ENNReal.ofReal q) mu ≤ ENNReal.ofReal B)
    (hDn : eLpNorm D (ENNReal.ofReal q) mu ≤ ENNReal.ofReal (C * growth)) :
    eLpNorm (fun omega => R omega + G omega + c * (D omega + 1))
      (ENNReal.ofReal q) mu ≤ ENNReal.ofReal ((A + B + c * (C + 1)) * growth) := by
  have hq0 := zero_lt_one.trans_le hq
  have h1 : eLpNorm (fun _ : Omega => (1 : ℝ)) (ENNReal.ofReal q) mu = 1 := by
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr hq0).ne' (NeZero.ne mu)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one, enorm_one]
  have hD1 := (eLpNorm_add_le hDm.aestronglyMeasurable aestronglyMeasurable_const
    (ENNReal.one_le_ofReal.mpr hq)).trans (add_le_add hDn (le_of_eq h1))
  have hT : eLpNorm (fun omega => c * (D omega + 1)) (ENNReal.ofReal q) mu ≤
      ENNReal.ofReal (c * (C * growth + 1)) := by
    calc
      _ = ENNReal.ofReal c * eLpNorm (fun omega => D omega + 1) (ENNReal.ofReal q) mu := by
        simpa only [Pi.smul_apply, smul_eq_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hc]
          using eLpNorm_const_smul c (fun omega => D omega + 1) (ENNReal.ofReal q) mu
      _ ≤ ENNReal.ofReal c * (ENNReal.ofReal (C * growth) + 1) :=
        mul_le_mul_right hD1 _
      _ = _ := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) (by norm_num),
          ← ENNReal.ofReal_mul hc]
  have hRG := (eLpNorm_add_le hRm.aestronglyMeasurable hGm.aestronglyMeasurable
    (ENNReal.one_le_ofReal.mpr hq)).trans (add_le_add hRn hGn)
  have hfull := (eLpNorm_add_le (hRm.add hGm).aestronglyMeasurable
    ((hDm.add measurable_const).const_mul c).aestronglyMeasurable
    (ENNReal.one_le_ofReal.mpr hq)).trans (add_le_add hRG hT)
  refine hfull.trans ?_
  rw [← ENNReal.ofReal_add (by positivity) hB,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith only [mul_le_mul_of_nonneg_left hg hB,
    mul_le_mul_of_nonneg_left hg hc]

end SubdiffusiveProcess.Static
