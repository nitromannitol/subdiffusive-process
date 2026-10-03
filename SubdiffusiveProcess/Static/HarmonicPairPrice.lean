module

public import SubdiffusiveProcess.Static.HarmonicPairGeometry

@[expose] public section

/-! # The fixed pair gap exponent three -/
open MeasureTheory Homogenization Metric
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal Pointwise
noncomputable section
namespace SubdiffusiveProcess.Static

/-- Two chart/pasting powers and one finite-bank power fit exactly into the
pair gap exponent three. -/
theorem pair_gap_three_bound {h g D C : ℝ} (hh : 0 < h) (hg : 0 < g)
    (hC : 0 ≤ C) (hscale : h⁻¹ ≤ D / g) :
    C * h ^ (-(3 / 2 : ℝ)) * h ^ (-(1 / 2 : ℝ)) ≤
      D ^ 3 * (h * C) * g ^ (-3 : ℝ) := by
  have hcube := pow_le_pow_left₀ (inv_pos.mpr hh).le hscale 3
  rw [div_pow] at hcube
  have hsplit : h ^ (-(3 / 2 : ℝ)) * h ^ (-(1 / 2 : ℝ)) = (h ^ 2)⁻¹ := by
    rw [← Real.rpow_add hh, show -(3 / 2 : ℝ) + -(1 / 2 : ℝ) = -2 by ring,
      Real.rpow_neg hh.le, Real.rpow_two]
  rw [mul_assoc, hsplit, Real.rpow_neg hg.le,
    show g ^ (3 : ℝ) = g ^ (3 : ℕ) by norm_cast]
  calc
    C * (h ^ 2)⁻¹ = (h * C) * h⁻¹ ^ 3 := by field_simp
    _ ≤ (h * C) * (D ^ 3 / g ^ 3) :=
      mul_le_mul_of_nonneg_left hcube (mul_nonneg hh.le hC)
    _ = _ := by ring

end SubdiffusiveProcess.Static
