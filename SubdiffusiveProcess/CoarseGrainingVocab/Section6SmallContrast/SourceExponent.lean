import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.Carrier

/-!
# Arithmetic of the source exponent

The energy test uses the embedding `L^p(B_1) ⊆ L²(B_r)`.  It is valid in
the manuscript's regime `d ≥ 2`; this file makes that otherwise implicit
dimension restriction and the identity `d / p = 1 - alpha` explicit.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

/-- The source exponent is positive. -/
theorem schauderSourceExponent_pos {d : ℕ} {alpha : ℝ}
    (hd : 1 ≤ d) (halpha : alpha < 1) :
    0 < schauderSourceExponent d alpha := by
  unfold schauderSourceExponent
  exact div_pos (by exact_mod_cast hd) (sub_pos.mpr halpha)

/-- In the intended PDE dimensions, the printed exponent is at least two, so
the `L^p` datum can be used in the quadratic energy test. -/
theorem two_le_schauderSourceExponent {d : ℕ} {alpha : ℝ}
    (hd : 2 ≤ d) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) :
    2 ≤ schauderSourceExponent d alpha := by
  unfold schauderSourceExponent
  have hden : 0 < 1 - alpha := sub_pos.mpr halpha1
  apply (le_div_iff₀ hden).2
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

/-- The scale exponent in the forcing row is exactly `1-alpha`. -/
theorem dimension_div_schauderSourceExponent {d : ℕ} {alpha : ℝ}
    (hd : 1 ≤ d) (halpha : alpha < 1) :
    (d : ℝ) / schauderSourceExponent d alpha = 1 - alpha := by
  unfold schauderSourceExponent
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have ha0 : 1 - alpha ≠ 0 := ne_of_gt (sub_pos.mpr halpha)
  field_simp

/-- The dyadic forcing coefficient printed after choosing `theta=1/2`. -/
theorem half_forcing_coefficient_rewrite {d : ℕ} {alpha : ℝ}
    (hd : 1 ≤ d) (halpha : alpha < 1) :
    2 * (1 / 2 : ℝ) ^
        ((d : ℝ) / schauderSourceExponent d alpha - (d : ℝ) / 2) =
      2 ^ (1 + (d : ℝ) / 2 - (d : ℝ) /
        schauderSourceExponent d alpha) := by
  rw [dimension_div_schauderSourceExponent hd halpha]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  calc
    2 * Real.exp (Real.log (1 / 2) * (1 - alpha - (d : ℝ) / 2)) =
        Real.exp (Real.log 2) *
          Real.exp (Real.log (1 / 2) * (1 - alpha - (d : ℝ) / 2)) := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ = Real.exp (Real.log 2 +
          Real.log (1 / 2) * (1 - alpha - (d : ℝ) / 2)) := by
            rw [Real.exp_add]
    _ = Real.exp (Real.log 2 * (1 + (d : ℝ) / 2 - (1 - alpha))) := by
            rw [hloghalf]
            congr 1
            ring

end


end SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
