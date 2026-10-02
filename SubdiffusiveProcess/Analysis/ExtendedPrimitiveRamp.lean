import SubdiffusiveProcess.Main.PrimitiveScores
import SubdiffusiveProcess.Analysis.RelativeScoreComparison

/-! Monotonicity and finite-argument relative comparison for the extended
primitive ramp. Infinity is retained in the monotonicity statement; passage
to the real ramp is asserted only for finite arguments.
-/
open scoped ENNReal
namespace SubdiffusiveProcess

/-- The extended primitive ramp is monotone, including at infinity. -/
theorem extendedPrimitiveRamp_mono (lo hi : ℝ) {X Y : ℝ≥0∞} (hXY : X ≤ Y) :
    extendedPrimitiveRamp lo hi X ≤ extendedPrimitiveRamp lo hi Y := by
  unfold extendedPrimitiveRamp
  apply ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _))
  gcongr

/-- At finite arguments the extended ramp equals the ordinary real bounded ramp. -/
theorem extendedPrimitiveRamp_eq_ramp (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo < hi)
    (X : ℝ≥0∞) (hX : X ≠ ⊤) :
    extendedPrimitiveRamp lo hi X = Lane3.ramp lo hi X.toReal := by
  unfold extendedPrimitiveRamp
  conv_lhs => rw [← ENNReal.ofReal_toReal hX]
  rw [← ENNReal.ofReal_sub _ hlo, ← ENNReal.ofReal_div_of_pos (sub_pos.mpr hlohi),
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_mono.map_min, ENNReal.toReal_ofReal']
  simp only [Lane3.ramp, min_max_distrib_left,
    min_eq_right (show (0 : ℝ) ≤ 1 by norm_num), max_comm]

/-- A finite one-sided relative error gives an absolute extended-ramp error. -/
theorem extendedPrimitiveRamp_le_of_relative_le (lo hi : ℝ)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (X Y : ℝ≥0∞) (hX : X ≠ ⊤) (hY : Y ≠ ⊤)
    (eta : ℝ) (heta : 0 ≤ eta) (hXY : X.toReal ≤ (1 + eta) * Y.toReal + eta) :
    extendedPrimitiveRamp lo hi X ≤ extendedPrimitiveRamp lo hi Y +
      eta * (1 + hi) / (hi - lo) := by
  rw [extendedPrimitiveRamp_eq_ramp lo hi hlo hlohi X hX,
    extendedPrimitiveRamp_eq_ramp lo hi hlo hlohi Y hY]
  exact ramp_le_of_relative_le hlo hlohi heta hXY

end SubdiffusiveProcess
