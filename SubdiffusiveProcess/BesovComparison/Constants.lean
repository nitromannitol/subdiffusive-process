import SubdiffusiveProcess.BesovComparison.MetricBounds
import SubdiffusiveProcess.BesovComparison.ScalarBounds

/-! A finite common comparison constant depending only on the dimension. -/
open Homogenization
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.BesovComparison

def comparisonConstant (d : ℕ) : ℝ :=
  (2 * 3 ^ d) * (2 ^ 3 * 3 ^ (3*d+2)) * ((d : ℝ)+1) ^ (d+1)

theorem one_le_comparisonConstant (d : ℕ) : 1 ≤ comparisonConstant d := by
  unfold comparisonConstant
  apply one_le_mul_of_one_le_of_one_le
  · apply one_le_mul_of_one_le_of_one_le
    · exact one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by norm_num))
    · exact one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by norm_num))
  · exact one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg d))

theorem ofReal_comparisonConstant (d : ℕ) :
    ENNReal.ofReal (comparisonConstant d) =
      upperConstant d * Gagliardo.gagliardoBesovLowerConstant d * metricConstant d := by
  unfold comparisonConstant upperConstant Gagliardo.gagliardoBesovLowerConstant metricConstant
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity)]
  simp [ENNReal.ofReal_add (Nat.cast_nonneg d) zero_le_one]

theorem lowerConstant_le_comparisonConstant (d : ℕ) :
    Gagliardo.gagliardoBesovLowerConstant d ≤ ENNReal.ofReal (comparisonConstant d) := by
  rw [ofReal_comparisonConstant]
  calc
    _ = 1 * Gagliardo.gagliardoBesovLowerConstant d * 1 := by simp
    _ ≤ _ := mul_le_mul' (mul_le_mul' (one_le_upperConstant d) le_rfl) (one_le_metricConstant d)

theorem upper_metric_le_comparisonConstant (d : ℕ) :
    upperConstant d * metricConstant d ≤ ENNReal.ofReal (comparisonConstant d) := by
  rw [ofReal_comparisonConstant]
  calc
    _ = upperConstant d * 1 * metricConstant d := by simp
    _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl (one_le_lowerConstant d)) le_rfl

end SubdiffusiveProcess.BesovComparison
