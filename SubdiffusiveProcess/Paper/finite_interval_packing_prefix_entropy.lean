import SubdiffusiveProcess.Lane3.Subdivision
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

namespace Paper



theorem finite_interval_packing_prefix_entropy
    (d H1 J : ℕ) (hd : 2 ≤ d) :
    (Fintype.card
        (Fin J → OddGridIndex d (subdivisionHalfWidth H1)) : ℝ) ≤
      Real.exp ((d : ℝ) * (H1 : ℝ) * (J : ℝ) * Real.log 3) := by
  have hcard :
      Fintype.card (Fin J → OddGridIndex d (subdivisionHalfWidth H1)) =
        3 ^ (H1 * d * J) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    rw [SubdiffusiveProcess.Lane3.two_mul_subdivisionHalfWidth_add_one]
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hcard]
  have hpos : (0 : ℝ) < 3 ^ (H1 * d * J) := by positivity
  calc
    ((3 ^ (H1 * d * J) : ℕ) : ℝ) =
        Real.exp (Real.log ((3 : ℝ) ^ (H1 * d * J))) := by
          rw [Real.exp_log hpos]
          norm_cast
    _ = Real.exp ((H1 * d * J : ℕ) * Real.log 3) := by
          rw [Real.log_pow]
    _ = Real.exp ((d : ℝ) * (H1 : ℝ) * (J : ℝ) * Real.log 3) := by
          congr 1
          push_cast
          ring
    _ ≤ Real.exp ((d : ℝ) * (H1 : ℝ) * (J : ℝ) * Real.log 3) := le_rfl

end Paper
