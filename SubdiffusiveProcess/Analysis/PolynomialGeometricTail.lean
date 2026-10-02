import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Polynomial factors preserve strictly geometric decay. These scalar
estimates make no probabilistic or model-specific assertion.
-/
open scoped BigOperators
namespace SubdiffusiveProcess

/-- A shifted polynomial times a positive contracting geometric sequence is summable. -/
theorem summable_shifted_pow_mul_geometric (b : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ b * r ^ n) := by
  have hb : Summable (fun n : ℕ => (n : ℝ) ^ b * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one b
      (by simpa only [Real.norm_eq_abs, abs_of_pos hr0] using hr1)
  have hshift := (hb.comp_injective Nat.succ_injective).mul_left r⁻¹
  refine hshift.congr (fun n => ?_)
  simp only [Function.comp_apply, Nat.cast_succ, pow_succ]
  field_simp [hr0.ne']

/-- A shifted polynomial times a decaying real power of three is summable. -/
theorem summable_shifted_pow_mul_triadic (b : ℕ) {a : ℝ} (ha : a < 0) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ b * (3 : ℝ) ^ (a * n)) := by
  have hr0 : 0 < (3 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : (3 : ℝ) ^ a < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ha
  simpa only [Real.rpow_mul_natCast (show (0 : ℝ) ≤ 3 by norm_num)] using
    summable_shifted_pow_mul_geometric b hr0 hr1

/-- A polynomial cost is absorbed by half of a positive triadic decay rate. -/
theorem exists_polynomial_triadic_half_decay_bound (b : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ((n : ℝ) + 1) ^ b * (3 : ℝ) ^ (-a * n) ≤
        C * (3 : ℝ) ^ (-(a / 2) * n) := by
  let f : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ b * (3 : ℝ) ^ (-(a / 2) * n)
  have hf0 n : 0 ≤ f n := mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)
  have hfs : Summable f := summable_shifted_pow_mul_triadic b (by linarith only [ha])
  have hsum0 : 0 ≤ ∑' n, f n := tsum_nonneg hf0
  refine ⟨1 + ∑' n, f n, by linarith only [hsum0], ?_⟩
  intro n
  have hn : f n ≤ 1 + ∑' j, f j := by
    have hterm := hfs.le_tsum n (fun j _ => hf0 j)
    linarith only [hterm]
  have hmul := mul_le_mul_of_nonneg_right hn
    (Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) (-(a / 2) * n))
  convert hmul using 1
  dsimp only [f]
  rw [mul_assoc, ← Real.rpow_add (show (0 : ℝ) < 3 by norm_num)]
  congr 2
  ring

end SubdiffusiveProcess
