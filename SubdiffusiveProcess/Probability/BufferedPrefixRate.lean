import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! A larger exponential tail rate absorbs a fixed prefix buffer and a factor
of two. This scalar inequality does not assert any probabilistic estimate.
-/
namespace SubdiffusiveProcess

/-- The larger rate pays both the factor two and a fixed prefix buffer. -/
theorem buffered_prefix_tail_le
    (A : ℝ) (hA : 0 < A) (buffer D : ℕ) (hD : 1 ≤ D) :
    2 * Real.exp (-((A * ((buffer : ℝ) + 1) + Real.log 2) * (D : ℝ))) ≤
      Real.exp (-(A * ((D : ℝ) + buffer))) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hbuf := mul_nonneg (Nat.cast_nonneg (α := ℝ) buffer)
    (sub_nonneg.mpr hD')
  have hlogD := mul_nonneg hlog (sub_nonneg.mpr hD')
  have hAbuf := mul_nonneg hA.le hbuf
  rw [show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)],
    ← Real.exp_add, Real.log_exp]
  apply Real.exp_le_exp.mpr
  nlinarith only [hAbuf, hlogD]

end SubdiffusiveProcess
