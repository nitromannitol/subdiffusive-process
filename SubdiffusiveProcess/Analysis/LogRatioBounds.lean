module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! A bound on the logarithmic difference of positive numbers gives both
directions of their ratio estimate. No coefficient or probability is involved.
-/
namespace SubdiffusiveProcess

/-- Absolute logarithmic control gives a two-sided exponential ratio bound. -/
theorem exp_ratio_of_log_sub {a b K : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : |Real.log a - Real.log b| ≤ K) :
    Real.exp (-K) ≤ a / b ∧ a / b ≤ Real.exp K := by
  have hab : 0 < a / b := div_pos ha hb
  have hid : Real.log a - Real.log b = Real.log (a / b) :=
    (Real.log_div ha.ne' hb.ne').symm
  rw [hid] at h
  have hh := abs_le.mp h
  constructor
  · exact (Real.exp_le_exp.mpr hh.1).trans_eq (Real.exp_log hab)
  · exact (Real.exp_log hab).symm.trans_le (Real.exp_le_exp.mpr hh.2)

end SubdiffusiveProcess
