module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.BelowCutoffInputs

@[expose] public section

/-!
# Quarter-scale conversion of the four v4 budgets

The existing boundary Hölder recurrence is written with the retired v3
powers.  The excess theorem now has the v4 powers.  At the only scale used by
the recurrence, `s = 1/4`, doubling its constant absorbs all four changes.

Argument: `l.excess.decay.good.scales.GMC`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

/-- The v4 contraction/error coefficient at `s = 1/4` is bounded by the v3
coefficient with twice the constant. -/
theorem belowCutoff_quarter_contractionBudget_v4_le_doubled_v3
    {C base amp epsilon E : ℝ}
    (hC : 0 ≤ C) (hbase : 0 ≤ base) (hE : 0 ≤ E) :
    C * (base + amp * (1 / 4 : ℝ) ^ (-2 : ℝ) * epsilon) * E ≤
      (2 * C) *
        (base + amp * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * epsilon) * E := by
  norm_num
  have h : C * base ≤ 2 * C * base := by nlinarith
  nlinarith

/-- The slope/mean homogenization-error budget is exactly preserved after
doubling the constant. -/
theorem belowCutoff_quarter_errorBudget_v4_eq_doubled_v3
    {C amp Err slopeMean : ℝ} :
    C * amp * (1 / 4 : ℝ) ^ (-2 : ℝ) * Err * slopeMean =
      (2 * C) * amp * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * Err * slopeMean := by
  have hp2 : (1 / 4 : ℝ) ^ (-2 : ℝ) = 16 := by norm_num
  have hp32 : (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) = 8 := by norm_num
  rw [hp2, hp32]
  ring

/-- The forcing budget is exactly preserved after doubling the constant. -/
theorem belowCutoff_quarter_forcingBudget_v4_eq_doubled_v3
    {C amp forcing : ℝ} :
    C * (1 / 4 : ℝ) ^ (-8 : ℝ) * amp * forcing =
      (2 * C) * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) * amp * forcing := by
  have hp8 : (1 / 4 : ℝ) ^ (-8 : ℝ) = 65536 := by norm_num
  have hp15 : (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) = 32768 := by norm_num
  rw [hp8, hp15]
  ring

/-- The boundary Hölder budget is exactly preserved after doubling the
constant. -/
theorem belowCutoff_quarter_boundaryBudget_v4_eq_doubled_v3
    {C amp boundary : ℝ} :
    C * (1 / 4 : ℝ) ^ (-7 / 2 : ℝ) * amp * boundary =
      (2 * C) * (1 / 4 : ℝ) ^ (-3 : ℤ) * amp * boundary := by
  have hp7 : (1 / 4 : ℝ) ^ (-7 / 2 : ℝ) = 128 := by norm_num
  have hp3 : (1 / 4 : ℝ) ^ (-3 : ℤ) = 64 := by norm_num
  rw [hp7, hp3]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
