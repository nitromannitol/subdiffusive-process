import SubdiffusiveProcess.Section6SumErrors.PaperStopping
/-!
# PaperConstant

One dimension-only constant simultaneously controls the smallness threshold, averaged Gaussian bound and stopping-depth exponential moment.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response
noncomputable section

/-- One dimension-only constant for every bound in the sum-of-errors lemma. -/
def paperConstant (d : ℕ) (D : ℝ) : ℝ :=
  1 + |D * (2 + 4 * (d : ℝ))| + 2 * windowCoeff d D + spatialBase d D + 4 * spatialBase d D ^ 2

theorem paperConstant_bounds (d : ℕ) (D : ℝ) :
    0 < paperConstant d D ∧ D * (2 + 4 * (d : ℝ)) ≤ paperConstant d D ∧
    2 * windowCoeff d D ≤ paperConstant d D ∧ spatialBase d D ≤ paperConstant d D ∧
    4 * spatialBase d D ^ 2 ≤ paperConstant d D := by
  have hK := windowCoeff_pos d D
  have hB := spatialBase_pos d D
  have hA := abs_nonneg (D * (2 + 4 * (d : ℝ)))
  have hle := le_abs_self (D * (2 + 4 * (d : ℝ)))
  have hsq := sq_nonneg (spatialBase d D)
  unfold paperConstant
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end
end SubdiffusiveProcess.Section6SumErrors.Response
