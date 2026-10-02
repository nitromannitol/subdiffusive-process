import SubdiffusiveProcess.Lane4.Bridge
import Mathlib.Tactic

/-! Logarithmic increments of a cutoff coefficient equal potential increments.
This identity supplies no bound on either increment. -/

open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess.Lane4

/-- The normalization cancels when taking a logarithmic coefficient increment. -/
theorem log_cutoffCoefficient_sub {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (x y : SpatialCoordinates d) :
    Real.log (cutoffCoefficient M H omega N x) - Real.log (cutoffCoefficient M H omega N y) =
      cutoffPotential H omega N x - cutoffPotential H omega N y := by
  unfold cutoffCoefficient
  rw [Real.log_mul (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne')
      (Real.exp_ne_zero _),
    Real.log_mul (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne')
      (Real.exp_ne_zero _), Real.log_exp, Real.log_exp]
  ring

end SubdiffusiveProcess.Lane4
