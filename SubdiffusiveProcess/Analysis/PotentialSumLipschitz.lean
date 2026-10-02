import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.LongRatio
import Mathlib.Analysis.Calculus.MeanValue

/-! Finite potential sums obey a mean-value bound from their summed shell gradients.
No infinite-series convergence or stochastic estimate is asserted. -/

open Set SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess

/-- A finite sum of smooth potentials has the Lipschitz bound supplied by its gradient sum. -/
theorem potentialSample_sum_increment_le {d : ℕ}
    (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (J : ℕ) (X Y : Vec d) (G : ℝ)
    (hgrad : ∀ Z ∈ segment ℝ X Y,
      ∑ i ∈ Finset.range J, euclideanNorm (shellGradient (eta i) Z) ≤ G) :
    |∑ i ∈ Finset.range J, (eta i Y - eta i X)| ≤ (d : ℝ) * G * ‖Y - X‖ := by
  let S : Vec d → ℝ := fun Z => ∑ i ∈ Finset.range J, eta i Z
  let D : Vec d → (Vec d →L[ℝ] ℝ) := fun Z =>
    ∑ i ∈ Finset.range J, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (eta i) Z
  have hder : ∀ Z, HasFDerivAt S (D Z) Z := by
    intro Z
    have h := HasFDerivAt.sum (u := Finset.range J) (fun i _ => (eta i).hasFDerivAt Z)
    convert h using 1
    funext Z'
    simp only [S, Finset.sum_apply]
  have hbd : ∀ Z ∈ segment ℝ X Y, ‖fderiv ℝ S Z‖ ≤ (d : ℝ) * G := by
    intro Z hZ
    rw [(hder Z).fderiv]
    calc ‖D Z‖ ≤ ∑ i ∈ Finset.range J,
          ‖SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (eta i) Z‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range J, (d : ℝ) * euclideanNorm (shellGradient (eta i) Z) :=
        Finset.sum_le_sum fun i _ =>
          Section6Localization.potentialDeriv_norm_le_dimension_mul_shellGradient (eta i) Z
      _ = (d : ℝ) * ∑ i ∈ Finset.range J, euclideanNorm (shellGradient (eta i) Z) := by
        rw [Finset.mul_sum]
      _ ≤ (d : ℝ) * G := mul_le_mul_of_nonneg_left (hgrad Z hZ) (Nat.cast_nonneg d)
  have h := (convex_segment X Y).norm_image_sub_le_of_norm_fderiv_le
    (fun Z _ => (hder Z).differentiableAt) hbd (left_mem_segment ℝ X Y)
    (right_mem_segment ℝ X Y)
  simpa only [Real.norm_eq_abs, S, Finset.sum_sub_distrib] using h

end SubdiffusiveProcess
