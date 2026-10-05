module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumSmoothSolution
public import Homogenization.Sobolev.Foundations.QuantitativeCutoff
@[expose] public section

/-! A dimension-dependent Laplacian bound in terms of the classical Hessian. -/

set_option autoImplicit false
open Homogenization MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

private theorem euclideanCoordLaplacian_le_hessian'
    {d : ℕ} {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (x : Vec d) {B : ℝ} (hB : ‖iteratedFDeriv ℝ 2 η x‖ ≤ B) :
    |euclideanCoordLaplacian η x| ≤ (d : ℝ) * B := by
  have hcoord : ∀ i : Fin d, |euclideanCoordSecondDeriv i i η x| ≤ B := by
    intro i
    calc
      |euclideanCoordSecondDeriv i i η x| =
          ‖fderiv ℝ (fderiv ℝ η) x (basisVec i) (basisVec i)‖ := by
            rw [euclideanCoordSecondDeriv_eq_fderiv_fderiv hη]
            simp [Real.norm_eq_abs]
      _ = ‖iteratedFDeriv ℝ 2 η x ![basisVec i, basisVec i]‖ := by
            simp [iteratedFDeriv_two_apply]
      _ ≤ ‖iteratedFDeriv ℝ 2 η x‖ * ∏ j, ‖![basisVec i, basisVec i] j‖ := by
            simpa using ContinuousMultilinearMap.le_opNorm
              (iteratedFDeriv ℝ 2 η x) ![basisVec i, basisVec i]
      _ = ‖iteratedFDeriv ℝ 2 η x‖ := by simp
      _ ≤ B := hB
  calc
    |euclideanCoordLaplacian η x| =
        |∑ i : Fin d, euclideanCoordSecondDeriv i i η x| := rfl
    _ ≤ ∑ i : Fin d, |euclideanCoordSecondDeriv i i η x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, B := Finset.sum_le_sum fun i _ => hcoord i
    _ = (d : ℝ) * B := by simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The scalar Laplacian is bounded by dimension times the Hessian operator norm. -/
theorem goodCube_abs_coeffFluxDiv_one_le_hessian
    {d : ℕ} {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (x : Vec d) :
    |coeffFluxDiv (fun _ => 1) eta x| ≤
      (d : ℝ) * ‖iteratedFDeriv ℝ 2 eta x‖ := by
  have hEq : coeffFluxDiv (fun _ => 1) eta x = euclideanCoordLaplacian eta x := by
    simp only [coeffFluxDiv, one_mul]
    rfl
  rw [hEq]
  exact euclideanCoordLaplacian_le_hessian' heta x le_rfl

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
