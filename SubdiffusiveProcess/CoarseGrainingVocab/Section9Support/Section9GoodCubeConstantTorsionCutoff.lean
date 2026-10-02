import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumSmoothSolution
import Homogenization.Sobolev.Foundations.QuantitativeCutoff
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.TestSubmodule
/-! A smooth plateau on the middle half with support strictly inside the cube. -/

set_option autoImplicit false
open Homogenization MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Construct the cutoff and retain its dimensional Hessian bound at every cube scale. -/
theorem goodCube_exists_middleHalfCutoff
    {d : ℕ} (Q : TriadicCube d) :
    ∃ eta : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) eta ∧ HasCompactSupport eta ∧
      tsupport eta ⊆ openCubeSet Q ∧
      (∀ x, 0 ≤ eta x ∧ eta x ≤ 1) ∧
      (∀ x ∈ scaledClosedCubeSet Q (1 / 2), eta x = 1) ∧
      ∀ x, ‖iteratedFDeriv ℝ 2 eta x‖ ≤
        64 * quantitativeCubeCutoffHessianConst d / (cubeScaleFactor Q) ^ 2 := by
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  have hrR : (1 / 2 : ℝ) < 3 / 4 := by norm_num
  let eta : QuantitativeCubeCutoff Q (1 / 2) (3 / 4) :=
    QuantitativeCubeCutoff.canonical Q (1 / 2) (3 / 4) hr hrR
  refine ⟨eta, eta.smooth, eta.hasCompactSupport, ?_,
    fun x => ⟨eta.nonneg x, eta.le_one x⟩,
    fun x hx => eta.eq_one_on_inner x hx, ?_⟩
  · change tsupport (QuantitativeCubeCutoff.canonicalFun Q (1 / 2) (3 / 4)) ⊆ openCubeSet Q
    exact (QuantitativeCubeCutoff.canonicalFun_tsupport_subset_scaledClosedCubeSet hr hrR).trans
      (Homogenization.scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q
        (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1))
  · intro x
    have hcr : 0 < cubeRadius Q := cubeRadius_pos Q
    have hS : cubeScaleFactor Q = 2 * cubeRadius Q :=
      cubeScaleFactor_eq_two_mul_cubeRadius Q
    have hSpos : 0 < cubeScaleFactor Q := by rw [hS]; linarith
    have hSne : cubeScaleFactor Q ≠ 0 := ne_of_gt hSpos
    have hden : ((3 / 4 - 1 / 2 : ℝ) * cubeRadius Q) ^ 2 =
        (cubeScaleFactor Q) ^ 2 / 64 := by
      rw [hS]; ring
    calc ‖iteratedFDeriv ℝ 2 eta x‖
        ≤ quantitativeCubeCutoffHessianConst d /
            (((3 / 4 - 1 / 2 : ℝ) * cubeRadius Q) ^ 2) := eta.hessian_bound x
      _ = quantitativeCubeCutoffHessianConst d /
            ((cubeScaleFactor Q) ^ 2 / 64) := by rw [hden]
      _ = 64 * quantitativeCubeCutoffHessianConst d / (cubeScaleFactor Q) ^ 2 := by
          field_simp

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
