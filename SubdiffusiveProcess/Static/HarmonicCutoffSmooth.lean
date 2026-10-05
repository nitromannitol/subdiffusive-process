module

public import SubdiffusiveProcess.Static.HarmonicCutoffGrid
public import Homogenization.Sobolev.Foundations.QuantitativeCutoff

@[expose] public section

/-! # Quantitative smooth data for the harmonic cutoff cells -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Homogenization Metric
open scoped Topology

noncomputable section
namespace SubdiffusiveProcess.Static

/-- A dimension-only smooth cutoff datum with both derivative bounds. -/
theorem exists_smooth_cube_cutoff (d : ℕ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ a1 a2 : ℝ, 0 < a1 → a1 < a2 →
      ∃ f : (Fin d → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
        (∀ x, ‖x‖ ≤ a1 → f x = 1) ∧
        (∀ x, a2 ≤ ‖x‖ → f x = 0) ∧
        (∀ x, ‖fderiv ℝ f x‖ ≤ C0 / (a2 - a1)) ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C0 / (a2 - a1) ^ 2) := by
  let C0 := 1 + quantitativeCubeCutoffGradientConst d + quantitativeCubeCutoffHessianConst d
  have hG : 0 ≤ quantitativeCubeCutoffGradientConst d := by
    unfold quantitativeCubeCutoffGradientConst
    exact mul_nonneg (by positivity) smoothTransitionProfile.derivBound_nonneg
  have hH : 0 ≤ quantitativeCubeCutoffHessianConst d := by
    unfold quantitativeCubeCutoffHessianConst
    positivity
  have hC0 : 0 < C0 := by dsimp [C0]; linarith
  refine ⟨C0, hC0, ?_⟩
  intro a1 a2 ha1 ha12
  let Q := originCube d 0
  have h1 : 0 < 2 * a1 := by positivity
  have h12 : 2 * a1 < 2 * a2 := by linarith
  let cutoff := QuantitativeCubeCutoff.canonical Q (2 * a1) (2 * a2) h1 h12
  have hrad : cubeRadius Q = (1 / 2 : ℝ) := cubeRadius_eq_half_of_scale_eq_zero rfl
  have hcenter : cubeCenter Q = 0 := by
    funext i
    simp [Q, cubeCenter, originCube]
  have hgap : (2 * a2 - 2 * a1) * cubeRadius Q = a2 - a1 := by rw [hrad]; ring
  refine ⟨cutoff.toFun, cutoff.smooth, fun x => ⟨cutoff.nonneg x, cutoff.le_one x⟩,
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    apply cutoff.eq_one_on_inner
    intro i
    have hi := (pi_norm_le_iff_of_nonneg ha1.le).mp hx i
    have he : 2 * a1 * cubeRadius Q = a1 := by rw [hrad]; ring
    simpa only [hcenter, he, Pi.zero_apply, sub_zero, Real.norm_eq_abs] using hi
  · intro x hx
    by_contra hzero
    have hxs := cutoff.support_subset hzero
    have hsmall : ‖x‖ < a2 := by
      apply (pi_norm_lt_iff (ha1.trans ha12)).mpr
      intro i
      have hi := hxs i
      have he : 2 * a2 * cubeRadius Q = a2 := by rw [hrad]; ring
      simpa only [hcenter, he, Pi.zero_apply, sub_zero, Real.norm_eq_abs] using hi
    exact (not_lt_of_ge hx) hsmall
  · intro x
    refine (cutoff.gradient_bound x).trans ?_
    rw [hgap]
    apply div_le_div_of_nonneg_right _ (sub_pos.mpr ha12).le
    dsimp [C0]; linarith
  · intro x
    have hbase := cutoff.hessian_bound x
    rw [hgap] at hbase
    have heq : ‖fderiv ℝ (fderiv ℝ cutoff.toFun) x‖ =
        ‖iteratedFDeriv ℝ 2 cutoff.toFun x‖ := by
      calc
        _ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ cutoff.toFun) x‖ := by
          simpa only [fderivWithin_univ, iteratedFDerivWithin_univ] using
            (norm_iteratedFDerivWithin_one (𝕜 := ℝ) (fderiv ℝ cutoff.toFun)
              (uniqueDiffWithinAt_univ (x := x))).symm
        _ = _ := norm_iteratedFDeriv_fderiv
    rw [heq]
    refine hbase.trans ?_
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    dsimp [C0]; linarith

end SubdiffusiveProcess.Static
