module

public import SubdiffusiveProcess.Static.CutoffUnitCoercivity
public import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
public import Homogenization.Sobolev.H1.Translation
public import Homogenization.Geometry.CubeMetric
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

@[expose] public section

/-! # Native Sobolev charts for arbitrary real cubes -/

open MeasureTheory Homogenization
open scoped ENNReal Pointwise

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The unit triadic cube is the open sup-norm ball of radius `1/2`. -/
theorem unitCube_eq_ball (d : ℕ) :
    openCubeSet (originCube d 0) = Metric.ball (0 : Vec d) (1 / 2) := by
  have hcenter : Homogenization.cubeCenter (originCube d 0) = 0 := by
    funext i
    simp [Homogenization.cubeCenter, Homogenization.cubeScaleFactor, originCube]
  have h := (ball_cubeCenter_eq_openCubeSet (originCube d 0)).symm
  rw [hcenter] at h
  simpa [Homogenization.cubeRadius, Homogenization.cubeScaleFactor, originCube] using h

/-- The chart has precisely the requested real centre and side. -/
theorem translate_smul_unitCube {d : ℕ} (y : Vec d) {t : ℝ} (ht : 0 < t) :
    translateSet y (t • openCubeSet (originCube d 0)) = Metric.ball y (t / 2) := by
  rw [unitCube_eq_ball, smul_ball ht.ne']
  simp only [smul_zero, Real.norm_eq_abs, abs_of_pos ht]
  ext x
  rw [mem_translateSet_iff_sub_mem]
  simp only [Metric.mem_ball, dist_zero_right, dist_eq_norm]
  congr 1
  ring

private def castH1 {d : ℕ} {U V : Set (Vec d)} (h : U = V) (H : H1Function U) :
    H1Function V := h ▸ H

@[simp] private theorem castH1_toFun {d : ℕ} {U V : Set (Vec d)} (h : U = V)
    (H : H1Function U) : (castH1 h H).toFun = H.toFun := by subst V; rfl

@[simp] private theorem castH1_grad {d : ℕ} {U V : Set (Vec d)} (h : U = V)
    (H : H1Function U) : (castH1 h H).grad = H.grad := by subst V; rfl

private def castH10 {d : ℕ} {U V : Set (Vec d)} (h : U = V) (H : H10Function U) :
    H10Function V := h ▸ H

@[simp] private theorem castH10_toFun {d : ℕ} {U V : Set (Vec d)} (h : U = V)
    (H : H10Function U) : (castH10 h H).toFun = H.toFun := by subst V; rfl

@[simp] private theorem castH10_grad {d : ℕ} {U V : Set (Vec d)} (h : U = V)
    (H : H10Function U) : (castH10 h H).grad = H.grad := by subst V; rfl

/-- Normalized affine pullback: the gradient is the unscaled physical
weak gradient, and the function is divided by the chart side. -/
theorem exists_H1_affine_chart {d : ℕ} (y : Vec d) {t : ℝ} (ht : 0 < t)
    (H : H1Function (Metric.ball y (t / 2))) :
    ∃ W : H1Function (openCubeSet (originCube d 0)),
      W.toFun = (fun x => t⁻¹ * H.toFun (y + t • x)) ∧
      W.grad = (fun x => H.grad (y + t • x)) := by
  let H0 := castH1 (translate_smul_unitCube y ht).symm H
  let H1 := H1Function.untranslate y H0
  let W := H1.undilateSet ht rfl
  refine ⟨W, ?_, ?_⟩
  · funext x
    simp only [W, H1Function.undilateSet_toFun, H1, H1Function.untranslate_toFun, H0,
      castH1_toFun, add_comm]
  · funext x
    simp only [W, H1Function.undilateSet_grad, H1, H1Function.untranslate_grad, H0,
      castH1_grad, add_comm]

/-- The same chart preserves trace-zero membership. -/
theorem exists_H10_affine_chart {d : ℕ} (y : Vec d) {t : ℝ} (ht : 0 < t)
    (H : H10Function (Metric.ball y (t / 2))) :
    ∃ W : H10Function (openCubeSet (originCube d 0)),
      W.toFun = (fun x => t⁻¹ * H.toFun (y + t • x)) ∧
      W.grad = (fun x => H.grad (y + t • x)) := by
  let H0 := castH10 (translate_smul_unitCube y ht).symm H
  let H1 := H10Function.untranslate y H0
  let W : H10Function (openCubeSet (originCube d 0)) := t⁻¹ • H1.unscale ht
  refine ⟨W, ?_, ?_⟩
  · funext x
    change t⁻¹ * (H1.unscale ht).toH1Function.toFun x = _
    rw [H10Function.unscale_toH1Function, H1Function.unscale_toFun]
    simp only [H1, H10Function.untranslate_toH1Function, H1Function.untranslate_toFun,
      H0, castH10_toFun, add_comm]
  · funext x
    change t⁻¹ • (H1.unscale ht).toH1Function.grad x = _
    rw [H10Function.unscale_toH1Function, H1Function.unscale_grad]
    simp only [H1, H10Function.untranslate_toH1Function, H1Function.untranslate_grad]
    change t⁻¹ • (t • (castH10 (translate_smul_unitCube y ht).symm H).grad (t • x + y)) = _
    rw [castH10_grad, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_comm]

end SubdiffusiveProcess.Static
