import SubdiffusiveProcess.LaplacianCorrector.Dilation
import SubdiffusiveProcess.MeyersRegularity.AffineLp
import Homogenization.Book.Ch01.Theorems.NormScaling

/-! Affine Sobolev pullback and transport of the scalar weak equation. -/

open MeasureTheory Filter Set Homogenization
open scoped ENNReal NNReal Topology Pointwise BigOperators

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

theorem cast_h1_toFun {d : ℕ} {U V : Set (Vec d)} (h : U = V) (u : H1Function U) :
    (h ▸ u).toFun = u.toFun := by cases h; rfl

theorem cast_h1_grad {d : ℕ} {U V : Set (Vec d)} (h : U = V) (u : H1Function U) :
    (h ▸ u).grad = u.grad := by cases h; rfl

theorem cast_h10_toFun {d : ℕ} {U V : Set (Vec d)} (h : U = V) (u : H10Function U) :
    (h ▸ u).toH1Function.toFun = u.toH1Function.toFun := by cases h; rfl

theorem cast_h10_grad {d : ℕ} {U V : Set (Vec d)} (h : U = V) (u : H10Function U) :
    (h ▸ u).toH1Function.grad = u.toH1Function.grad := by exact SubdiffusiveProcess.LaplacianCorrector.grad_cast_zeroTrace (d := d) (U := U) (V := V) (hUV := h) (u := u)

theorem scalarEquation_cast {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    (u : H1Function U) (a h : Vec d → ℝ) (heq : ScalarEquation a h u) :
    ScalarEquation a h (hUV ▸ u) := by cases hUV; exact heq

/-- Normalize by R so that the weak gradient has no additional scalar factor. -/
def affinePullback {d : ℕ} {R : ℝ} (hR : 0 < R) (z : Vec d) {U : Set (Vec d)}
    (u : H1Function (translateSet z (R • U))) : H1Function U :=
  (u.untranslate z).undilateSet hR rfl

theorem affinePullback_toFun {d : ℕ} {R : ℝ} (hR : 0 < R) (z : Vec d) {U : Set (Vec d)}
    (u : H1Function (translateSet z (R • U))) (x : Vec d) :
    (affinePullback hR z u).toFun x = R⁻¹*u.toFun (R • x+z) := by
  simp only [affinePullback, H1Function.undilateSet_toFun, H1Function.untranslate_toFun]

theorem affinePullback_grad {d : ℕ} {R : ℝ} (hR : 0 < R) (z : Vec d) {U : Set (Vec d)}
    (u : H1Function (translateSet z (R • U))) (x : Vec d) :
    (affinePullback hR z u).grad x = u.grad (R • x+z) := by
  simp only [affinePullback, H1Function.undilateSet_grad, H1Function.untranslate_grad]

/-- Push a unit-domain H10 test into the physical domain using the inverse unscale API. -/
def affineTest {d : ℕ} {R : ℝ} (hR : 0 < R) (z : Vec d) {U : Set (Vec d)}
    (phi : H10Function U) : H10Function (translateSet z (R • U)) := by
  have hU : U = R⁻¹ • (R • U) := by rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  let phiA : H10Function (R⁻¹ • (R • U)) := hU ▸ phi
  exact (phiA.unscale (inv_pos.mpr hR)).translate z

theorem affineTest_toFun {d : ℕ} {R : ℝ} (hR : 0 < R) (z : Vec d) {U : Set (Vec d)}
    (phi : H10Function U) (x : Vec d) :
    (affineTest hR z phi).toH1Function.toFun (R • x+z) = phi.toH1Function.toFun x := by
  simp only [affineTest, H10Function.translate_toH1Function, H1Function.translate_toFun,
    H10Function.unscale_toH1Function, H1Function.unscale_toFun, cast_h10_toFun,
    add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]

theorem affineTest_grad {d : ℕ} {R : ℝ} (hR : 0 < R) (z : Vec d) {U : Set (Vec d)}
    (phi : H10Function U) (x : Vec d) :
    (affineTest hR z phi).toH1Function.grad (R • x+z) = R⁻¹ • phi.toH1Function.grad x := by
  simp only [affineTest, H10Function.translate_toH1Function, H1Function.translate_grad,
    H10Function.unscale_toH1Function, H1Function.unscale_grad, cast_h10_grad,
    add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]

/-- Transport the original scalar weak equation with the exact normalization of its source. -/
theorem scalarEquation_affinePullback {d : ℕ} {R : ℝ} (hR : 0 < R) (z : Vec d)
    {U : Set (Vec d)} (u : H1Function (translateSet z (R • U))) (a h : Vec d → ℝ)
    (heq : ScalarEquation a h u) :
    ScalarEquation (fun x => a (R • x+z)) (fun x => R*h (R • x+z))
      (affinePullback hR z u) := by
  intro phi
  let w := affinePullback hR z u
  have hs := heq (affineTest hR z phi)
  rw [Book.Ch01.setIntegral_translateSet_smul_set_eq_comp_affine_of_pos hR,
    Book.Ch01.setIntegral_translateSet_smul_set_eq_comp_affine_of_pos hR] at hs
  simp only [smul_eq_mul] at hs
  simp_rw [affineTest_grad, affineTest_toFun] at hs
  have hleft : (fun x => a (R • x+z)*vecDot (u.grad (R • x+z)) (R⁻¹ • phi.toH1Function.grad x)) =
      (fun x => R⁻¹*(a (R • x+z)*vecDot (w.grad x) (phi.toH1Function.grad x))) := by
    funext x
    rw [vecDot_smul_right, ← affinePullback_grad hR z u]
    ring
  rw [hleft, integral_const_mul] at hs
  have hcan : R⁻¹*(∫ x in U, a (R • x+z)*vecDot (w.grad x) (phi.toH1Function.grad x)) =
      -(∫ x in U, h (R • x+z)*phi.toH1Function.toFun x) := by
    apply mul_left_cancel₀ (pow_ne_zero d hR.ne')
    simpa only [mul_neg] using hs
  have hunit := congrArg (fun t : ℝ => R*t) hcan
  simp only [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, mul_neg] at hunit
  change (∫ x in U, a (R • x+z)*vecDot (w.grad x) (phi.toH1Function.grad x)) =
    -(∫ x in U, (R*h (R • x+z))*phi.toH1Function.toFun x)
  simp only [mul_assoc]
  rw [integral_const_mul]
  exact hunit

end SubdiffusiveProcess.MeyersRegularity
