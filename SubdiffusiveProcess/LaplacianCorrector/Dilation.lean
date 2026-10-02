import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCorrectorEnergyBridge
import Homogenization.Book.Ch02.Dilation
import Homogenization.Sobolev.Foundations.CoerciveH1Dilation

/-! # Dilation and uniqueness of identity-coefficient corrector energies -/

open MeasureTheory Homogenization
open scoped ENNReal Pointwise

noncomputable section
namespace SubdiffusiveProcess.LaplacianCorrector

theorem smul_zeroTrace_toH1 {d : ℕ} {U : Set (Vec d)} (a : ℝ) (u : H10Function U) :
    (a • u).toH1Function = a • u.toH1Function := rfl

theorem grad_cast_zeroTrace {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    (u : H10Function U) :
    (hUV ▸ u).toH1Function.grad = u.toH1Function.grad := by
  subst V
  rfl

theorem grad_cast_meanZero {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    (u : H1MeanZeroFunction U) :
    (hUV ▸ u).toH1Function.grad = u.toH1Function.grad := by
  subst V
  rfl

/-- Normalized dilation of a zero-trace function; its gradient is a plain pullback. -/
def dilateZeroTrace {d : ℕ} {U V : Set (Vec d)} {a : ℝ}
    (ha : 0 < a) (hV : V = a • U) (u : H10Function U) : H10Function V := by
  have hU : U = a⁻¹ • V := by
    rw [hV, inv_smul_smul₀ ha.ne']
  exact a • (H10Function.unscale (inv_pos.mpr ha) (hU ▸ u))

@[simp] theorem dilateZeroTrace_grad {d : ℕ} {U V : Set (Vec d)} {a : ℝ}
    (ha : 0 < a) (hV : V = a • U) (u : H10Function U) (x : Vec d) :
    (dilateZeroTrace ha hV u).toH1Function.grad x = u.toH1Function.grad (a⁻¹ • x) := by
  subst V
  simp only [dilateZeroTrace, smul_zeroTrace_toH1, H1Function.smul_grad,
    H10Function.unscale_toH1Function, H1Function.unscale_grad,
    grad_cast_zeroTrace, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]

/-- Normalized dilation of a mean-zero function. -/
def dilateMeanZero {d : ℕ} {U V : Set (Vec d)} {a : ℝ}
    (ha : 0 < a) (hV : V = a • U) (u : H1MeanZeroFunction U) : H1MeanZeroFunction V := by
  have hU : U = a⁻¹ • V := by
    rw [hV, inv_smul_smul₀ ha.ne']
  exact a • (H1MeanZeroFunction.unscale (inv_pos.mpr ha) (hU ▸ u))

@[simp] theorem dilateMeanZero_grad {d : ℕ} {U V : Set (Vec d)} {a : ℝ}
    (ha : 0 < a) (hV : V = a • U) (u : H1MeanZeroFunction U) (x : Vec d) :
    (dilateMeanZero ha hV u).toH1Function.grad x = u.toH1Function.grad (a⁻¹ • x) := by
  subst V
  simp [dilateMeanZero, grad_cast_meanZero, smul_smul, ha.ne']

theorem IsZeroTraceDirichletRhsWeakSolution.dilate_identity
    {d : ℕ} {U V : Set (Vec d)} {a : ℝ}
    (ha : 0 < a) (hV : V = a • U) {u : H10Function U} {g : Vec d → Vec d}
    (hu : IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d) U u g) :
    IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d) V
      (dilateZeroTrace ha hV u) (fun x => g (a⁻¹ • x)) := by
  subst V
  intro phi
  have hweak := hu (phi.unscale ha)
  have hw :
      (∫ x in U, vecDot (u.toH1Function.grad x) (phi.toH1Function.grad (a • x))) =
      ∫ x in U, vecDot (g x) (phi.toH1Function.grad (a • x)) := by
    simp only [matVecMul_identityCoeffField, H10Function.unscale_toH1Function,
      H1Function.unscale_grad, vecDot_smul_right, integral_const_mul] at hweak
    exact mul_left_cancel₀ ha.ne' hweak
  have hl := Measure.setIntegral_comp_smul_of_pos (μ := volume)
    (f := fun x => vecDot (u.toH1Function.grad (a⁻¹ • x)) (phi.toH1Function.grad x))
    (s := U) ha
  have hr := Measure.setIntegral_comp_smul_of_pos (μ := volume)
    (f := fun x => vecDot (g (a⁻¹ • x)) (phi.toH1Function.grad x))
    (s := U) ha
  simp only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at hl hr
  rw [hl, hr] at hw
  simp only [Module.finrank_fin_fun, smul_eq_mul] at hw
  simp only [matVecMul_identityCoeffField, dilateZeroTrace_grad]
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero d ha.ne')) hw

theorem IsMeanZeroNeumannRhsWeakSolution.dilate_identity
    {d : ℕ} {U V : Set (Vec d)} {a : ℝ}
    (ha : 0 < a) (hV : V = a • U) {u : H1MeanZeroFunction U} {g : Vec d → Vec d}
    (hu : IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d) U u g) :
    IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d) V
      (dilateMeanZero ha hV u) (fun x => g (a⁻¹ • x)) := by
  subst V
  intro phi
  have hweak := hu (phi.unscale ha)
  have hw :
      (∫ x in U, vecDot (u.toH1Function.grad x) (phi.toH1Function.grad (a • x))) =
      ∫ x in U, vecDot (g x) (phi.toH1Function.grad (a • x)) := by
    simp only [matVecMul_identityCoeffField, H1MeanZeroFunction.unscale_grad,
      vecDot_smul_right, integral_const_mul] at hweak
    exact mul_left_cancel₀ ha.ne' hweak
  have hl := Measure.setIntegral_comp_smul_of_pos (μ := volume)
    (f := fun x => vecDot (u.toH1Function.grad (a⁻¹ • x)) (phi.toH1Function.grad x))
    (s := U) ha
  have hr := Measure.setIntegral_comp_smul_of_pos (μ := volume)
    (f := fun x => vecDot (g (a⁻¹ • x)) (phi.toH1Function.grad x))
    (s := U) ha
  simp only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] at hl hr
  rw [hl, hr] at hw
  simp only [Module.finrank_fin_fun, smul_eq_mul] at hw
  simp only [matVecMul_identityCoeffField, dilateMeanZero_grad]
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero d ha.ne')) hw

theorem openCubeSet_originCube_succ {d : ℕ} (k : ℤ) :
    openCubeSet (originCube d (k + 1)) = (3 : ℝ) • openCubeSet (originCube d k) := by
  rw [openCubeSet_originCube_eq_smul_originCube_zero,
    openCubeSet_originCube_eq_smul_originCube_zero k, smul_smul]
  congr 1
  simp only [cubeScaleFactor, originCube, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
  ring

theorem cubeVolume_originCube_succ {d : ℕ} (k : ℤ) :
    cubeVolume (originCube d (k + 1)) = (3 : ℝ) ^ d * cubeVolume (originCube d k) := by
  rw [cubeVolume_eq_pow_scale, cubeVolume_eq_pow_scale]
  simp only [originCube, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one, mul_pow]
  ring

theorem cubeAverage_grad_sq_eq {d : ℕ} (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) :
    cubeAverage Q (fun x => vecNormSq (u.grad x)) =
      (cubeVolume Q)⁻¹ * ‖u.gradToHilbertVectorL2‖ ^ 2 := by
  rw [cubeAverage, setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    ← real_inner_self_eq_norm_sq]
  change _ = (cubeVolume Q)⁻¹ * inner ℝ
    (toHilbertVectorL2OfVecField u.grad_memVectorL2)
    (toHilbertVectorL2OfVecField u.grad_memVectorL2)
  rw [inner_toHilbertVectorL2OfVecField_eq_integral]
  rfl

theorem cubeAverage_succ_pullback {d : ℕ} (k : ℤ) (f : Vec d → ℝ) :
    cubeAverage (originCube d (k + 1)) (fun x => f ((3 : ℝ)⁻¹ • x)) =
      cubeAverage (originCube d k) f := by
  have hc := Measure.setIntegral_comp_smul_of_pos (μ := volume)
    (f := fun x => f ((3 : ℝ)⁻¹ • x))
    (s := openCubeSet (originCube d k)) (by norm_num : (0 : ℝ) < 3)
  simp only [smul_smul, inv_mul_cancel₀ (by norm_num : (3 : ℝ) ≠ 0), one_smul,
    Module.finrank_fin_fun, smul_eq_mul,
    ← openCubeSet_originCube_succ] at hc
  simp only [cubeAverage, setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    cubeVolume_originCube_succ, mul_inv_rev]
  rw [mul_assoc, ← hc]

theorem dirichlet_grad_eq_of_same_rhs {d : ℕ} (Q : TriadicCube d)
    {u v : H10Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hu : IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d) (openCubeSet Q) u g)
    (hv : IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d) (openCubeSet Q) v g) :
    u.toH1Function.gradToHilbertVectorL2 = v.toH1Function.gradToHilbertVectorL2 := by
  have heq := hu.gradToVectorL2_eq_of_isEllipticFieldOn
    (openCubeSet_nonempty_internal Q) hv
    (isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q))
  have hb (z : H1Function (openCubeSet Q)) :
      z.gradToHilbertVectorL2 = vectorL2ToHilbertVectorL2 z.gradToVectorL2 :=
    (vectorL2ToHilbertVectorL2_toVectorL2 z.grad_memVectorL2).symm
  rw [hb u.toH1Function, hb v.toH1Function, heq]

theorem neumann_grad_eq_of_same_rhs {d : ℕ} (Q : TriadicCube d)
    {u v : H1MeanZeroFunction (openCubeSet Q)} {g : Vec d → Vec d}
    (hu : IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d) (openCubeSet Q) u g)
    (hv : IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d) (openCubeSet Q) v g) :
    u.gradToHilbertVectorL2 = v.gradToHilbertVectorL2 := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have heq := hu.gradToVectorL2_eq_of_isEllipticFieldOn
    (openCubeSet_nonempty_internal Q) hv
    (isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q))
  have hb (z : H1MeanZeroFunction (openCubeSet Q)) :
      z.gradToHilbertVectorL2 = vectorL2ToHilbertVectorL2 z.gradToVectorL2 :=
    (vectorL2ToHilbertVectorL2_toVectorL2 z.toH1Function.grad_memVectorL2).symm
  rw [hb u, hb v, heq]

end SubdiffusiveProcess.LaplacianCorrector
