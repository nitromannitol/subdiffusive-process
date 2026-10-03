module

public import SubdiffusiveProcess.Static.AffineChart
public import SubdiffusiveProcess.Static.HarmonicCutoffNativeCells
public import SubdiffusiveProcess.Static.HarmonicCellAffineEnergy

@[expose] public section

/-! # Affine charts of harmonic cutoff cells -/
open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal Pointwise
noncomputable section
namespace SubdiffusiveProcess.Static

def pairCastH10 {d : ℕ} {U V : Set (Vec d)} (h : U = V)
    (e : H10Function U) : H10Function V := h ▸ e
@[simp] theorem pairCastH10_fun {d : ℕ} {U V : Set (Vec d)} (h : U = V)
    (e : H10Function U) : (pairCastH10 h e).toFun = e.toFun := by subst V; rfl
@[simp] theorem pairCastH10_grad {d : ℕ} {U V : Set (Vec d)} (h : U = V)
    (e : H10Function U) : (pairCastH10 h e).grad = e.grad := by subst V; rfl

/-- Push a unit-cell zero-trace correction into a cell of arbitrary positive side. -/
def pairCellPushH10 {d : ℕ} (y : Vec d) {h : ℝ} (hh : 0 < h)
    (e : H10Function (openCubeSet (originCube d 0))) :
    H10Function (Metric.ball y (h / 2)) := by
  have heq : openCubeSet (originCube d 0) =
      h⁻¹ • (h • openCubeSet (originCube d 0)) := by
    rw [smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  let e0 := pairCastH10 heq e
  exact pairCastH10 (translate_smul_unitCube y hh)
    ((e0.unscale (inv_pos.mpr hh)).translate y)

@[simp] theorem pairCellPushH10_fun {d : ℕ} (y : Vec d) {h : ℝ} (hh : 0 < h)
    (e : H10Function (openCubeSet (originCube d 0))) (x : Vec d) :
    (pairCellPushH10 y hh e).toFun x = e.toFun (h⁻¹ • (x - y)) := by
  simp [pairCellPushH10, H10Function.translate_toH1Function,
    H1Function.translate_toFun, H10Function.unscale_toH1Function,
    H1Function.unscale_toFun]

@[simp] theorem pairCellPushH10_grad {d : ℕ} (y : Vec d) {h : ℝ} (hh : 0 < h)
    (e : H10Function (openCubeSet (originCube d 0))) (x : Vec d) :
    (pairCellPushH10 y hh e).grad x = h⁻¹ • e.grad (h⁻¹ • (x - y)) := by
  simp [pairCellPushH10, H10Function.translate_toH1Function,
    H1Function.translate_grad, H10Function.unscale_toH1Function,
    H1Function.unscale_grad]


/-- The derivative of an affine pullback carries exactly its side factor. -/
theorem pair_affine_fderiv {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (y : Vec d) (h : ℝ) (f : Vec d → F)
    (hf : Differentiable ℝ f) (x : Vec d) :
    fderiv ℝ (fun w => f (y + h • w)) x = h • fderiv ℝ f (y + h • x) := by
  have hc : HasFDerivAt (fun w : Vec d => y + h • w)
      (h • ContinuousLinearMap.id ℝ (Vec d)) x :=
    (hasFDerivAt_id x).const_smul h |>.const_add y
  rw [show (fun w => f (y + h • w)) = f ∘ (fun w => y + h • w) from rfl,
    fderiv_comp x (hf _) hc.differentiableAt, hc.fderiv]
  ext v
  simp

/-- Affine pullbacks of smooth compact data are smooth compact data. -/
theorem pair_affine_smooth_compact {d : ℕ} (y : Vec d) {h : ℝ} (hh : 0 < h)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w => f (y + h • w)) ∧
      HasCompactSupport (fun w => f (y + h • w)) := by
  have hchart : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec d => y + h • w) := by
    simpa only [Pi.add_apply, Pi.smul_apply, Function.id_def] using!
      ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec d => y)).add ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec d => h)).smul (contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec d => w))))
  refine ⟨hf.comp hchart, ?_⟩
  simpa [Function.comp_def, Homeomorph.trans_apply, Homeomorph.smulOfNeZero,
    Homeomorph.addRight, add_comm] using
    hc.comp_homeomorph ((Homeomorph.smulOfNeZero h hh.ne').trans (Homeomorph.addRight y))


/-- The first two derivative bounds scale by the first two powers of the side. -/
theorem pair_affine_derivative_bounds {d : ℕ} (y : Vec d) {h : ℝ} (hh : 0 < h)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) {B1 B2 : ℝ}
    (hB1 : ∀ x, ‖fderiv ℝ f x‖ ≤ B1)
    (hB2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B2) (x : Vec d) :
    ‖fderiv ℝ (fun w => f (y + h • w)) x‖ ≤ h * B1 ∧
      ‖fderiv ℝ (fderiv ℝ (fun w => f (y + h • w))) x‖ ≤ h ^ 2 * B2 := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    ((contDiff_succ_iff_fderiv.mp (hf.of_le (WithTop.coe_le_coe.mpr le_top) : ContDiff ℝ (1 + 1) f)).2.2).differentiable (by simp)
  have heq : fderiv ℝ (fun w => f (y + h • w)) =
      fun w => h • fderiv ℝ f (y + h • w) := funext (pair_affine_fderiv y h f hd)
  constructor
  · rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left (hB1 _) hh.le
  · rw [heq]
    have hc : Differentiable ℝ (fun w : Vec d => fderiv ℝ f (y + h • w)) :=
      hdf.comp ((differentiable_const y).add (differentiable_id.const_smul h))
    change ‖fderiv ℝ (h • (fun w : Vec d => fderiv ℝ f (y + h • w))) x‖ ≤ _
    rw [fderiv_const_smul (hc x) h,
      pair_affine_fderiv y h (fderiv ℝ f) hdf x]
    calc
      _ ≤ h * (h * ‖fderiv ℝ (fderiv ℝ f) (y + h • x)‖) := by
        have h1 := ContinuousLinearMap.opNorm_smul_le h (h • fderiv ℝ (fderiv ℝ f) (y + h • x))
        have h2 := ContinuousLinearMap.opNorm_smul_le h (fderiv ℝ (fderiv ℝ f) (y + h • x))
        rw [Real.norm_eq_abs, abs_of_pos hh] at h1 h2
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hh.le)
      _ ≤ h ^ 2 * B2 := by nlinarith only [mul_le_mul_of_nonneg_left (hB2 (y + h • x)) (sq_nonneg h)]

/-- The native smooth gradient vector obeys the same affine chain rule. -/
theorem pair_affine_gradVec {d : ℕ} (y : Vec d) (h : ℝ)
    (f : Vec d → ℝ) (hf : Differentiable ℝ f) (x : Vec d) :
    aux_hcut_gradVec (fun w => f (y + h • w)) x =
      h • aux_hcut_gradVec f (y + h • x) := by
  funext i
  simp [aux_hcut_gradVec, pair_affine_fderiv y h f hf x]

end SubdiffusiveProcess.Static
