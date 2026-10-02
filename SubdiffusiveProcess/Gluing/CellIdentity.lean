import Mathlib
import Homogenization.Sobolev.H1.Definitions
import Homogenization.Sobolev.WeakDerivatives
import SubdiffusiveProcess.Gluing.Cutoff
import SubdiffusiveProcess.Gluing.Vanishing

/-!
# Gluing: the weak-derivative identity of one cell tested against `θ φ`

For `u ∈ H¹(ball c h)`, `φ` smooth with compact support and `θ = gcTheta c h δ`, the product
`θ φ` is an admissible test function in the cell, and (with `W = u` on the cell)
`∫ W θ ∂_jφ + ∫ W φ ∂_jθ = - ∫ ∂_j u θ φ`, all integrals over the whole space.
-/

open MeasureTheory Set Filter Topology Homogenization
open scoped ContDiff
noncomputable section
namespace SubdiffusiveProcess.Gluing

variable {d : ℕ}

theorem fderiv_mul_apply {θ φ : (Fin d → ℝ) → ℝ} (hθ : ContDiff ℝ ∞ θ) (hφ : ContDiff ℝ ∞ φ)
    (x : Fin d → ℝ) (v : Fin d → ℝ) :
    fderiv ℝ (fun y => θ y * φ y) x v =
      θ x * fderiv ℝ φ x v + φ x * fderiv ℝ θ x v := by
  have hdθ : Differentiable ℝ θ := hθ.differentiable (by simp)
  have hdφ : Differentiable ℝ φ := hφ.differentiable (by simp)
  have := ((hdθ x).hasFDerivAt.mul (hdφ x).hasFDerivAt).fderiv
  change fderiv ℝ (θ * φ) x v = _
  rw [this]
  simp [smul_eq_mul]

/-- A function vanishing off a set has the same set integral and full integral. -/
theorem setIntegral_eq_integral_of_notMem_zero {s : Set (Fin d → ℝ)} {F : (Fin d → ℝ) → ℝ}
    (h : ∀ x, x ∉ s → F x = 0) : ∫ x in s, F x = ∫ x, F x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero h

theorem cell_identity {c : Fin d → ℝ} {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    (u : H1Function (Metric.ball c h)) {W : (Fin d → ℝ) → ℝ} (hWc : Continuous W)
    (hW : ∀ x ∈ Metric.ball c h, W x = u.toFun x)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (j : Fin d) :
    (∫ x, W x * (gcTheta c h δ x * fderiv ℝ φ x (Pi.single j 1))) +
      (∫ x, W x * (φ x * fderiv ℝ (gcTheta c h δ) x (Pi.single j 1))) =
      -∫ x, (u.grad x j) * (gcTheta c h δ x * φ x) := by
  set θ := gcTheta c h δ with hθdef
  have hθ : ContDiff ℝ ∞ θ := gcTheta_contDiff c h δ
  have hθc : HasCompactSupport θ := hasCompactSupport_gcTheta hh hδ
  have hθsub : tsupport θ ⊆ Metric.ball c h := tsupport_gcTheta_subset hh hδ
  have hψ : ContDiff ℝ ∞ (fun y => θ y * φ y) := hθ.mul hφ
  have hψc : HasCompactSupport (fun y => θ y * φ y) := hθc.mul_right
  have hψsub : tsupport (fun y => θ y * φ y) ⊆ Metric.ball c h :=
    (tsupport_mul_subset_left).trans hθsub
  have hweak : (∫ x in Metric.ball c h,
      u.toFun x * fderiv ℝ (fun y => θ y * φ y) x (Pi.single j 1)) =
      -∫ x in Metric.ball c h, u.grad x j * (θ x * φ x) :=
    u.hasWeakGradient j (fun y => θ y * φ y) hψ hψc hψsub
  -- vanishing off the cell
  have hθ0 : ∀ x, x ∉ Metric.ball c h → θ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hxt => hx (hθsub hxt)
  have hdθ0 : ∀ x, x ∉ Metric.ball c h → fderiv ℝ θ x (Pi.single j 1) = 0 := by
    intro x hx
    have hnot : x ∉ tsupport fun x => fderiv ℝ θ x (Pi.single j 1) :=
      fun hxt => hx (hθsub (gl_tsupport_fderiv_apply_subset _ hxt))
    simpa using image_eq_zero_of_notMem_tsupport hnot
  -- the left side of the weak identity
  have hdψ : ∀ x, fderiv ℝ (fun y => θ y * φ y) x (Pi.single j 1) =
      θ x * fderiv ℝ φ x (Pi.single j 1) + φ x * fderiv ℝ θ x (Pi.single j 1) :=
    fun x => fderiv_mul_apply hθ hφ x _
  have hL : ∫ x in Metric.ball c h, u.toFun x * fderiv ℝ (fun y => θ y * φ y) x (Pi.single j 1) =
      (∫ x, W x * (θ x * fderiv ℝ φ x (Pi.single j 1))) +
        (∫ x, W x * (φ x * fderiv ℝ θ x (Pi.single j 1))) := by
    have e1 : ∫ x in Metric.ball c h, u.toFun x * fderiv ℝ (fun y => θ y * φ y) x (Pi.single j 1) =
        ∫ x in Metric.ball c h, (W x * (θ x * fderiv ℝ φ x (Pi.single j 1)) +
          W x * (φ x * fderiv ℝ θ x (Pi.single j 1))) := by
      refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun x hx => ?_
      simp only [hdψ, ← hW x hx]
      ring
    rw [e1, setIntegral_eq_integral_of_notMem_zero (fun x hx => by
      simp [hθ0 x hx, hdθ0 x hx])]
    have hcφ' : Continuous fun x => fderiv ℝ φ x (Pi.single j 1) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcθ' : Continuous fun x => fderiv ℝ θ x (Pi.single j 1) :=
      (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
    have i1 : Integrable fun x => W x * (θ x * fderiv ℝ φ x (Pi.single j 1)) :=
      (hWc.mul (hθ.continuous.mul hcφ')).integrable_of_hasCompactSupport
        ((hθc.mul_right).mul_left)
    have i2 : Integrable fun x => W x * (φ x * fderiv ℝ θ x (Pi.single j 1)) :=
      (hWc.mul (hφ.continuous.mul hcθ')).integrable_of_hasCompactSupport
        ((hθc.fderiv_apply (𝕜 := ℝ) (Pi.single j 1)).mul_left.mul_left)
    exact integral_add i1 i2
  have hR : ∫ x in Metric.ball c h, u.grad x j * (θ x * φ x) =
      ∫ x, u.grad x j * (θ x * φ x) := by
    exact setIntegral_eq_integral_of_notMem_zero (fun x hx => by simp [hθ0 x hx])
  rw [hL, hR] at hweak
  exact hweak

end SubdiffusiveProcess.Gluing
