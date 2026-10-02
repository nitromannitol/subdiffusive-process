import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.DomainMonotonicity
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.MassiveWeakSolutionAlgebra




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- **Re-basing an `H¹` function.**  If `v` agrees almost everywhere on `W`
with the value function of `u : H¹(W)`, then `v` itself is the value function
of an `H¹(W)` function with the same weak gradient. -/
def H1Function.ofAEEq {W : Set (Vec d)} (u : H1Function W) (v : Vec d → ℝ)
    (hv : v =ᵐ[volume.restrict W] u.toFun) : H1Function W where
  toFun := v
  grad := u.grad
  memL2 := u.memL2.ae_eq hv.symm
  gradMemL2 := u.gradMemL2
  hasWeakGradient := by
    intro i φ hφ hφc hφsub
    have hint : (∫ x in W, v x * (fderiv ℝ φ x) (basisVec i) ∂volume) =
        ∫ x in W, u.toFun x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards [hv] with x hx
      rw [hx]
    rw [hint]
    exact u.hasWeakGradient i φ hφ hφc hφsub

@[simp]
theorem H1Function.ofAEEq_toFun {W : Set (Vec d)} (u : H1Function W)
    (v : Vec d → ℝ) (hv : v =ᵐ[volume.restrict W] u.toFun) :
    (H1Function.ofAEEq u v hv).toFun = v := rfl

@[simp]
theorem H1Function.ofAEEq_grad {W : Set (Vec d)} (u : H1Function W)
    (v : Vec d → ℝ) (hv : v =ᵐ[volume.restrict W] u.toFun) :
    (H1Function.ofAEEq u v hv).grad = u.grad := rfl

/-- The weak massive equation is preserved by scalar multiples. -/
theorem IsMassiveWeakSolutionOn.const_smul {W : Set (Vec d)}
    {c rho : Vec d → ℝ} {mu : ℝ} {u : H1Function W} {f : Vec d → ℝ}
    (r : ℝ) (hu : IsMassiveWeakSolutionOn c rho mu W u f) :
    IsMassiveWeakSolutionOn c rho mu W (r • u) (fun x ↦ r * f x) := by
  intro φ
  have hEq := hu φ
  have hval : ∀ x, (r • u).toFun x = r * u.toFun x := fun x ↦ rfl
  have hgrad : ∀ x, (r • u).grad x = r • u.grad x := fun x ↦ rfl
  have hmass :
      (∫ x in W, rho x * (r • u).toFun x * φ.toH1Function.toFun x ∂volume) =
        r * ∫ x in W, rho x * u.toFun x * φ.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [hval x]; ring
  have hen :
      (∫ x in W, vecDot (c x • (r • u).grad x) (φ.toH1Function.grad x) ∂volume) =
        r * ∫ x in W, vecDot (c x • u.grad x) (φ.toH1Function.grad x) ∂volume := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [hgrad x, smul_comm (c x) r, vecDot_smul_left]
  have hrhs :
      (∫ x in W, rho x * (r * f x) * φ.toH1Function.toFun x ∂volume) =
        r * ∫ x in W, rho x * f x * φ.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    ring
  rw [hmass, hen, hrhs]
  linear_combination r * hEq

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
