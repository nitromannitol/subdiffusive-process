import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionMaximum
/-! Comparison with constant-coefficient zero-trace unit-forcing torsion. -/

set_option autoImplicit false
open Homogenization MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Every zero-trace weak subsolution lies below the constant-coefficient torsion. -/
theorem goodCube_ae_le_constantTorsion_of_subsolution
    {d : ℕ} [NeZero d] {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    {sigma : ℝ} (hsigma : 0 < sigma) (v u : H10Function W)
    (hv : ∀ phi : H10Function W, (∀ x, 0 ≤ phi.toH1Function.toFun x) →
      sigma * (∫ x in W, vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume) ≤
        ∫ x in W, phi.toH1Function.toFun x ∂volume)
    (hu : IsMassiveWeakSolutionOn (fun _ => sigma) (fun _ => 1) 0 W
      u.toH1Function (fun _ => 1)) :
    ∀ᵐ x ∂volume.restrict W, v.toH1Function.toFun x ≤ u.toH1Function.toFun x := by
  have hpair : ∀ phi : H10Function W, (∀ x, 0 ≤ phi.toH1Function.toFun x) →
      (∫ x in W, vecDot ((v - u).toH1Function.grad x) (phi.toH1Function.grad x) ∂volume) ≤ 0 := by
    intro phi hphi
    have hv' := hv phi hphi
    have hu2 : ∫ x in W, vecDot (sigma • u.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume
        = ∫ x in W, phi.toH1Function.toFun x ∂volume := by
      have h := hu phi
      simp only [zero_mul, one_mul, zero_add] at h
      exact h
    have hu' : sigma * (∫ x in W, vecDot (u.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume)
        = ∫ x in W, phi.toH1Function.toFun x ∂volume := by
      simp_rw [vecDot_smul_left] at hu2
      rw [integral_const_mul] at hu2
      exact hu2
    have hgrad : (v - u).toH1Function.grad = v.toH1Function.grad - u.toH1Function.grad :=
      H1Function.sub_grad v.toH1Function u.toH1Function
    have hinteg :
        (fun x => vecDot ((v - u).toH1Function.grad x) (phi.toH1Function.grad x))
          = (fun x => vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x)
              - vecDot (u.toH1Function.grad x) (phi.toH1Function.grad x)) := by
      funext x
      simp only [hgrad, vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    have hsub : (∫ x in W, vecDot ((v - u).toH1Function.grad x) (phi.toH1Function.grad x) ∂volume)
        = (∫ x in W, vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume)
          - (∫ x in W, vecDot (u.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume) := by
      rw [hinteg, integral_sub
        (f := fun x => vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x))
        (g := fun x => vecDot (u.toH1Function.grad x) (phi.toH1Function.grad x))
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.integrableOn_vecDot_grad v.toH1Function phi.toH1Function)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.integrableOn_vecDot_grad u.toH1Function phi.toH1Function)]
    have hle : sigma * (∫ x in W, vecDot ((v - u).toH1Function.grad x)
        (phi.toH1Function.grad x) ∂volume) ≤ 0 := by
      rw [hsub, mul_sub]
      linarith
    by_contra hcon
    exact absurd (mul_pos hsigma (not_le.1 hcon)) (not_lt.2 hle)
  have h := goodCube_ae_nonpos_of_nonpos_laplacian_pairing hW (v - u) hpair
  filter_upwards [h] with x hx
  change (v.toH1Function - u.toH1Function).toFun x ≤ 0 at hx
  rw [H1Function.sub_toFun] at hx
  exact sub_nonpos.mp hx

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
