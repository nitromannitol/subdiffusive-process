import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- The difference of two local massive weak solutions solves the equation
with the difference of their forcing terms. -/
theorem IsMassiveWeakSolutionOn.sub {W : Set (Vec d)} {c rho : Vec d → ℝ}
    {mu lam Lam rhoMax : ℝ}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    {u v : H1Function W} {f g : Vec d → ℝ}
    (hf : MemL2On W f) (hg : MemL2On W g)
    (hu : IsMassiveWeakSolutionOn c rho mu W u f)
    (hv : IsMassiveWeakSolutionOn c rho mu W v g) :
    IsMassiveWeakSolutionOn c rho mu W (u - v) (f - g) := by
  intro phi
  have hmassU := integrableOn_mass_term hrhoMeas hrhoBdd
    u.memL2 phi.toH1Function.memL2
  have hmassV := integrableOn_mass_term hrhoMeas hrhoBdd
    v.memL2 phi.toH1Function.memL2
  have henergyU := integrableOn_energy_term hEll
    u.grad_memVectorL2 phi.toH1Function.grad_memVectorL2
  have henergyV := integrableOn_energy_term hEll
    v.grad_memVectorL2 phi.toH1Function.grad_memVectorL2
  have hrhsF := integrableOn_mass_term hrhoMeas hrhoBdd
    hf phi.toH1Function.memL2
  have hrhsG := integrableOn_mass_term hrhoMeas hrhoBdd
    hg phi.toH1Function.memL2
  rw [H1Function.sub_toFun, H1Function.sub_grad]
  simp only [Pi.sub_apply, smul_sub]
  rw [show (∫ x in W, rho x * (u.toFun x - v.toFun x) *
          phi.toH1Function.toFun x ∂volume) =
        (∫ x in W, rho x * u.toFun x * phi.toH1Function.toFun x ∂volume) -
          ∫ x in W, rho x * v.toFun x * phi.toH1Function.toFun x ∂volume by
      rw [← integral_sub hmassU hmassV]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by ring]
  rw [show (∫ x in W, vecDot
          (c x • u.grad x - c x • v.grad x) (phi.toH1Function.grad x) ∂volume) =
        (∫ x in W, vecDot (c x • u.grad x) (phi.toH1Function.grad x) ∂volume) -
          ∫ x in W, vecDot (c x • v.grad x) (phi.toH1Function.grad x) ∂volume by
      rw [← integral_sub henergyU henergyV]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]]
  rw [show (∫ x in W, rho x * (f x - g x) *
          phi.toH1Function.toFun x ∂volume) =
        (∫ x in W, rho x * f x * phi.toH1Function.toFun x ∂volume) -
          ∫ x in W, rho x * g x * phi.toH1Function.toFun x ∂volume by
      rw [← integral_sub hrhsF hrhsG]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by ring]
  have hu' := hu phi
  have hv' := hv phi
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
