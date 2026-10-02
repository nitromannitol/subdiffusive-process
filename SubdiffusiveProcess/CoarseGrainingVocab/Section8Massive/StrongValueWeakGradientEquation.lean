import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.StrongValueWeakGradientLimit

/-!
# Stability of the massive equation under local weak convergence

The cube exhaustion converges strongly in the value component and weakly in
the gradient component.  Since both terms in the massive form are continuous
linear functionals of the corresponding component, the weak equation passes
to the limit.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization

noncomputable section

variable {d : ℕ} {W : Set (Vec d)}

/-- A strong-`L²` value limit and weak-`L²` gradient limit of massive weak
solutions is again a massive weak solution. -/
theorem isMassiveWeakSolutionOn_of_tendsto_value_of_tendsto_inner_gradient
    {c rho : Vec d → ℝ} {mu lam Lam rhoMax : ℝ}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    {f : Vec d → ℝ} (hf : MemL2On W f)
    (w : ℕ → H1Function W) (v : H1Function W) (phi : ℕ → ℕ)
    (hvalue : Tendsto (fun n ↦ (w (phi n)).toScalarL2) atTop
      (nhds v.toScalarL2))
    (hgradient : ∀ z : HilbertVectorL2 W,
      Tendsto (fun n ↦ inner ℝ (w (phi n)).gradToHilbertVectorL2 z) atTop
        (nhds (inner ℝ v.gradToHilbertVectorL2 z)))
    (hw : ∀ n, IsMassiveWeakSolutionOn c rho mu W (w n) f) :
    IsMassiveWeakSolutionOn c rho mu W v f := by
  intro psi
  let test := MassiveH1Hilbert.ofH1Function psi.toH1Function
  let Lvalue : ScalarL2 W →L[ℝ] ℝ :=
    (InnerProductSpace.toDual ℝ (ScalarL2 W) psi.toH1Function.toScalarL2).comp
      (MassiveScalarMultiplier.clm hrhoMeas hrhoBdd)
  let Lgradient : HilbertVectorL2 W →L[ℝ] ℝ :=
    (InnerProductSpace.toDual ℝ (HilbertVectorL2 W)
      psi.toH1Function.gradToHilbertVectorL2).comp
      (hilbertCoeffOperator hEll)
  let z : HilbertVectorL2 W :=
    (InnerProductSpace.toDual ℝ (HilbertVectorL2 W)).symm Lgradient
  have hLvalue (F : ScalarL2 W) :
      Lvalue F = inner ℝ (MassiveScalarMultiplier.clm hrhoMeas hrhoBdd F)
        psi.toH1Function.toScalarL2 := by
    dsimp only [Lvalue]
    rw [ContinuousLinearMap.comp_apply,
      InnerProductSpace.toDual_apply_apply, real_inner_comm]
  have hLgradient (G : HilbertVectorL2 W) :
      Lgradient G = inner ℝ (hilbertCoeffOperator hEll G)
        psi.toH1Function.gradToHilbertVectorL2 := by
    dsimp only [Lgradient]
    rw [ContinuousLinearMap.comp_apply,
      InnerProductSpace.toDual_apply_apply, real_inner_comm]
  have hinner (G : HilbertVectorL2 W) :
      inner ℝ G z = Lgradient G := by
    calc
      inner ℝ G z = inner ℝ z G := (real_inner_comm G z).symm
      _ = Lgradient G := InnerProductSpace.toDual_symm_apply
  have hvalueLim : Tendsto
      (fun n ↦ Lvalue (w (phi n)).toScalarL2) atTop
      (nhds (Lvalue v.toScalarL2)) :=
    Lvalue.continuous.continuousAt.tendsto.comp hvalue
  have hgradientLim : Tendsto
      (fun n ↦ Lgradient (w (phi n)).gradToHilbertVectorL2) atTop
      (nhds (Lgradient v.gradToHilbertVectorL2)) := by
    simpa only [hinner] using hgradient z
  have hleft : Tendsto
      (fun n ↦ mu * Lvalue (w (phi n)).toScalarL2 +
        Lgradient (w (phi n)).gradToHilbertVectorL2) atTop
      (nhds (mu * Lvalue v.toScalarL2 + Lgradient v.gradToHilbertVectorL2)) :=
    (tendsto_const_nhds.mul hvalueLim).add hgradientLim
  let rhs := MassiveH1Hilbert.forcingFunctional hrhoMeas hrhoBdd hf test
  have heq : ∀ n, mu * Lvalue (w (phi n)).toScalarL2 +
      Lgradient (w (phi n)).gradToHilbertVectorL2 = rhs := by
    intro n
    have hform : MassiveH1Hilbert.massiveBilin (mu := mu) hEll hrhoMeas hrhoBdd
        (MassiveH1Hilbert.ofH1Function (w (phi n))) test = rhs := by
      simpa only [test, rhs,
        MassiveH1Hilbert.massiveBilin_apply_ofH1Function,
        MassiveH1Hilbert.forcingFunctional_apply_ofH1Function] using
        hw (phi n) psi
    simpa only [MassiveH1Hilbert.massiveBilin_apply,
      MassiveH1Hilbert.massBilin_apply,
      MassiveH1Hilbert.coeffGradientBilin_apply,
      MassiveH1Hilbert.value_ofH1Function,
      MassiveH1Hilbert.gradient_ofH1Function, test, hLvalue, hLgradient] using hform
  have hright : Tendsto
      (fun n ↦ mu * Lvalue (w (phi n)).toScalarL2 +
        Lgradient (w (phi n)).gradToHilbertVectorL2) atTop (nhds rhs) := by
    simp only [heq]
    exact tendsto_const_nhds
  have hlimit : mu * Lvalue v.toScalarL2 +
      Lgradient v.gradToHilbertVectorL2 = rhs :=
    tendsto_nhds_unique hleft hright
  have hform : MassiveH1Hilbert.massiveBilin (mu := mu) hEll hrhoMeas hrhoBdd
      (MassiveH1Hilbert.ofH1Function v) test = rhs := by
    simpa only [MassiveH1Hilbert.massiveBilin_apply,
      MassiveH1Hilbert.massBilin_apply,
      MassiveH1Hilbert.coeffGradientBilin_apply,
      MassiveH1Hilbert.value_ofH1Function,
      MassiveH1Hilbert.gradient_ofH1Function, test, hLvalue, hLgradient] using hlimit
  simpa only [test, rhs,
    MassiveH1Hilbert.massiveBilin_apply_ofH1Function,
    MassiveH1Hilbert.forcingFunctional_apply_ofH1Function] using hform

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
