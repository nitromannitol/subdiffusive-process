import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.StrongValueWeakGradientEquation




set_option autoImplicit false

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization

noncomputable section

variable {d : ℕ} {W : Set (Vec d)}

/-- **The zero-mass limit of the massive equation.**  If massive weak solutions with masses
`mu n → 0` converge strongly in the value component and weakly in the gradient component,
the limit solves the Poisson equation `-∇·(c∇v) = ρ f`, i.e. the massive equation at mass
zero.  This is the `mu → 0` companion of
`isMassiveWeakSolutionOn_of_tendsto_value_of_tendsto_inner_gradient`, whose mass is fixed. -/
theorem isMassiveWeakSolutionOn_zero_of_tendsto_value_of_tendsto_inner_gradient
    {c rho : Vec d → ℝ} {lam Lam rhoMax : ℝ} {mu : ℕ → ℝ}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    {f : Vec d → ℝ} (hf : MemL2On W f)
    (w : ℕ → H1Function W) (v : H1Function W) (phi : ℕ → ℕ)
    (hmu : Tendsto (fun n ↦ mu (phi n)) atTop (nhds 0))
    (hvalue : Tendsto (fun n ↦ (w (phi n)).toScalarL2) atTop
      (nhds v.toScalarL2))
    (hgradient : ∀ z : HilbertVectorL2 W,
      Tendsto (fun n ↦ inner ℝ (w (phi n)).gradToHilbertVectorL2 z) atTop
        (nhds (inner ℝ v.gradToHilbertVectorL2 z)))
    (hw : ∀ n, IsMassiveWeakSolutionOn c rho (mu n) W (w n) f) :
    IsMassiveWeakSolutionOn c rho 0 W v f := by
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
      (fun n ↦ mu (phi n) * Lvalue (w (phi n)).toScalarL2 +
        Lgradient (w (phi n)).gradToHilbertVectorL2) atTop
      (nhds (0 * Lvalue v.toScalarL2 + Lgradient v.gradToHilbertVectorL2)) :=
    (hmu.mul hvalueLim).add hgradientLim
  let rhs := MassiveH1Hilbert.forcingFunctional hrhoMeas hrhoBdd hf test
  have heq : ∀ n, mu (phi n) * Lvalue (w (phi n)).toScalarL2 +
      Lgradient (w (phi n)).gradToHilbertVectorL2 = rhs := by
    intro n
    have hform : MassiveH1Hilbert.massiveBilin (mu := mu (phi n)) hEll hrhoMeas hrhoBdd
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
      (fun n ↦ mu (phi n) * Lvalue (w (phi n)).toScalarL2 +
        Lgradient (w (phi n)).gradToHilbertVectorL2) atTop (nhds rhs) := by
    simp only [heq]
    exact tendsto_const_nhds
  have hlimit : 0 * Lvalue v.toScalarL2 +
      Lgradient v.gradToHilbertVectorL2 = rhs :=
    tendsto_nhds_unique hleft hright
  have hform : MassiveH1Hilbert.massiveBilin (mu := 0) hEll hrhoMeas hrhoBdd
      (MassiveH1Hilbert.ofH1Function v) test = rhs := by
    simpa only [MassiveH1Hilbert.massiveBilin_apply,
      MassiveH1Hilbert.massBilin_apply,
      MassiveH1Hilbert.coeffGradientBilin_apply,
      MassiveH1Hilbert.value_ofH1Function,
      MassiveH1Hilbert.gradient_ofH1Function, test, hLvalue, hLgradient] using hlimit
  simpa only [test, rhs,
    MassiveH1Hilbert.massiveBilin_apply_ofH1Function,
    MassiveH1Hilbert.forcingFunctional_apply_ofH1Function] using hform

/-- **The zero-mass limit of a bounded pointwise family of massive solutions.**  On a
finite-measure window, a uniformly bounded pointwise limit of massive solutions whose masses
tend to zero and whose gradients are uniformly bounded has an `H¹` representative solving the
Poisson equation `-∇·(c∇v) = ρ f`.  This is the `mu → 0` companion of
`exists_isMassiveWeakSolutionOn_of_bounded_pointwise_limit`. -/
theorem exists_isMassiveWeakSolutionOn_zero_of_bounded_pointwise_limit
    [IsFiniteMeasure (volumeMeasureOn W)]
    {c rho : Vec d → ℝ} {lam Lam rhoMax C Cgrad : ℝ} {mu : ℕ → ℝ}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    {f u : Vec d → ℝ} (hf : MemL2On W f)
    (w : ℕ → H1Function W)
    (hbound : ∀ n, ∀ᵐ x ∂(volumeMeasureOn W), |(w n).toFun x| ≤ C)
    (hpoint : ∀ᵐ x ∂(volumeMeasureOn W),
      Tendsto (fun n ↦ (w n).toFun x) atTop (nhds (u x)))
    (hgradient : ∀ n, ‖(w n).gradToHilbertVectorL2‖ ≤ Cgrad)
    (hmu : Tendsto mu atTop (nhds 0))
    (hw : ∀ n, IsMassiveWeakSolutionOn c rho (mu n) W (w n) f) :
    ∃ v : H1Function W,
      v.toFun =ᵐ[volumeMeasureOn W] u ∧
        IsMassiveWeakSolutionOn c rho 0 W v f := by
  have hwMeas : ∀ n, AEStronglyMeasurable (w n).toFun (volumeMeasureOn W) :=
    fun n ↦ (w n).memL2.1
  have huMeas : AEStronglyMeasurable u (volumeMeasureOn W) :=
    aestronglyMeasurable_of_tendsto_ae atTop hwMeas hpoint
  have huBound : ∀ᵐ x ∂(volumeMeasureOn W), ‖u x‖ ≤ C := by
    filter_upwards [hpoint, ae_all_iff.2 hbound] with x hx hxb
    have hmem : u x ∈ Set.Icc (-C) C := by
      apply isClosed_Icc.mem_of_tendsto hx
      exact Filter.Eventually.of_forall fun n ↦ (abs_le.mp (hxb n))
    simpa only [Real.norm_eq_abs] using (abs_le.mpr hmem)
  have hu : MemL2On W u := MemLp.of_bound huMeas C huBound
  have hvalue : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ (w n).toFun x - u x) 2
        (volumeMeasureOn W)) atTop (nhds 0) :=
    tendsto_eLpNorm_two_of_tendsto_ae_of_dominated hwMeas hu
      (memLp_const C) hbound hpoint
  obtain ⟨v, phi, hphi, hvu, hvalueSub, hgradientSub⟩ :=
    exists_h1Function_of_tendsto_value_of_gradient_norm_le w hu hvalue
      Cgrad hgradient
  refine ⟨v, hvu, ?_⟩
  refine isMassiveWeakSolutionOn_zero_of_tendsto_value_of_tendsto_inner_gradient
    hEll hrhoMeas hrhoBdd hf w v phi ?_ hvalueSub hgradientSub hw
  simpa only [Function.comp_def] using hmu.comp hphi.tendsto_atTop

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
