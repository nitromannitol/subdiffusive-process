import SubdiffusiveProcess.Section10.TorsionExitGenerator

/-! The actual weak generator also accepts compact `C²` tests. This adapter
uses the existing coordinate integration-by-parts and native `H¹₀` approximation
exports; it does not change the coefficient energy or speed measure. -/

noncomputable section
open Homogenization MeasureTheory Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
namespace SubdiffusiveProcess.Section10

variable {d : ℕ} {c w rho : Vec d → ℝ}

/-- Two derivatives of a test give one derivative of its coordinate gradient. -/
theorem contDiff_one_euclideanCoordDeriv_of_two
    (hw : ContDiff ℝ 2 w) (i : Fin d) :
    ContDiff ℝ 1 (euclideanCoordDeriv i w) := by
  exact (hw.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem contDiff_coeffFluxComponent_of_two (hc : ContDiff ℝ 1 c) (hw : ContDiff ℝ 2 w)
    (i : Fin d) : ContDiff ℝ 1 (fun y ↦ c y * euclideanCoordDeriv i w y) :=
  hc.mul (contDiff_one_euclideanCoordDeriv_of_two hw i)

theorem continuous_coeffFluxComponent_of_two (hc : ContDiff ℝ 1 c) (hw : ContDiff ℝ 2 w)
    (i : Fin d) : Continuous (fun y ↦ c y * euclideanCoordDeriv i w y) :=
  (contDiff_coeffFluxComponent_of_two hc hw i).continuous

theorem continuous_coeffFluxComponentDeriv_of_two (hc : ContDiff ℝ 1 c)
    (hw : ContDiff ℝ 2 w) (i : Fin d) :
    Continuous (euclideanCoordDeriv i (fun y ↦ c y * euclideanCoordDeriv i w y)) := by
  have := (contDiff_coeffFluxComponent_of_two hc hw i).continuous_fderiv le_rfl
  simpa [euclideanCoordDeriv] using this.clm_apply continuous_const

/-- **Integration by parts for the flux of a smooth compactly supported
function against a smooth test.**  For a `C¹` coefficient `c` and a smooth `w`,
each component `c ∂ᵢw` of the flux is `C¹`, so the repository's smooth-test
weak-derivative identity `HasWeakPartialDerivOn.of_contDiff` applies coordinate
by coordinate on any set `U`. -/
theorem setIntegral_coeffFlux_dot_euclideanGradient_of_two
    (hc : ContDiff ℝ 1 c) (hw : ContDiff ℝ 2 w) {U : Set (Vec d)}
    {psi : Vec d → ℝ} (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) (hpsisupp : HasCompactSupport psi)
    (hsub : tsupport psi ⊆ U) :
    ∫ x in U, vecDot (coeffFlux c w x) (euclideanGradient psi x) ∂volume =
      ∫ x in U, (-(coeffFluxDiv c w x)) * psi x ∂volume := by
  classical
  set F : Fin d → Vec d → ℝ := fun i y ↦ c y * euclideanCoordDeriv i w y with hF
  have hFcont : ∀ i, Continuous (F i) := fun i ↦ continuous_coeffFluxComponent_of_two hc hw i
  have hDcont : ∀ i, Continuous (euclideanCoordDeriv i (F i)) := fun i ↦
    continuous_coeffFluxComponentDeriv_of_two hc hw i
  have hpsicont : Continuous psi := hpsi.continuous
  have hpsigradsupp : ∀ i, HasCompactSupport (euclideanCoordDeriv i psi) := fun i ↦
    hasCompactSupport_euclideanCoordDeriv hpsisupp i
  have hpsigradcont : ∀ i, Continuous (euclideanCoordDeriv i psi) := fun i ↦
    (contDiff_euclideanCoordDeriv hpsi i).continuous
  have hLint : ∀ i : Fin d,
      IntegrableOn (fun x ↦ F i x * euclideanCoordDeriv i psi x) U volume := fun i ↦
    (((hFcont i).mul (hpsigradcont i)).integrable_of_hasCompactSupport
      ((hpsigradsupp i).mul_left)).restrict
  have hRint : ∀ i : Fin d,
      IntegrableOn (fun x ↦ euclideanCoordDeriv i (F i) x * psi x) U volume := fun i ↦
    (((hDcont i).mul hpsicont).integrable_of_hasCompactSupport hpsisupp.mul_left).restrict
  have key : ∀ i : Fin d,
      ∫ x in U, F i x * euclideanCoordDeriv i psi x ∂volume =
        -∫ x in U, euclideanCoordDeriv i (F i) x * psi x ∂volume := by
    intro i
    simpa [euclideanCoordDeriv] using
      (HasWeakPartialDerivOn.of_contDiff (U := U) (i := i)
        (contDiff_coeffFluxComponent_of_two hc hw i)) psi hpsi hpsisupp hsub
  have hL : ∫ x in U, vecDot (coeffFlux c w x) (euclideanGradient psi x) ∂volume =
      ∑ i : Fin d, ∫ x in U, F i x * euclideanCoordDeriv i psi x ∂volume := by
    rw [← MeasureTheory.integral_finset_sum _ (fun i _ ↦ hLint i)]
    rfl
  have hR : ∑ i : Fin d, -∫ x in U, euclideanCoordDeriv i (F i) x * psi x ∂volume =
      ∫ x in U, (-(coeffFluxDiv c w x)) * psi x ∂volume := by
    rw [Finset.sum_neg_distrib,
      ← MeasureTheory.integral_finset_sum _ (fun i _ ↦ hRint i), ← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp [coeffFluxDiv, hF, Finset.sum_mul]
  rw [hL, ← hR]
  exact Finset.sum_congr rfl fun i _ ↦ key i


theorem isMassiveWeakSolutionOn_ofContDiffOnBounded_of_two
    (hc : ContDiff ℝ 1 c) (hw : ContDiff ℝ 2 w)
    {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W) {mu rhoMax : ℝ}
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    (hrhoNe : ∀ x, rho x ≠ 0) :
    IsMassiveWeakSolutionOn c rho mu W
      (H1Function.ofContDiffOnIsOpenBoundedConvexDomain hW (hw.of_le (by simp)))
      (smoothMassiveForcing c rho mu w) := by
  classical
  intro phi
  set u : H1Function W :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hW (hw.of_le (by simp)) with hu
  have hufun : u.toFun = w := rfl
  have hfluxL2 : MemVectorL2 W (coeffFlux c w) :=
    memL2On_of_continuous hW (continuous_pi fun i ↦ continuous_coeffFluxComponent_of_two hc hw i)
  have hdivL2 : MemScalarL2 W (fun x ↦ -(coeffFluxDiv c w x)) :=
    memL2On_of_continuous hW ((continuous_finset_sum _ fun i _ ↦ continuous_coeffFluxComponentDeriv_of_two hc hw i).neg)
  have henergy : ∫ x in W, vecDot (c x • u.grad x) (phi.toH1Function.grad x) ∂volume =
      ∫ x in W, (-(coeffFluxDiv c w x)) * phi.toH1Function.toFun x ∂volume := by
    have hrw : (fun x ↦ vecDot (c x • u.grad x) (phi.toH1Function.grad x)) =
        fun x ↦ vecDot (coeffFlux c w x) (phi.toH1Function.grad x) := rfl
    rw [hrw]
    exact h10WeakEquationOn_of_contDiff_tests hW.isOpen hfluxL2 hdivL2
      (fun _psi hpsi hpsisupp hsub ↦
        setIntegral_coeffFlux_dot_euclideanGradient_of_two hc hw hpsi hpsisupp hsub) phi
  have hmass : IntegrableOn
      (fun x ↦ rho x * w x * phi.toH1Function.toFun x) W volume :=
    integrableOn_mass_term hrhoMeas hrhoBdd u.memL2 phi.toH1Function.memL2
  have hdiv : IntegrableOn
      (fun x ↦ (-(coeffFluxDiv c w x)) * phi.toH1Function.toFun x) W volume :=
    hdivL2.integrable_mul phi.toH1Function.memL2
  have hrhs : ∫ x in W, rho x * smoothMassiveForcing c rho mu w x *
        phi.toH1Function.toFun x ∂volume =
      mu * ∫ x in W, rho x * w x * phi.toH1Function.toFun x ∂volume +
        ∫ x in W, (-(coeffFluxDiv c w x)) * phi.toH1Function.toFun x ∂volume := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add
      (hmass.const_mul mu) hdiv]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    have hne : rho x ≠ 0 := hrhoNe x
    simp only [smoothMassiveForcing]
    field_simp
    ring
  rw [henergy, hrhs, hufun]

end SubdiffusiveProcess.Section10
