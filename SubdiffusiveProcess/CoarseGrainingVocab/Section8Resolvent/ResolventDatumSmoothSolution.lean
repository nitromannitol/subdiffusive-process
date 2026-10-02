import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumDenseRange
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.VectorFieldAndApex.WeakEquationHelpers
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Filter
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- The flux `c ∇w`. -/
def coeffFlux (c w : Vec d → ℝ) : Vec d → Vec d :=
  fun x i ↦ c x * euclideanCoordDeriv i w x

/-- The classical divergence `∇·(c ∇w)`. -/
def coeffFluxDiv (c w : Vec d → ℝ) : Vec d → ℝ :=
  fun x ↦ ∑ i : Fin d, euclideanCoordDeriv i (fun y ↦ c y * euclideanCoordDeriv i w y) x

variable {c w : Vec d → ℝ}

theorem contDiff_coeffFluxComponent (hc : ContDiff ℝ 1 c) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (i : Fin d) : ContDiff ℝ 1 (fun y ↦ c y * euclideanCoordDeriv i w y) :=
  hc.mul ((contDiff_euclideanCoordDeriv hw i).of_le (by simp))

theorem continuous_coeffFluxComponent (hc : ContDiff ℝ 1 c) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (i : Fin d) : Continuous (fun y ↦ c y * euclideanCoordDeriv i w y) :=
  (contDiff_coeffFluxComponent hc hw i).continuous

theorem continuous_coeffFluxComponentDeriv (hc : ContDiff ℝ 1 c)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (i : Fin d) :
    Continuous (euclideanCoordDeriv i (fun y ↦ c y * euclideanCoordDeriv i w y)) := by
  have := (contDiff_coeffFluxComponent hc hw i).continuous_fderiv le_rfl
  simpa [euclideanCoordDeriv] using this.clm_apply continuous_const

/-- **Integration by parts for the flux of a smooth compactly supported
function against a smooth test.**  For a `C¹` coefficient `c` and a smooth `w`,
each component `c ∂ᵢw` of the flux is `C¹`, so the repository's smooth-test
weak-derivative identity `HasWeakPartialDerivOn.of_contDiff` applies coordinate
by coordinate on any set `U`. -/
theorem setIntegral_coeffFlux_dot_euclideanGradient
    (hc : ContDiff ℝ 1 c) (hw : ContDiff ℝ (⊤ : ℕ∞) w) {U : Set (Vec d)}
    {psi : Vec d → ℝ} (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) (hpsisupp : HasCompactSupport psi)
    (hsub : tsupport psi ⊆ U) :
    ∫ x in U, vecDot (coeffFlux c w x) (euclideanGradient psi x) ∂volume =
      ∫ x in U, (-(coeffFluxDiv c w x)) * psi x ∂volume := by
  classical
  set F : Fin d → Vec d → ℝ := fun i y ↦ c y * euclideanCoordDeriv i w y with hF
  have hFcont : ∀ i, Continuous (F i) := fun i ↦ continuous_coeffFluxComponent hc hw i
  have hDcont : ∀ i, Continuous (euclideanCoordDeriv i (F i)) := fun i ↦
    continuous_coeffFluxComponentDeriv hc hw i
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
        (contDiff_coeffFluxComponent hc hw i)) psi hpsi hpsisupp hsub
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

/-! ### Support and integrability of the flux -/

theorem tsupport_coeffFluxComponent_subset (i : Fin d) :
    tsupport (fun y ↦ c y * euclideanCoordDeriv i w y) ⊆ tsupport w := by
  refine closure_minimal (fun x hx ↦ ?_) isClosed_closure
  have hx' : c x * euclideanCoordDeriv i w x ≠ 0 := hx
  have hfd : fderiv ℝ w x ≠ 0 := by
    intro h
    exact hx' (by simp [euclideanCoordDeriv, h])
  exact support_fderiv_subset (𝕜 := ℝ) (f := w) hfd

theorem coeffFlux_eq_zero_of_notMem {x : Vec d} (hx : x ∉ tsupport w) :
    coeffFlux c w x = 0 := by
  have hfd : fderiv ℝ w x = 0 := by
    by_contra hne
    exact hx (support_fderiv_subset (𝕜 := ℝ) (f := w) hne)
  funext i
  simp [coeffFlux, euclideanCoordDeriv, hfd]

theorem coeffFluxDiv_eq_zero_of_notMem {x : Vec d} (hx : x ∉ tsupport w) :
    coeffFluxDiv c w x = 0 := by
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hfd : fderiv ℝ (fun y ↦ c y * euclideanCoordDeriv i w y) x = 0 := by
    by_contra hne
    exact hx (tsupport_coeffFluxComponent_subset (c := c) (w := w) i
      (support_fderiv_subset (𝕜 := ℝ) hne))
  show fderiv ℝ (fun y ↦ c y * euclideanCoordDeriv i w y) x (basisVec i) = 0
  rw [hfd]
  rfl

theorem hasCompactSupport_coeffFlux (hwsupp : HasCompactSupport w) :
    HasCompactSupport (coeffFlux c w) :=
  HasCompactSupport.intro hwsupp fun _ hx ↦ coeffFlux_eq_zero_of_notMem hx

theorem hasCompactSupport_coeffFluxDiv (hwsupp : HasCompactSupport w) :
    HasCompactSupport (coeffFluxDiv c w) :=
  HasCompactSupport.intro hwsupp fun _ hx ↦ coeffFluxDiv_eq_zero_of_notMem hx

theorem continuous_coeffFlux (hc : ContDiff ℝ 1 c) (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    Continuous (coeffFlux c w) :=
  continuous_pi fun i ↦ continuous_coeffFluxComponent hc hw i

theorem continuous_coeffFluxDiv (hc : ContDiff ℝ 1 c) (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    Continuous (coeffFluxDiv c w) :=
  continuous_finset_sum _ fun i _ ↦ continuous_coeffFluxComponentDeriv hc hw i

theorem memVectorL2_coeffFlux (hc : ContDiff ℝ 1 c) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwsupp : HasCompactSupport w) (U : Set (Vec d)) : MemVectorL2 U (coeffFlux c w) :=
  ((continuous_coeffFlux hc hw).memLp_of_hasCompactSupport
    (hasCompactSupport_coeffFlux hwsupp)).restrict U

theorem memScalarL2_neg_coeffFluxDiv (hc : ContDiff ℝ 1 c) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwsupp : HasCompactSupport w) (U : Set (Vec d)) :
    MemScalarL2 U (fun x ↦ -(coeffFluxDiv c w x)) :=
  (((continuous_coeffFluxDiv hc hw).neg).memLp_of_hasCompactSupport
    (hasCompactSupport_coeffFluxDiv hwsupp).neg).restrict U

/-- **Integration by parts against an `H¹₀` test.**  The smooth-test identity
extends to every `H¹₀(U)` test by the approximation data bundled in
`H10Function` (`Homogenization.h10WeakEquationOn_of_contDiff_tests`). -/
theorem setIntegral_coeffFlux_dot_h10grad
    (hc : ContDiff ℝ 1 c) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwsupp : HasCompactSupport w)
    {U : Set (Vec d)} (hU : IsOpen U) (phi : H10Function U) :
    ∫ x in U, vecDot (coeffFlux c w x) (phi.toH1Function.grad x) ∂volume =
      ∫ x in U, (-(coeffFluxDiv c w x)) * phi.toH1Function.toFun x ∂volume :=
  h10WeakEquationOn_of_contDiff_tests hU (memVectorL2_coeffFlux hc hw hwsupp U)
    (memScalarL2_neg_coeffFluxDiv hc hw hwsupp U)
    (fun _psi hpsi hpsisupp hsub ↦
      setIntegral_coeffFlux_dot_euclideanGradient hc hw hpsi hpsisupp hsub) phi

/-! ### A smooth compactly supported function is a massive weak solution -/

/-- The forcing for which a smooth compactly supported `w` solves the massive
equation: `f = μ w − ρ⁻¹ ∇·(c∇w)`. -/
def smoothMassiveForcing (c rho : Vec d → ℝ) (mu : ℝ) (w : Vec d → ℝ) : Vec d → ℝ :=
  fun x ↦ mu * w x - coeffFluxDiv c w x / rho x

variable {rho : Vec d → ℝ}

/-- **A smooth compactly supported function solves the massive equation** with
the classical forcing `μ w − ρ⁻¹ ∇·(c∇w)`. -/
theorem isMassiveWeakSolutionOn_ofContDiff
    (hc : ContDiff ℝ 1 c) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwsupp : HasCompactSupport w)
    {W : Set (Vec d)} (hW : IsOpen W) {mu rhoMax : ℝ}
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    (hrhoNe : ∀ x, rho x ≠ 0) :
    IsMassiveWeakSolutionOn c rho mu W
      (H1Function.ofContDiff hW (hw.of_le (by simp)) hwsupp)
      (smoothMassiveForcing c rho mu w) := by
  classical
  intro phi
  set u : H1Function W := H1Function.ofContDiff hW (hw.of_le (by simp)) hwsupp with hu
  have hufun : u.toFun = w := rfl
  have henergy : ∫ x in W, vecDot (c x • u.grad x) (phi.toH1Function.grad x) ∂volume =
      ∫ x in W, (-(coeffFluxDiv c w x)) * phi.toH1Function.toFun x ∂volume := by
    have hrw : (fun x ↦ vecDot (c x • u.grad x) (phi.toH1Function.grad x)) =
        fun x ↦ vecDot (coeffFlux c w x) (phi.toH1Function.grad x) := rfl
    rw [hrw]
    exact setIntegral_coeffFlux_dot_h10grad hc hw hwsupp hW phi
  have hmass : IntegrableOn
      (fun x ↦ rho x * w x * phi.toH1Function.toFun x) W volume :=
    integrableOn_mass_term hrhoMeas hrhoBdd u.memL2 phi.toH1Function.memL2
  have hdiv : IntegrableOn
      (fun x ↦ (-(coeffFluxDiv c w x)) * phi.toH1Function.toFun x) W volume :=
    (memScalarL2_neg_coeffFluxDiv hc hw hwsupp W).integrable_mul phi.toH1Function.memL2
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

/-! ### The bounded-domain variant, without compact support

On a bounded domain a merely smooth `w` is already in `H¹`, and the flux and
its divergence are bounded there, so the same computation applies with no
support hypothesis.  This is what exhibits the growing solutions of the massive
equation. -/

theorem memL2On_of_continuous {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    {E : Type*} [NormedAddCommGroup E] {g : Vec d → E} (hg : Continuous g) :
    MeasureTheory.MemLp g 2 (volume.restrict W) := by
  classical
  letI : MeasureTheory.IsFiniteMeasure (volume.restrict W) :=
    hW.isSobolevRegularDomain.isFiniteMeasure_restrict_volume
  have hcompact : IsCompact (closure W) :=
    hW.isSobolevRegularDomain.isBoundedDomain.isBounded.isCompact_closure
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hg.continuousOn
  refine MeasureTheory.MemLp.of_bound hg.aestronglyMeasurable C ?_
  rw [MeasureTheory.ae_restrict_iff' hW.isOpen.measurableSet]
  exact Filter.Eventually.of_forall fun x hx ↦ hC x (subset_closure hx)

/-- **A smooth function on a bounded domain solves the massive equation** with
the classical forcing.  No compact support is required. -/
theorem isMassiveWeakSolutionOn_ofContDiffOnBounded
    (hc : ContDiff ℝ 1 c) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
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
    memL2On_of_continuous hW (continuous_coeffFlux hc hw)
  have hdivL2 : MemScalarL2 W (fun x ↦ -(coeffFluxDiv c w x)) :=
    memL2On_of_continuous hW ((continuous_coeffFluxDiv hc hw).neg)
  have henergy : ∫ x in W, vecDot (c x • u.grad x) (phi.toH1Function.grad x) ∂volume =
      ∫ x in W, (-(coeffFluxDiv c w x)) * phi.toH1Function.toFun x ∂volume := by
    have hrw : (fun x ↦ vecDot (c x • u.grad x) (phi.toH1Function.grad x)) =
        fun x ↦ vecDot (coeffFlux c w x) (phi.toH1Function.grad x) := rfl
    rw [hrw]
    exact h10WeakEquationOn_of_contDiff_tests hW.isOpen hfluxL2 hdivL2
      (fun _psi hpsi hpsisupp hsub ↦
        setIntegral_coeffFlux_dot_euclideanGradient hc hw hpsi hpsisupp hsub) phi
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

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
