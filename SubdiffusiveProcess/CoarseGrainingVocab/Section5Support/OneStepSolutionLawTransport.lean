module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMeasurableCorrectors
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationarySetTransfer
public import Homogenization.Sobolev.Foundations.CoerciveH1Translation

@[expose] public section

/-!
# Stationary transport of finite-volume one-step solution observables

The finite-volume corrector on a translated cube is obtained by translating
the solution on the origin cube for the translated cutoff sample.  The
translation covariance is deterministic; stationarity is applied only after
the gradient has been represented by the fixed continuous solution operator.
Thus no measurable choice of Sobolev solutions is used.

This is the GMC analogue of the measurable-corrector and stationarity split in
`Algsuperdiff/Section3/Provider/Diffusivity/Corrector/CorrectorMeasurableGradient.lean`
and
`Algsuperdiff/Section3/Provider/Diffusivity/ApproximateRecurrence/
LocalizationFluctuationStationarity.lean`.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- Translating the sample translates the literal one-step suffix multiplier
in the opposite argument slot. -/
theorem oneStepMultiplierAt_translatePotentialSequence {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (z x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    oneStepMultiplierAt M n h x (translatePotentialSequence z omega) =
      oneStepMultiplierAt M n h (x + z) omega := by
  unfold oneStepMultiplierAt cutoffRatioMinusOne aCutoffAtInt
  split_ifs with hn
  <;> simp only [aCutoff_translatePotentialSequence]

/-- Translation covariance of the literal one-step vector forcing. -/
theorem oneStepForcingField_translatePotentialSequence {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (z x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    oneStepMultiplierAt M n h x (translatePotentialSequence z omega) • p =
      oneStepMultiplierAt M n h (x + z) omega • p := by
  rw [oneStepMultiplierAt_translatePotentialSequence]

/-- Change of variables under the stationary product law, stated for the real
observables used below. -/
theorem integral_comp_translatePotentialSequence_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Vec d)
    (F : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ) (hF : AEStronglyMeasurable F M.P.toMeasure) :
    ∫ omega, F (translatePotentialSequence z omega) ∂M.P.toMeasure =
      ∫ omega, F omega ∂M.P.toMeasure := by
  simpa [Function.comp_def] using Homogenization.integral_comp_eq_of_map_eq
    (measurable_translatePotentialSequence z)
    (potentialSequenceLaw_stationary M z) F hF

/-- The product cutoff law is measure preserving under every spatial
translation. -/
theorem measurePreserving_translatePotentialSequence {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Vec d) :
    MeasurePreserving (translatePotentialSequence (d := d) z)
      M.P.toMeasure M.P.toMeasure :=
  ⟨measurable_translatePotentialSequence z,
    potentialSequenceLaw_stationary M z⟩

/-! ## Deterministic covariance of the two weak problems -/

/-- A zero-trace solution for the identity coefficient translates to the
translated domain with the translated vector datum. -/
theorem IsZeroTraceDirichletRhsWeakSolution.translate_identity
    {d : ℕ} {U : Set (Vec d)} {u : H10Function U}
    {g : Vec d → Vec d}
    (hu : IsZeroTraceDirichletRhsWeakSolution
      (identityCoeffField d) U u g) (z : Vec d) :
    IsZeroTraceDirichletRhsWeakSolution
      (identityCoeffField d) (translateSet z U) (u.translate z)
      (fun x ↦ g (x - z)) := by
  intro phiZ
  let phi : H10Function U := phiZ.untranslate z
  have hweak := hu phi
  have hleft :
      ∫ x in translateSet z U,
          vecDot (matVecMul (identityCoeffField d x)
            ((u.translate z).toH1Function.grad x))
            (phiZ.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (u.toH1Function.grad x)
          (phi.toH1Function.grad x) ∂volume := by
    rw [← setIntegral_comp_addRight_translateSet z U]
    apply integral_congr_ae
    filter_upwards with x
    simp [phi, matVecMul_identityCoeffField, sub_eq_add_neg, add_assoc]
  have hright :
      ∫ x in translateSet z U,
          vecDot (g (x - z)) (phiZ.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (g x) (phi.toH1Function.grad x) ∂volume := by
    rw [← setIntegral_comp_addRight_translateSet z U]
    apply integral_congr_ae
    filter_upwards with x
    simp [phi, sub_eq_add_neg, add_assoc]
  rw [hleft, hright]
  simpa only [matVecMul_identityCoeffField] using hweak

/-- A centered Neumann solution for the identity coefficient translates to
the translated domain with the translated vector datum. -/
theorem IsMeanZeroNeumannRhsWeakSolution.translate_identity
    {d : ℕ} {U : Set (Vec d)} {u : H1MeanZeroFunction U}
    {g : Vec d → Vec d}
    (hu : IsMeanZeroNeumannRhsWeakSolution
      (identityCoeffField d) U u g) (z : Vec d) :
    IsMeanZeroNeumannRhsWeakSolution
      (identityCoeffField d) (translateSet z U) (u.translate z)
      (fun x ↦ g (x - z)) := by
  intro phiZ
  let phi : H1MeanZeroFunction U := phiZ.untranslate z
  have hweak := hu phi
  have hleft :
      ∫ x in translateSet z U,
          vecDot (matVecMul (identityCoeffField d x)
            ((u.translate z).toH1Function.grad x))
            (phiZ.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (u.toH1Function.grad x)
          (phi.toH1Function.grad x) ∂volume := by
    rw [← setIntegral_comp_addRight_translateSet z U]
    apply integral_congr_ae
    filter_upwards with x
    simp [phi, matVecMul_identityCoeffField, sub_eq_add_neg, add_assoc]
  have hright :
      ∫ x in translateSet z U,
          vecDot (g (x - z)) (phiZ.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (g x) (phi.toH1Function.grad x) ∂volume := by
    rw [← setIntegral_comp_addRight_translateSet z U]
    apply integral_congr_ae
    filter_upwards with x
    simp [phi, sub_eq_add_neg, add_assoc]
  rw [hleft, hright]
  simpa only [matVecMul_identityCoeffField] using hweak

/-- Translation is an isometry on the Hilbert `L²` class of an `H¹`
gradient. -/
theorem H1Function.norm_gradToHilbertVectorL2_translate_eq
    {d : ℕ} {U : Set (Vec d)} (u : H1Function U) (z : Vec d) :
    ‖(u.translate z).gradToHilbertVectorL2‖ =
      ‖u.gradToHilbertVectorL2‖ := by
  let T : Vec d → Vec d := fun x ↦ x - z
  let hmu := measurePreserving_subRight_restrict_translateSet (d := d) z U
  unfold H1Function.gradToHilbertVectorL2 toHilbertVectorL2OfVecField
    toHilbertVectorL2
  rw [Lp.norm_toLp, Lp.norm_toLp]
  exact congrArg ENNReal.toReal (by
    simpa [H1Function.translate, hilbertifyVecField, T, Function.comp,
      volumeMeasureOn] using!
      (eLpNorm_comp_measurePreserving
        (g := hilbertifyVecField u.grad) (p := (2 : ℝ≥0∞))
        (memHilbertVectorL2_hilbertifyVecField
          u.grad_memVectorL2).aestronglyMeasurable hmu))

section OriginCube

variable {d : ℕ}

/-- Canonical origin-cube zero-Dirichlet solution for the literal suffix
forcing. -/
def oneStepOriginDirichletSolution [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    H10Function (openCubeSet (originCube d m)) := by
  let Q := originCube d m
  let G := oneStepShellForcingH1 M n h omega p Q hh
  exact CubeCalderonZygmund.openCubeSetScalarDivergenceSolution
    Q (sigma0 := 1) (by norm_num) G.toField
      G.memVectorL2_toField_openCubeSet

theorem oneStepOriginDirichletSolution_isWeakSolution [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d)
      (openCubeSet (originCube d m))
      (oneStepOriginDirichletSolution M n h p m omega hh)
      (fun x ↦ -oneStepMultiplierAt M n h x omega • p) := by
  let Q := originCube d m
  let G := oneStepShellForcingH1 M n h omega p Q hh
  intro phi
  have hweak :=
    CubeCalderonZygmund.openCubeSetScalarDivergenceSolution_weak
      Q (sigma0 := 1) (by norm_num) G.toField
        G.memVectorL2_toField_openCubeSet phi
  have hfield : ∀ x, G.toField x =
      oneStepMultiplierAt M n h x omega • p := by
    intro x
    rw [oneStepShellForcing_paired_toField M n h omega p Q hh,
      oneStepShellForcingW14_toField_apply]
  calc
    _ = -∫ x in openCubeSet Q,
        vecDot (G.toField x) (phi.toH1Function.grad x) ∂volume := by
      simpa only [oneStepOriginDirichletSolution, Q, G,
        matVecMul_identityCoeffField, one_mul] using hweak
    _ = ∫ x in openCubeSet Q,
        vecDot (-oneStepMultiplierAt M n h x omega • p)
          (phi.toH1Function.grad x) ∂volume := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      rw [hfield]
      simp only [vecDot_neg_left, neg_smul]

/-- Canonical origin-cube centered Neumann solution for the literal suffix
forcing. -/
def oneStepOriginNeumannSolution [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    H1MeanZeroFunction (openCubeSet (originCube d m)) := by
  let Q := originCube d m
  let G := oneStepShellForcingH1 M n h omega p Q hh
  exact CubeCalderonZygmund.centeredCubeMeanZeroScalarDivergenceSolution
    m (sigma0 := 1) (by norm_num) G.toField
      G.memVectorL2_toField_openCubeSet

theorem oneStepOriginNeumannSolution_isWeakSolution [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d)
      (openCubeSet (originCube d m))
      (oneStepOriginNeumannSolution M n h p m omega hh)
      (fun x ↦ -oneStepMultiplierAt M n h x omega • p) := by
  let Q := originCube d m
  let G := oneStepShellForcingH1 M n h omega p Q hh
  have hweak :=
    CubeCalderonZygmund.centeredCubeMeanZeroScalarDivergenceSolution_isWeakSolution
      m (sigma0 := 1) (by norm_num) G.toField
        G.memVectorL2_toField_openCubeSet
  have hfield : ∀ x, G.toField x =
      oneStepMultiplierAt M n h x omega • p := by
    intro x
    rw [oneStepShellForcing_paired_toField M n h omega p Q hh,
      oneStepShellForcingW14_toField_apply]
  simpa only [oneStepOriginNeumannSolution, Q, G, scalarMatrix,
    hfield, neg_smul] using! hweak

/-- The Dirichlet gradient returned by the fixed solution operator on an
origin cube. -/
def oneStepOriginDirichletGradientL2 [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    HilbertVectorL2 (openCubeSet (originCube d m)) := by
  let Q := originCube d m
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q)
      (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  exact oneStepDirichletGradientOfForcingClass
    (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q))
    (openCubeSet_nonempty_internal Q) hEll
    (-oneStepShellForcingL2 M n h p Q omega)

/-- The Neumann gradient returned by the fixed solution operator on an origin
cube. -/
def oneStepOriginNeumannGradientL2 [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    HilbertVectorL2 (openCubeSet (originCube d m)) := by
  let Q := originCube d m
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q)
      (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  exact oneStepNeumannGradientOfForcingClass
    (translatedCubeMeanZeroH1CoerciveEstimate Q)
    (openCubeSet_nonempty_internal Q) hEll
    (-oneStepShellForcingL2 M n h p Q omega)

theorem oneStepOriginDirichletSolution_gradient_eq [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    H1Function.gradToHilbertVectorL2
        (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function =
      oneStepOriginDirichletGradientL2 M n h p m omega := by
  let Q := originCube d m
  let G := oneStepShellForcingH1 M n h omega p Q hh
  let hG : MemVectorL2 (openCubeSet Q) G.toField :=
    G.memVectorL2_toField_openCubeSet
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q)
      (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  have hweak : IsZeroTraceDirichletRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q)
      (oneStepOriginDirichletSolution M n h p m omega hh)
      (fun x ↦ -G.toField x) := by
    intro phi
    have hraw :=
      CubeCalderonZygmund.openCubeSetScalarDivergenceSolution_weak
        Q (sigma0 := 1) (by norm_num) G.toField hG phi
    calc
      _ = -∫ x in openCubeSet Q,
          vecDot (G.toField x) (phi.toH1Function.grad x) ∂volume := by
        simpa only [oneStepOriginDirichletSolution, Q, G,
          matVecMul_identityCoeffField, one_mul] using hraw
      _ = ∫ x in openCubeSet Q,
          vecDot (-G.toField x) (phi.toH1Function.grad x) ∂volume := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with x
        simp only [vecDot_neg_left]
  calc
    _ = oneStepDirichletGradientOfForcingClass
        (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q))
        (openCubeSet_nonempty_internal Q) hEll
        (toHilbertVectorL2OfVecField hG.neg) := by
      exact gradToHilbertVectorL2_eq_oneStepDirichletGradientOfForcingClass
        hG.neg
        (PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
          (isOpenBoundedConvexDomain_openCubeSet Q))
        (openCubeSet_nonempty_internal Q) hEll hweak
    _ = oneStepOriginDirichletGradientL2 M n h p m omega := by
      apply congrArg (oneStepDirichletGradientOfForcingClass
        (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q))
        (openCubeSet_nonempty_internal Q) hEll)
      rw [toHilbertVectorL2OfVecField_neg_oneStep hG]
      congr 1
      exact (oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
        M n h p Q omega hh).symm

theorem oneStepOriginNeumannSolution_gradient_eq [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    (oneStepOriginNeumannSolution M n h p m omega hh).gradToHilbertVectorL2 =
      oneStepOriginNeumannGradientL2 M n h p m omega := by
  let Q := originCube d m
  let G := oneStepShellForcingH1 M n h omega p Q hh
  let hG : MemVectorL2 (openCubeSet Q) G.toField :=
    G.memVectorL2_toField_openCubeSet
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q)
      (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  have hweak : IsMeanZeroNeumannRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q)
      (oneStepOriginNeumannSolution M n h p m omega hh)
      (fun x ↦ -G.toField x) := by
    simpa only [oneStepOriginNeumannSolution, Q, G, scalarMatrix] using!
      (CubeCalderonZygmund.centeredCubeMeanZeroScalarDivergenceSolution_isWeakSolution
        m (sigma0 := 1) (by norm_num) G.toField hG)
  calc
    _ = oneStepNeumannGradientOfForcingClass
        (translatedCubeMeanZeroH1CoerciveEstimate Q)
        (openCubeSet_nonempty_internal Q) hEll
        (toHilbertVectorL2OfVecField hG.neg) := by
      exact gradToHilbertVectorL2_eq_oneStepNeumannGradientOfForcingClass
        hG.neg (translatedCubeMeanZeroH1CoerciveEstimate Q)
        (openCubeSet_nonempty_internal Q) hEll hweak
    _ = oneStepOriginNeumannGradientL2 M n h p m omega := by
      apply congrArg (oneStepNeumannGradientOfForcingClass
        (translatedCubeMeanZeroH1CoerciveEstimate Q)
        (openCubeSet_nonempty_internal Q) hEll)
      rw [toHilbertVectorL2OfVecField_neg_oneStep hG]
      congr 1
      exact (oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
        M n h p Q omega hh).symm

/-! ## Energy contraction of the canonical solution operators -/

/-- For the identity coefficient, the zero-Dirichlet solution-gradient
operator is a contraction of the ambient `L²` forcing class. -/
theorem norm_oneStepOriginDirichletGradientL2_le_forcing [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    ‖oneStepOriginDirichletGradientL2 M n h p m omega‖ ≤
      ‖oneStepShellForcingL2 M n h p (originCube d m) omega‖ := by
  let Q := originCube d m
  let u := oneStepOriginDirichletSolution M n h p m omega hh
  let G := oneStepShellForcingH1 M n h omega p Q hh
  let hG : MemVectorL2 (openCubeSet Q) G.toField :=
    G.memVectorL2_toField_openCubeSet
  have hfield : ∀ x, G.toField x =
      oneStepMultiplierAt M n h x omega • p := by
    intro x
    rw [oneStepShellForcing_paired_toField M n h omega p Q hh,
      oneStepShellForcingW14_toField_apply]
  have hu : IsZeroTraceDirichletRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q) u (fun x ↦ -G.toField x) := by
    simpa only [Q, G, u, hfield, neg_smul] using
      oneStepOriginDirichletSolution_isWeakSolution M n h p m omega hh
  have henergy := hu.energy_identity
  have hlhs :
      ∫ x in openCubeSet Q,
          vecDot (u.toH1Function.grad x) (u.toH1Function.grad x) ∂volume =
        ‖u.toH1Function.gradToHilbertVectorL2‖ ^ 2 := by
    calc
      _ = inner ℝ u.toH1Function.gradToHilbertVectorL2
          u.toH1Function.gradToHilbertVectorL2 := by
        simpa [H1Function.gradToHilbertVectorL2] using
          (inner_toHilbertVectorL2OfVecField_eq_integral
            u.toH1Function.grad_memVectorL2
            u.toH1Function.grad_memVectorL2).symm
      _ = _ := real_inner_self_eq_norm_sq _
  have hrhs :
      ∫ x in openCubeSet Q,
          vecDot (-G.toField x) (u.toH1Function.grad x) ∂volume =
        inner ℝ (toHilbertVectorL2OfVecField hG.neg)
          u.toH1Function.gradToHilbertVectorL2 := by
    simpa [H1Function.gradToHilbertVectorL2] using
      (inner_toHilbertVectorL2OfVecField_eq_integral hG.neg
        u.toH1Function.grad_memVectorL2).symm
  have hsq :
      ‖u.toH1Function.gradToHilbertVectorL2‖ ^ 2 =
        inner ℝ (toHilbertVectorL2OfVecField hG.neg)
          u.toH1Function.gradToHilbertVectorL2 := by
    rw [← hlhs, ← hrhs]
    simpa only [matVecMul_identityCoeffField] using henergy
  have hmul :
      ‖u.toH1Function.gradToHilbertVectorL2‖ ^ 2 ≤
        ‖toHilbertVectorL2OfVecField hG.neg‖ *
          ‖u.toH1Function.gradToHilbertVectorL2‖ := by
    rw [hsq]
    exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hcontract :
      ‖u.toH1Function.gradToHilbertVectorL2‖ ≤
        ‖toHilbertVectorL2OfVecField hG.neg‖ := by
    have hnonneg := norm_nonneg u.toH1Function.gradToHilbertVectorL2
    by_cases hz : ‖u.toH1Function.gradToHilbertVectorL2‖ = 0
    · rw [hz]
      exact norm_nonneg _
    · have hpos : 0 < ‖u.toH1Function.gradToHilbertVectorL2‖ :=
        lt_of_le_of_ne hnonneg (Ne.symm hz)
      nlinarith
  rw [oneStepOriginDirichletSolution_gradient_eq M n h p m omega hh] at hcontract
  calc
    _ ≤ ‖toHilbertVectorL2OfVecField hG.neg‖ := hcontract
    _ = ‖oneStepShellForcingL2 M n h p Q omega‖ := by
      rw [toHilbertVectorL2OfVecField_neg_oneStep hG, norm_neg]
      exact congrArg norm
        (oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
          M n h p Q omega hh).symm

/-- The centered Neumann solution-gradient operator obeys the same identity-
coefficient contraction. -/
theorem norm_oneStepOriginNeumannGradientL2_le_forcing [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    ‖oneStepOriginNeumannGradientL2 M n h p m omega‖ ≤
      ‖oneStepShellForcingL2 M n h p (originCube d m) omega‖ := by
  let Q := originCube d m
  let u := oneStepOriginNeumannSolution M n h p m omega hh
  let G := oneStepShellForcingH1 M n h omega p Q hh
  let hG : MemVectorL2 (openCubeSet Q) G.toField :=
    G.memVectorL2_toField_openCubeSet
  have hfield : ∀ x, G.toField x =
      oneStepMultiplierAt M n h x omega • p := by
    intro x
    rw [oneStepShellForcing_paired_toField M n h omega p Q hh,
      oneStepShellForcingW14_toField_apply]
  have hu : IsMeanZeroNeumannRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q) u (fun x ↦ -G.toField x) := by
    simpa only [Q, G, u, hfield, neg_smul] using
      oneStepOriginNeumannSolution_isWeakSolution M n h p m omega hh
  have henergy := hu.energy_identity
  have hlhs :
      ∫ x in openCubeSet Q,
          vecDot (u.toH1Function.grad x) (u.toH1Function.grad x) ∂volume =
        ‖u.gradToHilbertVectorL2‖ ^ 2 := by
    calc
      _ = inner ℝ u.gradToHilbertVectorL2 u.gradToHilbertVectorL2 := by
        simpa [H1MeanZeroFunction.gradToHilbertVectorL2,
          H1Function.gradToHilbertVectorL2] using
          (inner_toHilbertVectorL2OfVecField_eq_integral
            u.toH1Function.grad_memVectorL2
            u.toH1Function.grad_memVectorL2).symm
      _ = _ := real_inner_self_eq_norm_sq _
  have hrhs :
      ∫ x in openCubeSet Q,
          vecDot (-G.toField x) (u.toH1Function.grad x) ∂volume =
        inner ℝ (toHilbertVectorL2OfVecField hG.neg)
          u.gradToHilbertVectorL2 := by
    simpa [H1MeanZeroFunction.gradToHilbertVectorL2,
      H1Function.gradToHilbertVectorL2] using
      (inner_toHilbertVectorL2OfVecField_eq_integral hG.neg
        u.toH1Function.grad_memVectorL2).symm
  have hsq : ‖u.gradToHilbertVectorL2‖ ^ 2 =
      inner ℝ (toHilbertVectorL2OfVecField hG.neg)
        u.gradToHilbertVectorL2 := by
    rw [← hlhs, ← hrhs]
    simpa only [matVecMul_identityCoeffField] using henergy
  have hmul : ‖u.gradToHilbertVectorL2‖ ^ 2 ≤
      ‖toHilbertVectorL2OfVecField hG.neg‖ *
        ‖u.gradToHilbertVectorL2‖ := by
    rw [hsq]
    exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  have hcontract : ‖u.gradToHilbertVectorL2‖ ≤
      ‖toHilbertVectorL2OfVecField hG.neg‖ := by
    have hnonneg := norm_nonneg u.gradToHilbertVectorL2
    by_cases hz : ‖u.gradToHilbertVectorL2‖ = 0
    · rw [hz]
      exact norm_nonneg _
    · have hpos : 0 < ‖u.gradToHilbertVectorL2‖ :=
        lt_of_le_of_ne hnonneg (Ne.symm hz)
      nlinarith
  rw [oneStepOriginNeumannSolution_gradient_eq M n h p m omega hh] at hcontract
  calc
    _ ≤ ‖toHilbertVectorL2OfVecField hG.neg‖ := hcontract
    _ = ‖oneStepShellForcingL2 M n h p Q omega‖ := by
      rw [toHilbertVectorL2OfVecField_neg_oneStep hG, norm_neg]
      exact congrArg norm
        (oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
          M n h p Q omega hh).symm

/-! ## Actual translated-cube solutions -/

/-- The translated-cube Dirichlet solution is the translate of the canonical
origin solution evaluated at the translated sample. -/
def oneStepTranslatedDirichletSolution [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    H10Function (translateSet z (openCubeSet (originCube d m))) :=
  (oneStepOriginDirichletSolution M n h p m
    (translatePotentialSequence z omega) hh).translate z

/-- The translated-cube Neumann solution is the translate of the canonical
origin solution evaluated at the translated sample. -/
def oneStepTranslatedNeumannSolution [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    H1MeanZeroFunction (translateSet z (openCubeSet (originCube d m))) :=
  (oneStepOriginNeumannSolution M n h p m
    (translatePotentialSequence z omega) hh).translate z

/-- The translated Dirichlet solution solves the literal problem on
`z + Q`; this is the deterministic identification needed before invoking
stationarity. -/
theorem oneStepTranslatedDirichletSolution_isWeakSolution [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d)
      (translateSet z (openCubeSet (originCube d m)))
      (oneStepTranslatedDirichletSolution M n h p z m omega hh)
      (fun x ↦ -oneStepMultiplierAt M n h x omega • p) := by
  have h0 := oneStepOriginDirichletSolution_isWeakSolution
    M n h p m (translatePotentialSequence z omega) hh
  have hT :=
    IsZeroTraceDirichletRhsWeakSolution.translate_identity h0 z
  have hdatum : (fun x : Vec d => -oneStepMultiplierAt M n h (x - z)
      (translatePotentialSequence z omega) • p) =
      (fun x => -oneStepMultiplierAt M n h x omega • p) := by
    funext x
    rw [oneStepMultiplierAt_translatePotentialSequence]
    simp only [sub_add_cancel]
  rw [hdatum] at hT
  exact hT

/-- Neumann counterpart of
`oneStepTranslatedDirichletSolution_isWeakSolution`. -/
theorem oneStepTranslatedNeumannSolution_isWeakSolution [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d)
      (translateSet z (openCubeSet (originCube d m)))
      (oneStepTranslatedNeumannSolution M n h p z m omega hh)
      (fun x ↦ -oneStepMultiplierAt M n h x omega • p) := by
  have h0 := oneStepOriginNeumannSolution_isWeakSolution
    M n h p m (translatePotentialSequence z omega) hh
  have hT :=
    IsMeanZeroNeumannRhsWeakSolution.translate_identity h0 z
  have hdatum : (fun x : Vec d => -oneStepMultiplierAt M n h (x - z)
      (translatePotentialSequence z omega) • p) =
      (fun x => -oneStepMultiplierAt M n h x omega • p) := by
    funext x
    rw [oneStepMultiplierAt_translatePotentialSequence]
    simp only [sub_add_cancel]
  rw [hdatum] at hT
  exact hT

/-- Literal fourth-power gradient observable of the translated Dirichlet
solution. -/
def oneStepTranslatedDirichletGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) : ℝ :=
  ‖H1Function.gradToHilbertVectorL2
      (oneStepTranslatedDirichletSolution M n h p z m omega hh).toH1Function‖ ^ 4

/-- Literal fourth-power gradient observable of the translated Neumann
solution. -/
def oneStepTranslatedNeumannGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) : ℝ :=
  ‖(oneStepTranslatedNeumannSolution M n h p z m omega hh).gradToHilbertVectorL2‖ ^ 4

/-- Pathwise operator-level identification of the translated Dirichlet
observable with the origin observable evaluated at the translated sample. -/
theorem oneStepTranslatedDirichletGradientFourth_eq [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    oneStepTranslatedDirichletGradientFourth M n h p z m omega hh =
      ‖oneStepOriginDirichletGradientL2 M n h p m
        (translatePotentialSequence z omega)‖ ^ 4 := by
  unfold oneStepTranslatedDirichletGradientFourth
    oneStepTranslatedDirichletSolution
  change
    ‖H1Function.gradToHilbertVectorL2
      ((oneStepOriginDirichletSolution M n h p m
        (translatePotentialSequence z omega) hh).toH1Function.translate z)‖ ^ 4 = _
  rw [H1Function.norm_gradToHilbertVectorL2_translate_eq]
  rw [oneStepOriginDirichletSolution_gradient_eq M n h p m
    (translatePotentialSequence z omega) hh]

/-- Pathwise operator-level identification of the translated Neumann
observable with the origin observable evaluated at the translated sample. -/
theorem oneStepTranslatedNeumannGradientFourth_eq [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    oneStepTranslatedNeumannGradientFourth M n h p z m omega hh =
      ‖oneStepOriginNeumannGradientL2 M n h p m
        (translatePotentialSequence z omega)‖ ^ 4 := by
  unfold oneStepTranslatedNeumannGradientFourth
    oneStepTranslatedNeumannSolution
  change
    ‖H1Function.gradToHilbertVectorL2
      ((oneStepOriginNeumannSolution M n h p m
        (translatePotentialSequence z omega) hh).toH1Function.translate z)‖ ^ 4 = _
  rw [H1Function.norm_gradToHilbertVectorL2_translate_eq]
  have heq := oneStepOriginNeumannSolution_gradient_eq M n h p m
    (translatePotentialSequence z omega) hh
  change H1Function.gradToHilbertVectorL2
      (oneStepOriginNeumannSolution M n h p m
        (translatePotentialSequence z omega) hh).toH1Function = _ at heq
  rw [heq]

theorem measurable_oneStepOriginDirichletGradientL2 [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable (oneStepOriginDirichletGradientL2 M n h p m) := by
  let Q := originCube d m
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q)
      (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  exact (continuous_oneStepDirichletGradientOfForcingClass
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q))
      (openCubeSet_nonempty_internal Q) hEll).measurable.comp
    (measurable_oneStepShellForcingL2 M n h p Q hh).neg

theorem measurable_oneStepOriginNeumannGradientL2 [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable (oneStepOriginNeumannGradientL2 M n h p m) := by
  let Q := originCube d m
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q)
      (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  exact (continuous_oneStepNeumannGradientOfForcingClass
      (translatedCubeMeanZeroH1CoerciveEstimate Q)
      (openCubeSet_nonempty_internal Q) hEll).measurable.comp
    (measurable_oneStepShellForcingL2 M n h p Q hh).neg

/-- Fourth power of the origin-cube Dirichlet solution-operator gradient. -/
def oneStepOriginDirichletGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  ‖oneStepOriginDirichletGradientL2 M n h p m omega‖ ^ 4

/-- Fourth power of the origin-cube Neumann solution-operator gradient. -/
def oneStepOriginNeumannGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  ‖oneStepOriginNeumannGradientL2 M n h p m omega‖ ^ 4

theorem measurable_oneStepOriginDirichletGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable (oneStepOriginDirichletGradientFourth M n h p m) := by
  exact ((measurable_oneStepOriginDirichletGradientL2 M n h p m hh).norm.pow_const 4)

theorem measurable_oneStepOriginNeumannGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable (oneStepOriginNeumannGradientFourth M n h p m) := by
  exact ((measurable_oneStepOriginNeumannGradientL2 M n h p m hh).norm.pow_const 4)

/-- The literal translated-cube Dirichlet fourth-moment observable is Borel
measurable because it is the origin solution-operator observable composed
with the measurable sample translation. -/
theorem measurable_oneStepTranslatedDirichletGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable (fun omega ↦
      oneStepTranslatedDirichletGradientFourth M n h p z m omega hh) := by
  have heq : (fun omega ↦
      oneStepTranslatedDirichletGradientFourth M n h p z m omega hh) =
      oneStepOriginDirichletGradientFourth M n h p m ∘
        translatePotentialSequence z := by
    funext omega
    exact oneStepTranslatedDirichletGradientFourth_eq M n h p z m omega hh
  rw [heq]
  exact (measurable_oneStepOriginDirichletGradientFourth M n h p m hh).comp
    (measurable_translatePotentialSequence z)

/-- Neumann counterpart of
`measurable_oneStepTranslatedDirichletGradientFourth`. -/
theorem measurable_oneStepTranslatedNeumannGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable (fun omega ↦
      oneStepTranslatedNeumannGradientFourth M n h p z m omega hh) := by
  have heq : (fun omega ↦
      oneStepTranslatedNeumannGradientFourth M n h p z m omega hh) =
      oneStepOriginNeumannGradientFourth M n h p m ∘
        translatePotentialSequence z := by
    funext omega
    exact oneStepTranslatedNeumannGradientFourth_eq M n h p z m omega hh
  rw [heq]
  exact (measurable_oneStepOriginNeumannGradientFourth M n h p m hh).comp
    (measurable_translatePotentialSequence z)

/-- Stationarity transports the fourth moment of the Dirichlet
solution-operator observable. -/
theorem integral_oneStepOriginDirichletGradientFourth_translate_eq [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    ∫ omega, oneStepOriginDirichletGradientFourth M n h p m
        (translatePotentialSequence z omega) ∂M.P.toMeasure =
      ∫ omega, oneStepOriginDirichletGradientFourth M n h p m omega
        ∂M.P.toMeasure := by
  exact integral_comp_translatePotentialSequence_eq M z _
    (measurable_oneStepOriginDirichletGradientFourth M n h p m hh).aestronglyMeasurable

/-- Stationarity transports the fourth moment of the Neumann
solution-operator observable. -/
theorem integral_oneStepOriginNeumannGradientFourth_translate_eq [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    ∫ omega, oneStepOriginNeumannGradientFourth M n h p m
        (translatePotentialSequence z omega) ∂M.P.toMeasure =
      ∫ omega, oneStepOriginNeumannGradientFourth M n h p m omega
        ∂M.P.toMeasure := by
  exact integral_comp_translatePotentialSequence_eq M z _
    (measurable_oneStepOriginNeumannGradientFourth M n h p m hh).aestronglyMeasurable

/-- The literal fourth moment on `z + Q` is exactly the fourth moment of the
origin-cube Dirichlet solution.  Stationarity is applied to the measurable
solution-operator observable, after the deterministic weak-problem
translation above. -/
theorem integral_oneStepTranslatedDirichletGradientFourth_eq_origin [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    ∫ omega, oneStepTranslatedDirichletGradientFourth
        M n h p z m omega hh ∂M.P.toMeasure =
      ∫ omega, oneStepOriginDirichletGradientFourth
        M n h p m omega ∂M.P.toMeasure := by
  calc
    _ = ∫ omega, oneStepOriginDirichletGradientFourth M n h p m
        (translatePotentialSequence z omega) ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      exact oneStepTranslatedDirichletGradientFourth_eq M n h p z m omega hh
    _ = _ := integral_oneStepOriginDirichletGradientFourth_translate_eq
      M n h p z m hh

/-- Neumann counterpart of
`integral_oneStepTranslatedDirichletGradientFourth_eq_origin`. -/
theorem integral_oneStepTranslatedNeumannGradientFourth_eq_origin [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    ∫ omega, oneStepTranslatedNeumannGradientFourth
        M n h p z m omega hh ∂M.P.toMeasure =
      ∫ omega, oneStepOriginNeumannGradientFourth
        M n h p m omega ∂M.P.toMeasure := by
  calc
    _ = ∫ omega, oneStepOriginNeumannGradientFourth M n h p m
        (translatePotentialSequence z omega) ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      exact oneStepTranslatedNeumannGradientFourth_eq M n h p z m omega hh
    _ = _ := integral_oneStepOriginNeumannGradientFourth_translate_eq
      M n h p z m hh

/-- Integrability of the origin Dirichlet fourth moment transports to every
translated cube. -/
theorem integrable_oneStepTranslatedDirichletGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h)
    (hI : Integrable (oneStepOriginDirichletGradientFourth M n h p m)
      M.P.toMeasure) :
    Integrable (fun omega ↦
      oneStepTranslatedDirichletGradientFourth M n h p z m omega hh)
      M.P.toMeasure := by
  have hcomp := ((measurePreserving_translatePotentialSequence M z).integrable_comp
    hI.1).2 hI
  apply hcomp.congr
  filter_upwards with omega
  exact (oneStepTranslatedDirichletGradientFourth_eq
    M n h p z m omega hh).symm

/-- Integrability of the origin Neumann fourth moment transports to every
translated cube. -/
theorem integrable_oneStepTranslatedNeumannGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h)
    (hI : Integrable (oneStepOriginNeumannGradientFourth M n h p m)
      M.P.toMeasure) :
    Integrable (fun omega ↦
      oneStepTranslatedNeumannGradientFourth M n h p z m omega hh)
      M.P.toMeasure := by
  have hcomp := ((measurePreserving_translatePotentialSequence M z).integrable_comp
    hI.1).2 hI
  apply hcomp.congr
  filter_upwards with omega
  exact (oneStepTranslatedNeumannGradientFourth_eq
    M n h p z m omega hh).symm

/-- A finite normalized family of translated Dirichlet cubes has exactly the
single origin-cube fourth moment. -/
theorem normalized_finset_integral_oneStepTranslatedDirichletGradientFourth_eq
    [NeZero d] {iota : Type*} [DecidableEq iota]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (center : iota → Vec d) (s : Finset iota) (hs : s.Nonempty)
    (m : ℤ) (hh : 0 < h) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, oneStepTranslatedDirichletGradientFourth
          M n h p (center i) m omega hh ∂M.P.toMeasure =
      ∫ omega, oneStepOriginDirichletGradientFourth M n h p m omega
        ∂M.P.toMeasure := by
  simp_rw [integral_oneStepTranslatedDirichletGradientFourth_eq_origin
    M n h p _ m hh]
  rw [Finset.sum_const]
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast hs.card_ne_zero
  simp only [nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- Neumann counterpart of the normalized finite-family law. -/
theorem normalized_finset_integral_oneStepTranslatedNeumannGradientFourth_eq
    [NeZero d] {iota : Type*} [DecidableEq iota]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (center : iota → Vec d) (s : Finset iota) (hs : s.Nonempty)
    (m : ℤ) (hh : 0 < h) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, oneStepTranslatedNeumannGradientFourth
          M n h p (center i) m omega hh ∂M.P.toMeasure =
      ∫ omega, oneStepOriginNeumannGradientFourth M n h p m omega
        ∂M.P.toMeasure := by
  simp_rw [integral_oneStepTranslatedNeumannGradientFourth_eq_origin
    M n h p _ m hh]
  rw [Finset.sum_const]
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast hs.card_ne_zero
  simp only [nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-! ## Normalized parent-gradient observables -/

/-- Normalized spatial `L²` norm of the origin Dirichlet corrector gradient. -/
def oneStepOriginDirichletNormalizedGradient [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  (cubeVolume (originCube d m))⁻¹ ^ (1 / 2 : ℝ) *
    ‖oneStepOriginDirichletGradientL2 M n h p m omega‖

/-- Normalized spatial `L²` norm of the origin Neumann corrector gradient. -/
def oneStepOriginNeumannNormalizedGradient [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  (cubeVolume (originCube d m))⁻¹ ^ (1 / 2 : ℝ) *
    ‖oneStepOriginNeumannGradientL2 M n h p m omega‖

/-- Normalized spatial `L²` norm of the translated Dirichlet gradient. -/
def oneStepTranslatedDirichletNormalizedGradient [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) : ℝ :=
  (cubeVolume (originCube d m))⁻¹ ^ (1 / 2 : ℝ) *
    ‖H1Function.gradToHilbertVectorL2
      (oneStepTranslatedDirichletSolution M n h p z m omega hh).toH1Function‖

/-- Normalized spatial `L²` norm of the translated Neumann gradient. -/
def oneStepTranslatedNeumannNormalizedGradient [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) : ℝ :=
  (cubeVolume (originCube d m))⁻¹ ^ (1 / 2 : ℝ) *
    ‖(oneStepTranslatedNeumannSolution M n h p z m omega hh).gradToHilbertVectorL2‖

/-- The source-facing fourth power of the normalized spatial `L²` norm of
the origin Dirichlet gradient.  Since the operator carrier uses restricted
Lebesgue measure, normalization contributes `|Q|⁻²` after taking the
fourth power. -/
def oneStepOriginDirichletNormalizedGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  oneStepOriginDirichletNormalizedGradient M n h p m omega ^ 4

/-- Neumann counterpart of
`oneStepOriginDirichletNormalizedGradientFourth`. -/
def oneStepOriginNeumannNormalizedGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  oneStepOriginNeumannNormalizedGradient M n h p m omega ^ 4

/-- Normalized fourth-power Dirichlet-gradient observable on `z + Q`. -/
def oneStepTranslatedDirichletNormalizedGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) : ℝ :=
  oneStepTranslatedDirichletNormalizedGradient M n h p z m omega hh ^ 4

/-- Normalized fourth-power Neumann-gradient observable on `z + Q`. -/
def oneStepTranslatedNeumannNormalizedGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) : ℝ :=
  oneStepTranslatedNeumannNormalizedGradient M n h p z m omega hh ^ 4

theorem measurable_oneStepOriginDirichletNormalizedGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable (oneStepOriginDirichletNormalizedGradientFourth M n h p m) := by
  exact (measurable_const.mul
    (measurable_oneStepOriginDirichletGradientL2 M n h p m hh).norm).pow_const 4

theorem measurable_oneStepOriginNeumannNormalizedGradientFourth [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable (oneStepOriginNeumannNormalizedGradientFourth M n h p m) := by
  exact (measurable_const.mul
    (measurable_oneStepOriginNeumannGradientL2 M n h p m hh).norm).pow_const 4

/-- The normalized Dirichlet parent-gradient observable on `z + Q` is the
origin observable evaluated at the translated sample. -/
theorem oneStepTranslatedDirichletNormalizedGradientFourth_eq [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    oneStepTranslatedDirichletNormalizedGradientFourth
        M n h p z m omega hh =
      oneStepOriginDirichletNormalizedGradientFourth M n h p m
        (translatePotentialSequence z omega) := by
  unfold oneStepTranslatedDirichletNormalizedGradientFourth
    oneStepOriginDirichletNormalizedGradientFourth
    oneStepTranslatedDirichletNormalizedGradient
    oneStepOriginDirichletNormalizedGradient
  unfold oneStepTranslatedDirichletSolution
  change (_ * ‖H1Function.gradToHilbertVectorL2
    ((oneStepOriginDirichletSolution M n h p m
      (translatePotentialSequence z omega) hh).toH1Function.translate z)‖) ^ 4 = _
  rw [H1Function.norm_gradToHilbertVectorL2_translate_eq,
    oneStepOriginDirichletSolution_gradient_eq]

/-- Neumann counterpart of
`oneStepTranslatedDirichletNormalizedGradientFourth_eq`. -/
theorem oneStepTranslatedNeumannNormalizedGradientFourth_eq [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    oneStepTranslatedNeumannNormalizedGradientFourth
        M n h p z m omega hh =
      oneStepOriginNeumannNormalizedGradientFourth M n h p m
        (translatePotentialSequence z omega) := by
  unfold oneStepTranslatedNeumannNormalizedGradientFourth
    oneStepOriginNeumannNormalizedGradientFourth
    oneStepTranslatedNeumannNormalizedGradient
    oneStepOriginNeumannNormalizedGradient
  unfold oneStepTranslatedNeumannSolution
  change (_ * ‖H1Function.gradToHilbertVectorL2
    ((oneStepOriginNeumannSolution M n h p m
      (translatePotentialSequence z omega) hh).toH1Function.translate z)‖) ^ 4 = _
  rw [H1Function.norm_gradToHilbertVectorL2_translate_eq]
  have heq := oneStepOriginNeumannSolution_gradient_eq
    M n h p m (translatePotentialSequence z omega) hh
  change H1Function.gradToHilbertVectorL2
      (oneStepOriginNeumannSolution M n h p m
        (translatePotentialSequence z omega) hh).toH1Function = _ at heq
  rw [heq]

theorem measurable_oneStepTranslatedDirichletNormalizedGradientFourth
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable (fun omega ↦
      oneStepTranslatedDirichletNormalizedGradientFourth
        M n h p z m omega hh) := by
  have heq : (fun omega ↦
      oneStepTranslatedDirichletNormalizedGradientFourth
        M n h p z m omega hh) =
      oneStepOriginDirichletNormalizedGradientFourth M n h p m ∘
        translatePotentialSequence z := by
    funext omega
    exact oneStepTranslatedDirichletNormalizedGradientFourth_eq
      M n h p z m omega hh
  rw [heq]
  exact (measurable_oneStepOriginDirichletNormalizedGradientFourth
    M n h p m hh).comp (measurable_translatePotentialSequence z)

theorem measurable_oneStepTranslatedNeumannNormalizedGradientFourth
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    Measurable (fun omega ↦
      oneStepTranslatedNeumannNormalizedGradientFourth
        M n h p z m omega hh) := by
  have heq : (fun omega ↦
      oneStepTranslatedNeumannNormalizedGradientFourth
        M n h p z m omega hh) =
      oneStepOriginNeumannNormalizedGradientFourth M n h p m ∘
        translatePotentialSequence z := by
    funext omega
    exact oneStepTranslatedNeumannNormalizedGradientFourth_eq
      M n h p z m omega hh
  rw [heq]
  exact (measurable_oneStepOriginNeumannNormalizedGradientFourth
    M n h p m hh).comp (measurable_translatePotentialSequence z)

/-- Exact fourth-moment law for the normalized Dirichlet parent-gradient
observable on every translated cube. -/
theorem integral_oneStepTranslatedDirichletNormalizedGradientFourth_eq_origin
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    ∫ omega, oneStepTranslatedDirichletNormalizedGradientFourth
        M n h p z m omega hh ∂M.P.toMeasure =
      ∫ omega, oneStepOriginDirichletNormalizedGradientFourth
        M n h p m omega ∂M.P.toMeasure := by
  calc
    _ = ∫ omega, oneStepOriginDirichletNormalizedGradientFourth
        M n h p m (translatePotentialSequence z omega) ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      exact oneStepTranslatedDirichletNormalizedGradientFourth_eq
        M n h p z m omega hh
    _ = _ := integral_comp_translatePotentialSequence_eq M z _
      (measurable_oneStepOriginDirichletNormalizedGradientFourth
        M n h p m hh).aestronglyMeasurable

/-- Exact fourth-moment law for the normalized Neumann parent-gradient
observable on every translated cube. -/
theorem integral_oneStepTranslatedNeumannNormalizedGradientFourth_eq_origin
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h) :
    ∫ omega, oneStepTranslatedNeumannNormalizedGradientFourth
        M n h p z m omega hh ∂M.P.toMeasure =
      ∫ omega, oneStepOriginNeumannNormalizedGradientFourth
        M n h p m omega ∂M.P.toMeasure := by
  calc
    _ = ∫ omega, oneStepOriginNeumannNormalizedGradientFourth
        M n h p m (translatePotentialSequence z omega) ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      exact oneStepTranslatedNeumannNormalizedGradientFourth_eq
        M n h p z m omega hh
    _ = _ := integral_comp_translatePotentialSequence_eq M z _
      (measurable_oneStepOriginNeumannNormalizedGradientFourth
        M n h p m hh).aestronglyMeasurable

/-- Integrability of the normalized origin Dirichlet fourth moment transports
to every translated cube. -/
theorem integrable_oneStepTranslatedDirichletNormalizedGradientFourth
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h)
    (hI : Integrable
      (oneStepOriginDirichletNormalizedGradientFourth M n h p m)
      M.P.toMeasure) :
    Integrable (fun omega ↦
      oneStepTranslatedDirichletNormalizedGradientFourth
        M n h p z m omega hh) M.P.toMeasure := by
  have hcomp := ((measurePreserving_translatePotentialSequence M z).integrable_comp
    hI.1).2 hI
  apply hcomp.congr
  filter_upwards with omega
  exact (oneStepTranslatedDirichletNormalizedGradientFourth_eq
    M n h p z m omega hh).symm

/-- Neumann counterpart of the normalized integrability transport. -/
theorem integrable_oneStepTranslatedNeumannNormalizedGradientFourth
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p z : Vec d) (m : ℤ) (hh : 0 < h)
    (hI : Integrable
      (oneStepOriginNeumannNormalizedGradientFourth M n h p m)
      M.P.toMeasure) :
    Integrable (fun omega ↦
      oneStepTranslatedNeumannNormalizedGradientFourth
        M n h p z m omega hh) M.P.toMeasure := by
  have hcomp := ((measurePreserving_translatePotentialSequence M z).integrable_comp
    hI.1).2 hI
  apply hcomp.congr
  filter_upwards with omega
  exact (oneStepTranslatedNeumannNormalizedGradientFourth_eq
    M n h p z m omega hh).symm

/-- A finite normalized family of translated Dirichlet parent cubes has
exactly the origin normalized fourth moment. -/
theorem normalized_finset_integral_oneStepTranslatedDirichletNormalizedGradientFourth_eq
    [NeZero d] {iota : Type*} [DecidableEq iota]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (center : iota → Vec d) (s : Finset iota) (hs : s.Nonempty)
    (m : ℤ) (hh : 0 < h) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, oneStepTranslatedDirichletNormalizedGradientFourth
          M n h p (center i) m omega hh ∂M.P.toMeasure =
      ∫ omega, oneStepOriginDirichletNormalizedGradientFourth
        M n h p m omega ∂M.P.toMeasure := by
  simp_rw [integral_oneStepTranslatedDirichletNormalizedGradientFourth_eq_origin
    M n h p _ m hh]
  rw [Finset.sum_const]
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  simp only [nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- Neumann counterpart of the normalized finite-family law. -/
theorem normalized_finset_integral_oneStepTranslatedNeumannNormalizedGradientFourth_eq
    [NeZero d] {iota : Type*} [DecidableEq iota]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (center : iota → Vec d) (s : Finset iota) (hs : s.Nonempty)
    (m : ℤ) (hh : 0 < h) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, oneStepTranslatedNeumannNormalizedGradientFourth
          M n h p (center i) m omega hh ∂M.P.toMeasure =
      ∫ omega, oneStepOriginNeumannNormalizedGradientFourth
        M n h p m omega ∂M.P.toMeasure := by
  simp_rw [integral_oneStepTranslatedNeumannNormalizedGradientFourth_eq_origin
    M n h p _ m hh]
  rw [Finset.sum_const]
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  simp only [nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end OriginCube

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
