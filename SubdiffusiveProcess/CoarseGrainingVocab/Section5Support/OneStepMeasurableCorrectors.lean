module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCanonicalCorrectors
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMeasurableForcing
public import Homogenization.Deterministic.CoarsePoincareRHS.Correctors

@[expose] public section

/-!
# Sample-measurable one-step corrector gradients

The one-step shell forcing is measurable in the Hilbert `L²` carrier and the
constant-coefficient Dirichlet/Neumann solution maps are continuous.  This
module combines those facts and identifies arbitrary weak solutions with the
canonical operator values.  Consequently no measurable choice of Sobolev
solutions is required.

This is the scalar GMC counterpart of
`Algsuperdiff/.../Corrector/CorrectorMeasurableGradient.lean`.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- A family of zero-Dirichlet one-step correctors has a measurable gradient
in the Hilbert `L²` carrier. -/
theorem measurable_oneStepShellDirichletGradL2 {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h)
    (uD : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → H10Function (openCubeSet Q))
    (huD : ∀ omega,
      CubeDirichletDivergenceProblem Q (uD omega)
        (oneStepShellForcingH1 M n h omega p Q hh).toField) :
    Measurable fun omega =>
      (uD omega).toH1Function.gradToHilbertVectorL2 := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q)
      (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  let hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization
        (openCubeSet Q) :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet Q)
  let D := oneStepDirichletGradientOfForcingClass
    (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q))
    (openCubeSet_nonempty_internal Q) hEll
  have hforce : Measurable (oneStepShellForcingL2 M n h p Q) :=
    measurable_oneStepShellForcingL2 M n h p Q hh
  have heq : (fun omega =>
      (uD omega).toH1Function.gradToHilbertVectorL2) =
      D ∘ fun omega => -oneStepShellForcingL2 M n h p Q omega := by
    funext omega
    let G := oneStepShellForcingH1 M n h omega p Q hh
    let hG : MemVectorL2 (openCubeSet Q) G.toField :=
      G.memVectorL2_toField_openCubeSet
    have hweak : IsZeroTraceDirichletRhsWeakSolution
        (identityCoeffField d) (openCubeSet Q) (uD omega)
        (fun x => -G.toField x) := by
      intro phi
      have hbase := huD omega phi
      simp only [matVecMul_identityCoeffField]
      change
        ∫ x in openCubeSet Q,
            vecDot ((uD omega).toH1Function.grad x)
              (phi.toH1Function.grad x) ∂volume =
          ∫ x in openCubeSet Q,
            vecDot (-G.toField x) (phi.toH1Function.grad x) ∂volume
      calc
        _ = -∫ x in openCubeSet Q,
            vecDot (G.toField x) (phi.toH1Function.grad x) ∂volume := by
          simpa only [CubeDirichletDivergenceProblem,
            matVecMul_identityCoeffField] using hbase
        _ = _ := by
          rw [← integral_neg]
          apply integral_congr_ae
          filter_upwards with x
          exact (vecDot_neg_left (G.toField x) (phi.toH1Function.grad x)).symm
    calc
      (uD omega).toH1Function.gradToHilbertVectorL2 =
          D (toHilbertVectorL2OfVecField hG.neg) := by
        exact gradToHilbertVectorL2_eq_oneStepDirichletGradientOfForcingClass
          hG.neg hRealize (openCubeSet_nonempty_internal Q) hEll hweak
      _ = D (-oneStepShellForcingL2 M n h p Q omega) := by
        apply congrArg D
        rw [toHilbertVectorL2OfVecField_neg_oneStep hG]
        congr 1
        exact (oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
          M n h p Q omega hh).symm
  rw [heq]
  exact (continuous_oneStepDirichletGradientOfForcingClass _ _ _).measurable.comp
    hforce.neg

/-- A family of centered Neumann one-step correctors has a measurable gradient
in the Hilbert `L²` carrier. -/
theorem measurable_oneStepShellNeumannGradL2 {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h)
    (uN : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → H1MeanZeroFunction (openCubeSet Q))
    (huN : ∀ omega,
      IsMeanZeroNeumannRhsWeakSolution
        (identityCoeffField d) (openCubeSet Q) (uN omega)
        (fun x =>
          -(oneStepShellForcingH1 M n h omega p Q hh).toField x)) :
    Measurable fun omega => (uN omega).gradToHilbertVectorL2 := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q)
      (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  let D := oneStepNeumannGradientOfForcingClass
    (translatedCubeMeanZeroH1CoerciveEstimate Q)
    (openCubeSet_nonempty_internal Q) hEll
  have hforce : Measurable (oneStepShellForcingL2 M n h p Q) :=
    measurable_oneStepShellForcingL2 M n h p Q hh
  have heq : (fun omega => (uN omega).gradToHilbertVectorL2) =
      D ∘ fun omega => -oneStepShellForcingL2 M n h p Q omega := by
    funext omega
    let G := oneStepShellForcingH1 M n h omega p Q hh
    let hG : MemVectorL2 (openCubeSet Q) G.toField :=
      G.memVectorL2_toField_openCubeSet
    calc
      (uN omega).gradToHilbertVectorL2 =
          D (toHilbertVectorL2OfVecField hG.neg) := by
        exact gradToHilbertVectorL2_eq_oneStepNeumannGradientOfForcingClass
          hG.neg (translatedCubeMeanZeroH1CoerciveEstimate Q)
          (openCubeSet_nonempty_internal Q) hEll (huN omega)
      _ = D (-oneStepShellForcingL2 M n h p Q omega) := by
        apply congrArg D
        rw [toHilbertVectorL2OfVecField_neg_oneStep hG]
        congr 1
        exact (oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
          M n h p Q omega hh).symm
  rw [heq]
  exact (continuous_oneStepNeumannGradientOfForcingClass _ _ _).measurable.comp
    hforce.neg

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
