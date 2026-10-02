import Homogenization.PDE.DirichletRHS
import Homogenization.PDE.NeumannRHS
import Homogenization.Sobolev.PotentialSolenoidalL2Realization
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-!
# Continuous solution operators for the one-step correctors

The pointwise correctors in the one-step argument are chosen Sobolev
solutions.  Choice alone gives no parameter measurability.  This module
instead exposes their gradient classes as fixed continuous maps of the forcing
class in `HilbertVectorL2`.

The construction mirrors
`Algsuperdiff/Section3/Provider/Diffusivity/Corrector/
MeasurablePrereqSolutionOperator.lean`: Riesz representation, restriction to
the appropriate closed gradient space, and the inverse Lax--Milgram operator.
The identification theorems apply to arbitrary weak solutions, so later
measurability results do not depend on how the Sobolev solution was selected.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]

open Homogenization.PotentialZeroTraceHilbert

/-! ## Dirichlet solution operator -/

/-- Riesz representative in the zero-trace potential subspace of an ambient
`L²` forcing class. -/
def oneStepDirichletForcingRieszOfClass (M : PotentialSolenoidalL2Data U)
    (G : HilbertVectorL2 U) : Space M :=
  forcingRieszMap M ((InnerProductSpace.toDual ℝ (HilbertVectorL2 U) G).comp
    ((submodule (M := M)).subtypeL))

/-- Gradient class of the zero-Dirichlet Lax--Milgram solution. -/
def oneStepDirichletGradientOfForcingClass {a : CoeffField d} {lam Lam : ℝ}
    (M : PotentialSolenoidalL2Data U) (hne : Set.Nonempty U)
    (hEll : IsEllipticFieldOn lam Lam U a) (G : HilbertVectorL2 U) :
    HilbertVectorL2 U :=
  field ((isCoercive_coeffBilin (M := M) hne hEll).continuousLinearEquivOfBilin.symm
    (oneStepDirichletForcingRieszOfClass M G))

omit [IsFiniteMeasure (volumeMeasureOn U)] in
/-- The Dirichlet gradient solution operator is continuous. -/
theorem continuous_oneStepDirichletGradientOfForcingClass
    {a : CoeffField d} {lam Lam : ℝ}
    (M : PotentialSolenoidalL2Data U) (hne : Set.Nonempty U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    Continuous (oneStepDirichletGradientOfForcingClass M hne hEll) := by
  have hrestrict : Continuous fun l : HilbertVectorL2 U →L[ℝ] ℝ =>
      l.comp ((submodule (M := M)).subtypeL) :=
    ((ContinuousLinearMap.compL ℝ (Space M) (HilbertVectorL2 U) ℝ).flip
      ((submodule (M := M)).subtypeL)).continuous
  exact continuous_subtype_val.comp
    ((((isCoercive_coeffBilin (M := M) hne
        hEll).continuousLinearEquivOfBilin.symm).continuous).comp
      (((InnerProductSpace.toDual ℝ (Space M)).symm.continuous).comp
        (hrestrict.comp (InnerProductSpace.toDual ℝ (HilbertVectorL2 U)).continuous)))

omit [IsFiniteMeasure (volumeMeasureOn U)] in
/-- Every zero-trace weak solution has the gradient class returned by the
continuous solution operator. -/
theorem gradToHilbertVectorL2_eq_oneStepDirichletGradientOfForcingClass
    {a : CoeffField d} {lam Lam : ℝ} {g : Vec d → Vec d} {u : H10Function U}
    (hg : MemVectorL2 U g)
    (hRealize : PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U)
    (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a)
    (hu : IsZeroTraceDirichletRhsWeakSolution a U u g) :
    u.toH1Function.gradToHilbertVectorL2 =
      oneStepDirichletGradientOfForcingClass
        (PotentialSolenoidalL2Data.ofSubmoduleClosures U) hne hEll
        (toHilbertVectorL2OfVecField hg) := by
  set M : PotentialSolenoidalL2Data U :=
    PotentialSolenoidalL2Data.ofSubmoduleClosures U with hM
  set zu : Space M := ofH10Function M u with hzu
  have key : ∀ w : Space M,
      inner ℝ (forcingRieszRep M hg) w = coeffBilin (M := M) hEll zu w := by
    intro w
    obtain ⟨phi, hphi⟩ :=
      PotentialSolenoidalL2Data.isPotentialZeroTraceOn_of_mem_potentialZeroTrace_ofSubmoduleClosures
        (U := U) hRealize (vectorField w)
        (by simpa [hM] using mem_potentialZeroTrace w)
    rw [inner_forcingRieszRep_apply, forcingFunctionalCLM_apply_eq_integral,
      coeffBilin_apply_eq_integral]
    have hzfield : vectorField zu = u.toH1Function.gradToVectorL2 := by
      rw [hzu]
      exact vectorField_ofH10Function M u
    have hrhs :
        ∫ x in U, vecDot (matVecMul (a x) (vectorField zu x)) (vectorField w x)
            ∂volume =
          ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x))
            (phi.toH1Function.grad x) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards [H1Function.coeFn_gradToVectorL2 u.toH1Function] with x hx
      rw [hphi, hzfield, hx]
    have hlhs :
        ∫ x in U, vecDot (g x) (vectorField w x) ∂volume =
          ∫ x in U, vecDot (g x) (phi.toH1Function.grad x) ∂volume := by
      rw [hphi]
    rw [hlhs, hrhs, hu phi]
  have heq : forcingRieszRep M hg =
      (isCoercive_coeffBilin (M := M) hne hEll).continuousLinearEquivOfBilin zu :=
    IsCoercive.unique_continuousLinearEquivOfBilin _ key
  have hz : zu =
      (isCoercive_coeffBilin (M := M) hne hEll).continuousLinearEquivOfBilin.symm
        (forcingRieszRep M hg) := by
    rw [heq, ContinuousLinearEquiv.symm_apply_apply]
  calc
    u.toH1Function.gradToHilbertVectorL2 = field zu := rfl
    _ = oneStepDirichletGradientOfForcingClass M hne hEll
        (toHilbertVectorL2OfVecField hg) := by
      rw [oneStepDirichletGradientOfForcingClass, hz]
      rfl

/-! ## Neumann solution operator -/

/-- Riesz representative in the coercive mean-zero `H¹` graph space of an
ambient `L²` forcing class. -/
def oneStepNeumannForcingRieszOfClass (G : HilbertVectorL2 U) :
    H1CoerciveHilbertSpace (U := U) :=
  H1CoerciveHilbert.forcingRieszMap (U := U)
    ((InnerProductSpace.toDual ℝ (HilbertVectorL2 U) G).comp
      (H1CoerciveHilbert.gradientCLM (U := U)))

/-- Gradient class of the mean-zero Neumann Lax--Milgram solution. -/
def oneStepNeumannGradientOfForcingClass {a : CoeffField d} {lam Lam : ℝ}
    (hC : H1CoerciveEstimate U) (hne : Set.Nonempty U)
    (hEll : IsEllipticFieldOn lam Lam U a) (G : HilbertVectorL2 U) :
    HilbertVectorL2 U :=
  H1CoerciveHilbert.gradient (U := U)
    ((H1CoerciveHilbert.isCoercive_coeffGradientBilin (U := U)
      (a := a) (lam := lam) (Lam := Lam) hC hne hEll).continuousLinearEquivOfBilin.symm
      (oneStepNeumannForcingRieszOfClass G))

/-- The Neumann gradient solution operator is continuous. -/
theorem continuous_oneStepNeumannGradientOfForcingClass
    {a : CoeffField d} {lam Lam : ℝ}
    (hC : H1CoerciveEstimate U) (hne : Set.Nonempty U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    Continuous (oneStepNeumannGradientOfForcingClass hC hne hEll) := by
  have hrestrict : Continuous fun l : HilbertVectorL2 U →L[ℝ] ℝ =>
      l.comp (H1CoerciveHilbert.gradientCLM (U := U)) :=
    ((ContinuousLinearMap.compL ℝ (H1CoerciveHilbertSpace (U := U))
      (HilbertVectorL2 U) ℝ).flip
        (H1CoerciveHilbert.gradientCLM (U := U))).continuous
  exact (H1CoerciveHilbert.gradientCLM (U := U)).continuous.comp
    ((((H1CoerciveHilbert.isCoercive_coeffGradientBilin (U := U)
        (a := a) (lam := lam) (Lam := Lam) hC hne
        hEll).continuousLinearEquivOfBilin.symm).continuous).comp
      (((InnerProductSpace.toDual ℝ (H1CoerciveHilbertSpace (U := U))).symm.continuous).comp
        (hrestrict.comp (InnerProductSpace.toDual ℝ (HilbertVectorL2 U)).continuous)))

/-- Every mean-zero Neumann weak solution has the gradient class returned by
the continuous solution operator. -/
theorem gradToHilbertVectorL2_eq_oneStepNeumannGradientOfForcingClass
    {a : CoeffField d} {lam Lam : ℝ} {g : Vec d → Vec d}
    {u : H1MeanZeroFunction U}
    (hg : MemVectorL2 U g) (hC : H1CoerciveEstimate U)
    (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a)
    (hu : IsMeanZeroNeumannRhsWeakSolution a U u g) :
    u.gradToHilbertVectorL2 =
      oneStepNeumannGradientOfForcingClass hC hne hEll
        (toHilbertVectorL2OfVecField hg) := by
  have hvec :=
    gradToVectorL2_eq_coeffGradientProblemSolution_of_h1CoerciveEstimate
      (U := U) (a := a) (lam := lam) (Lam := Lam) hg hC hne hu hEll
  have hbridge : ∀ v : H1MeanZeroFunction U,
      v.gradToHilbertVectorL2 =
        vectorL2ToHilbertVectorL2 (U := U) v.gradToVectorL2 := fun v =>
    (vectorL2ToHilbertVectorL2_toVectorL2
      (U := U) v.toH1Function.grad_memVectorL2).symm
  rw [hbridge u, hvec, ← hbridge]
  show (H1CoerciveHilbert.toH1MeanZeroFunction
      (H1CoerciveHilbert.coeffGradientProblemSolution
        (U := U) (a := a) (lam := lam) (Lam := Lam)
        hg hC hne hEll)).gradToHilbertVectorL2 = _
  rw [H1CoerciveHilbert.toH1MeanZeroFunction_gradToHilbertVectorL2]
  rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
