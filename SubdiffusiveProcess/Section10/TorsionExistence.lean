module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalGreenContinuity
public import SubdiffusiveProcess.Assumptions.CoefficientRegularity

@[expose] public section

/-! Actual native zero-trace torsion from the existing variational solver. -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
namespace SubdiffusiveProcess.Section10

/-- The actual unit-forcing weak equation, with original coefficients. -/
def IsWeakTorsion {d : ℕ} (A b : Vec d → ℝ) (U : Set (Vec d))
    (u : H10Function U) : Prop :=
  IsMassiveWeakSolutionOn A b 0 U u.toH1Function (fun _ => 1)

/-- Native H10 torsion exists under the existing local coefficient bounds. -/
theorem exists_weakTorsion {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {A b : Vec d → ℝ} (hA : CoefficientOn U A) (hb : CoefficientOn U b) :
    ∃ u : H10Function U, IsWeakTorsion A b U u := by
  letI : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  letI := variational_weighted_isFiniteMeasure hU.isOpen.measurableSet hb
  exact exists_interior_variational_green hU hne hA hb (memLp_const (1 : ℝ))

/-- The chosen native torsion uses genuine variational existence. -/
def weakTorsion {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {A b : Vec d → ℝ} (hA : CoefficientOn U A) (hb : CoefficientOn U b) : H10Function U :=
  Classical.choose (exists_weakTorsion hU hne hA hb)

lemma weakTorsion_spec {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {A b : Vec d → ℝ} (hA : CoefficientOn U A) (hb : CoefficientOn U b) :
    IsWeakTorsion A b U (weakTorsion hU hne hA hb) :=
  Classical.choose_spec (exists_weakTorsion hU hne hA hb)

/-- Positive continuous coefficients discharge all qualitative solver inputs. -/
theorem exists_weakTorsion_of_continuous_pos {d : ℕ} [NeZero d]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {A b : Vec d → ℝ} (hA : Continuous A) (hApos : ∀ x, 0 < A x)
    (hb : Continuous b) (hbpos : ∀ x, 0 < b x) :
    ∃ u : H10Function U, IsWeakTorsion A b U u :=
  exists_weakTorsion hU hne
    (SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos
      hA hApos hU.isBoundedDomain.isBounded)
    (SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos
      hb hbpos hU.isBoundedDomain.isBounded)



end SubdiffusiveProcess.Section10
