import SubdiffusiveProcess.Paper.cutoff_lifetime_package
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.Assumptions.CoefficientRegularity

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_local_compact_coefficients
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) :
    ∀ K : Set (SpatialCoordinates d), IsCompact K →
      CoefficientOn K (cutoffCoefficient M H omega N) ∧
        CoefficientOn K (cutoffSpeedDensity M H omega N) := by
  intro K hK
  refine ⟨SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos
    (Lane4.cutoffCoefficient_continuous M H omega N)
    (Lane4.cutoffCoefficient_pos M H omega N) hK.isBounded, ?_⟩
  apply SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos
    (a := cutoffSpeedDensity M H omega N) _ _ hK.isBounded
  · unfold cutoffSpeedDensity cutoffPotential
    exact Real.continuous_exp.comp
      (((H omega).continuous.add
        (continuous_finset_sum _ fun j _ => (omega (-(Int.ofNat j))).continuous)).sub
        continuous_const)
  · intro x
    exact Real.exp_pos _

end Paper

