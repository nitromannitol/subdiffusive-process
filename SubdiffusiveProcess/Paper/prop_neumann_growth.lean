import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.CubeNegativeL2Norm
import SubdiffusiveProcess.Main.HalfFractionalOrder
import SubdiffusiveProcess.Sobolev.BoundaryEnergy
import SubdiffusiveProcess.Sobolev.FoldDiscounts
import SubdiffusiveProcess.Sobolev.LoadApproximation
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.AffineResponses
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.CoarseGrainingVocab.Core
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.rem_resolved
import SubdiffusiveProcess.Paper.lane4_smoothed_neumann_source_scaling
import SubdiffusiveProcess.Paper.aux_prop_neumann_growth_solution_bridge
import SubdiffusiveProcess.Paper.prop_neumann_growth_assembly
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Paper.lem_coercivity
import SubdiffusiveProcess.Paper.lem_even
import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Paper.lem_neumann_error
import SubdiffusiveProcess.Paper.prop_folded_iteration
import SubdiffusiveProcess.Paper.prop_growth
import SubdiffusiveProcess.Paper.rem_repair
import SubdiffusiveProcess.Paper.rem_resolved_strata
import SubdiffusiveProcess.Paper.rem_resolved_meshes
import SubdiffusiveProcess.Paper.rem_resolved_microscopic
import SubdiffusiveProcess.Paper.rem_resolved_eps_power
import SubdiffusiveProcess.Paper.lem_infrared

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper



theorem prop_neumann_growth :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (t : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
    ∀ (rho : ℝ → ℝ), ContDiff ℝ ∞ rho → (∀ tau, 0 ≤ rho tau) →
      (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) → (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ), (∑ i : Fin d, (pvec i) ^ 2) = 1 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ) (eps : ℝ), 0 < eps → eps < 1 / 8 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
              (faceBump rho pvec eps) v →
          ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ unitNeumannCube d →
            0 < rad → rad ≤ 1 →
            localGradientEnergy
                (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                (s := Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
                (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
              K N om * eps ^ (-2 : ℝ) * rad ^ t := by
  exact prop_neumann_growth_assembly

end Paper
