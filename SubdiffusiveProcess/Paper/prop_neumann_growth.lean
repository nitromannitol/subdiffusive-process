module

public import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CubeNegativeL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Section6.Defs.HolderRegularityConclusions
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.rem_resolved
public import SubdiffusiveProcess.Paper.smoothed_neumann_source_scaling
public import SubdiffusiveProcess.Paper.aux_prop_neumann_growth_solution_bridge
public import SubdiffusiveProcess.Paper.prop_neumann_growth_assembly
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_even
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.lem_neumann_error
public import SubdiffusiveProcess.Paper.prop_folded_iteration
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.rem_repair
public import SubdiffusiveProcess.Paper.rem_resolved_strata
public import SubdiffusiveProcess.Paper.rem_resolved_meshes
public import SubdiffusiveProcess.Paper.rem_resolved_microscopic
public import SubdiffusiveProcess.Paper.rem_resolved_eps_power
public import SubdiffusiveProcess.Paper.lem_infrared

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper

/-- Proposition (paper label `eq:mfd-13`). The disorder is not a free `∀ (om : BilateralField d)` but the almost-sure common-field event `∀ᵐ om ∂(chaosSampleLaw M).toMeasure`.  The existential `K` and `Cbound` stay BEFORE that event, and every cutoff `N`, every `eps`, every source, every center `x` and every radius `rad` is quantified INSIDE the same event; the moment bank and the threshold order are unchanged and no hypothesis was added.

- original common field/infrared characterization from lem_infrared
- moment inputs in_responses/in_poincare/in_extension
- carried published Meyers--Morrey small-perturbation input `_W`, supplied at paper label `eq:mfd-13`  and consumed in the below-wavelength step through `rem_resolved_microscopic`
- full folded, two-mesh, microscopic, load argument from existing deps
- uniform eps^-2 and all radii
- a.e. restriction agrees with InfraredCharacterization
- finite list fixes disorder: `ps : Fin k → ℝ` is fixed before the disorder
- oneK for all moments: ONE `K` serves all listed moment orders
- carried deterministic one-step input `D` (part (v) of the deterministic iteration input), consumed by `prop_folded_iteration` and `rem_resolved`
- `D` is a carried supplier input, not an additional conclusion or a weakened target
- the Lean assembly uses the sufficient `eps^-2` global energy bound
  from the carried mean-zero Poincare inequality and cutoff eigenvalue moments;
  `rem_resolved` then gives the exact stated local bound
- the source's stronger epsilon-uniform route remains recorded in
  `smoothed_neumann_source_scaling` and `aux_prop_neumann_growth_solution_bridge`
-/
theorem prop_neumann_growth :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (t : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
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

end SubdiffusiveProcess.Paper
