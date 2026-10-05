module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Main.LayerScaling
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Paper.cell_catalogue
public import SubdiffusiveProcess.Paper.good_event
public import SubdiffusiveProcess.Paper.lem_finite_good_cell
public import SubdiffusiveProcess.Paper.finite_interval_packing
public import SubdiffusiveProcess.Paper.paper_responses_bank
public import SubdiffusiveProcess.Paper.finite_response_ramp
public import SubdiffusiveProcess.Paper.lem_rare_tests
public import SubdiffusiveProcess.Paper.lem_finite_trace_tests
public import SubdiffusiveProcess.Paper.lem_local_normalizations
public import SubdiffusiveProcess.Paper.inputs_EM_witness
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.rem_bank
public import SubdiffusiveProcess.Paper.prop_16
public import SubdiffusiveProcess.Paper.lfsgs_trace_moments
public import SubdiffusiveProcess.Paper.aux_test_prop16_rd_band
public import SubdiffusiveProcess.Paper.classical_cube_fractional_interpolation
public import SubdiffusiveProcess.Paper.classical_cube_fractional_compact_embedding

@[expose] public section

/-! This module establishes quotientCBetaNorm congr on for finite stopping; it does not assert the full stopping theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.Paper

variable {d : ℕ}

/-- cAlphaNorm congr on in the finite stopping construction. -/
theorem aux_lfsgs_quotientCBetaNorm_congr_on_cAlphaNorm_congr_on {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d))
    (f g : SpatialCoordinates d → ℝ) (hfg : ∀ x ∈ S, f x = g x) :
    cAlphaNorm beta S f = cAlphaNorm beta S g := by
  have h1 : {v : ℝ | ∃ x ∈ S, v = |f x|} = {v : ℝ | ∃ x ∈ S, v = |g x|} := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [hfg x hx]⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, by rw [hfg x hx]⟩
  have h2 : holderSeminorm beta S f = holderSeminorm beta S g := by
    unfold holderSeminorm
    rw [aux_lem_local_normalizations_holderRatio_congr beta S f g hfg]
  unfold cAlphaNorm
  rw [h1, h2]

/-- quotientCBetaNorm congr on in the finite stopping construction. -/
theorem lfsgs_quotientCBetaNorm_congr_on {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d))
    (f g : SpatialCoordinates d → ℝ) (hfg : ∀ x ∈ S, f x = g x) :
    quotientCBetaNorm beta S f = quotientCBetaNorm beta S g := by
  unfold quotientCBetaNorm
  congr 1
  ext v
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, _root_.SubdiffusiveProcess.Paper.aux_lfsgs_quotientCBetaNorm_congr_on_cAlphaNorm_congr_on beta S (fun x => f x - c) (fun x => g x - c)
      (fun x hx => by show f x - c = g x - c; rw [hfg x hx])⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, (_root_.SubdiffusiveProcess.Paper.aux_lfsgs_quotientCBetaNorm_congr_on_cAlphaNorm_congr_on beta S (fun x => f x - c) (fun x => g x - c)
      (fun x hx => by show f x - c = g x - c; rw [hfg x hx])).symm⟩

end SubdiffusiveProcess.Paper
