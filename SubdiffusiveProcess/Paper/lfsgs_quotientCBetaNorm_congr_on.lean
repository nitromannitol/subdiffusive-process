import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Geometry.OddGrid
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Lane4.Inputs
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
import SubdiffusiveProcess.Assumptions.Actions
import SubdiffusiveProcess.Main.LayerScaling
import Mathlib.Tactic
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.cutoff_good_scale_input
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.sum_errors_baseline_input
import SubdiffusiveProcess.Paper.primitive_scores
import SubdiffusiveProcess.Paper.cell_catalogue
import SubdiffusiveProcess.Paper.good_event
import SubdiffusiveProcess.Paper.lem_finite_good_cell
import SubdiffusiveProcess.Paper.finite_interval_packing
import SubdiffusiveProcess.Paper.paper_responses_bank
import SubdiffusiveProcess.Paper.finite_response_ramp
import SubdiffusiveProcess.Paper.lem_rare_tests
import SubdiffusiveProcess.Paper.lem_finite_trace_tests
import SubdiffusiveProcess.Paper.lem_local_normalizations
import SubdiffusiveProcess.Paper.inputs_EM_witness
import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Paper.rem_bank
import SubdiffusiveProcess.Paper.prop_16
import SubdiffusiveProcess.Paper.lfsgs_trace_moments
import SubdiffusiveProcess.Paper.aux_test_prop16_rd_band
import SubdiffusiveProcess.Paper.classical_cube_fractional_interpolation
import SubdiffusiveProcess.Paper.classical_cube_fractional_compact_embedding

/-! This module establishes quotientCBetaNorm congr on for finite stopping; it does not assert the full stopping theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace Paper

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
    exact ⟨c, Paper.aux_lfsgs_quotientCBetaNorm_congr_on_cAlphaNorm_congr_on beta S (fun x => f x - c) (fun x => g x - c)
      (fun x hx => by show f x - c = g x - c; rw [hfg x hx])⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, (Paper.aux_lfsgs_quotientCBetaNorm_congr_on_cAlphaNorm_congr_on beta S (fun x => f x - c) (fun x => g x - c)
      (fun x hx => by show f x - c = g x - c; rw [hfg x hx])).symm⟩

end Paper
