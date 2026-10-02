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
import SubdiffusiveProcess.FiniteStopping.ResponseNormalization

/-! This module establishes response bank for finite stopping; it does not assert the full stopping theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace Paper

variable {d : ℕ}

/-- response bank in the finite stopping construction. -/
theorem lfsgs_response_bank {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ Cresp : ℝ, 0 < Cresp ∧
      ∀ model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, ∃ Rm : in_responses d model, Rm.C = Cresp := by
  classical
  obtain ⟨C0, hC0, hall⟩ := paper_responses_bank d hd
  refine ⟨C0, hC0, fun model => ?_⟩
  obtain ⟨hord, hle1, hlow⟩ := SubdiffusiveProcess.FiniteStopping.ahom_inputs model
  set defect : ℕ → SpatialCoordinates d → BilateralField d → ℝ :=
    fun m y om => (aux_rbpf_defect_exists model m y om).choose with hdefect_def
  have hdnn : ∀ m y om, 0 ≤ defect m y om :=
    fun m y om => (aux_rbpf_defect_exists model m y om).choose_spec.1
  have hdgr := fun m y om => (aux_rbpf_defect_exists model m y om).choose_spec.2
  obtain ⟨Rm, hRmC, -, -⟩ := hall model hord hle1 hlow defect hdnn hdgr
  exact ⟨Rm, hRmC⟩

end Paper
