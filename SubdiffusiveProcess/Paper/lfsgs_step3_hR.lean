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
import SubdiffusiveProcess.Paper.lfsgs_normalized_Aext_seminorm

/-! This module establishes step3 hR for finite stopping; it does not assert the full stopping theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace Paper

variable {d : ℕ}

/-- step3 hR in the finite stopping construction. -/
theorem lfsgs_step3_hR
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Sf : SobolevFoundationalInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (aN aM : PositiveCoefficient (centeredCube z r hr))
    (aUN aUM : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (sN sM Aext : ℝ) (hsN : 0 < sN) (hsM : 0 < sM) (hAext : 0 < Aext)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hscaleN : ∀ g : SpatialCoordinates d → ℝ,
      sInf (aux_lem_local_normalizations_Lset z r hr aN g) =
        r ^ ((d : ℝ) - 2) * sN *
          sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUN (g ∘ cubeDilation z 0 r)))
    (hscaleM : ∀ g : SpatialCoordinates d → ℝ,
      sInf (aux_lem_local_normalizations_Lset z r hr aM g) =
        r ^ ((d : ℝ) - 2) * sM *
          sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUM (g ∘ cubeDilation z 0 r)))
    (hPN : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (hPM : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (hClauseAextN : ∀ (b : weakSobolevGraph (centeredCube z r hr))
        (G : SpatialCoordinates d → ℝ),
      ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
      IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
      ∀ c : ℝ, dirichletResponse (killedResponseSpace hPN) aN b ≤
        Aext * r ^ ((d : ℝ) - 2) * sN *
          (cAlphaNorm beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
            Set (SpatialCoordinates d))) (fun x => G (z + r • x) - c)) ^ 2)
    (hClauseAextM : ∀ (b : weakSobolevGraph (centeredCube z r hr))
        (G : SpatialCoordinates d → ℝ),
      ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
      IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
      ∀ c : ℝ, dirichletResponse (killedResponseSpace hPM) aM b ≤
        Aext * r ^ ((d : ℝ) - 2) * sM *
          (cAlphaNorm beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
            Set (SpatialCoordinates d))) (fun x => G (z + r • x) - c)) ^ 2) :
    ∃ qN qM : Seminorm ℝ (SpatialCoordinates d → ℝ),
      (∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
        (qN g) ^ 2 = sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUN g)) ∧
      (∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
        (qM g) ^ 2 = sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUM g)) ∧
      (∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
        (qN g) ^ 2 ≤ Aext * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2 ∧
        (qM g) ^ 2 ≤ Aext * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2) := by
  obtain ⟨qN, hqN1, hqN2⟩ := Paper.lfsgs_normalized_Aext_seminorm hd Sf z r hr aN aUN sN Aext hsN hAext
    beta hbeta hscaleN hPN hClauseAextN
  obtain ⟨qM, hqM1, hqM2⟩ := Paper.lfsgs_normalized_Aext_seminorm hd Sf z r hr aM aUM sM Aext hsM hAext
    beta hbeta hscaleM hPM hClauseAextM
  exact ⟨qN, qM, hqN1, hqM1, fun g hg => ⟨hqN2 g hg, hqM2 g hg⟩⟩

end Paper
