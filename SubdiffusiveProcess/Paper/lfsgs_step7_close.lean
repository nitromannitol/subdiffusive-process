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
public import SubdiffusiveProcess.FiniteStopping.HolderInterpolation
public import SubdiffusiveProcess.FiniteStopping.TraceRescaling
public import SubdiffusiveProcess.Paper.lfsgs_normalized_Aext_seminorm

@[expose] public section

/-! This module establishes step7 close for finite stopping; it does not assert the full stopping theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.Paper

variable {d : ℕ}

/-- step7 close in the finite stopping construction. -/
theorem lfsgs_step7_close
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (alpha beta : ℝ) (_hbeta : 1 / 2 < beta) (hba : beta < alpha) (_halpha : alpha < 1)
    (Aext eta : ℝ) (_hAext : 0 ≤ Aext) (_heta : 0 < eta)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (sN sM : ℝ) (hsN : 0 < sN) (hsM : 0 < sM)
    (aN aM : PositiveCoefficient (centeredCube z r hr))
    (aUN aUM : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (hPN : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (hPM : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (qN qM : Seminorm ℝ (SpatialCoordinates d → ℝ))
    (hscaleN : ∀ g : SpatialCoordinates d → ℝ,
      sInf (aux_lem_local_normalizations_Lset z r hr aN g) =
        r ^ ((d : ℝ) - 2) * sN *
          sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUN (g ∘ cubeDilation z 0 r)))
    (hscaleM : ∀ g : SpatialCoordinates d → ℝ,
      sInf (aux_lem_local_normalizations_Lset z r hr aM g) =
        r ^ ((d : ℝ) - 2) * sM *
          sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUM (g ∘ cubeDilation z 0 r)))
    (hqN1 : ∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
      (qN g) ^ 2 = sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUN g))
    (hqM1 : ∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
      (qM g) ^ 2 = sInf (aux_lem_local_normalizations_Lset 0 1 one_pos aUM g))
    (hR : ∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
      (qN g) ^ 2 ≤ Aext * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2 ∧
      (qM g) ^ 2 ≤ Aext * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2)
    (Hs : Finset (SpatialCoordinates d → ℝ))
    (hmain : ∀ (qN qM : Seminorm ℝ (SpatialCoordinates d → ℝ)),
      (∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
        (qN g) ^ 2 ≤ Aext * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2 ∧
        (qM g) ^ 2 ≤ Aext * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2) →
      (∀ h ∈ Hs, |(qN h) ^ 2 - (qM h) ^ 2| ≤ eta / 2) →
      ∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass alpha 0 1 g →
        |(qN g) ^ 2 - (qM g) ^ 2| ≤
          eta * (cellBoundaryQuotientNorm alpha 0 1 g) ^ 2)
    (htest : ∀ h ∈ Hs, |(qN h) ^ 2 - (qM h) ^ 2| ≤ eta / 2) :
    ∀ (u : weakSobolevGraph (centeredCube z r hr)) (G : SpatialCoordinates d → ℝ),
      ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
      IsCellBoundaryClass alpha z r G →
      ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
      |dirichletResponse (killedResponseSpace hPN) aN u / (r ^ ((d : ℝ) - 2) * sN) -
        dirichletResponse (killedResponseSpace hPM) aM u / (r ^ ((d : ℝ) - 2) * sM)| ≤
        eta * (cellBoundaryQuotientNorm alpha z r G) ^ 2 := by
  intro u G hGc hGalpha hGrep
  set g' : SpatialCoordinates d → ℝ := G ∘ cubeDilation z 0 r with hg'def
  have hcd_eq : rescaledDatum z r G = G ∘ cubeDilation z 0 r := by
    funext y
    congr 1
    funext i
    simp only [Pi.zero_apply, sub_zero]
  have hGalphaClass : IsCellBoundaryClass alpha 0 1 g' := by
    rw [hg'def, ← hcd_eq]
    exact (SubdiffusiveProcess.FiniteStopping.IsCellBoundaryClass_rescale alpha z r G).mp hGalpha
  have hGbetaClass : IsCellBoundaryClass beta 0 1 g' := by
    refine ⟨?_, ?_⟩
    · have h1 := hGalphaClass.1
      rw [SubdiffusiveProcess.FiniteStopping.rescaledDatum_unit] at h1 ⊢
      exact SubdiffusiveProcess.FiniteStopping.isHolderOn_beta_of_alpha hba.le g' h1
    · have h2 := hGalphaClass.2
      rw [SubdiffusiveProcess.FiniteStopping.rescaledDatum_unit] at h2 ⊢
      assumption
  have hrespN : dirichletResponse (killedResponseSpace hPN) aN u =
      r ^ ((d : ℝ) - 2) * sN * (qN g') ^ 2 := by
    have heq : dirichletResponse (killedResponseSpace hPN) aN u =
        sInf (aux_lem_local_normalizations_Lset z r hr aN G) :=
      _root_.SubdiffusiveProcess.Paper.aux_lfsgs_normalized_Aext_seminorm_dirichletResponse_eq_sInf hd z r hr hPN aN u G G hGc hGrep (fun x _ => rfl)
    rw [heq, hscaleN G, ← hg'def, hqN1 g' hGbetaClass]
  have hrespM : dirichletResponse (killedResponseSpace hPM) aM u =
      r ^ ((d : ℝ) - 2) * sM * (qM g') ^ 2 := by
    have heq : dirichletResponse (killedResponseSpace hPM) aM u =
        sInf (aux_lem_local_normalizations_Lset z r hr aM G) :=
      _root_.SubdiffusiveProcess.Paper.aux_lfsgs_normalized_Aext_seminorm_dirichletResponse_eq_sInf hd z r hr hPM aM u G G hGc hGrep (fun x _ => rfl)
    rw [heq, hscaleM G, ← hg'def, hqM1 g' hGbetaClass]
  have hposN : (0 : ℝ) < r ^ ((d : ℝ) - 2) * sN := by positivity
  have hposM : (0 : ℝ) < r ^ ((d : ℝ) - 2) * sM := by positivity
  have hdivN : dirichletResponse (killedResponseSpace hPN) aN u / (r ^ ((d : ℝ) - 2) * sN) =
      (qN g') ^ 2 := by
    rw [hrespN]; field_simp
  have hdivM : dirichletResponse (killedResponseSpace hPM) aM u / (r ^ ((d : ℝ) - 2) * sM) =
      (qM g') ^ 2 := by
    rw [hrespM]; field_simp
  have hquot : cellBoundaryQuotientNorm alpha z r G = cellBoundaryQuotientNorm alpha 0 1 g' := by
    rw [hg'def, ← hcd_eq]
    exact SubdiffusiveProcess.FiniteStopping.cellBoundaryQuotientNorm_rescale alpha z r G
  rw [hdivN, hdivM, hquot]
  exact hmain qN qM hR htest g' hGalphaClass

end SubdiffusiveProcess.Paper
