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
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
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
public import SubdiffusiveProcess.FiniteStopping.BoundaryTraceComparison

@[expose] public section

/-! This module establishes sub mem killed of boundary eq for finite stopping; it does not assert the full stopping theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.Paper

variable {d : ℕ}

/-- unit Λ in the finite stopping construction. -/
def aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ
    {d : ℕ} (alpha : ℝ)
    (a : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) :
    aux_lem_local_normalizations_classW alpha (0 : SpatialCoordinates d) 1 → ℝ :=
  fun v => sInf (aux_lem_local_normalizations_Lset (0 : SpatialCoordinates d) 1 one_pos a v.val)

/-- unit Λ nonneg in the finite stopping construction. -/
theorem aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ_nonneg
    {d : ℕ} (alpha : ℝ)
    (a : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (v : aux_lem_local_normalizations_classW alpha (0 : SpatialCoordinates d) 1) :
    0 ≤ _root_.SubdiffusiveProcess.Paper.aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ alpha a v :=
  aux_lem_local_normalizations_sInf_nonneg 0 1 one_pos a v.val

/-- unit Λ smul in the finite stopping construction. -/
theorem aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ_smul
    {d : ℕ} (alpha : ℝ)
    (a : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) (c : ℝ)
    (v : aux_lem_local_normalizations_classW alpha (0 : SpatialCoordinates d) 1) :
    _root_.SubdiffusiveProcess.Paper.aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ alpha a (c • v) =
      c ^ 2 * _root_.SubdiffusiveProcess.Paper.aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ alpha a v := by
  show sInf (aux_lem_local_normalizations_Lset 0 1 one_pos a (c • v).val) =
    c ^ 2 * sInf (aux_lem_local_normalizations_Lset 0 1 one_pos a v.val)
  rw [Submodule.coe_smul]
  exact aux_lem_local_normalizations_sInf_smul 0 1 one_pos a v.val c

/-- unit Λ tri in the finite stopping construction. -/
theorem aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ_tri
    {d : ℕ} (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (alpha : ℝ) (halpha : alpha ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (a : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (v w : aux_lem_local_normalizations_classW alpha (0 : SpatialCoordinates d) 1) :
    Real.sqrt (_root_.SubdiffusiveProcess.Paper.aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ alpha a (v + w)) ≤
      Real.sqrt (_root_.SubdiffusiveProcess.Paper.aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ alpha a v) +
        Real.sqrt (_root_.SubdiffusiveProcess.Paper.aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ alpha a w) := by
  have hHolder : ∀ u : aux_lem_local_normalizations_classW alpha (0 : SpatialCoordinates d) 1,
      IsHolderOn alpha (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))) u.val := by
    intro u
    have h := u.property.1
    rwa [aux_lem_local_normalizations_rescaled_unit] at h
  have hne : ∀ u : aux_lem_local_normalizations_classW alpha (0 : SpatialCoordinates d) 1,
      (aux_lem_local_normalizations_Lset
        (0 : SpatialCoordinates d) 1 one_pos a u.val).Nonempty := by
    intro u
    obtain ⟨b, U, -, -, -, hmem⟩ := aux_lem_local_normalizations_Lset_nonempty
      (hd := hd) Sf alpha halpha a u.val (hHolder u)
    exact ⟨_, hmem⟩
  show Real.sqrt (sInf (aux_lem_local_normalizations_Lset 0 1 one_pos a (v + w).val)) ≤ _
  rw [Submodule.coe_add]
  exact aux_lem_local_normalizations_sInf_tri 0 1 one_pos a v.val w.val (hne v) (hne w)

/-- unit seminorm in the finite stopping construction. -/
theorem aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_seminorm
    {d : ℕ} (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (alpha : ℝ) (halpha : alpha ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (a : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) :
    ∃ q : Seminorm ℝ (SpatialCoordinates d → ℝ),
      ∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass alpha 0 1 g →
        (q g) ^ 2 = sInf (aux_lem_local_normalizations_Lset
          (0 : SpatialCoordinates d) 1 one_pos a g) := by
  have hex : ∃ p : Seminorm ℝ (aux_lem_local_normalizations_classW alpha
      (0 : SpatialCoordinates d) 1), ∀ v, p v = Real.sqrt (
        _root_.SubdiffusiveProcess.Paper.aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ alpha a v) := by
    refine @SubdiffusiveProcess.FiniteStopping.seminorm_of_sqrt
      (aux_lem_local_normalizations_classW alpha (0 : SpatialCoordinates d) 1) _ _
      (_root_.SubdiffusiveProcess.Paper.aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ alpha a) ?_ ?_ ?_
    · exact _root_.SubdiffusiveProcess.Paper.aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ_nonneg alpha a
    · exact _root_.SubdiffusiveProcess.Paper.aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ_smul alpha a
    · exact _root_.SubdiffusiveProcess.Paper.aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ_tri hd Sf alpha halpha a
  obtain ⟨p, hp⟩ := hex
  obtain ⟨q, hq⟩ := SubdiffusiveProcess.FiniteStopping.seminorm_extend _ p
  refine ⟨q, fun g hg => ?_⟩
  have hgV : g ∈ aux_lem_local_normalizations_classW alpha (0 : SpatialCoordinates d) 1 := hg
  have hqg := hq (⟨g, hgV⟩ : aux_lem_local_normalizations_classW alpha
    (0 : SpatialCoordinates d) 1)
  rw [hqg, hp]
  exact Real.sq_sqrt (_root_.SubdiffusiveProcess.Paper.aux_lfsgs_sub_mem_killed_of_boundary_eq_unit_Λ_nonneg alpha a ⟨g, hgV⟩)

/-- aux submemkilled of continuous boundary zero in the finite stopping construction. -/
theorem aux_lfsgs_sub_mem_killed_of_boundary_eq_aux_submemkilled_of_continuous_boundary_zero
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr))
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)))
    (hrep : ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U)
    (hzero : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0) :
    (u : SobolevData (centeredCube z r hr)) ∈ killedSobolevGraph (centeredCube z r hr) := by
  exact lem_extension_trace_class_transport hd z r hr u U hU hrep hzero

/-- sub mem killed of boundary eq in the finite stopping construction. -/
theorem lfsgs_sub_mem_killed_of_boundary_eq
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u u' : weakSobolevGraph (centeredCube z r hr))
    (U U' : SpatialCoordinates d → ℝ)
    (hUc : ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)))
    (hU'c : ContinuousOn U' (closedCube z r hr : Set (SpatialCoordinates d)))
    (hU : ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U)
    (hU' : ((u' : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U')
    (hbdry : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = U' x) :
    u.val - u'.val ∈ killedSobolevGraph (centeredCube z r hr) := by
  set w : weakSobolevGraph (centeredCube z r hr) := u - u' with hwdef
  have hwval : (w : SobolevData (centeredCube z r hr)) = u.val - u'.val := by
    dsimp [w]
  rw [← hwval]
  have hWcont : ContinuousOn (U - U') (closedCube z r hr : Set (SpatialCoordinates d)) :=
    hUc.sub hU'c
  have hWrep : ((w : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] (U - U') := by
    dsimp [w]
    exact (Lp.coeFn_sub ((u : SobolevData (centeredCube z r hr)).1)
      ((u' : SobolevData (centeredCube z r hr)).1)).trans (hU.sub hU')
  have hWzero : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      (U - U') x = 0 := by
    intro x hx
    simp only [Pi.sub_apply, hbdry x hx, sub_self]
  exact _root_.SubdiffusiveProcess.Paper.aux_lfsgs_sub_mem_killed_of_boundary_eq_aux_submemkilled_of_continuous_boundary_zero hd z r hr w (U - U')
    hWcont hWrep hWzero

end SubdiffusiveProcess.Paper
