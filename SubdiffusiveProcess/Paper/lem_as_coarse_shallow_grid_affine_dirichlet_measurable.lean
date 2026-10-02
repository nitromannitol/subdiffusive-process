import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_matched_affine_moment
import Mathlib.Tactic

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

def aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_global_log_potential {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (om : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  ContinuousMap.const _ (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) -
    ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
    ∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat i))

def aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_root_log_potential {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (om : BilateralField d) : C(closedCube (0 : SpatialCoordinates d) 1 (by norm_num), ℝ) :=
  (aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_global_log_potential M N om).restrict
      (closedCube (0 : SpatialCoordinates d) 1 (by norm_num) :
        Set (SpatialCoordinates d))

theorem aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_global_log_potential_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Measurable (aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_global_log_potential M N) := by
  exact measurable_const.add
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply (-(Int.ofNat i)))

theorem aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_root_log_potential_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (om : BilateralField d) :
    continuousPositiveLog
      (SubdiffusiveProcess.Lane4.cutoffCoefficientCM M
        (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
        (0 : SpatialCoordinates d) (by norm_num))
      (SubdiffusiveProcess.Lane4.cutoffCoefficientCM_pos M
        (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
        (0 : SpatialCoordinates d) (by norm_num)) =
      aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_root_log_potential M N om := by
  ext x
  simp only [continuousPositiveLog, aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_root_log_potential,
    aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_global_log_potential,
    SubdiffusiveProcess.Lane4.cutoffCoefficientCM,
    ContinuousMap.coe_mk, ContinuousMap.restrict_apply,
    ContinuousMap.add_apply, ContinuousMap.const_apply, ContinuousMap.sum_apply]
  rw [cutoffCoefficient, Real.log_mul
    (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne')
    (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
  simp only [cutoffPotential, Pi.zero_apply, zero_add]
  dsimp [ContinuousMap.restrict]
  simp only [ContinuousMap.add_apply, ContinuousMap.const_apply,
    ContinuousMap.sum_apply]
  ring

def aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_exp_coeff {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (om : BilateralField d) :
    PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)) := by
  let Om := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let K := closedCube (0 : SpatialCoordinates d) 1 (by norm_num)
  haveI : Fact ((Om : Set (SpatialCoordinates d)) ⊆ K) :=
    ⟨centeredCube_subset_closedCube (0 : SpatialCoordinates d) (by norm_num)⟩
  exact expPotentialCoefficient (compactPotentialToLp K
    (aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_root_log_potential M N om))

theorem aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_coeff_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (om : BilateralField d) :
    SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M
      (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
      (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1) =
    aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_exp_coeff M N om := by
  let Om := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let K := closedCube (0 : SpatialCoordinates d) 1 (by norm_num)
  haveI : Fact ((Om : Set (SpatialCoordinates d)) ⊆ K) :=
    ⟨centeredCube_subset_closedCube (0 : SpatialCoordinates d) (by norm_num)⟩
  unfold SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient
    normalizedContinuousPositiveCoefficient aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_exp_coeff
  rw [aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_root_log_potential_eq]
  simp only [Real.log_one, ContinuousMap.const_zero, sub_zero]

def aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_response {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (e : Homogenization.Vec d) (om : BilateralField d) : ℝ :=
  affineDirichletResponse
    (centeredCube_isBounded (0 : SpatialCoordinates d)
      (by norm_num : (0 : ℝ) < 1))
    (aux_matched_root_poincare (d := d)).1
    (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M
      (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
      (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1)) e

theorem lem_as_coarse_shallow_grid_affine_dirichlet_measurable {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (e : Homogenization.Vec d) :
    Measurable (fun om => affineDirichletResponse
      (centeredCube_isBounded (0 : SpatialCoordinates d)
        (by norm_num : (0 : ℝ) < 1))
      (aux_matched_root_poincare (d := d)).1
      (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M
        (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
        (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1)) e) := by
  change Measurable (aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_response M N e)
  let Om := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let K := closedCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let hP := aux_matched_root_poincare (d := d)
  haveI : Fact ((Om : Set (SpatialCoordinates d)) ⊆ K) :=
    ⟨centeredCube_subset_closedCube (0 : SpatialCoordinates d) (by norm_num)⟩
  have hlog : Measurable (aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_global_log_potential M N) :=
    aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_global_log_potential_measurable M N
  have hD := ((continuous_dirichletResponse_compact
    (killedResponseSpace hP.1) K
      (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d)
        (by norm_num : (0 : ℝ) < 1)) e 0)).comp
    (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d)))).measurable.comp hlog
  convert hD using 1
  funext om
  dsimp only [aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_response]
  rw [aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_coeff_eq M N om]
  rfl

end Paper

