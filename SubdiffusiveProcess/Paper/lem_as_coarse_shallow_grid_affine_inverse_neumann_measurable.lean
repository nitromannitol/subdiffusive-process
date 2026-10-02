import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_affine_dirichlet_measurable
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_matched_limit_affine_moment

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The finite inverse affine Neumann response is measurable in the actual cutoff field. -/
theorem lem_as_coarse_shallow_grid_affine_inverse_neumann_measurable {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (e : Homogenization.Vec d) :
    Measurable (aux_matched_affine_finite_response M e true N) := by
  let Om := centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let K := closedCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let hP := aux_matched_root_poincare (d := d)
  haveI : Fact ((Om : Set (SpatialCoordinates d)) ⊆ K) :=
    ⟨centeredCube_subset_closedCube (0 : SpatialCoordinates d) (by norm_num)⟩
  have hlog : Measurable
      (aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_global_log_potential M N) :=
    aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_global_log_potential_measurable M N
  have hR := ((continuous_inverseResponse_compact
    (meanZeroResponseSpace hP.2) K
      ((affineNeumannLoad e).comp (subspaceGradient (meanZeroSobolevGraph Om)))).comp
    (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d)))).measurable.comp hlog
  have hEq : aux_matched_affine_finite_response M e true N =
      (fun om => inverseResponse (meanZeroResponseSpace hP.2)
        (expPotentialCoefficient (compactPotentialToLp K
          ((aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_global_log_potential M N om).restrict
            (K : Set (SpatialCoordinates d)))))
        ((affineNeumannLoad e).comp (subspaceGradient (meanZeroSobolevGraph Om)))) := by
    funext om
    change inverseResponse (meanZeroResponseSpace hP.2)
      (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M
        (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
        (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1))
      ((affineNeumannLoad e).comp (subspaceGradient (meanZeroSobolevGraph Om))) = _
    congr 1
    exact aux_lem_as_coarse_shallow_grid_affine_dirichlet_measurable_coeff_eq M N om
  rw [hEq]
  exact hR

end Paper

