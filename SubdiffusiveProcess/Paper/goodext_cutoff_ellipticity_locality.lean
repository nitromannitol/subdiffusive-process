import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Paper.lem_extension_cell_moment

/-! This theorem identifies ambient and local cutoff coefficient charts on a contained cell. It
establishes chart locality for the coarse upper and inverse lower coefficients; it does not give
a stochastic moment estimate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace Paper

/-- The ambient and local cutoff charts give the same upper and inverse lower coarse coefficient on a contained cell. -/
theorem goodext_cutoff_ellipticity_locality
    {d : ℕ} [NeZero d] (I : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (xi : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (w : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (hsub : (centeredCube w s hs : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (sigma : ℝ) (hsigma : sigma ∈ Ioc (0 : ℝ) 1) :
    I.Lam z r hr (cutoffPositiveCoefficient M H xi N z hr) w s sigma 2 =
      I.Lam w s hs (cutoffPositiveCoefficient M H xi N w hs) w s sigma 2 ∧
    (I.lam z r hr (cutoffPositiveCoefficient M H xi N z hr) w s sigma 2)⁻¹ =
      (I.lam w s hs (cutoffPositiveCoefficient M H xi N w hs) w s sigma 2)⁻¹ := by
  constructor
  · rw [aux_lem_extension_cell_moment_Lam_eq_tsum I z r hr _ w s hs hsub sigma hsigma,
      aux_lem_extension_cell_moment_Lam_eq_tsum I w s hs _ w s hs (by exact subset_rfl)
        sigma hsigma]
    apply tsum_congr
    intro n
    rw [aux_lem_extension_cell_moment_maxB_chart_eq I M H xi N z r hr w s hs hsub n,
      aux_lem_extension_cell_moment_maxB_chart_eq I M H xi N w s hs w s hs
        (by exact subset_rfl) n]
  · rw [aux_lem_extension_cell_moment_lam_inv_eq_tsum I z r hr _ w s hs hsub sigma hsigma,
      aux_lem_extension_cell_moment_lam_inv_eq_tsum I w s hs _ w s hs
        (by exact subset_rfl) sigma hsigma]
    apply tsum_congr
    intro n
    rw [aux_lem_extension_cell_moment_maxS_chart_eq I M H xi N z r hr w s hs hsub n,
      aux_lem_extension_cell_moment_maxS_chart_eq I M H xi N w s hs w s hs
        (by exact subset_rfl) n]

end Paper
