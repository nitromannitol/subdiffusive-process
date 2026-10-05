module

public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_family_grids_actual
public import SubdiffusiveProcess.Paper.conv_represented_joint_grids
public import SubdiffusiveProcess.Paper.limit_form_package_side
public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Paper.thm_c1_env_calibration_core
public import SubdiffusiveProcess.Paper.prop_conc_mesh_cutoff_family
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Harmonic-cell bounds on the `3^d` cells of the padded cube `Q(z,R)` (mesh level `J = 1`) for every smooth
datum: `aux_prop_conc_mesh_cutoff_family_AllCellBounds` at `J = 1` without the side restriction. -/
def calib_h0_large_cell_bounds {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (a : ℕ → SpatialCoordinates d → ℝ) (t alpha : ℝ) : Prop :=
  ∀ theta : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ theta →
    ∀ thetaH : Homogenization.H1Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      thetaH.toFun = theta →
      aux_prop_conc_mesh_cutoff_family_CellBounds z R hR a t alpha 1 thetaH

end SubdiffusiveProcess.Paper
