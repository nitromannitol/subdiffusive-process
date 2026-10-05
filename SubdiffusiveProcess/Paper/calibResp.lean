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

/-- The infrared-free affine Dirichlet response `Λ⁰_{N,Q_{3^k}}(e₀)` (H = 0 cutoff coefficient). -/
def calibResp (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k N : ℕ) (β : BilateralField d) : ℝ :=
  haveI : NeZero d := ⟨by omega⟩
  affineDirichletResponse
    (centeredCube_isBounded (0 : SpatialCoordinates d) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))
    (centeredCube_killedPoincare (0 : SpatialCoordinates d) (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) β N 0
      (pow_pos (zero_lt_three : (0 : ℝ) < 3) k))
    (aux_thm_c1_envcal_e0 d (by omega))

end SubdiffusiveProcess.Paper
