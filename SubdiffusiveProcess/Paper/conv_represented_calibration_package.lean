module

public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_family_grids_actual
public import SubdiffusiveProcess.Paper.conv_represented_joint_grids
public import SubdiffusiveProcess.Paper.limit_form_package_side
public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Paper.thm_c1_env_calibration_core
public import SubdiffusiveProcess.Paper.prop_conc_mesh_cutoff_family
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.calibResp
public import SubdiffusiveProcess.Paper.calib_h0_large_cell_bounds

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **The calibration coordinates of a represented package** (joint coordinates added to the extraction):
almost-sure limits `LE k`, `LF k` of the responses `calibResp (K0+k)` along the two represented cutoff
sequences, an almost-sure limit `hinf` (locally uniform) of the infrared potentials `H (env n omega)`, and the
harmonic-cell bounds of the `H = 0` coefficient sequences on the padded calibration cubes. -/
def conv_represented_calibration_package (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (env : ℕ → Ω → BilateralField d)
    (NE NF : ℕ → ℕ) (t alpha : ℝ) : Prop :=
  ∃ (K0 : ℕ) (LE LF : ℕ → Ω → ℝ) (hinf : Ω → C(SpatialCoordinates d, ℝ)),
    (∀ k, ∀ᵐ omega ∂P, Tendsto (fun n => calibResp d hd M (K0 + k) (NE n) (env n omega)) atTop (𝓝 (LE k omega))) ∧
    (∀ k, ∀ᵐ omega ∂P, Tendsto (fun n => calibResp d hd M (K0 + k) (NF n) (env n omega)) atTop (𝓝 (LF k omega))) ∧
    (∀ᵐ omega ∂P, Tendsto (fun n => H (env n omega)) atTop (𝓝 (hinf omega))) ∧
    (∀ᵐ omega ∂P, ∀ k,
      calib_h0_large_cell_bounds (0 : SpatialCoordinates d) (3 * (3 : ℝ) ^ (K0 + k + 1) / 3)
        (by positivity)
        (fun n => cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (env n omega) (NE n))
        t alpha) ∧
    (∀ᵐ omega ∂P, ∀ k,
      calib_h0_large_cell_bounds (0 : SpatialCoordinates d) (3 * (3 : ℝ) ^ (K0 + k + 1) / 3)
        (by positivity)
        (fun n => cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) (env n omega) (NF n))
        t alpha)

end SubdiffusiveProcess.Paper
