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

/-- Regular strongly local limit forms with energy measures of both candidates (the limit-side packages of
`conv_represented_thm_c1_family_grids_actual`, without the nested-cube compatibility). -/
def conv_represented_limit_forms_package (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (env : ℕ → Ω → BilateralField d)
    (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
    (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ] DomainL2 (centeredCube (Z i) (R i) (hR i)))
    (NE NF : ℕ → ℕ) : Prop :=
  ∀ᵐ omega ∂P,
    ∃ (LE : ∀ i, aux_limit_form_package_limit_side d hd (Z i) (R i) (hR i) (Sspace i)
        (GE i omega) (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (NE n) (Z i) (hR i)))
      (LF : ∀ i, aux_limit_form_package_limit_side d hd (Z i) (R i) (hR i) (Sspace i)
        (GF i omega) (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (NF n) (Z i) (hR i))),
      ∀ i, _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal (LE i).form.toClosedForm ∧
        _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal (LF i).form.toClosedForm




end SubdiffusiveProcess.Paper
