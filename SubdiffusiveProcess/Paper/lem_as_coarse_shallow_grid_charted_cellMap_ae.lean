module

public import SubdiffusiveProcess.Paper.lem_extension_cell_moment
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_scale_shift
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory SubdiffusiveProcess SubdiffusiveProcess.Lane4 Homogenization Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The chart used by the shallow grid has the actual physical cutoff
coefficient as its scalar representative on the origin cell. -/
theorem aux_lem_as_coarse_shallow_grid_charted_coefficient_ae {d : ℕ}
    (Jc : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω : BilateralField d) (N : ℕ) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) :
    ∀ᵐ y ∂volumeMeasureOn (openCubeSet (originCube d 0)),
      ((Jc.chart z r hr (cutoffPositiveCoefficient M H ω N z hr) z r).coeffOn
        (originCube d 0)).toCoeffField y =
        scalarMatrix (cutoffCoefficient M H ω N (fun i => z i + r * y i)) := by
  exact aux_lem_extension_cell_moment_chart_scalar_identity Jc M H ω N z r hr
    z r hr subset_rfl (originCube d 0) subset_rfl

/-- The specialization at a retained depth uses exactly the cell map in the
coarse-field coefficient comparison. -/
theorem lem_as_coarse_shallow_grid_charted_cellMap_ae {d : ℕ}
    (Jc : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω : BilateralField d) (N k : ℕ) (w : SpatialCoordinates d) :
    ∀ᵐ y ∂volumeMeasureOn (openCubeSet (originCube d 0)),
      ((Jc.chart w ((3 : ℝ)^(-(k : ℤ))) (by positivity)
        (cutoffPositiveCoefficient M H ω N w (by positivity))
        w ((3 : ℝ)^(-(k : ℤ)))).coeffOn (originCube d 0)).toCoeffField y =
        scalarMatrix (cutoffCoefficient M H ω N
          (aux_lem_as_coarse_shallow_grid_cellMap k w y)) := by
  filter_upwards [aux_lem_as_coarse_shallow_grid_charted_coefficient_ae
    Jc M H ω N w ((3 : ℝ)^(-(k : ℤ))) (by positivity)] with y hy
  have hmap : aux_lem_as_coarse_shallow_grid_cellMap k w y =
      (fun i => w i + (3 : ℝ)^(-(k : ℤ)) * y i) := by
    funext i
    simp [aux_lem_as_coarse_shallow_grid_cellMap, cubeDilation_apply]
  simpa only [hmap] using hy

end Paper


