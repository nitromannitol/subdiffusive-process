module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_charted_cellMap_ae
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_cell_coefficient_comparison
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_cellMap_mem_osc_ball
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity Homogenization Set TopologicalSpace
open scoped NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Concrete killed and mean-zero Poincaré witnesses on the chart's origin cell. -/
theorem aux_lem_as_coarse_shallow_grid_charted_origin_poincare {d : ℕ} [NeZero d] :
    let Ω : Opens (SpatialCoordinates d) :=
      centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
    (∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph Ω) u‖) ∧
    (∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph Ω) u‖) := by
  let Ω : Opens (SpatialCoordinates d) :=
    centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  have hgeom : Homogenization.IsOpenBoundedConvexDomain
      (Ω : Set (SpatialCoordinates d)) := by
    have hset : (Ω : Set (SpatialCoordinates d)) =
        openCubeSet (originCube d 0) := by
      simpa [Ω] using
        (centeredCube_zero_eq_openCubeSet_originCube (d := d) 0 (by norm_num))
    rw [hset]
    exact isOpenBoundedConvexDomain_openCubeSet (originCube d 0)
  exact exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain Ω hgeom

/-- The actual charted origin-cell field has the shifted-bank scalar bounds
almost everywhere, with the paper's concrete coarse factor and oscillation. -/
theorem lem_as_coarse_shallow_grid_charted_origin_scalar_bounds {d : ℕ}
    (Jc : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω : BilateralField d) (N k : ℕ) (hk : k ≤ N)
    (w : SpatialCoordinates d) :
    ∀ᵐ y ∂volumeMeasureOn (openCubeSet (originCube d 0)),
      let g : C(SpatialCoordinates d, ℝ) :=
        H ω + ∑ j ∈ Finset.range k, ω (-(j : ℤ))
      let osc : ℝ := sSup {v : ℝ | ∃ x ∈ Metric.closedBall w
        (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
        ∃ x' ∈ Metric.closedBall w (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)),
          v = |g x - g x'|}
      let s : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp (g w - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
      let a : ℝ := cutoffCoefficient M
        (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
        (aux_lem_as_coarse_shallow_grid_scaleShift k w ω) (N-k) y
      let b : ℝ := cutoffCoefficient M H ω N
        (aux_lem_as_coarse_shallow_grid_cellMap k w y)
      ((Jc.chart w ((3 : ℝ)^(-(k : ℤ))) (by positivity)
        (cutoffPositiveCoefficient M H ω N w (by positivity))
        w ((3 : ℝ)^(-(k : ℤ)))).coeffOn (originCube d 0)).toCoeffField y =
          scalarMatrix b ∧
        (s * Real.exp (-osc)) * a ≤ b ∧ b ≤ (s * Real.exp osc) * a := by
  filter_upwards [lem_as_coarse_shallow_grid_charted_cellMap_ae Jc M H ω N k w,
    ae_restrict_mem (measurableSet_openCubeSet (originCube d 0))] with y hchart hy
  have hball := lem_as_coarse_shallow_grid_cellMap_mem_osc_ball (k := k) w y hy
  have hbounds := lem_as_coarse_shallow_grid_actual_cell_coefficient_comparison
    M H ω N k hk w y hball
  exact ⟨hchart, hbounds.1, hbounds.2⟩

end SubdiffusiveProcess.Paper
