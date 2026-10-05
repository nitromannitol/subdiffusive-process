module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_charted_cellMap_ae
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_scale_shift

@[expose] public section

open MeasureTheory SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity Homogenization Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The charted positive coefficient has the exact coarse-factor times
infrared-free shifted coefficient on the origin cell. -/
theorem lem_as_coarse_shallow_grid_charted_shifted_factor_ae {d : ℕ}
    (Jc : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω : BilateralField d) (N k : ℕ) (hk : k ≤ N)
    (w : SpatialCoordinates d) :
    ∀ᵐ y ∂volumeMeasureOn (openCubeSet (originCube d 0)),
      ((Jc.chart w ((3 : ℝ)^(-(k : ℤ))) (by positivity)
        (cutoffPositiveCoefficient M H ω N w (by positivity))
        w ((3 : ℝ)^(-(k : ℤ)))).coeffOn (originCube d 0)).toCoeffField y =
        scalarMatrix
          ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N-k) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) *
            Real.exp (H ω (aux_lem_as_coarse_shallow_grid_cellMap k w y) +
              ∑ j ∈ Finset.range k,
                ω (-(j : ℤ)) (aux_lem_as_coarse_shallow_grid_cellMap k w y) -
                (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
              (aux_lem_as_coarse_shallow_grid_scaleShift k w ω) (N-k) y) := by
  filter_upwards [lem_as_coarse_shallow_grid_charted_cellMap_ae Jc M H ω N k w]
    with y hy
  rw [hy, aux_lem_as_coarse_shallow_grid_cutoff_factor M H ω N k hk w y]
  simp only [Int.ofNat_eq_natCast]

end SubdiffusiveProcess.Paper
