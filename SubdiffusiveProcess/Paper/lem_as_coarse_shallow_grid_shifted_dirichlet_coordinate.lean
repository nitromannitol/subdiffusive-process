module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_root_dirichlet_coordinate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_scale_shift

@[expose] public section

open MeasureTheory SubdiffusiveProcess Homogenization Homogenization.Book.Ch02 Filter
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The actual scale-shifted Dirichlet bank coordinate inherits the root
coordinate's measurability and uniform moment bound. -/
theorem lem_as_coarse_shallow_grid_shifted_dirichlet_coordinate {d : ℕ} [NeZero d]
    (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ0 C0 : ℝ, 0 < δ0 ∧ 0 < C0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ δ0 →
      ∀ (e : Homogenization.Vec d), vecNormSq e = 1 →
      ∀ (Z : BilateralField d → ℝ),
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (aux_matched_affine_finite_response M e false) atTop Z →
      ∀ (k : ℕ) (w : SpatialCoordinates d),
        AEStronglyMeasurable
          (fun om => Z (aux_lem_as_coarse_shallow_grid_scaleShift k w om))
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm
          (fun om => Z (aux_lem_as_coarse_shallow_grid_scaleShift k w om))
          (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (2 * volume.real
            (centeredCube (0 : SpatialCoordinates d) 1
              (by norm_num) : Set (SpatialCoordinates d)) * (C0 + 1)) := by
  obtain ⟨δ0, C0, hδ0, hC0, hroot⟩ :=
    lem_as_coarse_shallow_grid_root_dirichlet_coordinate hd I q hq
  refine ⟨δ0, C0, hδ0, hC0, ?_⟩
  intro M hM e he Z hconv k w
  obtain ⟨hZ, hbound⟩ := hroot M hM e he Z hconv
  have hp : MeasurePreserving
      (aux_lem_as_coarse_shallow_grid_scaleShift k w)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure :=
    lem_as_coarse_shallow_grid_scale_shift M k w
  refine ⟨hZ.comp_quasiMeasurePreserving hp.quasiMeasurePreserving, ?_⟩
  rw [show (fun om => Z (aux_lem_as_coarse_shallow_grid_scaleShift k w om)) =
    Z ∘ aux_lem_as_coarse_shallow_grid_scaleShift k w from rfl]
  rw [eLpNorm_comp_measurePreserving hZ hp]
  exact hbound

end SubdiffusiveProcess.Paper

