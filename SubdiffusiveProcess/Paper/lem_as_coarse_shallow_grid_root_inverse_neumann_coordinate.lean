import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_affine_inverse_neumann_measurable
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_scale_shift

open MeasureTheory SubdiffusiveProcess Homogenization Homogenization.Book.Ch02 Filter
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The actual inverse-Neumann bank limit and all its scale shifts inherit
the uniform affine moment bound from the finite responses. -/
theorem lem_as_coarse_shallow_grid_root_inverse_neumann_coordinate {d : ℕ} [NeZero d]
    (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ0 C0 : ℝ, 0 < δ0 ∧ 0 < C0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ δ0 →
      ∀ (e : Homogenization.Vec d), vecNormSq e = 1 →
      ∀ (Z : BilateralField d → ℝ),
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (aux_matched_affine_finite_response M e true) atTop Z →
        (AEStronglyMeasurable Z (chaosSampleLaw M).toMeasure ∧
          eLpNorm Z (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (2 * volume.real
              (centeredCube (0 : SpatialCoordinates d) 1
                (by norm_num) : Set (SpatialCoordinates d)) * (C0 + 1))) ∧
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
  obtain ⟨δ0, C0, hδ0, hC0, hmoment⟩ :=
    lem_as_coarse_shallow_grid_matched_limit_affine_moment hd I q hq
  refine ⟨δ0, C0, hδ0, hC0, ?_⟩
  intro M hM e he Z hconv
  have hfinite : ∀ N, AEStronglyMeasurable
      (aux_matched_affine_finite_response M e true N)
      (chaosSampleLaw M).toMeasure := by
    intro N
    exact (lem_as_coarse_shallow_grid_affine_inverse_neumann_measurable M N e).aestronglyMeasurable
  obtain ⟨hLp, hbound⟩ := hmoment M hM e he true Z hfinite hconv
  refine ⟨⟨hLp.1, hbound⟩, ?_⟩
  intro k w
  have hp : MeasurePreserving
      (aux_lem_as_coarse_shallow_grid_scaleShift k w)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure :=
    lem_as_coarse_shallow_grid_scale_shift M k w
  refine ⟨hLp.1.comp_quasiMeasurePreserving hp.quasiMeasurePreserving, ?_⟩
  rw [show (fun om => Z (aux_lem_as_coarse_shallow_grid_scaleShift k w om)) =
    Z ∘ aux_lem_as_coarse_shallow_grid_scaleShift k w from rfl]
  rw [eLpNorm_comp_measurePreserving hLp.1 hp]
  exact hbound

end Paper

