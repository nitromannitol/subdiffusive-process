import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_matched_affine_moment
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_limit_bank_norm

open MeasureTheory SubdiffusiveProcess Homogenization Homogenization.Book.Ch02
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

def aux_matched_affine_finite_response {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (e : Homogenization.Vec d)
    (inverse : Bool) (N : ℕ) (om : BilateralField d) : ℝ :=
  let hP := aux_matched_root_poincare (d := d)
  let aQ := SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient M
    (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N
    (0 : SpatialCoordinates d) (by norm_num : (0 : ℝ) < 1)
  if inverse then affineInverseNeumannResponse hP.2 aQ e
  else affineDirichletResponse
    (centeredCube_isBounded (0 : SpatialCoordinates d)
      (by norm_num : (0 : ℝ) < 1)) hP.1 aQ e

theorem lem_as_coarse_shallow_grid_matched_limit_affine_moment {d : ℕ} [NeZero d]
    (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (p : ℝ) (hp : 1 ≤ p) :
    ∃ δ0 C0 : ℝ, 0 < δ0 ∧ 0 < C0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ δ0 →
      ∀ (e : Homogenization.Vec d), vecNormSq e = 1 →
      ∀ (inverse : Bool) (Z : BilateralField d → ℝ),
        (∀ N, AEStronglyMeasurable
          (aux_matched_affine_finite_response M e inverse N)
          (chaosSampleLaw M).toMeasure) →
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (aux_matched_affine_finite_response M e inverse) Filter.atTop Z →
        MemLp Z (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ∧
        eLpNorm Z (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (2 * volume.real
            (centeredCube (0 : SpatialCoordinates d) 1
              (by norm_num) : Set (SpatialCoordinates d)) * (C0 + 1)) := by
  obtain ⟨δ0, C0, hδ0, hC0, hfinite⟩ :=
    lem_as_coarse_shallow_grid_matched_affine_moment hd I p hp
  refine ⟨δ0, C0, hδ0, hC0, ?_⟩
  intro M hM e he inverse Z hmeas hconv
  apply lem_as_coarse_shallow_grid_limit_bank_norm
    (chaosSampleLaw M).toMeasure (ENNReal.ofReal (2 * p))
    (ENNReal.ofReal (2 * volume.real
      (centeredCube (0 : SpatialCoordinates d) 1
        (by norm_num) : Set (SpatialCoordinates d)) * (C0 + 1)))
  · exact ENNReal.ofReal_lt_top
  · exact hmeas
  · intro N
    have h := hfinite M hM N e he
    unfold aux_matched_physical_affine_moment_bound at h
    cases inverse with
    | false => simpa [aux_matched_affine_finite_response] using h.1
    | true => simpa [aux_matched_affine_finite_response] using h.2
  · exact hconv

end Paper

