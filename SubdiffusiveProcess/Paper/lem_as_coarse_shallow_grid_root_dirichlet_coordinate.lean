import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_matched_limit_affine_moment
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_affine_dirichlet_measurable

open MeasureTheory SubdiffusiveProcess Homogenization Homogenization.Book.Ch02 Filter
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The root Dirichlet coordinate of a response-bank limit has a concrete
uniform moment bound. The convergence premise is the corresponding output of
the response-bank completion, and carries no moment assumption. -/
theorem lem_as_coarse_shallow_grid_root_dirichlet_coordinate {d : ℕ} [NeZero d]
    (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ δ0 C0 : ℝ, 0 < δ0 ∧ 0 < C0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ δ0 →
      ∀ (e : Homogenization.Vec d), vecNormSq e = 1 →
      ∀ (Z : BilateralField d → ℝ),
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (aux_matched_affine_finite_response M e false) atTop Z →
        AEStronglyMeasurable Z (chaosSampleLaw M).toMeasure ∧
        eLpNorm Z (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (2 * volume.real
            (centeredCube (0 : SpatialCoordinates d) 1
              (by norm_num) : Set (SpatialCoordinates d)) * (C0 + 1)) := by
  obtain ⟨δ0, C0, hδ0, hC0, hmoment⟩ :=
    lem_as_coarse_shallow_grid_matched_limit_affine_moment hd I q hq
  refine ⟨δ0, C0, hδ0, hC0, ?_⟩
  intro M hM e he Z hconv
  have hfinite : ∀ N, AEStronglyMeasurable
      (aux_matched_affine_finite_response M e false N)
      (chaosSampleLaw M).toMeasure := by
    intro N
    have hm : Measurable (aux_matched_affine_finite_response M e false N) := by
      simpa [aux_matched_affine_finite_response] using
        (lem_as_coarse_shallow_grid_affine_dirichlet_measurable M N e)
    exact hm.aestronglyMeasurable
  obtain ⟨hLp, hbound⟩ := hmoment M hM e he false Z hfinite hconv
  exact ⟨hLp.1, hbound⟩

end Paper

