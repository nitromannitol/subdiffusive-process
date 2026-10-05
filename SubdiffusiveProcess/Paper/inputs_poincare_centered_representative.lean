module

public import SubdiffusiveProcess.Paper.in_poincare

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_poincare_centered_representative (d : ℕ) (_hd : 2 ≤ d) :
    (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∀ u : weakSobolevGraph (centeredCube z r hr),
    ∃ w : meanZeroSobolevGraph (centeredCube z r hr),
      ((w : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun x => (u : SobolevData (centeredCube z r hr)).1 x -
          _root_.SubdiffusiveProcess.EllipticRegularity.setAverage
            (centeredCube z r hr : Set (SpatialCoordinates d))
            (u : SobolevData (centeredCube z r hr)).1) ∧
      sobolevGradient (w : SobolevData (centeredCube z r hr)) =
        sobolevGradient (u : SobolevData (centeredCube z r hr))) := by
  intro z r hr u
  let Ω := centeredCube z r hr
  have hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)) := by
    dsimp [Ω]
    exact centeredCube_isBounded z hr
  have hvol : volume.real (Ω : Set (SpatialCoordinates d)) ≠ 0 := by
    exact ne_of_gt (by dsimp [Ω]; exact centeredCube_volume_pos z hr)
  let w := meanZeroSobolevRepresentative hΩ hvol u
  refine ⟨w, ?_, ?_⟩
  · have havg :
        _root_.SubdiffusiveProcess.EllipticRegularity.setAverage (Ω : Set (SpatialCoordinates d))
            (u : SobolevData Ω).1 =
          (∫ y in (Ω : Set (SpatialCoordinates d)), (u : SobolevData Ω).1 y) /
            volume.real (Ω : Set (SpatialCoordinates d)) := by
      have hint :
          (∫ y in (Ω : Set (SpatialCoordinates d)), (u : SobolevData Ω).1 y
            ∂volume.restrict (Ω : Set (SpatialCoordinates d))) =
          ∫ y in (Ω : Set (SpatialCoordinates d)), (u : SobolevData Ω).1 y := by
        rw [Measure.restrict_restrict_of_subset (μ := volume)
          (s := (Ω : Set (SpatialCoordinates d))) (t := (Ω : Set (SpatialCoordinates d)))
          Set.Subset.rfl]
      unfold _root_.SubdiffusiveProcess.EllipticRegularity.setAverage
      rw [hint, div_eq_mul_inv, mul_comm]
    filter_upwards [meanZeroSobolevRepresentative_coeFn hΩ hvol u] with x hx
    rw [hx, havg]
  · have hgrad := meanZeroSobolevRepresentative_gradient hΩ hvol u
    change sobolevGradient (w : SobolevData Ω) =
      sobolevGradient (u : SobolevData Ω) at hgrad
    exact hgrad

end SubdiffusiveProcess.Paper

