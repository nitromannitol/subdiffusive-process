import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.CubeDilation
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem aux_lane4_coercivity_dilation_integral_scaling
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1) (F : SpatialCoordinates d → ℝ)
    (hF : AEStronglyMeasurable F
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), F y) =
      r ^ d *
        (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)), F (cubeDilation z 0 r x)) := by
  have hmap := map_cubeDilation_restrict z 0 hr h1
  have hc : ENNReal.ofReal |(r ^ d)⁻¹| ≠ 0 := by
    positivity
  have hFscaled : AEStronglyMeasurable F
      (ENNReal.ofReal |(r ^ d)⁻¹| •
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    refine ⟨hF.mk F, hF.stronglyMeasurable_mk, ?_⟩
    exact (MeasureTheory.Measure.ae_smul_measure_iff hc).2 hF.ae_eq_mk
  have hFmap : AEStronglyMeasurable F
      (Measure.map (cubeDilation z 0 r)
        (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)))) := by
    rw [hmap]
    exact hFscaled
  have hchange :
      (∫ y, F y ∂Measure.map (cubeDilation z 0 r)
        (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)))) =
        ∫ x, F (cubeDilation z 0 r x) ∂volume.restrict
          (centeredCube (0 : SpatialCoordinates d) 1 h1 :
            Set (SpatialCoordinates d)) := by
    exact integral_map (continuous_cubeDilation z 0 r).measurable.aemeasurable hFmap
  have htransport :
      (ENNReal.ofReal |(r ^ d)⁻¹|).toReal •
          (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), F y) =
        ∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)), F (cubeDilation z 0 r x) := by
    calc
      (ENNReal.ofReal |(r ^ d)⁻¹|).toReal •
          (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), F y) =
          ∫ y, F y ∂(ENNReal.ofReal |(r ^ d)⁻¹| •
            volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
              symm
              exact integral_smul_measure F _
      _ = ∫ y, F y ∂Measure.map (cubeDilation z 0 r)
          (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
            Set (SpatialCoordinates d))) := by rw [hmap]
      _ = ∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)), F (cubeDilation z 0 r x) := hchange
  have hreal : (ENNReal.ofReal |(r ^ d)⁻¹|).toReal = (r ^ d)⁻¹ := by
    rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos]
    positivity
  have htransport' :
      (r ^ d)⁻¹ * (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), F y) =
        ∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)), F (cubeDilation z 0 r x) := by
    rw [hreal] at htransport
    simpa only [smul_eq_mul] using htransport
  have hpow : r ^ d ≠ 0 := pow_ne_zero d (ne_of_gt hr)
  calc
    (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), F y) =
        r ^ d * ((r ^ d)⁻¹ *
          (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), F y)) := by
            rw [← mul_assoc, mul_inv_cancel₀ hpow, one_mul]
    _ = r ^ d *
        (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)), F (cubeDilation z 0 r x)) := by
            rw [htransport']

end Paper
