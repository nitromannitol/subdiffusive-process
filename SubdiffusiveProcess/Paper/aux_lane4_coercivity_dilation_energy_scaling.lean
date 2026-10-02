import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Paper.aux_lane4_coercivity_dilation_integral_scaling

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Statement-only fine child: coefficient-energy scaling after the affine pullback. -/
theorem aux_lane4_coercivity_dilation_energy_scaling
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (u : SobolevData (centeredCube z r hr))
    (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (hcoeff : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)), b.val x = a.val (cubeDilation z 0 r x))
    (hvalue : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)), w.1 x = u.1 (cubeDilation z 0 r x))
    (hgrad : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)), w.2 i x = r * u.2 i (cubeDilation z 0 r x)) :
    sobolevCoefficientForm a u u =
      r ^ ((d : ℝ) - 2) * sobolevCoefficientForm b w w := by
  change weightedGradientForm a.val (sobolevGradient u) (sobolevGradient u) =
    r ^ ((d : ℝ) - 2) *
      weightedGradientForm b.val (sobolevGradient w) (sobolevGradient w)
  rw [weightedGradientForm_apply, weightedGradientForm_apply]
  have hscale (i : Fin d) :
      (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          a.val y * (u.2 i y * u.2 i y)) =
        r ^ d *
          (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
            Set (SpatialCoordinates d)),
            a.val (cubeDilation z 0 r x) *
              (u.2 i (cubeDilation z 0 r x) * u.2 i (cubeDilation z 0 r x))) := by
    let F : SpatialCoordinates d → ℝ := fun y =>
      a.val y * (u.2 i y * u.2 i y)
    have hF : AEStronglyMeasurable F
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
      exact (Lp.aestronglyMeasurable a.val).mul
        ((Lp.aestronglyMeasurable (u.2 i)).mul (Lp.aestronglyMeasurable (u.2 i)))
    have hT : AEMeasurable (cubeDilation z 0 r)
        (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d))) :=
      (continuous_cubeDilation z 0 r).measurable.aemeasurable
    have hc : ENNReal.ofReal |(r ^ d)⁻¹| ≠ 0 := by
      positivity
    have hFm : AEStronglyMeasurable F
        (Measure.map (cubeDilation z 0 r)
          (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
            Set (SpatialCoordinates d)))) := by
      rw [map_cubeDilation_restrict z 0 hr h1]
      exact hF.mono_ac Measure.smul_absolutelyContinuous
    have hchange := integral_map (μ := volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) hT
      hFm
    rw [map_cubeDilation_restrict z 0 hr h1, integral_smul_measure] at hchange
    have hpowpos : 0 < r ^ d := by positivity
    rw [smul_eq_mul, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_pos (inv_pos.mpr hpowpos)] at hchange
    change (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), F y) =
      r ^ d * (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)), F (cubeDilation z 0 r x))
    calc
      (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), F y) =
          r ^ d * ((r ^ d)⁻¹ *
            (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), F y)) := by
              field_simp [pow_ne_zero _ hr.ne']
      _ = r ^ d * (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)), F (cubeDilation z 0 r x)) := by
            rw [← hchange]
  have hpull (i : Fin d) :
      (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)),
          a.val (cubeDilation z 0 r x) *
            (u.2 i (cubeDilation z 0 r x) * u.2 i (cubeDilation z 0 r x))) =
        r⁻¹ ^ 2 *
          (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
            Set (SpatialCoordinates d)), b.val x * (w.2 i x * w.2 i x)) := by
    calc
      (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)),
          a.val (cubeDilation z 0 r x) *
            (u.2 i (cubeDilation z 0 r x) * u.2 i (cubeDilation z 0 r x))) =
          ∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
            Set (SpatialCoordinates d)),
            r⁻¹ ^ 2 * (b.val x * (w.2 i x * w.2 i x)) := by
              apply integral_congr_ae
              filter_upwards [hcoeff, hgrad i] with x hcoeff_x hgrad_x
              rw [hcoeff_x, hgrad_x]
              field_simp [hr.ne']
      _ = r⁻¹ ^ 2 *
          (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
            Set (SpatialCoordinates d)), b.val x * (w.2 i x * w.2 i x)) := by
              rw [integral_const_mul]
  have hpower : r ^ d * r⁻¹ ^ 2 = r ^ ((d : ℝ) - 2) := by
    calc
      r ^ d * r⁻¹ ^ 2 = r ^ (d : ℝ) / r ^ (2 : ℝ) := by
        rw [Real.rpow_natCast r d]
        field_simp [hr.ne']
        exact Real.rpow_natCast r 2
      _ = r ^ ((d : ℝ) - 2) := (Real.rpow_sub hr _ _).symm
  simp [sobolevGradient]
  calc
    (∑ i : Fin d, ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        a.val x * (u.2 i x * u.2 i x)) =
        ∑ i : Fin d, r ^ d *
          (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
            Set (SpatialCoordinates d)),
            a.val (cubeDilation z 0 r x) *
              (u.2 i (cubeDilation z 0 r x) * u.2 i (cubeDilation z 0 r x))) := by
          exact Finset.sum_congr rfl fun i _ => hscale i
    _ = ∑ i : Fin d, r ^ d *
          (r⁻¹ ^ 2 *
            (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
              Set (SpatialCoordinates d)), b.val x * (w.2 i x * w.2 i x))) := by
          exact Finset.sum_congr rfl fun i _ => congrArg (fun t => r ^ d * t) (hpull i)
    _ = r ^ ((d : ℝ) - 2) *
          (∑ i : Fin d, ∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
            Set (SpatialCoordinates d)), b.val x * (w.2 i x * w.2 i x)) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_assoc, hpower]

end Paper
