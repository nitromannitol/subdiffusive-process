import SubdiffusiveProcess.Analysis.TriadicChildAverages
import SubdiffusiveProcess.Analysis.CubeFractionalKernel

open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess

/-- The weighted parent-to-child average increment is controlled by the literal parent fractional kernel energy. -/
theorem ofReal_sum_triadic_child_mass_mul_average_sub_average_sq_le_fractional_kernel
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M)
    (μ : Measure (SpatialCoordinates d)) [IsFiniteMeasure μ]
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f 2
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hmass : ∀ k : OddGridIndex d 1,
      μ.real (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) ≤ M) :
    ENNReal.ofReal
        (∑ k : OddGridIndex d 1,
          μ.real (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) *
            |averageOn (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) f -
              averageOn (centeredCube z r hr : Set (SpatialCoordinates d)) f| ^ 2) ≤
      ENNReal.ofReal (M * (((r / 3) ^ d) * (r ^ d))⁻¹) *
        (ENNReal.ofReal (Real.sqrt d * r)) ^ ((d : ℝ) + 1) *
          (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ENNReal.ofReal ((f y - f x) ^ 2) /
                (ENNReal.ofReal
                  (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^ ((d : ℝ) + 1)) := by
  classical
  let P : Set (SpatialCoordinates d) := centeredCube z r hr
  have hf1 : IntegrableOn f P := hf.integrable (by norm_num)
  have hf2 : IntegrableOn (fun x => f x ^ 2) P := hf.integrable_sq
  have hprod : Integrable
      (fun w : SpatialCoordinates d × SpatialCoordinates d =>
        (f w.1 - f w.2) ^ 2)
      ((volume.restrict P).prod (volume.restrict P)) := by
    have hfst : Integrable
        (fun w : SpatialCoordinates d × SpatialCoordinates d => f w.1 ^ 2)
        ((volume.restrict P).prod (volume.restrict P)) :=
      hf2.comp_fst (volume.restrict P)
    have hsnd : Integrable
        (fun w : SpatialCoordinates d × SpatialCoordinates d => f w.2 ^ 2)
        ((volume.restrict P).prod (volume.restrict P)) :=
      hf2.comp_snd (volume.restrict P)
    have hcross : Integrable
        (fun w : SpatialCoordinates d × SpatialCoordinates d =>
          f w.1 * f w.2)
        ((volume.restrict P).prod (volume.restrict P)) :=
      hf1.mul_prod hf1
    have heq : (fun w : SpatialCoordinates d × SpatialCoordinates d =>
        (f w.1 - f w.2) ^ 2) =
        (fun w => f w.1 ^ 2 - 2 * (f w.1 * f w.2) + f w.2 ^ 2) := by
      funext w
      ring
    rw [heq]
    exact (hfst.sub (hcross.const_mul 2)).add hsnd
  have hgintegrable : IntegrableOn
      (fun y => ∫ x in P, |f y - f x| ^ 2) P := by
    have h := hprod.integral_prod_left
    have h' : Integrable
        (fun y => ∫ x in P, (f y - f x) ^ 2)
        (volume.restrict P) := by
      simpa only [Prod.fst, Prod.snd] using h
    have heq : (fun y => ∫ x in P, |f y - f x| ^ 2) =
        (fun y => ∫ x in P, (f y - f x) ^ 2) := by
      funext y
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        change |f y - f x| ^ 2 = (f y - f x) ^ 2
        rw [sq_abs])
    rw [heq]
    exact h'
  have hinner : ∀ᵐ y ∂(volume.restrict P),
      Integrable (fun x => |f y - f x| ^ 2) (volume.restrict P) := by
    filter_upwards [hprod.swap.prod_left_ae] with y hy
    simpa only [Prod.fst, Prod.snd, sq_abs] using hy
  have hbridge :
      ENNReal.ofReal (∫ y in P, ∫ x in P, |f y - f x| ^ 2) =
        (∫⁻ y in P, ∫⁻ x in P, ENNReal.ofReal ((f y - f x) ^ 2)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgintegrable
      (Filter.Eventually.of_forall fun y => integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun x => sq_nonneg |f y - f x|))]
    apply lintegral_congr_ae
    filter_upwards [hinner] with y hy
    calc
      ENNReal.ofReal (∫ x in P, |f y - f x| ^ 2) =
          ∫⁻ x in P, ENNReal.ofReal (|f y - f x| ^ 2) :=
        ofReal_integral_eq_lintegral_ofReal hy
          (Filter.Eventually.of_forall fun x => sq_nonneg |f y - f x|)
      _ = ∫⁻ x in P, ENNReal.ofReal ((f y - f x) ^ 2) := by
        apply lintegral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          change ENNReal.ofReal (|f y - f x| ^ 2) =
            ENNReal.ofReal ((f y - f x) ^ 2)
          rw [sq_abs])
  have hsum := sum_triadic_child_mass_mul_average_sub_average_sq_le
    (z := z) hr hM μ f hf hmass
  have hkernel := double_lintegral_sq_le_diameter_rpow_mul_fractional_kernel
    hd z hr f
  have hbridge' :
      ENNReal.ofReal (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), |f y - f x| ^ 2) =
        (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ENNReal.ofReal ((f y - f x) ^ 2)) := by
    simpa [P] using hbridge
  calc
    ENNReal.ofReal
        (∑ k : OddGridIndex d 1,
          μ.real (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) *
            |averageOn (oddGridCell z r hr 1 k : Set (SpatialCoordinates d)) f -
              averageOn (centeredCube z r hr : Set (SpatialCoordinates d)) f| ^ 2) ≤
      ENNReal.ofReal
        (M * (((r / 3) ^ d) * (r ^ d))⁻¹ *
          (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              |f y - f x| ^ 2)) := by
      exact ENNReal.ofReal_le_ofReal hsum
    _ = ENNReal.ofReal (M * (((r / 3) ^ d) * (r ^ d))⁻¹) *
          ENNReal.ofReal (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              |f y - f x| ^ 2) := by
      have hcoef : 0 ≤ M * (((r / 3) ^ d) * (r ^ d))⁻¹ :=
        mul_nonneg hM (by positivity)
      exact ENNReal.ofReal_mul hcoef
    _ ≤ ENNReal.ofReal (M * (((r / 3) ^ d) * (r ^ d))⁻¹) *
        ((ENNReal.ofReal (Real.sqrt d * r)) ^ ((d : ℝ) + 1) *
          (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ENNReal.ofReal ((f y - f x) ^ 2) /
              (ENNReal.ofReal
                (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^ ((d : ℝ) + 1))) := by
      rw [hbridge']
      gcongr
    _ = ENNReal.ofReal (M * (((r / 3) ^ d) * (r ^ d))⁻¹) *
        (ENNReal.ofReal (Real.sqrt d * r)) ^ ((d : ℝ) + 1) *
          (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ENNReal.ofReal ((f y - f x) ^ 2) /
              (ENNReal.ofReal
                (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^ ((d : ℝ) + 1)) := by
      ring

end SubdiffusiveProcess
