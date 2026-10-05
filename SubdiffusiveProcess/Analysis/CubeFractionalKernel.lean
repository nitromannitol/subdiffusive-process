module

public import SubdiffusiveProcess.Geometry.CubeEuclideanDiameter

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess

/-- On a centered cube, the unweighted squared-difference integral is controlled by the unnormalized order-one fractional kernel energy. -/
theorem double_lintegral_sq_le_diameter_rpow_mul_fractional_kernel
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (f : SpatialCoordinates d → ℝ) :
    (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal ((f y - f x) ^ 2)) ≤
      (ENNReal.ofReal (Real.sqrt d * r)) ^ ((d : ℝ) + 1) *
        (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ENNReal.ofReal ((f y - f x) ^ 2) /
              (ENNReal.ofReal
                (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^ ((d : ℝ) + 1)) := by
  have hp : 0 ≤ (d : ℝ) + 1 := by positivity
  have hmeas : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hC_top :
      (ENNReal.ofReal (Real.sqrt d * r)) ^ ((d : ℝ) + 1) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top
  have hpoint : ∀ y ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal ((f y - f x) ^ 2) ≤
          (ENNReal.ofReal (Real.sqrt d * r)) ^ ((d : ℝ) + 1) *
            (ENNReal.ofReal ((f y - f x) ^ 2) /
              (ENNReal.ofReal
                (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^ ((d : ℝ) + 1)) := by
    intro y hy x hx
    by_cases hdist : Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2) = 0
    · have hsum : (∑ j : Fin d, (y j - x j) ^ 2) = 0 := by
        apply (Real.sqrt_eq_zero (Finset.sum_nonneg fun j _ => sq_nonneg (y j - x j))).mp
        exact hdist
      have hcoord : ∀ j : Fin d, y j = x j := by
        intro j
        have hle : (y j - x j) ^ 2 ≤ ∑ i : Fin d, (y i - x i) ^ 2 := by
          exact Finset.single_le_sum (fun i _ => sq_nonneg (y i - x i)) (Finset.mem_univ j)
        have hz : (y j - x j) ^ 2 = 0 := le_antisymm (hsum ▸ hle) (sq_nonneg _)
        nlinarith
      have hxy : y = x := funext hcoord
      simp [hxy]
    · have hdist_pos : 0 < Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2) :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hdist)
      have hdiam : Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2) ≤ Real.sqrt d * r := by
        have hsum_eq : (∑ j : Fin d, (x j - y j) ^ 2) =
            ∑ j : Fin d, (y j - x j) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        rw [← hsum_eq]
        exact euclideanDist_le_sqrt_dim_mul_side_of_mem_centeredCube z hr hx hy
      have hofreal : ENNReal.ofReal
          (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2)) ≤
          ENNReal.ofReal (Real.sqrt d * r) := ENNReal.ofReal_le_ofReal hdiam
      have hrpow :
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^ ((d : ℝ) + 1) ≤
            (ENNReal.ofReal (Real.sqrt d * r)) ^ ((d : ℝ) + 1) :=
        ENNReal.rpow_le_rpow hofreal hp
      have hden_pos : 0 <
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^ ((d : ℝ) + 1) :=
        ENNReal.rpow_pos_of_nonneg (ENNReal.ofReal_pos.mpr hdist_pos) hp
      have hden_top :
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^ ((d : ℝ) + 1) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top
      calc
        ENNReal.ofReal ((f y - f x) ^ 2) =
            (ENNReal.ofReal
              (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^ ((d : ℝ) + 1) *
              (ENNReal.ofReal ((f y - f x) ^ 2) /
                (ENNReal.ofReal
                  (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^ ((d : ℝ) + 1)) := by
          rw [ENNReal.mul_div_cancel (ne_of_gt hden_pos) hden_top]
        _ ≤ (ENNReal.ofReal (Real.sqrt d * r)) ^ ((d : ℝ) + 1) *
              (ENNReal.ofReal ((f y - f x) ^ 2) /
                (ENNReal.ofReal
                  (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^ ((d : ℝ) + 1)) :=
          mul_le_mul_left hrpow _
  calc
    (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal ((f y - f x) ^ 2)) ≤
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          (ENNReal.ofReal (Real.sqrt d * r)) ^ ((d : ℝ) + 1) *
            (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ENNReal.ofReal ((f y - f x) ^ 2) /
                (ENNReal.ofReal
                  (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^ ((d : ℝ) + 1)) := by
      refine setLIntegral_mono_ae' hmeas (ae_of_all _ ?_)
      intro y hy
      calc
        (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ENNReal.ofReal ((f y - f x) ^ 2)) ≤
            ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              (ENNReal.ofReal (Real.sqrt d * r)) ^ ((d : ℝ) + 1) *
                (ENNReal.ofReal ((f y - f x) ^ 2) /
                  (ENNReal.ofReal
                    (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^ ((d : ℝ) + 1)) := by
          refine setLIntegral_mono_ae' hmeas (ae_of_all _ ?_)
          intro x hx
          exact hpoint y hy x hx
        _ = (ENNReal.ofReal (Real.sqrt d * r)) ^ ((d : ℝ) + 1) *
              (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
                ENNReal.ofReal ((f y - f x) ^ 2) /
                  (ENNReal.ofReal
                    (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^ ((d : ℝ) + 1)) := by
          rw [MeasureTheory.lintegral_const_mul' _ _ hC_top]
    _ = (ENNReal.ofReal (Real.sqrt d * r)) ^ ((d : ℝ) + 1) *
        (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ENNReal.ofReal ((f y - f x) ^ 2) /
              (ENNReal.ofReal
                (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) ^ ((d : ℝ) + 1)) := by
      rw [MeasureTheory.lintegral_const_mul' _ _ hC_top]


end SubdiffusiveProcess
