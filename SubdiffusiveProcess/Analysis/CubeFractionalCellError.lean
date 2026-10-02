import SubdiffusiveProcess.Analysis.CubeCellProjection
import SubdiffusiveProcess.Geometry.CubeEuclideanDiameter
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory Filter Set TopologicalSpace Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-- The unnormalized scalar Gagliardo integral on the actual centered cube. -/
def cubeGagliardoIntegral {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : ℝ) (f : DomainL2 (centeredCube z r hr)) : ℝ≥0∞ :=
  ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
    ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((f x - f y) ^ 2) /
        ENNReal.ofReal (euclideanDist x y) ^ ((d : ℝ) + 2 * s)

/-- The averaging approximation has error of order the cell side to the fractional order. -/
theorem cubeCellProjection_error_sq_le {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (s : ℝ) (hs : 0 < s) (m : ℕ)
    (f : DomainL2 (centeredCube z r hr)) :
    ENNReal.ofReal (‖f - cubeCellProjection z r hr m f‖ ^ 2) ≤
      (ENNReal.ofReal ((r / (2 * (m : ℝ) + 1)) ^ d))⁻¹ *
        (ENNReal.ofReal (Real.sqrt d * (r / (2 * (m : ℝ) + 1)))) ^ ((d : ℝ) + 2 * s) *
          cubeGagliardoIntegral z r hr s f := by
  classical
  let Q : Set (SpatialCoordinates d) := centeredCube z r hr
  let q : OddGridIndex d m → Set (SpatialCoordinates d) := fun k => oddGridCell z r hr m k
  let delta : ℝ := r / (2 * (m : ℝ) + 1)
  have hdelta : 0 < delta := div_pos hr (by positivity)
  let power : ℝ := (d : ℝ) + 2 * s
  have hpower : 0 < power := by dsimp [power]; positivity
  let diam : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt d * delta) ^ power
  let invvol : ℝ≥0∞ := (ENNReal.ofReal (delta ^ d))⁻¹
  let kernel : SpatialCoordinates d → SpatialCoordinates d → ℝ≥0∞ := fun x y =>
    ENNReal.ofReal ((f x - f y) ^ 2) / ENNReal.ofReal (euclideanDist x y) ^ power
  let error : SpatialCoordinates d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (((f - cubeCellProjection z r hr m f : DomainL2 (centeredCube z r hr)) x) ^ 2)
  have hnorm : ENNReal.ofReal (‖f - cubeCellProjection z r hr m f‖ ^ 2) =
      ∫⁻ x in Q, error x := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    exact eLpNorm_two_sq_eq_lintegral_sq _ _
  have hpair (k : OddGridIndex d m) (x y : SpatialCoordinates d)
      (hx : x ∈ q k) (hy : y ∈ q k) :
      ENNReal.ofReal ((f x - f y) ^ 2) ≤ diam * kernel x y := by
    by_cases hxy : x = y
    · subst y
      simp only [sub_self, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero, zero_le]
    have hdistpos : 0 < euclideanDist x y :=
      lt_of_le_of_ne (euclideanDist_nonneg x y) (Ne.symm ((euclideanDist_eq_zero_iff).not.mpr hxy))
    have hdistbound : euclideanDist x y ≤ Real.sqrt d * delta := by
      simpa only [euclideanDist, euclideanNorm, vecNormSq, vecDot, Pi.sub_apply, pow_two] using
        euclideanDist_le_sqrt_dim_mul_side_of_mem_centeredCube (oddGridCenter z r m k)
          hdelta hx hy
    have hden0 : ENNReal.ofReal (euclideanDist x y) ^ power ≠ 0 := by
      exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hdistpos) ENNReal.ofReal_ne_top).ne'
    have hdent : ENNReal.ofReal (euclideanDist x y) ^ power ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg hpower.le ENNReal.ofReal_ne_top
    calc
      ENNReal.ofReal ((f x - f y) ^ 2) =
          ENNReal.ofReal (euclideanDist x y) ^ power * kernel x y :=
        (ENNReal.mul_div_cancel hden0 hdent).symm
      _ ≤ diam * kernel x y := mul_le_mul_left
        (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hdistbound) hpower.le) _
  have hcell (k : OddGridIndex d m) :
      (∫⁻ x in q k, error x) ≤ invvol * diam * ∫⁻ x in q k, ∫⁻ y in Q, kernel x y := by
    have hsub : q k ⊆ Q := oddGridCell_subset z hr m k
    have hvol0 : volume (q k) ≠ 0 := by
      rw [oddGridCell_volume]
      exact (ENNReal.ofReal_pos.mpr (pow_pos hdelta d)).ne'
    have hfcell : MemLp (f : SpatialCoordinates d → ℝ) 2 (volume.restrict (q k)) :=
      MemLp.mono_measure (Measure.restrict_mono hsub le_rfl) (Lp.memLp f)
    have herrorrep : error =ᵐ[volume.restrict (q k)] fun x =>
        ENNReal.ofReal ((f x - averageOn (q k) f) ^ 2) := by
      have hsubrep := ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub
        (Lp.coeFn_sub f (cubeCellProjection z r hr m f))
      filter_upwards [hsubrep, cubeCellProjection_coeFn_on_cell z r hr m f k]
        with x hx hp
      simp only [error, hx, Pi.sub_apply, hp, q]
    have hjensen (x : SpatialCoordinates d) :
        ENNReal.ofReal ((f x - averageOn (q k) f) ^ 2) ≤
          invvol * ∫⁻ y in q k, ENNReal.ofReal ((f x - f y) ^ 2) := by
      have h := sq_sub_mean_le_lintegral_sq (volume.restrict (q k))
        (by simpa only [Measure.restrict_apply_univ] using hvol0) f hfcell x
      simpa only [Measure.restrict_apply_univ, Measure.real, averageOn, volumeAverage,
        q, invvol, delta, oddGridCell_volume] using h
    rw [lintegral_congr_ae herrorrep]
    calc
      (∫⁻ x in q k, ENNReal.ofReal ((f x - averageOn (q k) f) ^ 2)) ≤
          ∫⁻ x in q k, invvol * ∫⁻ y in q k, ENNReal.ofReal ((f x - f y) ^ 2) :=
        lintegral_mono hjensen
      _ ≤ ∫⁻ x in q k, invvol * (diam * ∫⁻ y in Q, kernel x y) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict (oddGridCell z r hr m k).isOpen.measurableSet]
          with x hx
        apply mul_le_mul_right
        calc
          (∫⁻ y in q k, ENNReal.ofReal ((f x - f y) ^ 2)) ≤
              ∫⁻ y in q k, diam * kernel x y := by
            apply lintegral_mono_ae
            filter_upwards [self_mem_ae_restrict (oddGridCell z r hr m k).isOpen.measurableSet]
              with y hy
            exact hpair k x y hx hy
          _ = diam * ∫⁻ y in q k, kernel x y := by
            rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hpower.le ENNReal.ofReal_ne_top)]
          _ ≤ diam * ∫⁻ y in Q, kernel x y := mul_le_mul_right (lintegral_mono_set hsub) _
      _ = invvol * diam * ∫⁻ x in q k, ∫⁻ y in Q, kernel x y := by
        simp_rw [← mul_assoc]
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top
          (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hdelta d)))
          (ENNReal.rpow_ne_top_of_nonneg hpower.le ENNReal.ofReal_ne_top))]
  have hpartition (F : SpatialCoordinates d → ℝ≥0∞) :
      (∫⁻ x in Q, F x) = ∑ k : OddGridIndex d m, ∫⁻ x in q k, F x := by
    rw [← setLIntegral_congr (oddGrid_union_ae_eq z hr m),
      lintegral_iUnion (fun k => (oddGridCell z r hr m k).isOpen.measurableSet)
        (oddGridCell_pairwiseDisjoint z hr m), tsum_fintype]
  rw [hnorm, hpartition]
  calc
    (∑ k : OddGridIndex d m, ∫⁻ x in q k, error x) ≤
        ∑ k : OddGridIndex d m, invvol * diam * ∫⁻ x in q k, ∫⁻ y in Q, kernel x y :=
      Finset.sum_le_sum (fun k _ => hcell k)
    _ = invvol * diam * ∫⁻ x in Q, ∫⁻ y in Q, kernel x y := by
      rw [← Finset.mul_sum, ← hpartition]
    _ = _ := rfl

end SubdiffusiveProcess
