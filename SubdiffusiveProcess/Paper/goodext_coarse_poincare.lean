import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Sobolev.CoarseEnergyArithmetic
import SubdiffusiveProcess.Paper.Foundations.Lane4.WeightedInJComparison
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.OneStepDatum
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.NormalizedL2




open Filter MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped Topology ENNReal NNReal

noncomputable section
namespace Paper

/-- Centering the native graph identifies its normalized L2 norm with the oscillation of any representative. -/
theorem aux_goodext_coarse_poincare_centered
    {d : ℕ} (hd : 2 ≤ d) (I : in_J d) (Pin : in_poincare d hd I)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (u : weakSobolevGraph (centeredCube z r hr))
    (U : SpatialCoordinates d → ℝ)
    (hU : ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] U)) :
    normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
      (fun x => U x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
        ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), U y) ≤
      Pin.C * r * (I.lam z r hr a z r 1 1) ^ (-(1 / 2) : ℝ) *
        normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
          (sobolevGradient u.val) := by
  obtain ⟨w, hw, hgrad⟩ := Pin.centered_representative z r hr u
  have havg : setAverage (centeredCube z r hr : Set (SpatialCoordinates d)) u.val.1 =
      (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
        ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), U y := by
    unfold setAverage
    rw [Measure.restrict_restrict (centeredCube z r hr).isOpen.measurableSet,
      Set.inter_self, integral_congr_ae hU]
  have hrep : ((w.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun x => U x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
          ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), U y)) := by
    filter_upwards [hw, hU] with x hx hu
    rw [hx, hu, havg]
  have hnorm := Section6SchauderDatum.normalizedL2On_congr_ae hrep
  have hpin := Pin.poincare_meanZero_all_radii z r hr a w
  rw [hgrad] at hpin
  rw [← hnorm, Section6Iteration.normalizedL2On_eq_toReal_eLpNorm_div (Lp.memLp w.val.1)]
  simpa only [Lp.norm_def, measureReal_def] using hpin

/-- The good-cell q=2 ellipticity lower bound controls centered oscillation through the actual cutoff energy. -/
theorem goodext_coarse_poincare
    {d : ℕ} (hd : 2 ≤ d) (I : in_J d) (Pin : in_poincare d hd I)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (u : weakSobolevGraph (centeredCube z r hr))
    (U : SpatialCoordinates d → ℝ)
    (hU : ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] U))
    (sigma cell s : ℝ) (hsigma : 0 < sigma) (hsigma1 : 2 * sigma ≤ 1)
    (hcell : 0 < cell) (hs : 0 < s)
    (hell : cell * s ≤ I.lam z r hr a z r sigma 2) :
    normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
      (fun x => U x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
        ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), U y) ≤
      Pin.C * r *
        ((Homogenization.Book.Ch02.geometricDiscount sigma 2 /
          Homogenization.Book.Ch02.geometricDiscount 1 1) * (cell * s)) ^ (-(1 / 2) : ℝ) *
        Real.sqrt (localGradientEnergy a (centeredCube z r hr).isOpen.measurableSet
          (sobolevGradient u.val) /
            volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  let c := Homogenization.Book.Ch02.geometricDiscount sigma 2 /
    Homogenization.Book.Ch02.geometricDiscount 1 1
  have hc : 0 < c := div_pos
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by positivity))
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by norm_num))
  have hcompare := (inJ_q_comparison hd I z r hr a z r hr (Subset.rfl)
    hsigma hsigma1 le_rfl).2
  have hlower : c * (cell * s) ≤ I.lam z r hr a z r 1 1 :=
    (mul_le_mul_of_nonneg_left hell hc.le).trans hcompare
  have hpow : (I.lam z r hr a z r 1 1) ^ (-(1 / 2) : ℝ) ≤
      (c * (cell * s)) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hc (mul_pos hcell hs)) hlower (by norm_num)
  exact (aux_goodext_coarse_poincare_centered hd I Pin z r hr a u U hU).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (mul_nonneg Pin.C_pos.le hr.le))
      (Real.sqrt_nonneg _))

/-- The coarse Poincare inequality in the squared form used by the energy-measure limit. -/
theorem aux_goodext_coarse_poincare_squared
    {d : ℕ} (hd : 2 ≤ d) (I : in_J d) (Pin : in_poincare d hd I)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (u : weakSobolevGraph (centeredCube z r hr))
    (U : SpatialCoordinates d → ℝ)
    (hU : ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] U))
    (sigma cell s : ℝ) (hsigma : 0 < sigma) (hsigma1 : 2 * sigma ≤ 1)
    (hcell : 0 < cell) (hs : 0 < s)
    (hell : cell * s ≤ I.lam z r hr a z r sigma 2) :
    (normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d))
      (fun x => U x - (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
        ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), U y)) ^ 2 ≤
      (Pin.C ^ 2 * r ^ 2 *
        ((Homogenization.Book.Ch02.geometricDiscount sigma 2 /
          Homogenization.Book.Ch02.geometricDiscount 1 1) * cell)⁻¹ /
            volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) * s⁻¹ *
        localGradientEnergy a (centeredCube z r hr).isOpen.measurableSet
          (sobolevGradient u.val) := by
  have hc : 0 < Homogenization.Book.Ch02.geometricDiscount sigma 2 /
      Homogenization.Book.Ch02.geometricDiscount 1 1 := div_pos
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by positivity))
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by norm_num))
  apply sq_le_coarse_energy_of_le_sqrt
    (Section6Iteration.normalizedL2On_nonneg _ _) Pin.C_pos.le hr.le
    (mul_pos hc hcell) hs (localGradientEnergy_nonneg _ _ _)
    (centeredCube_volume_pos z hr)
  simpa only [mul_assoc] using goodext_coarse_poincare hd I Pin z r hr a u U hU
    sigma cell s hsigma hsigma1 hcell hs hell

end Paper
