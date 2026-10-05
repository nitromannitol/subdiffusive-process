module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSobolevNormalization
@[expose] public section

/-!
# Cube-average tests and a volume ratio supply the weighted mass ratio.
-/

set_option autoImplicit false
open Homogenization MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Cube-average tests and a volume ratio supply the weighted mass ratio. -/
theorem goodCube_mass_ratio_of_average_bounds
    {d : ℕ} {U V : Set (Vec d)} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hU0 : volume U ≠ 0) (hUt : volume U ≠ ⊤)
    (hV0 : volume V ≠ 0) (hVt : volume V ≠ ⊤)
    {a : Vec d → ℝ} (haU : IntegrableOn a U) (haV : IntegrableOn a V)
    (hnU : ∀ᵐ x ∂volume.restrict U, 0 ≤ a x)
    (hnV : ∀ᵐ x ∂volume.restrict V, 0 ≤ a x)
    {theta : ℝ} (htheta : 0 ≤ theta)
    (hvol : ENNReal.ofReal theta * volume V ≤ volume U)
    (hlower : (1 / 2 : ℝ) ≤ volumeAverage U a)
    (hupper : volumeAverage V a ≤ 3 / 2) :
    ENNReal.ofReal (theta / 3) * weightedMeasure a V ≤ weightedMeasure a U := by
  have hVe : weightedMeasure a V
      = ENNReal.ofReal (volumeAverage V a) * volume V :=
    goodCube_weightedMeasure_eq_volume_mul_average hV hV0 hVt haV hnV
  have hUe : weightedMeasure a U
      = ENNReal.ofReal (volumeAverage U a) * volume U :=
    goodCube_weightedMeasure_eq_volume_mul_average hU hU0 hUt haU hnU
  rw [hUe, hVe]
  calc ENNReal.ofReal (theta / 3) * (ENNReal.ofReal (volumeAverage V a) * volume V)
      ≤ ENNReal.ofReal (theta / 3) * (ENNReal.ofReal ((3 : ℝ) / 2) * volume V) := by
        gcongr
    _ = ENNReal.ofReal ((1 : ℝ) / 2) * (ENNReal.ofReal theta * volume V) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg htheta (by norm_num)),
          show theta / 3 * ((3 : ℝ) / 2) = (1 / 2 : ℝ) * theta by ring,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_assoc]
    _ ≤ ENNReal.ofReal ((1 : ℝ) / 2) * volume U := mul_le_mul_right hvol _
    _ ≤ ENNReal.ofReal (volumeAverage U a) * volume U :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hlower) _

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
