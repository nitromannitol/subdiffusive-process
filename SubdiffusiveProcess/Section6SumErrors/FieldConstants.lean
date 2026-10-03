module

public import SubdiffusiveProcess.Section6SumErrors.RowConstants
public import SubdiffusiveProcess.Section6SumErrors.WindowFluctuation

@[expose] public section

/-!
# FieldConstants

Dimension-only coefficient bounds for the finite-field and gradient scales, with elementary order and logarithm comparisons.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
noncomputable section

/-- A dimension-only coefficient for the finite-field scale. -/
def fieldBase (d : ℕ) : ℝ :=
  Ch04.gammaTriangleConst 2 *
    (1 + |holderErrorFieldCubeCoeff d| + 1024 * |holderErrorFieldGammaCoeff d|)

theorem fieldBase_pos (d : ℕ) : 0 < fieldBase d := by
  unfold fieldBase
  exact mul_pos IndependentSums.gammaTriangleConst_pos (by positivity)

theorem finiteFieldScale_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) :
    accumulatedFiniteFieldScaleBound M s ≤ fieldBase d * (s ^ 2)⁻¹ * M.delta := by
  let t := s / 8
  have ht : 0 < t := by dsimp only [t]; positivity
  have ht1 : t ≤ 1 := by dsimp only [t]; linarith
  have hroot : t ≤ Real.sqrt t := by
    rw [Real.le_sqrt ht.le ht.le]
    nlinarith
  have hi : (Real.sqrt t)⁻¹ ≤ t⁻¹ :=
    (inv_le_inv₀ (Real.sqrt_pos.mpr ht) ht).2 hroot
  have hw : (Real.sqrt (s / 8))⁻¹ * (s / 8)⁻¹ ≤ 64 * (s ^ 2)⁻¹ := by
    calc
      _ ≤ t⁻¹ * t⁻¹ := mul_le_mul_of_nonneg_right hi (inv_nonneg.mpr ht.le)
      _ = 64 * (s ^ 2)⁻¹ := by dsimp only [t]; field_simp [hs.ne']; ring
  have hs2 : 1 ≤ (s ^ 2)⁻¹ := (one_le_inv₀ (sq_pos_of_pos hs)).2 (by nlinarith)
  have hc : fieldOneCubeMajorantScale M 0 0 = holderErrorFieldCubeCoeff d * M.delta := by
    unfold fieldOneCubeMajorantScale holderErrorFieldCubeCoeff
    norm_num
    ring
  have hg := fieldOneGammaScale_eq_coeff_mul M
  have hcube : fieldOneCubeMajorantScale M 0 0 ≤
      |holderErrorFieldCubeCoeff d| * (s ^ 2)⁻¹ * M.delta := by
    rw [hc]
    exact mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hs2))
      M.shellPrefix.delta_pos.le
  have hd0 := M.shellPrefix.delta_pos.le
  have htri : 0 ≤ Ch04.gammaTriangleConst 2 := IndependentSums.gammaTriangleConst_pos.le
  have hgrad : 16 * fieldOneGammaDimScale M *
      ((Real.sqrt (s / 8))⁻¹ * (s / 8)⁻¹) ≤
      16 * (|holderErrorFieldGammaCoeff d| * M.delta) * (64 * (s ^ 2)⁻¹) := by
    have hcoeff : fieldOneGammaDimScale M ≤ |holderErrorFieldGammaCoeff d| * M.delta := by
      rw [hg]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) M.shellPrefix.delta_pos.le
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hcoeff (by norm_num)
    · exact hw
    · positivity
    · positivity
  unfold accumulatedFiniteFieldScaleBound fieldBase
  calc
    _ = Ch04.gammaTriangleConst 2 * (fieldOneCubeMajorantScale M 0 0 +
        16 * fieldOneGammaDimScale M * ((Real.sqrt (s / 8))⁻¹ * (s / 8)⁻¹)) := by ring
    _ ≤ Ch04.gammaTriangleConst 2 *
        (|holderErrorFieldCubeCoeff d| * (s ^ 2)⁻¹ * M.delta +
          16 * (|holderErrorFieldGammaCoeff d| * M.delta) * (64 * (s ^ 2)⁻¹)) :=
      mul_le_mul_of_nonneg_left (add_le_add hcube hgrad) htri
    _ ≤ _ := by
      have hn : 0 ≤ Ch04.gammaTriangleConst 2 * (s ^ 2)⁻¹ * M.delta := by positivity
      have he : Ch04.gammaTriangleConst 2 *
          (1 + |holderErrorFieldCubeCoeff d| + 1024 * |holderErrorFieldGammaCoeff d|) *
          (s ^ 2)⁻¹ * M.delta =
          Ch04.gammaTriangleConst 2 *
            (|holderErrorFieldCubeCoeff d| * (s ^ 2)⁻¹ * M.delta +
              16 * (|holderErrorFieldGammaCoeff d| * M.delta) * (64 * (s ^ 2)⁻¹)) +
          Ch04.gammaTriangleConst 2 * (s ^ 2)⁻¹ * M.delta := by ring
      rw [he]
      exact le_add_of_nonneg_right hn

/-- All non-response terms are paid by a dimension-only coefficient. -/
def fieldGammaBase (d : ℕ) : ℝ := 1 + |holderErrorFieldGammaCoeff d|
/-- A dimension-only coefficient for the gradient row scale. -/
def gradientBase (d : ℕ) : ℝ := 1 + |holderErrorGradientOwnCoeff d|
/-- A dimension-only coefficient for the gradient envelope scale. -/
def gradientTailBase (d : ℕ) : ℝ := 1 + |holderErrorGradientEnvelopeCoeff d|

theorem fieldGammaScale_le {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    fieldOneGammaDimScale M ≤ fieldGammaBase d * M.delta := by
  rw [fieldOneGammaScale_eq_coeff_mul]
  apply mul_le_mul_of_nonneg_right _ M.shellPrefix.delta_pos.le
  unfold fieldGammaBase
  linarith [le_abs_self (holderErrorFieldGammaCoeff d)]

theorem gradientScale_le {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    accumulatedGradientOwnRowScale M ≤ gradientBase d * M.delta := by
  rw [gradientOwnScale_eq_coeff_mul]
  apply mul_le_mul_of_nonneg_right _ M.shellPrefix.delta_pos.le
  unfold gradientBase
  linarith [le_abs_self (holderErrorGradientOwnCoeff d)]

theorem gradientTailScale_le {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    accumulatedGradientEnvelopeScale M ≤ gradientTailBase d * M.delta := by
  rw [gradientEnvelopeScale_eq_coeff_mul]
  apply mul_le_mul_of_nonneg_right _ M.shellPrefix.delta_pos.le
  unfold gradientTailBase
  linarith [le_abs_self (holderErrorGradientEnvelopeCoeff d)]

theorem inv_pow_le_order {s a : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (n : ℕ) (ha : a ≤ -(n : ℝ)) : (s ^ n)⁻¹ ≤ s ^ a := by
  rw [inv_pow_eq_rpow s hs]
  exact Real.rpow_le_rpow_of_exponent_ge hs hs1 ha

theorem inv_pow_mul_rpow {s a : ℝ} (hs : 0 < s) (n : ℕ) :
    (s ^ n)⁻¹ * s ^ a = s ^ (a - n) := by
  rw [inv_pow_eq_rpow s hs, ← Real.rpow_add hs]
  congr 1
  ring

theorem delta_le_logScale {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    M.delta ≤ holderLogAbsorption * M.delta * Real.sqrt |Real.log M.delta| := by
  have hlog := one_add_sqrt_abs_log_le_holderLogAbsorption_mul M
  have hr := Real.sqrt_nonneg |Real.log M.delta|
  have h1 : 1 ≤ holderLogAbsorption * Real.sqrt |Real.log M.delta| := by linarith
  have hp := mul_le_mul_of_nonneg_left h1 M.shellPrefix.delta_pos.le
  simpa only [mul_one, mul_assoc, mul_left_comm, mul_comm] using hp

end
end SubdiffusiveProcess.Section6SumErrors.Response
