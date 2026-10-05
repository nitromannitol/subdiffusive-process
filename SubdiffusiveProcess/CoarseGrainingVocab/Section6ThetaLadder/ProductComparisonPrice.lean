module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorBudgetReadout

@[expose] public section

/-!
# Theta-perturbed ladder: fixed-order comparison price

At zero forcing, the exact local coarse-graining budget is linear in the
product homogenization error and in the weighted root-energy price.  This
file removes the unused forcing branch at the fixed manuscript orders.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

/-- Dimension-only fixed-order coefficient in the zero-forcing local
coarse-graining budget. -/
def productFlatLinearConstant (C : ℝ≥0∞) : ℝ :=
  Real.rpow productMiddleOrder.1 (-(1 / 2 : ℝ)) *
    C.toReal * productMiddleOrder.1⁻¹ *
    Real.rpow 3 productLowOrder.1

theorem productFlatLinearConstant_nonneg (C : ℝ≥0∞) :
    0 ≤ productFlatLinearConstant C := by
  unfold productFlatLinearConstant productMiddleOrder productLowOrder
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) ENNReal.toReal_nonneg)
      (inv_nonneg.mpr (by norm_num)))
    (Real.rpow_nonneg (by norm_num) _)

/-- The fixed-order, zero-forcing local comparator budget is linear in its
error and energy slots. -/
theorem productFlatLocalCoarseBound_toReal_le
    (C : ℝ≥0∞) {alpha E S : ℝ} (n : ℤ)
    (halpha : 0 < alpha) (hE : 0 ≤ E) (hS : 0 ≤ S) :
    (flatComparatorLocalCoarseBound C alpha
      productMiddleOrder productLowOrder productHighOrder
      E E S 0 n).toReal ≤
        productFlatLinearConstant C * Real.sqrt alpha * E * S := by
  have hraw := flatComparatorLocalCoarseBound_toReal_le
    C alpha productMiddleOrder productLowOrder productHighOrder
      E E S 0 n (by
        norm_num [productMiddleOrder, productHighOrder])
      halpha hE hE hS le_rfl
  simp only [mul_zero, add_zero] at hraw
  calc
    _ ≤ Real.rpow productMiddleOrder.1 (-(1 / 2 : ℝ)) *
        (C.toReal * productMiddleOrder.1⁻¹ * Real.sqrt alpha *
          Real.rpow 3 productLowOrder.1 * E * S) := hraw
    _ = productFlatLinearConstant C * Real.sqrt alpha * E * S := by
      unfold productFlatLinearConstant
      ring

/-- Monotone outer spectral readout for a nonnegative real local budget. -/
theorem productSpectralReadout_mono {d : ℕ} [NeZero d]
    {alpha R S : ℝ} (halpha : 0 < alpha) (hR : 0 ≤ R) (hRS : R ≤ S) :
    (flatComparatorSharpSpectralConstant d *
        ENNReal.ofReal (alpha⁻¹ * R)).toReal ≤
      (flatComparatorSharpSpectralConstant d).toReal * alpha⁻¹ * S := by
  have hscale : 0 ≤ alpha⁻¹ := inv_nonneg.mpr halpha.le
  have hmono : ENNReal.ofReal (alpha⁻¹ * R) ≤
      ENNReal.ofReal (alpha⁻¹ * S) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hRS hscale)
  have htop : flatComparatorSharpSpectralConstant d ≠ ∞ :=
    (flatComparatorSharpSpectralConstant_lt_top d).ne
  have hmulENN : flatComparatorSharpSpectralConstant d *
      ENNReal.ofReal (alpha⁻¹ * R) ≤
      flatComparatorSharpSpectralConstant d *
        ENNReal.ofReal (alpha⁻¹ * S) := by
    gcongr
  have hmul := ENNReal.toReal_mono
    (ENNReal.mul_ne_top htop ENNReal.ofReal_ne_top)
    hmulENN
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg hscale hR),
    ENNReal.toReal_ofReal (mul_nonneg hscale (hR.trans hRS))] at hmul
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg hscale hR)]
  calc
    _ ≤ (flatComparatorSharpSpectralConstant d).toReal *
        (alpha⁻¹ * S) := hmul
    _ = _ := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
