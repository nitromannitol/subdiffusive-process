module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ProductOriginRecurrence

@[expose] public section

/-!
# Theta-perturbed ladder: inserting the good-scale product-error cap

The coefficient-generic recurrence has already been proved in
`ProductOriginRecurrence`.  This module performs only its monotone
substitution in the product homogenization-error slot.  It is the exact seam
at which the ordinary cutoff good-scale bound and the sensitivity
`sqrt epsilon` price enter the deterministic iteration.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} [NeZero d]

/-- Replace the literal product error in the origin-cube recurrence by any
larger nonnegative cap.  No PDE or recurrence argument is repeated here. -/
theorem productOrigin_excessRecurrence_of_errorCap
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B)
    {b epsilon alpha Ebase Ecap : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hb : 0 < b) (hepsilon : 0 < epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (n : ℤ) (k : ℕ) (hk : 6 ≤ k)
    (hparentB : cube d n ⊆ B)
    (u : H1Function (cube d n))
    (hu : IsWeaklyHarmonicOn
      (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * theta x)
      (cube d n) u)
    (hbaseParent : paperHomogenizationError
      (originCube d n) (originCube d n).scale
      ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
      (aCutoffFamily M L omega) alpha ≤ ENNReal.ofReal Ebase)
    (hbaseInner : paperHomogenizationError
      (originCube d (n - 2)) (originCube d (n - 2)).scale
      ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
      (aCutoffFamily M L omega) alpha ≤ ENNReal.ofReal Ebase)
    (hparentOne :
      (paperHomogenizationError
        (originCube d n) (originCube d n).scale
        ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
        (localizedThetaCoeffFamily M L omega hB theta htheta
          hepsilon.le (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha).toReal ≤ 1)
    (hproductError :
      (paperHomogenizationError
        (originCube d (n - 2)) (originCube d (n - 2)).scale
        ((3 / 16 : ℝ) / 6) .infinity (.finite 2)
        (localizedThetaCoeffFamily M L omega hB theta htheta
          hepsilon.le (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha).toReal ≤ Ecap)
    (ell : Affine d)
    (hell : ell ∈ affineMinimizers (cube d n) u.toFun) :
    excess (n - (k : ℤ)) (cube d (n - (k : ℤ))) u.toFun ≤
      oneStepContractionConst d * Section6Schauder.schauderInteriorConst d *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
          excess n (cube d n) u.toFun +
        productOriginRecurrenceErrorConstant d hd k * Ecap *
          (excess n (cube d n) u.toFun +
            Real.sqrt (d : ℝ) / 2 * Real.sqrt (vecNormSq ell.slope)) := by
  have hraw := productOrigin_excessRecurrence d hd M L omega hB theta htheta
    hb hepsilon hepsilonHalf hnear halpha n k hk hparentB u hu hbaseParent
    hbaseInner hparentOne ell hell
  have hcoef : 0 ≤ productOriginRecurrenceErrorConstant d hd k :=
    productOriginRecurrenceErrorConstant_nonneg d hd k
  have hparent : 0 ≤ excess n (cube d n) u.toFun := by
    rw [Section6Iteration.excess_eq_affineExcessScaled]
    exact Section6Iteration.affineExcessScaled_nonneg _ _ _
  have hslope : 0 ≤ Real.sqrt (vecNormSq ell.slope) := Real.sqrt_nonneg _
  have hbracket : 0 ≤ excess n (cube d n) u.toFun +
      Real.sqrt (d : ℝ) / 2 * Real.sqrt (vecNormSq ell.slope) := by
    positivity
  have hmono := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hproductError hcoef) hbracket
  exact hraw.trans (add_le_add le_rfl hmono)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
