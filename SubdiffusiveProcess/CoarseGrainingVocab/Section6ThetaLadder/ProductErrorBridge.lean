import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.GoodScaleError
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.PaperErrorBridge

/-!
# Theta-perturbed ladder: paper error to Chapter 2 error

The product response estimate is an `ENNReal` paper error, whereas the sharp
flat-comparator theorem consumes Chapter 2's real-valued `q = 2` error.  The
base-error cap makes the product paper error finite, so the existing
full-block-to-scalar-probe comparison may be read back through `toReal`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Homogenization Homogenization.Book
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A finite cap on the base paper error also makes the localized product
paper error finite. -/
theorem paperHomogenizationError_localizedTheta_ne_top_of_base_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B)
    {b epsilon alpha s E : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (hs : 0 < s) (Q : TriadicCube d)
    (hbase : paperHomogenizationError Q Q.scale s .infinity (.finite 2)
      (aCutoffFamily M L omega) alpha ≤ ENNReal.ofReal E) :
    paperHomogenizationError Q Q.scale s .infinity (.finite 2)
      (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
        (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha ≠ ⊤ := by
  have hraw := paperHomogenizationError_localizedTheta_le_add_sqrt
    M L omega hB theta htheta hepsilon hepsilonHalf hnear halpha hs Q Q.scale
  let A : ℝ≥0∞ := ENNReal.ofReal (1 + 16 * epsilon) ^ (1 / 2 : ℝ)
  let D : ℝ≥0∞ := ENNReal.ofReal (15 * epsilon) ^ (1 / 2 : ℝ)
  have hcap : paperHomogenizationError Q Q.scale s .infinity (.finite 2)
        (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
          (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha ≤
      A * ENNReal.ofReal E + D :=
    hraw.trans (add_le_add (mul_le_mul_right hbase A) le_rfl)
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top,
       ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top⟩)
    hcap

/-- The Chapter 2 full-block error of the product family is bounded by the
literal real-valued product paper error. -/
theorem homogenizationErrorOnCube_localizedTheta_le_paper_toReal
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B)
    {b epsilon alpha s E : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (hs : 0 < s) (Q : TriadicCube d)
    (hbase : paperHomogenizationError Q Q.scale s .infinity (.finite 2)
      (aCutoffFamily M L omega) alpha ≤ ENNReal.ofReal E) :
    Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2)
        (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
          (hepsilonHalf.trans_lt (by norm_num)) hnear)
        (scalarMatrix (d := d) alpha) ≤
      (paperHomogenizationError Q Q.scale s .infinity (.finite 2)
        (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
          (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha).toReal := by
  let F := localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
    (hepsilonHalf.trans_lt (by norm_num)) hnear
  have htop : paperHomogenizationError Q Q.scale s .infinity (.finite 2)
      F alpha ≠ ⊤ := by
    exact paperHomogenizationError_localizedTheta_ne_top_of_base_le
      M L omega hB theta htheta hepsilon hepsilonHalf hnear halpha hs Q hbase
  have hraw :=
    Section6HarmonicApproximation.ofReal_homogenizationErrorOnCube_infinity_two_le_paper
      Q F (fun R ↦
        (localizedThetaTriadicCoeffData M L omega hB theta htheta hepsilon.le
          (hepsilonHalf.trans_lt (by norm_num)) hnear).onCube R |>.isSymmetric)
      hs halpha
  exact (ENNReal.ofReal_le_iff_le_toReal htop).mp hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
