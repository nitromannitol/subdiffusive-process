import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.FamilySensitivity
import SubdiffusiveProcess.CoarseGrainingVocab.Section6AnnularCarrier
import Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation.Geometric

/-!
# Theta-perturbed cutoff Hölder ladder: multiscale response aggregation

This module performs the `q = 2`, `p = ∞` weighted aggregation following the
cube-wise sensitivity estimate.  The additive perturbation is paid once
because the geometric weights have total mass one.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Homogenization Homogenization.Book
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The descendant-scale maximum inherits the same affine response bound. -/
theorem paperMaxDescendantProbeAtScale_localizedTheta_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B) {b epsilon alpha : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (Q : TriadicCube d) (k : ℤ) :
    paperMaxDescendantProbeAtScale Q k
        (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
          (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha ≤
      ENNReal.ofReal (1 + 16 * epsilon) *
          paperMaxDescendantProbeAtScale Q k (aCutoffFamily M L omega) alpha +
        ENNReal.ofReal (15 * epsilon) := by
  unfold paperMaxDescendantProbeAtScale
  refine iSup_le fun R ↦ ?_
  have hR := paperScalarProbeMax_localizedTheta_le M L omega hB theta htheta
    hepsilon hepsilonHalf hnear halpha R
  have hsup := le_iSup
    (fun S : {S : TriadicCube d // S ∈ descendantsAtScale Q k} ↦
      paperScalarProbeMax S (aCutoffFamily M L omega) alpha) R
  have hmul : ENNReal.ofReal (1 + 16 * epsilon) *
      paperScalarProbeMax R (aCutoffFamily M L omega) alpha ≤
      ENNReal.ofReal (1 + 16 * epsilon) *
        (⨆ S : {S : TriadicCube d // S ∈ descendantsAtScale Q k},
          paperScalarProbeMax S (aCutoffFamily M L omega) alpha) := by
    exact mul_le_mul_right hsup (ENNReal.ofReal (1 + 16 * epsilon))
  exact hR.trans (by
    simpa only [add_comm] using
      add_le_add_right hmul (ENNReal.ofReal (15 * epsilon)))

/-- Weighted-series form of the theta response bound. -/
theorem weightedSeries_localizedTheta_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B) {b epsilon alpha s : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (hs : 0 < s) (Q : TriadicCube d) (n : ℤ) :
    (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
        paperMaxDescendantProbeAtScale Q (n - (l : ℤ))
          (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
            (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha) ≤
      ENNReal.ofReal (1 + 16 * epsilon) *
          (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
            paperMaxDescendantProbeAtScale Q (n - (l : ℤ))
              (aCutoffFamily M L omega) alpha) +
        ENNReal.ofReal (15 * epsilon) := by
  let A : ℝ≥0∞ := ENNReal.ofReal (1 + 16 * epsilon)
  let D : ℝ≥0∞ := ENNReal.ofReal (15 * epsilon)
  let w : ℕ → ℝ≥0∞ := fun l ↦ ENNReal.ofReal (Ch02.geometricWeight s 2 l)
  let X : ℕ → ℝ≥0∞ := fun l ↦
    paperMaxDescendantProbeAtScale Q (n - (l : ℤ))
      (aCutoffFamily M L omega) alpha
  let Y : ℕ → ℝ≥0∞ := fun l ↦
    paperMaxDescendantProbeAtScale Q (n - (l : ℤ))
      (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
        (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha
  have hpoint : ∀ l, Y l ≤ A * X l + D := by
    intro l
    exact paperMaxDescendantProbeAtScale_localizedTheta_le M L omega hB
      theta htheta hepsilon hepsilonHalf hnear halpha Q (n - (l : ℤ))
  have hwReal : Summable (fun l : ℕ ↦ Ch02.geometricWeight s 2 l) := by
    simpa only [Ch02.geometricWeight_eq_old] using
      (Homogenization.summable_geometricWeight (s := s) (q := 2) (by positivity))
  have hwSum : ∑' l : ℕ, w l = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · rw [show (∑' l : ℕ, Ch02.geometricWeight s 2 l) = 1 by
        simpa only [Ch02.geometricWeight_eq_old] using
          (Homogenization.tsum_geometricWeight_eq_one
            (s := s) (q := 2) (by positivity))]
      simp
    · intro l
      exact Homogenization.geometricWeight_nonneg l (by positivity)
    · exact hwReal
  calc
    ∑' l : ℕ, w l * Y l ≤ ∑' l : ℕ, w l * (A * X l + D) :=
      ENNReal.tsum_le_tsum fun l ↦ by
        exact mul_le_mul_right (hpoint l) (w l)
    _ = ∑' l : ℕ, (A * (w l * X l) + D * w l) := by
      refine tsum_congr fun l ↦ ?_
      ring
    _ = A * (∑' l : ℕ, w l * X l) + D * (∑' l : ℕ, w l) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ = A * (∑' l : ℕ, w l * X l) + D := by rw [hwSum, mul_one]

/-- The exact finite-`q = 2` homogenization error of the localized theta
family is controlled by the base error plus one additive response price. -/
theorem paperHomogenizationError_localizedTheta_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B) {b epsilon alpha s : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (hs : 0 < s) (Q : TriadicCube d) (n : ℤ) :
    paperHomogenizationError Q n s .infinity (.finite 2)
        (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
          (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha ≤
      (ENNReal.ofReal (1 + 16 * epsilon) *
          paperHomogenizationError Q n s .infinity (.finite 2)
            (aCutoffFamily M L omega) alpha ^ (2 : ℝ) +
        ENNReal.ofReal (15 * epsilon)) ^ (1 / 2 : ℝ) := by
  rw [paperHomogenizationError_infinity_two_eq_weighted_series,
    paperHomogenizationError_infinity_two_eq_weighted_series]
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  have hseries := weightedSeries_localizedTheta_le M L omega hB theta htheta
    hepsilon hepsilonHalf hnear halpha hs Q n
  refine hseries.trans_eq ?_
  congr 2
  rw [← ENNReal.rpow_mul]
  norm_num

/-- Minkowski form of the response perturbation.  This is the manuscript's
`(1 + C ε) 𝓔 + C ε^(1/2)` row, kept in `ℝ≥0∞` so no finiteness premise is
needed. -/
theorem paperHomogenizationError_localizedTheta_le_add_sqrt
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B) {b epsilon alpha s : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (hs : 0 < s) (Q : TriadicCube d) (n : ℤ) :
    paperHomogenizationError Q n s .infinity (.finite 2)
        (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
          (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha ≤
      ENNReal.ofReal (1 + 16 * epsilon) ^ (1 / 2 : ℝ) *
          paperHomogenizationError Q n s .infinity (.finite 2)
            (aCutoffFamily M L omega) alpha +
        ENNReal.ofReal (15 * epsilon) ^ (1 / 2 : ℝ) := by
  let E : ℝ≥0∞ := paperHomogenizationError Q n s .infinity (.finite 2)
    (aCutoffFamily M L omega) alpha
  let A : ℝ≥0∞ := ENNReal.ofReal (1 + 16 * epsilon)
  let D : ℝ≥0∞ := ENNReal.ofReal (15 * epsilon)
  have hraw := paperHomogenizationError_localizedTheta_le M L omega hB theta
    htheta hepsilon hepsilonHalf hnear halpha hs Q n
  change _ ≤ A ^ (1 / 2 : ℝ) * E + D ^ (1 / 2 : ℝ)
  refine hraw.trans ((ENNReal.rpow_add_le_add_rpow (A * E ^ (2 : ℝ)) D
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_mul]
  norm_num

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
