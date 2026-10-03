module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ErrorAggregation

@[expose] public section

/-!
# Theta-perturbed cutoff Hölder ladder: the good-scale error cap

This is the real-valued form of the manuscript's response sensitivity row.
It is stated with an abstract cap on the unperturbed paper error so that the
ordinary cutoff good-scale theorem can be inserted without changing the
theta recurrence.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Homogenization Homogenization.Book
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- On a base good scale, the theta error is the old error cap plus the
single `sqrt ε` sensitivity price. -/
theorem paperHomogenizationError_localizedTheta_toReal_le_of_base_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B) {b epsilon alpha s E : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (hs : 0 < s) (hE : 0 ≤ E)
    (Q : TriadicCube d) (n : ℤ)
    (hbase : paperHomogenizationError Q n s .infinity (.finite 2)
      (aCutoffFamily M L omega) alpha ≤ ENNReal.ofReal E) :
    (paperHomogenizationError Q n s .infinity (.finite 2)
      (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
        (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha).toReal ≤
      Real.sqrt (1 + 16 * epsilon) * E + Real.sqrt (15 * epsilon) := by
  let Et : ℝ≥0∞ := paperHomogenizationError Q n s .infinity (.finite 2)
    (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
      (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha
  let E0 : ℝ≥0∞ := paperHomogenizationError Q n s .infinity (.finite 2)
    (aCutoffFamily M L omega) alpha
  let A : ℝ≥0∞ := ENNReal.ofReal (1 + 16 * epsilon) ^ (1 / 2 : ℝ)
  let D : ℝ≥0∞ := ENNReal.ofReal (15 * epsilon) ^ (1 / 2 : ℝ)
  have hraw : Et ≤ A * E0 + D := by
    exact paperHomogenizationError_localizedTheta_le_add_sqrt M L omega hB
      theta htheta hepsilon hepsilonHalf hnear halpha hs Q n
  have hmono : A * E0 + D ≤ A * ENNReal.ofReal E + D := by
    exact add_le_add (mul_le_mul_right hbase A) le_rfl
  have hAtop : A ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hDtop : D ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hrightTop : A * ENNReal.ofReal E + D ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hAtop ENNReal.ofReal_ne_top, hDtop⟩
  have hreal := ENNReal.toReal_mono hrightTop (hraw.trans hmono)
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hAtop ENNReal.ofReal_ne_top) hDtop,
    ENNReal.toReal_mul] at hreal
  dsimp only [A, D] at hreal
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hE,
    ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 + 16 * epsilon),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 15 * epsilon)] at hreal
  simpa only [Et, Real.sqrt_eq_rpow] using hreal

/-- Manuscript good-scale form of the preceding estimate.  If the ordinary
error is bounded by `K * eta`, then the multiplier changes that cap by at most
a constant (depending on `K`, hence ultimately only on the dimension) times
`sqrt epsilon`. -/
theorem paperHomogenizationError_localizedTheta_toReal_le_goodScale
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B) {b epsilon alpha s eta K : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (hs : 0 < s) (heta : 0 ≤ eta)
    (hetaOne : eta ≤ 1) (hK : 0 ≤ K)
    (Q : TriadicCube d) (n : ℤ)
    (hbase : paperHomogenizationError Q n s .infinity (.finite 2)
      (aCutoffFamily M L omega) alpha ≤ ENNReal.ofReal (K * eta)) :
    (paperHomogenizationError Q n s .infinity (.finite 2)
      (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
        (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha).toReal ≤
      K * eta + (8 * K + Real.sqrt 15) * Real.sqrt epsilon := by
  have hKeta : 0 ≤ K * eta := mul_nonneg hK heta
  have hraw := paperHomogenizationError_localizedTheta_toReal_le_of_base_le
    M L omega hB theta htheta hepsilon hepsilonHalf hnear halpha hs hKeta Q n hbase
  have hsqrtCoeff : Real.sqrt (1 + 16 * epsilon) ≤ 1 + 8 * epsilon := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hepsilonOne : epsilon ≤ 1 := hepsilonHalf.trans (by norm_num)
  have hsqrtEpsilonOne : Real.sqrt epsilon ≤ 1 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by simpa using hepsilonOne⟩
  have hepsilonSqrt : epsilon ≤ Real.sqrt epsilon := by
    nlinarith [Real.sq_sqrt hepsilon.le, Real.sqrt_nonneg epsilon]
  have hKetaK : K * eta ≤ K := by
    nlinarith
  have hepsKeta : epsilon * (K * eta) ≤ Real.sqrt epsilon * K := by
    calc
      epsilon * (K * eta) ≤ Real.sqrt epsilon * (K * eta) :=
        mul_le_mul_of_nonneg_right hepsilonSqrt hKeta
      _ ≤ Real.sqrt epsilon * K :=
        mul_le_mul_of_nonneg_left hKetaK (Real.sqrt_nonneg epsilon)
  have hsqrtProduct : Real.sqrt (15 * epsilon) = Real.sqrt 15 * Real.sqrt epsilon := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 15)]
  have hcoeffMul :
      Real.sqrt (1 + 16 * epsilon) * (K * eta) ≤
        K * eta + 8 * (Real.sqrt epsilon * K) := by
    calc
      Real.sqrt (1 + 16 * epsilon) * (K * eta) ≤
          (1 + 8 * epsilon) * (K * eta) :=
        mul_le_mul_of_nonneg_right hsqrtCoeff hKeta
      _ = K * eta + 8 * (epsilon * (K * eta)) := by ring
      _ ≤ K * eta + 8 * (Real.sqrt epsilon * K) := by
        gcongr
  rw [hsqrtProduct] at hraw
  calc
    _ ≤ Real.sqrt (1 + 16 * epsilon) * (K * eta) +
        Real.sqrt 15 * Real.sqrt epsilon := hraw
    _ ≤ K * eta + 8 * (Real.sqrt epsilon * K) +
        Real.sqrt 15 * Real.sqrt epsilon := add_le_add hcoeffMul le_rfl
    _ = K * eta + (8 * K + Real.sqrt 15) * Real.sqrt epsilon := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
