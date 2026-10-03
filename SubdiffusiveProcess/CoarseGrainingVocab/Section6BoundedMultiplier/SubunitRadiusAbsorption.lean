module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubunitGeometry

@[expose] public section

/-!
# Deterministic absorption of the below-scale random radius

On the restricted gradient-good event, the logarithmic Lipschitz threshold
grows at most like `3^m`.  Consequently the adaptive small-contrast radius is
bounded below by a dimension-only constant times `3^{-m}`.  This is the
pre-threshold price absorbed by the scale-one Campanato factor.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

/-- Dimension-only coefficient in the crude exponential growth bound for the
restricted logarithmic-gradient threshold. -/
def boundedMultiplierRadiusGrowthConst (d : ℕ) : ℝ :=
  fixedCutoffOscillationConst / 2 *
    (Real.sqrt (shellCoverLogConst * (d : ℝ)) + (Real.log 2)⁻¹)

theorem boundedMultiplierRadiusGrowthConst_pos (d : ℕ) :
    0 < boundedMultiplierRadiusGrowthConst d := by
  unfold boundedMultiplierRadiusGrowthConst
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcover : 0 ≤ shellCoverLogConst * (d : ℝ) :=
    mul_nonneg shellCoverLogConst_pos.le (Nat.cast_nonneg d)
  exact mul_pos (div_pos fixedCutoffOscillationConst_pos (by norm_num))
    (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _)
      (inv_pos.mpr hlog))

/-- Dimension-only threshold coefficient for negative parent scales.  In
that regime the cover radius is definitionally one, hence the cover has
exactly `3^d` shifts. -/
def boundedMultiplierNegativeRadiusGrowthConst (d : ℕ) : ℝ :=
  fixedCutoffOscillationConst / 2 *
    (Real.sqrt (Real.log ((3 : ℝ) ^ d)) + (Real.log 2)⁻¹)

theorem boundedMultiplierNegativeRadiusGrowthConst_pos (d : ℕ) :
    0 < boundedMultiplierNegativeRadiusGrowthConst d := by
  unfold boundedMultiplierNegativeRadiusGrowthConst
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact mul_pos (div_pos fixedCutoffOscillationConst_pos (by norm_num))
    (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (inv_pos.mpr hlog))

/-- Radius floor for the direct negative-parent-scale branch. -/
def boundedMultiplierNegativeRadiusFloor (d : ℕ) : ℝ :=
  min (6 : ℝ)⁻¹
    (min (1 / 4 : ℝ)
      (boundedMultiplierEpsilonStar d /
        (1 + boundedMultiplierNegativeRadiusGrowthConst d)))

theorem boundedMultiplierNegativeRadiusFloor_pos (d : ℕ) :
    0 < boundedMultiplierNegativeRadiusFloor d := by
  unfold boundedMultiplierNegativeRadiusFloor
  apply lt_min (by norm_num)
  apply lt_min (by norm_num)
  exact div_pos (boundedMultiplierEpsilonStar_pos d)
    (by linarith [boundedMultiplierNegativeRadiusGrowthConst_pos d])

/-- Dimension-only floor for the localization radius after the cover-growth
price has been extracted. -/
def boundedMultiplierRadiusFloor (d : ℕ) : ℝ :=
  min (6 : ℝ)⁻¹
    (min (1 / 4 : ℝ)
      (boundedMultiplierEpsilonStar d /
        (1 + boundedMultiplierRadiusGrowthConst d)))

theorem boundedMultiplierRadiusFloor_pos (d : ℕ) :
    0 < boundedMultiplierRadiusFloor d := by
  unfold boundedMultiplierRadiusFloor
  apply lt_min (by norm_num)
  apply lt_min (by norm_num)
  exact div_pos (boundedMultiplierEpsilonStar_pos d)
    (by linarith [boundedMultiplierRadiusGrowthConst_pos d])

private theorem log_two_le_abs_log_delta {d : ℕ} (M : GMCModel d) :
    Real.log 2 ≤ |Real.log M.delta| := by
  have hlogNonpos : Real.log M.delta ≤ 0 :=
    Real.log_nonpos M.shellPrefix.delta_pos.le
      (M.shellPrefix.delta_le_half.trans (by norm_num))
  have hlogLe : Real.log M.delta ≤ Real.log (1 / 2 : ℝ) :=
    Real.log_le_log M.shellPrefix.delta_pos M.shellPrefix.delta_le_half
  rw [abs_of_nonpos hlogNonpos]
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
    (by norm_num : (2 : ℝ) ≠ 0)] at hlogLe
  simp only [Real.log_one, zero_sub] at hlogLe
  linarith

/-- The good-event threshold grows no faster than a dimension-only multiple
of `3^m`.  The estimate is deliberately crude: it uses `delta ≤ 1/2` only. -/
theorem half_boundedMultiplierCoverOscillationThreshold_le_growth
    {d : ℕ} (M : GMCModel d) {m : ℤ} (hm : 0 < m) :
    boundedMultiplierCoverOscillationThreshold M m / 2 ≤
      boundedMultiplierRadiusGrowthConst d * (3 : ℝ) ^ m := by
  let N : ℝ := ((shellCoverShifts d m).card : ℝ)
  have hNone : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Finset.card_ne_zero.mpr (shellCoverShifts_nonempty d m))
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hNone
  have hsqrtLog : Real.sqrt (Real.log N) ≤
      Real.sqrt (shellCoverLogConst * (d : ℝ)) * (3 : ℝ) ^ m := by
    have hsmall : Real.sqrt (Real.log N) ≤
        Real.sqrt (3 * Real.log N) := by
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hcover := shellCover_gaussianFactor_le M hm
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by ring, ← Real.sqrt_eq_rpow] at hcover
    exact hsmall.trans (by simpa only [N] using hcover)
  have hthree : 1 ≤ (3 : ℝ) ^ m := by
    exact one_le_zpow₀ (by norm_num) hm.le
  have hdeltaSqrt : M.delta * Real.sqrt (Real.log N) ≤
      Real.sqrt (shellCoverLogConst * (d : ℝ)) * (3 : ℝ) ^ m := by
    calc
      M.delta * Real.sqrt (Real.log N) ≤
          1 * Real.sqrt (Real.log N) := by
        exact mul_le_mul_of_nonneg_right
          (M.shellPrefix.delta_le_half.trans (by norm_num))
          (Real.sqrt_nonneg _)
      _ = Real.sqrt (Real.log N) := one_mul _
      _ ≤ _ := hsqrtLog
  have habsPos : 0 < |Real.log M.delta| :=
    lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      (log_two_le_abs_log_delta M)
  have hinvLog : |Real.log M.delta|⁻¹ ≤ (Real.log 2)⁻¹ := by
    exact (inv_le_inv₀ habsPos (Real.log_pos (by norm_num))).2
      (log_two_le_abs_log_delta M)
  have hcancel :
      M.delta * (M.delta * |Real.log M.delta|)⁻¹ =
        |Real.log M.delta|⁻¹ := by
    field_simp [M.shellPrefix.delta_pos.ne', habsPos.ne']
  have htail : M.delta *
        (Real.sqrt (Real.log N) +
          (M.delta * |Real.log M.delta|)⁻¹) ≤
      (Real.sqrt (shellCoverLogConst * (d : ℝ)) + (Real.log 2)⁻¹) *
        (3 : ℝ) ^ m := by
    rw [mul_add, hcancel]
    calc
      M.delta * Real.sqrt (Real.log N) + |Real.log M.delta|⁻¹ ≤
          Real.sqrt (shellCoverLogConst * (d : ℝ)) * (3 : ℝ) ^ m +
            (Real.log 2)⁻¹ := add_le_add hdeltaSqrt hinvLog
      _ ≤ (Real.sqrt (shellCoverLogConst * (d : ℝ)) + (Real.log 2)⁻¹) *
          (3 : ℝ) ^ m := by
        have hinv0 : 0 ≤ (Real.log 2)⁻¹ :=
          (inv_pos.mpr (Real.log_pos (by norm_num))).le
        nlinarith
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left htail fixedCutoffOscillationConst_pos.le)
    (by norm_num : (0 : ℝ) ≤ 2)
  unfold boundedMultiplierCoverOscillationThreshold
  dsimp only [boundedMultiplierCoverTailParameter]
  unfold boundedMultiplierRadiusGrowthConst
  dsimp only [N] at hscaled
  convert hscaled using 1 <;> ring

/-- Sharp form used in the closing argument: the threshold has only
square-root growth in the positive parent scale. -/
theorem half_boundedMultiplierCoverOscillationThreshold_le_sqrtGrowth
    {d : ℕ} (M : GMCModel d) {m : ℤ} (hm : 0 < m) :
    boundedMultiplierCoverOscillationThreshold M m / 2 ≤
      boundedMultiplierRadiusGrowthConst d *
        (Real.sqrt (m : ℝ) + 1) := by
  let N : ℝ := ((shellCoverShifts d m).card : ℝ)
  have hNone : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Finset.card_ne_zero.mpr (shellCoverShifts_nonempty d m))
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hNone
  have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast hm.le
  have hsqrtLog : Real.sqrt (Real.log N) ≤
      Real.sqrt (shellCoverLogConst * (d : ℝ)) * Real.sqrt (m : ℝ) := by
    have hsmall : Real.sqrt (Real.log N) ≤
        Real.sqrt (3 * Real.log N) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have hcover := shellCover_gaussianFactor_le_sqrt M hm
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by ring, ← Real.sqrt_eq_rpow] at hcover
    exact hsmall.trans (by simpa only [N] using hcover)
  have hdeltaSqrt : M.delta * Real.sqrt (Real.log N) ≤
      Real.sqrt (shellCoverLogConst * (d : ℝ)) * Real.sqrt (m : ℝ) := by
    exact (mul_le_mul_of_nonneg_left hsqrtLog M.shellPrefix.delta_pos.le).trans
      (by
        have hhalf := M.shellPrefix.delta_le_half
        have hnonneg : 0 ≤ Real.sqrt (shellCoverLogConst * (d : ℝ)) *
            Real.sqrt (m : ℝ) := by positivity
        nlinarith)
  have habsPos : 0 < |Real.log M.delta| :=
    lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      (log_two_le_abs_log_delta M)
  have hinvLog : |Real.log M.delta|⁻¹ ≤ (Real.log 2)⁻¹ :=
    (inv_le_inv₀ habsPos (Real.log_pos (by norm_num))).2
      (log_two_le_abs_log_delta M)
  have hcancel :
      M.delta * (M.delta * |Real.log M.delta|)⁻¹ =
        |Real.log M.delta|⁻¹ := by
    field_simp [M.shellPrefix.delta_pos.ne', habsPos.ne']
  have htail : M.delta *
        (Real.sqrt (Real.log N) +
          (M.delta * |Real.log M.delta|)⁻¹) ≤
      (Real.sqrt (shellCoverLogConst * (d : ℝ)) + (Real.log 2)⁻¹) *
        (Real.sqrt (m : ℝ) + 1) := by
    rw [mul_add, hcancel]
    have hrootD : 0 ≤ Real.sqrt (shellCoverLogConst * (d : ℝ)) :=
      Real.sqrt_nonneg _
    have hrootM : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
    have hinv0 : 0 ≤ (Real.log 2)⁻¹ :=
      (inv_pos.mpr (Real.log_pos (by norm_num))).le
    calc
      M.delta * Real.sqrt (Real.log N) + |Real.log M.delta|⁻¹ ≤
          Real.sqrt (shellCoverLogConst * (d : ℝ)) * Real.sqrt (m : ℝ) +
            (Real.log 2)⁻¹ := add_le_add hdeltaSqrt hinvLog
      _ ≤ (Real.sqrt (shellCoverLogConst * (d : ℝ)) + (Real.log 2)⁻¹) *
          (Real.sqrt (m : ℝ) + 1) := by nlinarith
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left htail fixedCutoffOscillationConst_pos.le)
    (by norm_num : (0 : ℝ) ≤ 2)
  unfold boundedMultiplierCoverOscillationThreshold
  dsimp only [boundedMultiplierCoverTailParameter]
  unfold boundedMultiplierRadiusGrowthConst
  dsimp only [N] at hscaled
  convert hscaled using 1 <;> ring

/-- At a negative parent scale the logarithmic cover price is a fixed
dimension-only constant. -/
theorem half_boundedMultiplierCoverOscillationThreshold_le_negativeGrowth
    {d : ℕ} (M : GMCModel d) {m : ℤ} (hm : m < 0) :
    boundedMultiplierCoverOscillationThreshold M m / 2 ≤
      boundedMultiplierNegativeRadiusGrowthConst d := by
  let N : ℝ := ((shellCoverShifts d m).card : ℝ)
  have htoNat : (m + 1).toNat = 0 := by omega
  have hcard : N = (3 : ℝ) ^ d := by
    dsimp only [N]
    rw [card_shellCoverShifts, shellCoverRadius, htoNat]
    norm_num
  have hNone : 1 ≤ N := by
    rw [hcard]
    exact one_le_pow₀ (by norm_num)
  have hsqrt0 : 0 ≤ Real.sqrt (Real.log N) := Real.sqrt_nonneg _
  have hdeltaSqrt : M.delta * Real.sqrt (Real.log N) ≤
      Real.sqrt (Real.log N) := by
    exact mul_le_of_le_one_left hsqrt0
      (M.shellPrefix.delta_le_half.trans (by norm_num))
  have habsPos : 0 < |Real.log M.delta| :=
    lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      (log_two_le_abs_log_delta M)
  have hinvLog : |Real.log M.delta|⁻¹ ≤ (Real.log 2)⁻¹ :=
    (inv_le_inv₀ habsPos (Real.log_pos (by norm_num))).2
      (log_two_le_abs_log_delta M)
  have hcancel :
      M.delta * (M.delta * |Real.log M.delta|)⁻¹ =
        |Real.log M.delta|⁻¹ := by
    field_simp [M.shellPrefix.delta_pos.ne', habsPos.ne']
  have htail : M.delta *
        (Real.sqrt (Real.log N) +
          (M.delta * |Real.log M.delta|)⁻¹) ≤
      Real.sqrt (Real.log ((3 : ℝ) ^ d)) + (Real.log 2)⁻¹ := by
    rw [mul_add, hcancel]
    calc
      M.delta * Real.sqrt (Real.log N) + |Real.log M.delta|⁻¹ ≤
          Real.sqrt (Real.log N) + (Real.log 2)⁻¹ :=
        add_le_add hdeltaSqrt hinvLog
      _ = Real.sqrt (Real.log ((3 : ℝ) ^ d)) + (Real.log 2)⁻¹ := by
        rw [hcard]
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left htail fixedCutoffOscillationConst_pos.le)
    (by norm_num : (0 : ℝ) ≤ 2)
  unfold boundedMultiplierCoverOscillationThreshold
  dsimp only [boundedMultiplierCoverTailParameter]
  unfold boundedMultiplierNegativeRadiusGrowthConst
  dsimp only [N] at hscaled
  convert hscaled using 1 <;> ring

/-- On the restricted gradient-good event and at positive parent scale, the
adaptive radius is at least a dimension-only multiple of `3^{-m}`. -/
theorem boundedMultiplierRadiusFloor_div_zpow_le_localRadius
    {d : ℕ} (M : GMCModel d) (L : ℕ) {m : ℤ} (hm : 0 < m)
    (z : Vec d) {omega : PotentialSample d}
    (hgood : omega ∈ coveringRestrictedGradientGood M L m z) :
    boundedMultiplierRadiusFloor d / (3 : ℝ) ^ m ≤
      boundedMultiplierLocalRadius M L m z omega := by
  let A := (3 : ℝ) ^ m
  let K := boundedMultiplierRadiusGrowthConst d
  let epsilon := boundedMultiplierEpsilonStar d
  have hApos : 0 < A := by dsimp only [A]; positivity
  have hAone : 1 ≤ A := by
    dsimp only [A]
    exact one_le_zpow₀ (by norm_num) hm.le
  have hKpos : 0 < K := boundedMultiplierRadiusGrowthConst_pos d
  have hepsilon : 0 < epsilon := boundedMultiplierEpsilonStar_pos d
  have hfloor : 0 < boundedMultiplierRadiusFloor d :=
    boundedMultiplierRadiusFloor_pos d
  have hfloorMesh : boundedMultiplierRadiusFloor d ≤ (6 : ℝ)⁻¹ :=
    min_le_left _ _
  have hfloorAmbient : boundedMultiplierRadiusFloor d ≤ 1 / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hfloorEpsilon : boundedMultiplierRadiusFloor d ≤ epsilon / (1 + K) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hthreshold : boundedMultiplierCoverOscillationThreshold M m / 2 ≤
      K * A := by
    simpa only [K, A] using
      half_boundedMultiplierCoverOscillationThreshold_le_growth M hm
  have hdenSmall : 0 <
      1 + boundedMultiplierCoverOscillationThreshold M m / 2 := by
    have hG0 := coveringLogLipschitzModulus_nonneg M L m z omega
    have hG : coveringLogLipschitzModulus M L m z omega ≤
        boundedMultiplierCoverOscillationThreshold M m / 2 := by
      simpa only [coveringRestrictedGradientGood, Set.mem_setOf_eq] using hgood
    linarith
  have hdenLarge : 0 < (1 + K) * A :=
    mul_pos (by linarith) hApos
  have hden : 1 + boundedMultiplierCoverOscillationThreshold M m / 2 ≤
      (1 + K) * A := by
    nlinarith
  have hmesh : boundedMultiplierRadiusFloor d / A ≤ (6 : ℝ)⁻¹ := by
    rw [div_le_iff₀ hApos]
    nlinarith
  have hambient : boundedMultiplierRadiusFloor d / A ≤ A / 4 := by
    rw [div_le_iff₀ hApos]
    nlinarith [sq_nonneg (A - 1)]
  have hfrac : boundedMultiplierRadiusFloor d / A ≤
      epsilon /
        (1 + boundedMultiplierCoverOscillationThreshold M m / 2) := by
    calc
      boundedMultiplierRadiusFloor d / A ≤
          (epsilon / (1 + K)) / A :=
        div_le_div_of_nonneg_right hfloorEpsilon hApos.le
      _ = epsilon / ((1 + K) * A) := by rw [div_div]
      _ ≤ epsilon /
          (1 + boundedMultiplierCoverOscillationThreshold M m / 2) :=
        div_le_div_of_nonneg_left hepsilon.le hdenSmall hden
  have hlower : boundedMultiplierRadiusFloor d / A ≤
      min (6 : ℝ)⁻¹
        (min (A / 4)
          (epsilon /
            (1 + boundedMultiplierCoverOscillationThreshold M m / 2))) :=
    le_min hmesh (le_min hambient hfrac)
  have hlower' : boundedMultiplierRadiusFloor d / (3 : ℝ) ^ m ≤
      min (6 : ℝ)⁻¹
        (min ((3 : ℝ) ^ m / 4)
          (boundedMultiplierEpsilonStar d /
            (1 + boundedMultiplierCoverOscillationThreshold M m / 2))) := by
    simpa only [A, epsilon] using hlower
  exact hlower'.trans
    (deterministicRadiusLower_le_boundedMultiplierLocalRadius M L m z hgood)

/-- Sharp radius floor used below scale one: the adaptive radius loses only a
factor `sqrt(m)+1`, which is absorbable by any fixed positive exponential
Campanato rate. -/
theorem boundedMultiplierRadiusFloor_div_sqrt_add_one_le_localRadius
    {d : ℕ} (M : GMCModel d) (L : ℕ) {m : ℤ} (hm : 0 < m)
    (z : Vec d) {omega : PotentialSample d}
    (hgood : omega ∈ coveringRestrictedGradientGood M L m z) :
    boundedMultiplierRadiusFloor d / (Real.sqrt (m : ℝ) + 1) ≤
      boundedMultiplierLocalRadius M L m z omega := by
  let T := boundedMultiplierCoverOscillationThreshold M m / 2
  let S := Real.sqrt (m : ℝ) + 1
  let K := boundedMultiplierRadiusGrowthConst d
  let epsilon := boundedMultiplierEpsilonStar d
  have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast hm.le
  have hS : 1 ≤ S := by
    dsimp only [S]
    linarith [Real.sqrt_nonneg (m : ℝ)]
  have hSpos : 0 < S := zero_lt_one.trans_le hS
  have hthree : 1 ≤ (3 : ℝ) ^ m :=
    one_le_zpow₀ (by norm_num) hm.le
  have hKpos : 0 < K := boundedMultiplierRadiusGrowthConst_pos d
  have hepsilon : 0 < epsilon := boundedMultiplierEpsilonStar_pos d
  have hthreshold : T ≤ K * S := by
    simpa only [T, K, S] using
      half_boundedMultiplierCoverOscillationThreshold_le_sqrtGrowth M hm
  have hT0 : 0 ≤ T := by
    have hG0 := coveringLogLipschitzModulus_nonneg M L m z omega
    have hG : coveringLogLipschitzModulus M L m z omega ≤ T := by
      simpa only [coveringRestrictedGradientGood, Set.mem_setOf_eq, T] using hgood
    exact hG0.trans hG
  have hdenSmall : 0 < 1 + T := by linarith
  have hden : 1 + T ≤ (1 + K) * S := by
    nlinarith [Real.sqrt_nonneg (m : ℝ)]
  have hfloorMesh : boundedMultiplierRadiusFloor d ≤ (6 : ℝ)⁻¹ :=
    min_le_left _ _
  have hfloorAmbient : boundedMultiplierRadiusFloor d ≤ 1 / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hfloorEpsilon : boundedMultiplierRadiusFloor d ≤ epsilon / (1 + K) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hmesh : boundedMultiplierRadiusFloor d / S ≤ (6 : ℝ)⁻¹ := by
    rw [div_le_iff₀ hSpos]
    nlinarith
  have hambient : boundedMultiplierRadiusFloor d / S ≤ (3 : ℝ) ^ m / 4 := by
    rw [div_le_iff₀ hSpos]
    nlinarith
  have hfrac : boundedMultiplierRadiusFloor d / S ≤ epsilon / (1 + T) := by
    calc
      boundedMultiplierRadiusFloor d / S ≤ (epsilon / (1 + K)) / S :=
        div_le_div_of_nonneg_right hfloorEpsilon hSpos.le
      _ = epsilon / ((1 + K) * S) := by rw [div_div]
      _ ≤ epsilon / (1 + T) :=
        div_le_div_of_nonneg_left hepsilon.le hdenSmall hden
  have hlower : boundedMultiplierRadiusFloor d / S ≤
      min (6 : ℝ)⁻¹
        (min ((3 : ℝ) ^ m / 4) (epsilon / (1 + T))) :=
    le_min hmesh (le_min hambient hfrac)
  have hlower' : boundedMultiplierRadiusFloor d /
        (Real.sqrt (m : ℝ) + 1) ≤
      min (6 : ℝ)⁻¹
        (min ((3 : ℝ) ^ m / 4)
          (boundedMultiplierEpsilonStar d /
            (1 + boundedMultiplierCoverOscillationThreshold M m / 2))) := by
    simpa only [S, T, epsilon] using hlower
  exact hlower'.trans
    (deterministicRadiusLower_le_boundedMultiplierLocalRadius M L m z hgood)

/-- In the direct negative-parent-scale branch the adaptive radius is a fixed
dimension-only fraction of the ambient scale `3^m`. -/
theorem boundedMultiplierNegativeRadiusFloor_mul_zpow_le_localRadius
    {d : ℕ} (M : GMCModel d) (L : ℕ) {m : ℤ} (hm : m < 0)
    (z : Vec d) {omega : PotentialSample d}
    (hgood : omega ∈ coveringRestrictedGradientGood M L m z) :
    boundedMultiplierNegativeRadiusFloor d * (3 : ℝ) ^ m ≤
      boundedMultiplierLocalRadius M L m z omega := by
  let A := (3 : ℝ) ^ m
  let T := boundedMultiplierCoverOscillationThreshold M m / 2
  let K := boundedMultiplierNegativeRadiusGrowthConst d
  let epsilon := boundedMultiplierEpsilonStar d
  have hApos : 0 < A := by dsimp only [A]; positivity
  have hAone : A ≤ 1 := by
    dsimp only [A]
    exact (zpow_le_one_iff_right₀ (by norm_num)).2 hm.le
  have hT0 : 0 ≤ T := by
    have hG0 := coveringLogLipschitzModulus_nonneg M L m z omega
    have hG : coveringLogLipschitzModulus M L m z omega ≤ T := by
      simpa only [coveringRestrictedGradientGood, Set.mem_setOf_eq, T] using hgood
    exact hG0.trans hG
  have hthreshold : T ≤ K := by
    simpa only [T, K] using
      half_boundedMultiplierCoverOscillationThreshold_le_negativeGrowth M hm
  have hdenSmall : 0 < 1 + T := by linarith
  have hden : 1 + T ≤ 1 + K := by linarith
  have hfloorMesh : boundedMultiplierNegativeRadiusFloor d ≤ (6 : ℝ)⁻¹ :=
    min_le_left _ _
  have hfloorAmbient : boundedMultiplierNegativeRadiusFloor d ≤ 1 / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hfloorEpsilon : boundedMultiplierNegativeRadiusFloor d ≤
      epsilon / (1 + K) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hfloor0 : 0 ≤ boundedMultiplierNegativeRadiusFloor d :=
    (boundedMultiplierNegativeRadiusFloor_pos d).le
  have hmesh : boundedMultiplierNegativeRadiusFloor d * A ≤ (6 : ℝ)⁻¹ :=
    (mul_le_of_le_one_right hfloor0 hAone).trans hfloorMesh
  have hambient : boundedMultiplierNegativeRadiusFloor d * A ≤ A / 4 := by
    simpa [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_right hfloorAmbient hApos.le
  have hfrac : boundedMultiplierNegativeRadiusFloor d * A ≤
      epsilon / (1 + T) := by
    calc
      boundedMultiplierNegativeRadiusFloor d * A ≤
          boundedMultiplierNegativeRadiusFloor d :=
        mul_le_of_le_one_right hfloor0 hAone
      _ ≤ epsilon / (1 + K) := hfloorEpsilon
      _ ≤ epsilon / (1 + T) :=
        div_le_div_of_nonneg_left (boundedMultiplierEpsilonStar_pos d).le
          hdenSmall hden
  have hlower : boundedMultiplierNegativeRadiusFloor d * A ≤
      min (6 : ℝ)⁻¹ (min (A / 4) (epsilon / (1 + T))) :=
    le_min hmesh (le_min hambient hfrac)
  have hlower' : boundedMultiplierNegativeRadiusFloor d * (3 : ℝ) ^ m ≤
      min (6 : ℝ)⁻¹
        (min ((3 : ℝ) ^ m / 4)
          (boundedMultiplierEpsilonStar d /
            (1 + boundedMultiplierCoverOscillationThreshold M m / 2))) := by
    simpa only [A, T, epsilon] using hlower
  exact hlower'.trans
    (deterministicRadiusLower_le_boundedMultiplierLocalRadius M L m z hgood)

/-- The square-root radius loss is absorbed by every fixed positive
exponential rate.  This elementary form avoids an asymptotic-sequence API:
`1+t ≤ exp t` is enough. -/
theorem sqrt_add_one_le_inv_mul_exp
    {x epsilon : ℝ} (hx : 1 ≤ x) (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    Real.sqrt x + 1 ≤ epsilon⁻¹ * Real.exp (epsilon * x) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hsqrt : Real.sqrt x ≤ x := (Real.sqrt_le_iff).2 ⟨hx0, by nlinarith⟩
  have hscaled : epsilon * (Real.sqrt x + 1) ≤ 1 + epsilon * x := by
    have hsqrt' := mul_le_mul_of_nonneg_left hsqrt hepsilon.le
    nlinarith
  have hexp : 1 + epsilon * x ≤ Real.exp (epsilon * x) :=
    by simpa only [add_comm] using Real.add_one_le_exp (epsilon * x)
  have hmul : epsilon * (Real.sqrt x + 1) ≤ Real.exp (epsilon * x) :=
    hscaled.trans hexp
  calc
    Real.sqrt x + 1 = epsilon⁻¹ * (epsilon * (Real.sqrt x + 1)) := by
      field_simp [hepsilon.ne']
    _ ≤ epsilon⁻¹ * Real.exp (epsilon * x) :=
      mul_le_mul_of_nonneg_left hmul (inv_pos.mpr hepsilon).le

/-- Base-three spelling of `sqrt_add_one_le_inv_mul_exp`, ready for the
Campanato exponent reserve. -/
theorem sqrt_add_one_le_inv_mul_three_rpow
    {x c : ℝ} (hx : 1 ≤ x) (hc : 0 < c)
    (hcLog : c * Real.log 3 ≤ 1) :
    Real.sqrt x + 1 ≤
      (c * Real.log 3)⁻¹ * (3 : ℝ) ^ (c * x) := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hepsilon : 0 < c * Real.log 3 := mul_pos hc hlog
  have h := sqrt_add_one_le_inv_mul_exp hx hepsilon hcLog
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    show Real.log 3 * (c * x) = (c * Real.log 3) * x by ring]
  exact h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
