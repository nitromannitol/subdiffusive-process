import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SubunitRadiusAbsorption

/-!
# A deterministic localization radius at nonpositive parent scales

For `m ≤ 0` the covering family has at most `7^d` cells.  The restricted
gradient-good event therefore gives a dimension-only fraction of `3^m` as a
lower bound for the adaptive small-contrast radius.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

/-- Dimension-only logarithmic-gradient price for all nonpositive scales. -/
def boundedMultiplierNonpositiveRadiusGrowthConst (d : ℕ) : ℝ :=
  fixedCutoffOscillationConst / 2 *
    (Real.sqrt (Real.log ((7 : ℝ) ^ d)) + (Real.log 2)⁻¹)

theorem boundedMultiplierNonpositiveRadiusGrowthConst_pos (d : ℕ) :
    0 < boundedMultiplierNonpositiveRadiusGrowthConst d := by
  unfold boundedMultiplierNonpositiveRadiusGrowthConst
  exact mul_pos (div_pos fixedCutoffOscillationConst_pos (by norm_num))
    (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _)
      (inv_pos.mpr (Real.log_pos (by norm_num))))

/-- The fixed fraction used by the direct `m ≤ 0` branch.  The extra `1/8`
collar keeps its outer ball inside the frozen `3/8` oscillation window. -/
def boundedMultiplierNonpositiveRadiusFloor (d : ℕ) : ℝ :=
  min (1 / 8 : ℝ)
    (min (6 : ℝ)⁻¹
      (boundedMultiplierEpsilonStar d /
        (1 + boundedMultiplierNonpositiveRadiusGrowthConst d)))

theorem boundedMultiplierNonpositiveRadiusFloor_pos (d : ℕ) :
    0 < boundedMultiplierNonpositiveRadiusFloor d := by
  unfold boundedMultiplierNonpositiveRadiusFloor
  apply lt_min (by norm_num)
  apply lt_min (by norm_num)
  exact div_pos (boundedMultiplierEpsilonStar_pos d)
    (by linarith [boundedMultiplierNonpositiveRadiusGrowthConst_pos d])

theorem boundedMultiplierNonpositiveRadiusFloor_le_eighth (d : ℕ) :
    boundedMultiplierNonpositiveRadiusFloor d ≤ 1 / 8 :=
  min_le_left _ _

theorem boundedMultiplierNonpositiveRadiusFloor_le_sixth (d : ℕ) :
    boundedMultiplierNonpositiveRadiusFloor d ≤ (6 : ℝ)⁻¹ :=
  (min_le_right _ _).trans (min_le_left _ _)

private theorem log_two_le_abs_log_delta_nonpositive {d : ℕ}
    (M : GMCModel d) :
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

/-- For every nonpositive parent scale, the cover-union threshold has a
dimension-only bound. -/
theorem half_boundedMultiplierCoverOscillationThreshold_le_nonpositiveGrowth
    {d : ℕ} (M : GMCModel d) {m : ℤ} (hm : m ≤ 0) :
    boundedMultiplierCoverOscillationThreshold M m / 2 ≤
      boundedMultiplierNonpositiveRadiusGrowthConst d := by
  let N : ℝ := ((shellCoverShifts d m).card : ℝ)
  have htoNat : (m + 1).toNat ≤ 1 := by omega
  have hrad : shellCoverRadius m ≤ 3 := by
    rw [shellCoverRadius]
    exact Nat.pow_le_pow_right (by norm_num) htoNat
  have hbase : 2 * shellCoverRadius m + 1 ≤ 7 := by omega
  have hcardNat : (shellCoverShifts d m).card ≤ 7 ^ d := by
    rw [card_shellCoverShifts]
    exact Nat.pow_le_pow_left hbase d
  have hcard : N ≤ (7 : ℝ) ^ d := by
    dsimp only [N]
    exact_mod_cast hcardNat
  have hNone : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Finset.card_ne_zero.mpr (shellCoverShifts_nonempty d m))
  have hseven : 0 < (7 : ℝ) ^ d := by positivity
  have hsqrtLog : Real.sqrt (Real.log N) ≤
      Real.sqrt (Real.log ((7 : ℝ) ^ d)) := by
    exact Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hcard)
  have hdeltaSqrt : M.delta * Real.sqrt (Real.log N) ≤
      Real.sqrt (Real.log ((7 : ℝ) ^ d)) := by
    calc
      M.delta * Real.sqrt (Real.log N) ≤ 1 * Real.sqrt (Real.log N) := by
        exact mul_le_mul_of_nonneg_right
          (M.shellPrefix.delta_le_half.trans (by norm_num))
          (Real.sqrt_nonneg _)
      _ = Real.sqrt (Real.log N) := one_mul _
      _ ≤ _ := hsqrtLog
  have habsPos : 0 < |Real.log M.delta| :=
    lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      (log_two_le_abs_log_delta_nonpositive M)
  have hinvLog : |Real.log M.delta|⁻¹ ≤ (Real.log 2)⁻¹ :=
    (inv_le_inv₀ habsPos (Real.log_pos (by norm_num))).2
      (log_two_le_abs_log_delta_nonpositive M)
  have hcancel :
      M.delta * (M.delta * |Real.log M.delta|)⁻¹ =
        |Real.log M.delta|⁻¹ := by
    field_simp [M.shellPrefix.delta_pos.ne', habsPos.ne']
  have htail : M.delta *
        (Real.sqrt (Real.log N) +
          (M.delta * |Real.log M.delta|)⁻¹) ≤
      Real.sqrt (Real.log ((7 : ℝ) ^ d)) + (Real.log 2)⁻¹ := by
    rw [mul_add, hcancel]
    exact add_le_add hdeltaSqrt hinvLog
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left htail fixedCutoffOscillationConst_pos.le)
    (by norm_num : (0 : ℝ) ≤ 2)
  unfold boundedMultiplierCoverOscillationThreshold
  dsimp only [boundedMultiplierCoverTailParameter]
  unfold boundedMultiplierNonpositiveRadiusGrowthConst
  dsimp only [N] at hscaled
  convert hscaled using 1 <;> ring

/-- On the restricted gradient-good event, a fixed dimension-only fraction
of `3^m` is available at every nonpositive scale. -/
theorem boundedMultiplierNonpositiveRadiusFloor_mul_zpow_le_localRadius
    {d : ℕ} (M : GMCModel d) (L : ℕ) {m : ℤ} (hm : m ≤ 0)
    (z : Vec d) {omega : PotentialSample d}
    (hgood : omega ∈ coveringRestrictedGradientGood M L m z) :
    boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m ≤
      boundedMultiplierLocalRadius M L m z omega := by
  let A := (3 : ℝ) ^ m
  let T := boundedMultiplierCoverOscillationThreshold M m / 2
  let K := boundedMultiplierNonpositiveRadiusGrowthConst d
  let epsilon := boundedMultiplierEpsilonStar d
  have hApos : 0 < A := by dsimp only [A]; positivity
  have hAone : A ≤ 1 := by
    dsimp only [A]
    exact (zpow_le_one_iff_right₀ (by norm_num)).2 hm
  have hT0 : 0 ≤ T := by
    have hG0 := coveringLogLipschitzModulus_nonneg M L m z omega
    have hG : coveringLogLipschitzModulus M L m z omega ≤ T := by
      simpa only [coveringRestrictedGradientGood, Set.mem_setOf_eq, T] using hgood
    exact hG0.trans hG
  have hthreshold : T ≤ K := by
    simpa only [T, K] using
      half_boundedMultiplierCoverOscillationThreshold_le_nonpositiveGrowth M hm
  have hdenSmall : 0 < 1 + T := by linarith
  have hden : 1 + T ≤ 1 + K := by linarith
  have hfloorMesh : boundedMultiplierNonpositiveRadiusFloor d ≤ (6 : ℝ)⁻¹ :=
    boundedMultiplierNonpositiveRadiusFloor_le_sixth d
  have hfloorAmbient : boundedMultiplierNonpositiveRadiusFloor d ≤ 1 / 4 :=
    (boundedMultiplierNonpositiveRadiusFloor_le_eighth d).trans (by norm_num)
  have hfloorEpsilon : boundedMultiplierNonpositiveRadiusFloor d ≤
      epsilon / (1 + K) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hfloor0 : 0 ≤ boundedMultiplierNonpositiveRadiusFloor d :=
    (boundedMultiplierNonpositiveRadiusFloor_pos d).le
  have hmesh : boundedMultiplierNonpositiveRadiusFloor d * A ≤ (6 : ℝ)⁻¹ :=
    (mul_le_of_le_one_right hfloor0 hAone).trans hfloorMesh
  have hambient : boundedMultiplierNonpositiveRadiusFloor d * A ≤ A / 4 := by
    simpa [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_right hfloorAmbient hApos.le
  have hfrac : boundedMultiplierNonpositiveRadiusFloor d * A ≤
      epsilon / (1 + T) := by
    calc
      boundedMultiplierNonpositiveRadiusFloor d * A ≤
          boundedMultiplierNonpositiveRadiusFloor d :=
        mul_le_of_le_one_right hfloor0 hAone
      _ ≤ epsilon / (1 + K) := hfloorEpsilon
      _ ≤ epsilon / (1 + T) :=
        div_le_div_of_nonneg_left (boundedMultiplierEpsilonStar_pos d).le
          hdenSmall hden
  have hlower : boundedMultiplierNonpositiveRadiusFloor d * A ≤
      min (6 : ℝ)⁻¹ (min (A / 4) (epsilon / (1 + T))) :=
    le_min hmesh (le_min hambient hfrac)
  have hlower' : boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m ≤
      min (6 : ℝ)⁻¹
        (min ((3 : ℝ) ^ m / 4)
          (boundedMultiplierEpsilonStar d /
            (1 + boundedMultiplierCoverOscillationThreshold M m / 2))) := by
    simpa only [A, T, epsilon] using hlower
  exact hlower'.trans
    (deterministicRadiusLower_le_boundedMultiplierLocalRadius M L m z hgood)

theorem boundedMultiplierNonpositiveRadius_mul_le_mesh
    {d : ℕ} {m : ℤ} (hm : m ≤ 0) :
    boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m ≤ (6 : ℝ)⁻¹ := by
  have hpow : (3 : ℝ) ^ m ≤ 1 :=
    (zpow_le_one_iff_right₀ (by norm_num)).2 hm
  exact (mul_le_of_le_one_right
    (boundedMultiplierNonpositiveRadiusFloor_pos d).le hpow).trans
      (boundedMultiplierNonpositiveRadiusFloor_le_sixth d)

theorem boundedMultiplierNonpositiveRadius_mul_le_ambient
    {d : ℕ} {m : ℤ} :
    boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m ≤
      (3 : ℝ) ^ m / 4 := by
  have hpow : 0 ≤ (3 : ℝ) ^ m := by positivity
  have hfloor : boundedMultiplierNonpositiveRadiusFloor d ≤ (1 / 4 : ℝ) :=
    (boundedMultiplierNonpositiveRadiusFloor_le_eighth d).trans (by norm_num)
  simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right
    hfloor hpow

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
