module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseMoment

@[expose] public section

/-!
# Gamma-two completion of the parameterized cutoff response row

The Section 4 headline controls the response score only up to its natural
moment cutoff.  This module combines that estimate with the deterministic
cap of the square-root row.  The dimension-only arithmetic is kept explicit:
at exponent `s / 2`, the squared Gamma-two scale costs `s⁻³`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped ENNReal

noncomputable section

/-- The first score moment that sees every spatial direction at exponent
`s / 2`. -/
def cutoffParameterizedResponseMomentFloor (d : ℕ) (s : ℝ) : ℝ :=
  2 + 2 * (d : ℝ) * (s / 2)⁻¹

theorem cutoffParameterizedResponseMomentFloor_two_le
    (d : ℕ) {s : ℝ} (hs : 0 < s) :
    2 ≤ cutoffParameterizedResponseMomentFloor d s := by
  unfold cutoffParameterizedResponseMomentFloor
  have hsInv : 0 ≤ (s / 2)⁻¹ := inv_nonneg.mpr (by positivity)
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num)
    (Nat.cast_nonneg d)) hsInv)

theorem cutoffParameterizedResponseMomentFloor_dimension
    (d : ℕ) (s : ℝ) :
    2 * (d : ℝ) * (s / 2)⁻¹ ≤
      cutoffParameterizedResponseMomentFloor d s := by
  unfold cutoffParameterizedResponseMomentFloor
  linarith

/-- A deliberately generous dimension-only coefficient.  Its four terms pay
respectively for positivity, direct moments, the fixed-floor downgrade, and
the deterministic high-moment cap. -/
def cutoffParameterizedResponseGammaCoeff (d : ℕ) (C : ℝ) : ℝ :=
  1 + 322 * C + 512 * C * (d : ℝ)

theorem cutoffParameterizedResponseGammaCoeff_pos
    (d : ℕ) {C : ℝ} (hC : 0 < C) :
    0 < cutoffParameterizedResponseGammaCoeff d C := by
  unfold cutoffParameterizedResponseGammaCoeff
  positivity

/-- The squared parameterized response scale.  Writing it with an integer
power makes the `s⁻³` loss literal before taking the square root. -/
def cutoffParameterizedResponseGammaSqConst
    (d : ℕ) (C s : ℝ) : ℝ :=
  cutoffParameterizedResponseGammaCoeff d C * s⁻¹ ^ 3

theorem cutoffParameterizedResponseGammaSqConst_pos
    (d : ℕ) {C s : ℝ} (hC : 0 < C) (hs : 0 < s) :
    0 < cutoffParameterizedResponseGammaSqConst d C s := by
  unfold cutoffParameterizedResponseGammaSqConst
  exact mul_pos (cutoffParameterizedResponseGammaCoeff_pos d hC)
    (pow_pos (inv_pos.mpr hs) 3)

theorem cutoffParameterizedResponseGammaSqConst_high_le
    (d : ℕ) {C s : ℝ} (hC : 0 < C) (hs : 0 < s) (hs1 : s ≤ 1) :
    16 * C * ((s / 2) ^ 2)⁻¹ ≤
      cutoffParameterizedResponseGammaSqConst d C s := by
  unfold cutoffParameterizedResponseGammaSqConst
    cutoffParameterizedResponseGammaCoeff
  field_simp [hs.ne']
  have hsSq : s ^ 2 ≤ 1 := by nlinarith
  have hCsq : C * s ^ 2 ≤ C :=
    by simpa using! mul_le_mul_of_nonneg_left hsSq hC.le
  nlinarith [hCsq,
    show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]

theorem cutoffParameterizedResponseGammaSqConst_floor_le
    (d : ℕ) {C s : ℝ} (hC : 0 < C) (hs : 0 < s) (hs1 : s ≤ 1) :
    32 * C * ((s / 2) ^ 2)⁻¹ *
        cutoffParameterizedResponseMomentFloor d s ≤
      cutoffParameterizedResponseGammaSqConst d C s := by
  unfold cutoffParameterizedResponseMomentFloor
    cutoffParameterizedResponseGammaSqConst
    cutoffParameterizedResponseGammaCoeff
  field_simp [hs.ne']
  nlinarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]

theorem cutoffParameterizedResponseGammaSqConst_cap_le
    (d : ℕ) {C s : ℝ} (hC : 0 < C) (hs : 0 < s) (hs1 : s ≤ 1) :
    C * (4 / s) / 2 ≤ cutoffParameterizedResponseGammaSqConst d C s := by
  unfold cutoffParameterizedResponseGammaSqConst
    cutoffParameterizedResponseGammaCoeff
  field_simp [hs.ne']
  have hsSq : s ^ 2 ≤ 1 := by nlinarith
  have hCsq : C * s ^ 2 ≤ C :=
    by simpa using! mul_le_mul_of_nonneg_left hsSq hC.le
  nlinarith [hCsq,
    show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]

/-- The Gamma-two scale of one parameterized finite-cutoff response row. -/
def cutoffParameterizedResponseGammaScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C s : ℝ) : ℝ :=
  Real.sqrt (cutoffParameterizedResponseGammaSqConst d C s) * M.delta *
    Real.sqrt |Real.log M.delta|

theorem cutoffParameterizedResponseGammaScale_pos {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {C s : ℝ}
    (hC : 0 < C) (hs : 0 < s) :
    0 < cutoffParameterizedResponseGammaScale M C s := by
  have hsq : 0 < cutoffParameterizedResponseGammaSqConst d C s :=
    cutoffParameterizedResponseGammaSqConst_pos d hC hs
  have hlogNeg : Real.log M.delta < 0 :=
    Real.log_neg M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
  unfold cutoffParameterizedResponseGammaScale
  exact mul_pos (mul_pos (Real.sqrt_pos.mpr hsq) M.shellPrefix.delta_pos)
    (Real.sqrt_pos.mpr (abs_pos.mpr hlogNeg.ne))

theorem cutoffParameterizedResponseGammaScale_sq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {C s : ℝ}
    (hC : 0 < C) (hs : 0 < s) :
    cutoffParameterizedResponseGammaScale M C s ^ 2 =
      cutoffParameterizedResponseGammaSqConst d C s * M.delta ^ 2 *
        |Real.log M.delta| := by
  have hsq : 0 ≤ cutoffParameterizedResponseGammaSqConst d C s :=
    (cutoffParameterizedResponseGammaSqConst_pos d hC hs).le
  have hlog : 0 ≤ |Real.log M.delta| := abs_nonneg _
  unfold cutoffParameterizedResponseGammaScale
  rw [mul_pow, mul_pow, Real.sq_sqrt hsq, Real.sq_sqrt hlog]

/-- Printed form of the response scale: the square-root of the literal
`s⁻³` coefficient is exactly `s⁻³ᐚ²`. -/
theorem cutoffParameterizedResponseGammaScale_eq_rpow {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {C s : ℝ}
    (hC : 0 < C) (hs : 0 < s) :
    cutoffParameterizedResponseGammaScale M C s =
      Real.sqrt (cutoffParameterizedResponseGammaCoeff d C) *
        s ^ (-3 / 2 : ℝ) * M.delta * Real.sqrt |Real.log M.delta| := by
  have hcoeff : 0 ≤ cutoffParameterizedResponseGammaCoeff d C :=
    (cutoffParameterizedResponseGammaCoeff_pos d hC).le
  have hsInv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hinv : Real.sqrt (s⁻¹ ^ 3) = s ^ (-3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (s⁻¹) 3,
      ← Real.rpow_mul hsInv]
    rw [Real.inv_rpow hs.le, ← Real.rpow_neg hs.le]
    norm_num
  unfold cutoffParameterizedResponseGammaScale
    cutoffParameterizedResponseGammaSqConst
  rw [Real.sqrt_mul hcoeff, hinv]

/-- One parameterized cutoff response row has Gamma-two growth uniformly in
the cutoff level.  The hypotheses are precisely the headline moment range and
the numerical requirement that its dimension floor lie inside that range. -/
theorem isBigOWith_gammaTwo_cutoffParameterizedResponseRow_of_score_bound
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {C s : ℝ}
    (hC : 0 < C) (hs : 0 < s) (hs1 : s ≤ 1)
    (hCL : 1 ≤ C * |Real.log M.delta|)
    (hfloor : cutoffParameterizedResponseMomentFloor d s ≤
      C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹)
    (hscore : ∀ (q : ℝ), 1 ≤ q →
      q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
      2 * (d : ℝ) * (s / 2)⁻¹ ≤ q →
      ∀ j : ℕ,
        paperENNRealLpNorm M.P.toMeasure q
            (cutoffLocalResponseScore M L (s / 2) 1 1 j) ≤
          ENNReal.ofReal
            (8 * C * ((s / 2) ^ 2)⁻¹ * q * Real.log (2 + q) *
              M.delta ^ 2))
    (j : ℕ) :
    Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2)
      (cutoffParameterizedResponseRow M L s j)
      (Real.exp 1 * cutoffParameterizedResponseGammaScale M C s) := by
  let logDelta : ℝ := |Real.log M.delta|
  let H : ℝ := C⁻¹ * (M.delta ^ 2)⁻¹ * logDelta⁻¹
  let p0 : ℝ := 2 * H
  let A : ℝ := cutoffParameterizedResponseGammaScale M C s
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hlogDelta : 0 < logDelta := by
    dsimp only [logDelta]
    exact abs_pos.mpr (ne_of_lt (Real.log_neg hdelta
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))))
  have hH : 0 < H := by dsimp only [H]; positivity
  have hp0 : 0 < p0 := by dsimp only [p0]; positivity
  have hA : 0 < A := cutoffParameterizedResponseGammaScale_pos M hC hs
  have hfloorH : cutoffParameterizedResponseMomentFloor d s ≤ H := by
    simpa only [H, logDelta] using! hfloor
  have hHdelta : H ≤ (M.delta ^ 2)⁻¹ := by
    have hCLinv : (C * logDelta)⁻¹ ≤ 1 :=
      (inv_le_one₀ (mul_pos hC hlogDelta)).2 hCL
    dsimp only [H]
    calc
      C⁻¹ * (M.delta ^ 2)⁻¹ * logDelta⁻¹ =
          (C * logDelta)⁻¹ * (M.delta ^ 2)⁻¹ := by field_simp
      _ ≤ 1 * (M.delta ^ 2)⁻¹ := by gcongr
      _ = _ := one_mul _
  have hcapSq : 4 / s ≤ A ^ 2 * p0 := by
    have hDcap := cutoffParameterizedResponseGammaSqConst_cap_le
      d hC hs hs1
    have hscaleSq := cutoffParameterizedResponseGammaScale_sq M hC hs
    have hlogAbs : |Real.log M.delta| ≠ 0 := by
      simpa only [logDelta] using! hlogDelta.ne'
    have hcalc : A ^ 2 * p0 =
        2 * cutoffParameterizedResponseGammaSqConst d C s / C := by
      dsimp only [A, p0, H, logDelta]
      rw [hscaleSq]
      field_simp [hC.ne', hdelta.ne', hlogAbs]
    rw [hcalc]
    calc
      4 / s = (2 / C) * (C * (4 / s) / 2) := by
        field_simp [hC.ne', hs.ne']
      _ ≤ (2 / C) * cutoffParameterizedResponseGammaSqConst d C s :=
        mul_le_mul_of_nonneg_left hDcap (by positivity)
      _ = 2 * cutoffParameterizedResponseGammaSqConst d C s / C := by ring
  have hcap : Real.sqrt (4 / s) ≤ A * Real.sqrt p0 := by
    have hleft0 : 0 ≤ Real.sqrt (4 / s) := Real.sqrt_nonneg _
    have hright0 : 0 ≤ A * Real.sqrt p0 :=
      mul_nonneg hA.le (Real.sqrt_nonneg _)
    rw [← sq_le_sq₀ hleft0 hright0, mul_pow,
      Real.sq_sqrt (div_nonneg (by norm_num) hs.le), Real.sq_sqrt hp0.le]
    exact hcapSq
  apply isBigOWith_gammaTwo_of_bounded_low_moment_growth
    hA (measurable_cutoffParameterizedResponseRow M L s j)
    (cutoffParameterizedResponseRow_nonneg M L s j)
    (cutoffParameterizedResponseRow_le_sqrt_cap M L s j) hcap
  intro p hp hpUpper
  have hpPos : 0 < p := zero_lt_one.trans_le hp
  by_cases hpLarge : 2 * cutoffParameterizedResponseMomentFloor d s ≤ p
  · let q : ℝ := p / 2
    have hqTwo : 2 ≤ q := by
      dsimp only [q]
      linarith [cutoffParameterizedResponseMomentFloor_two_le d hs]
    have hqFloor : cutoffParameterizedResponseMomentFloor d s ≤ q := by
      dsimp only [q]
      linarith
    have hqH : q ≤ H := by
      dsimp only [q, p0] at hpUpper ⊢
      linarith
    have hqSmall : q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ *
        |Real.log M.delta|⁻¹ := by
      simpa only [H, logDelta] using! hqH
    have hqDim : 2 * (d : ℝ) * (s / 2)⁻¹ ≤ q :=
      (cutoffParameterizedResponseMomentFloor_dimension d s).trans hqFloor
    let R : ℝ := 8 * C * ((s / 2) ^ 2)⁻¹ * q *
      Real.log (2 + q) * M.delta ^ 2
    have hR : 0 ≤ R := by
      have hlog : 0 ≤ Real.log (2 + q) := Real.log_nonneg (by linarith)
      dsimp only [R]
      positivity
    have hnorm := hscore q (by linarith) hqSmall hqDim j
    have hpTwo : 2 ≤ p := by
      linarith [cutoffParameterizedResponseMomentFloor_two_le d hs]
    have hmoment := integral_cutoffParameterizedResponseRow_rpow_le_of_score_norm
      (p := p) (R := R) M L hs j hpTwo hR (by
        simpa only [R, q] using! hnorm)
    have hqDelta : q ≤ (M.delta ^ 2)⁻¹ := hqH.trans hHdelta
    have hlog := log_two_add_le_four_abs_log hdelta
      M.shellPrefix.delta_le_half (by linarith : 0 ≤ q) hqDelta
    have hRsq : Real.sqrt R ≤ A * Real.sqrt p := by
      have hhigh := cutoffParameterizedResponseGammaSqConst_high_le
        d hC hs hs1
      have hscaleSq := cutoffParameterizedResponseGammaScale_sq M hC hs
      have hright0 : 0 ≤ A * Real.sqrt p :=
        mul_nonneg hA.le (Real.sqrt_nonneg _)
      rw [← sq_le_sq₀ (Real.sqrt_nonneg _) hright0,
        Real.sq_sqrt hR, mul_pow, Real.sq_sqrt hpPos.le]
      rw [hscaleSq]
      dsimp only [R, A, logDelta]
      calc
        8 * C * ((s / 2) ^ 2)⁻¹ * q * Real.log (2 + q) *
              M.delta ^ 2 ≤
            8 * C * ((s / 2) ^ 2)⁻¹ * q *
              (4 * |Real.log M.delta|) * M.delta ^ 2 := by gcongr
        _ = (16 * C * ((s / 2) ^ 2)⁻¹) *
              (M.delta ^ 2 * |Real.log M.delta|) * p := by
          dsimp only [q]
          ring
        _ ≤ cutoffParameterizedResponseGammaSqConst d C s *
              (M.delta ^ 2 * |Real.log M.delta|) * p := by gcongr
        _ = cutoffParameterizedResponseGammaSqConst d C s * M.delta ^ 2 *
              |Real.log M.delta| * p := by ring
    refine ⟨hmoment.1, hmoment.2.trans ?_⟩
    exact Real.rpow_le_rpow (Real.sqrt_nonneg R) hRsq hpPos.le
  · have hpFloor : p ≤ 2 * cutoffParameterizedResponseMomentFloor d s :=
      le_of_not_ge hpLarge
    let q0 : ℝ := cutoffParameterizedResponseMomentFloor d s
    let P0 : ℝ := 2 * q0
    let R0 : ℝ := 8 * C * ((s / 2) ^ 2)⁻¹ * q0 *
      Real.log (2 + q0) * M.delta ^ 2
    have hq0Two : 2 ≤ q0 := by
      simpa only [q0] using! cutoffParameterizedResponseMomentFloor_two_le d hs
    have hq0Small : q0 ≤ C⁻¹ * (M.delta ^ 2)⁻¹ *
        |Real.log M.delta|⁻¹ := by
      simpa only [q0] using! hfloor
    have hq0Dim : 2 * (d : ℝ) * (s / 2)⁻¹ ≤ q0 := by
      simpa only [q0] using! cutoffParameterizedResponseMomentFloor_dimension d s
    have hR0 : 0 ≤ R0 := by
      have hlog : 0 ≤ Real.log (2 + q0) := Real.log_nonneg (by linarith)
      dsimp only [R0]
      positivity
    have hnorm0 := hscore q0 (by linarith) hq0Small hq0Dim j
    have hP0half : P0 / 2 = q0 := by dsimp only [P0]; ring
    have hmoment0 := integral_cutoffParameterizedResponseRow_rpow_le_of_score_norm
      (p := P0) (R := R0) M L hs j (by
        dsimp only [P0]
        linarith) hR0 (by
          rw [hP0half]
          simpa only [R0] using! hnorm0)
    have hq0Delta : q0 ≤ (M.delta ^ 2)⁻¹ := hfloorH.trans hHdelta
    have hlog0 := log_two_add_le_four_abs_log hdelta
      M.shellPrefix.delta_le_half (by linarith : 0 ≤ q0) hq0Delta
    have hBscale : Real.sqrt R0 ≤ A := by
      have hfloorC := cutoffParameterizedResponseGammaSqConst_floor_le
        d hC hs hs1
      have hscaleSq := cutoffParameterizedResponseGammaScale_sq M hC hs
      have hleft0 : 0 ≤ Real.sqrt R0 := Real.sqrt_nonneg _
      rw [← sq_le_sq₀ hleft0 hA.le, Real.sq_sqrt hR0, hscaleSq]
      dsimp only [R0, q0, A]
      calc
        8 * C * ((s / 2) ^ 2)⁻¹ *
              cutoffParameterizedResponseMomentFloor d s *
              Real.log (2 + cutoffParameterizedResponseMomentFloor d s) *
              M.delta ^ 2 ≤
            8 * C * ((s / 2) ^ 2)⁻¹ *
              cutoffParameterizedResponseMomentFloor d s *
              (4 * |Real.log M.delta|) * M.delta ^ 2 := by gcongr
        _ = (32 * C * ((s / 2) ^ 2)⁻¹ *
              cutoffParameterizedResponseMomentFloor d s) * M.delta ^ 2 *
              |Real.log M.delta| := by ring
        _ ≤ cutoffParameterizedResponseGammaSqConst d C s * M.delta ^ 2 *
              |Real.log M.delta| := by gcongr
    have hP0 : 0 < P0 := by dsimp only [P0, q0]; linarith
    have hdown := integral_nonneg_rpow_le_of_high_moment
      (measurable_cutoffParameterizedResponseRow M L s j)
      (cutoffParameterizedResponseRow_nonneg M L s j)
      hpPos (q := P0) (by simpa only [P0, q0] using! hpFloor)
      (Real.sqrt_nonneg R0) hmoment0.1 hmoment0.2
    have hsqrtp : 1 ≤ Real.sqrt p := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hp
    have hbase : Real.sqrt R0 ≤ A * Real.sqrt p :=
      hBscale.trans (by nlinarith [hA])
    refine ⟨hdown.1, hdown.2.trans ?_⟩
    exact Real.rpow_le_rpow (Real.sqrt_nonneg R0) hbase hpPos.le

/-- Uniform general-`s` Gamma-two completion with the proved Section 4
headline fully consumed.  Only the literal moment-floor condition remains. -/
theorem exists_isBigOWith_gammaTwo_cutoffParameterizedResponseRow
    {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ), 0 < s → s ≤ 1 →
        cutoffParameterizedResponseMomentFloor d s ≤
          C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        ∀ L j : ℕ,
          Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 2)
            (cutoffParameterizedResponseRow M L s j)
            (Real.exp 1 * cutoffParameterizedResponseGammaScale M C s) := by
  obtain ⟨_c, C0, _hc, hC0, hscore0⟩ :=
    exists_cutoffParameterizedResponseScore_norm_bound (d := d)
  let C : ℝ := 1 + C0 + (Real.log 2)⁻¹
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hC0C : C0 ≤ C := by
    dsimp only [C]
    have : 0 < (Real.log 2)⁻¹ := inv_pos.mpr hlogTwo
    linarith
  have hlogInvC : (Real.log 2)⁻¹ ≤ C := by
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro M s hs hs1 hfloor L j
  have hCL : 1 ≤ C * |Real.log M.delta| := by
    calc
      1 = (Real.log 2)⁻¹ * Real.log 2 := by field_simp [hlogTwo.ne']
      _ ≤ C * Real.log 2 :=
        mul_le_mul_of_nonneg_right hlogInvC hlogTwo.le
      _ ≤ C * |Real.log M.delta| :=
        mul_le_mul_of_nonneg_left (log_two_le_abs_log_delta M) hC.le
  apply isBigOWith_gammaTwo_cutoffParameterizedResponseRow_of_score_bound
    M L hC hs hs1 hCL hfloor _ j
  intro q hq hsmall hdim k
  have hCinv : C⁻¹ ≤ C0⁻¹ := (inv_le_inv₀ hC hC0).2 hC0C
  have hfactor : 0 ≤ (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
    positivity
  have hsmall0 : q ≤ C0⁻¹ * (M.delta ^ 2)⁻¹ *
      |Real.log M.delta|⁻¹ := by
    exact hsmall.trans (by
      calc
        C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ =
            C⁻¹ * ((M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹) := by ring
        _ ≤ C0⁻¹ * ((M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹) :=
          mul_le_mul_of_nonneg_right hCinv hfactor
        _ = _ := by ring)
  have hraw := hscore0 M q hq hsmall0 s hs hs1 hdim L k
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hlog : 0 ≤ Real.log (2 + q) := Real.log_nonneg (by linarith)
  have hrest : 0 ≤ ((s / 2) ^ 2)⁻¹ * q * Real.log (2 + q) *
      M.delta ^ 2 := by positivity
  exact hraw.trans (ENNReal.ofReal_le_ofReal (by
    calc
      8 * C0 * ((s / 2) ^ 2)⁻¹ * q * Real.log (2 + q) *
          M.delta ^ 2 =
          (8 * C0) * (((s / 2) ^ 2)⁻¹ * q * Real.log (2 + q) *
            M.delta ^ 2) := by ring
      _ ≤ (8 * C) * (((s / 2) ^ 2)⁻¹ * q * Real.log (2 + q) *
            M.delta ^ 2) := by gcongr
      _ = 8 * C * ((s / 2) ^ 2)⁻¹ * q * Real.log (2 + q) *
          M.delta ^ 2 := by ring))

theorem cutoffParameterizedResponseMomentFloor_mul_s_le
    (d : ℕ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    cutoffParameterizedResponseMomentFloor d s * s ≤
      2 + 4 * (d : ℝ) := by
  unfold cutoffParameterizedResponseMomentFloor
  field_simp [hs.ne']
  nlinarith

/-- The cutoff ladder's natural lower bound on `s` places the parameterized
moment floor inside the proved headline range. -/
theorem cutoffParameterizedResponseMomentFloor_le_of_budget
    {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {C s : ℝ}
    (hC : 0 < C) (hs : 0 < s) (hs1 : s ≤ 1)
    (hbudget : C * (2 + 4 * (d : ℝ)) * M.delta ^ 2 *
      |Real.log M.delta| ≤ s) :
    cutoffParameterizedResponseMomentFloor d s ≤
      C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hlog : 0 < |Real.log M.delta| := by
    exact abs_pos.mpr (ne_of_lt (Real.log_neg hdelta
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))))
  let D : ℝ := 2 + 4 * (d : ℝ)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hfloorS : cutoffParameterizedResponseMomentFloor d s * s ≤ D := by
    simpa only [D] using!
      cutoffParameterizedResponseMomentFloor_mul_s_le d hs hs1
  have hfloor : cutoffParameterizedResponseMomentFloor d s ≤ D / s :=
    (le_div_iff₀ hs).2 (by simpa [mul_comm] using! hfloorS)
  have hbudget' : C * D * (M.delta ^ 2 * |Real.log M.delta|) ≤ s := by
    simpa only [D] using! (by simpa [mul_assoc] using! hbudget)
  have hratio : C * D * (M.delta ^ 2 * |Real.log M.delta|) / s ≤ 1 := by
    exact (div_le_one hs).2 hbudget'
  have hprod : C * cutoffParameterizedResponseMomentFloor d s *
      (M.delta ^ 2 * |Real.log M.delta|) ≤ 1 := by
    calc
      C * cutoffParameterizedResponseMomentFloor d s *
            (M.delta ^ 2 * |Real.log M.delta|) ≤
          C * (D / s) * (M.delta ^ 2 * |Real.log M.delta|) := by gcongr
      _ = C * D * (M.delta ^ 2 * |Real.log M.delta|) / s := by ring
      _ ≤ 1 := hratio
  have hdenom : 0 < C * M.delta ^ 2 * |Real.log M.delta| := by positivity
  calc
    cutoffParameterizedResponseMomentFloor d s ≤
        1 / (C * M.delta ^ 2 * |Real.log M.delta|) := by
      rw [le_div_iff₀ hdenom]
      nlinarith [hprod]
    _ = C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ := by
      field_simp [hC.ne', hdelta.ne', hlog.ne']

/-- The general response-row Gamma estimate in the exact cutoff-ladder
smallness form.  Its scale has squared loss `s⁻³`, hence row loss
`s⁻³ᐚ²`. -/
theorem exists_isBigOWith_gammaTwo_cutoffParameterizedResponseRow_of_budget
    {d : ℕ} [NeZero d] :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ),
        0 < s → s ≤ 1 →
        K * M.delta ^ 2 * |Real.log M.delta| ≤ s →
        ∀ L j : ℕ,
          Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 2)
            (cutoffParameterizedResponseRow M L s j)
            (Real.exp 1 * cutoffParameterizedResponseGammaScale M C s) := by
  obtain ⟨C, hC, hrow⟩ :=
    exists_isBigOWith_gammaTwo_cutoffParameterizedResponseRow (d := d)
  let K : ℝ := C * (2 + 4 * (d : ℝ))
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, C, hK, hC, ?_⟩
  intro M s hs hs1 hbudget L j
  apply hrow M s hs hs1 _ L j
  apply cutoffParameterizedResponseMomentFloor_le_of_budget M hC hs hs1
  simpa only [K] using! hbudget

/-! ## Finite-range array carrier -/

/-- Triangular array carrying the parameterized capped response rows. -/
noncomputable def cutoffParameterizedResponseRowArray {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ) :
    ℤ → ℤ → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ :=
  fun k j omega => Real.sqrt
    (min (cutoffResponseScoreArray M L (s / 2) 1 1 k j omega) (4 / s))

theorem measurable_cutoffParameterizedResponseRowArray
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ) (k j : ℤ) :
    Measurable (cutoffParameterizedResponseRowArray M L s k j) := by
  unfold cutoffParameterizedResponseRowArray
  exact Real.continuous_sqrt.measurable.comp
    ((measurable_cutoffResponseScoreArray M L (s / 2) 1 1 k j).min
      measurable_const)

theorem cutoffParameterizedResponseRowArray_diag
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ) (j : ℕ) :
    cutoffParameterizedResponseRowArray M L s (j : ℤ) (j : ℤ) =
      cutoffParameterizedResponseRow M L s j := by
  funext omega
  unfold cutoffParameterizedResponseRowArray cutoffParameterizedResponseRow
    cutoffParameterizedResponseScore
  simp only [cutoffResponseScoreArray, Int.natCast_nonneg, le_rfl, and_self,
    if_true, Int.toNat_natCast]

/-- Capping preserves the response score's dimension-only finite range. -/
theorem columnsIndep_cutoffParameterizedResponseRowArray
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ) :
    SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      (cutoffParameterizedResponseRowArray M L s) (responseScoreRange d) := by
  let f : ℝ → ℝ := fun x => Real.sqrt (min x (4 / s))
  have hf : Measurable f := Real.continuous_sqrt.measurable.comp
    (measurable_id.min measurable_const)
  simpa only [cutoffParameterizedResponseRowArray, f] using!
    columnsIndep_comp_entry M.P.toMeasure
      (cutoffResponseScoreArray M L (s / 2) 1 1)
      (responseScoreRange d)
      (columnsIndep_cutoffResponseScoreArray M L (s / 2) 1 1) f hf

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
