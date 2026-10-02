import SubdiffusiveProcess.Section6SumErrors.ResponseBasic

/-!
# ResponseGamma

Gaussian tail bounds for the truncated response rows. Low moments use the score estimate and high moments use the deterministic truncation.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped ENNReal BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- An admissible moment floor exceeding the spatial entropy threshold. -/
def holderResponseMomentFloor (s : ℝ) (d : ℕ) : ℝ :=
  2 + 2 * (d : ℝ) * (holderResponseScoreS s)⁻¹

theorem holderResponseMomentFloor_two_le (s : ℝ) (hs : 0 < s) (d : ℕ) :
    2 ≤ (holderResponseMomentFloor s) d := by
  unfold holderResponseMomentFloor
  have hs : 0 ≤ (holderResponseScoreS s)⁻¹ :=
    inv_nonneg.mpr (holderResponseScoreS_pos s hs).le
  have : 0 ≤ 2 * (d : ℝ) * (holderResponseScoreS s)⁻¹ := by positivity
  linarith

theorem holderResponseMomentFloor_dimension (s : ℝ) (d : ℕ) :
    2 * (d : ℝ) * (holderResponseScoreS s)⁻¹ ≤ (holderResponseMomentFloor s) d := by
  unfold holderResponseMomentFloor
  linarith

/-- The coefficient of the squared Gaussian response-row scale. -/
noncomputable def holderResponseGammaSqConst (s : ℝ) (d : ℕ) (C : ℝ) : ℝ :=
  1 + 32 * C * (holderResponseScoreS s ^ 2)⁻¹ *
    (1 + holderResponseMomentFloor s d) + C * holderResponseScoreCap s / 2

theorem holderResponseGammaSqConst_pos (s : ℝ) (hs : 0 < s)
    {d : ℕ} {C : ℝ} (hC : 0 < C) : 0 < holderResponseGammaSqConst s d C := by
  have hf : 0 ≤ holderResponseMomentFloor s d :=
    (by linarith [holderResponseMomentFloor_two_le s hs d])
  have hcap := (holderResponseScoreCap_pos s hs).le
  unfold holderResponseGammaSqConst
  positivity

/-- The Gaussian response-row scale at a given moment constant. -/
noncomputable def holderResponseGammaScale (s : ℝ) {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C : ℝ) : ℝ :=
  Real.sqrt ((holderResponseGammaSqConst s) d C) * M.delta *
    Real.sqrt |Real.log M.delta|

theorem holderResponseGammaScale_pos (s : ℝ) (hs : 0 < s) {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {C : ℝ} (hC : 0 < C) :
    0 < (holderResponseGammaScale s) M C := by
  have hsq : 0 < (holderResponseGammaSqConst s) d C :=
    (holderResponseGammaSqConst_pos s hs) hC
  have hlogNeg : Real.log M.delta < 0 :=
    Real.log_neg M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
  unfold holderResponseGammaScale
  exact mul_pos (mul_pos (Real.sqrt_pos.mpr hsq) M.shellPrefix.delta_pos)
    (Real.sqrt_pos.mpr (abs_pos.mpr hlogNeg.ne))

theorem holderResponseGammaScale_sq (s : ℝ) (hs : 0 < s) {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {C : ℝ} (hC : 0 < C) :
    (holderResponseGammaScale s) M C ^ 2 =
      (holderResponseGammaSqConst s) d C * M.delta ^ 2 *
        |Real.log M.delta| := by
  have hsq : 0 ≤ (holderResponseGammaSqConst s) d C :=
    ((holderResponseGammaSqConst_pos s hs) hC).le
  have hlog : 0 ≤ |Real.log M.delta| := abs_nonneg _
  unfold holderResponseGammaScale
  rw [mul_pow, mul_pow, Real.sq_sqrt hsq, Real.sq_sqrt hlog]

theorem holderResponseGammaSqConst_high_le (s : ℝ) (hs : 0 < s)
    {d : ℕ} {C : ℝ} (hC : 0 < C) :
    16 * C * (holderResponseScoreS s ^ 2)⁻¹ ≤ holderResponseGammaSqConst s d C := by
  have hf : 0 ≤ holderResponseMomentFloor s d :=
    (by linarith [holderResponseMomentFloor_two_le s hs d])
  have hcap := (holderResponseScoreCap_pos s hs).le
  have hx : 0 ≤ C * (holderResponseScoreS s ^ 2)⁻¹ := by positivity
  have hxf := mul_nonneg hx hf
  have hc : 0 ≤ C * holderResponseScoreCap s / 2 := by positivity
  unfold holderResponseGammaSqConst
  nlinarith

theorem holderResponseGammaSqConst_floor_le (s : ℝ) (hs : 0 < s)
    {d : ℕ} {C : ℝ} (hC : 0 < C) :
    32 * C * (holderResponseScoreS s ^ 2)⁻¹ * holderResponseMomentFloor s d ≤
      holderResponseGammaSqConst s d C := by
  have hx : 0 ≤ C * (holderResponseScoreS s ^ 2)⁻¹ := by positivity
  have hcap := (holderResponseScoreCap_pos s hs).le
  have hc : 0 ≤ C * holderResponseScoreCap s / 2 := by positivity
  unfold holderResponseGammaSqConst
  nlinarith

theorem holderResponseGammaSqConst_cap_le (s : ℝ) (hs : 0 < s)
    {d : ℕ} {C : ℝ} (hC : 0 < C) :
    C * holderResponseScoreCap s / 2 ≤ holderResponseGammaSqConst s d C := by
  have hf : 0 ≤ holderResponseMomentFloor s d :=
    (by linarith [holderResponseMomentFloor_two_le s hs d])
  have hx : 0 ≤ 32 * C * (holderResponseScoreS s ^ 2)⁻¹ *
    (1 + holderResponseMomentFloor s d) := by positivity
  unfold holderResponseGammaSqConst
  linarith

theorem isBigOWith_gammaTwo_holderResponseRow_of_score_bound (s : ℝ) (hs : 0 < s)
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {C : ℝ} (hC : 0 < C)
    (hCL : 1 ≤ C * |Real.log M.delta|)
    (hfloor : (holderResponseMomentFloor s) d ≤
      C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹)
    (hscore : ∀ (q : ℝ), 1 ≤ q →
      q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
      2 * (d : ℝ) * (holderResponseScoreS s)⁻¹ ≤ q →
      ∀ j : ℕ,
        paperENNRealLpNorm M.P.toMeasure q
            (localResponseScore M (holderResponseScoreS s) 1 1 j) ≤
          ENNReal.ofReal
            (8 * C * ((holderResponseScoreS s) ^ 2)⁻¹ * q *
              Real.log (2 + q) * M.delta ^ 2))
    (j : ℕ) :
    Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2)
      ((holderResponseRow s) M j)
      (Real.exp 1 * (holderResponseGammaScale s) M C) := by
  let L : ℝ := |Real.log M.delta|
  let H : ℝ := C⁻¹ * (M.delta ^ 2)⁻¹ * L⁻¹
  let p0 : ℝ := 2 * H
  let A : ℝ := (holderResponseGammaScale s) M C
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hL : 0 < L := by
    dsimp only [L]
    exact abs_pos.mpr (ne_of_lt (Real.log_neg hdelta
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))))
  have hH : 0 < H := by dsimp only [H]; positivity
  have hp0 : 0 < p0 := by dsimp only [p0]; positivity
  have hA : 0 < A := (holderResponseGammaScale_pos s hs) M hC
  have hfloorH : (holderResponseMomentFloor s) d ≤ H := by
    simpa only [H, L] using hfloor
  have hpFloorP0 : 2 * (holderResponseMomentFloor s) d ≤ p0 := by
    dsimp only [p0]
    linarith
  have hHdelta : H ≤ (M.delta ^ 2)⁻¹ := by
    have hCLinv : (C * L)⁻¹ ≤ 1 :=
      (inv_le_one₀ (mul_pos hC hL)).2 hCL
    dsimp only [H]
    calc
      C⁻¹ * (M.delta ^ 2)⁻¹ * L⁻¹ =
          (C * L)⁻¹ * (M.delta ^ 2)⁻¹ := by field_simp
      _ ≤ 1 * (M.delta ^ 2)⁻¹ := by gcongr
      _ = _ := one_mul _
  have hcapSq : (holderResponseScoreCap s) ≤ A ^ 2 * p0 := by
    have hDcap := (holderResponseGammaSqConst_cap_le (d := d) s hs) hC
    have hscaleSq := (holderResponseGammaScale_sq s hs) M hC
    have hcalc : A ^ 2 * p0 =
        2 * (holderResponseGammaSqConst s) d C / C := by
      dsimp only [A, p0, H, L]
      rw [hscaleSq]
      field_simp [hC.ne', hdelta.ne',
        (abs_pos.mpr (ne_of_lt (Real.log_neg hdelta
          (M.shellPrefix.delta_le_half.trans_lt (by norm_num))))).ne']
    rw [hcalc]
    calc
      (holderResponseScoreCap s) = (2 / C) *
          (C * (holderResponseScoreCap s) / 2) := by field_simp [hC.ne']
      _ ≤ (2 / C) * (holderResponseGammaSqConst s) d C :=
        mul_le_mul_of_nonneg_left hDcap (by positivity)
      _ = 2 * (holderResponseGammaSqConst s) d C / C := by ring
  have hcap : Real.sqrt (holderResponseScoreCap s) ≤ A * Real.sqrt p0 := by
    have hleft0 : 0 ≤ Real.sqrt (holderResponseScoreCap s) := Real.sqrt_nonneg _
    have hright0 : 0 ≤ A * Real.sqrt p0 :=
      mul_nonneg hA.le (Real.sqrt_nonneg _)
    rw [← sq_le_sq₀ hleft0 hright0, mul_pow,
      Real.sq_sqrt (holderResponseScoreCap_pos s hs).le, Real.sq_sqrt hp0.le]
    exact hcapSq
  apply isBigOWith_gammaTwo_of_bounded_low_moment_growth
    hA ((measurable_holderResponseRow s) M j)
    ((holderResponseRow_nonneg s) M j) ((holderResponseRow_le_sqrt_cap s) M j)
    hcap
  intro p hp hpUpper
  have hpPos : 0 < p := zero_lt_one.trans_le hp
  by_cases hpLarge : 2 * (holderResponseMomentFloor s) d ≤ p
  · let q : ℝ := p / 2
    have hqTwo : 2 ≤ q := by
      dsimp only [q]
      have := (holderResponseMomentFloor_two_le s hs) d
      linarith
    have hqFloor : (holderResponseMomentFloor s) d ≤ q := by
      dsimp only [q]
      linarith
    have hqH : q ≤ H := by
      dsimp only [q, p0] at hpUpper ⊢
      linarith
    have hqSmall : q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ *
        |Real.log M.delta|⁻¹ := by simpa only [H, L] using hqH
    have hqDim : 2 * (d : ℝ) * (holderResponseScoreS s)⁻¹ ≤ q :=
      ((holderResponseMomentFloor_dimension s) d).trans hqFloor
    let R : ℝ := 8 * C * ((holderResponseScoreS s) ^ 2)⁻¹ * q *
      Real.log (2 + q) * M.delta ^ 2
    have hR : 0 ≤ R := by
      have hlog : 0 ≤ Real.log (2 + q) := Real.log_nonneg (by linarith)
      dsimp only [R]
      positivity
    have hnorm := hscore q (by linarith) hqSmall hqDim j
    have hmoment := (integral_holderResponseRow_rpow_le_of_score_norm s hs)
      (p := p) (R := R) M j (by
        linarith [(holderResponseMomentFloor_two_le s hs) d]) hR (by
        simpa only [R, q] using hnorm)
    have hqDelta : q ≤ (M.delta ^ 2)⁻¹ := hqH.trans hHdelta
    have hlog := log_two_add_le_four_abs_log hdelta
      M.shellPrefix.delta_le_half (by linarith : 0 ≤ q) hqDelta
    have hRsq : Real.sqrt R ≤ A * Real.sqrt p := by
      have hhigh := (holderResponseGammaSqConst_high_le (d := d) s hs) hC
      have hscaleSq := (holderResponseGammaScale_sq s hs) M hC
      have hright0 : 0 ≤ A * Real.sqrt p :=
        mul_nonneg hA.le (Real.sqrt_nonneg _)
      rw [← sq_le_sq₀ (Real.sqrt_nonneg _) hright0,
        Real.sq_sqrt hR, mul_pow, Real.sq_sqrt hpPos.le]
      rw [hscaleSq]
      dsimp only [R, A, L]
      calc
        8 * C * ((holderResponseScoreS s) ^ 2)⁻¹ * q *
              Real.log (2 + q) * M.delta ^ 2 ≤
            8 * C * ((holderResponseScoreS s) ^ 2)⁻¹ * q *
              (4 * |Real.log M.delta|) * M.delta ^ 2 := by
          gcongr
        _ = (16 * C * ((holderResponseScoreS s) ^ 2)⁻¹) *
              (M.delta ^ 2 * |Real.log M.delta|) * p := by
          dsimp only [q]
          ring
        _ ≤ (holderResponseGammaSqConst s) d C *
              (M.delta ^ 2 * |Real.log M.delta|) * p := by
          gcongr
        _ = (holderResponseGammaSqConst s) d C * M.delta ^ 2 *
              |Real.log M.delta| * p := by ring
    refine ⟨hmoment.1, hmoment.2.trans ?_⟩
    exact Real.rpow_le_rpow (Real.sqrt_nonneg R) hRsq hpPos.le
  · have hpFloor : p ≤ 2 * (holderResponseMomentFloor s) d := le_of_not_ge hpLarge
    let q0 : ℝ := (holderResponseMomentFloor s) d
    let P0 : ℝ := 2 * q0
    let R0 : ℝ := 8 * C * ((holderResponseScoreS s) ^ 2)⁻¹ * q0 *
      Real.log (2 + q0) * M.delta ^ 2
    have hq0Two : 2 ≤ q0 := (holderResponseMomentFloor_two_le s hs) d
    have hq0Small : q0 ≤ C⁻¹ * (M.delta ^ 2)⁻¹ *
        |Real.log M.delta|⁻¹ := by simpa only [q0] using hfloor
    have hq0Dim : 2 * (d : ℝ) * (holderResponseScoreS s)⁻¹ ≤ q0 :=
      (holderResponseMomentFloor_dimension s) d
    have hR0 : 0 ≤ R0 := by
      have hlog : 0 ≤ Real.log (2 + q0) := Real.log_nonneg (by
        have := (holderResponseMomentFloor_two_le s hs) d
        dsimp only [q0]
        linarith)
      dsimp only [R0]
      positivity
    have hnorm0 := hscore q0 (by linarith) hq0Small hq0Dim j
    have hP0half : P0 / 2 = q0 := by
      dsimp only [P0]
      ring
    have hmoment0 := (integral_holderResponseRow_rpow_le_of_score_norm s hs)
      (p := P0) (R := R0) M j (by
        dsimp only [P0]
        linarith) hR0 (by
          rw [hP0half]
          simpa only [R0] using hnorm0)
    have hBscale : Real.sqrt R0 ≤ A := by
      have hfloorC := holderResponseGammaSqConst_floor_le s hs (d := d) hC
      have hscaleSq := holderResponseGammaScale_sq s hs M hC
      have hlog := log_two_add_le_four_abs_log hdelta M.shellPrefix.delta_le_half
        (by linarith : 0 ≤ q0) (hfloorH.trans hHdelta)
      rw [← sq_le_sq₀ (Real.sqrt_nonneg R0) hA.le,
        Real.sq_sqrt hR0, hscaleSq]
      dsimp only [R0, q0, A]
      calc
        _ ≤ 8 * C * (holderResponseScoreS s ^ 2)⁻¹ *
              holderResponseMomentFloor s d * (4 * |Real.log M.delta|) * M.delta ^ 2 := by
          gcongr
        _ = (32 * C * (holderResponseScoreS s ^ 2)⁻¹ *
              holderResponseMomentFloor s d) * M.delta ^ 2 * |Real.log M.delta| := by ring
        _ ≤ holderResponseGammaSqConst s d C * M.delta ^ 2 * |Real.log M.delta| := by
          gcongr
    have hP0 : 0 < P0 := by
      dsimp only [P0, q0]
      linarith [(holderResponseMomentFloor_two_le s hs) d]
    have hdown := integral_nonneg_rpow_le_of_high_moment
      ((measurable_holderResponseRow s) M j) ((holderResponseRow_nonneg s) M j)
      hpPos (q := P0) (by simpa only [P0, q0] using hpFloor)
      (Real.sqrt_nonneg R0)
      hmoment0.1 hmoment0.2
    have hsqrtp : 1 ≤ Real.sqrt p := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hp
    have hbase : Real.sqrt R0 ≤ A * Real.sqrt p :=
      hBscale.trans (by nlinarith [hA])
    refine ⟨hdown.1, hdown.2.trans ?_⟩
    exact Real.rpow_le_rpow (Real.sqrt_nonneg R0) hbase hpPos.le

theorem exists_isBigOWith_gammaTwo_holderResponseRow (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        (holderResponseMomentFloor s) d ≤
          C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        ∀ j : ℕ,
          Homogenization.IndependentSums.IsBigOWith M.P.toMeasure
            (Homogenization.IndependentSums.gammaSigma 2)
            ((holderResponseRow s) M j)
            (Real.exp 1 * (holderResponseGammaScale s) M C) := by
  obtain ⟨_c, C0, _hc, hC0, hscore0⟩ :=
    (exists_holderResponseScore_norm_bound (d := d) s hs hs1)
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
  intro M hfloor j
  have hL : 0 < |Real.log M.delta| := by
    exact abs_pos.mpr (ne_of_lt (Real.log_neg M.shellPrefix.delta_pos
      (M.shellPrefix.delta_le_half.trans_lt (by norm_num))))
  have hCL : 1 ≤ C * |Real.log M.delta| := by
    calc
      1 = (Real.log 2)⁻¹ * Real.log 2 := by
        field_simp [hlogTwo.ne']
      _ ≤ C * Real.log 2 :=
        mul_le_mul_of_nonneg_right hlogInvC hlogTwo.le
      _ ≤ C * |Real.log M.delta| :=
        mul_le_mul_of_nonneg_left (log_two_le_abs_log_delta M) hC.le
  apply (isBigOWith_gammaTwo_holderResponseRow_of_score_bound s hs)
    M hC hCL hfloor _ j
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
  have hraw := hscore0 M q hq hsmall0 hdim k
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hlog : 0 ≤ Real.log (2 + q) := Real.log_nonneg (by linarith)
  have hrest : 0 ≤ ((holderResponseScoreS s) ^ 2)⁻¹ * q *
      Real.log (2 + q) * M.delta ^ 2 := by positivity
  exact hraw.trans (ENNReal.ofReal_le_ofReal (by
    calc
      8 * C0 * ((holderResponseScoreS s) ^ 2)⁻¹ * q *
          Real.log (2 + q) * M.delta ^ 2 =
          (8 * C0) * (((holderResponseScoreS s) ^ 2)⁻¹ * q *
            Real.log (2 + q) * M.delta ^ 2) := by ring
      _ ≤ (8 * C) * (((holderResponseScoreS s) ^ 2)⁻¹ * q *
            Real.log (2 + q) * M.delta ^ 2) := by gcongr
      _ = 8 * C * ((holderResponseScoreS s) ^ 2)⁻¹ * q *
          Real.log (2 + q) * M.delta ^ 2 := by ring))

end
end SubdiffusiveProcess.Section6SumErrors.Response
