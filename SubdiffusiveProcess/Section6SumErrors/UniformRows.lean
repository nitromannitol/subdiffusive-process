module

public import SubdiffusiveProcess.Section6SumErrors.WindowConstants
@[expose] public section

/-!
# UniformRows

A single response-moment constant chosen before s and the model; both row means and Gaussian tails use that constant.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators ENNReal
noncomputable section
theorem exists_uniformScore_bound {d : ℕ} [NeZero d] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (q : ℝ),
        1 ≤ q →
        q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        2 * (d : ℝ) * (holderResponseScoreS s)⁻¹ ≤ q →
        ∀ j : ℕ,
          paperENNRealLpNorm M.P.toMeasure q
              (localResponseScore M (holderResponseScoreS s) 1 1 j) ≤
            ENNReal.ofReal
              (8 * C * ((holderResponseScoreS s) ^ 2)⁻¹ * q *
                Real.log (2 + q) * M.delta ^ 2) := by
  obtain ⟨c, C, hc, hC, hmoment⟩ :=
    exists_localResponseScore_moment_bound (d := d)
  refine ⟨c, C, hc, hC, ?_⟩
  intro s hs hs1 M q hq hsmall hdim j
  have hraw := hmoment M q hq hsmall (holderResponseScoreS s) 1 1 j
  have hsum := responseScore_geometric_sum_le (j := j)
    (holderResponseScoreS_pos s hs) (holderResponseScoreS_le_one s hs1)
    (zero_lt_one.trans_le hq) hdim
  have hA0 : 0 ≤ C * q * Real.log (2 + q) * M.delta ^ 2 := by
    have hlog : 0 ≤ Real.log (2 + q) :=
      Real.log_nonneg (by linarith)
    positivity
  have hfactor :
      (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹ *
            ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2)) =
        (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹) *
          ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
    exact (Finset.sum_mul (s := Finset.range (j - 1))
      (f := fun n ↦
        ENNReal.ofReal
            ((3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))) *
          ((descendantsAtScale
            (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹)
      (ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2))).symm
  calc
    paperENNRealLpNorm M.P.toMeasure q
        (localResponseScore M (holderResponseScoreS s) 1 1 j) ≤
      ENNReal.ofReal (2 * (holderResponseScoreS s)⁻¹) *
        ∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹ *
            ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
      simpa only [one_pow, inv_one, mul_one] using hraw
    _ = ENNReal.ofReal (2 * (holderResponseScoreS s)⁻¹) *
        (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal
              ((3 : ℝ) ^ (-(holderResponseScoreS s) * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ q⁻¹) *
          ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
      rw [hfactor]
      ring

    _ ≤ ENNReal.ofReal (2 * (holderResponseScoreS s)⁻¹) *
        ENNReal.ofReal (4 / (holderResponseScoreS s)) *
          ENNReal.ofReal (C * q * Real.log (2 + q) * M.delta ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (zero_le)) (zero_le)
    _ = ENNReal.ofReal
        (8 * C * ((holderResponseScoreS s) ^ 2)⁻¹ * q *
          Real.log (2 + q) * M.delta ^ 2) := by
      have htInv : 0 ≤ (holderResponseScoreS s)⁻¹ :=
        inv_nonneg.mpr (holderResponseScoreS_pos s hs).le
      have hleft : 0 ≤ 2 * (holderResponseScoreS s)⁻¹ := by positivity
      have hright : 0 ≤ 4 / (holderResponseScoreS s) :=
        div_nonneg (by norm_num) (holderResponseScoreS_pos s hs).le
      rw [← ENNReal.ofReal_mul hleft,
        ← ENNReal.ofReal_mul (mul_nonneg hleft hright)]
      congr 1
      field_simp [(holderResponseScoreS_pos s hs).ne']
      ring



theorem exists_uniformRow_bounds {d : ℕ} [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        holderResponseMomentFloor s d ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        (∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
          (IndependentSums.gammaSigma 2) (holderResponseRow s M j)
          (Real.exp 1 * holderResponseGammaScale s M C)) ∧
        (∀ j : ℕ, ∫ ω, holderResponseRow s M j ω ∂M.P.toMeasure ≤
          rowMeanCoeff s d C * M.delta) := by
  obtain ⟨_c, C0, _hc, hC0, hscore0⟩ := exists_uniformScore_bound (d := d)
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
  intro s hs hs1 M hfloor
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
  have hscore : ∀ (q : ℝ), 1 ≤ q →
      q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
      2 * (d : ℝ) * (holderResponseScoreS s)⁻¹ ≤ q →
      ∀ j : ℕ,
        paperENNRealLpNorm M.P.toMeasure q
            (localResponseScore M (holderResponseScoreS s) 1 1 j) ≤
          ENNReal.ofReal
            (8 * C * ((holderResponseScoreS s) ^ 2)⁻¹ * q *
              Real.log (2 + q) * M.delta ^ 2) := by
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
    have hraw := hscore0 s hs hs1 M q hq hsmall0 hdim k
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

  constructor
  · exact fun j => isBigOWith_gammaTwo_holderResponseRow_of_score_bound s hs M hC hCL hfloor hscore j
  · exact fun j => integral_row_le_meanCoeff s hs M hC hfloor hscore j

end
end SubdiffusiveProcess.Section6SumErrors.Response
