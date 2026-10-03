module

public import SubdiffusiveProcess.Section6SumErrors.StoppingTail
@[expose] public section

/-!
# PaperStopping

The second half of the sum-of-errors lemma, with the measurable integer index, all-sample pathwise bound and printed exponential-moment scale.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped ENNReal BigOperators
noncomputable section

/-- The dimension-only part of the spatial-entropy coefficient. -/
def spatialBase (d : ℕ) (D : ℝ) : ℝ :=
  4 * holderErrorSpatialEntropy d * windowCoeff d D * holderLogAbsorption

theorem spatialBase_pos (d : ℕ) (D : ℝ) : 0 < spatialBase d D := by
  have hQ := zero_lt_one.trans_le (holderErrorSpatialEntropy_one_le d)
  have hK := windowCoeff_pos d D
  have hH := holderLogAbsorption_pos
  unfold spatialBase
  positivity

theorem rpow_neg_seven_halves_sq {s : ℝ} (hs : 0 < s) :
    (s ^ (-7 / 2 : ℝ)) ^ (2 : ℕ) = s ^ (-7 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
  norm_num

theorem rpow_neg_two_eq_inv_sq {lam : ℝ} (hlam : 0 < lam) : lam ^ (-2 : ℝ) = (lam ^ 2)⁻¹ := by
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hlam.le, Real.rpow_two]

theorem stopping_bound {d : ℕ} [NeZero d]
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {D C : ℝ} (hD : 0 < D)
    (hbase : spatialBase d D ≤ C) (hsq : 4 * spatialBase d D ^ 2 ≤ C)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) (holderResponseRow s M j)
      (Real.exp 1 * holderResponseGammaScale s M D))
    (hmean : ∀ j : ℕ, ∫ ω, holderResponseRow s M j ω ∂M.P.toMeasure ≤ rowMeanCoeff s d D * M.delta)
    (lam : ℝ) (hlam : 0 < lam)
    (hthreshold : C * s ^ (-7 / 2 : ℝ) * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ) ≤ lam)
    (m : ℕ) :
    ∃ Mrv : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℤ,
      Measurable Mrv ∧ (∀ ω, -1 ≤ Mrv ω ∧ Mrv ω ≤ (m : ℤ)) ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp
        ((C * s ^ (-7 : ℝ) * M.delta ^ 2 * |Real.log M.delta| * lam ^ (-2 : ℝ))⁻¹ *
          max ((m : ℝ) - (Mrv ω : ℝ) - 1) 0)) ∂M.P.toMeasure ≤ 2 ∧
      ∀ ω, ∀ n : ℕ, (n : ℤ) ≤ Mrv ω →
        ∀ z : Homogenization.Vec d, OnTriadicGrid n z → z ∈ cube d m →
          ∑ j ∈ Finset.Icc n m, accumulatedError M none j z s ω ≤ lam * ((m : ℝ) - (n : ℝ)) := by
  let U := s ^ (-7 / 2 : ℝ)
  let L := Real.sqrt |Real.log M.delta|
  let den := spatialBase d D * U * M.delta * L
  let u := lam / den
  let A := (u ^ 2)⁻¹
  let B := C * s ^ (-7 : ℝ) * M.delta ^ 2 * |Real.log M.delta| * lam ^ (-2 : ℝ)
  have hd := M.shellPrefix.delta_pos
  have hU : 0 < U := Real.rpow_pos_of_pos hs _
  have hL : 0 < L := Real.sqrt_pos.mpr (abs_pos.mpr
    (Real.log_neg hd (M.shellPrefix.delta_le_half.trans_lt (by norm_num))).ne)
  have hbase0 := spatialBase_pos d D
  have hC : 0 < C := hbase0.trans_le hbase
  have hden : 0 < den := by dsimp only [den]; positivity
  have hdenlam : den ≤ lam := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbase hU.le) hd.le) hL.le
    apply h.trans
    simpa only [U, L, Real.sqrt_eq_rpow] using hthreshold
  have hu : 1 ≤ u := by dsimp only [u]; rw [le_div_iff₀ hden]; simpa using hdenlam
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hA : 0 < A := inv_pos.mpr (sq_pos_of_pos hu0)
  have hB : 0 < B := by
    have hl : 0 < |Real.log M.delta| := (Real.sqrt_pos.mp hL)
    dsimp only [B]
    positivity
  have hlambda : spatialCoeff s d D * M.delta * Real.sqrt |Real.log M.delta| * u ≤ lam := by
    have heq : spatialCoeff s d D * M.delta * Real.sqrt |Real.log M.delta| = den := by
      dsimp only [spatialCoeff, tailWindowCoeff, spatialBase, den, U, L]
      ring
    rw [heq]
    dsimp only [u]
    exact le_of_eq (mul_div_cancel₀ lam hden.ne')
  have htail : ∀ q : ℕ, 1 ≤ q → M.P.toMeasure.real
      {ω | q < errorStoppingDepth M lam s m ω} ≤ 2 * Real.exp (-((q : ℝ) / A)) := by
    intro q hq
    have h := stoppingDepth_tail s hs hs1 M hD hu hrow hmean hlambda q m hq
    simpa only [A, div_inv_eq_mul, mul_comm] using h
  have hmoment := lintegral_stoppingIndex_excess_le_of_tail M lam s m hA htail
  have hscale : 4 * A ≤ B := by
    have heq : 4 * A = 4 * spatialBase d D ^ 2 * s ^ (-7 : ℝ) * M.delta ^ 2 *
        |Real.log M.delta| * lam ^ (-2 : ℝ) := by
      have hLs : L ^ 2 = |Real.log M.delta| := Real.sq_sqrt (abs_nonneg _)
      dsimp only [A, u]
      rw [div_pow, inv_div]
      dsimp only [den]
      rw [mul_pow, mul_pow, mul_pow, hLs]
      rw [show U ^ 2 = s ^ (-7 : ℝ) from rpow_neg_seven_halves_sq hs, rpow_neg_two_eq_inv_sq hlam]
      ring
    rw [heq]
    dsimp only [B]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs.le _)) (sq_nonneg _)) (abs_nonneg _))
      (Real.rpow_nonneg hlam.le _)
  refine ⟨stoppingIndex M lam s m, measurable_stoppingIndex M lam s m,
    stoppingIndex_bounds M lam s m, ?_, ?_⟩
  · apply le_trans _ hmoment
    apply lintegral_mono
    intro ω
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (le_max_right _ _)
    exact (inv_le_inv₀ hB (by positivity)).mpr hscale
  · exact fun ω n hn z hz hzc => sum_le_of_le_stoppingIndex M lam s m ω n hn z hz hzc

end
end SubdiffusiveProcess.Section6SumErrors.Response
