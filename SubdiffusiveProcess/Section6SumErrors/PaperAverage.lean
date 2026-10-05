module

public import SubdiffusiveProcess.Section6SumErrors.AverageMoment
@[expose] public section

/-!
# PaperAverage

The first half of the sum-of-errors lemma, retaining the literal window length and both printed powers of s.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped ENNReal BigOperators
noncomputable section

theorem rpow_neg_half_mul_self (W : ℝ) (hW : 0 < W) : W ^ (-1 / 2 : ℝ) * W = Real.sqrt W := by
  rw [show (-1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, Real.rpow_sub hW, Real.rpow_one]
  rw [div_mul_cancel₀ _ hW.ne', Real.sqrt_eq_rpow]

theorem average_bound {d : ℕ} [NeZero d]
    (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {D C : ℝ} (hD : 0 < D)
    (htwo : 2 * windowCoeff d D ≤ C)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) (holderResponseRow s M j)
      (Real.exp 1 * holderResponseGammaScale s M D))
    (hmean : ∀ j : ℕ, ∫ ω, holderResponseRow s M j ω ∂M.P.toMeasure ≤ rowMeanCoeff s d D * M.delta)
    {n m : ℕ} (hnm : n ≤ m) (z : Homogenization.Vec d) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
      (((C * s ^ (-7 / 2 : ℝ) * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ) *
        ((m : ℝ) - (n : ℝ) + 1) ^ (-1 / 2 : ℝ))⁻¹ *
        max ((∑ k ∈ Finset.Icc n m, accumulatedError M none k z s ω) /
          ((m : ℝ) - (n : ℝ) + 1) - C * s ^ (-7 / 2 : ℝ) * M.delta) 0) ^ (2 : ℕ))) ∂M.P.toMeasure ≤ 2 := by
  let W : ℝ := (m : ℝ) - (n : ℝ) + 1
  let U : ℝ := s ^ (-7 / 2 : ℝ)
  let L : ℝ := Real.sqrt |Real.log M.delta|
  let V : ℝ := windowCoeff d D * U * M.delta * L * Real.sqrt W
  let B : ℝ := C * U * M.delta * L * W ^ (-1 / 2 : ℝ)
  have hW : 0 < W := by
    have hcast : (n : ℝ) ≤ m := by exact_mod_cast hnm
    dsimp only [W]
    linarith
  have hWcast : ((m + 1 - n : ℕ) : ℝ) = W := by
    rw [Nat.cast_sub (by omega : n ≤ m + 1), Nat.cast_add, Nat.cast_one]
    dsimp only [W]
    ring
  have hL : 0 < L := Real.sqrt_pos.mpr (abs_pos.mpr
    (Real.log_neg M.shellPrefix.delta_pos (M.shellPrefix.delta_le_half.trans_lt (by norm_num))).ne)
  have hU : 0 < U := Real.rpow_pos_of_pos hs _
  have hd := M.shellPrefix.delta_pos
  have hK := windowCoeff_pos d D
  have hC : 0 < C := by linarith
  have hV : 0 < V := by dsimp only [V]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hfluct := isBigO_accumulatedErrorWindowFluctuation s hs hs1 M z hnm
    (mul_pos (Real.exp_pos 1) (holderResponseGammaScale_pos s hs M hD)) hrow
  have hfluct' : IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (accumulatedErrorWindowFluctuation s M z n m) V := by
    apply hfluct.mono_scale
    simpa only [V, U, L, hWcast] using fluctuationScale_le M hs hs1 hD hnm
  have hupper := ae_sum_accumulatedError_le_mean_add_fluctuation s hs hs1 M z hnm
    (rowMeanCoeff s d D * M.delta) hmean
  have ha : accumulatedErrorWindowMeanBound s M
      (rowMeanCoeff s d D * M.delta) n m ≤
      W * (C * U * M.delta) := by
    apply (meanBound_le M hs hs1 hD n m).trans
    have hKC : windowCoeff d D ≤ C := by linarith
    rw [hWcast]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC hU.le) hd.le) hW.le
  have hscale : 2 * V ≤ B * W := by
    have h := mul_le_mul_of_nonneg_right htwo
      (show 0 ≤ U * M.delta * L * Real.sqrt W by positivity)
    dsimp only [V, B]
    rw [mul_assoc (C * U * M.delta * L), rpow_neg_half_mul_self W hW]
    convert h using 1 <;> ring
  have hout := lintegral_average_exp_square_le hW hV hB
    (aemeasurable_fluctuation s M z n m) hfluct' hupper ha hscale
  simpa only [B, W, U, L, Real.sqrt_eq_rpow] using hout

end
end SubdiffusiveProcess.Section6SumErrors.Response
