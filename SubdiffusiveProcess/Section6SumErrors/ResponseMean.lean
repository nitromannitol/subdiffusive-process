module

public import SubdiffusiveProcess.Section6SumErrors.ResponseGamma

@[expose] public section

/-!
# ResponseMean

The deterministic response-row mean from a single admissible score moment, without a logarithmic delta factor.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped ENNReal
noncomputable section

/-- The low-moment response mean has no dependence on `log delta`. -/
def rowMeanCoeff (s : ℝ) (d : ℕ) (C : ℝ) : ℝ :=
  Real.sqrt (8 * C * (holderResponseScoreS s ^ 2)⁻¹ *
    holderResponseMomentFloor s d * Real.log (2 + holderResponseMomentFloor s d))

theorem integral_row_le_meanCoeff {d : ℕ} [NeZero d]
    (s : ℝ) (hs : 0 < s)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {C : ℝ} (hC : 0 < C)
    (hfloor : holderResponseMomentFloor s d ≤
      C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹)
    (hscore : ∀ q : ℝ, 1 ≤ q →
      q ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
      2 * (d : ℝ) * (holderResponseScoreS s)⁻¹ ≤ q →
      ∀ j : ℕ, paperENNRealLpNorm M.P.toMeasure q
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.localResponseScore M
          (holderResponseScoreS s) 1 1 j) ≤
        ENNReal.ofReal (8 * C * (holderResponseScoreS s ^ 2)⁻¹ * q *
          Real.log (2 + q) * M.delta ^ 2))
    (j : ℕ) :
    ∫ omega, holderResponseRow s M j omega ∂M.P.toMeasure ≤
      rowMeanCoeff s d C * M.delta := by
  let q := holderResponseMomentFloor s d
  let B := 8 * C * (holderResponseScoreS s ^ 2)⁻¹ * q * Real.log (2 + q)
  have hq : 2 ≤ q := holderResponseMomentFloor_two_le s hs d
  have hB : 0 ≤ B := by
    have hl : 0 ≤ Real.log (2 + q) := Real.log_nonneg (by linarith)
    dsimp only [B]
    positivity
  have hnorm := hscore q (by linarith) hfloor
    (holderResponseMomentFloor_dimension s d) j
  have hm := integral_holderResponseRow_rpow_le_of_score_norm s hs M j
    (p := 2 * q) (by linarith) (R := B * M.delta ^ 2) (by positivity)
    (by simpa only [B, show 2 * q / 2 = q by ring] using hnorm)
  have hdown := integral_nonneg_rpow_le_of_high_moment
    (measurable_holderResponseRow s M j)
    (holderResponseRow_nonneg s M j)
    (p := 1) (q := 2 * q) (by norm_num) (by linarith)
    (Real.sqrt_nonneg (B * M.delta ^ 2)) hm.1 hm.2
  simp only [Real.rpow_one] at hdown
  calc
    _ ≤ Real.sqrt (B * M.delta ^ 2) := hdown.2
    _ = rowMeanCoeff s d C * M.delta := by
      rw [Real.sqrt_mul hB, Real.sqrt_sq M.shellPrefix.delta_pos.le]
      rfl

end
end SubdiffusiveProcess.Section6SumErrors.Response
