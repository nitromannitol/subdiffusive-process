module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.SharpMeanScaleBound

@[expose] public section

/-!
# Discharging `CutoffParameterizedErrorWindowInput`

`ErrorWindowGeneric.CutoffParameterizedErrorWindowInput` was the single named
input that conjunct (3) waited on, and (via Appendix D.3) the shared obligation
of conjunct (2).  Both halves are now proved:

* mean — `SharpMeanScaleBound.cutoffParameterizedAccumulatedErrorWindowMeanBound_le`;
* fluctuation —
  `SharpFluctuationScaleBound.cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen_sharp_le`.

They come with different constants, so the discharge takes their sum and uses
monotonicity of `errorWindowScale` in `Cw`.  The budget parameter `Kw` is
unused — the sharp bounds hold for every `0 < s ≤ 1` — so it is witnessed by `1`;
the predicate keeps the binder only so the downstream stopping chain, which
threads `Kw` into its own constant, does not have to change shape.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

theorem errorWindowScale_mono {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    {Cw Cw' s : ℝ} (hs : 0 < s) (h : Cw ≤ Cw') :
    errorWindowScale M Cw s ≤ errorWindowScale M Cw' s := by
  unfold errorWindowScale
  have h1 : (0:ℝ) ≤ s ^ (-7 / 2 : ℝ) := (Real.rpow_pos_of_pos hs _).le
  have h2 : (0:ℝ) ≤ M.delta := M.shellPrefix.delta_pos.le
  have h3 : (0:ℝ) ≤ Real.sqrt |Real.log M.delta| := Real.sqrt_nonneg _
  have hstep : Cw * s ^ (-7 / 2 : ℝ) * M.delta ≤
      Cw' * s ^ (-7 / 2 : ℝ) * M.delta :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h h1) h2
  exact mul_le_mul_of_nonneg_right hstep h3

/-- **The named window input is no longer an input.** -/
theorem cutoffParameterizedErrorWindowInput_holds (d : ℕ) [NeZero d] :
    CutoffParameterizedErrorWindowInput d := by
  intro Crow hCrow
  have hmean : 0 < sharpErrorWindowMeanConst d Crow :=
    sharpErrorWindowMeanConst_pos hCrow
  have hfluct : 0 < sharpErrorWindowConst d Crow :=
    sharpErrorWindowConst_pos hCrow
  refine ⟨1, sharpErrorWindowMeanConst d Crow + sharpErrorWindowConst d Crow,
    one_pos, by linarith, ?_⟩
  intro M s hs hs1 _hbudget n m hnm
  refine ⟨?_, ?_⟩
  · refine (cutoffParameterizedAccumulatedErrorWindowMeanBound_le
      M hCrow hs hs1 n m).trans ?_
    exact mul_le_mul_of_nonneg_left
      (errorWindowScale_mono M hs (by linarith)) (Nat.cast_nonneg _)
  · refine (cutoffParameterizedAccumulatedErrorWindowFluctuationScaleGen_sharp_le
      M hCrow hs hs1 hnm).trans ?_
    exact mul_le_mul_of_nonneg_right
      (errorWindowScale_mono M hs (by linarith)) (Real.sqrt_nonneg _)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
