import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.SharpMeanWindow
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedAccumulatedErrorWindow

/-!
# The accumulated-error window with a sharp (log-free) response mean

The last level of the sharp-mean chain: the finite-cutoff accumulated-error
window, with the response mean slot carrying an arbitrary valid first-moment
bound `mu1` instead of the Gamma-two surrogate `gammaMomentConst 2 · A`.

Only the response component moves.  The field-low, field-active and gradient
components are reproduced verbatim from the landed lemmas, and the
fluctuation carrier
`Section6Cutoff.cutoffParameterizedAccumulatedErrorWindowFluctuation` is
literally unchanged — so the landed
`isBigO_cutoffParameterizedAccumulatedErrorWindowFluctuation` still supplies
its Gamma-two scale verbatim.

This is the shape conjunct (2) of `p.cutoff.regularity.good.scales` consumes:
the printed estimate puts `|log δ|^{1/2}` in the `O_{Γ_2}` scale but *not* in
the subtracted mean, and that is exactly the split produced here.

Additive only: no landed declaration is modified.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The accumulated-error window mean bound with a sharp response slot.
Identical to
`Section6Cutoff.cutoffParameterizedAccumulatedErrorWindowMeanBound` except
that `gammaMomentConst 2 · A` is replaced by `mu1`. -/
def cutoffParameterizedAccumulatedErrorWindowSharpMeanBound {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s mu1 : ℝ) (n m : ℕ) : ℝ :=
  ((m + 1 - n : ℕ) : ℝ) *
    (2 * (8 / s) * mu1 +
      2 * (IndependentSums.gammaMomentConst 2 *
        accumulatedFiniteFieldScaleBound M s) +
      (3 / 2 : ℝ) *
        (IndependentSums.gammaMomentConst 2 *
          accumulatedGradientOwnRowScale M))

/-- The arbitrary-`s` finite-cutoff accumulated-error window, with the
response mean slot sharpened to any valid first-moment bound. -/
theorem ae_sum_cutoffParameterizedAccumulatedError_le_sharp_mean
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {mu1 : ℝ}
    (hmu1 : ∀ j : ℕ,
      ∫ eta, cutoffParameterizedResponseRow M L s j eta ∂M.P.toMeasure ≤ mu1) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑ k ∈ Finset.Icc n m,
        accumulatedError M (some L) k z s omega) ≤
        cutoffParameterizedAccumulatedErrorWindowSharpMeanBound M s mu1 n m +
          cutoffParameterizedAccumulatedErrorWindowFluctuation
            M L s z n m omega := by
  have hresponse :=
    ae_sum_translatedCutoffParameterizedAccumulatedResponseSup_le_sharp_mean
      M L hs hs1 z hnm hmu1
  have hs8 : s / 8 ≤ 1 := by linarith
  filter_upwards [hresponse, ae_sum_accumulatedGradientSuffix_le M z hnm]
    with omega hresp hgrad
  have hfinite :=
    sum_translatedBlockSup_add_shellZero_le_finiteFieldWindowConvolution
      z hs n m omega
  have hfieldEq := accumulatedFiniteFieldWindowConvolution_eq_low_add_active
    z s hnm omega
  have hfieldActive := accumulatedFiniteFieldActiveWindow_le_centered_add_mean
    M z hs hs8 hnm omega
  have hgradMean := sum_accumulatedGradientOwnRow_le_centered_add_mean
    M z n m omega
  have hcarrier :
      (∑ k ∈ Finset.Icc n m,
        accumulatedError M (some L) k z s omega) ≤
        (∑ k ∈ Finset.Icc n m,
          translatedCutoffParameterizedAccumulatedResponseSup
            M L s k z omega) +
        2 * (accumulatedFiniteFieldLowWindow z s n m omega +
          accumulatedFiniteFieldActiveWindow z s n m omega) +
        (3 / 2 : ℝ) *
          ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
            accumulatedGradientEnvelope m z omega) := by
    calc
      (∑ k ∈ Finset.Icc n m,
          accumulatedError M (some L) k z s omega) =
        (∑ k ∈ Finset.Icc n m,
          translatedCutoffParameterizedAccumulatedResponseSup
            M L s k z omega) +
        (∑ k ∈ Finset.Icc n m,
          (translatedAccumulatedBlockSup k z s omega +
            (3 : ℝ) ^ (-(s / 8) * k) *
              supNormOn (translatedCube d (k : ℤ) z) (omega 0))) +
        (∑ k ∈ Finset.Icc n m, ∑' j : ℕ, if k ≤ j then
          (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
            (shellGradient (omega j)) else 0) := by
          simp_rw [accumulatedError_some_eq_parameterized_parts]
          simp_rw [Finset.sum_add_distrib]
          ring
      _ ≤ (∑ k ∈ Finset.Icc n m,
            translatedCutoffParameterizedAccumulatedResponseSup
              M L s k z omega) +
          2 * accumulatedFiniteFieldWindowConvolution z s n m omega +
          (3 / 2 : ℝ) *
            ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
              accumulatedGradientEnvelope m z omega) := by linarith
      _ = _ := by rw [hfieldEq]
  unfold cutoffParameterizedAccumulatedResponseWindowSharpMeanBound at hresp
  unfold cutoffParameterizedAccumulatedErrorWindowSharpMeanBound
    cutoffParameterizedAccumulatedErrorWindowFluctuation
  calc
    _ ≤ (∑ k ∈ Finset.Icc n m,
          translatedCutoffParameterizedAccumulatedResponseSup
            M L s k z omega) +
        2 * (accumulatedFiniteFieldLowWindow z s n m omega +
          accumulatedFiniteFieldActiveWindow z s n m omega) +
        (3 / 2 : ℝ) *
          ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
            accumulatedGradientEnvelope m z omega) := hcarrier
    _ ≤ ((m + 1 - n : ℕ) : ℝ) * (2 * (8 / s) * mu1) +
          cutoffParameterizedAccumulatedResponseWindowFluctuation
            M L s z n m omega +
        2 * (accumulatedFiniteFieldLowWindow z s n m omega +
          (centeredAccumulatedFiniteFieldActiveWindow M z s n m omega +
            ((m + 1 - n : ℕ) : ℝ) *
              (IndependentSums.gammaMomentConst 2 *
                accumulatedFiniteFieldScaleBound M s))) +
        (3 / 2 : ℝ) *
          ((centeredAccumulatedGradientWindow M z n m omega +
              ((m + 1 - n : ℕ) : ℝ) *
                (IndependentSums.gammaMomentConst 2 *
                  accumulatedGradientOwnRowScale M)) +
            accumulatedGradientEnvelope m z omega) := by gcongr
    _ = _ := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
