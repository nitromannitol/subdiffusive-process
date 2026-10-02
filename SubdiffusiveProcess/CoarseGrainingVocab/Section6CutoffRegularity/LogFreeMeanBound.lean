import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.SharpMeanScaleBound
import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.SharpMeanAccumulated

/-!
# The log-free mean bound

Conjunct (2) of `p.cutoff.regularity.good.scales` subtracts `C * s ^ (-7/2) * delta`
from the window average — with **no** `√|log delta|`.  So unlike the window input
of `SharpMeanScaleBound.lean`, whose target `errorWindowScale` carries the
logarithm, this bound must be genuinely log-free.

That is exactly what the sharp-mean chain of Appendices B–D was built for: with
the response slot carrying the *direct* first-moment bound
`mu1 ≤ Cr * s ^ (-2) * delta` of `ResponseFirstMoment.lean` in place of the
`Gamma`-two surrogate `gammaMomentConst 2 * A ≍ s^{-3/2} delta √|log delta|`,
every slot of `cutoffParameterizedAccumulatedErrorWindowSharpMeanBound` is a pure
multiple of `delta` times a power of `s`, with no logarithm anywhere.

Slot weights: response `s^{-3}`, field `s^{-3/2}`, gradient `s^0` — all inside
`s^{-7/2}`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

theorem zpow_neg_two_eq {s : ℝ} : s ^ (-2 : ℤ) = (s⁻¹) ^ 2 := by
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, inv_pow]

/-- Raise a bare `v ^ 3` monomial by the `u ≥ 1` factor. -/
theorem monoV3 {u v del : ℝ} (hu : 1 ≤ u) (hv : 0 ≤ v) (hdel : 0 ≤ del) :
    v ^ 3 * del ≤ u * v ^ 3 * del := by
  have h : v ^ 3 * del ≤ u * (v ^ 3 * del) :=
    le_mul_of_one_le_left (by positivity) hu
  exact h.trans_eq (by ring)

/-- `s ^ (-7/2) * delta`, written multiplicatively. -/
def logFreeMasterScale {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s : ℝ) : ℝ :=
  (Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta

theorem logFreeMasterScale_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s : ℝ} (hs : 0 < s) :
    logFreeMasterScale M s = s ^ (-7 / 2 : ℝ) * M.delta := by
  unfold logFreeMasterScale
  rw [rpow_neg_seven_halves hs]

/-- Constant of the log-free mean bound. -/
def logFreeMeanConst (d : ℕ) (Cr : ℝ) : ℝ :=
  16 * Cr +
    (2 * IndependentSums.gammaMomentConst 2 *
        IndependentSums.gammaTriangleConst 2 * fieldOneCubeMajorantZeroConst d +
      256 * IndependentSums.gammaMomentConst 2 *
        IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 *
        fieldOneGammaDimConst d) +
    (3 / 2 : ℝ) * IndependentSums.gammaMomentConst 2 * gradientOwnRowConst d

theorem logFreeMeanConst_pos {d : ℕ} {Cr : ℝ} (hCr : 0 < Cr) :
    0 < logFreeMeanConst d Cr := by
  have hmom : (0:ℝ) < IndependentSums.gammaMomentConst 2 :=
    IndependentSums.gammaMomentConst_pos (by norm_num)
  have hT : (0:ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hS8 : (0:ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hcD := fieldOneGammaDimConst_nonneg d
  have hc0 := fieldOneCubeMajorantZeroConst_nonneg d
  have hcg := gradientOwnRowConst_nonneg d
  unfold logFreeMeanConst
  have h1 : (0:ℝ) < 16 * Cr := by linarith
  have h2 : (0:ℝ) ≤ 2 * IndependentSums.gammaMomentConst 2 *
      IndependentSums.gammaTriangleConst 2 * fieldOneCubeMajorantZeroConst d := by
    positivity
  have h3 : (0:ℝ) ≤ 256 * IndependentSums.gammaMomentConst 2 *
      IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 *
      fieldOneGammaDimConst d := by positivity
  have h4 : (0:ℝ) ≤ (3 / 2 : ℝ) * IndependentSums.gammaMomentConst 2 *
      gradientOwnRowConst d := by positivity
  linarith

/-- **The log-free mean bound.**  Every slot of the sharp mean is a multiple of
`delta` times a power of `s` at most `7/2`, with no `|log delta|`. -/
theorem cutoffParameterizedAccumulatedErrorWindowSharpMeanBound_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {s mu1 Cr : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hCr : 0 ≤ Cr)
    (hmu1 : mu1 ≤ Cr * s ^ (-2 : ℤ) * M.delta) (n m : ℕ) :
    cutoffParameterizedAccumulatedErrorWindowSharpMeanBound M s mu1 n m ≤
      ((m + 1 - n : ℕ) : ℝ) *
        (logFreeMeanConst d Cr * s ^ (-7 / 2 : ℝ) * M.delta) := by
  have hu := one_le_inv_sqrt hs hs1
  have hv := one_le_inv hs hs1
  have hdel := M.shellPrefix.delta_pos
  have hmom : (0:ℝ) < IndependentSums.gammaMomentConst 2 :=
    IndependentSums.gammaMomentConst_pos (by norm_num)
  have hT : (0:ℝ) < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hS8 : (0:ℝ) < Real.sqrt 8 := Real.sqrt_pos.mpr (by norm_num)
  have hcD := fieldOneGammaDimConst_nonneg d
  have hc0 := fieldOneCubeMajorantZeroConst_nonneg d
  have hcg := gradientOwnRowConst_nonneg d
  have hW : (0:ℝ) ≤ ((m + 1 - n : ℕ) : ℝ) := Nat.cast_nonneg _
  -- response slot
  have hresp : 2 * (8 / s) * mu1 ≤
      (16 * Cr) * ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta) := by
    have hmul : 2 * (8 / s) * mu1 ≤ 2 * (8 / s) * (Cr * s ^ (-2 : ℤ) * M.delta) := by
      refine mul_le_mul_of_nonneg_left hmu1 ?_
      have : (0:ℝ) ≤ 8 / s := by positivity
      linarith
    refine hmul.trans ?_
    have heq : 2 * (8 / s) * (Cr * s ^ (-2 : ℤ) * M.delta)
        = (16 * Cr) * ((s⁻¹) ^ 3 * M.delta) := by
      rw [zpow_neg_two_eq]
      simp only [div_eq_mul_inv]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (monoV3 (u := (Real.sqrt s)⁻¹) (v := s⁻¹) (del := M.delta) hu
        (by linarith) hdel.le) (by linarith)
  -- field slot
  have hfield : 2 * (IndependentSums.gammaMomentConst 2 *
      accumulatedFiniteFieldScaleBound M s) ≤
      (2 * IndependentSums.gammaMomentConst 2 *
          IndependentSums.gammaTriangleConst 2 *
          fieldOneCubeMajorantZeroConst d +
        256 * IndependentSums.gammaMomentConst 2 *
          IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 *
          fieldOneGammaDimConst d) *
        ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta) := by
    have hC1 : (0:ℝ) ≤ 2 * IndependentSums.gammaMomentConst 2 *
        IndependentSums.gammaTriangleConst 2 *
        fieldOneCubeMajorantZeroConst d := by positivity
    have hC2 : (0:ℝ) ≤ 256 * IndependentSums.gammaMomentConst 2 *
        IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 *
        fieldOneGammaDimConst d := by positivity
    have h1 := mul_le_mul_of_nonneg_left
      (monoBaseNoW (u := (Real.sqrt s)⁻¹) (v := s⁻¹) (del := M.delta)
        hu hv hdel.le) hC1
    have h2 := mul_le_mul_of_nonneg_left
      (monoUV1NoW (u := (Real.sqrt s)⁻¹) (v := s⁻¹) (del := M.delta)
        (by linarith) hv hdel.le) hC2
    calc 2 * (IndependentSums.gammaMomentConst 2 *
            accumulatedFiniteFieldScaleBound M s)
        = (2 * IndependentSums.gammaMomentConst 2 *
              IndependentSums.gammaTriangleConst 2 *
              fieldOneCubeMajorantZeroConst d) * M.delta +
          (256 * IndependentSums.gammaMomentConst 2 *
              IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 *
              fieldOneGammaDimConst d) *
            ((Real.sqrt s)⁻¹ * s⁻¹ * M.delta) := by
          rw [accumulatedFiniteFieldScaleBound_eq M hs]; ring
      _ ≤ (2 * IndependentSums.gammaMomentConst 2 *
              IndependentSums.gammaTriangleConst 2 *
              fieldOneCubeMajorantZeroConst d) *
            ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta) +
          (256 * IndependentSums.gammaMomentConst 2 *
              IndependentSums.gammaTriangleConst 2 * Real.sqrt 8 *
              fieldOneGammaDimConst d) *
            ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta) := add_le_add h1 h2
      _ = _ := by ring
  -- gradient slot
  have hgrad : (3 / 2 : ℝ) * (IndependentSums.gammaMomentConst 2 *
      accumulatedGradientOwnRowScale M) ≤
      ((3 / 2 : ℝ) * IndependentSums.gammaMomentConst 2 *
        gradientOwnRowConst d) *
        ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta) := by
    have hC : (0:ℝ) ≤ (3 / 2 : ℝ) * IndependentSums.gammaMomentConst 2 *
        gradientOwnRowConst d := by positivity
    calc (3 / 2 : ℝ) * (IndependentSums.gammaMomentConst 2 *
            accumulatedGradientOwnRowScale M)
        = ((3 / 2 : ℝ) * IndependentSums.gammaMomentConst 2 *
            gradientOwnRowConst d) * M.delta := by
          rw [accumulatedGradientOwnRowScale_eq]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (monoBaseNoW (u := (Real.sqrt s)⁻¹) (v := s⁻¹) (del := M.delta)
            hu hv hdel.le) hC
  have hbracket : 2 * (8 / s) * mu1 +
      2 * (IndependentSums.gammaMomentConst 2 *
        accumulatedFiniteFieldScaleBound M s) +
      (3 / 2 : ℝ) * (IndependentSums.gammaMomentConst 2 *
        accumulatedGradientOwnRowScale M) ≤
      logFreeMeanConst d Cr *
        ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta) := by
    refine (add_le_add (add_le_add hresp hfield) hgrad).trans (le_of_eq ?_)
    unfold logFreeMeanConst
    ring
  unfold cutoffParameterizedAccumulatedErrorWindowSharpMeanBound
  calc ((m + 1 - n : ℕ) : ℝ) *
        (2 * (8 / s) * mu1 +
          2 * (IndependentSums.gammaMomentConst 2 *
            accumulatedFiniteFieldScaleBound M s) +
          (3 / 2 : ℝ) * (IndependentSums.gammaMomentConst 2 *
            accumulatedGradientOwnRowScale M))
      ≤ ((m + 1 - n : ℕ) : ℝ) *
          (logFreeMeanConst d Cr *
            ((Real.sqrt s)⁻¹ * (s⁻¹) ^ 3 * M.delta)) :=
        mul_le_mul_of_nonneg_left hbracket hW
    _ = ((m + 1 - n : ℕ) : ℝ) *
          (logFreeMeanConst d Cr * s ^ (-7 / 2 : ℝ) * M.delta) := by
        rw [rpow_neg_seven_halves hs]; ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
