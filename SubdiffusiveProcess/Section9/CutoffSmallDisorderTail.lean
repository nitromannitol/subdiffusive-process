

module

public import SubdiffusiveProcess.Section9.CutoffOneCubeTail
public import SubdiffusiveProcess.Section9.SmallDisorderExponent

@[expose] public section

/-!
# Uniform small-disorder one-cube tails

This module combines the exact numerical exponent choice with the centered
cutoff-cube moment consumer. It is ordinary support below the weighted-volume
theorem, not a source-facing theorem.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.Section9

open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions

/-- Dimensionally uniform choice of the source exponent for all subsequent
models and cutoff indices. -/
theorem exists_cutoffOriginCube_smallDisorder_tail (d : ℕ) :
    ∃ c δzero : ℝ, 0 < c ∧ 0 < δzero ∧
      ∀ M : GMCModel d, M.delta ≤ δzero → ∀ m : ℕ,
        let p := smallDisorderExponent c M.delta
        2 ≤ p ∧
          SubdiffusiveProcess.OGammaLE M.P.toMeasure 1 p⁻¹
            (fun omega ↦ Real.log (cutoffOriginCubeAverage M m omega) -
              Real.log (9 / 8 : ℝ)) ∧
          M.P.toMeasure.real
              {omega | 1 / 2 ≤ |cutoffOriginCubeAverage M m omega - 1|} ≤
            Real.exp (-p * Real.log 4) := by
  obtain ⟨c, δzero, hc, hδzero, hchoice⟩ :=
    exists_smallDisorderExponent_parameters
      (negativeBesovOneCubeConst d) (negativeBesovOneCubeSmallConst d) (1 / 8)
      (negativeBesovOneCubeConst_pos d) (negativeBesovOneCubeSmallConst_pos d)
      (by norm_num)
  refine ⟨c, δzero, hc, hδzero, ?_⟩
  intro M hM m
  dsimp only
  obtain ⟨-, hp, hsmall, hmoment⟩ := hchoice M.delta M.shellPrefix.delta_pos hM
  refine ⟨hp, ?_⟩
  exact cutoffOriginCube_log_tail_and_failure M m
    (smallDisorderExponent c M.delta) hp hsmall hmoment

end SubdiffusiveProcess.Section9
