module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support
public import SubdiffusiveProcess.Providers.Section4.HomogenizationStep

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal


theorem SubdiffusiveProcess.Frozen.Section4.homogenization_step {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m0 : ℕ) (ξ δ1 : ℝ),
        0 < m0 → 16 * (d : ℝ) ≤ ξ →
        C * ξ * M.delta ^ 2 ≤ δ1 → δ1 ≤ c →
        inductionHypothesis M m0 ξ δ1 →
        ∀ (m L : ℕ), 0 < m → L ≤ m0 →
          (L : ℝ) + C * Real.log (2 + ξ) ≤ m →
          paperENNRealLpNorm M.P.toMeasure ξ (normalizedDefectAt M L m) ≤
            ENNReal.ofReal ((1 / 4 : ℝ) * δ1)

:= SubdiffusiveProcess.Providers.Section4.homogenization_step
