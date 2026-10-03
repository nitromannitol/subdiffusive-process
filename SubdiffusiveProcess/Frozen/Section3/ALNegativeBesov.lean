module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section3Support
public import SubdiffusiveProcess.Providers.Section3.ALNegativeBesov

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal


theorem SubdiffusiveProcess.Frozen.Section3.a_l_negative_besov {d : ℕ} :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s p : ℝ),
        0 < s → s ≤ 1 → 2 ≤ p →
        C * p * M.delta ^ 2 ≤ s →
        p * M.delta ^ 2 * Real.log (2 + p) ≤ c →
        ∀ (m : ℕ) (n : ℤ), -1 ≤ n → n < (m : ℤ) →
          ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
              paperENNRealLpNorm M.P.toMeasure p
                (cutoffRatioNegativeBesov M m n s p) ≤
            ENNReal.ofReal (C * s⁻¹ * M.delta * Real.sqrt p * Real.log p) ∧
          ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
              paperENNRealLpNorm M.P.toMeasure p
                (inverseCutoffRatioNegativeBesov M m n s p) ≤
            ENNReal.ofReal (C * s⁻¹ * M.delta * Real.sqrt p * Real.log p)

:= SubdiffusiveProcess.Providers.Section3.a_l_negative_besov
