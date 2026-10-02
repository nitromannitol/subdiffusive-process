import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support
import SubdiffusiveProcess.Providers.Section4.MultiscaleResponseLargeCubes

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal


theorem SubdiffusiveProcess.Frozen.Section4.multiscale_response_large_cubes {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (L m0 : ℕ) (s delta1 ξ : ℝ),
        0 < s → s ≤ 1 → M.delta ^ 2 ≤ delta1 → delta1 < 1 →
        L ≤ m0 →
        4 * (d : ℝ) * s⁻¹ ≤ ξ →
        ξ ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
        inductionHypothesis M m0 ξ delta1 →
        ∀ K : ℕ, L ≤ K → ∀ z : PaperCubeTranslate d, ∀ r : ℕ,
          (r = 1 ∨ r = 2) →
          paperENNRealLpNorm M.P.toMeasure ξ
              (translatedHomogenizationErrorRandom M L K z s r) ≤
            ENNReal.ofReal
              (C * Real.rpow s (-(1 / (r : ℝ))) * Real.sqrt delta1)

:= SubdiffusiveProcess.Providers.Section4.multiscale_response_large_cubes
