module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support
public import SubdiffusiveProcess.Providers.Section4.CoarseGrainedBound

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal


theorem SubdiffusiveProcess.Section4.coarse_grained_bound {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (ξ : ℝ),
        1 ≤ ξ →
        ξ ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
        ∀ m : ℕ,
          paperENNRealLpNorm M.P.toMeasure ξ
              (normalizedDefect M m
                (Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))) ≤
            ENNReal.ofReal (C * ξ * Real.log (2 + ξ) * M.delta ^ 2) ∧
          ∀ s : ℝ, 0 < s → s ≤ 1 →
            4 * (d : ℝ) * s⁻¹ ≤ ξ →
            C * ξ * Real.log (2 + ξ) * M.delta ^ 2 ≤ c * s →
            c ≤ s * Real.log (2 + ξ) →
            paperENNRealLpNorm M.P.toMeasure ξ
                (homogenizationErrorRandom M m m s) ≤
              ENNReal.ofReal
                (C * s⁻¹ * Real.sqrt (ξ * Real.log (2 + ξ) * M.delta ^ 2))

:= SubdiffusiveProcess.Providers.Section4.coarse_grained_bound
    _root_.SubdiffusiveProcess.Section4.combine_under_s
    _root_.SubdiffusiveProcess.Section4.homogenization_step
