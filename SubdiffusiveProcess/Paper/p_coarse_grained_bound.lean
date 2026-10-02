import SubdiffusiveProcess.Frozen.Section4.CoarseGrainedBound

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem p_coarse_grained_bound {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (ξ : ℝ),
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
    := SubdiffusiveProcess.Frozen.Section4.coarse_grained_bound

end Paper
