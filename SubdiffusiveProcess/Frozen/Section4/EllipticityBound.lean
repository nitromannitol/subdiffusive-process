module

public import SubdiffusiveProcess.Providers.Section4.EllipticityBound

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal


theorem SubdiffusiveProcess.Frozen.Section4.ellipticity_bound {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (m0 : ℕ) (ξ delta1 : ℝ),
        6 ≤ ξ → M.delta ^ 2 ≤ delta1 → delta1 < 1 →
        inductionHypothesis M m0 ξ delta1 →
        ∀ s : ℝ, 0 < s → s ≤ 1 →
          4 * (d : ℝ) * s⁻¹ ≤ ξ →
          ξ ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
          (∀ (m : ℕ) (n : ℤ), n ≤ (m0 : ℤ) → n ≤ (m : ℤ) →
            paperENNRealLpNorm M.P.toMeasure ξ
                (ellipticityMomentObservable M m n s) ≤
              ENNReal.ofReal
                (C * s⁻¹ * Real.sqrt delta1 *
                  Real.rpow 3
                    (((d : ℝ) / ξ + s / 2) * (((m : ℤ) - n : ℤ) : ℝ)))) ∧
          (∀ L : ℕ, L ≤ m0 →
            paperENNRealLpNorm M.P.toMeasure ξ
                (homogenizationErrorRandom M L L s) ≤
              ENNReal.ofReal (C * s⁻¹ * Real.sqrt delta1))

:= SubdiffusiveProcess.Providers.Section4.ellipticity_bound
