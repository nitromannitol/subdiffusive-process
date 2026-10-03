module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section3Support
public import SubdiffusiveProcess.Providers.Section3.InfraredApproxCutoffs

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal


theorem SubdiffusiveProcess.Frozen.Section3.infrared_approx_cutoffs {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (k : ℤ)
        (xi : ℝ) (U : Ch02.Domain d),
        1 ≤ xi →
        (U : Set (Vec d)) ⊆
          Homogenization.openCubeSet (Homogenization.originCube d k) →
        paperENNRealLpNorm M.P.toMeasure xi
              (cutoffSensitivityForwardSup M n U) +
            paperENNRealLpNorm M.P.toMeasure xi
              (cutoffSensitivityReverseSup M n U) ≤
          ENNReal.ofReal
            (C * Real.sqrt xi * M.delta * Real.rpow 3 ((k : ℝ) - n) *
              Real.exp (C * xi * M.delta ^ 2 *
                Real.rpow 3 (2 * ((k : ℝ) - n)))) ∧
        ∀ m : ℕ, n < m →
          paperLpNorm M.P.toMeasure xi
              (paperTwoTermLpObservable xi
                (fun ω => normalizedMatrixDeviation
                  (randomAStarMatrix M m U ω) (randomAStarMatrix M n U ω) 1)
                (fun ω => normalizedMatrixDeviation
                  (randomAMatrix M m U ω) (randomAMatrix M n U ω) 1)) +
            paperLpNorm M.P.toMeasure xi
              (paperTwoTermLpObservable xi
                (fun ω => normalizedMatrixDeviation
                  (randomAStarMatrix M n U ω) (randomAStarMatrix M m U ω) 1)
                (fun ω => normalizedMatrixDeviation
                  (randomAMatrix M n U ω) (randomAMatrix M m U ω) 1)) ≤
            ENNReal.ofReal (C * Real.sqrt xi * M.delta *
                (Real.sqrt ((m - n : ℕ) : ℝ) + max ((k : ℝ) - n) 0) *
              Real.exp (C * xi * M.delta ^ 2 *
                (((m - n : ℕ) : ℝ) + (max ((k : ℝ) - n) 0) ^ 2)))

:= SubdiffusiveProcess.Providers.Section3.infrared_approx_cutoffs
