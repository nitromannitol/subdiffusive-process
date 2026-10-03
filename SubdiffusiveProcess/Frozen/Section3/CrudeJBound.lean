module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section3Support
public import SubdiffusiveProcess.Providers.Section3.CrudeJBound

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal


theorem SubdiffusiveProcess.Frozen.Section3.crude_j_bound {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (xi : ℝ)
        (U : Ch02.Domain d),
        1 ≤ xi →
        (U : Set (Vec d)) ⊆
          Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ)) →
        paperENNRealLpNorm M.P.toMeasure xi (normalizedDefect M m U) ≤
          ENNReal.ofReal
            (C * xi * (m + 1 : ℝ) * M.delta ^ 2 *
              Real.exp (C * xi * (m + 1 : ℝ) * M.delta ^ 2))

:= SubdiffusiveProcess.Providers.Section3.crude_j_bound
