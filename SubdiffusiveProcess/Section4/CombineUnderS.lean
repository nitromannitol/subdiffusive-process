module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support
public import SubdiffusiveProcess.Providers.Section4.CombineUnderS

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

theorem SubdiffusiveProcess.Section4.combine_under_s {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (ξ δ1 : ℝ),
        16 * (d : ℝ) ≤ ξ →
        C * ξ * M.delta ^ 2 ≤ δ1 → δ1 ≤ c →
        inductionHypothesis M L ξ δ1 →
        ∀ m : ℕ, 0 < m → L ≤ m →
          C * Real.rpow 3 (-((m - L : ℕ) : ℝ)) ≤ (1 / 4 : ℝ) →
          ∀ p q : Vec d,
            q = ahom M L • p → Homogenization.vecNormSq q ≤ ahom M L →
            expectedJ M L m p q ≤
              C * δ1 * (δ1 + Real.rpow 3 (-((m - L : ℕ) : ℝ))) +
                C * ∑ n ∈ Finset.Icc L m,
                  Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
                    expectedJDifference M L n m p q
:= SubdiffusiveProcess.Providers.Section4.combine_under_s
