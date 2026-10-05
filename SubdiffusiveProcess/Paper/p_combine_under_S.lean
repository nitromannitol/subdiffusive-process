module

public import SubdiffusiveProcess.Section4.CombineUnderS

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Proposition `p.combine.under.S`.

Correspondence with the live paper statement:
* `E[J(cu_m,p,q;a_L)]` is `expectedJ M L m p q`; `E[J(cu_n,p,q;a_L) - J(cu_m,p,q;a_L)]` is
  `expectedJDifference M L n m p q`; the sum is over `n ∈ {L,…,m}` with weight `3^{-(m-n)}`.
* `(e.pq.normed)`: `q = ahom_L • p` and `|q|² ≤ ahom_L` (`vecNormSq q ≤ ahom M L`).
* `S(L, ξ, δ1)` is `inductionHypothesis M L ξ δ1`; `m ∈ ℕ` is `0 < m`; the single constant `C` serves in
  `C ξ δ² ≤ δ1`, `C 3^{-(m-L)} ≤ 1/4` and the conclusion, exactly as in the paper. -/
theorem p_combine_under_S {d : ℕ} :
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
    := _root_.SubdiffusiveProcess.Section4.combine_under_s

end SubdiffusiveProcess.Paper
