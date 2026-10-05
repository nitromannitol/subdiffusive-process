module

public import SubdiffusiveProcess.Section4.HomogenizationStep

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Proposition `p.homogenization.step`.

Correspondence with the live paper statement:
* `E[max_{|e|=1} J(cu_m, ahom_L^{-1/2} e, ahom_L^{1/2} e; a_L)^ξ]^{1/ξ}` is
  `paperENNRealLpNorm ℙ ξ (normalizedDefectAt M L m)` (sphere maximum on the origin cube of scale `m`
  for the cutoff `L`).
* `m0 ∈ ℕ` is `0 < m0`; `m ∈ ℕ` is `0 < m`; `L ∈ ℕ_0`, `L ≤ m0`; `m ≥ L + C log(2+ξ)` is
  `(L:ℝ) + C * Real.log (2 + ξ) ≤ m`. -/
theorem p_homogenization_step {d : ℕ} :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m0 : ℕ) (ξ δ1 : ℝ),
        0 < m0 → 16 * (d : ℝ) ≤ ξ →
        C * ξ * M.delta ^ 2 ≤ δ1 → δ1 ≤ c →
        inductionHypothesis M m0 ξ δ1 →
        ∀ (m L : ℕ), 0 < m → L ≤ m0 →
          (L : ℝ) + C * Real.log (2 + ξ) ≤ m →
          paperENNRealLpNorm M.P.toMeasure ξ (normalizedDefectAt M L m) ≤
            ENNReal.ofReal ((1 / 4 : ℝ) * δ1)
    := _root_.SubdiffusiveProcess.Section4.homogenization_step

end SubdiffusiveProcess.Paper
