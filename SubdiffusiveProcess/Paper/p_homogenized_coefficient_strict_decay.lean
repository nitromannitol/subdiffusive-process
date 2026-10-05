module

public import SubdiffusiveProcess.Section5.HomogenizedCoefficientStrictDecay

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Proposition `p.homogenized.coefficient.strict.decay`.

Correspondence with the live paper statement: `η_sub(d, law(g0)) > 0` is `∃ eta` for the given model `M`;
`d = 2 → η = τ²/log 3`, `3 ≤ d → η ≤ τ²/(d log 3)`, and `ahom_m ≤ 3^{-η(m+1)}` for every `m ∈ ℕ_0`. -/
theorem p_homogenized_coefficient_strict_decay {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∃ eta : ℝ, 0 < eta ∧
      (d = 2 →
        eta = _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3) ∧
      (3 ≤ d →
        eta ≤ _root_.SubdiffusiveProcess.Model.tauSq M.P /
          ((d : ℝ) * Real.log 3)) ∧
      ∀ m : ℕ, ahom M m ≤ Real.rpow 3 (-eta * (m + 1 : ℝ))
    := _root_.SubdiffusiveProcess.Section5.homogenized_coefficient_strict_decay M

end SubdiffusiveProcess.Paper
