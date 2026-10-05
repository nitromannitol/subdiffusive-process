module

public import SubdiffusiveProcess.Frozen.Section5.SharpAsymptotic

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Proposition `p.sharp.asymptotic`.

Correspondence with the live paper statement: `δ0(d) > 0`, `C(d) < ∞` are fixed before the model `M`;
for `M.delta ≤ δ0` and every `m ∈ ℕ_0`,
`|log ahom_m + 2 τ² (m+1)/d| ≤ C δ² |log δ| (1 + m δ)`. -/
theorem p_sharp_asymptotic {d : ℕ} :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        M.delta ≤ delta0 → ∀ m : ℕ,
          |Real.log (ahom M m) +
              2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
            C * M.delta ^ 2 * |Real.log M.delta| *
              (1 + (m : ℝ) * M.delta)
    := SubdiffusiveProcess.Frozen.Section5.sharp_asymptotic

end SubdiffusiveProcess.Paper
