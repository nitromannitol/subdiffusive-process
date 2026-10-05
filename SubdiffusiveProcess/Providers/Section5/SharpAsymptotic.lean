module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.Assembly

@[expose] public section

/-!
# The sharp diffusivity asymptotic

`sharp_asymptotic` supplies the scalar source-facing estimate by applying
`Section5DualCompetitor.sharp_asymptotic_final`. The separate
`SharpAsymptoticCore` module holds the block arithmetic used by the primal
and dual-cell constructions, avoiding an import cycle.
-/

namespace SubdiffusiveProcess.Providers.Section5

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

theorem sharp_asymptotic {d : ℕ} :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        M.delta ≤ delta0 → ∀ m : ℕ,
          |Real.log (ahom M m) +
              2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
            C * M.delta ^ 2 * |Real.log M.delta| *
              (1 + (m : ℝ) * M.delta) :=
  Section5DualCompetitor.sharp_asymptotic_final

end

end SubdiffusiveProcess.Providers.Section5
