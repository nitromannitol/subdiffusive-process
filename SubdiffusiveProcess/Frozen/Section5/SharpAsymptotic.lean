module

public import SubdiffusiveProcess.Providers.Section5.SharpAsymptotic

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab


theorem SubdiffusiveProcess.Frozen.Section5.sharp_asymptotic {d : ℕ} :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        M.delta ≤ delta0 → ∀ m : ℕ,
          |Real.log (ahom M m) +
              2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
            C * M.delta ^ 2 * |Real.log M.delta| *
              (1 + (m : ℝ) * M.delta)

:= SubdiffusiveProcess.Providers.Section5.sharp_asymptotic
