import SubdiffusiveProcess.Providers.Section5.SharpAsymptotic

open SubdiffusiveProcess.CoarseGrainingVocab


theorem SubdiffusiveProcess.Frozen.Section5.sharp_asymptotic {d : ℕ} :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        M.delta ≤ delta0 → ∀ m : ℕ,
          |Real.log (ahom M m) +
              2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (m + 1 : ℝ) / d| ≤
            C * M.delta ^ 2 * |Real.log M.delta| *
              (1 + (m : ℝ) * M.delta)

:= SubdiffusiveProcess.Providers.Section5.sharp_asymptotic
