module

public import SubdiffusiveProcess.Providers.Section5.RenormalizedDiffusivities

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab


theorem SubdiffusiveProcess.Frozen.Section5.renormalized_diffusivities {d : ℕ} :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        ∃ eta : ℝ, 0 < eta ∧
          (∀ n m : ℕ, n ≤ m →
            Real.exp (-(m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤
                ahom M m ∧
            ahom M m ≤ ahom M n ∧
            ahom M n ≤ min 1
              (Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P *
                ((m - n : ℕ) : ℝ)) * ahom M m) ∧
            ahom M m ≤ Real.rpow 3 (-eta * (m + 1 : ℝ))) ∧
          (d = 2 → ∀ m : ℕ,
            ahom M m =
              Real.exp (-(m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) ∧
          (M.delta ≤ delta0 → ∀ m : ℕ,
            |Real.log (ahom M m) +
                2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (m + 1 : ℝ) / d| ≤
              C * M.delta ^ 2 * |Real.log M.delta| *
                (1 + (m : ℝ) * M.delta))

:= SubdiffusiveProcess.Providers.Section5.renormalized_diffusivities
