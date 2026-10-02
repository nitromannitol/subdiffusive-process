import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.Assembly

/-!
# Provider for the sharp diffusivity asymptotic

The source-facing export is added here once the concrete dual-cell carrier
has landed. Keeping the deterministic assembly in `SharpAsymptoticCore`
breaks the import cycle with the ordinary dual-closure infrastructure.
-/

namespace SubdiffusiveProcess.Providers.Section5

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

theorem sharp_asymptotic {d : ℕ} :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        M.delta ≤ delta0 → ∀ m : ℕ,
          |Real.log (ahom M m) +
              2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (m + 1 : ℝ) / d| ≤
            C * M.delta ^ 2 * |Real.log M.delta| *
              (1 + (m : ℝ) * M.delta) :=
  Section5DualCompetitor.sharp_asymptotic_final

end

end SubdiffusiveProcess.Providers.Section5
