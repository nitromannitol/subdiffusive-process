module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure.DualClosure
public import SubdiffusiveProcess.Providers.Section5.OneStepConcretePrimalClosure
public import SubdiffusiveProcess.Providers.Section5.SharpAsymptoticCore

@[expose] public section




open MeasureTheory Homogenization Homogenization.Book

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Providers.Section5

noncomputable section

/-- The high-dimensional `DualCellMajorantInputs`, stated without an ambient
`NeZero d` instance. -/
def DualCellMajorantInputsOfNeZero (d : ℕ) : Prop :=
  ∀ hd : 3 ≤ d, @DualCellMajorantInputs d ⟨by omega⟩

/-- **The sharp asymptotic from the dual cell majorants.**  The
conclusion is byte-identical to `SubdiffusiveProcess.Section5.sharp_asymptotic`. -/
theorem sharp_asymptotic_of_concrete {d : ℕ}
    (hdual : DualCellMajorantInputsOfNeZero d) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        M.delta ≤ delta0 → ∀ m : ℕ,
          |Real.log (ahom M m) +
              2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
            C * M.delta ^ 2 * |Real.log M.delta| *
              (1 + (m : ℝ) * M.delta) := by
  refine sharp_asymptotic_of_high_dimensional_one_step_bounds ?_ ?_
  · intro hd
    have : NeZero d := ⟨by omega⟩
    exact sharpOneStepUpperConclusion_of_concrete hd
  · intro hd
    have hne : NeZero d := ⟨by omega⟩
    exact sharpOneStepLowerConclusion_of_dualCellMajorants hd (hdual hd)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure
