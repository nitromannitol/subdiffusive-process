module

public import SubdiffusiveProcess.Section10.StrictDecayProvider
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Main.DiffusionPath
public import MarkovProcess.Path.ExitTime

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Paper

theorem lim_strict_decay {d : ℕ} (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ delta0 →
      ∃ C eta c : ℝ, 0 < C ∧ 0 < eta ∧ 0 < c ∧
        (d = 2 → eta = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P / Real.log 3) ∧
        (∀ l m : ℕ, l ≤ m →
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M m / SubdiffusiveProcess.CoarseGrainingVocab.ahom M l ≤
            C * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (l : ℝ))))) ∧
        (∀ r R : ℝ, 1 ≤ r → r ≤ R →
          c * (R / r) ^ (2 + eta) ≤
            SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) R /
              SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) r) ∧
        ∀ (L : ℕ) (r R : ℝ), 1 ≤ r → r ≤ R → R ≤ (3 : ℝ) ^ L →
          c * (R / r) ^ (2 + eta) ≤
            SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScaleCutoff
                (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) L R /
              SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScaleCutoff
                (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) L r := by
  exact SubdiffusiveProcess.Section10.strict_decay hd

end Paper
