module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support
public import SubdiffusiveProcess.Providers.Section5.HomogenizedCoefficientStrictDecay

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab


theorem SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_strict_decay {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∃ eta : ℝ, 0 < eta ∧
      (d = 2 →
        eta = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P / Real.log 3) ∧
      (3 ≤ d →
        eta ≤ SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P /
          ((d : ℝ) * Real.log 3)) ∧
      ∀ m : ℕ, ahom M m ≤ Real.rpow 3 (-eta * (m + 1 : ℝ))

:= SubdiffusiveProcess.Providers.Section5.homogenized_coefficient_strict_decay M
