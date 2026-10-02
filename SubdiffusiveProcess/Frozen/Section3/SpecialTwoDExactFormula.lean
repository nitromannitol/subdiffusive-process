import SubdiffusiveProcess.CoarseGrainingVocab.Section3Support
import SubdiffusiveProcess.Providers.Section3.SpecialTwoDExactFormula

open SubdiffusiveProcess.CoarseGrainingVocab


theorem SubdiffusiveProcess.Frozen.Section3.special_two_d_exact_formula
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel 2) (m : ℕ) :
    ahom M m =
      Real.exp (-(m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)

:= SubdiffusiveProcess.Providers.Section3.special_two_d_exact_formula M m
