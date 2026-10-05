module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section3Support
public import SubdiffusiveProcess.Providers.Section3.SpecialTwoDExactFormula

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab

theorem SubdiffusiveProcess.Section3.special_two_d_exact_formula
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) :
    ahom M m =
      Real.exp (-(m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
:= SubdiffusiveProcess.Providers.Section3.special_two_d_exact_formula M m
