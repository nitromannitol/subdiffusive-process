module

public import SubdiffusiveProcess.Section3.SpecialTwoDExactFormula

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem p_special_two_d_exact_formula
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) :
    ahom M m =
      Real.exp (-(m + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) :=
  _root_.SubdiffusiveProcess.Section3.special_two_d_exact_formula M m

end SubdiffusiveProcess.Paper
