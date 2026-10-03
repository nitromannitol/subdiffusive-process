module

public import SubdiffusiveProcess.Frozen.Section3.SpecialTwoDExactFormula

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem p_special_two_d_exact_formula
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel 2) (m : ℕ) :
    ahom M m =
      Real.exp (-(m + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) :=
  SubdiffusiveProcess.Frozen.Section3.special_two_d_exact_formula M m

end Paper
