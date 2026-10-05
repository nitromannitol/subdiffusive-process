module

public import SubdiffusiveProcess.Section6.Defs.Affine

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab

/-- Evaluation of a scalar affine function. -/
def Affine.eval {d : ℕ} (ell : Affine d) (x : Vec d) : ℝ :=
  ell.constant + Homogenization.vecDot ell.slope x

end SubdiffusiveProcess.CoarseGrainingVocab
