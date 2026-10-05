module

public import SubdiffusiveProcess.Section6.Defs.H2Datum

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open scoped BigOperators ENNReal

noncomputable section

/-- The coordinate-sum `H²` norm on a weak-Hessian datum. -/
def SubdiffusiveProcess.CoarseGrainingVocab.H2Datum.norm {d : ℕ} {Q : TriadicCube d}
    (h : H2Datum Q) : ℝ≥0∞ :=
  l2Size Q h.toH1.toFun +
    (∑ i : Fin d, l2Size Q (fun x ↦ h.toH1.grad x i)) +
      ∑ i : Fin d, ∑ j : Fin d, l2Size Q (h.weakHessian.hess i j)

end
