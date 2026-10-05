module

public import SubdiffusiveProcess.Model.AnchoredLog
public import SubdiffusiveProcess.Model.GMCModel

@[expose] public section

/-!
# The anchored coefficient
-/

open Homogenization

/-- The normalized coefficient on the canonical anchored-convergence event. -/

noncomputable def SubdiffusiveProcess.Model.aAnchored {d : ℕ}
    (_M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d)
    (x : Vec d) : ℝ :=
  Real.exp (_root_.SubdiffusiveProcess.Model.anchoredLog omega x)

