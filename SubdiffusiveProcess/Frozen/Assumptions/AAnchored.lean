module

public import SubdiffusiveProcess.Frozen.Assumptions.AnchoredLog
public import SubdiffusiveProcess.Frozen.Assumptions.GMCModel

@[expose] public section

/-!
# The anchored coefficient
-/

open Homogenization

/-- The normalized coefficient on the canonical anchored-convergence event. -/

noncomputable def SubdiffusiveProcess.Frozen.Assumptions.aAnchored {d : ℕ}
    (_M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    (x : Vec d) : ℝ :=
  Real.exp (SubdiffusiveProcess.Frozen.Assumptions.anchoredLog omega x)

