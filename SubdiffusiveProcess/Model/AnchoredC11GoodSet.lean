module

public import SubdiffusiveProcess.Model.IsAnchoredC11Limit

@[expose] public section

/-!
# Canonical anchored-convergence event
-/

/-- The event on which the anchored logarithmic sums have a unique local
`C¹ˑ¹` limit. -/
def SubdiffusiveProcess.Model.anchoredC11GoodSet (d : ℕ) :
    Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
  {omega | ∃! g : _root_.SubdiffusiveProcess.Model.PotentialField d,
    _root_.SubdiffusiveProcess.Model.IsAnchoredC11Limit omega g}
