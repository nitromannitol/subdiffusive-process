module

public import SubdiffusiveProcess.Frozen.Assumptions.IsAnchoredC11Limit

@[expose] public section

/-!
# Canonical anchored-convergence event
-/

/-- The event on which the anchored logarithmic sums have a unique local
`C¹ˑ¹` limit. -/

def SubdiffusiveProcess.Frozen.Assumptions.anchoredC11GoodSet (d : ℕ) :
    Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :=
  {omega | ∃! g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
    SubdiffusiveProcess.Frozen.Assumptions.IsAnchoredC11Limit omega g}

