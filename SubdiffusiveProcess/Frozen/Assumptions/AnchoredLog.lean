module

public import SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample

@[expose] public section

/-!
# The anchored logarithmic potential
-/

/-- The unique anchored local `C¹ˑ¹` limit on the canonical good event. -/

noncomputable def SubdiffusiveProcess.Frozen.Assumptions.anchoredLog {d : ℕ}
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField d :=
  Classical.choose omega.property.exists

