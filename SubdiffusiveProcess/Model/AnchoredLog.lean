module

public import SubdiffusiveProcess.Model.AnchoredC11Sample

@[expose] public section

/-!
# The anchored logarithmic potential
-/

/-- The unique anchored local `C¹ˑ¹` limit on the canonical good event. -/
noncomputable def SubdiffusiveProcess.Model.anchoredLog {d : ℕ}
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) :
    _root_.SubdiffusiveProcess.Model.PotentialField d :=
  Classical.choose omega.property.exists
