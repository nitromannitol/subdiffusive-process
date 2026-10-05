module

public import SubdiffusiveProcess.Assumptions.PotentialField

@[expose] public section

/-!
# Sequences of scalar potential layers
-/

/-- The one-sided sequence of scalar potential layers. -/

abbrev SubdiffusiveProcess.Model.PotentialSample (d : ℕ) :=
  ℕ → _root_.SubdiffusiveProcess.Model.PotentialField d

