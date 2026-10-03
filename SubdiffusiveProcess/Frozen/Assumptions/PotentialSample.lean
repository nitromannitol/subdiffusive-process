module

public import SubdiffusiveProcess.Assumptions.PotentialField

@[expose] public section

/-!
# Sequences of scalar potential layers
-/




abbrev SubdiffusiveProcess.Frozen.Assumptions.PotentialSample (d : ℕ) :=
  ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d

