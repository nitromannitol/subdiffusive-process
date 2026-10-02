import SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11GoodSet

/-!
# Sample carrier for the anchored coefficient
-/

/-- Samples carrying the proof that their anchored local `C¹ˑ¹` limit
exists uniquely. -/

abbrev SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample (d : ℕ) :=
  {omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d //
    omega ∈ SubdiffusiveProcess.Frozen.Assumptions.anchoredC11GoodSet d}

