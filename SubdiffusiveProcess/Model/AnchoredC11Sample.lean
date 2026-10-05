module

public import SubdiffusiveProcess.Model.AnchoredC11GoodSet

@[expose] public section

/-!
# Sample carrier for the anchored coefficient
-/

/-- Samples carrying the proof that their anchored local `C¹ˑ¹` limit
exists uniquely. -/

abbrev SubdiffusiveProcess.Model.AnchoredC11Sample (d : ℕ) :=
  {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d //
    omega ∈ _root_.SubdiffusiveProcess.Model.anchoredC11GoodSet d}

