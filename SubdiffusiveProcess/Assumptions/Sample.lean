module

public import SubdiffusiveProcess.Frozen.Assumptions.PotentialSample

@[expose] public section

/-!
# Measurable coordinates of the potential sequence
-/

-- REUSE-CANDIDATE: Algsuperdiff/Assumptions/ShellField/SequenceLaw.lean

namespace SubdiffusiveProcess.Frozen.Assumptions

variable {d : ℕ}

theorem measurable_potentialCoordinate (k : ℕ) :
    Measurable (fun ω : PotentialSample d ↦ ω k) :=
  measurable_pi_apply k

end SubdiffusiveProcess.Frozen.Assumptions
