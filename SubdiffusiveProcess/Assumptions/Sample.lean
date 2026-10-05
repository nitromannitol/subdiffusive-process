module

public import SubdiffusiveProcess.Model.PotentialSample

@[expose] public section

/-!
# Measurable coordinates of the potential sequence
-/



namespace SubdiffusiveProcess.Model

variable {d : ℕ}

theorem measurable_potentialCoordinate (k : ℕ) :
    Measurable (fun ω : PotentialSample d ↦ ω k) :=
  measurable_pi_apply k

end SubdiffusiveProcess.Model
