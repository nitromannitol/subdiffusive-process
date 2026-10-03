module

public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Frozen.Assumptions.ZeroPotentialLaw

@[expose] public section

/-!
# Assumption (g3)
-/

open Homogenization MeasureTheory ProbabilityTheory




structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawG3 (d : ℕ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  signed_coordinate_permutations : ∀ (R : Mat d)
      (hR : IsSignedPermutationMatrix R),
    (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).map
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR) =
      SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P
  negation :
    (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).map
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate =
      SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P

