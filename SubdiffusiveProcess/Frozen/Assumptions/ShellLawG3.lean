import SubdiffusiveProcess.Assumptions.Actions
import SubdiffusiveProcess.Frozen.Assumptions.ZeroPotentialLaw

/-!
# Assumption (g3)
-/

open Homogenization MeasureTheory ProbabilityTheory




structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawG3 (d : ℕ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  signed_coordinate_permutations : ∀ (R : Mat d)
      (hR : IsSignedPermutationMatrix R),
    (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).map
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_rotate R hR).aemeasurable =
      SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P
  negation :
    (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).map
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_negate.aemeasurable =
      SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P

