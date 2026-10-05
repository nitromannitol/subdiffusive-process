module

public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Model.ZeroPotentialLaw

@[expose] public section

/-!
# Assumption (g3)
-/

open Homogenization MeasureTheory ProbabilityTheory

/-- Signed-coordinate-permutation and sign symmetry of the zero-layer law,
assumption (g3), `a.g3`. -/

structure SubdiffusiveProcess.Model.ShellLawG3 (d : ℕ)
    (P : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d)) : Prop where
  signed_coordinate_permutations : ∀ (R : Mat d)
      (hR : IsSignedPermutationMatrix R),
    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw P).map
        (_root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR) =
      _root_.SubdiffusiveProcess.Model.zeroPotentialLaw P
  negation :
    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw P).map
        _root_.SubdiffusiveProcess.Model.PotentialField.negate =
      _root_.SubdiffusiveProcess.Model.zeroPotentialLaw P

