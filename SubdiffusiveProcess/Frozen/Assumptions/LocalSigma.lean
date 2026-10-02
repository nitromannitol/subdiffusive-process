import SubdiffusiveProcess.Assumptions.PotentialField

/-!
# Local sigma-fields for scalar potentials
-/

open Homogenization




def SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma {d : ℕ}
    (U : Set (Vec d)) :
    MeasurableSpace (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
  MeasurableSpace.comap
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.forgetPotential
    (LocalSigmaR U)

