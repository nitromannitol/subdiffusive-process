module

public import SubdiffusiveProcess.Model.ZeroPotentialLaw
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Disorder strength from the layer law

`tauSq P` is the logarithm of the exponential moment of the level-zero
potential at the origin. It is a real-valued total definition: Lean assigns
zero to a nonintegrable real integral and `Real.log 0 = 0`. On a `GMCModel`,
`G4.exponential_integrable` and `G4.tauSq_pos` give its intended positive,
finite-moment interpretation. Off that domain the definition alone is not a
certificate of integrability or positive disorder.
-/

open MeasureTheory ProbabilityTheory

/-- The disorder strength `τ² = log 𝔼[exp(g₀(0))]`,
`a.g4`. -/

noncomputable def SubdiffusiveProcess.Model.tauSq {d : ℕ}
    (P : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d)) : ℝ :=
  Real.log
    (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, Real.exp (g 0)
      ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw P).toMeasure)

