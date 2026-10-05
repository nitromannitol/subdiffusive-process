module

public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Model.ZeroPotentialLaw
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
# Common assumptions on the potential layers
-/

open Homogenization MeasureTheory ProbabilityTheory

/-- Dimension and disorder range, mutual independence, and exact marginal
scaling of the layers;  -/
structure SubdiffusiveProcess.Model.ShellLawPrefix (d : ℕ) (delta : ℝ)
    (P : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d)) : Prop where
  dimension : 2 ≤ d
  delta_pos : 0 < delta
  delta_le_half : delta ≤ (1 : ℝ) / 2
  independent :
    iIndepFun (fun k : ℕ ↦ fun ω : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ ω k)
      P.toMeasure
  marginal_scaling : ∀ k : ℕ,
    _root_.SubdiffusiveProcess.Model.potentialMarginalLaw P k =
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw P).map
        (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k)
