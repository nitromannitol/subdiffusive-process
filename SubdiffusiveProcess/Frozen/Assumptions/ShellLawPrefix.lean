import SubdiffusiveProcess.Assumptions.Actions
import SubdiffusiveProcess.Frozen.Assumptions.ZeroPotentialLaw
import Mathlib.Probability.Independence.Basic

/-!
# Common assumptions on the potential layers
-/

open Homogenization MeasureTheory ProbabilityTheory




structure SubdiffusiveProcess.Frozen.Assumptions.ShellLawPrefix (d : ℕ) (delta : ℝ)
    (P : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) : Prop where
  dimension : 2 ≤ d
  delta_pos : 0 < delta
  delta_le_half : delta ≤ (1 : ℝ) / 2
  independent :
    iIndepFun (fun k : ℕ ↦ fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d ↦ ω k)
      P.toMeasure
  marginal_scaling : ∀ k : ℕ,
    SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw P k =
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw P).map
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k).aemeasurable

