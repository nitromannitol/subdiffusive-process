module

public import SubdiffusiveProcess.Section10.ClassicalBrownianLinearImage
public import SubdiffusiveProcess.Processes.FiniteEvaluationMeasureDetermination
public import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch

@[expose] public section

open MeasureTheory MarkovProcess
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- A literal FDD-to-path-law interface on the finite coordinate carrier.
The characteristic-function equality is the consumer's algebraic obligation. -/
theorem finiteRealPath_measure_eq_of_fdd_charFunDual
    {d : ℕ} (Q R : Measure (FiniteRealPath d))
    [IsFiniteMeasure Q] [IsFiniteMeasure R]
    (h : ∀ I : Finset ℝ≥0,
      charFunDual (Q.map (ContinuousPath.finiteEvaluation (fun t : I => (t : ℝ≥0)))) =
        charFunDual (R.map (ContinuousPath.finiteEvaluation (fun t : I => (t : ℝ≥0))))) :
    Q = R := by
  apply SubdiffusiveProcess.path_measure_eq_of_finiteEvaluation_map_eq
  intro I
  exact Measure.ext_of_charFunDual (h I)

end SubdiffusiveProcess.Section10
