module

public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.ResponseMoments.Forms
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.ResponseMoments.DirichletForm
public import SubdiffusiveProcess.ResponseMoments.ResamplingV2
public import SubdiffusiveProcess.ResponseMoments.UpperDensity
public import SubdiffusiveProcess.ResponseMoments.BandFiltration
public import SubdiffusiveProcess.Probability.LayerProductBlocks
public import SubdiffusiveProcess.Probability.ResponseCompactness
public import SubdiffusiveProcess.Variational.QuadraticSaving
public import SubdiffusiveProcess.Compactness.OperatorLimits
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Quadratic-form saving. The proof uses the theorem `quadratic_form_saving` of `SubdiffusiveProcess/Variational/QuadraticSaving.lean`. -/
theorem lem_saving {V : Type} [AddCommGroup V] [Module ℝ V]
    (Q0 Bq : QuadraticForm ℝ V) (hQ : ∀ v, 0 ≤ Q0 v) (hB : ∀ v, 0 ≤ Bq v)
    (Del a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hdom : ∀ v, Bq v ≤ Del * Q0 v) (b l : V)
    (hsaving : a * Del * Q0 l ≤ Bq l) :
    Del * (a / 2 * Q0 b - 4 * Q0 (b - l)) ≤ Bq b :=
  quadratic_form_saving Q0 Bq hQ hB ha ha1 hdom b l hsaving

end SubdiffusiveProcess.Paper
