import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Lane3.Forms
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Lane3.DirichletForm
import SubdiffusiveProcess.Lane3.ResamplingV2
import SubdiffusiveProcess.Lane3.UpperDensity
import SubdiffusiveProcess.Lane3.BandFiltration
import SubdiffusiveProcess.Probability.LayerProductBlocks
import SubdiffusiveProcess.Probability.ResponseCompactness
import SubdiffusiveProcess.Variational.QuadraticSaving
import SubdiffusiveProcess.Compactness.OperatorLimits
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lem_saving {V : Type} [AddCommGroup V] [Module ℝ V]
    (Q0 Bq : QuadraticForm ℝ V) (hQ : ∀ v, 0 ≤ Q0 v) (hB : ∀ v, 0 ≤ Bq v)
    (Del a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hdom : ∀ v, Bq v ≤ Del * Q0 v) (b l : V)
    (hsaving : a * Del * Q0 l ≤ Bq l) :
    Del * (a / 2 * Q0 b - 4 * Q0 (b - l)) ≤ Bq b :=
  quadratic_form_saving Q0 Bq hQ hB ha ha1 hdom b l hsaving

end Paper
