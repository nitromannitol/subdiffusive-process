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

/-- lemma `mfd:lem-block-projections` (paper lines 1550-1569): on a product of three probability spaces the two one-block projections commute to the middle-block projection, and the middle-block error is at most the sum of the two.  Closed by `condExp_leftMiddle_condExp_middleRight`, `condExp_middleRight_condExp_leftMiddle` (`Probability/ProductConditionalExpectation.lean`) and `product_condExp_error_eLpNorm_le` (`Probability/ProductLpContraction.lean`). -/
theorem lem_block_projections
    {A Bm Cm : Type} [MeasurableSpace A] [MeasurableSpace Bm] [MeasurableSpace Cm]
    (mu : Measure A) (nu : Measure Bm) (tau : Measure Cm)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure tau]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (Y : (A × Bm) × Cm → ℝ) (hY : Integrable Y ((mu.prod nu).prod tau)) :
    (((mu.prod nu).prod tau)[((mu.prod nu).prod tau)[Y | middleRightSigma] |
          leftMiddleSigma] =ᵐ[(mu.prod nu).prod tau]
        ((mu.prod nu).prod tau)[Y | middleSigma]) ∧
      (((mu.prod nu).prod tau)[((mu.prod nu).prod tau)[Y | leftMiddleSigma] |
          middleRightSigma] =ᵐ[(mu.prod nu).prod tau]
        ((mu.prod nu).prod tau)[Y | middleSigma]) ∧
      eLpNorm (Y - ((mu.prod nu).prod tau)[Y | middleSigma]) p
            ((mu.prod nu).prod tau) ≤
          eLpNorm (Y - ((mu.prod nu).prod tau)[Y | leftMiddleSigma]) p
            ((mu.prod nu).prod tau) +
          eLpNorm (Y - ((mu.prod nu).prod tau)[Y | middleRightSigma]) p
            ((mu.prod nu).prod tau) :=
  ⟨condExp_leftMiddle_condExp_middleRight hY,
    condExp_middleRight_condExp_leftMiddle hY,
    product_condExp_error_eLpNorm_le hp hp_top hY⟩

end Paper
