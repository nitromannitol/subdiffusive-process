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



theorem lem_compact_responses {X ι : Type} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    (nu : Measure X) [IsProbabilityMeasure nu] (f : ι → X → ℝ)
    (Cc : ℝ) (hC : 0 ≤ Cc)
    (hn : ∀ i x, x ∈ nu.support → 0 ≤ f i x)
    (hcmp : ∀ i x, x ∈ nu.support → ∀ y, y ∈ nu.support →
      f i x ≤ Real.exp (Cc * dist x y) * f i y)
    (p q : ℝ≥0∞) [hp : Fact (1 ≤ p)] (hpq : p < q) (hq : q ≠ ∞)
    (K : ℝ≥0∞) (hK : K ≠ ∞) (hf : ∀ i, MemLp (f i) q nu)
    (hb : ∀ i, eLpNorm (f i) q nu ≤ K) :
    IsCompact (closure (Set.range (fun i => ((hf i).mono_exponent hpq.le).toLp (f i)))) :=
  law_responses_isCompact_closure nu hC hn hcmp hpq hq hK hf hb

end SubdiffusiveProcess.Paper
