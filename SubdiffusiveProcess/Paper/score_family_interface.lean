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



def score_family_interface (Om : Type) [MeasurableSpace Om] (d : ℕ)
    (Fsc Psc Rsc Dsc Zsc : ℕ → (Fin d → ℝ) → Om → ℝ)
    (zeroDis : Om) (eps : ℝ)
    (scoreOf : (ℕ → (Fin d → ℝ) → Om → ℝ) → Prop) : Prop :=
  0 < eps ∧ eps < 1 ∧
    (∀ (m : ℕ) (z : Fin d → ℝ) (ω : Om), 0 ≤ Fsc m z ω) ∧
    (∀ (m : ℕ) (z : Fin d → ℝ) (ω : Om), 2 ≤ Psc m z ω) ∧
    (∀ (m : ℕ) (z : Fin d → ℝ) (ω : Om), 0 ≤ Rsc m z ω) ∧
    (∀ (m : ℕ) (z : Fin d → ℝ) (ω : Om), 0 ≤ Dsc m z ω) ∧
    (∀ (m : ℕ) (z : Fin d → ℝ),
      Fsc m z zeroDis = 0 ∧ Psc m z zeroDis = 2 ∧
        Rsc m z zeroDis = 0 ∧ Dsc m z zeroDis = 0) ∧
    (∀ (m : ℕ) (z : Fin d → ℝ) (ω : Om),
      Zsc m z ω = ramp (eps / 2) eps (Fsc m z ω) + ramp 6 12 (Psc m z ω) +
        ramp (eps ^ 2 / 4) (eps ^ 2) (Rsc m z ω)) ∧
    (∀ (m : ℕ) (z : Fin d → ℝ) (ω : Om), 0 ≤ Zsc m z ω ∧ Zsc m z ω ≤ 3) ∧
    (∀ X : ℕ → (Fin d → ℝ) → Om → ℝ, scoreOf X ↔
      ∃ w : Fin 4 → ℝ, (∀ i : Fin 4, 0 ≤ w i) ∧
        X = fun (m : ℕ) (z : Fin d → ℝ) (ω : Om) =>
          w 0 * Dsc m z ω + w 1 * ramp (eps / 2) eps (Fsc m z ω) +
            w 2 * ramp 6 12 (Psc m z ω) +
            w 3 * ramp (eps ^ 2 / 4) (eps ^ 2) (Rsc m z ω))

end SubdiffusiveProcess.Paper
