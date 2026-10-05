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



def good_event (Om : Type) (d : ℕ) (Roots Enl Cmp : Type)
    [Fintype Enl] [Fintype Cmp]
    (centres : Roots → ℕ → Finset (Fin d → ℝ))
    (pre : Roots → ℕ → (Fin d → ℝ) → Finset ℤ)
    (Z Dsc : ℤ → (Fin d → ℝ) → Om → ℝ)
    (ellipMin ellipMax : Enl → Om → ℝ)
    (AE : Enl → Om → Matrix (Fin d) (Fin d) ℝ)
    (coarseErr refRatio : Cmp → Om → ℝ) (chosen : Cmp)
    (c0 Cd cell lam lamDet epshom cdet : ℝ) (k0 : ℕ) (ω : Om) : Prop :=
  0 < lam ∧ lam < 1 ∧ 0 < cell ∧ 0 < epshom ∧ 0 < cdet ∧ 0 < c0 ∧
    (∀ (U : Roots) (D : ℕ),
      ((centres U D).card : ℝ) ≤ Cd * (3 : ℝ) ^ ((d : ℝ) * (D : ℝ))) ∧
    (∀ (U : Roots) (D : ℕ), k0 ≤ D → ∀ w ∈ centres U D,
      (∑ j ∈ pre U D w, Z j w ω) < lam * (D : ℝ) ∧
        (∑ j ∈ pre U D w, Dsc j w ω) < lam * (D : ℝ)) ∧
    lam < lamDet ∧
    (∀ e : Enl, cell ≤ ellipMin e ω ∧ ellipMax e ω ≤ cell⁻¹) ∧
    (∀ (e : Enl) (x : Fin d → ℝ),
      c0 * Matrix.trace (AE e ω) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (AE e ω).mulVec x) ∧
    coarseErr chosen ω ≤ epshom * cdet ∧
    (∀ cq : Cmp, refRatio cq ω ∈ Set.Icc (1 / 2 : ℝ) 2)

end SubdiffusiveProcess.Paper
