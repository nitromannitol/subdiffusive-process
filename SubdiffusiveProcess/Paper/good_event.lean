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

end Paper
