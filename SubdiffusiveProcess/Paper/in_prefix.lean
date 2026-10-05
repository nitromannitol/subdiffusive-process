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
public import SubdiffusiveProcess.Paper.score_family_interface

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- remark `mfd:in-prefix` : the fixed-centre prefix bound.

The score is pinned to the carrier `primitive_scores` : `X` is either the bad score `Z_{m,z}` or the continuous error score `D_{m,z}`, which are the paper's two cases `X = Z` and `X = D`.  The REGIME is part of the bundle, as the paper states it: for a fixed threshold `lam > 0` and every `A < infinity` there is a disorder threshold `disorder0 > 0`, and the exponential prefix bound `P[ sum_{i<k} X_{n+i,z} > lam k / 4 ] <= C e^{-Ak}` is asserted only for `disorder <= disorder0`.  Without that gate the bundle would claim the bound at every disorder, which is false and would make it unsatisfiable.  The disorder parameter is tied to the law and the scores by the moment clause `||X_{n,z}||_{L^2} <= C disorder`, uniformly in `n` and `z`, so `disorder` is the size of the scores under `P` and not a free real.

Uniformity in the position `n` of the interval is stationarity (Assumption a.g1) together with the moment order and the exponents are fixed before the disorder is reduced, so `A` and `Cc` are parameters of the definition, not functions of the score. -/
def in_prefix (Om : Type) [MeasurableSpace Om] (P : Measure Om) (d : ℕ)
    (Fsc Psc Rsc Dsc Zsc : ℕ → (Fin d → ℝ) → Om → ℝ)
    (zeroDis : Om) (eps : ℝ)
    (scoreOf : (ℕ → (Fin d → ℝ) → Om → ℝ) → Prop)
    (X : ℕ → (Fin d → ℝ) → Om → ℝ)
    (lam A Cc disorder disorder0 : ℝ) : Prop :=
  _root_.SubdiffusiveProcess.Paper.score_family_interface Om d Fsc Psc Rsc Dsc Zsc zeroDis eps scoreOf ∧
    (X = Zsc ∨ X = Dsc) ∧
    0 < lam ∧ 0 < A ∧ 0 < Cc ∧ 0 < disorder0 ∧
    (∀ (n : ℕ) (z : Fin d → ℝ),
      eLpNorm (X n z) 2 P ≤ ENNReal.ofReal (Cc * disorder)) ∧
    (0 < disorder → disorder ≤ disorder0 →
      ∀ (n : ℕ) (z : Fin d → ℝ) (k : ℕ), 1 ≤ k →
        P {ω | lam * (k : ℝ) / 4 < ∑ i ∈ Finset.range k, X (n + i) z ω} ≤
          ENNReal.ofReal (Cc * Real.exp (-(A * (k : ℝ)))))

end SubdiffusiveProcess.Paper
