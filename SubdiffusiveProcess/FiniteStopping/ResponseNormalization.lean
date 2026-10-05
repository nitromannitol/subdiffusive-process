module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Main.LayerScaling
public import Mathlib.Tactic

@[expose] public section

/-! This module establishes ahom inputs for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- ahom inputs in the finite stopping construction. -/
theorem ahom_inputs {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    (∀ n m : ℕ, n < m →
      SubdiffusiveProcess.CoarseGrainingVocab.ahom model m ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom model n ∧
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model n ≤
          Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq model.P * ((m : ℝ) - n)) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model m) ∧
    (∀ m : ℕ, SubdiffusiveProcess.CoarseGrainingVocab.ahom model m ≤ 1) ∧
    (∀ m : ℕ, Real.exp (-((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) ≤
      SubdiffusiveProcess.CoarseGrainingVocab.ahom model m) := by
  refine ⟨?_, SubdiffusiveProcess.CoarseGrainingVocab.ahom_le_one model, ?_⟩
  · intro n m hnm
    have h := (_root_.SubdiffusiveProcess.Section3.annealed_matrix_bounds (d := d)).2 model m n hnm
    simpa only [Nat.cast_sub hnm.le] using h
  · intro m
    simpa only [neg_add_rev] using (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower model m)

end SubdiffusiveProcess.FiniteStopping
