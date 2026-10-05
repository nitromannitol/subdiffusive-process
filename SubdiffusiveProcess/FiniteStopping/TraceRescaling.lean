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

/-! This module establishes IsCellBoundaryClass rescale for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- rescaledDatum unit in the finite stopping construction. -/
theorem rescaledDatum_unit {d : ℕ} (g : SpatialCoordinates d → ℝ) :
    rescaledDatum (0 : SpatialCoordinates d) 1 g = g := by
  funext y
  unfold rescaledDatum
  congr 1
  funext i
  simp only [Pi.zero_apply, one_mul, zero_add]

/-- cellBoundaryQuotientNorm rescale in the finite stopping construction. -/
theorem cellBoundaryQuotientNorm_rescale {d : ℕ} (beta : ℝ) (z : SpatialCoordinates d)
    (r : ℝ) (g : SpatialCoordinates d → ℝ) :
    cellBoundaryQuotientNorm beta z r g =
      cellBoundaryQuotientNorm beta 0 1 (rescaledDatum z r g) := by
  unfold cellBoundaryQuotientNorm
  rw [SubdiffusiveProcess.FiniteStopping.rescaledDatum_unit]

/-- IsCellBoundaryClass rescale in the finite stopping construction. -/
theorem IsCellBoundaryClass_rescale {d : ℕ} (beta : ℝ) (z : SpatialCoordinates d)
    (r : ℝ) (g : SpatialCoordinates d → ℝ) :
    IsCellBoundaryClass beta z r g ↔ IsCellBoundaryClass beta 0 1 (rescaledDatum z r g) := by
  unfold IsCellBoundaryClass
  rw [SubdiffusiveProcess.FiniteStopping.rescaledDatum_unit]

end SubdiffusiveProcess.FiniteStopping
