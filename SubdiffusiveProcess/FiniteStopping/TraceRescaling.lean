import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Geometry.OddGrid
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Lane4.Inputs
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
import SubdiffusiveProcess.Assumptions.Actions
import SubdiffusiveProcess.Main.LayerScaling
import Mathlib.Tactic

/-! This module establishes IsCellBoundaryClass rescale for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
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
