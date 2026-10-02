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

/-! This module establishes ahom inputs for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- ahom inputs in the finite stopping construction. -/
theorem ahom_inputs {d : ℕ} (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    (∀ n m : ℕ, n < m →
      SubdiffusiveProcess.CoarseGrainingVocab.ahom model m ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom model n ∧
        SubdiffusiveProcess.CoarseGrainingVocab.ahom model n ≤
          Real.exp (2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P * ((m : ℝ) - n)) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model m) ∧
    (∀ m : ℕ, SubdiffusiveProcess.CoarseGrainingVocab.ahom model m ≤ 1) ∧
    (∀ m : ℕ, Real.exp (-((m : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) ≤
      SubdiffusiveProcess.CoarseGrainingVocab.ahom model m) := by
  refine ⟨?_, SubdiffusiveProcess.CoarseGrainingVocab.ahom_le_one model, ?_⟩
  · intro n m hnm
    have h := (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds (d := d)).2 model m n hnm
    simpa only [Nat.cast_sub hnm.le] using h
  · intro m
    simpa only [neg_add_rev] using (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower model m)

end SubdiffusiveProcess.FiniteStopping
