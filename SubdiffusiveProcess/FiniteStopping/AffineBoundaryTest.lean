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

/-! This module establishes trace affine test for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- trace affine test in the finite stopping construction. -/
theorem trace_affine_test {d : ℕ} (hd : 2 ≤ d) :
    ∃ phi : SpatialCoordinates d → ℝ,
      ContDiff ℝ ∞ phi ∧
      ∃ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
        phi x ≠ phi y := by
  let i0 : Fin d := ⟨0, by omega⟩
  let p0 : Fin d → ℝ := Pi.single i0 1
  let phi : SpatialCoordinates d → ℝ := affineSlope p0
  let x : SpatialCoordinates d := Pi.single i0 (1 / 2)
  let y : SpatialCoordinates d := Pi.single i0 (-1 / 2)
  have hxnorm : dist x (0 : SpatialCoordinates d) = 1 / 2 := by
    apply le_antisymm
    · apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)).2
      intro i
      by_cases hi : i = i0
      · subst i
        simp only [one_div, Pi.single_eq_same, Pi.zero_apply, dist_zero_right, norm_inv, Real.norm_ofNat, le_refl, x]
      · simp only [one_div, ne_eq, hi, not_false_eq_true, Pi.single_eq_of_ne, Pi.zero_apply, dist_self, inv_nonneg, Nat.ofNat_nonneg, x]
    · have h := norm_le_pi_norm (x - (0 : SpatialCoordinates d)) i0
      have h' : dist (x i0) 0 ≤ ‖x‖ := by
        simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs, Pi.sub_apply, Pi.zero_apply] using h
      have hx : x i0 = 1 / 2 := by simp only [one_div, Pi.single_eq_same, x, i0]
      rw [hx, Real.dist_eq] at h'
      norm_num at h'
      simpa only [one_div, dist_eq_norm, sub_zero, ge_iff_le] using h'
  have hynorm : dist y (0 : SpatialCoordinates d) = 1 / 2 := by
    apply le_antisymm
    · apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)).2
      intro i
      by_cases hi : i = i0
      · subst i
        simp only [Pi.single_eq_same, Pi.zero_apply, dist_zero_right, norm_div, norm_neg, one_mem, CStarRing.norm_of_mem_unitary, Real.norm_ofNat, one_div, le_refl, y]
      · simp only [ne_eq, hi, not_false_eq_true, Pi.single_eq_of_ne, Pi.zero_apply, dist_self, one_div, inv_nonneg, Nat.ofNat_nonneg, y]
    · have h := norm_le_pi_norm (y - (0 : SpatialCoordinates d)) i0
      have h' : dist (y i0) 0 ≤ ‖y‖ := by
        simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs, Pi.sub_apply, Pi.zero_apply] using h
      have hy : y i0 = -1 / 2 := by simp only [Pi.single_eq_same, y, i0]
      rw [hy, Real.dist_eq] at h'
      norm_num at h'
      simpa only [one_div, dist_eq_norm, sub_zero, ge_iff_le] using h'
  have hxfront : x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    change x ∈ frontier (Metric.ball (0 : SpatialCoordinates d) (1 / 2))
    rw [frontier_ball (0 : SpatialCoordinates d) (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    exact hxnorm
  have hyfront : y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    change y ∈ frontier (Metric.ball (0 : SpatialCoordinates d) (1 / 2))
    rw [frontier_ball (0 : SpatialCoordinates d) (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    exact hynorm
  have hphi : ContDiff ℝ ∞ phi := (affineSlope p0).contDiff
  have hx : x i0 = 1 / 2 := by simp only [one_div, Pi.single_eq_same, x, i0]
  have hy : y i0 = -1 / 2 := by simp only [Pi.single_eq_same, y, i0]
  have heval (v : SpatialCoordinates d) : phi v = v i0 := by
    change affineSlope p0 v = v i0
    rw [affineSlope_apply]
    rw [Finset.sum_eq_single i0]
    · simp only [Pi.single_eq_same, one_mul, p0]
    · intro i hi hne
      simp only [ne_eq, hne, not_false_eq_true, Pi.single_eq_of_ne, zero_mul, p0]
    · intro hi
      exact (hi (Finset.mem_univ i0)).elim
  refine ⟨phi, hphi, x, hxfront, y, hyfront, ?_⟩
  rw [heval x, heval y, hx, hy]
  norm_num

end SubdiffusiveProcess.FiniteStopping
