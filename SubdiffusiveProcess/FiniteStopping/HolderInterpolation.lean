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

/-! This module establishes isHolderOn beta of alpha for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- isHolderOn beta of alpha in the finite stopping construction. -/
theorem isHolderOn_beta_of_alpha {d : ℕ} {alpha beta : ℝ} (hab : beta ≤ alpha)
    (G : SpatialCoordinates d → ℝ)
    (hG : Lane4.IsHolderOn alpha
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) G) :
    Lane4.IsHolderOn beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) G := by
  unfold Lane4.IsHolderOn at hG ⊢
  obtain ⟨M, hM⟩ := hG
  refine ⟨M * (Real.sqrt d) ^ (alpha - beta), ?_⟩
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  have hxy1 : dist x y ≤ 1 := by
    have hx' : x ∈ Metric.closedBall (0 : SpatialCoordinates d) (1 / 2) :=
      Metric.closure_ball_subset_closedBall (frontier_subset_closure hx)
    have hy' : y ∈ Metric.closedBall (0 : SpatialCoordinates d) (1 / 2) :=
      Metric.closure_ball_subset_closedBall (frontier_subset_closure hy)
    calc dist x y ≤ dist x 0 + dist 0 y := dist_triangle x 0 y
      _ ≤ 1 / 2 + 1 / 2 := add_le_add (by simpa only [dist_zero_right, one_div, Metric.mem_closedBall] using hx') (by simpa only [dist_comm, dist_zero_right, one_div, Metric.mem_closedBall] using hy')
      _ = 1 := by norm_num
  set t : ℝ := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with htdef
  have hne : ∃ j, x j ≠ y j := by
    by_contra hcon; push_neg at hcon; exact hxy (funext hcon)
  have ht0 : 0 < t := by
    obtain ⟨j, hj⟩ := hne
    refine Real.sqrt_pos.2 (Finset.sum_pos' (fun i _ => by positivity) ⟨j, Finset.mem_univ j, ?_⟩)
    exact sq_pos_of_ne_zero (sub_ne_zero.2 hj)
  have htD : t ≤ Real.sqrt d := by
    rw [htdef]
    apply Real.sqrt_le_sqrt
    calc (∑ j : Fin d, (x j - y j) ^ 2) ≤ ∑ _j : Fin d, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hcoord : |x i - y i| ≤ dist x y := by
            have hle := norm_le_pi_norm (x - y) i
            simpa only [dist_eq_norm, ge_iff_le, Pi.sub_apply, Real.norm_eq_abs] using hle
          have hcoord1 : |x i - y i| ≤ 1 := hcoord.trans hxy1
          have hsq : (x i - y i) ^ 2 ≤ 1 := by
            rw [← sq_abs]
            exact pow_le_one₀ (abs_nonneg _) hcoord1
          linarith only [hab, hM, hx, hy, hxy, hxy1, htdef, hne, ht0, hcoord, hcoord1, hsq]
      _ = (d : ℝ) := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hab' : 0 ≤ alpha - beta := by linarith only [hab, hM, hx, hy, hxy, hxy1, htdef, hne, ht0, htD]
  have hMv : |G x - G y| / t ^ alpha ≤ M := hM ⟨x, hx, y, hy, hxy, rfl⟩
  have htapos : (0 : ℝ) < t ^ alpha := Real.rpow_pos_of_pos ht0 alpha
  have hMnn : 0 ≤ M := le_trans (div_nonneg (abs_nonneg _) htapos.le) hMv
  have hbound : |G x - G y| ≤ M * t ^ alpha := (div_le_iff₀ htapos).1 hMv
  have hsplit : t ^ alpha = t ^ beta * t ^ (alpha - beta) := by
    have hadd := Real.rpow_add ht0 beta (alpha - beta)
    rwa [show beta + (alpha - beta) = alpha by ring] at hadd
  have hpow : t ^ (alpha - beta) ≤ (Real.sqrt d) ^ (alpha - beta) :=
    Real.rpow_le_rpow ht0.le htD hab'
  have htbpos : (0 : ℝ) < t ^ beta := Real.rpow_pos_of_pos ht0 beta
  have hfinal : |G x - G y| ≤ M * (Real.sqrt d) ^ (alpha - beta) * t ^ beta := by
    calc |G x - G y| ≤ M * t ^ alpha := hbound
      _ = M * (t ^ beta * t ^ (alpha - beta)) := by rw [hsplit]
      _ ≤ M * (t ^ beta * (Real.sqrt d) ^ (alpha - beta)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow htbpos.le) hMnn
      _ = M * (Real.sqrt d) ^ (alpha - beta) * t ^ beta := by ring
  exact (div_le_iff₀ htbpos).2 hfinal

end SubdiffusiveProcess.FiniteStopping
