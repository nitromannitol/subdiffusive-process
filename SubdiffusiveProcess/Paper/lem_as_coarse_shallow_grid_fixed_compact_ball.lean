module

public import SubdiffusiveProcess.Paper.reference_oscillation_moments

@[expose] public section

open MeasureTheory Set Filter Metric ProbabilityTheory TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem lem_as_coarse_shallow_grid_fixed_compact_ball
    (d k : ℕ) (y : SpatialCoordinates d)
    (hy : ∀ i : Fin d, |y i| ≤ (1 / 2 : ℝ)) :
    Metric.closedBall y (3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2)) ⊆
      Metric.closedBall (0 : SpatialCoordinates d) 3 := by
  have hr_le : (3 : ℝ) ^ (-(k : ℤ)) ≤ 1 := by
    rw [zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ (by norm_num) (by omega))
  have hy_norm : ‖y‖ ≤ 1 := by
    rw [Pi.norm_def]
    have hsup : (Finset.univ.sup fun b : Fin d => ‖y b‖₊) ≤ (1 : ℝ≥0) := by
      apply Finset.sup_le
      intro i hi
      apply NNReal.coe_le_coe.mp
      have hh : |y i| ≤ (1 : ℝ) := (hy i).trans (by norm_num)
      simpa [Real.norm_eq_abs] using hh
    exact_mod_cast hsup
  intro x hx
  rw [mem_closedBall, dist_eq_norm]
  have hx' : ‖x - y‖ ≤ 3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2) := by
    simpa [mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_comm] using hx
  have hr_le' : 3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2) ≤ 3 / 2 := by
    calc
      3 * (3 ^ (-(k : ℤ)) / 2) ≤ 3 * ((1 : ℝ) / 2) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hr_le (by norm_num)) (by norm_num)
      _ = 3 / 2 := by ring
  have hxy : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    simpa only [sub_add_cancel] using (norm_add_le (x - y) y)
  have : ‖x‖ ≤ (3 / 2 : ℝ) + 1 := hxy.trans
    (add_le_add (hx'.trans hr_le') hy_norm)
  have hx3 : ‖x‖ ≤ 3 := by nlinarith
  simpa only [sub_zero] using hx3

theorem aux_shallow_fixed_compact_restrict_norm_le
    (d k : ℕ) (y : SpatialCoordinates d)
    (hy : ∀ i : Fin d, |y i| ≤ (1 / 2 : ℝ))
    (h : C(SpatialCoordinates d, ℝ)) :
    ‖h.restrict (aux_reference_oscillation_moments_Kball y
      (3 * ((3 : ℝ) ^ (-(k : ℤ)) / 2)) : Set (SpatialCoordinates d))‖ ≤
    ‖h.restrict (aux_reference_oscillation_moments_Kball
      (0 : SpatialCoordinates d) 3 : Set (SpatialCoordinates d))‖ := by
  apply ContinuousMap.norm_restrict_mono_set h
  exact lem_as_coarse_shallow_grid_fixed_compact_ball d k y hy

end SubdiffusiveProcess.Paper
