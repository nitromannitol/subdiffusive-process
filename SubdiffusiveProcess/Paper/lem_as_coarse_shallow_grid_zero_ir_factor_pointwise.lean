import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_osc_sup_pair_bound
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_ahom_exp_pair
import Mathlib.Tactic

open Set Metric TopologicalSpace SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Remove the infrared field from both the cell oscillation and the
positive/inverse scalar factor, paying one compact exponential norm. -/
theorem lem_as_coarse_shallow_grid_zero_ir_factor_pointwise
    {d : ℕ} (f h : C(SpatialCoordinates d, ℝ))
    (y : SpatialCoordinates d) (r : ℝ) (hr : 0 ≤ r)
    (hy : y ∈ Metric.closedBall y r) (s : ℝ) (hs : 0 < s) :
    let O0 : ℝ := sSup {v : ℝ | ∃ a ∈ Metric.closedBall y r,
      ∃ b ∈ Metric.closedBall y r, v = |f a - f b|}
    let O : ℝ := sSup {v : ℝ | ∃ a ∈ Metric.closedBall y r,
      ∃ b ∈ Metric.closedBall y r,
        v = |(f + h) a - (f + h) b|}
    let n : ℝ := ‖h.restrict (Metric.closedBall y r : Set (SpatialCoordinates d))‖
    Real.exp O0 * (s + s⁻¹) ≤
      (Real.exp O * ((Real.exp (h y) * s) + (Real.exp (h y) * s)⁻¹)) *
        Real.exp (3 * n) := by
  intro O0 O n
  have h_abs_le_n : |h y| ≤ n := by
    have h_norm := (h.restrict (Metric.closedBall y r : Set (SpatialCoordinates d))).norm_coe_le_norm ⟨y, hy⟩
    simpa [n, Real.norm_eq_abs] using h_norm
  have h_exp_abs : Real.exp |h y| ≤ Real.exp n := Real.exp_le_exp.mpr h_abs_le_n
  have h_pair := aux_shallow_zero_ir_pair_le s (h y) hs
  have h_osc := aux_shallow_zero_ir_osc_exp_bound f h y r hr
  have h_nonneg_O : 0 ≤ Real.exp O := (Real.exp_pos _).le
  have h_nonneg_O0 : 0 ≤ Real.exp O0 := (Real.exp_pos _).le
  have h_nonneg_sum : 0 ≤ s + s⁻¹ := add_nonneg hs.le (inv_nonneg.mpr hs.le)
  have h_nonneg_pair : 0 ≤ (Real.exp (h y) * s) + (Real.exp (h y) * s)⁻¹ :=
    add_nonneg (mul_nonneg (Real.exp_pos _).le hs.le)
      (inv_nonneg.mpr (mul_nonneg (Real.exp_pos _).le hs.le))
  have h_nonneg_osc_prod : 0 ≤ Real.exp O * Real.exp (2 * n) :=
    mul_nonneg h_nonneg_O (Real.exp_pos _).le
  have h_mid : s + s⁻¹ ≤ Real.exp n * ((Real.exp (h y) * s) + (Real.exp (h y) * s)⁻¹) := by
    calc
      s + s⁻¹ ≤ Real.exp |h y| * ((Real.exp (h y) * s) + (Real.exp (h y) * s)⁻¹) := h_pair
      _ ≤ Real.exp n * ((Real.exp (h y) * s) + (Real.exp (h y) * s)⁻¹) :=
        mul_le_mul_of_nonneg_right h_exp_abs h_nonneg_pair
  calc
    Real.exp O0 * (s + s⁻¹) ≤ (Real.exp O * Real.exp (2 * n)) * (Real.exp n * ((Real.exp (h y) * s) + (Real.exp (h y) * s)⁻¹)) :=
      mul_le_mul h_osc h_mid h_nonneg_sum h_nonneg_osc_prod
    _ = Real.exp O * (Real.exp (2 * n) * Real.exp n) * ((Real.exp (h y) * s) + (Real.exp (h y) * s)⁻¹) := by ring
    _ = Real.exp O * Real.exp (2 * n + n) * ((Real.exp (h y) * s) + (Real.exp (h y) * s)⁻¹) := by rw [Real.exp_add]
    _ = Real.exp O * Real.exp (3 * n) * ((Real.exp (h y) * s) + (Real.exp (h y) * s)⁻¹) := by ring
    _ = (Real.exp O * ((Real.exp (h y) * s) + (Real.exp (h y) * s)⁻¹)) * Real.exp (3 * n) := by ring

end Paper

