module

public import SubdiffusiveProcess.Paper.prop_speed_resolvent
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

@[expose] public section

/-! Supports: mfd_lem_killing.
Literal integral-to-Hilbert conversion for the produced trace objective. -/
open MeasureTheory SubdiffusiveProcess
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_mfd_lem_killing_trace_objective
    {d : ℕ}
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (v : SpatialCoordinates d → ℝ) (w : Lp ℝ 2 nu)
    (hvw : v =ᵐ[nu] w) (e lam : ℝ) :
    e + lam * (∫ x, v x ^ 2 ∂nu) - 2 * (∫ x, f x * v x ∂nu) =
      e + lam * ‖w‖ ^ 2 - 2 * ⟪BoundedContinuousFunction.toLp 2 nu ℝ f, w⟫_ℝ := by
  have hload : (∫ x, f x * v x ∂nu) =
      ⟪BoundedContinuousFunction.toLp 2 nu ℝ f, w⟫_ℝ := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hvw, BoundedContinuousFunction.coeFn_toLp 2 nu ℝ f] with x hx hfx
    rw [hx, hfx]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  rw [aux_prop_speed_resolvent_sq_integral_congr v w hvw, hload]

end Paper
