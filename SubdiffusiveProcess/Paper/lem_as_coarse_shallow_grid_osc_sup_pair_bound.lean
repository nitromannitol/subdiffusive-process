module

public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Tactic

@[expose] public section

open Set Metric Topology TopologicalSpace SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The closed-ball oscillation supremum controls every pair of points in
that ball; boundedness is supplied by continuity on its compact closure. -/
theorem lem_as_coarse_shallow_grid_osc_sup_pair_bound {d : ℕ}
    (g : C(SpatialCoordinates d, ℝ)) (y : SpatialCoordinates d)
    (r : ℝ) (x x' : SpatialCoordinates d)
    (hx : x ∈ Metric.closedBall y r) (hx' : x' ∈ Metric.closedBall y r) :
    |g x - g x'| ≤
      sSup {v : ℝ | ∃ a ∈ Metric.closedBall y r,
        ∃ b ∈ Metric.closedBall y r, v = |g a - g b|} := by
  let K : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall y r, ProperSpace.isCompact_closedBall y r⟩
  let S : Set ℝ := {v : ℝ | ∃ a ∈ Metric.closedBall y r,
    ∃ b ∈ Metric.closedBall y r, v = |g a - g b|}
  have hbound : BddAbove S := by
    refine ⟨2 * ‖g.restrict (K : Set (SpatialCoordinates d))‖, ?_⟩
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := hv
    have ha' := (g.restrict (K : Set (SpatialCoordinates d))).norm_coe_le_norm ⟨a, ha⟩
    have hb' := (g.restrict (K : Set (SpatialCoordinates d))).norm_coe_le_norm ⟨b, hb⟩
    have htri := abs_sub_le (g a) 0 (g b)
    simp only [sub_zero, zero_sub, abs_neg] at htri
    have ha'' : |g a| ≤ ‖g.restrict (K : Set (SpatialCoordinates d))‖ := by
      simpa only [ContinuousMap.restrict_apply, Real.norm_eq_abs] using ha'
    have hb'' : |g b| ≤ ‖g.restrict (K : Set (SpatialCoordinates d))‖ := by
      simpa only [ContinuousMap.restrict_apply, Real.norm_eq_abs] using hb'
    linarith
  have hmem : |g x - g x'| ∈ S := ⟨x, hx, x', hx', rfl⟩
  exact le_csSup hbound hmem

/-- Removing an infrared potential changes the closed-ball oscillation by
at most twice its compact supremum norm. -/
theorem aux_shallow_osc_without_H_le
    {d : ℕ} (f h : C(SpatialCoordinates d, ℝ))
    (y : SpatialCoordinates d) (r : ℝ) (hr : 0 ≤ r) :
    sSup {v : ℝ | ∃ a ∈ Metric.closedBall y r,
      ∃ b ∈ Metric.closedBall y r, v = |f a - f b|} ≤
      sSup {v : ℝ | ∃ a ∈ Metric.closedBall y r,
        ∃ b ∈ Metric.closedBall y r,
          v = |(f + h) a - (f + h) b|} +
        2 * ‖h.restrict (Metric.closedBall y r : Set (SpatialCoordinates d))‖ := by
  let K : Compacts (SpatialCoordinates d) :=
    ⟨Metric.closedBall y r, ProperSpace.isCompact_closedBall y r⟩
  let S : Set ℝ := {v : ℝ | ∃ a ∈ Metric.closedBall y r,
    ∃ b ∈ Metric.closedBall y r, v = |f a - f b|}
  have hy : y ∈ Metric.closedBall y r := Metric.mem_closedBall_self hr
  have hne : S.Nonempty := ⟨0, y, hy, y, hy, by simp⟩
  refine csSup_le hne ?_
  intro v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := hv
  have hFH := lem_as_coarse_shallow_grid_osc_sup_pair_bound (f + h) y r a b ha hb
  have ha' := (h.restrict (K : Set (SpatialCoordinates d))).norm_coe_le_norm ⟨a, ha⟩
  have hb' := (h.restrict (K : Set (SpatialCoordinates d))).norm_coe_le_norm ⟨b, hb⟩
  have ha'' : |h a| ≤ ‖h.restrict (K : Set (SpatialCoordinates d))‖ := by
    simpa only [ContinuousMap.restrict_apply, Real.norm_eq_abs] using ha'
  have hb'' : |h b| ≤ ‖h.restrict (K : Set (SpatialCoordinates d))‖ := by
    simpa only [ContinuousMap.restrict_apply, Real.norm_eq_abs] using hb'
  have htri : |f a - f b| ≤ |(f + h) a - (f + h) b| + |h a - h b| := by
    have heq : f a - f b = ((f + h) a - (f + h) b) - (h a - h b) := by
      simp only [ContinuousMap.add_apply]
      ring
    rw [heq]
    simpa only [← sub_eq_add_neg, abs_neg] using
      (abs_add_le ((f + h) a - (f + h) b) (-(h a - h b)))
  have habs := abs_sub_le (h a) 0 (h b)
  simp only [sub_zero, zero_sub, abs_neg] at habs
  change |h a| ≤ ‖h.restrict (Metric.closedBall y r : Set (SpatialCoordinates d))‖ at ha''
  change |h b| ≤ ‖h.restrict (Metric.closedBall y r : Set (SpatialCoordinates d))‖ at hb''
  linarith

/-- The infrared-free exponential oscillation is bounded by the full-field
oscillation times the compact exponential norm of the infrared field. -/
theorem aux_shallow_zero_ir_osc_exp_bound
    {d : ℕ} (f h : C(SpatialCoordinates d, ℝ))
    (y : SpatialCoordinates d) (r : ℝ) (hr : 0 ≤ r) :
    Real.exp (sSup {v : ℝ | ∃ a ∈ Metric.closedBall y r,
      ∃ b ∈ Metric.closedBall y r, v = |f a - f b|}) ≤
      Real.exp (sSup {v : ℝ | ∃ a ∈ Metric.closedBall y r,
        ∃ b ∈ Metric.closedBall y r,
          v = |(f + h) a - (f + h) b|}) *
      Real.exp (2 * ‖h.restrict (Metric.closedBall y r : Set (SpatialCoordinates d))‖) := by
  have hineq := aux_shallow_osc_without_H_le f h y r hr
  have h_exp := Real.exp_le_exp.mpr hineq
  rw [Real.exp_add] at h_exp
  exact h_exp

end SubdiffusiveProcess.Paper
