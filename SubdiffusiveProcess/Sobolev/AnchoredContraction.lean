import SubdiffusiveProcess.Sobolev.AnchoredLayers
open MeasureTheory Set TopologicalSpace
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess

/-- A contracting spatial dilation bounds the actual anchored compact-root norm by the local Lipschitz envelope times the contraction and root radius. -/
theorem norm_anchored_contraction_on_compact_le
    {d : ℕ} (K : Compacts (SpatialCoordinates d))
    (f : C(SpatialCoordinates d, ℝ)) {c R : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hR : 0 ≤ R)
    (hK : ∀ x ∈ (K : Set (SpatialCoordinates d)), ‖x‖ ≤ R)
    {W : ℝ≥0}
    (hf : LipschitzOnWith W f (Metric.closedBall (0 : SpatialCoordinates d) R)) :
    ‖(f.comp (⟨fun x : SpatialCoordinates d => c • x,
        continuous_const.smul continuous_id⟩ : C(SpatialCoordinates d, SpatialCoordinates d))).restrict
          (K : Set (SpatialCoordinates d)) - ContinuousMap.const K (f 0)‖ ≤
      c * R * (W : ℝ) := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg hc0 hR) W.coe_nonneg)).mpr
  intro x
  have hcx : c • (x : SpatialCoordinates d) ∈
      Metric.closedBall (0 : SpatialCoordinates d) R := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hc0]
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)).trans (by
        simpa only [one_mul] using hK x x.property)
  have hzero : (0 : SpatialCoordinates d) ∈ Metric.closedBall 0 R := by
    simpa [Metric.mem_closedBall] using hR
  have hb := hf.dist_le_mul (c • (x : SpatialCoordinates d)) hcx 0 hzero
  rw [dist_eq_norm, dist_eq_norm, sub_zero] at hb
  change ‖f (c • (x : SpatialCoordinates d)) - f 0‖ ≤ c * R * (W : ℝ)
  exact hb.trans (by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    calc
      (W : ℝ) * (c * ‖(x : SpatialCoordinates d)‖) =
          c * ‖(x : SpatialCoordinates d)‖ * (W : ℝ) := by ring
      _ ≤ c * R * (W : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hK x x.property) hc0) W.coe_nonneg)

end SubdiffusiveProcess
