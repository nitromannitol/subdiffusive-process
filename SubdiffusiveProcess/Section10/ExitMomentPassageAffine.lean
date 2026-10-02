import SubdiffusiveProcess.Section10.TorsionExitDensityTransport
import SubdiffusiveProcess.Section10.PhysicalLocalTransportResolvent

/-! Powered affine/time normalization uses the already proved literal
survival-event transport. No finiteness or centered-start assumption is used. -/
open MeasureTheory ProbabilityTheory MarkovProcess Set Homogenization SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.ExitMomentPassage
open PhysicalLocalTransport

/-- Exit normalization for an arbitrary open domain and arbitrary path. -/
theorem exitTime_rescale_eq {d : ℕ} (e : Vec d ≃ₜ Vec d) (c : ℝ≥0)
    (hc : 0 < c) (U : Set (Vec d)) (hU : IsOpen U) (w : DiffusionPath d) :
    ContinuousPath.exitTime U (ContinuousPath.rescale e.symm c w) =
      (c : ℝ≥0∞)⁻¹ * ContinuousPath.exitTime (e '' U) w := by
  apply WithTop.eq_of_forall_le_coe_iff
  intro t
  change ContinuousPath.exitTime U (ContinuousPath.rescale e.symm c w) ≤ (t : ℝ≥0∞) ↔ _
  rw [ENNReal.inv_mul_le_iff (ENNReal.coe_ne_zero.mpr hc.ne') ENNReal.coe_ne_top]
  simpa only [not_lt, ENNReal.coe_mul] using
    not_congr (SubdiffusiveProcess.Section10.lt_exitTime_rescale_iff e c hc hU t w)

/-- Literal powered moments of mapped laws, including zero and infinite exits. -/
theorem exitMoment_map_rescale {d : ℕ} (mu : Measure (DiffusionPath d))
    (e : Vec d ≃ₜ Vec d) (c : ℝ≥0) (hc : 0 < c)
    (U : Set (Vec d)) (hU : IsOpen U) (p : ℝ) (hp : 0 < p) :
    (∫⁻ w, ContinuousPath.exitTime U w ^ p
      ∂mu.map (ContinuousPath.rescale e.symm c)) =
        ((c : ℝ≥0∞)^p)⁻¹ * ∫⁻ w, ContinuousPath.exitTime (e '' U) w ^ p ∂mu := by
  have hf : Measurable (fun w : DiffusionPath d => ContinuousPath.exitTime U w ^ p) :=
    (ENNReal.continuous_rpow_const (y := p)).measurable.comp
      (ContinuousPath.isStoppingTime_exitTime U hU).measurable'
  rw [lintegral_map hf (ContinuousPath.measurable_rescale e.symm c)]
  simp_rw [exitTime_rescale_eq e c hc U hU,
    ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.inv_rpow]
  exact lintegral_const_mul _
    ((ENNReal.continuous_rpow_const (y := p)).measurable.comp
      (ContinuousPath.isStoppingTime_exitTime (e '' U) (e.isOpen_image.mpr hU)).measurable')

/-- Restoring the raw positive clock after normalized moment estimates. -/
theorem exitMoment_eq_clock_mul_map {d : ℕ} (mu : Measure (DiffusionPath d))
    (e : Vec d ≃ₜ Vec d) (c : ℝ≥0) (hc : 0 < c)
    (U : Set (Vec d)) (hU : IsOpen U) (p : ℝ) (hp : 0 < p) :
    (∫⁻ w, ContinuousPath.exitTime (e '' U) w ^ p ∂mu) =
      (c : ℝ≥0∞)^p * ∫⁻ w, ContinuousPath.exitTime U w ^ p
        ∂mu.map (ContinuousPath.rescale e.symm c) := by
  rw [exitMoment_map_rescale mu e c hc U hU p hp, ← mul_assoc,
    ENNReal.mul_inv_cancel
      (ENNReal.rpow_pos (by exact_mod_cast hc) ENNReal.coe_ne_top).ne'
      (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.coe_ne_top), one_mul]

/-- The exact image cube under the physical affine chart. -/
theorem physicalCoordinates_image_ball {d : ℕ} (m : ℕ) (z : Vec d) (r : ℝ) :
    physicalCoordinates m z '' Metric.ball (0 : Vec d) r =
      Metric.ball z (r*(3 : ℝ)^m) := by
  ext y
  have h3 : 0 < (3 : ℝ)^m := pow_pos (by norm_num) _
  have hmem : y ∈ physicalCoordinates m z '' Metric.ball (0 : Vec d) r ↔
      (physicalCoordinates m z).symm y ∈ Metric.ball (0 : Vec d) r := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [Homeomorph.symm_apply_apply] using hx
    · intro hy
      exact ⟨_, hy, (physicalCoordinates m z).apply_symm_apply y⟩
  rw [hmem, Metric.mem_ball, Metric.mem_ball, physicalCoordinates_symm_apply,
    dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h3),
    dist_eq_norm]
  rw [inv_mul_lt_iff₀ h3, mul_comm]

end SubdiffusiveProcess.Section10.ExitMomentPassage
