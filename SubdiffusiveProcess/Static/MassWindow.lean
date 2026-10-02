import SubdiffusiveProcess.Static.CubeMassAffine

/-! # A fixed triadic window for arbitrary reference geometry -/
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
noncomputable section
namespace SubdiffusiveProcess.Static

/-- One fixed enlarged window contains every point of the reference cube at
all physical parent scales. -/
theorem exists_mass_window {d : ℕ} (y0 : Vec d) (ρ0 : ℝ) :
    ∃ J : ℕ, ∀ m : ℕ, ∀ x ∈ Metric.ball y0 (ρ0 / 2),
      (3 : ℝ) ^ m • x ∈ openCubeSet (originCube d ((m : ℤ) + (J : ℤ))) := by
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (2 * ‖y0‖ + ρ0) (by norm_num : (1 : ℝ) < 3)
  refine ⟨J, ?_⟩
  intro m x hx
  have hnorm : ‖x‖ < (3 : ℝ) ^ J / 2 := by
    have hx' := Metric.mem_ball.mp hx
    rw [dist_eq_norm] at hx'
    have hn := norm_add_le (x - y0) y0
    rw [sub_add_cancel] at hn
    linarith
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hi0 : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hi : |x i| < (3 : ℝ) ^ J / 2 := hi0.trans_lt hnorm
  rw [abs_lt] at hi
  simp only [Pi.smul_apply, smul_eq_mul, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  have hp : 0 < (3 : ℝ) ^ m := by positivity
  constructor
  · have h := mul_lt_mul_of_pos_left hi.1 hp
    nlinarith only [h]
  · have h := mul_lt_mul_of_pos_left hi.2 hp
    nlinarith only [h]

end SubdiffusiveProcess.Static
