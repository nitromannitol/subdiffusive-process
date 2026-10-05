module

public import SubdiffusiveProcess.Static.HarmonicPairChart
public import SubdiffusiveProcess.Static.HarmonicCutoffGap

@[expose] public section

/-! # Exact affine windows and cutoff datum bounds -/
open MeasureTheory Homogenization Metric
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal Pointwise
noncomputable section
namespace SubdiffusiveProcess.Static

/-- An affine chart pulls a sup-norm ball back to its exactly scaled ball. -/
theorem pair_affine_preimage_ball {d : ℕ} (y x : Vec d) {h r : ℝ} (hh : 0 < h) :
    (fun w => y + h • w) ⁻¹' ball x r = ball (h⁻¹ • (x - y)) (r / h) := by
  ext w
  simp only [Set.mem_preimage, mem_ball, dist_eq_norm]
  have heq : y + h • w - x = h • (w - h⁻¹ • (x - y)) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hh.ne', one_smul]
    abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hh, lt_div_iff₀ hh]
  rw [mul_comm]

/-- The cell chart pulls its domain back to the native unit cube. -/
theorem pair_affine_preimage_cell {d : ℕ} (y : Vec d) {h : ℝ} (hh : 0 < h) :
    (fun w => y + h • w) ⁻¹' ball y (h / 2) = openCubeSet (originCube d 0) := by
  rw [pair_affine_preimage_ball y y hh, sub_self, smul_zero, unitCube_eq_ball]
  congr 1
  field_simp

/-- Any two points in the unit cube have sup-norm distance less than one. -/
theorem pair_unitCube_subset_ball_one {d : ℕ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) :
    openCubeSet (originCube d 0) ⊆ ball x 1 := by
  rw [unitCube_eq_ball, mem_ball_zero_iff] at hx
  intro w hw
  rw [unitCube_eq_ball, mem_ball_zero_iff] at hw
  rw [mem_ball, dist_eq_norm]
  exact (norm_sub_le w x).trans_lt (by linarith)

/-- A comparable mesh keeps the full smooth chart datum uniformly bounded. -/
theorem pair_affine_datum_size {d : ℕ} (y : Vec d) {h g C0 : ℝ}
    (hh : 0 < h) (_hg : 0 < g) (h5 : 5 * h ≤ g) (hC0 : 0 ≤ C0)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hD1 : ∀ x, ‖fderiv ℝ f x‖ ≤ C0 / (g - 3 * h))
    (hD2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C0 / (g - 3 * h) ^ 2) :
    ∀ x, |f (y + h • x)| ≤ 1 + C0 ∧
      ‖fderiv ℝ (fun w => f (y + h • w)) x‖ ≤ 1 + C0 ∧
      ‖fderiv ℝ (fderiv ℝ (fun w => f (y + h • w))) x‖ ≤ 1 + C0 := by
  have hgap : 0 < g - 3 * h := by linarith
  have hhgap : h ≤ g - 3 * h := by linarith
  have h1 : h * (C0 / (g - 3 * h)) ≤ C0 := by
    rw [← mul_div_assoc, div_le_iff₀ hgap]
    nlinarith only [mul_le_mul_of_nonneg_right hhgap hC0]
  have h2 : h ^ 2 * (C0 / (g - 3 * h) ^ 2) ≤ C0 := by
    rw [← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hgap)]
    nlinarith only [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh.le hhgap 2) hC0]
  intro x
  have hD := pair_affine_derivative_bounds y hh f hf hD1 hD2 x
  exact ⟨(by rw [abs_of_nonneg (hf01 _).1]; linarith [(hf01 (y + h • x)).2]),
    hD.1.trans (by linarith), hD.2.trans (by linarith)⟩

end SubdiffusiveProcess.Static
