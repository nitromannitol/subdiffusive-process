module

public import SubdiffusiveProcess.Static.AffineChart
public import SubdiffusiveProcess.Lane4.CubeDilation

@[expose] public section

/-! # Exact affine scaling of the lower integrals in static coercivity -/

open MeasureTheory Homogenization SubdiffusiveProcess SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Static
open scoped ENNReal Pointwise

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Affine change of variables for arbitrary nonnegative integrands. -/
theorem lintegral_ball_affine {d : ℕ} (y : Vec d) {t : ℝ} (ht : 0 < t)
    (g : Vec d → ℝ≥0∞) :
    (∫⁻ x in Metric.ball y (t / 2), g x) = ENNReal.ofReal (t ^ d) *
      ∫⁻ x in openCubeSet (originCube d 0), g (y + t • x) := by
  have hchart : cubeDilation y (0 : Vec d) t = fun x => y + t • x := by
    funext x i
    simp [cubeDilation_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h := lintegral_centeredCube_cubeDilation y (0 : Vec d) ht one_pos g
  simpa only [centeredCube, unitCube_eq_ball, hchart, div_one] using! h

/-- The squared value integral scales by `t^(d+2)` for the normalized chart. -/
theorem l2Sq_ball_affine {d : ℕ} (y : Vec d) {t : ℝ} (ht : 0 < t)
    (u : Vec d → ℝ) :
    (∫⁻ x in Metric.ball y (t / 2), ENNReal.ofReal (u x ^ 2)) =
      ENNReal.ofReal (t ^ (d + 2)) *
        ∫⁻ x in openCubeSet (originCube d 0),
          ENNReal.ofReal ((t⁻¹ * u (y + t • x)) ^ 2) := by
  rw [lintegral_ball_affine y ht]
  have hpoint : ∀ x, ENNReal.ofReal (u (y + t • x) ^ 2) =
      ENNReal.ofReal (t ^ 2) * ENNReal.ofReal ((t⁻¹ * u (y + t • x)) ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_mul (sq_nonneg t)]
    congr 1
    field_simp
  simp_rw [hpoint]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ t ^ d), ← pow_add]

/-- Energy scales by `t^d` because the normalized chart has the unscaled
physical weak gradient. -/
theorem energy_ball_affine {d : ℕ} (y : Vec d) {t : ℝ} (ht : 0 < t)
    (A : Vec d → ℝ) (F : Vec d → Vec d) :
    energy (Metric.ball y (t / 2)) A F = ENNReal.ofReal (t ^ d) *
      energy (openCubeSet (originCube d 0)) (fun x => A (y + t • x))
        (fun x => F (y + t • x)) :=
  lintegral_ball_affine y ht _

private theorem fractionalKernel_affine {d : ℕ} (y : Vec d) {t : ℝ} (ht : 0 < t)
    (u : Vec d → ℝ) (x z : Vec d) :
    ENNReal.ofReal ((u (y + t • x) - u (y + t • z)) ^ 2) /
        ENNReal.ofReal (‖(y + t • x) - (y + t • z)‖ ^ ((d : ℝ) + 3 / 2)) =
      ENNReal.ofReal (t ^ ((1 / 2 : ℝ) - d)) *
        (ENNReal.ofReal (((t⁻¹ * u (y + t • x)) - (t⁻¹ * u (y + t • z))) ^ 2) /
          ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) := by
  by_cases hdiag : x = z
  · subst z
    simp
  have hnorm : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hdiag)
  have hdist : ‖(y + t • x) - (y + t • z)‖ = t * ‖x - z‖ := by
    rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hpow : t ^ 2 = t ^ ((1 / 2 : ℝ) - d) * t ^ ((d : ℝ) + 3 / 2) := by
    rw [← Real.rpow_add ht,
      show (1 / 2 : ℝ) - d + ((d : ℝ) + 3 / 2) = 2 by ring]
    exact (Real.rpow_two t).symm
  have hnum : (u (y + t • x) - u (y + t • z)) ^ 2 = t ^ 2 *
      (((t⁻¹ * u (y + t • x)) - (t⁻¹ * u (y + t • z))) ^ 2) := by
    field_simp
  rw [hdist, Real.mul_rpow ht.le hnorm.le]
  rw [← ENNReal.ofReal_div_of_pos (mul_pos (Real.rpow_pos_of_pos ht _)
    (Real.rpow_pos_of_pos hnorm _)),
    ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hnorm _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), hnum, hpow]
  congr 1
  field_simp



theorem fractionalSeminormSq_ball_affine {d : ℕ} (y : Vec d) {t : ℝ} (ht : 0 < t)
    (u : Vec d → ℝ) :
    fractionalSeminormSq (Metric.ball y (t / 2)) u =
      ENNReal.ofReal (t ^ ((d : ℝ) + 1 / 2)) *
        fractionalSeminormSq (openCubeSet (originCube d 0))
          (fun x => t⁻¹ * u (y + t • x)) := by
  unfold fractionalSeminormSq
  rw [lintegral_ball_affine y ht]
  have hinner : ∀ x,
      (∫⁻ z in Metric.ball y (t / 2),
        ENNReal.ofReal ((u (y + t • x) - u z) ^ 2) /
          ENNReal.ofReal (‖(y + t • x) - z‖ ^ ((d : ℝ) + 3 / 2))) =
      ENNReal.ofReal (t ^ d) * ENNReal.ofReal (t ^ ((1 / 2 : ℝ) - d)) *
        ∫⁻ z in openCubeSet (originCube d 0),
          ENNReal.ofReal (((t⁻¹ * u (y + t • x)) - (t⁻¹ * u (y + t • z))) ^ 2) /
            ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2)) := by
    intro x
    rw [lintegral_ball_affine y ht]
    simp_rw [fractionalKernel_affine y ht u x]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_assoc]
  simp_rw [hinner]
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    ← mul_assoc]
  have hfactor : ENNReal.ofReal (t ^ d) *
      (ENNReal.ofReal (t ^ d) * ENNReal.ofReal (t ^ ((1 / 2 : ℝ) - d))) =
      ENNReal.ofReal (t ^ ((d : ℝ) + 1 / 2)) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ t ^ d),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ t ^ d)]
    congr 1
    simp only [← Real.rpow_natCast]
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    ring
  rw [hfactor]

end SubdiffusiveProcess.Static
