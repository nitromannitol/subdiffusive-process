module

public import SubdiffusiveProcess.Static.AffineIntegrals

@[expose] public section

/-! # Coercivity transfer from the native unit cube to arbitrary real cubes -/

open MeasureTheory Homogenization SubdiffusiveProcess.Static
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The two Jacobian factors of the literal fractional and value integrals. -/
def affineNormPrice (d : ℕ) (t : ℝ) : ℝ := t ^ ((d : ℝ) + 1 / 2) + t ^ (d + 2)

/-- A geometric transfer factor chosen to dominate both the energy and
value Jacobians; its dependence is only on the fixed chart geometry. -/
def affineCoercivityPrice (d : ℕ) (t : ℝ) : ℝ :=
  affineNormPrice d t * ((t ^ d)⁻¹ + (t ^ (d + 2))⁻¹)

theorem affineNormPrice_pos (d : ℕ) {t : ℝ} (ht : 0 < t) : 0 < affineNormPrice d t := by
  unfold affineNormPrice
  positivity

theorem affineCoercivityPrice_pos (d : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < affineCoercivityPrice d t := by
  unfold affineCoercivityPrice
  have := affineNormPrice_pos d ht
  positivity

private theorem affinePrice_jacobian_bounds (d : ℕ) {t : ℝ} (ht : 0 < t) :
    affineNormPrice d t ≤ affineCoercivityPrice d t * t ^ d ∧
      affineNormPrice d t ≤ affineCoercivityPrice d t * t ^ (d + 2) := by
  have hP : 0 ≤ affineNormPrice d t := (affineNormPrice_pos d ht).le
  constructor
  · calc
      affineNormPrice d t = affineNormPrice d t * ((t ^ d)⁻¹ * t ^ d) := by
        rw [inv_mul_cancel₀ (by positivity : t ^ d ≠ 0), mul_one]
      _ ≤ affineNormPrice d t * (((t ^ d)⁻¹ + (t ^ (d + 2))⁻¹) * t ^ d) := by
        gcongr
        exact le_add_of_nonneg_right (by positivity)
      _ = _ := by unfold affineCoercivityPrice; ring
  · calc
      affineNormPrice d t = affineNormPrice d t * ((t ^ (d + 2))⁻¹ * t ^ (d + 2)) := by
        rw [inv_mul_cancel₀ (by positivity : t ^ (d + 2) ≠ 0), mul_one]
      _ ≤ affineNormPrice d t * (((t ^ d)⁻¹ + (t ^ (d + 2))⁻¹) * t ^ (d + 2)) := by
        gcongr
        exact le_add_of_nonneg_left (by positivity)
      _ = _ := by unfold affineCoercivityPrice; ring

/-- Affine comparison of the literal full fractional squared norm. -/
theorem fractionalSqNorm_ball_affine_le {d : ℕ} (y : Vec d) {t : ℝ} (ht : 0 < t)
    (u : Vec d → ℝ) :
    fractionalSqNorm (Metric.ball y (t / 2)) u ≤ ENNReal.ofReal (affineNormPrice d t) *
      fractionalSqNorm (openCubeSet (originCube d 0)) (fun x => t⁻¹ * u (y + t • x)) := by
  change fractionalSeminormSq (Metric.ball y (t / 2)) u +
    (∫⁻ x in Metric.ball y (t / 2), ENNReal.ofReal (u x ^ 2)) ≤ _
  rw [fractionalSeminormSq_ball_affine y ht, l2Sq_ball_affine y ht]
  change _ ≤ _ * (fractionalSeminormSq _ _ + _)
  rw [mul_add]
  apply add_le_add
  · apply mul_le_mul_left
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by positivity))
  · apply mul_le_mul_left
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (Real.rpow_nonneg ht.le _))

/-- The native `H¹` coercivity estimate transports with a fixed geometric
factor, and no alteration of the physical coefficient. -/
theorem H1_coercivity_affine {d : ℕ} (y : Vec d) {t K : ℝ} (ht : 0 < t) (hK : 0 ≤ K)
    (A : Vec d → ℝ)
    (hunit : ∀ W : H1Function (openCubeSet (originCube d 0)),
      fractionalSqNorm (openCubeSet (originCube d 0)) W.toFun ≤ ENNReal.ofReal K *
        (energy (openCubeSet (originCube d 0)) (fun x => A (y + t • x)) W.grad +
          ∫⁻ x in openCubeSet (originCube d 0), ENNReal.ofReal (W.toFun x ^ 2))) :
    ∀ H : H1Function (Metric.ball y (t / 2)),
      fractionalSqNorm (Metric.ball y (t / 2)) H.toFun ≤
        ENNReal.ofReal (K * affineCoercivityPrice d t) *
          (energy (Metric.ball y (t / 2)) A H.grad +
            ∫⁻ x in Metric.ball y (t / 2), ENNReal.ofReal (H.toFun x ^ 2)) := by
  intro H
  obtain ⟨W, hWf, hWg⟩ := exists_H1_affine_chart y ht H
  have hu := hunit W
  rw [hWf, hWg] at hu
  refine ((fractionalSqNorm_ball_affine_le y ht H.toFun).trans
    (mul_le_mul_right hu _)).trans ?_
  rw [← mul_assoc, mul_add]
  rw [energy_ball_affine y ht, l2Sq_ball_affine y ht, mul_add]
  have hP := affinePrice_jacobian_bounds d ht
  have hT : 0 ≤ affineCoercivityPrice d t := (affineCoercivityPrice_pos d ht).le
  rw [ENNReal.ofReal_mul hK]
  apply add_le_add
  · have hbound := mul_le_mul_left (ENNReal.ofReal_le_ofReal hP.1) (ENNReal.ofReal K)
    rw [ENNReal.ofReal_mul hT] at hbound
    have h := mul_le_mul_left hbound
      (energy (openCubeSet (originCube d 0)) (fun x => A (y + t • x))
        (fun x => H.grad (y + t • x)))
    convert h using 1 <;> ring
  · have hbound := mul_le_mul_left (ENNReal.ofReal_le_ofReal hP.2) (ENNReal.ofReal K)
    rw [ENNReal.ofReal_mul hT] at hbound
    have h := mul_le_mul_left hbound
      (∫⁻ x in openCubeSet (originCube d 0), ENNReal.ofReal ((t⁻¹ * H.toFun (y + t • x)) ^ 2))
    convert h using 1 <;> ring

/-- The same transfer preserves the pure-energy conclusion for `H¹₀`. -/
theorem H10_coercivity_affine {d : ℕ} (y : Vec d) {t K : ℝ} (ht : 0 < t) (hK : 0 ≤ K)
    (A : Vec d → ℝ)
    (hunit : ∀ W : H10Function (openCubeSet (originCube d 0)),
      fractionalSqNorm (openCubeSet (originCube d 0)) W.toFun ≤ ENNReal.ofReal K *
        energy (openCubeSet (originCube d 0)) (fun x => A (y + t • x)) W.grad) :
    ∀ H : H10Function (Metric.ball y (t / 2)),
      fractionalSqNorm (Metric.ball y (t / 2)) H.toFun ≤
        ENNReal.ofReal (K * affineCoercivityPrice d t) *
          energy (Metric.ball y (t / 2)) A H.grad := by
  intro H
  obtain ⟨W, hWf, hWg⟩ := exists_H10_affine_chart y ht H
  have hu := hunit W
  rw [hWf, hWg] at hu
  refine ((fractionalSqNorm_ball_affine_le y ht H.toFun).trans
    (mul_le_mul_right hu _)).trans ?_
  rw [energy_ball_affine y ht]
  have hP := (affinePrice_jacobian_bounds d ht).1
  have hT : 0 ≤ affineCoercivityPrice d t := (affineCoercivityPrice_pos d ht).le
  rw [ENNReal.ofReal_mul hK]
  have hbound := mul_le_mul_left (ENNReal.ofReal_le_ofReal hP) (ENNReal.ofReal K)
  rw [ENNReal.ofReal_mul hT] at hbound
  have h := mul_le_mul_left hbound
    (energy (openCubeSet (originCube d 0)) (fun x => A (y + t • x))
      (fun x => H.grad (y + t • x)))
  convert h using 1 <;> ring

end SubdiffusiveProcess.Static
