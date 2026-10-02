import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.BallForcing
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.LocalGradientIteration
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.NormalizedL2
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Bridge

/-!
# Sup-ball geometry for the small-contrast Campanato readout

The Campanato telescope is run on the ambient sup-balls.  Their volume is
exactly `(2*r)^d`, while the local gradient estimate is available on the
containing Euclidean ball of radius `d*r`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

noncomputable section

variable {d : ℕ}

theorem euclideanBall_half_subset_unit_of_mem_half [NeZero d]
    {z : Vec d} (hz : z ∈ smallContrastBall d (1 / 2)) :
    euclideanBall z (1 / 2) ⊆ smallContrastUnitBall d := by
  apply euclideanBall_subset_of_center_distance_add_lt
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hzE := (mem_euclideanBall_toEuc_iff z 0
    (by norm_num : (0 : ℝ) < 1 / 2)).2 hz
  have hzlt : euclideanNorm z < 1 / 2 := by
    rw [Metric.mem_ball, dist_eq_norm] at hzE
    have heq : ‖toEuc z - toEuc 0‖ = euclideanNorm z := by
      unfold euclideanNorm
      rw [show vecNormSq z = euclideanSqDist z 0 by
        simp [euclideanSqDist, vecNormSq]]
      rw [← norm_sq_toEuc_sub z 0, Real.sqrt_sq (norm_nonneg _)]
    rw [heq] at hzE
    exact hzE
  simpa only [sub_zero] using (show euclideanNorm z + 1 / 2 ≤ 1 by linarith)

/-- Every sup-ball of radius `r` is contained in the Euclidean ball of radius
`d*r`. -/
theorem metricBall_subset_euclideanBall_dimension [NeZero d]
    (z : Vec d) (r : ℝ) :
    Metric.ball z r ⊆ euclideanBall z ((d : ℝ) * r) := by
  intro x hx
  have hsup : ‖x - z‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hE := euclideanNorm_le_dimension_mul_norm (x - z)
  have hlt : euclideanNorm (x - z) < (d : ℝ) * r :=
    lt_of_le_of_lt hE (mul_lt_mul_of_pos_left hsup (by
      have : 0 < (d : ℝ) := by
        by_contra h
        have : (d : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg d)
        exact (NeZero.ne d) (Nat.cast_eq_zero.mp this)
      exact this))
  have hrpos : 0 < r := lt_of_le_of_lt (norm_nonneg _) hsup
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hradius : 0 < (d : ℝ) * r := mul_pos hdpos hrpos
  apply (mem_euclideanBall_toEuc_iff x z hradius).1
  rw [Metric.mem_ball, dist_eq_norm]
  have heq : ‖toEuc x - toEuc z‖ = euclideanNorm (x - z) := by
    unfold euclideanNorm
    change ‖toEuc x - toEuc z‖ = Real.sqrt (euclideanSqDist x z)
    rw [← norm_sq_toEuc_sub x z, Real.sqrt_sq (norm_nonneg _)]
  rwa [heq]

/-- Real volume of a positive-radius sup-ball. -/
theorem volume_metricBall_toReal (z : Vec d) {r : ℝ} (hr : 0 < r) :
    (volume (Metric.ball z r)).toReal = (2 * r) ^ d := by
  rw [Real.volume_pi_ball z hr, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]

theorem volume_metricBall_toReal_pos (z : Vec d) {r : ℝ} (hr : 0 < r) :
    0 < (volume (Metric.ball z r)).toReal := by
  rw [volume_metricBall_toReal z hr]
  positivity

/-- The exact normalized-volume price from a radius-`r` sup-ball to its
Euclidean radius-`d*r` parent. -/
def metricToEuclideanVolumePrice (d : ℕ) : ℝ :=
  Real.sqrt
    ((volume (smallContrastUnitBall d)).toReal * (d : ℝ) ^ d / (2 : ℝ) ^ d)

theorem metricToEuclideanVolumePrice_nonneg (d : ℕ) :
    0 ≤ metricToEuclideanVolumePrice d :=
  Real.sqrt_nonneg _

theorem sqrt_volume_euclideanBall_dimension_div_metricBall [NeZero d]
    (z : Vec d) {r : ℝ} (hr : 0 < r) :
    Real.sqrt ((volume (euclideanBall z ((d : ℝ) * r))).toReal /
        (volume (Metric.ball z r)).toReal) =
      metricToEuclideanVolumePrice d := by
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  rw [volume_euclideanBall_toReal_eq_unit_mul_pow z (mul_pos hdpos hr),
    volume_metricBall_toReal z hr]
  unfold metricToEuclideanVolumePrice
  congr 1
  rw [mul_pow]
  rw [mul_pow]
  field_simp [ne_of_gt hr, ne_of_gt hdpos]

/-- Consecutive dyadic sup-balls have normalized-volume price `sqrt (2^d)`. -/
def halfBallVolumePrice (d : ℕ) : ℝ := Real.sqrt ((2 : ℝ) ^ d)

theorem halfBallVolumePrice_nonneg (d : ℕ) : 0 ≤ halfBallVolumePrice d :=
  Real.sqrt_nonneg _

theorem sqrt_volume_metricBall_div_halfBall
    (z : Vec d) {r : ℝ} (hr : 0 < r) :
    Real.sqrt ((volume (Metric.ball z r)).toReal /
        (volume (Metric.ball z (r / 2))).toReal) = halfBallVolumePrice d := by
  rw [volume_metricBall_toReal z hr,
    volume_metricBall_toReal z (by positivity : 0 < r / 2)]
  unfold halfBallVolumePrice
  congr 1
  rw [show 2 * (r / 2) = r by ring]
  field_simp [ne_of_gt hr]
  ring

/-- A radius-three parent costs `sqrt (3^d)` in normalized `L²`. -/
def tripleBallVolumePrice (d : ℕ) : ℝ := Real.sqrt ((3 : ℝ) ^ d)

theorem tripleBallVolumePrice_nonneg (d : ℕ) : 0 ≤ tripleBallVolumePrice d :=
  Real.sqrt_nonneg _

theorem sqrt_volume_tripleBall_div_ball
    (z w : Vec d) {r : ℝ} (hr : 0 < r) :
    Real.sqrt ((volume (Metric.ball z (3 * r))).toReal /
        (volume (Metric.ball w r)).toReal) = tripleBallVolumePrice d := by
  rw [volume_metricBall_toReal z (by positivity : 0 < 3 * r),
    volume_metricBall_toReal w hr]
  unfold tripleBallVolumePrice
  congr 1
  field_simp [ne_of_gt hr]
  rw [show 2 * 3 * r = (2 * r) * 3 by ring, mul_pow]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
