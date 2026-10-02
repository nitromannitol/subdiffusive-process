import SubdiffusiveProcess.Static.HarmonicCellReflection
import SubdiffusiveProcess.Static.HarmonicCellAffineEnergy

/-! # Quantitative geometry of all-face coefficient reflection -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube

noncomputable section
namespace SubdiffusiveProcess.Static

/-- A fold through the two endpoints of an interval is nonexpanding. -/
theorem intervalFold_abs_sub_le {lo hi : ℝ} (hlohi : lo ≤ hi) (x y : ℝ) :
    |(if x < lo then 2 * lo - x else if x < hi then x else 2 * hi - x) -
      (if y < lo then 2 * lo - y else if y < hi then y else 2 * hi - y)| ≤ |x - y| := by
  have h1 := le_abs_self (x - y)
  have h2 := neg_abs_le (x - y)
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- All-face cube folding has Lipschitz constant one in the native sup norm. -/
theorem lipschitz_cubeCoordinateFold {d : ℕ} (Q : TriadicCube d) :
    LipschitzWith 1 (cubeCoordinateFold Q) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))).2
  intro i
  simp only [Pi.sub_apply, Real.norm_eq_abs, cubeCoordinateFold]
  have hlohi : cubeLowerFaceCoord Q i ≤ cubeUpperFaceCoord Q i := by
    unfold cubeLowerFaceCoord cubeUpperFaceCoord
    have hs : 0 < cubeScaleFactor Q := by unfold cubeScaleFactor; positivity
    nlinarith [hs]
  exact (intervalFold_abs_sub_le hlohi (x i) (y i)).trans
    (by simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - y) i)

/-- The reflected coefficient is continuous. -/
theorem continuous_reflectedCoefficient {d : ℕ} (Q : TriadicCube d)
    (a : Vec d → ℝ) (ha : Continuous a) :
    Continuous (fun x => a (cubeCoordinateFold Q x)) :=
  ha.comp (lipschitz_cubeCoordinateFold Q).continuous

/-- Reflection preserves a logarithmic Lipschitz modulus. -/
theorem reflectedCoefficient_logLipschitz {d : ℕ} (Q : TriadicCube d)
    (a : Vec d → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hlog : ∀ x y, |Real.log (a x) - Real.log (a y)| ≤ D * ‖x - y‖) :
    ∀ x y, |Real.log (a (cubeCoordinateFold Q x)) -
      Real.log (a (cubeCoordinateFold Q y))| ≤ D * ‖x - y‖ := by
  intro x y
  refine (hlog _ _).trans (mul_le_mul_of_nonneg_left ?_ hD)
  simpa only [NNReal.coe_one, one_mul] using
    (lipschitz_cubeCoordinateFold Q).norm_sub_le x y

/-- The same nonexpansion preserves a modulus restricted to any fold image. -/
theorem reflectedCoefficient_logLipschitzOn {d : ℕ} (Q : TriadicCube d)
    (a : Vec d → ℝ) {W V : Set (Vec d)} {D : ℝ} (hD : 0 ≤ D)
    (hmap : Set.MapsTo (cubeCoordinateFold Q) W V)
    (hlog : ∀ x ∈ V, ∀ y ∈ V, |Real.log (a x) - Real.log (a y)| ≤ D * ‖x - y‖) :
    ∀ x ∈ W, ∀ y ∈ W, |Real.log (a (cubeCoordinateFold Q x)) -
      Real.log (a (cubeCoordinateFold Q y))| ≤ D * ‖x - y‖ := by
  intro x hx y hy
  refine (hlog _ (hmap hx) _ (hmap hy)).trans (mul_le_mul_of_nonneg_left ?_ hD)
  simpa only [NNReal.coe_one, one_mul] using
    (lipschitz_cubeCoordinateFold Q).norm_sub_le x y

/-- The parent reflection cube folds into the closed original unit cube. -/
theorem fold_origin_parent_mem_closedBall {d : ℕ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 1)) :
    cubeCoordinateFold (originCube d 0) x ∈ Metric.closedBall (0 : Vec d) (1 / 2) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).2
  intro i
  have hi := (mem_openCubeSet_originCube_iff.mp hx) i
  norm_num only [zpow_one] at hi
  simp only [cubeCoordinateFold, cubeLowerFaceCoord, cubeUpperFaceCoord,
    originCube, Pi.zero_apply, Int.cast_zero, zero_sub, zero_add, cubeScaleFactor, zpow_zero,
    mul_one, Real.norm_eq_abs]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- A half-unit Euclidean neighborhood of any original-cell point stays
inside the parent reflection cube, including at faces and corners. -/
theorem euclideanBall_cell_subset_parent {d : ℕ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) {rho : ℝ}
    (hrho : 0 < rho) (hrhohalf : rho ≤ 1 / 2) :
    euclideanBall x rho ⊆ openCubeSet (originCube d 1) := by
  intro y hy
  have hdist : ‖y - x‖ < rho := euclideanBall_subset_metricBall hrho hy
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have hi := norm_le_pi_norm (y - x) i
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hi
  have hib := lt_of_le_of_lt hi hdist
  rw [abs_lt] at hib
  have hxib := hx i
  norm_num only [zpow_zero, mul_one] at hxib
  norm_num only [zpow_one]
  constructor <;> linarith

end SubdiffusiveProcess.Static
