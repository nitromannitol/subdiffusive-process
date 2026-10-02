import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Analysis.RadialKernel
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal
namespace SubdiffusiveProcess

/-- The literal Euclidean fractional square integral is finite for a Lipschitz field on a cube, by radial domination and Haar translation. Used for M’s smooth test carrier, lines 988–1036. -/
theorem fractional_square_integral_lt_top_of_lipschitzOnWith
    {d k : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (f : SpatialCoordinates d → Fin k → ℝ) (K : ℝ≥0)
    (hf : LipschitzOnWith K f (centeredCube z r hr : Set (SpatialCoordinates d))) :
    (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin k, (f x i - f y i) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * s)) < ⊤ := by
  let q : ℝ := 2 - (d : ℝ) - 2 * s
  let C : ℝ := (k : ℝ) * (K : ℝ) ^ 2
  let H : SpatialCoordinates d → ℝ≥0∞ := fun w =>
    (Metric.ball (0 : SpatialCoordinates d) r).indicator
      (fun w => ENNReal.ofReal (‖w‖ ^ q)) w
  have hq : -(d : ℝ) < q := by dsimp [q]; linarith
  have hkernel := integrableOn_norm_rpow_ball (Nat.zero_lt_of_lt hd) q r hq
  have hH_lt_top : (∫⁻ w, H w) < ⊤ := by
    have hI : Integrable
        ((Metric.ball (0 : SpatialCoordinates d) r).indicator
          (fun w : SpatialCoordinates d => ‖w‖ ^ q)) :=
      hkernel.integrable_indicator Metric.isOpen_ball.measurableSet
    have hnonneg : 0 ≤ᵐ[volume]
        (Metric.ball (0 : SpatialCoordinates d) r).indicator
          (fun w : SpatialCoordinates d => ‖w‖ ^ q) := by
      filter_upwards [] with w
      by_cases hw : w ∈ Metric.ball (0 : SpatialCoordinates d) r
      · rw [indicator_of_mem hw]
        exact Real.rpow_nonneg (norm_nonneg _) _
      · rw [indicator_of_notMem hw]
        change (0 : ℝ) ≤ 0
        exact le_rfl
    have hIfin := hI.hasFiniteIntegral
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnonneg] at hIfin
    have heq : (fun w : SpatialCoordinates d =>
        ENNReal.ofReal ((Metric.ball (0 : SpatialCoordinates d) r).indicator
          (fun u : SpatialCoordinates d => ‖u‖ ^ q) w)) = H := by
      funext w
      by_cases hw : w ∈ Metric.ball (0 : SpatialCoordinates d) r
      · simp only [H, indicator_of_mem hw]
      · simp only [H, indicator_of_notMem hw, ENNReal.ofReal_zero]
    rwa [heq] at hIfin
  have hH_meas : Measurable H := by
    dsimp [H]
    apply Measurable.indicator
    · fun_prop
    · exact Metric.isOpen_ball.measurableSet
  have hdist (x y : SpatialCoordinates d) :
      ‖x - y‖ ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    apply (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).2
    calc
      |(x - y) i| ^ 2 = (x i - y i) ^ 2 := by simp [sq_abs]
      _ ≤ ∑ j : Fin d, (x j - y j) ^ 2 := by
        exact Finset.single_le_sum (fun j _ => sq_nonneg (x j - y j)) (Finset.mem_univ i)
  have hnum (x y : SpatialCoordinates d)
      (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)))
      (hy : y ∈ (centeredCube z r hr : Set (SpatialCoordinates d))) :
      ∑ i : Fin k, (f x i - f y i) ^ 2 ≤ C * ‖x - y‖ ^ 2 := by
    have hL : ‖f x - f y‖ ≤ (K : ℝ) * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hf.dist_le_mul x hx y hy
    calc
      _ ≤ ∑ _i : Fin k, ((K : ℝ) * ‖x - y‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : |f x i - f y i| ≤ (K : ℝ) * ‖x - y‖ :=
          (((pi_norm_le_iff_of_nonneg (norm_nonneg (f x - f y))).mp le_rfl) i).trans hL
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg (NNReal.coe_nonneg K) (norm_nonneg _))).2 hi'
      _ = C * ‖x - y‖ ^ 2 := by simp [C]; ring
  have hdiff_mem (x y : SpatialCoordinates d)
      (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)))
      (hy : y ∈ (centeredCube z r hr : Set (SpatialCoordinates d))) :
      x - y ∈ Metric.ball (0 : SpatialCoordinates d) r := by
    have hx' : ‖x - z‖ < r / 2 := by
      simpa only [centeredCube, Opens.coe_mk, Metric.mem_ball, dist_eq_norm] using hx
    have hy' : ‖z - y‖ < r / 2 := by
      have := Metric.mem_ball.mp hy
      simpa only [dist_eq_norm, norm_sub_rev] using this
    apply Metric.mem_ball.mpr
    simp only [dist_zero_right]
    calc
      ‖x - y‖ = ‖(x - z) + (z - y)‖ := by congr 1; module
      _ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
      _ < r := by linarith
  have hpoint (x y : SpatialCoordinates d)
      (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)))
      (hy : y ∈ (centeredCube z r hr : Set (SpatialCoordinates d))) :
      ENNReal.ofReal (∑ i : Fin k, (f x i - f y i) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * s) ≤ ENNReal.ofReal C * H (x - y) := by
    by_cases hxy : x = y
    · subst y
      simp
    · have ht : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
      have hp : 0 ≤ (d : ℝ) + 2 * s := by positivity
      have hquot :
          ENNReal.ofReal (∑ i : Fin k, (f x i - f y i) ^ 2) /
              (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                ((d : ℝ) + 2 * s) ≤
            ENNReal.ofReal (C * ‖x - y‖ ^ 2) /
              ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + 2 * s) := by
        apply ENNReal.div_le_div
        · exact ENNReal.ofReal_le_ofReal (hnum x y hx hy)
        · exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hdist x y)) hp
      calc
        _ ≤ ENNReal.ofReal (C * ‖x - y‖ ^ 2) /
              ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + 2 * s) := hquot
        _ = ENNReal.ofReal C * ENNReal.ofReal (‖x - y‖ ^ q) := by
          rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow (norm_nonneg _) 2]
          rw [mul_div_assoc, ← ENNReal.rpow_natCast]
          have hpow := ENNReal.rpow_sub (x := ENNReal.ofReal ‖x - y‖)
            (2 : ℝ) ((d : ℝ) + 2 * s)
            (ENNReal.ofReal_ne_zero_iff.mpr ht) ENNReal.ofReal_ne_top
          change ENNReal.ofReal C *
              (ENNReal.ofReal ‖x - y‖ ^ (2 : ℝ) /
                ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + 2 * s)) = _
          rw [← hpow]
          rw [ENNReal.ofReal_rpow_of_pos ht]
          congr 2
          dsimp [q]
          ring_nf
        _ = ENNReal.ofReal C * H (x - y) := by
          rw [show H (x - y) = ENNReal.ofReal (‖x - y‖ ^ q) by
            simp only [H, indicator_of_mem (hdiff_mem x y hx hy)]]
  have hinner (x : SpatialCoordinates d)
      (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))) :
      (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin k, (f x i - f y i) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * s)) ≤ ENNReal.ofReal C * (∫⁻ w, H w) := by
    calc
      _ ≤ ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal C * H (x - y) := by
        apply setLIntegral_mono' (centeredCube z r hr).isOpen.measurableSet
        intro y hy
        exact hpoint x y hx hy
      _ ≤ ∫⁻ y, ENNReal.ofReal C * H (x - y) :=
        setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal C * (∫⁻ y, H (x - y)) := by
        simpa only [Function.comp_apply] using
          (lintegral_const_mul'' (μ := volume) (ENNReal.ofReal C)
            (hH_meas.comp (by fun_prop : Measurable fun y : SpatialCoordinates d => x - y)).aemeasurable)
      _ = ENNReal.ofReal C * (∫⁻ w, H w) := by
        congr 1
        exact (volume.measurePreserving_sub_left x).lintegral_comp_emb
          (MeasurableEquiv.subLeft x).measurableEmbedding H
  calc
    _ ≤ ∫⁻ _x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal C * (∫⁻ w, H w) := by
      apply setLIntegral_mono' (centeredCube z r hr).isOpen.measurableSet
      intro x hx
      exact hinner x hx
    _ = (ENNReal.ofReal C * (∫⁻ w, H w)) *
        volume (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      rw [setLIntegral_const]
    _ < ⊤ := by
      apply ENNReal.mul_lt_top
      · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hH_lt_top
      · rw [centeredCube_volume z hr]
        exact ENNReal.ofReal_lt_top

end SubdiffusiveProcess
