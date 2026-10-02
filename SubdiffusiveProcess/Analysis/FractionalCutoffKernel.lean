import SubdiffusiveProcess.Analysis.RadialTruncatedKernel
import Mathlib.Topology.MetricSpace.Lipschitz
import Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry

open MeasureTheory Filter Set Homogenization
open scoped ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-- A Lipschitz cutoff equal to one on the unit cube and supported in the cube of side two. -/
def cubeExtensionCutoff {d : ℕ} (x : SpatialCoordinates d) : ℝ :=
  min 1 (max 0 (2 - 2 * ‖x‖))

theorem cubeExtensionCutoff_nonneg {d : ℕ} (x : SpatialCoordinates d) :
    0 ≤ cubeExtensionCutoff x := by
  exact le_min zero_le_one (le_max_left _ _)

theorem cubeExtensionCutoff_le_one {d : ℕ} (x : SpatialCoordinates d) :
    cubeExtensionCutoff x ≤ 1 := min_le_left _ _

theorem cubeExtensionCutoff_eq_one {d : ℕ} {x : SpatialCoordinates d} (hx : ‖x‖ ≤ 1 / 2) :
    cubeExtensionCutoff x = 1 := by
  unfold cubeExtensionCutoff
  rw [min_eq_left]
  exact le_trans (by linarith : 1 ≤ 2 - 2 * ‖x‖) (le_max_right _ _)

theorem cubeExtensionCutoff_eq_zero {d : ℕ} {x : SpatialCoordinates d} (hx : 1 ≤ ‖x‖) :
    cubeExtensionCutoff x = 0 := by
  unfold cubeExtensionCutoff
  rw [max_eq_left (by linarith : 2 - 2 * ‖x‖ ≤ 0)]
  norm_num

theorem cubeExtensionCutoff_lipschitz {d : ℕ} :
    LipschitzWith 2 (cubeExtensionCutoff (d := d)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |cubeExtensionCutoff x - cubeExtensionCutoff y| ≤ 2 * dist x y
  have h1 := abs_min_sub_min_le_max (1 : ℝ) (max 0 (2 - 2 * ‖x‖))
    1 (max 0 (2 - 2 * ‖y‖))
  have h2 := abs_max_sub_max_le_max (0 : ℝ) (2 - 2 * ‖x‖)
    0 (2 - 2 * ‖y‖)
  simp only [sub_self, abs_zero] at h1 h2
  rw [show max 0 |max 0 (2 - 2 * ‖x‖) - max 0 (2 - 2 * ‖y‖)| =
    |max 0 (2 - 2 * ‖x‖) - max 0 (2 - 2 * ‖y‖)| from max_eq_right (abs_nonneg _)] at h1
  rw [show max 0 |(2 - 2 * ‖x‖) - (2 - 2 * ‖y‖)| =
    |(2 - 2 * ‖x‖) - (2 - 2 * ‖y‖)| from max_eq_right (abs_nonneg _)] at h2
  calc
    _ ≤ |(2 - 2 * ‖x‖) - (2 - 2 * ‖y‖)| := h1.trans h2
    _ = 2 * |‖x‖ - ‖y‖| := by
      rw [show (2 - 2 * ‖x‖) - (2 - 2 * ‖y‖) = -2 * (‖x‖ - ‖y‖) by ring, abs_mul]
      norm_num
    _ ≤ 2 * dist x y := by
      rw [dist_eq_norm]
      exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (by norm_num)

/-- A radial integrable majorant for the error made by a Lipschitz cutoff. -/
def fractionalCutoffKernel {d : ℕ} (s : ℝ) (x : SpatialCoordinates d) : ℝ≥0∞ :=
  ENNReal.ofReal (if ‖x‖ ≤ 1 then 4 * ‖x‖ ^ (2 - ((d : ℝ) + 2 * s))
    else ‖x‖ ^ (-((d : ℝ) + 2 * s)))

def fractionalCutoffKernelMass (d : ℕ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : SpatialCoordinates d, fractionalCutoffKernel s x

theorem measurable_fractionalCutoffKernel {d : ℕ} (s : ℝ) :
    Measurable (fractionalCutoffKernel (d := d) s) := by
  unfold fractionalCutoffKernel
  apply Measurable.ennreal_ofReal
  exact Measurable.ite (measurableSet_le continuous_norm.measurable measurable_const)
    (measurable_const.mul (continuous_norm.measurable.pow_const _))
    (continuous_norm.measurable.pow_const _)

theorem fractionalCutoffKernelMass_ne_top {d : ℕ} (hd : 0 < d)
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) : fractionalCutoffKernelMass d s ≠ ⊤ := by
  letI : Inhabited (Fin d) := ⟨⟨0, hd⟩⟩
  letI : Nontrivial (SpatialCoordinates d) := Pi.nontrivial
  let p : ℝ := (d : ℝ) + 2 * s
  let k : ℝ → ℝ := fun y => if y ≤ 1 then 4 * y ^ (2 - p) else y ^ (-p)
  have hint : Integrable (fun x : SpatialCoordinates d => k ‖x‖) volume := by
    apply (integrable_fun_norm_addHaar volume (f := k)).mpr
    simp only [Module.finrank_fin_fun, smul_eq_mul]
    have hnear : IntegrableOn (fun y : ℝ => y ^ (d - 1) * k y) (Ioc 0 1) := by
      have hp : -1 < 1 - 2 * s := by linarith
      have hi : IntegrableOn (fun y : ℝ => y ^ (1 - 2 * s)) (Ioc 0 1) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
          (intervalIntegral.intervalIntegrable_rpow' hp)
      apply IntegrableOn.congr_fun (hi.const_mul 4) _ measurableSet_Ioc
      intro y hy
      dsimp only [k]
      rw [if_pos hy.2, mul_left_comm, ← Real.rpow_natCast, ← Real.rpow_add hy.1]
      congr 2
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      dsimp [p]
      ring
    have hfar : IntegrableOn (fun y : ℝ => y ^ (d - 1) * k y) (Ioi 1) := by
      apply (integrableOn_Ioi_rpow_of_lt (a := -1 - 2 * s) (by linarith) one_pos).congr_fun
        _ measurableSet_Ioi
      intro y hy
      have hypos : 0 < y := zero_lt_one.trans hy
      dsimp only [k]
      rw [if_neg (not_le.mpr hy), ← Real.rpow_natCast, ← Real.rpow_add hypos]
      congr 1
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      dsimp [p]
      ring
    have hcover : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
      ext y
      simp only [mem_Ioi, mem_union, mem_Ioc]
      constructor
      · intro hy
        rcases le_or_gt y 1 with h | h
        · exact Or.inl ⟨hy, h⟩
        · exact Or.inr h
      · rintro (h | h)
        · exact h.1
        · exact zero_lt_one.trans h
    rw [hcover]
    exact hnear.union hfar
  have hpos (x : SpatialCoordinates d) : 0 ≤ k ‖x‖ := by
    dsimp [k]
    split_ifs <;> positivity
  have hbridge := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hpos)
  unfold fractionalCutoffKernelMass fractionalCutoffKernel
  rw [← hbridge]
  exact ENNReal.ofReal_ne_top

theorem fractionalCutoffKernel_sub_rev {d : ℕ} (s : ℝ) (x y : SpatialCoordinates d) :
    fractionalCutoffKernel s (x - y) = fractionalCutoffKernel s (y - x) := by
  unfold fractionalCutoffKernel
  rw [norm_sub_rev]

theorem lintegral_fractionalCutoffKernel_sub {d : ℕ} (s : ℝ) (x : SpatialCoordinates d) :
    (∫⁻ y : SpatialCoordinates d, fractionalCutoffKernel s (x - y)) = fractionalCutoffKernelMass d s := by
  exact (Measure.measurePreserving_sub_left volume x).lintegral_comp
    (measurable_fractionalCutoffKernel s)

/-- The squared difference of the cutoff absorbs the kernel singularity. -/
theorem cubeExtensionCutoff_kernel_le {d : ℕ} (s : ℝ) (hs : 0 ≤ s)
    (x y : SpatialCoordinates d) :
    ENNReal.ofReal ((cubeExtensionCutoff x - cubeExtensionCutoff y) ^ 2) /
      ENNReal.ofReal (euclideanDist x y) ^ ((d : ℝ) + 2 * s) ≤
        fractionalCutoffKernel s (x - y) := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero,
      ENNReal.zero_div, zero_le]
  have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  let p : ℝ := (d : ℝ) + 2 * s
  have hpn : 0 ≤ p := by dsimp [p]; positivity
  have hmono : ENNReal.ofReal ((cubeExtensionCutoff x - cubeExtensionCutoff y) ^ 2) /
      ENNReal.ofReal (euclideanDist x y) ^ p ≤
        ENNReal.ofReal ((cubeExtensionCutoff x - cubeExtensionCutoff y) ^ 2) /
          ENNReal.ofReal ‖x - y‖ ^ p :=
    ENNReal.div_le_div_left (ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (norm_le_euclideanNorm (x - y))) hpn) _
  apply hmono.trans
  have hn0 : ENNReal.ofReal ‖x - y‖ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hn
  by_cases hnear : ‖x - y‖ ≤ 1
  · have hlip := (cubeExtensionCutoff_lipschitz (d := d)).dist_le_mul x y
    simp only [NNReal.coe_ofNat, dist_eq_norm, Real.norm_eq_abs] at hlip
    have hnum : (cubeExtensionCutoff x - cubeExtensionCutoff y) ^ 2 ≤ 4 * ‖x - y‖ ^ 2 := by
      have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * ‖x - y‖)).mpr hlip
      simpa only [sq_abs, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh
    calc
      _ ≤ ENNReal.ofReal (4 * ‖x - y‖ ^ 2) / ENNReal.ofReal ‖x - y‖ ^ p :=
        ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hnum) _
      _ = fractionalCutoffKernel s (x - y) := by
        unfold fractionalCutoffKernel
        rw [if_pos hnear, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
          ENNReal.ofReal_pow (norm_nonneg _), div_eq_mul_inv, ← ENNReal.rpow_neg,
          ← ENNReal.rpow_natCast, mul_assoc]
        norm_num only [Nat.cast_ofNat]
        rw [← ENNReal.rpow_add (2 : ℝ) (-p) hn0 ENNReal.ofReal_ne_top,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        congr 1
        exact ENNReal.ofReal_rpow_of_pos hn
  · have habs : |cubeExtensionCutoff x - cubeExtensionCutoff y| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith [cubeExtensionCutoff_nonneg x, cubeExtensionCutoff_le_one x,
        cubeExtensionCutoff_nonneg y, cubeExtensionCutoff_le_one y]
    have hnum : (cubeExtensionCutoff x - cubeExtensionCutoff y) ^ 2 ≤ 1 := by
      have hh := (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr habs
      simpa only [sq_abs, one_pow] using hh
    calc
      _ ≤ 1 / ENNReal.ofReal ‖x - y‖ ^ p := by
        apply ENNReal.div_le_div_right
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hnum
      _ = fractionalCutoffKernel s (x - y) := by
        unfold fractionalCutoffKernel
        rw [if_neg hnear, one_div, ← ENNReal.rpow_neg]
        exact ENNReal.ofReal_rpow_of_pos hn

end SubdiffusiveProcess
