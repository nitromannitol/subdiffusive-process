module

public import SubdiffusiveProcess.Analysis.RadialKernel
public import Homogenization.Ambient.Euclidean
public import Homogenization.Geometry.Translation
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

open MeasureTheory Filter Set Homogenization
open scoped ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-- A nonsingular radial majorant for the far part of a fractional kernel. -/
def cubeInterpolationKernel {d : ℕ} (t delta : ℝ) (x : SpatialCoordinates d) : ℝ≥0∞ :=
  ENNReal.ofReal (max delta ‖x‖) ^ (-((d : ℝ) + 2 * t))

/-- The finite mass at unit cutoff, used as an interpolation constant. -/
def cubeInterpolationKernelMass (d : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : SpatialCoordinates d, cubeInterpolationKernel t 1 x

theorem measurable_cubeInterpolationKernel {d : ℕ} (t delta : ℝ) :
    Measurable (cubeInterpolationKernel (d := d) t delta) := by
  unfold cubeInterpolationKernel
  fun_prop

theorem cubeInterpolationKernelMass_ne_top {d : ℕ} (hd : 0 < d) (t : ℝ) (ht : 0 < t) :
    cubeInterpolationKernelMass d t ≠ ⊤ := by
  let : Inhabited (Fin d) := ⟨⟨0, hd⟩⟩
  let : Nontrivial (SpatialCoordinates d) := Pi.nontrivial
  let p : ℝ := (d : ℝ) + 2 * t
  have hint : Integrable (fun x : SpatialCoordinates d => (max 1 ‖x‖) ^ (-p)) volume := by
    apply (integrable_fun_norm_addHaar volume (f := fun y : ℝ => (max 1 y) ^ (-p))).mpr
    simp only [Module.finrank_fin_fun, smul_eq_mul]
    have hleft : IntegrableOn (fun y : ℝ => y ^ (d - 1) * (max 1 y) ^ (-p)) (Ioc 0 1) := by
      apply ((continuous_pow (d - 1)).integrableOn_Ioc).congr_fun _ measurableSet_Ioc
      intro y hy
      dsimp only
      rw [max_eq_left hy.2, Real.one_rpow, mul_one]
    have hright : IntegrableOn (fun y : ℝ => y ^ (d - 1) * (max 1 y) ^ (-p)) (Ioi 1) := by
      apply (integrableOn_Ioi_rpow_of_lt (a := -1 - 2 * t) (by linarith) one_pos).congr_fun
        _ measurableSet_Ioi
      intro y hy
      have hyone : 1 < y := hy
      have hypos : 0 < y := zero_lt_one.trans hyone
      dsimp only
      rw [max_eq_right hyone.le, ← Real.rpow_natCast, ← Real.rpow_add hypos]
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
    exact hleft.union hright
  have hbridge := ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ (fun x => Real.rpow_nonneg (le_max_left (1 : ℝ) ‖x‖ |>.trans' zero_le_one) (-p)))
  unfold cubeInterpolationKernelMass
  have heq : (∫⁻ x : SpatialCoordinates d, cubeInterpolationKernel t 1 x) =
      ∫⁻ x : SpatialCoordinates d, ENNReal.ofReal ((max 1 ‖x‖) ^ (-p)) := by
    apply lintegral_congr
    intro x
    exact (ENNReal.ofReal_rpow_of_pos (zero_lt_one.trans_le (le_max_left 1 ‖x‖)))
  rw [heq, ← hbridge]
  exact ENNReal.ofReal_ne_top

theorem lintegral_cubeInterpolationKernel {d : ℕ} (t delta : ℝ) (hdelta : 0 < delta) :
    (∫⁻ x : SpatialCoordinates d, cubeInterpolationKernel t delta x) =
      ENNReal.ofReal delta ^ (-(2 * t)) * cubeInterpolationKernelMass d t := by
  have ha0 : ENNReal.ofReal delta ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hdelta
  have hpow0 : ENNReal.ofReal (delta ^ d) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hdelta d)
  have heq (x : SpatialCoordinates d) : cubeInterpolationKernel t delta (delta • x) =
      ENNReal.ofReal delta ^ (-((d : ℝ) + 2 * t)) * cubeInterpolationKernel t 1 x := by
    unfold cubeInterpolationKernel
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hdelta,
      ← show delta * max 1 ‖x‖ = max delta (delta * ‖x‖) from
        (mul_max_of_nonneg 1 ‖x‖ hdelta.le).trans (by rw [mul_one]),
      ENNReal.ofReal_mul hdelta.le]
    exact ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top _
  have hmap := lintegral_map (μ := (volume : Measure (SpatialCoordinates d))) (measurable_cubeInterpolationKernel (d := d) t delta)
    (measurable_const_smul delta : Measurable (fun x : SpatialCoordinates d => delta • x))
  rw [Measure.map_addHaar_smul volume hdelta.ne', Module.finrank_fin_fun,
    abs_of_pos (inv_pos.mpr (pow_pos hdelta d)), ENNReal.ofReal_inv_of_pos (pow_pos hdelta d),
    lintegral_smul_measure] at hmap
  have h := congrArg (fun a : ℝ≥0∞ => ENNReal.ofReal (delta ^ d) * a) hmap
  simp only [smul_eq_mul] at h
  rw [ENNReal.mul_inv_cancel_left hpow0 ENNReal.ofReal_ne_top] at h
  rw [lintegral_congr (fun x => heq x), lintegral_const_mul' _ _
    (ENNReal.rpow_ne_top_of_ne_zero ha0 ENNReal.ofReal_ne_top), ← mul_assoc,
    ENNReal.ofReal_pow hdelta.le, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_add (d : ℝ) (-((d : ℝ) + 2 * t)) ha0 ENNReal.ofReal_ne_top] at h
  convert h using 1
  congr 2
  ring

theorem lintegral_cubeInterpolationKernel_sub_le {d : ℕ} (t delta : ℝ)
    (hdelta : 0 < delta) (S : Set (SpatialCoordinates d)) (x : SpatialCoordinates d) :
    (∫⁻ y in S, cubeInterpolationKernel t delta (x - y)) ≤
      ENNReal.ofReal delta ^ (-(2 * t)) * cubeInterpolationKernelMass d t := by
  calc
    (∫⁻ y in S, cubeInterpolationKernel t delta (x - y)) ≤
        ∫⁻ y, cubeInterpolationKernel t delta (x - y) := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ y : SpatialCoordinates d, cubeInterpolationKernel t delta y :=
      (Measure.measurePreserving_sub_left volume x).lintegral_comp
        (measurable_cubeInterpolationKernel t delta)
    _ = _ := lintegral_cubeInterpolationKernel t delta hdelta

end SubdiffusiveProcess
