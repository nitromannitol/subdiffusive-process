module

public import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSeries

@[expose] public section

/-!
# The own-scale `(g2)` gauge of a single shell

Deterministic input for the anchored Borel–Cantelli.  Shell `k` of a sample is
`ω k = g (3⁻ᵏ ·)` in law, so on a fixed ball its anchored value, its gradient,
and its gradient Lipschitz seminorm are all controlled by `3⁻ᵏ` times the
`(g2)` observable of the reverse-scaled shell, with an extra `3⁻ᵏ` on the
Lipschitz seminorm.

The gauge itself is `ShellSensitivity.translatedShellG2 k 0`, whose `Γ₂` tail
at scale `(1 + log 2)^{1/2} δ` is `isBigOWith_gammaTwo_translatedShellG2`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open Homogenization Homogenization.IndependentSums MeasureTheory
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## The derivative of a spatially rescaled potential -/

/-- The chain rule for the spatial scaling action, in the exact form stored in
the carrier. -/
theorem deriv_spatialScale (r : ℝ) (g : PotentialField d) (x : Vec d) :
    PotentialField.deriv (PotentialField.spatialScale r g) x =
      r • PotentialField.deriv g (r • x) := by
  have hcomp : HasFDerivAt (fun y : Vec d => g (r • y))
      (r • PotentialField.deriv g (r • x)) x := by
    have h := (g.hasFDerivAt (r • x)).comp x ((hasFDerivAt_id x).const_smul r)
    simpa only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id,
      Function.comp_def] using h
  have hstored : HasFDerivAt (fun y : Vec d => g (r • y))
      (PotentialField.deriv (PotentialField.spatialScale r g) x) x := by
    simpa only [PotentialField.spatialScale_apply] using!
      (PotentialField.spatialScale r g).hasFDerivAt x
  exact hstored.unique hcomp

/-- The derivative of the reverse-scaled shell, read back at the original
point. -/
theorem deriv_unscalePotential (k : ℕ) (g : PotentialField d) (x : Vec d) :
    PotentialField.deriv (unscalePotential k g) (((3 : ℝ) ^ k)⁻¹ • x) =
      (3 : ℝ) ^ k • PotentialField.deriv g x := by
  have h3 : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  rw [unscalePotential, deriv_spatialScale, smul_smul, mul_inv_cancel₀ h3, one_smul]

/-- The shell derivative in terms of the reverse-scaled shell. -/
theorem deriv_eq_smul_deriv_unscalePotential (k : ℕ) (g : PotentialField d)
    (x : Vec d) :
    PotentialField.deriv g x =
      (((3 : ℝ) ^ k)⁻¹) •
        PotentialField.deriv (unscalePotential k g) ((((3 : ℝ) ^ k)⁻¹) • x) := by
  have h3 : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  rw [deriv_unscalePotential, smul_smul, inv_mul_cancel₀ h3, one_smul]

/-! ## The own-scale gauge -/

/-- The `(g2)` observable of the reverse-scaled shell `k`. -/
def shellUnitGauge (k : ℕ) (omega : PotentialSample d) : ℝ :=
  PotentialField.g2Observable (unscalePotential k (omega k))

theorem shellUnitGauge_eq_translatedShellG2 (k : ℕ) (omega : PotentialSample d) :
    shellUnitGauge k omega = translatedShellG2 k 0 omega := by
  have hzero : PotentialField.translate (0 : Vec d)
      (unscalePotential k (omega k)) = unscalePotential k (omega k) := by
    apply PotentialField.ext
    intro z
    simp
  rw [shellUnitGauge, translatedShellG2, hzero]

theorem shellUnitGauge_nonneg (k : ℕ) (omega : PotentialSample d) :
    0 ≤ shellUnitGauge k omega :=
  PotentialField.g2Observable_nonneg _

theorem measurable_shellUnitGauge (k : ℕ) :
    Measurable (shellUnitGauge (d := d) k) := by
  simpa only [funext fun omega => shellUnitGauge_eq_translatedShellG2 k omega] using
    measurable_translatedShellG2 (d := d) k 0

/-- The `Γ₂` tail of the own-scale gauge, uniformly in the shell index. -/
theorem isBigOWith_gammaTwo_shellUnitGauge (M : GMCModel d) (k : ℕ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (shellUnitGauge (d := d) k)
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
  simpa only [funext fun omega => shellUnitGauge_eq_translatedShellG2 k omega] using
    isBigOWith_gammaTwo_translatedShellG2 M k 0

/-! ## The scaled ball sits in the unit cube -/

/-- If `2R < 3ᵏ` then the whole ball of radius `R`, rescaled by `3⁻ᵏ`, sits in
the open unit cube. -/
theorem smul_mem_unitCube_of_mem_closedBall {k : ℕ} {R : ℝ}
    (hk : 2 * R < (3 : ℝ) ^ k) {x : Vec d}
    (hx : x ∈ Metric.closedBall (0 : Vec d) R) :
    (((3 : ℝ) ^ k)⁻¹) • x ∈ openCubeSet (originCube d 0) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hxi : |x i| ≤ R := (norm_le_pi_norm x i).trans hx
  have hxi' := abs_le.mp hxi
  simp only [Pi.smul_apply, smul_eq_mul, zpow_zero, mul_one]
  constructor
  · rw [← div_eq_inv_mul, lt_div_iff₀ h3]
    nlinarith [hxi'.1]
  · rw [← div_eq_inv_mul, div_lt_iff₀ h3]
    nlinarith [hxi'.2]

/-- Some shell index puts the whole ball inside the unit cube, and every later
one does as well. -/
theorem exists_shellStart (R : ℝ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 2 * R < (3 : ℝ) ^ k := by
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (2 * R) (by norm_num : (1 : ℝ) < 3)
  refine ⟨K, fun k hk => hK.trans_le ?_⟩
  exact pow_le_pow_right₀ (by norm_num) hk

/-! ## The three shell estimates above the start index -/

variable {omega : PotentialSample d}

/-- Gradient bound: `3⁻ᵏ` times the own-scale gauge. -/
theorem norm_deriv_le_shellUnitGauge {k : ℕ} {R : ℝ}
    (hk : 2 * R < (3 : ℝ) ^ k) {x : Vec d}
    (hx : x ∈ Metric.closedBall (0 : Vec d) R) :
    ‖PotentialField.deriv (omega k) x‖ ≤
      (((3 : ℝ) ^ k)⁻¹) * shellUnitGauge k omega := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hmem := smul_mem_unitCube_of_mem_closedBall (d := d) hk hx
  have hbound := PotentialField.norm_deriv_le_g2Observable
    (unscalePotential k (omega k)) hmem
  rw [deriv_eq_smul_deriv_unscalePotential k (omega k) x, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < ((3 : ℝ) ^ k)⁻¹)]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-- Gradient Lipschitz bound: `3⁻²ᵏ` times the own-scale gauge. -/
theorem norm_deriv_sub_deriv_le_shellUnitGauge {k : ℕ} {R : ℝ}
    (hk : 2 * R < (3 : ℝ) ^ k) {x y : Vec d}
    (hx : x ∈ Metric.closedBall (0 : Vec d) R)
    (hy : y ∈ Metric.closedBall (0 : Vec d) R) :
    ‖PotentialField.deriv (omega k) x - PotentialField.deriv (omega k) y‖ ≤
      ((((3 : ℝ) ^ k)⁻¹) * ((((3 : ℝ) ^ k)⁻¹) * shellUnitGauge k omega)) *
        ‖x - y‖ := by
  have h3 : (0 : ℝ) < ((3 : ℝ) ^ k)⁻¹ := by positivity
  have hmx := smul_mem_unitCube_of_mem_closedBall (d := d) hk hx
  have hmy := smul_mem_unitCube_of_mem_closedBall (d := d) hk hy
  have hbound := PotentialField.norm_deriv_sub_deriv_le_g2Observable_mul
    (unscalePotential k (omega k)) hmx hmy
  have hscaled : ‖(((3 : ℝ) ^ k)⁻¹) • x - (((3 : ℝ) ^ k)⁻¹) • y‖ =
      (((3 : ℝ) ^ k)⁻¹) * ‖x - y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos h3]
  rw [hscaled] at hbound
  have hkey : PotentialField.deriv (omega k) x - PotentialField.deriv (omega k) y =
      (((3 : ℝ) ^ k)⁻¹) •
        (PotentialField.deriv (unscalePotential k (omega k))
            ((((3 : ℝ) ^ k)⁻¹) • x) -
          PotentialField.deriv (unscalePotential k (omega k))
            ((((3 : ℝ) ^ k)⁻¹) • y)) := by
    rw [smul_sub, ← deriv_eq_smul_deriv_unscalePotential k (omega k) x,
      ← deriv_eq_smul_deriv_unscalePotential k (omega k) y]
  rw [hkey, norm_smul, Real.norm_eq_abs, abs_of_pos h3]
  calc
    (((3 : ℝ) ^ k)⁻¹) *
        ‖PotentialField.deriv (unscalePotential k (omega k))
            ((((3 : ℝ) ^ k)⁻¹) • x) -
          PotentialField.deriv (unscalePotential k (omega k))
            ((((3 : ℝ) ^ k)⁻¹) • y)‖ ≤
        (((3 : ℝ) ^ k)⁻¹) *
          (PotentialField.g2Observable (unscalePotential k (omega k)) *
            ((((3 : ℝ) ^ k)⁻¹) * ‖x - y‖)) :=
      mul_le_mul_of_nonneg_left hbound h3.le
    _ = ((((3 : ℝ) ^ k)⁻¹) * ((((3 : ℝ) ^ k)⁻¹) * shellUnitGauge k omega)) *
        ‖x - y‖ := by
      rw [shellUnitGauge]; ring

/-- Anchored value bound on the ball: the mean value inequality applied to the
gradient bound. -/
theorem abs_sub_origin_le_shellUnitGauge {k : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hk : 2 * R < (3 : ℝ) ^ k) {x : Vec d}
    (hx : x ∈ Metric.closedBall (0 : Vec d) R) :
    |omega k x - omega k 0| ≤ R * ((((3 : ℝ) ^ k)⁻¹) * shellUnitGauge k omega) := by
  have hconv : Convex ℝ (Metric.closedBall (0 : Vec d) R) := convex_closedBall _ _
  have hzero : (0 : Vec d) ∈ Metric.closedBall (0 : Vec d) R := by
    simpa using hR
  have hmean := hconv.norm_image_sub_le_of_norm_fderiv_le
    (f := fun z : Vec d => omega k z)
    (fun z _ => ((omega k).hasFDerivAt z).differentiableAt)
    (fun z hz => by
      rw [((omega k).hasFDerivAt z).fderiv]
      exact norm_deriv_le_shellUnitGauge hk hz)
    hzero hx
  rw [Real.norm_eq_abs] at hmean
  have hxnorm : ‖x - (0 : Vec d)‖ ≤ R := by
    simpa using hx
  have hC : 0 ≤ (((3 : ℝ) ^ k)⁻¹) * shellUnitGauge k omega :=
    mul_nonneg (by positivity) (shellUnitGauge_nonneg k omega)
  refine hmean.trans ?_
  rw [mul_comm R]
  exact mul_le_mul_of_nonneg_left hxnorm hC

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
