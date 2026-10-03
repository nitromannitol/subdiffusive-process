module

public import SubdiffusiveProcess.Section10.SmallDisplacementGeometry
public import SubdiffusiveProcess.Section10.ExitMomentPassage

@[expose] public section

open Filter MeasureTheory ProbabilityTheory MarkovProcess Set Topology SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.SmallDisplacement
open EndpointPaths

/-- Radius/cube-loss constant, independent of time, radius, scale and cutoff. -/
def displacementConstant (Cp p eta : ℝ) : ℝ :=
  max 1 Cp * (12 : ℝ) ^ (p * (2 + eta))

lemma displacementConstant_pos (Cp p eta : ℝ) : 0 < displacementConstant Cp p eta :=
  mul_pos (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
    (Real.rpow_pos_of_pos (by norm_num) _)

/-- Markov's inequality for a powered literal cube exit. -/
lemma small_displacement_at_scale {d : ℕ} (P : Measure (DiffusionPath d))
    (p eta Cp : ℝ) (hp : 0 < p) (k : ℕ) (t : ℝ≥0) (ht : 0 < t)
    (r : ℝ) (hr : 0 < r) (hscale : 4 * r ≤ (3 : ℝ) ^ (-(k : ℤ)))
    (hmoment : (∫⁻ w, smallExit k w ^ p ∂P) ≤
      ENNReal.ofReal (Cp * (3 : ℝ) ^ (-(p * (2 + eta) * k)))) :
    P {w | maximum t w ≤ r} ≤
      ENNReal.ofReal (Cp * (t : ℝ) ^ (-p) * ((3 : ℝ) ^ (-(k : ℤ))) ^ (p * (2 + eta))) := by
  have hpow : (t : ℝ≥0∞) ^ p ≠ 0 :=
    (ENNReal.rpow_pos (by exact_mod_cast ht) ENNReal.coe_ne_top).ne'
  have hmark := meas_ge_le_lintegral_div (μ := P) (f := fun w => smallExit k w ^ p)
    (ExitMomentPassage.smallExit_rpow_lsc k p hp).measurable.aemeasurable
    hpow (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.coe_ne_top)
  have hinc : {w : DiffusionPath d | maximum t w ≤ r} ⊆
      {w | (t : ℝ≥0∞) ^ p ≤ smallExit k w ^ p} := by
    intro w hw
    exact ENNReal.rpow_le_rpow (smallExit_gt_of_maximum_le w t k r hr hscale hw).le hp.le
  calc P {w | maximum t w ≤ r} ≤ P {w | (t : ℝ≥0∞) ^ p ≤ smallExit k w ^ p} :=
        measure_mono hinc
    _ ≤ (∫⁻ w, smallExit k w ^ p ∂P) / (t : ℝ≥0∞) ^ p := hmark
    _ ≤ ENNReal.ofReal (Cp * (3 : ℝ) ^ (-(p * (2 + eta) * k))) /
        (t : ℝ≥0∞) ^ p := ENNReal.div_le_div_right hmoment _
    _ = _ := by
      have htp : (t : ℝ≥0∞) ^ p = ENNReal.ofReal ((t : ℝ) ^ p) := by
        calc (t : ℝ≥0∞) ^ p = ENNReal.ofReal (t : ℝ) ^ p := by rw [ENNReal.coe_nnreal_eq]
          _ = _ := ENNReal.ofReal_rpow_of_nonneg t.property hp.le
      rw [htp,
        ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos (by exact_mod_cast ht) _)]
      congr 1
      have hrad := rpow_radius (p * (2 + eta) - 2) k
      rw [show 2 + (p * (2 + eta) - 2) = p * (2 + eta) by ring] at hrad
      rw [← hrad, Real.rpow_neg (x := (t : ℝ)) (y := p) t.property]
      ring

/-- All source radii 0 < r ≤ 1; r > 1/12 uses probability at most one. -/
theorem small_displacement_of_exit_moments {d : ℕ} (P : Measure (DiffusionPath d))
    [IsProbabilityMeasure P] (Cp p eta : ℝ) (hp : 0 < p) (heta : 0 < eta)
    (hmoment : ∀ k : ℕ, (∫⁻ w, smallExit k w ^ p ∂P) ≤
      ENNReal.ofReal (Cp * (3 : ℝ) ^ (-(p * (2 + eta) * k))))
    (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1) (r : ℝ) (hr : 0 < r) (_hr1 : r ≤ 1) :
    P {w | maximum t w ≤ r} ≤
      ENNReal.ofReal (displacementConstant Cp p eta * (t : ℝ) ^ (-p) * r ^ (p * (2 + eta))) := by
  have hA : 0 < p * (2 + eta) := mul_pos hp (by linarith)
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast ht
  have htR : (t : ℝ) ≤ 1 := by exact_mod_cast ht1
  have hCp : 0 ≤ max 1 Cp := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  by_cases hrs : r ≤ 1 / 12
  · obtain ⟨k, hklo, hkhi⟩ := exists_small_displacement_scale r hr hrs
    apply (small_displacement_at_scale P p eta Cp hp k t ht r hr hklo (hmoment k)).trans
    apply ENNReal.ofReal_le_ofReal
    have hrad := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (-(k : ℤ))) hkhi.le hA.le
    have hC := mul_le_mul_of_nonneg_right (le_max_right 1 Cp)
      (mul_nonneg (Real.rpow_nonneg t.property (-p)) (by positivity : (0 : ℝ) ≤ ((3 : ℝ) ^ (-(k : ℤ))) ^ (p * (2 + eta))))
    calc Cp * (t : ℝ) ^ (-p) * ((3 : ℝ) ^ (-(k : ℤ))) ^ (p * (2 + eta))
        ≤ max 1 Cp * (t : ℝ) ^ (-p) * ((3 : ℝ) ^ (-(k : ℤ))) ^ (p * (2 + eta)) := by
          simpa only [mul_assoc] using! hC
      _ ≤ max 1 Cp * (t : ℝ) ^ (-p) * (12 * r) ^ (p * (2 + eta)) :=
          mul_le_mul_of_nonneg_left hrad (mul_nonneg hCp (by positivity))
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 12) hr.le]; unfold displacementConstant; ring
  · apply prob_le_one.trans
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have htime : 1 ≤ (t : ℝ) ^ (-p) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 htR (by linarith)
    have hrad : 1 ≤ (12 * r) ^ (p * (2 + eta)) :=
      Real.one_le_rpow (by linarith) hA.le
    have h : (1 : ℝ) ≤ max 1 Cp * (t : ℝ) ^ (-p) * (12 * r) ^ (p * (2 + eta)) := by
      calc (1 : ℝ) ≤ max 1 Cp * (t : ℝ) ^ (-p) := by
            simpa only [one_mul] using mul_le_mul (le_max_left 1 Cp) htime (by norm_num : (0 : ℝ) ≤ 1) hCp
        _ = max 1 Cp * (t : ℝ) ^ (-p) * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hrad (mul_nonneg hCp (Real.rpow_nonneg t.property (-p)))
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 12) hr.le] at h
    unfold displacementConstant
    nlinarith only [h]

/-- The paper's scaled small-displacement estimate, at every 0<t,epsilon≤1. -/
theorem scaled_small_displacement {d : ℕ} (P : Measure (DiffusionPath d))
    [IsProbabilityMeasure P] (Cp p eta : ℝ) (hp : 0 < p) (heta : 0 < eta)
    (hmoment : ∀ k : ℕ, (∫⁻ w, smallExit k w ^ p ∂P) ≤
      ENNReal.ofReal (Cp * (3 : ℝ) ^ (-(p * (2 + eta) * k))))
    (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1) (epsilon : ℝ)
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1) :
    P {w | maximum t w ≤ epsilon * (t : ℝ) ^ (1 / (2 + eta))} ≤
      ENNReal.ofReal (displacementConstant Cp p eta * epsilon ^ (p * (2 + eta))) := by
  have ha : 0 < 2 + eta := by linarith
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast ht
  have hr := mul_pos heps (Real.rpow_pos_of_pos ht0 (1 / (2 + eta)))
  have hr1 : epsilon * (t : ℝ) ^ (1 / (2 + eta)) ≤ 1 :=
    mul_le_one₀ heps1 (Real.rpow_nonneg t.property _)
      (Real.rpow_le_one t.property (by exact_mod_cast ht1) (one_div_pos.mpr ha).le)
  have h := small_displacement_of_exit_moments P Cp p eta hp heta hmoment t ht ht1 _ hr hr1
  have heq : displacementConstant Cp p eta * (t : ℝ) ^ (-p) *
      (epsilon * (t : ℝ) ^ (1 / (2 + eta))) ^ (p * (2 + eta)) =
      displacementConstant Cp p eta * epsilon ^ (p * (2 + eta)) := by
    rw [Real.mul_rpow (x := epsilon) (y := (t : ℝ) ^ (1 / (2 + eta))) heps.le (Real.rpow_nonneg t.property _), ← Real.rpow_mul (x := (t : ℝ)) t.property (1 / (2 + eta)) (p * (2 + eta)),
      show 1 / (2 + eta) * (p * (2 + eta)) = p by field_simp [ha.ne']]
    rw [← mul_assoc, mul_assoc (displacementConstant Cp p eta),
      mul_comm ((t : ℝ) ^ (-p)) (epsilon ^ (p * (2 + eta))), ← mul_assoc,
      mul_assoc (displacementConstant Cp p eta * epsilon ^ (p * (2 + eta))),
      ← Real.rpow_add ht0, neg_add_cancel, Real.rpow_zero, mul_one]
  rwa [heq] at h

end SubdiffusiveProcess.Section10.SmallDisplacement
