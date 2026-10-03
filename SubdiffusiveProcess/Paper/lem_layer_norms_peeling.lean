module

public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Paper



theorem lem_layer_norms_peeling :
    ∀ (Cc : ℝ), 1 ≤ Cc →
    ∀ (Om : Type) [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P],
    ∀ disorder : ℝ, 0 < disorder → disorder ≤ 1 →
    ∀ S : ℕ → Om → ℝ,
    (∀ j, AEStronglyMeasurable (S j) P) →
    (∀ j omega, 0 ≤ S j omega) →
    ∀ covers : ℕ → ℝ,
    (∀ j, 1 ≤ covers j) →
    (∀ (j : ℕ) (s : ℝ), 0 ≤ s →
      P {omega | s < S j omega} ≤
        ENNReal.ofReal (2 * covers j * Real.exp (-(s ^ 2 / (Cc * disorder ^ 2))))) →
    ∀ j : ℕ,
      let a := disorder * Real.sqrt (Cc * Real.log (2 * covers j))
      let X := fun omega => max (S j omega - a) 0
      (∀ omega, 0 ≤ X omega ∧ S j omega ≤ a + X omega) ∧
      (∀ s : ℝ, 0 ≤ s → P {omega | s < X omega} ≤
        ENNReal.ofReal (Real.exp (-(s ^ 2 / (Cc * disorder ^ 2))))) := by
  intro Cc hCc Om instMeas P instProb disorder hdis hdis_le S hS_meas
    hS_nonneg covers hcov hreg j
  let a : ℝ := disorder * Real.sqrt (Cc * Real.log (2 * covers j))
  let X : Om → ℝ := fun omega => max (S j omega - a) 0
  change (∀ omega : Om, 0 ≤ X omega ∧ S j omega ≤ a + X omega) ∧
    (∀ s : ℝ, 0 ≤ s → P {omega | s < X omega} ≤
      ENNReal.ofReal (Real.exp (-(s ^ 2 / (Cc * disorder ^ 2)))))
  have hCcpos : 0 < Cc := lt_of_lt_of_le zero_lt_one hCc
  have hDpos : 0 < Cc * disorder ^ 2 :=
    mul_pos hCcpos (sq_pos_of_pos hdis)
  have hDne : Cc * disorder ^ 2 ≠ 0 := ne_of_gt hDpos
  have hlog : 0 ≤ Real.log (2 * covers j) := by
    apply Real.log_nonneg
    nlinarith [hcov j]
  have hClog : 0 ≤ Cc * Real.log (2 * covers j) :=
    mul_nonneg (le_of_lt hCcpos) hlog
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (le_of_lt hdis) (Real.sqrt_nonneg _)
  have ha_sq : a ^ 2 = (Cc * disorder ^ 2) * Real.log (2 * covers j) := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt hClog]
    ring
  have ha_div : a ^ 2 / (Cc * disorder ^ 2) = Real.log (2 * covers j) := by
    rw [ha_sq, mul_div_cancel_left₀ _ hDne]
  have hexp_a : Real.exp (a ^ 2 / (Cc * disorder ^ 2)) = 2 * covers j := by
    rw [ha_div]
    exact Real.exp_log (by nlinarith [hcov j])
  constructor
  · intro omega
    constructor
    · exact le_max_right _ _
    · dsimp [X]
      have hmax : S j omega - a ≤ max (S j omega - a) 0 :=
        le_max_left _ _
      linarith
  · intro s hs
    have hsub : {omega | s < X omega} ⊆ {omega | s + a < S j omega} := by
      intro omega h
      change s < max (S j omega - a) 0 at h
      change s + a < S j omega
      rcases lt_max_iff.mp h with hleft | hright
      · linarith
      · linarith
    have hcross : 1 ≤ Real.exp (2 * s * a / (Cc * disorder ^ 2)) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) ha_nonneg)
        (le_of_lt hDpos)
    have hkey : 2 * covers j ≤
        Real.exp (((s + a) ^ 2 - s ^ 2) / (Cc * disorder ^ 2)) := by
      calc
        2 * covers j = 1 * (2 * covers j) := by ring
        _ = 1 * Real.exp (a ^ 2 / (Cc * disorder ^ 2)) := by rw [hexp_a]
        _ ≤ Real.exp (2 * s * a / (Cc * disorder ^ 2)) *
            Real.exp (a ^ 2 / (Cc * disorder ^ 2)) :=
          mul_le_mul_of_nonneg_right hcross (Real.exp_nonneg _)
        _ = Real.exp (((s + a) ^ 2 - s ^ 2) / (Cc * disorder ^ 2)) := by
          rw [← Real.exp_add]
          congr 1
          ring
    have hsplit : Real.exp (-(s ^ 2 / (Cc * disorder ^ 2))) =
        Real.exp (-((s + a) ^ 2 / (Cc * disorder ^ 2))) *
          Real.exp (((s + a) ^ 2 - s ^ 2) / (Cc * disorder ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hfinal : 2 * covers j *
          Real.exp (-((s + a) ^ 2 / (Cc * disorder ^ 2))) ≤
        Real.exp (-(s ^ 2 / (Cc * disorder ^ 2))) := by
      rw [hsplit]
      calc
        2 * covers j *
            Real.exp (-((s + a) ^ 2 / (Cc * disorder ^ 2))) =
            Real.exp (-((s + a) ^ 2 / (Cc * disorder ^ 2))) *
              (2 * covers j) := by ring
        _ ≤ Real.exp (-((s + a) ^ 2 / (Cc * disorder ^ 2))) *
              Real.exp (((s + a) ^ 2 - s ^ 2) / (Cc * disorder ^ 2)) :=
          mul_le_mul_of_nonneg_left hkey (Real.exp_nonneg _)
    calc
      P {omega | s < X omega} ≤ P {omega | s + a < S j omega} :=
        measure_mono hsub
      _ ≤ ENNReal.ofReal (2 * covers j *
          Real.exp (-((s + a) ^ 2 / (Cc * disorder ^ 2)))) :=
        hreg j (s + a) (by linarith [ha_nonneg])
      _ ≤ ENNReal.ofReal (Real.exp (-(s ^ 2 / (Cc * disorder ^ 2)))) :=
        ENNReal.ofReal_le_ofReal hfinal

end Paper
