module

public import SubdiffusiveProcess.CoarseGrainingVocab.NormalizedL2Api

@[expose] public section

/-! # The average minimizes the normalized `L²` distance to constants

For a window `W` of finite volume and `f ∈ L²(W)`, the centered normalized `L²` seminorm
`‖f - ⨍_W f‖` is at most `‖f - c‖` for every constant `c`.  This file claims nothing
about oscillation of continuous representatives. -/

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section
namespace SubdiffusiveProcess

/-- The squared distance to a constant exceeds the squared distance to the average by
`(m - c)² |W|`, written as an inequality of integrals. -/
theorem integral_sq_sub_average_le_integral_sq_sub_const {d : ℕ}
    (W : Set (Homogenization.Vec d)) (hW : volume W ≠ ⊤)
    (f : Homogenization.Vec d → ℝ) (hf : MemLp f 2 (volume.restrict W)) (c : ℝ) :
    ∫ x in W, (f x - (volume.real W)⁻¹ * ∫ y in W, f y) ^ 2 ≤ ∫ x in W, (f x - c) ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.mpr hW
  set m : ℝ := (volume.real W)⁻¹ * ∫ y in W, f y with hm
  have hfi : Integrable f (volume.restrict W) := hf.integrable (by norm_num)
  have hf2 : Integrable (fun x => f x ^ 2) (volume.restrict W) := hf.integrable_sq
  have hsq : ∀ a : ℝ, Integrable (fun x => (f x - a) ^ 2) (volume.restrict W) := by
    intro a
    exact (hf.sub (memLp_const a)).integrable_sq
  have hdiff : (∫ x in W, (f x - c) ^ 2) - (∫ x in W, (f x - m) ^ 2) =
      (m - c) * (2 * (∫ x in W, f x) - (m + c) * volume.real W) := by
    rw [← integral_sub (hsq c) (hsq m)]
    have hpt : (fun x => (f x - c) ^ 2 - (f x - m) ^ 2) =
        fun x => (m - c) * (2 * f x - (m + c)) := by
      funext x; ring
    rw [hpt, integral_const_mul, integral_sub ((hfi.const_mul 2)) (integrable_const _),
      integral_const_mul, setIntegral_const, smul_eq_mul]
    ring
  by_cases hzero : volume.real W = 0
  · have hnull : volume W = 0 := by
      rw [Measure.real, ENNReal.toReal_eq_zero_iff] at hzero
      exact hzero.resolve_right hW
    rw [Measure.restrict_eq_zero.mpr hnull, integral_zero_measure, integral_zero_measure]
  · have hmean : ∫ x in W, f x = m * volume.real W := by
      rw [hm]; field_simp
    have hnonneg : 0 ≤ (m - c) * (2 * (∫ x in W, f x) - (m + c) * volume.real W) := by
      rw [hmean]
      have hv : 0 ≤ volume.real W := measureReal_nonneg
      have : (m - c) * (2 * (m * volume.real W) - (m + c) * volume.real W) =
          (m - c) ^ 2 * volume.real W := by ring
      rw [this]
      exact mul_nonneg (sq_nonneg _) hv
    linarith only [hdiff, hnonneg]

/-- The average minimizes the normalized `L²` distance to constants. -/
theorem normalizedL2On_sub_average_le_sub_const {d : ℕ}
    (W : Set (Homogenization.Vec d)) (hW : volume W ≠ ⊤)
    (f : Homogenization.Vec d → ℝ) (hf : MemLp f 2 (volume.restrict W)) (c : ℝ) :
    normalizedL2On W (fun x => f x - (volume.real W)⁻¹ * ∫ y in W, f y) ≤
      normalizedL2On W (fun x => f x - c) := by
  apply normalizedL2On_le_of_volumeAverage_le
  unfold Homogenization.volumeAverage
  exact mul_le_mul_of_nonneg_left
    (integral_sq_sub_average_le_integral_sq_sub_const W hW f hf c)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

end SubdiffusiveProcess
