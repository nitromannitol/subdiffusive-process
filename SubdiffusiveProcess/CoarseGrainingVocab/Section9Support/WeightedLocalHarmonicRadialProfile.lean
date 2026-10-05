module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
@[expose] public section

/-! The fixed radial coefficient and its bounded reciprocal profile. -/

set_option autoImplicit false
open Homogenization MeasureTheory Set
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicRadial

def radialCoefficient (x : Vec 2) : ℝ := (max 1 (x 0)) ^ 2
def reciprocalProfile (x : Vec 2) : ℝ := (max 1 (x 0))⁻¹

theorem continuous_radialCoefficient : Continuous radialCoefficient := by
  unfold radialCoefficient
  exact (Continuous.max continuous_const (continuous_apply 0)).pow 2

theorem radialCoefficient_pos (x : Vec 2) : 0 < radialCoefficient x := by
  unfold radialCoefficient
  have h1 : (1 : ℝ) ≤ max 1 (x 0) := le_max_left _ _
  have h2 : (0 : ℝ) < max 1 (x 0) := zero_lt_one.trans_le h1
  exact pow_pos h2 2

theorem continuous_reciprocalProfile : Continuous reciprocalProfile := by
  unfold reciprocalProfile
  exact Continuous.inv₀ (Continuous.max continuous_const (continuous_apply 0))
    (fun x => ne_of_gt (zero_lt_one.trans_le (le_max_left 1 (x 0))))

theorem reciprocalProfile_bounds (x : Vec 2) :
    0 ≤ reciprocalProfile x ∧ reciprocalProfile x ≤ 1 := by
  unfold reciprocalProfile
  constructor
  · exact inv_nonneg.2 (le_trans (by norm_num) (le_max_left 1 (x 0)))
  · rcases le_or_gt (x 0) 1 with hle | hlt
    · rw [max_eq_left hle]
      norm_num
    · rw [max_eq_right (le_of_lt hlt)]
      have h2 : (0 : ℝ) < x 0 := by linarith
      simpa only [inv_one] using (inv_le_inv₀ h2 zero_lt_one).2 (le_of_lt hlt)

theorem reciprocalProfile_sq_slab_bound {T : ℝ} (hT : 1 ≤ T) (x : Vec 2) :
    reciprocalProfile x ^ 2 ≤ T⁻¹ ^ 2 +
      {y : Vec 2 | y 0 < T}.indicator (fun _ => (1 : ℝ)) x := by
  unfold reciprocalProfile
  by_cases h : x 0 < T
  · rw [Set.indicator_of_mem (show x ∈ {y : Vec 2 | y 0 < T} from h)]
    have hprof : (max 1 (x 0))⁻¹ ≤ 1 := by
      rcases le_or_gt (x 0) 1 with hle | hlt
      · rw [max_eq_left hle]; norm_num
      · rw [max_eq_right (le_of_lt hlt)]
        have h2 : (0 : ℝ) < x 0 := by linarith
        simpa only [inv_one] using (inv_le_inv₀ h2 zero_lt_one).2 (le_of_lt hlt)
    have hsq : (max 1 (x 0))⁻¹ ^ 2 ≤ 1 := by
      have h4 : (0 : ℝ) ≤ (max 1 (x 0))⁻¹ :=
        inv_nonneg.2 (le_trans (by norm_num) (le_max_left 1 (x 0)))
      nlinarith
    nlinarith [hsq, sq_nonneg (T⁻¹ : ℝ)]
  · rw [Set.indicator_of_notMem (show x ∉ {y : Vec 2 | y 0 < T} from h)]
    have hxT : (T : ℝ) ≤ x 0 := not_lt.1 h
    have hmaxT : (T : ℝ) ≤ max 1 (x 0) := le_trans hxT (le_max_right 1 (x 0))
    have h1 : (0 : ℝ) < max 1 (x 0) :=
      zero_lt_one.trans_le (le_max_left 1 (x 0))
    have h2 : (0 : ℝ) < T := zero_lt_one.trans_le hT
    have hinv : (max 1 (x 0))⁻¹ ≤ T⁻¹ := (inv_le_inv₀ h1 h2).2 hmaxT
    have h4 : (0 : ℝ) ≤ T⁻¹ := inv_nonneg.2 (zero_le_one.trans hT)
    have hsq : (max 1 (x 0))⁻¹ ^ 2 ≤ T⁻¹ ^ 2 :=
      (sq_le_sq₀ (inv_nonneg.2 (zero_le_one.trans (le_max_left 1 (x 0)))) h4).2 hinv
    exact le_trans hsq (by rw [add_zero])

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicRadial