module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepLogarithm
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import Mathlib.Algebra.Order.Floor.Semifield

@[expose] public section

/-!
# Arithmetic scales for the sharp diffusivity iteration

This file implements the elementary choices made at
`l.one.step.upper` and `l.one.step.lower`.  We use a harmlessly enlarged starting scale
`ceil (128 * |log delta|)`: it dominates the manuscript's
`16 ceil |log_3 delta|` and has the same logarithmic size.  The block length
is the literal `floor (delta⁻¹)` from the source.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- An integer starting scale dominating `16 ceil |log_3 delta|`. -/
def sharpStartScale (delta : ℝ) : ℕ :=
  ⌈128 * |Real.log delta|⌉₊

/-- The block length `floor (delta⁻¹)` used in the Euclidean telescope. -/
def sharpBlockLength (delta : ℝ) : ℕ :=
  ⌊delta⁻¹⌋₊

theorem sharpBlockLength_pos {delta : ℝ}
    (hdelta : 0 < delta) (hhalf : delta ≤ (1 : ℝ) / 2) :
    0 < sharpBlockLength delta := by
  rw [sharpBlockLength, Nat.floor_pos]
  rw [one_le_inv₀ hdelta]
  linarith

theorem delta_mul_sharpBlockLength_le_one {delta : ℝ}
    (hdelta : 0 < delta) :
    delta * (sharpBlockLength delta : ℝ) ≤ 1 := by
  have hfloor : (sharpBlockLength delta : ℝ) ≤ delta⁻¹ := by
    exact Nat.floor_le (inv_nonneg.mpr hdelta.le)
  calc
    delta * (sharpBlockLength delta : ℝ) ≤ delta * delta⁻¹ :=
      mul_le_mul_of_nonneg_left hfloor hdelta.le
    _ = 1 := mul_inv_cancel₀ hdelta.ne'

theorem half_le_delta_mul_sharpBlockLength {delta : ℝ}
    (hdelta : 0 < delta) (hhalf : delta ≤ (1 : ℝ) / 2) :
    (1 : ℝ) / 2 ≤ delta * (sharpBlockLength delta : ℝ) := by
  have hinv : 1 ≤ delta⁻¹ := by
    rw [one_le_inv₀ hdelta]
    linarith
  have hfloor : delta⁻¹ / 2 < (sharpBlockLength delta : ℝ) := by
    exact Nat.div_two_lt_floor hinv
  have hmul := mul_lt_mul_of_pos_left hfloor hdelta
  have hcancel : delta * (delta⁻¹ / 2) = (1 : ℝ) / 2 := by
    field_simp [hdelta.ne']
  rw [hcancel] at hmul
  exact hmul.le

theorem half_le_abs_log_delta {delta : ℝ}
    (hdelta : 0 < delta) (hhalf : delta ≤ (1 : ℝ) / 2) :
    (1 : ℝ) / 2 ≤ |Real.log delta| := by
  have hdeltaOne : delta ≤ 1 := hhalf.trans (by norm_num)
  have hlogNonpos : Real.log delta ≤ 0 := Real.log_nonpos hdelta.le hdeltaOne
  rw [abs_of_nonpos hlogNonpos]
  have hmono : Real.log delta ≤ Real.log ((1 : ℝ) / 2) :=
    Real.log_le_log hdelta hhalf
  have hhalfLog : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  rw [hhalfLog] at hmono
  have hlogTwo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  linarith

theorem sharpStartScale_add_one_le {delta : ℝ}
    (hdelta : 0 < delta) (hhalf : delta ≤ (1 : ℝ) / 2) :
    ((sharpStartScale delta : ℕ) : ℝ) + 1 ≤
      132 * |Real.log delta| := by
  have hlog : (1 : ℝ) / 2 ≤ |Real.log delta| :=
    half_le_abs_log_delta hdelta hhalf
  have harg : 0 ≤ 128 * |Real.log delta| := by positivity
  have hceil : ((sharpStartScale delta : ℕ) : ℝ) <
      128 * |Real.log delta| + 1 := by
    exact Nat.ceil_lt_add_one harg
  dsimp [sharpStartScale] at hceil ⊢
  nlinarith

/-- The enlarged starting scale dominates the lower endpoint required by the
printed one-step lemmas. -/
theorem sourceStartScale_le_sharpStartScale {delta : ℝ}
    (hdelta : 0 < delta) (hhalf : delta ≤ (1 : ℝ) / 2) :
    16 * ⌈|Real.log delta / Real.log 3|⌉₊ ≤ sharpStartScale delta := by
  have hlog : (1 : ℝ) / 2 ≤ |Real.log delta| :=
    half_le_abs_log_delta hdelta hhalf
  have hlogThree : (1 : ℝ) / 2 < Real.log 3 := by
    have h23 : Real.log 2 < Real.log 3 :=
      Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    linarith [Real.log_two_gt_d9]
  have hlogThreePos : 0 < Real.log 3 := lt_trans (by norm_num) hlogThree
  have hratio : |Real.log delta / Real.log 3| ≤ 2 * |Real.log delta| := by
    rw [abs_div, abs_of_pos hlogThreePos]
    rw [div_le_iff₀ hlogThreePos]
    nlinarith [abs_nonneg (Real.log delta)]
  have hratioNonneg : 0 ≤ |Real.log delta / Real.log 3| := abs_nonneg _
  have hceil : (⌈|Real.log delta / Real.log 3|⌉₊ : ℝ) <
      |Real.log delta / Real.log 3| + 1 := Nat.ceil_lt_add_one hratioNonneg
  have hleft : (16 * ⌈|Real.log delta / Real.log 3|⌉₊ : ℕ) ≤
      ⌈128 * |Real.log delta|⌉₊ := by
    have htarget :
        (16 : ℝ) * (⌈|Real.log delta / Real.log 3|⌉₊ : ℝ) ≤
          128 * |Real.log delta| := by
      nlinarith
    have hcast :
        ((16 * ⌈|Real.log delta / Real.log 3|⌉₊ : ℕ) : ℝ) ≤
          (⌈128 * |Real.log delta|⌉₊ : ℝ) := by
      simpa using htarget.trans (Nat.le_ceil (128 * |Real.log delta|))
    exact_mod_cast hcast
  simpa [sharpStartScale] using hleft

/-- The complete base-scale clause of the sharp block payload. -/
theorem sharp_base_scale_bound {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (hm : m ≤ sharpStartScale M.delta) :
    |Real.log (ahom M m) +
        2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
      132 * M.delta ^ 2 * |Real.log M.delta| := by
  have hraw := abs_centered_log_le_normalization_drift M m
  have hmreal : (m : ℝ) + 1 ≤
      (sharpStartScale M.delta : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hm 1
  have hstart := sharpStartScale_add_one_le
    M.shellPrefix.delta_pos M.shellPrefix.delta_le_half
  have htau := tauSq_le_delta_sq M
  have hlogTwo : Real.log 2 / 2 ≤ 1 := by
    linarith [Real.log_two_lt_d9]
  have htauSimple : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta ^ 2 :=
    htau.trans (by
      have hdeltaSq : 0 ≤ M.delta ^ 2 := sq_nonneg _
      nlinarith)
  calc
    |Real.log (ahom M m) +
        2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
        ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P := hraw
    _ ≤ ((sharpStartScale M.delta : ℝ) + 1) * M.delta ^ 2 :=
      mul_le_mul hmreal htauSimple M.G4.tauSq_pos.le (by positivity)
    _ ≤ (132 * |Real.log M.delta|) * M.delta ^ 2 :=
      mul_le_mul_of_nonneg_right hstart (sq_nonneg _)
    _ = 132 * M.delta ^ 2 * |Real.log M.delta| := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
