module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Support.CutoffWeakScalingAlgebra
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock

@[expose] public section

/-!
# Logarithmic interpolation of the cutoff clock

The normalized logarithmic clock is bracketed by adjacent triadic values.
Clipping their indices at the cutoff preserves the required difference bounds.
-/

set_option autoImplicit false
open SubdiffusiveProcess.CoarseGrainingVocab.Section7Process
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Support.CutoffWeakScaling
noncomputable section
theorem log_triadic (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    Real.log (timeScaleTriadic a n) = 2 * (n : ℝ) * Real.log 3 - Real.log (a n) := by
  unfold timeScaleTriadic
  rw [Real.log_div (by positivity) (ha n).ne', Real.log_pow]
  push_cast
  ring

theorem log_exponent (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (n : ℕ)
    (hlog : ∀ k, Real.log (timeScaleTriadic a k) = 2*(k:ℝ)*Real.log 3-Real.log (a k)) :
    timeScaleExponent a n =
      (2 * Real.log 3 + Real.log (a n) - Real.log (a (n+1))) / Real.log 3 := by
  unfold timeScaleExponent Real.logb
  rw [Real.log_div (timeScaleTriadic_pos ha (n+1)).ne' (timeScaleTriadic_pos ha n).ne', hlog, hlog]
  push_cast
  ring

theorem index_below_one {r : ℝ} (hr : 0 < r) (h1 : r ≤ 1) : triadicIndex r = 0 := by
  unfold triadicIndex
  apply Nat.floor_eq_zero.mpr
  unfold Real.logb
  have hlog := Real.log_nonpos hr.le h1
  exact lt_of_le_of_lt (div_nonpos_of_nonpos_of_nonneg hlog (Real.log_pos (by norm_num)).le) (by norm_num)

theorem index_monotone {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    triadicIndex r ≤ triadicIndex R := by
  exact Nat.floor_mono ((Real.logb_le_logb (by norm_num) hr (hr.trans_le hrR)).mpr hrR)

theorem index_above_cutoff {r : ℝ} {L : ℕ} (hr : (3:ℝ)^L ≤ r) :
    L ≤ triadicIndex r := by
  have hr0 : (0:ℝ) < 3^L := pow_pos (by norm_num : (0:ℝ) < 3) L
  have h3 : (0:ℝ) < 3 := by norm_num
  have hle : (3:ℝ)^L ≤ r := hr
  have hm := index_monotone (r := 3^L) (R := r) hr0 hle
  rw [triadicIndex_triadic] at hm
  exact hm

theorem index_below_cutoff {r : ℝ} {L : ℕ} (hr : 0 < r) (hR : r ≤ (3:ℝ)^L) :
    triadicIndex r ≤ L := by
  have hm := index_monotone hr hR
  rw [triadicIndex_triadic] at hm
  exact hm

theorem log_affine_clock (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) {r : ℝ} (hr : 1 < r) :
    Real.log (timeScale a r) - 2*Real.log r =
      (1-(Real.logb 3 r-(triadicIndex r:ℝ)))*(-Real.log (a (triadicIndex r))) +
        (Real.logb 3 r-(triadicIndex r:ℝ))*(-Real.log (a (triadicIndex r+1))) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hp : 0 < r / (3:ℝ)^triadicIndex r := div_pos hr0 (by positivity)
  rw [timeScale, ite_eq_right (not_le.mpr hr),
    Real.log_mul (timeScaleTriadic_pos ha _).ne' (Real.rpow_pos_of_pos hp _).ne',
    Real.log_rpow hp, log_triadic a ha,
    log_exponent a ha _ (log_triadic a ha),
    Real.log_div hr0.ne' (by positivity), Real.log_pow]
  exact log_affine_slope_identity _ _ _ _ _ (Real.log_pos (by norm_num : (1:ℝ)<3)).ne'

/-- The normalized cutoff clock lies between adjacent logarithmic conductances. -/
theorem cutoff_log_bounds (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hmono : Monotone (fun n => -Real.log (a n))) (L : ℕ) {r : ℝ} (hr : 0 < r) :
    -Real.log (a (min (triadicIndex r) L)) ≤
        Real.log (timeScaleCutoff a L r) - 2*Real.log r ∧
      Real.log (timeScaleCutoff a L r) - 2*Real.log r ≤
        -Real.log (a (min (triadicIndex r) L + 1)) := by
  by_cases h1 : r ≤ 1
  · have hL : r ≤ (3:ℝ)^L := h1.trans (one_le_pow₀ (by norm_num))
    rw [timeScaleCutoff_of_le a L hL, timeScale_of_le_one a h1,
      log_quadratic hr (ha 0), index_below_one hr h1, Nat.zero_min]
    exact ⟨le_rfl, hmono (Nat.zero_le 1)⟩
  · by_cases hL : r ≤ (3:ℝ)^L
    · have hi := index_below_cutoff hr hL
      rw [timeScaleCutoff_of_le a L hL, min_eq_left hi,
        log_affine_clock a ha (lt_of_not_ge h1)]
      have hindex : (triadicIndex r : ℝ) ≤ Real.logb 3 r :=
        Nat.floor_le (Real.logb_nonneg (by norm_num) (le_of_not_ge h1))
      have hindex' : Real.logb 3 r < (triadicIndex r : ℝ)+1 :=
        Nat.lt_floor_add_one _
      exact affine_bounds (hmono (Nat.le_succ _)) (by linarith) (by linarith)
    · have hi := index_above_cutoff (le_of_not_ge hL)
      rw [timeScaleCutoff_of_gt a L (lt_of_not_ge hL), log_quadratic hr (ha L),
        min_eq_right hi]
      exact ⟨le_rfl, hmono (Nat.le_succ L)⟩

/-- Clipping the triadic indices can only reduce their separation. -/
theorem cutoff_index_gap {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (L : ℕ) :
    ((min (triadicIndex R) L+1 : ℕ) : ℝ) - (min (triadicIndex r) L : ℕ) ≤
      (Real.log R-Real.log r)/Real.log 3+2 := by
  have hxy := (Real.logb_le_logb (b := 3) (by norm_num) hr (hr.trans_le hrR)).mpr hrR
  have hg := index_cast_gap (L := L) (floor_max_bounds (Real.logb 3 r)).1
    (floor_max_bounds (Real.logb 3 R)).2 (max_le_max hxy le_rfl)
  change ((min (triadicIndex R) L+1 : ℕ) : ℝ) - (min (triadicIndex r) L : ℕ) ≤
    max (Real.logb 3 R) 0 - max (Real.logb 3 r) 0 + 2 at hg
  have hm := max_gap hxy
  have hh : ((min (triadicIndex R) L+1 : ℕ) : ℝ) - (min (triadicIndex r) L : ℕ) ≤
      Real.logb 3 R - Real.logb 3 r + 2 := by
    linarith only [hg, hm]
  convert hh using 1
  unfold Real.logb
  ring

/-- Discrete logarithmic increment bounds imply the continuous cutoff bounds. -/
theorem cutoff_weak_scaling_of_log_increments (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hmono : Monotone (fun n => -Real.log (a n))) {A B D : ℝ} (hB : 0 ≤ B)
    (hstep : ∀ n, -Real.log (a (n+1))-(-Real.log (a n)) ≤ D)
    (hincr : ∀ n m : ℕ, n ≤ m →
      Real.log (a n)-Real.log (a m) ≤ A+B*((m:ℝ)-(n:ℝ)))
    (L : ℕ) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    Real.exp (-D)*(R/r)^2 ≤ timeScaleCutoff a L R / timeScaleCutoff a L r ∧
      timeScaleCutoff a L R / timeScaleCutoff a L r ≤
        Real.exp (A+2*B)*(R/r)^(2+B/Real.log 3) := by
  have hR := hr.trans_le hrR
  have hTr := timeScaleCutoff_pos ha L hr
  have hTR := timeScaleCutoff_pos ha L hR
  have hbr := cutoff_log_bounds a ha hmono L hr
  have hbR := cutoff_log_bounds a ha hmono L hR
  have hnm := (clamped_order (index_monotone hr hrR) L).1
  have hl := interpolation_lower hmono hnm hbr.2 hbR.1 (hstep _)
  have hinc := hincr (min (triadicIndex r) L) (min (triadicIndex R) L+1) (by omega)
  have hgap := cutoff_index_gap hr hrR L
  have hlog := Real.log_le_log hr hrR
  have hnormalized :
      (Real.log (timeScaleCutoff a L R)-2*Real.log R) -
          (Real.log (timeScaleCutoff a L r)-2*Real.log r) ≤
        A+B*((min (triadicIndex R) L+1 : ℕ)-(min (triadicIndex r) L : ℕ) : ℝ) := by
    linarith only [hinc, hbr.1, hbR.2]
  have hu := log_scale_bound (Real.log_pos (by norm_num : (1:ℝ)<3)) hB hgap hlog
    hnormalized
  constructor
  · apply log_ratio_lower hr hR hTR hTr
    linarith
  · apply log_ratio_upper hr hR hTR hTr
    linarith

end
end SubdiffusiveProcess.CoarseGrainingVocab.Section7Support.CutoffWeakScaling
