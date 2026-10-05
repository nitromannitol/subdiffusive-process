module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Support.CutoffWeakScalingClock
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Support.CutoffWeakScalingModel
public import SubdiffusiveProcess.CoarseGrainingVocab.Section13.ClockPowerBridges

@[expose] public section

/-!
# The same strict-decay rate for real-radius clock ratios

Canonical adjacent-scale logarithmic interpolation bounds and annealed
one-step ordering pay a fixed endpoint loss. The cutoff agrees with the full
clock throughout the required window, so both clauses use the same constant.
-/

namespace SubdiffusiveProcess.Section10

open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (ahom ahom_pos)
open SubdiffusiveProcess.CoarseGrainingVocab.Section7Process
open SubdiffusiveProcess.CoarseGrainingVocab.Section7Support.CutoffWeakScaling

noncomputable section

/-- The canonical cutoff interpolation bounds, read below a larger cutoff,
give adjacent conductance bounds for the full clock, including radius one. -/
theorem strictDecay_clock_log_bounds {d : ℕ} (M : GMCModel d) {r : ℝ}
    (hr : 1 ≤ r) :
    -Real.log (ahom M (triadicIndex r)) ≤
        Real.log (timeScale (ahom M) r) - 2 * Real.log r ∧
      Real.log (timeScale (ahom M) r) - 2 * Real.log r ≤
        -Real.log (ahom M (triadicIndex r + 1)) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hcut : r ≤ (3 : ℝ) ^ (triadicIndex r + 1) :=
    ((SubdiffusiveProcess.CoarseGrainingVocab.Section13.lt_three_pow_triadicIndex_succ r).resolve_right
      (not_le.mpr hr0)).le
  have h := cutoff_log_bounds (ahom M) (ahom_pos M) (neg_log_mono M)
    (triadicIndex r + 1) hr0
  rw [timeScaleCutoff_of_le (ahom M) _ hcut, min_eq_left (Nat.le_succ _)] at h
  exact h

/-- A lawful arbitrary-scale conductance ratio implies the full real-radius
clock ratio with the same eta. Only a fixed endpoint constant is lost. -/
theorem strictDecay_timeScale_ratio {d : ℕ} (M : GMCModel d) {C eta : ℝ}
    (hC : 0 < C) (heta : 0 ≤ eta)
    (hdec : ∀ ell m : ℕ, ell ≤ m → ahom M m / ahom M ell ≤
      C * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (ell : ℝ)))))
    (r Rad : ℝ) (hr : 1 ≤ r) (hrRad : r ≤ Rad) :
    Real.exp (-(Real.log C + eta * Real.log 3 + 2 * tauSq M.P)) *
      (Rad / r) ^ (2 + eta) ≤ timeScale (ahom M) Rad / timeScale (ahom M) r := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hRad0 : 0 < Rad := hr0.trans_le hrRad
  have hRad1 : 1 ≤ Rad := hr.trans hrRad
  have hbr := strictDecay_clock_log_bounds M hr
  have hbRad := strictDecay_clock_log_bounds M hRad1
  have hindex := index_monotone hr0 hrRad
  have hdecLog := Real.log_le_log
    (div_pos (ahom_pos M (triadicIndex Rad)) (ahom_pos M (triadicIndex r)))
    (hdec (triadicIndex r) (triadicIndex Rad) hindex)
  rw [Real.log_div (ahom_pos M _).ne' (ahom_pos M _).ne',
    Real.log_mul hC.ne' (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 3)] at hdecLog
  have hstep := neg_log_step M (triadicIndex r)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hfloorR : Real.logb 3 Rad < (triadicIndex Rad : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hfloorr : (triadicIndex r : ℝ) ≤ Real.logb 3 r :=
    Nat.floor_le (Real.logb_nonneg (by norm_num) hr)
  unfold Real.logb at hfloorR hfloorr
  have hRlog := (div_lt_iff₀ hlog3).mp hfloorR
  have hrlog := (le_div_iff₀ hlog3).mp hfloorr
  have hgap : Real.log Rad - Real.log r ≤
      Real.log 3 * ((triadicIndex Rad : ℝ) - (triadicIndex r : ℝ) + 1) := by
    nlinarith only [hRlog, hrlog]
  have hgapEta := mul_le_mul_of_nonneg_left hgap heta
  have hnormalized :
      -(Real.log C + eta * Real.log 3 + 2 * tauSq M.P) +
        (2 + eta) * (Real.log Rad - Real.log r) ≤
      Real.log (timeScale (ahom M) Rad) - Real.log (timeScale (ahom M) r) := by
    nlinarith only [hbr.2, hbRad.1, hdecLog, hstep, hgapEta]
  apply (Real.log_le_log_iff
    (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (div_pos hRad0 hr0) _))
    (div_pos (timeScale_pos (ahom_pos M) hRad0)
      (timeScale_pos (ahom_pos M) hr0))).mp
  rw [Real.log_mul (Real.exp_pos _).ne'
      (Real.rpow_pos_of_pos (div_pos hRad0 hr0) _).ne',
    Real.log_exp, Real.log_rpow (div_pos hRad0 hr0),
    Real.log_div hRad0.ne' hr0.ne',
    Real.log_div (timeScale_pos (ahom_pos M) hRad0).ne'
      (timeScale_pos (ahom_pos M) hr0).ne']
  exact hnormalized

/-- In the specified finite-cutoff window both radii use the full clock, so
the very same eta and endpoint constant suffice. -/
theorem strictDecay_timeScaleCutoff_ratio {d : ℕ} (M : GMCModel d) {C eta : ℝ}
    (hC : 0 < C) (heta : 0 ≤ eta)
    (hdec : ∀ ell m : ℕ, ell ≤ m → ahom M m / ahom M ell ≤
      C * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (ell : ℝ)))))
    (L : ℕ) (r Rad : ℝ) (hr : 1 ≤ r) (hrRad : r ≤ Rad)
    (hRad : Rad ≤ (3 : ℝ) ^ L) :
    Real.exp (-(Real.log C + eta * Real.log 3 + 2 * tauSq M.P)) *
      (Rad / r) ^ (2 + eta) ≤
      timeScaleCutoff (ahom M) L Rad / timeScaleCutoff (ahom M) L r := by
  rw [timeScaleCutoff_of_le (ahom M) L hRad,
    timeScaleCutoff_of_le (ahom M) L (hrRad.trans hRad)]
  exact strictDecay_timeScale_ratio M hC heta hdec r Rad hr hrRad

end

end SubdiffusiveProcess.Section10
