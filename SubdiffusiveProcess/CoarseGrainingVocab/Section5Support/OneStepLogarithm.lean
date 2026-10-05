module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support
public import SubdiffusiveProcess.Section5.HomogenizedCoefficientReciprocalLower

@[expose] public section

/-!
# Logarithmic assembly for the section 5 one-step estimates

This file isolates the deterministic final line shared by the manuscript's
one-step upper and lower bounds (paper label `l.one.step.upper`).  Once the two
multiplicative estimates have been proved, `Real.log_le_sub_one_of_pos`
converts them to the centered logarithmic increment with no additional
smallness loss.

The estimates are separated by their proof role.
The PDE construction of the two multiplicative estimates is deliberately not
encoded as a theorem-shaped assumption here.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- Two reciprocal multiplicative comparisons imply the corresponding
centered logarithmic comparison.  This is the deterministic logarithmic step
used after `e.one.step.upper` and `e.one.step.lower`. -/
theorem abs_log_sub_log_add_le_of_two_sided_multiplicative
    {x y drift error : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hupper : x ≤ y * (1 - drift + error))
    (hlower : x⁻¹ ≤ y⁻¹ * (1 + drift + error)) :
    |Real.log x - Real.log y + drift| ≤ error := by
  have hratioUpper : x / y ≤ 1 - drift + error := by
    rw [div_le_iff₀ hy]
    simpa only [mul_comm] using hupper
  have hlogUpper : Real.log x - Real.log y ≤ -drift + error := by
    have hlog := Real.log_le_sub_one_of_pos (div_pos hx hy)
    rw [Real.log_div hx.ne' hy.ne'] at hlog
    linarith
  have hratioLower : y / x ≤ 1 + drift + error := by
    rw [div_eq_mul_inv]
    calc
      y * x⁻¹ = x⁻¹ * y := by ring
      _ ≤ (y⁻¹ * (1 + drift + error)) * y :=
        mul_le_mul_of_nonneg_right hlower hy.le
      _ = 1 + drift + error := by field_simp [hy.ne']
  have hlogLower : -(error) ≤ Real.log x - Real.log y + drift := by
    have hlog := Real.log_le_sub_one_of_pos (div_pos hy hx)
    rw [Real.log_div hy.ne' hx.ne'] at hlog
    linarith
  rw [abs_le]
  exact ⟨hlogLower, by linarith⟩

/-- Model-specialized form of the deterministic logarithmic conversion.

The hypotheses are exactly the conclusions of the printed one-step upper and
lower estimates at a starting scale `n` and gap `h`.  Their common error is
preserved verbatim in the centered-log conclusion. -/
theorem abs_centered_log_increment_le_of_one_step_bounds {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (error : ℝ)
    (hupper :
      ahom M (n + h) ≤ ahom M n *
        (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / d + error))
    (hlower :
      (ahom M (n + h))⁻¹ ≤ (ahom M n)⁻¹ *
        (1 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / d + error)) :
    |(Real.log (ahom M (n + h)) +
          2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (n + h + 1 : ℝ) / d) -
        (Real.log (ahom M n) +
          2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (n + 1 : ℝ) / d)| ≤
      error := by
  have hcurrent : 0 < ahom M (n + h) :=
    (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M (n + h))
  have hprevious : 0 < ahom M n :=
    (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M n)
  have hlog := abs_log_sub_log_add_le_of_two_sided_multiplicative
    hcurrent hprevious hupper hlower
  have hcentered :
      (Real.log (ahom M (n + h)) +
          2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (n + h + 1 : ℝ) / d) -
        (Real.log (ahom M n) +
          2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (n + 1 : ℝ) / d) =
        Real.log (ahom M (n + h)) - Real.log (ahom M n) +
          2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / d := by
    ring
  rw [hcentered]
  exact hlog

/-- The source's base-scale estimate before choosing
`J = 16 ceil |log_3 delta|`: the centered logarithm is bounded by one
normalization drift.  The only coefficient inputs are the sealed reciprocal
lower bound and `ahom ≤ 1`. -/
theorem abs_centered_log_le_normalization_drift {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) :
    |Real.log (ahom M m) +
        2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d| ≤
      ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P := by
  let A : ℝ := ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P
  let c : ℝ := 2 / (d : ℝ)
  have hd : (2 : ℝ) ≤ d := by
    exact_mod_cast M.shellPrefix.dimension
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le (by norm_num) hd
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    exact (div_le_one hdpos).2 hd
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by positivity) M.G4.tauSq_pos.le
  have hahom : 0 < ahom M m :=
    (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M m)
  have hlogUpper : Real.log (ahom M m) ≤ 0 :=
    Real.log_nonpos hahom.le (ahom_le_one M m)
  have hlogLower : -A ≤ Real.log (ahom M m) := by
    have hexp :=
      _root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M m
    have hlog := Real.log_le_log (Real.exp_pos _) hexp
    rw [Real.log_exp] at hlog
    dsimp [A]
    simpa only [neg_mul] using hlog
  have hcA0 : 0 ≤ c * A := mul_nonneg hc0 hA0
  have hcAle : c * A ≤ A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hA0
  have hcentered :
      Real.log (ahom M m) +
          2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (m + 1 : ℝ) / d =
        Real.log (ahom M m) + c * A := by
    dsimp [A, c]
    ring
  rw [hcentered, abs_le]
  constructor <;> linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
