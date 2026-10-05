module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Exponents.BetaExponents
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
public import SubdiffusiveProcess.Section5.HomogenizedCoefficientReciprocalLower

@[expose] public section




set_option autoImplicit false

open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section7Exponents
open SubdiffusiveProcess.CoarseGrainingVocab.Section7Process

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section10

variable {d : ℕ}

/-- `(3 : ℝ) ^ m` as an exponential, for the `rpow` bookkeeping below. -/
theorem three_pow_eq_exp (m : ℕ) : ((3 : ℝ) ^ m) = Real.exp ((m : ℝ) * Real.log 3) := by
  rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num : (0:ℝ) < 3), Real.rpow_natCast]

/-- A triadic radius raised to a real exponent. -/
theorem three_pow_rpow (m : ℕ) (b : ℝ) :
    ((3 : ℝ) ^ m) ^ b = Real.exp (b * ((m : ℝ) * Real.log 3)) := by
  rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
  congr 1
  ring

/-- **The clock's exact upper power bound at the triadic radii.**

From the PROVED `exp (-(m+1) tau^2) ≤ ahom M m`, the intrinsic clock satisfies
`Tr (3 ^ m) ≤ exp (tau^2) * (3 ^ m) ^ (2 + tau^2 / log 3)`, whose exponent is the planar
walk dimension `walkDimensionTwo M`. -/
theorem timeScale_triadic_le (M : GMCModel d) (m : ℕ) :
    timeScale (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) ((3 : ℝ) ^ m)
      ≤ Real.exp (tauSq M.P) * ((3 : ℝ) ^ m) ^ walkDimensionTwo M := by
  have hL : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlow : Real.exp (-(m + 1 : ℝ) * tauSq M.P) ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M m :=
    _root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M m
  have hpos : 0 < Real.exp (-(m + 1 : ℝ) * tauSq M.P) := Real.exp_pos _
  rw [timeScale_triadic, timeScaleTriadic]
  have hnum : (0 : ℝ) < (3 : ℝ) ^ (2 * m) := by positivity
  have hstep : (3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m
      ≤ (3 : ℝ) ^ (2 * m) / Real.exp (-(m + 1 : ℝ) * tauSq M.P) :=
    div_le_div_of_nonneg_left hnum.le hpos hlow
  refine hstep.trans (le_of_eq ?_)
  rw [div_eq_mul_inv, ← Real.exp_neg]
  rw [three_pow_rpow, walkDimensionTwo, ← Real.exp_add]
  have h2m : ((3 : ℝ) ^ (2 * m)) = Real.exp ((2 * (m : ℝ)) * Real.log 3) := by
    rw [three_pow_eq_exp (2 * m)]
    congr 1
    push_cast
    ring
  rw [h2m, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- **The power window's lower half fails for an overshooting `betaMinus`.**

For `d ≠ 2` and any `etaSub` above the planar subdiffusivity exponent `tau^2 / log 3`, the
inequality `cb * r ^ betaMinus C0 M etaSub ≤ Tr r` of
the uniform power-law bound for the diffusion time scale has no positive constant, already at the triadic
radii. -/
theorem not_clock_power_lower_bound_betaMinus (M : GMCModel d) (C0 etaSub : ℝ)
    (hd : d ≠ 2) (heta : tauSq M.P / Real.log 3 < etaSub) :
    ¬ ∃ cb : ℝ, 0 < cb ∧ ∀ m : ℕ,
        cb * ((3 : ℝ) ^ m) ^ betaMinus C0 M etaSub
          ≤ timeScale (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) ((3 : ℝ) ^ m) := by
  rintro ⟨cb, hcb, hbound⟩
  have hL : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  set bstar : ℝ := walkDimensionTwo M with hbstar
  set b : ℝ := betaMinus C0 M etaSub with hb
  have hlt : bstar < b := by
    have h1 : 2 + etaSub ≤ b := by
      rw [hb, betaMinus, ite_eq_right hd]
      exact le_max_left _ _
    have h2 : bstar = 2 + tauSq M.P / Real.log 3 := by rw [hbstar, walkDimensionTwo]
    rw [h2]
    linarith
  -- the two bounds collide: `cb ≤ exp (tau^2) * exp ((bstar - b) * m * log 3)`, which tends to 0
  have hkey : ∀ m : ℕ,
      cb ≤ Real.exp (tauSq M.P) * Real.exp ((bstar - b) * ((m : ℝ) * Real.log 3)) := by
    intro m
    have h := (hbound m).trans (timeScale_triadic_le M m)
    rw [three_pow_rpow, three_pow_rpow] at h
    have hposb : (0 : ℝ) < Real.exp (b * ((m : ℝ) * Real.log 3)) := Real.exp_pos _
    rw [← le_div_iff₀ hposb] at h
    refine h.trans (le_of_eq ?_)
    rw [mul_div_assoc, ← Real.exp_sub]
    congr 2
    ring
  -- choose `m` so large that the right side is below `cb`
  obtain ⟨m, hm⟩ := exists_nat_gt
    (Real.log (cb / Real.exp (tauSq M.P)) / ((bstar - b) * Real.log 3))
  have hneg : (bstar - b) * Real.log 3 < 0 := mul_neg_of_neg_of_pos (by linarith) hL
  have hgoal : Real.exp ((bstar - b) * ((m : ℝ) * Real.log 3))
      < cb / Real.exp (tauSq M.P) := by
    have hquot : (0 : ℝ) < cb / Real.exp (tauSq M.P) := by positivity
    rw [← Real.log_lt_log_iff (Real.exp_pos _) hquot, Real.log_exp]
    have hdiv : Real.log (cb / Real.exp (tauSq M.P)) / ((bstar - b) * Real.log 3) < (m : ℝ) := hm
    have := (div_lt_iff_of_neg hneg).mp hdiv
    calc (bstar - b) * ((m : ℝ) * Real.log 3)
        = (m : ℝ) * ((bstar - b) * Real.log 3) := by ring
      _ < Real.log (cb / Real.exp (tauSq M.P)) := this
  have hfinal := hkey m
  have hE : (0 : ℝ) < Real.exp (tauSq M.P) := Real.exp_pos _
  rw [lt_div_iff₀ hE] at hgoal
  nlinarith [hfinal, hgoal]

end SubdiffusiveProcess.CoarseGrainingVocab.Section10

end
