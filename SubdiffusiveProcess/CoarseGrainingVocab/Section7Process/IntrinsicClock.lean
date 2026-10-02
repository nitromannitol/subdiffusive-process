import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Process

open scoped NNReal

noncomputable section

/-! ### The clock at triadic radii -/



def timeScaleTriadic (ahom : ℕ → ℝ) (m : ℕ) : ℝ :=
  (3 : ℝ) ^ (2 * m) / ahom m

/-- At the unit radius the triadic value is `1 / ahom_0`. -/
@[simp]
theorem timeScaleTriadic_zero (ahom : ℕ → ℝ) : timeScaleTriadic ahom 0 = 1 / ahom 0 := by
  simp [timeScaleTriadic]

/-- The triadic values are positive when the conductances are. -/
theorem timeScaleTriadic_pos {ahom : ℕ → ℝ} (h : ∀ m, 0 < ahom m) (m : ℕ) :
    0 < timeScaleTriadic ahom m :=
  div_pos (by positivity) (h m)

/-- The exponent of the log-affine interpolation on the triadic block
`[3^m, 3^{m+1}]`: the slope of `log T` in `log r` measured in base `3`. -/
def timeScaleExponent (ahom : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.logb 3 (timeScaleTriadic ahom (m + 1) / timeScaleTriadic ahom m)

/-! ### The clock -/

/-- The block index of a radius: the triadic block `[3^m, 3^{m+1})` containing
`r ≥ 1`. -/
def triadicIndex (r : ℝ) : ℕ := ⌊Real.logb 3 r⌋₊



def timeScale (ahom : ℕ → ℝ) (r : ℝ) : ℝ :=
  if r ≤ 1 then r ^ 2 / ahom 0
  else
    timeScaleTriadic ahom (triadicIndex r) *
      (r / (3 : ℝ) ^ triadicIndex r) ^ timeScaleExponent ahom (triadicIndex r)

/-- Below the unit scale the clock is quadratic. -/
theorem timeScale_of_le_one (ahom : ℕ → ℝ) {r : ℝ} (hr : r ≤ 1) :
    timeScale ahom r = r ^ 2 / ahom 0 := by
  rw [timeScale, if_pos hr]

/-- The unit-scale value of the clock. -/
@[simp]
theorem timeScale_one (ahom : ℕ → ℝ) : timeScale ahom 1 = 1 / ahom 0 := by
  rw [timeScale_of_le_one ahom le_rfl, one_pow]

/-- The block index of a triadic radius is its exponent. -/
theorem triadicIndex_triadic (m : ℕ) : triadicIndex ((3 : ℝ) ^ m) = m := by
  have h3 : (1 : ℝ) < 3 := by norm_num
  have hcast : ((3 : ℝ) ^ m) = (3 : ℝ) ^ (m : ℝ) := (Real.rpow_natCast 3 m).symm
  rw [triadicIndex, hcast, Real.logb_rpow (b := 3) (by norm_num) (by norm_num),
    Nat.floor_natCast]

/-- **The clock at the triadic radii.**  `T(3^m) = 3^{2m} / ahom_m`, for every
`m`, including the unit radius where the two branches of the definition meet. -/
theorem timeScale_triadic (ahom : ℕ → ℝ) (m : ℕ) :
    timeScale ahom ((3 : ℝ) ^ m) = timeScaleTriadic ahom m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · have hgt : (1 : ℝ) < (3 : ℝ) ^ m := by
      have : (3 : ℝ) ^ 1 ≤ (3 : ℝ) ^ m := by
        exact pow_le_pow_right₀ (by norm_num) hm
      nlinarith [this]
    rw [timeScale, if_neg (not_le.mpr hgt), triadicIndex_triadic]
    rw [div_self (by positivity), Real.one_rpow, mul_one]

/-- The clock is positive at positive radii when the conductances are positive. -/
theorem timeScale_pos {ahom : ℕ → ℝ} (h : ∀ m, 0 < ahom m) {r : ℝ} (hr : 0 < r) :
    0 < timeScale ahom r := by
  rw [timeScale]
  split_ifs with hle
  · exact div_pos (by positivity) (h 0)
  · refine mul_pos (timeScaleTriadic_pos h _) (Real.rpow_pos_of_pos ?_ _)
    exact div_pos hr (by positivity)

/-! ### The cutoff clock -/



def timeScaleCutoff (ahom : ℕ → ℝ) (L : ℕ) (r : ℝ) : ℝ :=
  if r ≤ (3 : ℝ) ^ L then timeScale ahom r else r ^ 2 / ahom L

/-- Below the cutoff radius the cutoff clock is the clock. -/
theorem timeScaleCutoff_of_le (ahom : ℕ → ℝ) (L : ℕ) {r : ℝ} (hr : r ≤ (3 : ℝ) ^ L) :
    timeScaleCutoff ahom L r = timeScale ahom r := by
  rw [timeScaleCutoff, if_pos hr]

/-- Above the cutoff radius the cutoff clock is quadratic with conductance
`ahom_L`. -/
theorem timeScaleCutoff_of_gt (ahom : ℕ → ℝ) (L : ℕ) {r : ℝ} (hr : (3 : ℝ) ^ L < r) :
    timeScaleCutoff ahom L r = r ^ 2 / ahom L := by
  rw [timeScaleCutoff, if_neg (not_le.mpr hr)]



theorem timeScaleCutoff_triadic (ahom : ℕ → ℝ) (L : ℕ) :
    timeScaleCutoff ahom L ((3 : ℝ) ^ L) = ((3 : ℝ) ^ L) ^ 2 / ahom L := by
  rw [timeScaleCutoff_of_le ahom L le_rfl, timeScale_triadic, timeScaleTriadic,
    ← pow_mul, mul_comm 2 L]

/-- The cutoff clock is positive at positive radii. -/
theorem timeScaleCutoff_pos {ahom : ℕ → ℝ} (h : ∀ m, 0 < ahom m) (L : ℕ) {r : ℝ}
    (hr : 0 < r) : 0 < timeScaleCutoff ahom L r := by
  rw [timeScaleCutoff]
  split_ifs
  · exact timeScale_pos h hr
  · exact div_pos (by positivity) (h L)

/-! ### Weak scaling -/



def HasWeakScaling (F : ℝ → ℝ) (c C beta : ℝ) : Prop :=
  ∀ r R : ℝ, 0 < r → r ≤ R →
    c * (R / r) ^ 2 ≤ F R / F r ∧ F R / F r ≤ C * (R / r) ^ beta

/-! ### The intrinsic off-diagonal rate -/



def offDiagonalRate (F : ℝ → ℝ) (Rad t : ℝ) : ℝ :=
  if Rad = 0 then 0
  else sSup ((fun s : ℝ ↦ max (Rad / s - t / F s) 0) '' Set.Ioc 0 Rad)



@[simp]
theorem offDiagonalRate_zero (F : ℝ → ℝ) (t : ℝ) : offDiagonalRate F 0 t = 0 := by
  rw [offDiagonalRate, if_pos rfl]

/-- The off-diagonal rate is nonnegative. -/
theorem offDiagonalRate_nonneg (F : ℝ → ℝ) (Rad t : ℝ) : 0 ≤ offDiagonalRate F Rad t := by
  rw [offDiagonalRate]
  split_ifs with h
  · exact le_rfl
  · refine Real.sSup_nonneg ?_
    rintro u ⟨s, _, rfl⟩
    exact le_max_right _ _

/-- Every admissible scale contributes a lower bound to the off-diagonal rate,
once the defining family is bounded above. -/
theorem le_offDiagonalRate {F : ℝ → ℝ} {Rad t : ℝ} (hRad : Rad ≠ 0)
    (hbdd : BddAbove ((fun s : ℝ ↦ max (Rad / s - t / F s) 0) '' Set.Ioc 0 Rad))
    {s : ℝ} (hs : s ∈ Set.Ioc 0 Rad) :
    max (Rad / s - t / F s) 0 ≤ offDiagonalRate F Rad t := by
  rw [offDiagonalRate, if_neg hRad]
  exact le_csSup hbdd ⟨s, hs, rfl⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Process
