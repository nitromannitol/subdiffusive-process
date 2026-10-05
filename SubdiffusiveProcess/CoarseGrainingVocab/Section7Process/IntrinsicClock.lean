module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

/-!
# The intrinsic time scales of Section 7

This file transcribes the intrinsic clocks of the manuscript.  The manuscript's
displays are:

* the diffusion time scale:
  `T(3^m) := 3^{2m} / ahom_m` for `m ∈ ℕ₀`;
* `T(r) := r^2 / ahom_0` for `0 < r ≤ 1`;
* for `r ≥ 1`, `T` is extended so that
  `log T(r)` is affine in `log r` between consecutive triadic radii;
* the cutoff clock:
  `T_L(r) := T(r)` for `0 < r ≤ 3^L` and `T_L(r) := T(3^L)(r/3^L)^2 = r^2/ahom_L`
  for `r ≥ 3^L`;
* the weak-scaling window:
  `c (R/r)^2 ≤ T_L(R)/T_L(r) ≤ C (R/r)^{beta_+}` for `0 < r ≤ R`, uniformly
  in `L`;
* the intrinsic off-diagonal rate:
  `Phi_F(R,t) := sup_{0 < s ≤ R} (R/s - t/F(s))_+`, with `Phi_F(0,t) := 0`.

The clocks are defined from an abstract sequence `ahom : ℕ → ℝ` of homogenized
conductances, so that this file is independent of the probabilistic
construction of `ahom_m`.  Only the elementary structural properties are proved
here: the values at the triadic radii and below the unit scale, the agreement of
the two branches of the cutoff clock, positivity, and the basic bounds on the
off-diagonal rate.  The quantitative statements — monotonicity of `T(r)/r^2`,
the weak-scaling window, and the intrinsic off-diagonal optimization lemma
 — need the annealed ordering
`e.annealed.ordering` and the perturbative estimates of Sections 3-5 and are
not proved here.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Process

open scoped NNReal

noncomputable section

/-! ### The clock at triadic radii -/

/-- The intrinsic time scale at the triadic radius `3 ^ m`:
`T(3^m) = 3^{2m} / ahom_m`. -/
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

/-- The intrinsic time scale `T` : quadratic
below the unit scale, and log-affine in `log r` between consecutive triadic
radii above it. -/
def timeScale (ahom : ℕ → ℝ) (r : ℝ) : ℝ :=
  if r ≤ 1 then r ^ 2 / ahom 0
  else
    timeScaleTriadic ahom (triadicIndex r) *
      (r / (3 : ℝ) ^ triadicIndex r) ^ timeScaleExponent ahom (triadicIndex r)

/-- Below the unit scale the clock is quadratic. -/
theorem timeScale_of_le_one (ahom : ℕ → ℝ) {r : ℝ} (hr : r ≤ 1) :
    timeScale ahom r = r ^ 2 / ahom 0 := by
  rw [timeScale, ite_eq_left hr]

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
    rw [timeScale, ite_eq_right (not_le.mpr hgt), triadicIndex_triadic]
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

/-- The cutoff intrinsic time scale `T_L` : the
clock `T` below the cutoff radius `3^L`, continued quadratically above it. -/
def timeScaleCutoff (ahom : ℕ → ℝ) (L : ℕ) (r : ℝ) : ℝ :=
  if r ≤ (3 : ℝ) ^ L then timeScale ahom r else r ^ 2 / ahom L

/-- Below the cutoff radius the cutoff clock is the clock. -/
theorem timeScaleCutoff_of_le (ahom : ℕ → ℝ) (L : ℕ) {r : ℝ} (hr : r ≤ (3 : ℝ) ^ L) :
    timeScaleCutoff ahom L r = timeScale ahom r := by
  rw [timeScaleCutoff, ite_eq_left hr]

/-- Above the cutoff radius the cutoff clock is quadratic with conductance
`ahom_L`. -/
theorem timeScaleCutoff_of_gt (ahom : ℕ → ℝ) (L : ℕ) {r : ℝ} (hr : (3 : ℝ) ^ L < r) :
    timeScaleCutoff ahom L r = r ^ 2 / ahom L := by
  rw [timeScaleCutoff, ite_eq_right (not_le.mpr hr)]

/-- **The cutoff clock is continuous at the cutoff radius**: the two branches  agree there, both giving `3^{2L}/ahom_L`. -/
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

/-- The weak-scaling window with the clock growing at least quadratically and at
most with exponent `beta`, with constants `c` and `C`. -/
def HasWeakScaling (F : ℝ → ℝ) (c C beta : ℝ) : Prop :=
  ∀ r R : ℝ, 0 < r → r ≤ R →
    c * (R / r) ^ 2 ≤ F R / F r ∧ F R / F r ≤ C * (R / r) ^ beta

/-! ### The intrinsic off-diagonal rate -/

/-- The intrinsic off-diagonal rate of an increasing clock:
`Phi_F(R,t) = sup_{0 < s ≤ R} (R/s - t/F(s))_+`, with `Phi_F(0,t) = 0`. -/
def offDiagonalRate (F : ℝ → ℝ) (Rad t : ℝ) : ℝ :=
  if Rad = 0 then 0
  else sSup ((fun s : ℝ ↦ max (Rad / s - t / F s) 0) '' Set.Ioc 0 Rad)

/-- The convention `Phi_F(0, t) = 0`. -/
@[simp]
theorem offDiagonalRate_zero (F : ℝ → ℝ) (t : ℝ) : offDiagonalRate F 0 t = 0 := by
  rw [offDiagonalRate, ite_eq_left rfl]

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
  rw [offDiagonalRate, ite_eq_right hRad]
  exact le_csSup hbdd ⟨s, hs, rfl⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Process
