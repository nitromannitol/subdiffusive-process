module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJSupport
public import SubdiffusiveProcess.Section5.HomogenizedCoefficientReciprocalLower

@[expose] public section

/-!
# The intrinsic clock pays the Euclidean scale at every triadic radius

At a negative integer scale the clock uses `ahom M 0`; at a nonnegative
integer scale it uses the corresponding homogenized coefficient. Both
coefficients lie in `(0, 1]`, so the clock is at least the squared radius.
-/

set_option autoImplicit false
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The intrinsic clock at an integer triadic scale, including negative scales. -/
theorem goodCube_timeScale_triadic_int (a : ℕ → ℝ) (m : ℤ) :
    Section7Process.timeScale a ((3 : ℝ) ^ m) =
      ((3 : ℝ) ^ m) ^ 2 / a m.toNat := by
  by_cases hm : 0 ≤ m
  · lift m to ℕ using hm with k
    simp only [Int.toNat_natCast, zpow_natCast,
      Section7Process.timeScale_triadic, Section7Process.timeScaleTriadic]
    rw [← pow_mul, Nat.mul_comm k 2]
  · have hm0 : m ≤ 0 := le_of_lt (lt_of_not_ge hm)
    have hr : (3 : ℝ) ^ m ≤ 1 :=
      (zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 3)).2 hm0
    rw [Section7Process.timeScale_of_le_one a hr, Int.toNat_of_nonpos hm0]

/-- The actual intrinsic clock dominates the Euclidean squared radius. -/
theorem goodCube_sq_triadic_le_clock {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℤ) :
    ((3 : ℝ) ^ m) ^ 2 ≤ Section7Process.timeScale (ahom M) ((3 : ℝ) ^ m) := by
  rw [goodCube_timeScale_triadic_int]
  have ha : 0 < ahom M m.toNat :=
    (Real.exp_pos _).trans_le
      (_root_.SubdiffusiveProcess.Section5.homogenized_coefficient_reciprocal_lower M m.toNat)
  exact (le_div_iff₀ ha).2 (by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (ahom_le_one M m.toNat) (sq_nonneg ((3 : ℝ) ^ m)))

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
