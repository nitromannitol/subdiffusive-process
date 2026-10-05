module

public import SubdiffusiveProcess.Variational.LocalizedL2
public import SubdiffusiveProcess.Variational.RelativeAlgebra
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! # Relative changes of a nonconstant coefficient

Young's inequality controls the actual difference of two weighted integral
forms relative to the first coefficient. The local version retains the
original coefficient's energy on the changed set and needs no square-root
change of Hilbert space.
-/

open MeasureTheory InnerProductSpace Filter
open scoped ENNReal
namespace SubdiffusiveProcess

/-- Young's inequality in the form used to absorb half the difference energy. -/
theorem relative_young_mul (δ u v : ℝ) {c : ℝ} (hc : 0 < c) :
    δ * |u * v| ≤ δ ^ 2 / (2 * c) * u ^ 2 + c / 2 * v ^ 2 := by
  have he : δ ^ 2 / (2 * c) * u ^ 2 + c / 2 * v ^ 2 =
      (δ ^ 2 * u ^ 2 + c ^ 2 * v ^ 2) / (2 * c) := by
    field_simp
  rw [he]
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hc)).mpr
  have hs := sq_nonneg (δ * |u| - c * |v|)
  simp only [sub_sq, mul_pow, sq_abs] at hs
  rw [abs_mul]
  nlinarith

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A relative coefficient bound controls the full pairing by two weighted energies. -/
theorem weightedL2Form_difference_young (a b : Lp ℝ ∞ μ) {δ c : ℝ}
    (hc : 0 < c) (ha : ∀ᵐ x ∂μ, 0 ≤ a x)
    (hab : ∀ᵐ x ∂μ, |b x - a x| ≤ δ * a x) (u v : Lp ℝ 2 μ) :
    |weightedL2Form b u v - weightedL2Form a u v| ≤
      δ ^ 2 / (2 * c) * weightedL2Form a u u + c / 2 * weightedL2Form a v v := by
  rw [weightedL2Form_apply, weightedL2Form_apply,
    ← integral_sub (integrable_weighted_inner b u v) (integrable_weighted_inner a u v)]
  calc
    |∫ x, b x * inner ℝ (u x) (v x) - a x * inner ℝ (u x) (v x) ∂μ|
        ≤ ∫ x, |b x * inner ℝ (u x) (v x) - a x * inner ℝ (u x) (v x)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, δ ^ 2 / (2 * c) * (a x * inner ℝ (u x) (u x)) +
        c / 2 * (a x * inner ℝ (v x) (v x)) ∂μ := by
      apply integral_mono_ae
        ((integrable_weighted_inner b u v).sub (integrable_weighted_inner a u v)).norm
        (((integrable_weighted_inner a u u).const_mul _).add
          ((integrable_weighted_inner a v v).const_mul _))
      filter_upwards [ha, hab] with x hx hd
      simp only [Pi.sub_apply, Pi.add_apply, Real.norm_eq_abs]
      rw [← sub_mul, abs_mul]
      calc
        _ ≤ (δ * a x) * |inner ℝ (u x) (v x)| :=
          mul_le_mul_of_nonneg_right hd (abs_nonneg _)
        _ = a x * (δ * |u x * v x|) := by
          simp only [RCLike.inner_apply, conj_trivial, abs_mul]
          ring
        _ ≤ a x * (δ ^ 2 / (2 * c) * (u x) ^ 2 + c / 2 * (v x) ^ 2) :=
          mul_le_mul_of_nonneg_left (relative_young_mul δ (u x) (v x) hc) hx
        _ = _ := by
          simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
          ring
    _ = _ := by
      rw [integral_add ((integrable_weighted_inner a u u).const_mul _)
        ((integrable_weighted_inner a v v).const_mul _), integral_const_mul, integral_const_mul,
        weightedL2Form_apply, weightedL2Form_apply]

/-- A coefficient difference supported in s only tests the first vector inside s. -/
theorem weightedL2Form_difference_localize_left (a b : Lp ℝ ∞ μ) {s : Set α}
    (hs : MeasurableSet s) (hsupp : ∀ᵐ x ∂μ, x ∉ s → b x = a x) (u v : Lp ℝ 2 μ) :
    weightedL2Form b u v - weightedL2Form a u v =
      weightedL2Form b (localizeL2 hs u) v - weightedL2Form a (localizeL2 hs u) v := by
  simp only [weightedL2Form_apply]
  rw [← integral_sub (integrable_weighted_inner b u v) (integrable_weighted_inner a u v),
    ← integral_sub (integrable_weighted_inner b (localizeL2 hs u) v)
      (integrable_weighted_inner a (localizeL2 hs u) v)]
  apply integral_congr_ae
  filter_upwards [hsupp, localizeL2_coeFn hs u] with x hz he
  rw [he]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
  · simp only [hz hx, sub_self, Set.indicator_of_notMem hx, inner_zero_left, mul_zero]

/-- The localized relative Young inequality keeps the old solution's local energy. -/
theorem weightedL2Form_difference_young_local (a b : Lp ℝ ∞ μ) {s : Set α}
    (hs : MeasurableSet s) {δ c : ℝ} (hc : 0 < c)
    (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (hab : ∀ᵐ x ∂μ, |b x - a x| ≤ δ * a x)
    (hsupp : ∀ᵐ x ∂μ, x ∉ s → b x = a x) (u v : Lp ℝ 2 μ) :
    |weightedL2Form b u v - weightedL2Form a u v| ≤
      δ ^ 2 / (2 * c) * weightedL2Form a (localizeL2 hs u) (localizeL2 hs u) +
        c / 2 * weightedL2Form a v v := by
  rw [weightedL2Form_difference_localize_left a b hs hsupp]
  exact weightedL2Form_difference_young a b hc ha hab _ _

/-- Nonnegative coefficients have nonnegative quadratic energies. -/
theorem weightedL2Form_nonneg (a : Lp ℝ ∞ μ) (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (u : Lp ℝ 2 μ) :
    0 ≤ weightedL2Form a u u := by
  simpa only [zero_mul] using weightedL2Form_lower a ha u

/-- Local energy for a nonnegative coefficient is at most its global energy. -/
theorem weightedL2Form_localize_le (a : Lp ℝ ∞ μ) {s : Set α}
    (hs : MeasurableSet s) (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (u : Lp ℝ 2 μ) :
    weightedL2Form a (localizeL2 hs u) (localizeL2 hs u) ≤ weightedL2Form a u u := by
  rw [weightedL2Form_apply, weightedL2Form_apply]
  apply integral_mono_ae (integrable_weighted_inner a _ _) (integrable_weighted_inner a _ _)
  filter_upwards [ha, localizeL2_coeFn hs u] with x hx he
  rw [he]
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs]
  · simp only [Set.indicator_of_notMem hxs, inner_zero_left, mul_zero]
    exact mul_nonneg hx real_inner_self_nonneg

/-- On one vector the relative coefficient error is linear in its size. -/
theorem weightedL2Form_difference_self_le (a b : Lp ℝ ∞ μ) {δ : ℝ}
    (hab : ∀ᵐ x ∂μ, |b x - a x| ≤ δ * a x) (u : Lp ℝ 2 μ) :
    |weightedL2Form b u u - weightedL2Form a u u| ≤ δ * weightedL2Form a u u := by
  rw [weightedL2Form_apply, weightedL2Form_apply,
    ← integral_sub (integrable_weighted_inner b u u) (integrable_weighted_inner a u u)]
  calc
    _ ≤ ∫ x, |b x * inner ℝ (u x) (u x) - a x * inner ℝ (u x) (u x)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, δ * (a x * inner ℝ (u x) (u x)) ∂μ := by
      apply integral_mono_ae
        ((integrable_weighted_inner b u u).sub (integrable_weighted_inner a u u)).norm
        ((integrable_weighted_inner a u u).const_mul δ)
      filter_upwards [hab] with x hx
      simp only [Pi.sub_apply, Real.norm_eq_abs]
      rw [← sub_mul, abs_mul, abs_of_nonneg real_inner_self_nonneg]
      exact (mul_le_mul_of_nonneg_right hx real_inner_self_nonneg).trans_eq (mul_assoc _ _ _)
    _ = _ := by rw [integral_const_mul]

/-- The diagonal coefficient error uses only the old energy on the changed set. -/
theorem weightedL2Form_difference_self_le_local (a b : Lp ℝ ∞ μ) {s : Set α}
    (hs : MeasurableSet s) {δ : ℝ} (hab : ∀ᵐ x ∂μ, |b x - a x| ≤ δ * a x)
    (hsupp : ∀ᵐ x ∂μ, x ∉ s → b x = a x) (u : Lp ℝ 2 μ) :
    |weightedL2Form b u u - weightedL2Form a u u| ≤
      δ * weightedL2Form a (localizeL2 hs u) (localizeL2 hs u) := by
  rw [weightedL2Form_difference_localize_left a b hs hsupp u u,
    weightedL2Form_symm b (localizeL2 hs u) u, weightedL2Form_symm a (localizeL2 hs u) u,
    weightedL2Form_difference_localize_left a b hs hsupp u (localizeL2 hs u)]
  exact weightedL2Form_difference_self_le a b hab _

/-- Local quadratic control is proved once on scalar L2 before summing coordinates. -/
theorem weightedL2Form_localize_sub_le (a : Lp ℝ ∞ μ) {s : Set α}
    (hs : MeasurableSet s) (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (u v : Lp ℝ 2 μ) :
    weightedL2Form a (localizeL2 hs u) (localizeL2 hs u) ≤
      2 * weightedL2Form a (localizeL2 hs v) (localizeL2 hs v) +
        2 * weightedL2Form a (localizeL2 hs (u - v)) (localizeL2 hs (u - v)) := by
  have h := bilinear_quadratic_sub_le (weightedL2Form (E := ℝ) a)
    (weightedL2Form_symm a) (weightedL2Form_nonneg a ha)
    (localizeL2 hs u) (localizeL2 hs v)
  simpa only [localizeL2_sub] using h

end SubdiffusiveProcess
