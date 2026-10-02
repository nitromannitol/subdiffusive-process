import SubdiffusiveProcess.Variational.WeightedL2
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring

/-!
# Localized coefficient perturbations

Restriction by a measurable indicator is constructed in actual L2. Its
squared norm is the set integral of squared pointwise norms. The difference
between a weighted form and the unweighted inner product depends only on
the coefficient's changed set, and obeys a localized Cauchy--Schwarz bound.
These are the integral estimates used in Lemma 28, E033.
-/

open MeasureTheory InnerProductSpace Filter
open scoped ENNReal
namespace SubdiffusiveProcess
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Restriction of a vector field to a measurable set, extended by zero. -/
noncomputable def localizeL2 {s : Set α} (hs : MeasurableSet s) (u : Lp E 2 μ) : Lp E 2 μ :=
  ((Lp.memLp u).indicator hs).toLp (s.indicator u)

omit [InnerProductSpace ℝ E] in
/-- The localized L2 vector is the indicator product almost everywhere. -/
theorem localizeL2_coeFn {s : Set α} (hs : MeasurableSet s) (u : Lp E 2 μ) :
    localizeL2 hs u =ᵐ[μ] s.indicator u := MemLp.coeFn_toLp _

/-- The norm of the localized vector is exactly the local energy. -/
theorem localizeL2_norm_sq {s : Set α} (hs : MeasurableSet s) (u : Lp E 2 μ) :
    ‖localizeL2 hs u‖ ^ 2 = ∫ x in s, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [localizeL2_coeFn hs u] with x hx
  rw [hx]
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs, real_inner_self_eq_norm_sq]
  · simp only [Set.indicator_of_notMem hxs, inner_zero_left]

omit [InnerProductSpace ℝ E] in
/-- Localization does not increase the global L2 norm. -/
theorem localizeL2_norm_le {s : Set α} (hs : MeasurableSet s) (u : Lp E 2 μ) :
    ‖localizeL2 hs u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [localizeL2_coeFn hs u] with x hx
  rw [hx]
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx, le_refl]
  · simp only [Set.indicator_of_notMem hx, norm_zero, norm_nonneg]

omit [InnerProductSpace ℝ E] in
/-- Localization is linear on differences. -/
theorem localizeL2_sub {s : Set α} (hs : MeasurableSet s) (u v : Lp E 2 μ) :
    localizeL2 hs (u - v) = localizeL2 hs u - localizeL2 hs v := by
  apply Lp.ext
  filter_upwards [localizeL2_coeFn hs (u - v), Lp.coeFn_sub u v,
    Lp.coeFn_sub (localizeL2 hs u) (localizeL2 hs v), localizeL2_coeFn hs u,
    localizeL2_coeFn hs v] with x h1 h2 h3 h4 h5
  simp only [h1, h3, Pi.sub_apply, h4, h5]
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx, h2, Pi.sub_apply]
  · simp only [Set.indicator_of_notMem hx, sub_self]

/-- The norm of a coefficient perturbation depends only on energy in its support. -/
theorem weighted_multiplier_sub_norm_le (a : Lp ℝ ∞ μ) {s : Set α}
    (hs : MeasurableSet s) {δ : ℝ}
    (ha : ∀ᵐ x ∂μ, |a x - 1| ≤ δ)
    (hsupp : ∀ᵐ x ∂μ, x ∉ s → a x = 1) (u : Lp E 2 μ) :
    ‖(ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holder 2 a u - u‖ ≤
      δ * ‖localizeL2 hs u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ (E := E)).coeFn_holder (r := 2) a u,
    Lp.coeFn_sub ((ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holder 2 a u) u,
    localizeL2_coeFn hs u, ha, hsupp] with x hm hd hl hb hz
  simp only [hd, Pi.sub_apply, hm, ContinuousLinearMap.lsmul_apply, hl]
  by_cases hx : x ∈ s
  · have he : a x • u x - u x = (a x - 1) • u x := by rw [sub_smul, one_smul]
    rw [Set.indicator_of_mem hx, he, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg (u x))
  · simp only [hz hx, one_smul, sub_self, norm_zero, Set.indicator_of_notMem hx,
      mul_zero, le_refl]

/-- Localized Cauchy--Schwarz for the actual difference of weighted energy forms. -/
theorem weightedL2Form_sub_inner_le_global (a : Lp ℝ ∞ μ) {s : Set α}
    (hs : MeasurableSet s) {δ : ℝ}
    (ha : ∀ᵐ x ∂μ, |a x - 1| ≤ δ)
    (hsupp : ∀ᵐ x ∂μ, x ∉ s → a x = 1) (u v : Lp E 2 μ) :
    |weightedL2Form a u v - inner ℝ u v| ≤ δ * ‖localizeL2 hs u‖ * ‖v‖ := by
  change |inner ℝ ((ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holder 2 a u) v -
    inner ℝ u v| ≤ _
  rw [← inner_sub_left]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (weighted_multiplier_sub_norm_le a hs ha hsupp u)
      (norm_nonneg v))

/-- The perturbation form vanishes outside the coefficient's changed set. -/
theorem weightedL2Form_sub_inner_localize_right (a : Lp ℝ ∞ μ) {s : Set α}
    (hs : MeasurableSet s) (hsupp : ∀ᵐ x ∂μ, x ∉ s → a x = 1)
    (u v : Lp E 2 μ) :
    weightedL2Form a u v - inner ℝ u v =
      weightedL2Form a u (localizeL2 hs v) - inner ℝ u (localizeL2 hs v) := by
  simp only [weightedL2Form_apply, L2.inner_def]
  rw [← integral_sub (integrable_weighted_inner a u v) (L2.integrable_inner u v),
    ← integral_sub (integrable_weighted_inner a u (localizeL2 hs v))
      (L2.integrable_inner u (localizeL2 hs v))]
  apply integral_congr_ae
  filter_upwards [hsupp, localizeL2_coeFn hs v] with x hz hv
  rw [hv]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
  · simp only [hz hx, one_mul, sub_self, Set.indicator_of_notMem hx]

/-- Both arguments in the perturbation pairing can be localized. -/
theorem weightedL2Form_sub_inner_le (a : Lp ℝ ∞ μ) {s : Set α}
    (hs : MeasurableSet s) {δ : ℝ}
    (ha : ∀ᵐ x ∂μ, |a x - 1| ≤ δ)
    (hsupp : ∀ᵐ x ∂μ, x ∉ s → a x = 1) (u v : Lp E 2 μ) :
    |weightedL2Form a u v - inner ℝ u v| ≤
      δ * ‖localizeL2 hs u‖ * ‖localizeL2 hs v‖ := by
  rw [weightedL2Form_sub_inner_localize_right a hs hsupp u v]
  exact weightedL2Form_sub_inner_le_global a hs ha hsupp u (localizeL2 hs v)

/-- The localized weighted quadratic form is the actual local integral energy. -/
theorem weightedL2Form_localize_self (a : Lp ℝ ∞ μ) {s : Set α}
    (hs : MeasurableSet s) (u : Lp E 2 μ) :
    weightedL2Form a (localizeL2 hs u) (localizeL2 hs u) =
      ∫ x in s, a x * ‖u x‖ ^ 2 ∂μ := by
  rw [weightedL2Form_apply, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [localizeL2_coeFn hs u] with x hx
  rw [hx]
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs, real_inner_self_eq_norm_sq]
  · simp only [Set.indicator_of_notMem hxs, inner_zero_left, mul_zero]

end SubdiffusiveProcess
