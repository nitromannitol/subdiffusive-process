import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Tactic.Linarith

/-!
# Weighted integral forms on vector fields

The bilinear form is the actual integral of a bounded scalar weight times
the pointwise inner product. With base measure A dx and vectors equal to
Sobolev gradients this is the finite-cutoff energy. The identification of
the admissible Sobolev gradient spaces is a separate obligation.
-/

open MeasureTheory InnerProductSpace Filter
open scoped ENNReal
namespace SubdiffusiveProcess
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual integral form on square-integrable vector fields with a bounded scalar weight. -/
noncomputable def weightedL2Form (a : Lp ℝ ∞ μ) :
    Lp E 2 μ →L[ℝ] Lp E 2 μ →L[ℝ] ℝ :=
  (innerSL ℝ).comp ((ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holderL μ ∞ 2 2 a)

/-- The bounded-operator construction is exactly the weighted integral. -/
theorem weightedL2Form_apply (a : Lp ℝ ∞ μ) (u v : Lp E 2 μ) :
    weightedL2Form a u v = ∫ x, a x * inner ℝ (u x) (v x) ∂μ := by
  change inner ℝ ((ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holder 2 a u) v = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ (E := E)).coeFn_holder (r := 2) a u] with x hx
  rw [hx]
  simp only [ContinuousLinearMap.lsmul_apply, real_inner_smul_left]

/-- Weighted pairings are integrable; no undefined-integral convention is used. -/
theorem integrable_weighted_inner (a : Lp ℝ ∞ μ) (u v : Lp E 2 μ) :
    Integrable (fun x => a x * inner ℝ (u x) (v x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ)
    ((ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holder 2 a u) v).congr
  filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ (E := E)).coeFn_holder (r := 2) a u] with x hx
  rw [hx]
  simp only [ContinuousLinearMap.lsmul_apply, real_inner_smul_left]

/-- Real scalar weights give symmetric forms. -/
theorem weightedL2Form_symm (a : Lp ℝ ∞ μ) (u v : Lp E 2 μ) :
    weightedL2Form a u v = weightedL2Form a v u := by
  simp only [weightedL2Form_apply, real_inner_comm (u _) (v _)]

/-- Pointwise lower ellipticity passes to the actual L2 quadratic form. -/
theorem weightedL2Form_lower (a : Lp ℝ ∞ μ) {c : ℝ}
    (ha : ∀ᵐ x ∂μ, c ≤ a x) (u : Lp E 2 μ) :
    c * ‖u‖ ^ 2 ≤ weightedL2Form a u u := by
  rw [← real_inner_self_eq_norm_sq u, L2.inner_def, ← integral_const_mul,
    weightedL2Form_apply]
  apply integral_mono_ae ((L2.integrable_inner (𝕜 := ℝ) u u).const_mul c)
    (integrable_weighted_inner a u u)
  filter_upwards [ha] with x hx
  exact mul_le_mul_of_nonneg_right hx real_inner_self_nonneg

/-- Pointwise upper ellipticity bounds the L2 quadratic form. -/
theorem weightedL2Form_upper (a : Lp ℝ ∞ μ) {c : ℝ}
    (ha : ∀ᵐ x ∂μ, a x ≤ c) (u : Lp E 2 μ) :
    weightedL2Form a u u ≤ c * ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq u, L2.inner_def, ← integral_const_mul,
    weightedL2Form_apply]
  apply integral_mono_ae (integrable_weighted_inner a u u)
    ((L2.integrable_inner (𝕜 := ℝ) u u).const_mul c)
  filter_upwards [ha] with x hx
  exact mul_le_mul_of_nonneg_right hx real_inner_self_nonneg

/-- A uniform positive lower bound makes the weighted integral coercive. -/
theorem weightedL2Form_coercive (a : Lp ℝ ∞ μ) {c : ℝ} (hc : 0 < c)
    (ha : ∀ᵐ x ∂μ, c ≤ a x) : IsCoercive (weightedL2Form (E := E) a) := by
  refine ⟨c, hc, fun u => ?_⟩
  simpa only [pow_two, mul_assoc] using weightedL2Form_lower a ha u

/-- Pointwise coefficient order implies quadratic-form order. -/
theorem weightedL2Form_mono {a b : Lp ℝ ∞ μ} (hab : ∀ᵐ x ∂μ, a x ≤ b x)
    (u : Lp E 2 μ) : weightedL2Form a u u ≤ weightedL2Form b u u := by
  rw [weightedL2Form_apply, weightedL2Form_apply]
  apply integral_mono_ae (integrable_weighted_inner a u u) (integrable_weighted_inner b u u)
  filter_upwards [hab] with x hx
  exact mul_le_mul_of_nonneg_right hx real_inner_self_nonneg

end SubdiffusiveProcess
