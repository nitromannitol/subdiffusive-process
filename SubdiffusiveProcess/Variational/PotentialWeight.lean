module

public import SubdiffusiveProcess.Variational.WeightedL2
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Bounded potential weights

A measurable potential bounded in absolute value by S produces an actual
L-infinity coefficient exp(g), with bounds exp(-S), exp(S) and
|exp(g)-1| <= S exp(S). Outside the changed set its value is exactly one
almost everywhere. This realizes the coefficient hypotheses of the
localized perturbation estimates without assuming them separately.
-/

open MeasureTheory Filter
open scoped ENNReal
namespace SubdiffusiveProcess

/-- A bounded potential gives the finite perturbation size used in localized estimates. -/
theorem abs_exp_sub_one_le_bound {x S : ℝ} (hx : |x| ≤ S) :
    |Real.exp x - 1| ≤ S * Real.exp S := by
  have h : |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
    by_cases hp : 0 ≤ x
    · rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hp)), abs_of_nonneg hp]
      have hneg := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_nonneg x)
      have he : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      rw [he] at hneg
      nlinarith
    · have hm : x ≤ 0 := le_of_not_ge hp
      have hem : Real.exp x ≤ 1 := by
        simpa only [Real.exp_zero] using Real.exp_monotone hm
      rw [abs_of_nonpos (sub_nonpos.mpr hem), abs_of_nonpos hm]
      calc
        -(Real.exp x - 1) ≤ -x := by linarith [Real.add_one_le_exp x]
        _ ≤ -x * Real.exp (-x) := le_mul_of_one_le_right (neg_nonneg.mpr hm)
          (Real.one_le_exp (neg_nonneg.mpr hm))
  exact h.trans (mul_le_mul hx (Real.exp_monotone hx) (Real.exp_nonneg _) (abs_nonneg _ |>.trans hx))

/-- The exponential potential is realized in L-infinity with all coefficient bounds proved. -/
theorem exists_bounded_exp_weight {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : α → ℝ) (hg : AEStronglyMeasurable g μ) {S : ℝ}
    (hS : ∀ᵐ x ∂μ, |g x| ≤ S) {s : Set α}
    (hsupp : ∀ᵐ x ∂μ, x ∉ s → g x = 0) :
    ∃ a : Lp ℝ ∞ μ,
      (∀ᵐ x ∂μ, a x = Real.exp (g x)) ∧
      (∀ᵐ x ∂μ, Real.exp (-S) ≤ a x) ∧
      (∀ᵐ x ∂μ, a x ≤ Real.exp S) ∧
      (∀ᵐ x ∂μ, |a x - 1| ≤ S * Real.exp S) ∧
      (∀ᵐ x ∂μ, x ∉ s → a x = 1) := by
  have hge : AEStronglyMeasurable (fun x => Real.exp (g x)) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable hg
  have hm : MemLp (fun x => Real.exp (g x)) ∞ μ :=
    memLp_top_of_bound hge (Real.exp S) (by
      filter_upwards [hS] with x hx
      simpa only [Real.norm_eq_abs, Real.abs_exp] using
        Real.exp_monotone ((le_abs_self (g x)).trans hx))
  let a := hm.toLp (fun x => Real.exp (g x))
  have hae : ∀ᵐ x ∂μ, a x = Real.exp (g x) := hm.coeFn_toLp
  refine ⟨a, hae, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hae, hS] with x he hx
    rw [he]
    exact Real.exp_monotone (abs_le.mp hx).1
  · filter_upwards [hae, hS] with x he hx
    rw [he]
    exact Real.exp_monotone (abs_le.mp hx).2
  · filter_upwards [hae, hS] with x he hx
    rw [he]
    exact abs_exp_sub_one_le_bound hx
  · filter_upwards [hae, hsupp] with x he hx
    intro hxs
    rw [he, hx hxs, Real.exp_zero]

end SubdiffusiveProcess
