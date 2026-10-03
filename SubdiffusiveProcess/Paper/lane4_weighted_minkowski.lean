module

public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.Numeric
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace Paper



theorem lane4_weighted_minkowski :
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) (_hμ : IsProbabilityMeasure μ)
    (s q : ℝ), 0 < s → 1 ≤ q →
  ∀ (F : ℕ → Ω → ℝ) (B : ℕ → ℝ), (∀ k, 0 ≤ B k) →
    (∀ k, AEStronglyMeasurable (F k) μ) →
    (∀ k, eLpNorm (F k) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (B k)) →
  ∀ n : ℕ,
    eLpNorm (fun om => ∑ k ∈ Finset.range n,
        (3 : ℝ) ^ (-(s * (k : ℝ))) * F k om)
      (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (∑ k ∈ Finset.range n,
        B k * (3 : ℝ) ^ (-(s * (k : ℝ)))) := by
  intro Ω mΩ μ hμ s q hs hq F B hB hF hbound n
  let a : ℕ → ℝ := fun k => (3 : ℝ) ^ (-(s * (k : ℝ)))
  have ha_nonneg : ∀ k, 0 ≤ a k := by
    intro k
    dsimp [a]
    exact Real.rpow_nonneg (by norm_num) _
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    calc
      (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by norm_num
      _ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hq
  have hterm : ∀ k, eLpNorm (fun om => a k * F k om)
      (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (B k * a k) := by
    intro k
    calc
      eLpNorm (fun om => a k * F k om) (ENNReal.ofReal q) μ =
          ‖a k‖ₑ * eLpNorm (F k) (ENNReal.ofReal q) μ := by
        simpa only [Pi.smul_apply, smul_eq_mul] using!
          (eLpNorm_const_smul (a k) (F k) (ENNReal.ofReal q) μ)
      _ ≤ ‖a k‖ₑ * ENNReal.ofReal (B k) :=
        mul_le_mul_right (hbound k) _
      _ = ENNReal.ofReal (B k * a k) := by
        rw [Real.enorm_of_nonneg (ha_nonneg k)]
        rw [← ENNReal.ofReal_mul (ha_nonneg k)]
        congr 1
        ring
  change eLpNorm (fun om => ∑ k ∈ Finset.range n, a k * F k om)
      (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (∑ k ∈ Finset.range n, B k * a k)
  calc
    eLpNorm (fun om => ∑ k ∈ Finset.range n, a k * F k om)
        (ENNReal.ofReal q) μ ≤
        ∑ k ∈ Finset.range n, eLpNorm (fun om => a k * F k om)
          (ENNReal.ofReal q) μ := by
      rw [show (fun om => ∑ k ∈ Finset.range n, a k * F k om) =
          (∑ k ∈ Finset.range n, fun om => a k * F k om) by
            funext om
            simp]
      exact eLpNorm_sum_le (μ := μ) (p := ENNReal.ofReal q)
        (s := Finset.range n) (f := fun k om => a k * F k om)
        hp
    _ ≤ ∑ k ∈ Finset.range n, ENNReal.ofReal (B k * a k) := by
      exact Finset.sum_le_sum (fun k hk => hterm k)
    _ = ENNReal.ofReal (∑ k ∈ Finset.range n, B k * a k) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg (fun k hk => mul_nonneg (hB k) (ha_nonneg k))

end Paper
