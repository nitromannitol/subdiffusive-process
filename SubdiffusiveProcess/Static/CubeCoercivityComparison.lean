import SubdiffusiveProcess.Static.DyadicCoercivityAssembly
import SubdiffusiveProcess.Static.Comparison

/-! # Monotone scalar transport of individual cube coercivity -/

open MeasureTheory Homogenization SubdiffusiveProcess.Static
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Scalar coefficient comparison preserves both native coercivity clauses. -/
theorem cubeCoercivityEstimates_of_comparison {d : ℕ} {A0 A1 : Vec d → ℝ}
    {y : Vec d} {s K F : ℝ} (hK : 0 ≤ K) (hF : 1 ≤ F)
    (hA : ∀ x ∈ Metric.ball y (s / 2), A0 x ≤ F * A1 x)
    (h : cubeCoercivityEstimates A0 y s K) :
    cubeCoercivityEstimates A1 y s (K * F) := by
  constructor
  · intro H
    have hE := energy_le_mul measurableSet_ball (zero_le_one.trans hF) hA H.grad
    have hL : (∫⁻ x in Metric.ball y (s / 2), ENNReal.ofReal (H.toFun x ^ 2)) ≤
        ENNReal.ofReal F * ∫⁻ x in Metric.ball y (s / 2), ENNReal.ofReal (H.toFun x ^ 2) := by
      simpa only [one_mul] using mul_le_mul_left (ENNReal.one_le_ofReal.mpr hF)
        (∫⁻ x in Metric.ball y (s / 2), ENNReal.ofReal (H.toFun x ^ 2))
    refine ((h.1 H).trans (mul_le_mul_right (add_le_add hE hL) _)).trans_eq ?_
    rw [← mul_add, ← mul_assoc, ← ENNReal.ofReal_mul hK]
  · intro H
    have hE := energy_le_mul measurableSet_ball (zero_le_one.trans hF) hA H.grad
    refine ((h.2 H).trans (mul_le_mul_right hE _)).trans_eq ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul hK]

/-- Arbitrary a.e. value representatives have the same literal fractional
squared norm, including its double lower integral. -/
theorem fractionalSqNorm_congr_ae {d : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hfg : f =ᵐ[volume.restrict U] g) : fractionalSqNorm U f = fractionalSqNorm U g := by
  apply congrArg₂ (· + ·)
  · apply lintegral_congr_ae
    filter_upwards [hfg] with x hx
    apply lintegral_congr_ae
    filter_upwards [hfg] with z hz
    rw [hx, hz]
  · apply lintegral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]

end SubdiffusiveProcess.Static
