import SubdiffusiveProcess.Variational.WeightedL2

/-! # Scalar homogeneity of the actual weighted integral form -/

open MeasureTheory InnerProductSpace Filter
open scoped ENNReal
namespace SubdiffusiveProcess
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scaling the coefficient scales the integral form by the same scalar. -/
theorem weightedL2Form_smul (c : ℝ) (a : Lp ℝ ∞ μ) (u v : Lp E 2 μ) :
    weightedL2Form (c • a) u v = c * weightedL2Form a u v := by
  change inner ℝ (((ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holderL μ ∞ 2 2) (c • a) u) v = _
  rw [map_smul]
  change inner ℝ (c • ((ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holderL μ ∞ 2 2 a u)) v = _
  rw [real_inner_smul_left]
  rfl

/-- Almost-everywhere scalar coefficient comparison implies the same energy comparison. -/
theorem weightedL2Form_le_smul (c : ℝ) (a b : Lp ℝ ∞ μ)
    (hab : ∀ᵐ x ∂μ, a x ≤ c * b x) (u : Lp E 2 μ) :
    weightedL2Form a u u ≤ c * weightedL2Form b u u := by
  have h : ∀ᵐ x ∂μ, a x ≤ (c • b) x := by
    filter_upwards [hab, Lp.coeFn_smul c b] with x hx hc
    simpa only [hc, Pi.smul_apply, smul_eq_mul] using hx
  exact (weightedL2Form_mono h u).trans_eq (weightedL2Form_smul c b u u)

end SubdiffusiveProcess
