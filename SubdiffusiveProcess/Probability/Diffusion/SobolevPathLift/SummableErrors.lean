module

public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.PathLift

@[expose] public section

/-!
# a.e. summability of errors from weighted square estimates

  §2.3, Steps 2–3,
No single Mathlib lemma takes a sequence of
`L²`-type bounds to a.e. uniform convergence; the standard route is Chebyshev plus Borel–Cantelli.

**Borel–Cantelli is not needed.**  The whole content is Tonelli plus `ae_lt_top'`:

```text
∫ (∑ₖ (2ᵏ Dₖ)²) = ∑ₖ 4ᵏ ∫ Dₖ²  < ∞   ⟹   ∑ₖ (2ᵏ Dₖ)² < ∞ a.e.
```

and then `Dₖ = (2ᵏDₖ)·2⁻ᵏ ≤ (2ᵏDₖ)² + 4⁻ᵏ` gives `∑ₖ Dₖ < ∞` a.e. by comparison with a convergent
geometric series.  No measure of a level set is ever formed, so no Chebyshev step and no
Borel–Cantelli step appear, and — importantly for this application — **nothing requires the measure
to be finite or even σ-finite**, which is what the two-parameter `(x, ω)` measure
`pathMeasure = volume.bind (laplacianContinuousLaw d)` is not.

The statement is deliberately measure- and space-agnostic: it is about any `ℝ≥0∞`-valued sequence
whose weighted square integrals are summable, so any argument needing "square bounds ⟹ a.e. summable
errors" can cite it.
-/

set_option autoImplicit false

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift

/-- `a·b ≤ a² + b²` in `ℝ≥0∞`, where the sharper `2ab ≤ a² + b²` is unavailable for want of
subtraction. -/
theorem ennreal_mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

/-- `2 ^ (k · 2) = 4 ^ k` in `ℝ≥0∞`. -/
theorem two_pow_mul_two (k : ℕ) : (2 : ℝ≥0∞) ^ (k * 2) = (4 : ℝ≥0∞) ^ k := by
  rw [mul_comm, pow_mul]
  norm_num

theorem tsum_geometric_four_inv_ne_top : (∑' k : ℕ, ((4 : ℝ≥0∞)⁻¹) ^ k) ≠ ⊤ := by
  rw [ENNReal.tsum_geometric]
  refine ENNReal.inv_ne_top.mpr ?_
  have h : (4 : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_lt_one.mpr (by norm_num)
  exact fun hc => absurd (tsub_eq_zero_iff_le.mp hc) (not_le.mpr h)

/-- **Square bounds give a.e. summable errors.**  No finiteness of `μ` is used. -/
theorem ae_tsum_lt_top_of_lintegral_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : ℕ → Ω → ℝ≥0∞} (hD : ∀ k, AEMeasurable (D k) μ)
    (hsum : (∑' k : ℕ, (4 : ℝ≥0∞) ^ k * ∫⁻ ω, (D k ω) ^ 2 ∂μ) ≠ ⊤) :
    ∀ᵐ ω ∂μ, (∑' k : ℕ, D k ω) ≠ ⊤ := by
  -- the weighted squares are integrable, hence a.e. summable
  have hmeas : ∀ k : ℕ, AEMeasurable (fun ω => ((2 : ℝ≥0∞) ^ k * D k ω) ^ 2) μ := fun k =>
    ((aemeasurable_const.mul (hD k)).pow_const 2)
  have hlint : (∫⁻ ω, ∑' k : ℕ, ((2 : ℝ≥0∞) ^ k * D k ω) ^ 2 ∂μ)
      = ∑' k : ℕ, (4 : ℝ≥0∞) ^ k * ∫⁻ ω, (D k ω) ^ 2 ∂μ := by
    rw [lintegral_tsum hmeas]
    refine tsum_congr fun k => ?_
    have hrw : ∀ ω, ((2 : ℝ≥0∞) ^ k * D k ω) ^ 2 = (4 : ℝ≥0∞) ^ k * (D k ω) ^ 2 := by
      intro ω
      rw [mul_pow, ← pow_mul, two_pow_mul_two]
    simp only [hrw]
    exact lintegral_const_mul' _ _ (by simp)
  have hfin : (∫⁻ ω, ∑' k : ℕ, ((2 : ℝ≥0∞) ^ k * D k ω) ^ 2 ∂μ) ≠ ⊤ := by
    rw [hlint]; exact hsum
  have hae := ae_lt_top' (AEMeasurable.tsum hmeas) hfin
  filter_upwards [hae] with ω hω
  -- compare termwise with the weighted squares plus a geometric series
  have hcmp : ∀ k : ℕ, D k ω ≤ ((2 : ℝ≥0∞) ^ k * D k ω) ^ 2 + ((4 : ℝ≥0∞)⁻¹) ^ k := by
    intro k
    have h2 : ((2 : ℝ≥0∞) ^ k * D k ω) * ((2 : ℝ≥0∞) ^ k)⁻¹ = D k ω := by
      rw [mul_comm ((2 : ℝ≥0∞) ^ k) (D k ω), mul_assoc,
        ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]
    have h3 : (((2 : ℝ≥0∞) ^ k)⁻¹) ^ 2 = ((4 : ℝ≥0∞)⁻¹) ^ k := by
      rw [← ENNReal.inv_pow, ← ENNReal.inv_pow, ← pow_mul, two_pow_mul_two]
    calc D k ω = ((2 : ℝ≥0∞) ^ k * D k ω) * ((2 : ℝ≥0∞) ^ k)⁻¹ := h2.symm
      _ ≤ ((2 : ℝ≥0∞) ^ k * D k ω) ^ 2 + (((2 : ℝ≥0∞) ^ k)⁻¹) ^ 2 :=
          ennreal_mul_le_sq_add_sq _ _
      _ = ((2 : ℝ≥0∞) ^ k * D k ω) ^ 2 + ((4 : ℝ≥0∞)⁻¹) ^ k := by rw [h3]
  have hle : (∑' k : ℕ, D k ω)
      ≤ (∑' k : ℕ, ((2 : ℝ≥0∞) ^ k * D k ω) ^ 2) + ∑' k : ℕ, ((4 : ℝ≥0∞)⁻¹) ^ k := by
    rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum hcmp
  refine ne_top_of_le_ne_top ?_ hle
  exact ENNReal.add_ne_top.mpr ⟨hω.ne, tsum_geometric_four_inv_ne_top⟩

end SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift
