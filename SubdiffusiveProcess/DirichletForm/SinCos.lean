/-
# The rescaled sine and cosine used in the energy-measure order argument
-/
import SubdiffusiveProcess.DirichletForm.EnergyMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The rescaled sine and cosine

The comparison of energy measures from a comparison of forms uses the pair of
`C¹` functions `Φ_k^s(t) = k⁻¹ sin (k t)` and `Φ_k^c(t) = k⁻¹ cos (k t)`.  They
are bounded by `k⁻¹`, their derivatives have squares summing to `1`, and the
cross terms `Φ Φ'` of the two cancel, which is exactly what makes the Leibniz
rule collapse to `∫ v² dΓ(u) + k⁻² E(v)`.

This file records those identities.  They are pure real analysis and are stated
for their own sake; nothing here mentions a Dirichlet form.
-/

open Real

noncomputable section

namespace DirichletForm

/-- The rescaled sine `Φ_k^s(t) = k⁻¹ sin (k t)`. -/
def sinScaled (k t : ℝ) : ℝ := k⁻¹ * Real.sin (k * t)

/-- The rescaled cosine `Φ_k^c(t) = k⁻¹ cos (k t)`. -/
def cosScaled (k t : ℝ) : ℝ := k⁻¹ * Real.cos (k * t)

@[simp] theorem sinScaled_zero (k : ℝ) : sinScaled k 0 = 0 := by simp [sinScaled]

theorem cosScaled_zero (k : ℝ) : cosScaled k 0 = k⁻¹ := by simp [cosScaled]

theorem hasDerivAt_sinScaled (k t : ℝ) :
    HasDerivAt (sinScaled k) (k⁻¹ * (Real.cos (k * t) * k)) t := by
  have h1 : HasDerivAt (fun s : ℝ => k * s) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  simpa [sinScaled, Function.comp] using
    ((Real.hasDerivAt_sin (k * t)).comp t h1).const_mul k⁻¹

theorem hasDerivAt_cosScaled (k t : ℝ) :
    HasDerivAt (cosScaled k) (k⁻¹ * (-Real.sin (k * t) * k)) t := by
  have h1 : HasDerivAt (fun s : ℝ => k * s) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  simpa [cosScaled, Function.comp] using
    ((Real.hasDerivAt_cos (k * t)).comp t h1).const_mul k⁻¹

theorem deriv_sinScaled {k : ℝ} (hk : k ≠ 0) (t : ℝ) :
    deriv (sinScaled k) t = Real.cos (k * t) := by
  rw [(hasDerivAt_sinScaled k t).deriv]
  field_simp

theorem deriv_cosScaled {k : ℝ} (hk : k ≠ 0) (t : ℝ) :
    deriv (cosScaled k) t = -Real.sin (k * t) := by
  rw [(hasDerivAt_cosScaled k t).deriv]
  field_simp

theorem contDiff_sinScaled (k : ℝ) : ContDiff ℝ 1 (sinScaled k) := by
  unfold sinScaled
  fun_prop

theorem contDiff_cosScaled (k : ℝ) : ContDiff ℝ 1 (cosScaled k) := by
  unfold cosScaled
  fun_prop

/-- The squares of the two derivatives sum to `1`. -/
theorem sq_deriv_sinScaled_add_sq_deriv_cosScaled {k : ℝ} (hk : k ≠ 0) (t : ℝ) :
    deriv (sinScaled k) t ^ 2 + deriv (cosScaled k) t ^ 2 = 1 := by
  rw [deriv_sinScaled hk, deriv_cosScaled hk]
  have := Real.sin_sq_add_cos_sq (k * t)
  nlinarith [this]

/-- The cross terms `Φ Φ'` of the rescaled sine and cosine cancel. -/
theorem sinScaled_mul_deriv_add_cosScaled_mul_deriv {k : ℝ} (hk : k ≠ 0) (t : ℝ) :
    sinScaled k t * deriv (sinScaled k) t + cosScaled k t * deriv (cosScaled k) t = 0 := by
  rw [deriv_sinScaled hk, deriv_cosScaled hk, sinScaled, cosScaled]
  ring

/-- The squares of the rescaled sine and cosine sum to `k⁻²`. -/
theorem sq_sinScaled_add_sq_cosScaled (k t : ℝ) :
    sinScaled k t ^ 2 + cosScaled k t ^ 2 = (k ^ 2)⁻¹ := by
  rw [sinScaled, cosScaled, mul_pow, mul_pow, ← mul_add, Real.sin_sq_add_cos_sq, mul_one]
  exact inv_pow k 2

theorem abs_sinScaled_le {k : ℝ} (hk : 0 < k) (t : ℝ) : |sinScaled k t| ≤ k⁻¹ := by
  rw [sinScaled, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ k⁻¹)]
  have h : |Real.sin (k * t)| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  nlinarith [abs_nonneg (Real.sin (k * t)), (by positivity : (0:ℝ) ≤ k⁻¹)]

theorem abs_cosScaled_le {k : ℝ} (hk : 0 < k) (t : ℝ) : |cosScaled k t| ≤ k⁻¹ := by
  rw [cosScaled, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ k⁻¹)]
  have h : |Real.cos (k * t)| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  nlinarith [abs_nonneg (Real.cos (k * t)), (by positivity : (0:ℝ) ≤ k⁻¹)]

/-- `Φ_k^s` is bounded, in the form the core-algebra input asks for. -/
theorem exists_bound_sinScaled {k : ℝ} (hk : 0 < k) : ∃ M : ℝ, ∀ t : ℝ, |sinScaled k t| ≤ M :=
  ⟨k⁻¹, abs_sinScaled_le hk⟩

/-- `Φ_k^c` is bounded, in the form the core-algebra input asks for. -/
theorem exists_bound_cosScaled {k : ℝ} (hk : 0 < k) : ∃ M : ℝ, ∀ t : ℝ, |cosScaled k t| ≤ M :=
  ⟨k⁻¹, abs_cosScaled_le hk⟩

end DirichletForm
