import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Analysis

/-- The unique minimizer depends only on the source's measure class. This uses
the variational characterization over the full finite-energy domain. -/
theorem minimizer_eq_of_source_ae_eq
    {X V : Type*} [MeasurableSpace X] (nu : Measure X)
    (E : V → ℝ≥0∞) (J : V → X → ℝ) (lam : ℝ)
    (f g : X → ℝ) (hfg : f =ᵐ[nu] g) (u v : V)
    (hu : E u ≠ ⊤)
    (humin : ∀ w, E w ≠ ⊤ →
      (E u).toReal + lam * (∫ x, J u x ^ 2 ∂nu) - 2 * (∫ x, f x * J u x ∂nu) ≤
        (E w).toReal + lam * (∫ x, J w x ^ 2 ∂nu) - 2 * (∫ x, f x * J w x ∂nu))
    (hvuniq : ∀ w, E w ≠ ⊤ →
      (∀ z, E z ≠ ⊤ →
        (E w).toReal + lam * (∫ x, J w x ^ 2 ∂nu) - 2 * (∫ x, g x * J w x ∂nu) ≤
          (E z).toReal + lam * (∫ x, J z x ^ 2 ∂nu) - 2 * (∫ x, g x * J z x ∂nu)) →
      w = v) : u = v := by
  have hint (w : V) : (∫ x, f x * J w x ∂nu) = ∫ x, g x * J w x ∂nu := by
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
  apply hvuniq u hu
  intro w hw
  simpa only [hint] using humin w hw

end SubdiffusiveProcess.Analysis
