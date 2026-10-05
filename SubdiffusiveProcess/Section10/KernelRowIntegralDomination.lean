module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationDensity

@[expose] public section

/-! Fixed-test integral bounds from a.e. rectangle bounds. The exceptional
starting set may depend on the test: no uncountable intersection of row
exceptional sets and no prior row absolute continuity are assumed. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace SubdiffusiveProcess.Section10

/-- Integrate the rectangle bounds first, then recover a fixed-test a.e.
bound. This avoids exchanging `forall B` with `almost everywhere x`. -/
theorem ae_lintegral_le_of_ae_row_bound {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (mu : Measure α) [SigmaFinite mu] (nu : Measure β)
    (Q : Kernel α β) (M : ℝ≥0∞)
    (hrow : ∀ B : Set β, MeasurableSet B → ∀ᵐ x ∂mu, Q x B ≤ M * nu B)
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    ∀ᵐ x ∂mu, (∫⁻ y, g y ∂Q x) ≤ M * ∫⁻ y, g y ∂nu := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    ((Measure.measurable_lintegral hg).comp Q.measurable) 
  intro C hC _hCfinite
  have hcomp : Q ∘ₘ (mu.restrict C) ≤ (M * mu C) • nu := by
    apply Measure.le_iff.mpr
    intro B hB
    rw [Measure.bind_apply hB Q.aemeasurable, Measure.smul_apply, smul_eq_mul]
    calc
      (∫⁻ x in C, Q x B ∂mu) ≤ ∫⁻ _x in C, M * nu B ∂mu :=
        lintegral_mono_ae (ae_restrict_of_ae (hrow B hB))
      _ = (M * mu C) * nu B := by simp only [setLIntegral_const]; ring
  calc
    (∫⁻ x in C, ∫⁻ y, g y ∂Q x ∂mu) = ∫⁻ y, g y ∂(Q ∘ₘ mu.restrict C) :=
      (Measure.lintegral_bind Q.aemeasurable hg.aemeasurable).symm
    _ ≤ ∫⁻ y, g y ∂((M * mu C) • nu) := lintegral_mono' hcomp le_rfl
    _ = ∫⁻ _x in C, M * ∫⁻ y, g y ∂nu ∂mu := by
      rw [lintegral_smul_measure, setLIntegral_const, smul_eq_mul]
      ring

/-- Real nonnegative integrable tests inherit the same rectangle constant. -/
theorem ae_integral_le_of_ae_row_bound {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (mu : Measure α) [SigmaFinite mu] (nu : Measure β)
    (Q : Kernel α β) (M : ℝ) (hM : 0 ≤ M)
    (hrow : ∀ B : Set β, MeasurableSet B →
      ∀ᵐ x ∂mu, Q x B ≤ ENNReal.ofReal M * nu B)
    (g : β → ℝ) (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y)
    (hgnu : Integrable g nu) (hgQ : ∀ x, Integrable g (Q x)) :
    ∀ᵐ x ∂mu, (∫ y, g y ∂Q x) ≤ M * ∫ y, g y ∂nu := by
  filter_upwards [ae_lintegral_le_of_ae_row_bound mu nu Q (ENNReal.ofReal M)
    hrow (fun y ↦ ENNReal.ofReal (g y)) hg.ennreal_ofReal] with x hx
  rw [← ofReal_integral_eq_lintegral_ofReal (hgQ x) (ae_of_all _ hg0),
    ← ofReal_integral_eq_lintegral_ofReal hgnu (ae_of_all _ hg0),
    ← ENNReal.ofReal_mul hM] at hx
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM (integral_nonneg hg0))).mp hx

end SubdiffusiveProcess.Section10
