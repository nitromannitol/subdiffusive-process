module

public import SubdiffusiveProcess.Section10.BoundedC0Approximation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! Bounds tested against bounded C₀ functions extend to bounded Borel
functions for two arbitrary finite measures. Approximation in their sum
controls both integrals without an absolute-continuity premise. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ZeroAtInfty
namespace SubdiffusiveProcess.Section10

/-- A finite-measure C₀ test bound extends to every bounded measurable input,
with the same constants and without any relation between the two measures. -/
theorem integral_abs_le_of_c0TestBound {d : ℕ}
    (ν μ : Measure (Fin d → ℝ)) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {A B F : ℝ} (hA : 0 ≤ A) (hF : 0 ≤ F)
    (htest : ∀ h : C₀(Fin d → ℝ, ℝ), (∀ y, |h y| ≤ F) →
      (∫ y, |h y| ∂ν) ≤ A * (∫ y, |h y| ∂μ) + B)
    {f : (Fin d → ℝ) → ℝ} (hf : Measurable f)
    (hfbound : ∀ y, |f y| ≤ F) :
    (∫ y, |f y| ∂ν) ≤ A * (∫ y, |f y| ∂μ) + B := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hA1 : 0 < A + 1 := by linarith
  let η := ε / (A + 1)
  have hη : 0 < η := div_pos hε hA1
  obtain ⟨h, hhbound, hherror⟩ :=
    exists_bounded_c0_integral_sub_le (ν + μ) hf hF hfbound hη
  have hfint (ρ : Measure (Fin d → ℝ)) [IsFiniteMeasure ρ] : Integrable f ρ :=
    (integrable_const F).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hfbound)
  have hhint (ρ : Measure (Fin d → ℝ)) [IsFiniteMeasure ρ] :
      Integrable (fun y => h y) ρ :=
    (integrable_const F).mono' h.continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hhbound)
  have herror (ρ : Measure (Fin d → ℝ)) [IsFiniteMeasure ρ] :
      Integrable (fun y => |f y - h y|) ρ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using! ((hfint ρ).sub (hhint ρ)).norm
  have herr (ρ : Measure (Fin d → ℝ)) (hρ : ρ ≤ ν + μ) :
      (∫ y, |f y - h y| ∂ρ) ≤ η :=
    (integral_mono_measure hρ
      (Filter.Eventually.of_forall fun y => abs_nonneg (f y - h y))
      (herror (ν + μ))).trans hherror
  have hcompare (ρ : Measure (Fin d → ℝ)) [IsFiniteMeasure ρ]
      (hρ : ρ ≤ ν + μ) :
      |(∫ y, |f y| ∂ρ) - (∫ y, |h y| ∂ρ)| ≤ η := by
    calc
      _ = |∫ y, |f y| - |h y| ∂ρ| := by
        rw [integral_sub (hfint ρ).abs (hhint ρ).abs]
      _ ≤ ∫ y, abs (|f y| - |h y|) ∂ρ := abs_integral_le_integral_abs
      _ ≤ ∫ y, |f y - h y| ∂ρ :=
        integral_mono ((hfint ρ).abs.sub (hhint ρ).abs).abs (herror ρ)
          (fun y => abs_abs_sub_abs_le_abs_sub (f y) (h y))
      _ ≤ η := herr ρ hρ
  have hν := hcompare ν (Measure.le_add_right le_rfl)
  have hμ := hcompare μ (Measure.le_add_left le_rfl)
  have hscaled : (A + 1) * η = ε := by
    dsimp only [η]
    exact mul_div_cancel₀ ε (ne_of_gt hA1)
  calc
    _ ≤ (∫ y, |h y| ∂ν) + η := by linarith [(abs_le.mp hν).2]
    _ ≤ A * (∫ y, |h y| ∂μ) + B + η := by linarith [htest h hhbound]
    _ ≤ A * ((∫ y, |f y| ∂μ) + η) + B + η := by
      gcongr
      linarith [(abs_le.mp hμ).1]
    _ = _ := by nlinarith [hscaled]

end SubdiffusiveProcess.Section10
