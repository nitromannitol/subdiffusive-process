module

public import SubdiffusiveProcess.Model.HeatSemigroupVec
public import MarkovProcess.Kernel.Operator
@[expose] public section

/-!
# Lebesgue invariance of the Brownian transition kernels

The Gaussian translation formula and Tonelli's theorem give volume invariance
in every dimension. This supplies a reference measure for the killed Brownian
L² construction without using `LocalDiffusion`.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Model.HeatSemigroupVec

/-- Averaging Gaussian translates preserves the volume integral. -/
theorem lintegral_gaussianVec_volume {d : ℕ} (t : NNReal) (f : Vec d → ENNReal)
    (hf : Measurable f) :
    (∫⁻ x, ∫⁻ y, f y ∂gaussianVec d x t ∂(volume : Measure (Vec d)))
      = ∫⁻ y, f y ∂(volume : Measure (Vec d)) := by
  have hstep : ∀ x : Vec d, (∫⁻ y, f y ∂gaussianVec d x t)
      = ∫⁻ z, f (x + Real.sqrt t • z) ∂(gaussianVec d 0 1) := by
    intro x
    rw [gaussianVec_eq_map, lintegral_map hf (by fun_prop)]
  rw [lintegral_congr fun x => hstep x]
  rw [lintegral_lintegral_swap (μ := (volume : Measure (Vec d))) (ν := gaussianVec d 0 1)
    (f := fun (x z : Vec d) => f (x + Real.sqrt t • z))
    (hf.comp (show Measurable (fun p : Vec d × Vec d => p.1 + Real.sqrt t • p.2) from
      by fun_prop)).aemeasurable]
  rw [lintegral_congr fun z =>
    lintegral_add_right_eq_self (μ := (volume : Measure (Vec d))) f (Real.sqrt t • z)]
  rw [lintegral_const (μ := (gaussianVec d 0 1)), measure_univ, mul_one]

/-- Every Brownian transition kernel preserves Lebesgue measure. -/
theorem heatSemigroupVec_comp_volume (d : ℕ) (t : NNReal) :
    heatSemigroupVec d t ∘ₘ (volume : Measure (Vec d)) = volume := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind (heatSemigroupVec d t).aemeasurable hf.aemeasurable]
  simp_rw [heatSemigroupVec_apply]
  exact lintegral_gaussianVec_volume t f hf

/-- Lebesgue measure is a subinvariant reference measure for Brownian motion. -/
theorem isSubInvariant_volume_heatSemigroupVec (d : ℕ) :
    (heatSemigroupVec d).IsSubInvariant (volume : Measure (Vec d)) :=
  fun t => le_of_eq (heatSemigroupVec_comp_volume d t)

end SubdiffusiveProcess.Model.HeatSemigroupVec
