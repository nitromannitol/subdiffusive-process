import SubdiffusiveProcess.Sobolev.GradientEnergyMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The coefficient-gradient energy measure and its test-function dictionary.
This module identifies the literal density, finite local mass, and test integrals;
it does not assert convergence of any sequence of energy measures.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

/-- The finite energy measure of a native coordinate gradient and positive coefficient. -/
def gradientEnergyMeasure {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Q) (g : HilbertGradient Q) : Measure (SpatialCoordinates d) :=
  (volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
    (fun x => ENNReal.ofReal (a.val x * ∑ i : Fin d, (g i x) ^ 2))

/-- The gradient energy measure is finite and its local mass is the native local energy. -/
theorem gradientEnergyMeasure_finite_and_real {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Q) (g : HilbertGradient Q) :
    IsFiniteMeasure (gradientEnergyMeasure a g) ∧
      ∀ B : Set (SpatialCoordinates d), ∀ hB : MeasurableSet B,
        ((gradientEnergyMeasure a g) B).toReal = localGradientEnergy a hB g := by
  simpa only [gradientEnergyMeasure, Finset.mul_sum, Measure.real] using
    gradientEnergy_withDensity_finite_and_real a g

/-- Integrating a test against the native energy measure is the literal coefficient-gradient integral. -/
theorem gradientEnergyMeasure_integral {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Q) (g : HilbertGradient Q) (chi : SpatialCoordinates d → ℝ) :
    (∫ x, chi x ∂gradientEnergyMeasure a g) =
      ∫ x in (Q : Set (SpatialCoordinates d)), chi x * a.val x * ∑ i : Fin d, (g i x) ^ 2 := by
  have hf : Integrable (fun x => a.val x * ∑ i : Fin d, (g i x) ^ 2)
      (volume.restrict (Q : Set (SpatialCoordinates d))) := by
    simp only [Finset.mul_sum]
    apply integrable_finset_sum
    intro i hi
    simpa only [pow_two] using integrable_weighted_coordinates a.val g g i
  have hm := ENNReal.continuous_ofReal.measurable.comp_aemeasurable hf.aemeasurable
  change AEMeasurable (fun x => ENNReal.ofReal (a.val x * ∑ i : Fin d, (g i x) ^ 2))
    (volume.restrict (Q : Set (SpatialCoordinates d))) at hm
  rw [gradientEnergyMeasure, integral_withDensity_eq_integral_toReal_smul₀ hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) chi]
  apply integral_congr_ae
  filter_upwards [positiveCoefficient_ae_nonneg a] with x hx
  rw [ENNReal.toReal_ofReal (mul_nonneg hx (Finset.sum_nonneg fun i _ => sq_nonneg _))]
  simp only [smul_eq_mul]
  ring

end SubdiffusiveProcess
