module

public import SubdiffusiveProcess.Sobolev.LocalEnergy
public import SubdiffusiveProcess.Sobolev.PartitionEnergy
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Real
@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
namespace SubdiffusiveProcess
/-- The literal coefficient-weighted sum of squared gradient coordinates defines a finite measure. Its real value on every measurable set is exactly the existing local gradient energy. -/
theorem gradientEnergy_withDensity_finite_and_real
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (g : HilbertGradient Ω) :
    let μ : Measure (SpatialCoordinates d) :=
      (volume.restrict (Ω : Set (SpatialCoordinates d))).withDensity
        (fun x => ENNReal.ofReal (∑ i : Fin d, a.val x * (g i x) ^ 2))
    IsFiniteMeasure μ ∧
      ∀ (s : Set (SpatialCoordinates d)) (hs : MeasurableSet s),
        μ.real s = localGradientEnergy a hs g := by
  let ν : Measure (SpatialCoordinates d) :=
    volume.restrict (Ω : Set (SpatialCoordinates d))
  let f : SpatialCoordinates d → ℝ := fun x =>
    ∑ i : Fin d, a.val x * (g i x) ^ 2
  have hf : Integrable f ν := by
    dsimp [f, ν]
    apply integrable_finsetSum
    intro i hi
    simpa only [pow_two] using integrable_weighted_coordinates a.val g g i
  have hf_nonneg : 0 ≤ᵐ[ν] f := by
    filter_upwards [positiveCoefficient_ae_nonneg a] with x hax
    exact Finset.sum_nonneg fun i hi => mul_nonneg hax (sq_nonneg (g i x))
  have hlin : (∫⁻ x, ENNReal.ofReal (f x) ∂ν) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hf_nonneg).2 hf
  let μ : Measure (SpatialCoordinates d) :=
    ν.withDensity (fun x => ENNReal.ofReal (f x))
  have hμ : IsFiniteMeasure μ := isFiniteMeasure_withDensity hlin
  refine ⟨hμ, ?_⟩
  intro s hs
  rw [show μ.real s = (μ s).toReal by rfl]
  rw [show μ s = ∫⁻ x in s, ENNReal.ofReal (f x) ∂ν by
    exact withDensity_apply _ hs]
  rw [← ofReal_integral_eq_lintegral_ofReal (hf.integrableOn) (ae_restrict_of_ae hf_nonneg)]
  rw [ENNReal.toReal_ofReal]
  · rw [localGradientEnergy_eq_integral]
    rw [integral_finsetSum]
    intro i hi
    simpa only [ν, pow_two, IntegrableOn] using
      (integrable_weighted_coordinates a.val g g i).integrableOn
  · exact integral_nonneg_of_ae (ae_restrict_of_ae hf_nonneg)

end SubdiffusiveProcess
