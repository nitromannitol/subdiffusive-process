import SubdiffusiveProcess.Lnorm.CutoffVolumeResponseMeasurability
import SubdiffusiveProcess.Section9.CanonicalLimitIdentification

/-! Measurability and convergence of the actual scalar unweighted cutoff responses. -/

open Filter MeasureTheory TopologicalSpace SubdiffusiveProcess
open scoped Topology

namespace SubdiffusiveProcess.AuditRepairs

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem measurable_cutoff_scalar_inverse
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (f : DomainL2 (centeredCube z r hr)) :
    Measurable (fun β => inverseResponse S
      (Lane4.cutoffPositiveCoefficient M H β N z hr)
      ((sobolevVolumeLoad f).comp S.space.subtypeL)) := by
  have hc : Continuous (fun T : DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr) => inner ℝ f (T f)) :=
    continuous_const.inner ((ContinuousLinearMap.apply ℝ _ f).continuous)
  simpa only [volumeResponseOperator_quadratic] using
    (hc.comp_stronglyMeasurable
      (stronglyMeasurable_cutoffVolumeResponseOperator M H hH N z r hr S)).measurable

theorem cutoff_scalar_inverse_tendsto_in_measure
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (G : BilateralField d → DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr))
    (hconv : TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun N β => volumeResponseOperator S
        (Lane4.cutoffPositiveCoefficient M H β N z hr)) atTop G)
    (f : DomainL2 (centeredCube z r hr)) :
    TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun N β => inverseResponse S (Lane4.cutoffPositiveCoefficient M H β N z hr)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
      (fun β => inner ℝ f (G β f)) := by
  have hc : Continuous (fun T : DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr) => inner ℝ f (T f)) :=
    continuous_const.inner ((ContinuousLinearMap.apply ℝ _ f).continuous)
  have hmeas : ∀ N, AEStronglyMeasurable (fun β => inner ℝ f
      (volumeResponseOperator S (Lane4.cutoffPositiveCoefficient M H β N z hr) f))
      (chaosSampleLaw M).toMeasure := fun N => by
    simpa only [volumeResponseOperator_quadratic] using
      (measurable_cutoff_scalar_inverse M H hH N z r hr S f).aestronglyMeasurable
  simpa only [volumeResponseOperator_quadratic] using
    SubdiffusiveProcess.Section9.tendstoInMeasure_continuous_test (chaosSampleLaw M).toMeasure _ G _ hc hmeas hconv

end SubdiffusiveProcess.AuditRepairs
