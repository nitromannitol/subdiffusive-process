module

public import SubdiffusiveProcess.Lnorm.CutoffPotentialMeasurability
public import SubdiffusiveProcess.Sobolev.VolumeResponseContinuity

@[expose] public section

/-!
# Norm measurability of the actual cutoff inverse operators

Each operator is a continuous function of the normalized bounded potential on a
fixed cube. This gives strong measurability and supplies norm measurability
without a separability assumption on the full space of bounded operators.
-/

open MeasureTheory TopologicalSpace

namespace SubdiffusiveProcess

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The actual finite-cutoff volume-response operator is strongly measurable in operator norm. -/
theorem stronglyMeasurable_cutoffVolumeResponseOperator
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) :
    StronglyMeasurable (fun omega =>
      volumeResponseOperator S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)) := by
  simpa only [← Lnorm.proxy_pot_eq_coefficient] using
    (continuous_volumeResponseOperator_expPotentialCoefficient S).comp_stronglyMeasurable
      (Lnorm.stronglyMeasurable_cutoffPotential_Lp M H hH N z r hr)

/-- Borel measurability in the operator norm, for the actual cutoff inverse operator. -/
theorem measurable_cutoffVolumeResponseOperator
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) :
    @Measurable _ _ _ (borel (DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr)))
      (fun omega => volumeResponseOperator S
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)) := by
  let : MeasurableSpace (DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr)) := borel _
  let : BorelSpace (DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr)) := ⟨rfl⟩
  exact (stronglyMeasurable_cutoffVolumeResponseOperator M H hH N z r hr S).measurable

/-- Pairwise operator-norm distances are measurable for the actual cutoff operators. -/
theorem measurable_dist_cutoffVolumeResponseOperator
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (N N' : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) :
    Measurable (fun omega => dist
      (volumeResponseOperator S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr))
      (volumeResponseOperator S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N' z hr))) := by
  simp only [dist_eq_norm]
  exact ((stronglyMeasurable_cutoffVolumeResponseOperator M H hH N z r hr S).sub
      (stronglyMeasurable_cutoffVolumeResponseOperator M H hH N' z r hr S)).norm.measurable

end SubdiffusiveProcess
