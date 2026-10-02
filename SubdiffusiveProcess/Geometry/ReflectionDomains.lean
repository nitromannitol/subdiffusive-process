import SubdiffusiveProcess.Geometry.CoordinateReflection
import Mathlib.Topology.MetricSpace.Antilipschitz

/-! # Volume and boundedness of reflected domains

Domain volume equality follows from the actual Lebesgue-measure-preserving
coordinate map; it is not an extra premise for response normalization.
-/
open MeasureTheory Set TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {U Ω : Opens (SpatialCoordinates d)}

/-- Corresponding reflected open domains have exactly the same Lebesgue volume. -/
theorem coordinateReflection_domain_volume (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U) :
    volume (U : Set (SpatialCoordinates d)) = volume (Ω : Set (SpatialCoordinates d)) := by
  have h := (coordinateReflection_measurePreserving z I).measure_preimage
    Ω.isOpen.measurableSet.nullMeasurableSet
  rwa [hU] at h

/-- The real-valued volume used in the affine defect is also preserved. -/
theorem coordinateReflection_domain_volume_real (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U) :
    volume.real (U : Set (SpatialCoordinates d)) = volume.real (Ω : Set (SpatialCoordinates d)) :=
  congrArg ENNReal.toReal (coordinateReflection_domain_volume z I hU)

/-- A reflected domain is bounded whenever the original domain is bounded. -/
theorem coordinateReflection_domain_isBounded (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d))) :
    Bornology.IsBounded (U : Set (SpatialCoordinates d)) := by
  rw [← hU]
  exact (coordinateReflection_isometry z I).antilipschitz.isBounded_preimage hΩ

end SubdiffusiveProcess
