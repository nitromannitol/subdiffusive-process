import SubdiffusiveProcess.Sobolev.ReflectionResponses
import SubdiffusiveProcess.Sobolev.ReflectionPoincare
import SubdiffusiveProcess.Sobolev.DiagonalDefect
import SubdiffusiveProcess.Geometry.ReflectionDomains

/-! # Exact reflection of the volume-normalized diagonal defect

This is the actual response covariance needed for retained cells in the
original-grid fold. Boundedness, positive volume and ordinary Poincare on
the destination are obtained from the original domain. The Euclidean unit
slope set is carried onto itself by the same coordinate sign map.
-/
open MeasureTheory Set TopologicalSpace
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {U Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
variable [IsFiniteMeasure (volume.restrict (U : Set (SpatialCoordinates d)))]

/-- The normalized diagonal defect is covariant under actual coordinate reflection. -/
theorem affineDiagonalDefect_reflection (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : 0 < volume.real (Ω : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
    (hN : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) u‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) :
    affineDiagonalDefect (coordinateReflection_domain_isBounded z I hU hΩ)
      (by rw [coordinateReflection_domain_volume_real z I hU]; exact hvol)
      (killed_poincare_reflection z I hU hD) (meanZero_poincare_reflection z I hU hN)
      (reflectionCoefficient z I hU a) (coordinateReflectionDerivative I p) =
    affineDiagonalDefect hΩ hvol hD hN a p := by
  unfold affineDiagonalDefect
  rw [affineDirichletResponse_reflection, affineInverseNeumannResponse_reflection,
    coordinateReflection_domain_volume_real z I hU, coordinateReflectionDerivative_sum_sq]

/-- Reflection preserves the entire range of diagonal defects over Euclidean unit slopes. -/
theorem affineDiagonalDefect_unit_range_reflection (z : SpatialCoordinates d)
    (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : 0 < volume.real (Ω : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
    (hN : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) u‖)
    (a : PositiveCoefficient Ω) :
    (affineDiagonalDefect (coordinateReflection_domain_isBounded z I hU hΩ)
      (by rw [coordinateReflection_domain_volume_real z I hU]; exact hvol)
      (killed_poincare_reflection z I hU hD) (meanZero_poincare_reflection z I hU hN)
      (reflectionCoefficient z I hU a)) '' {p | ∑ i : Fin d, (p i)^2 = 1} =
    (affineDiagonalDefect hΩ hvol hD hN a) '' {p | ∑ i : Fin d, (p i)^2 = 1} := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨coordinateReflectionDerivative I p, ?_, ?_⟩
    · change (∑ i : Fin d, (coordinateReflectionDerivative I p i)^2) = 1
      rw [coordinateReflectionDerivative_sum_sq]
      exact hp
    · have h := affineDiagonalDefect_reflection z I hU hΩ hvol hD hN a
        (coordinateReflectionDerivative I p)
      rw [coordinateReflectionDerivative_involutive I p] at h
      exact h.symm
  · rintro ⟨p, hp, rfl⟩
    refine ⟨coordinateReflectionDerivative I p, ?_, ?_⟩
    · change (∑ i : Fin d, (coordinateReflectionDerivative I p i)^2) = 1
      rw [coordinateReflectionDerivative_sum_sq]
      exact hp
    · exact affineDiagonalDefect_reflection z I hU hΩ hvol hD hN a p

end SubdiffusiveProcess
