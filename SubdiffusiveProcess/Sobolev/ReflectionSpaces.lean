module

public import SubdiffusiveProcess.Sobolev.ReflectionEnergy

@[expose] public section

/-! # Bijections of the actual reflected variational spaces

The killed and mean-zero competitor maps below are the actual Sobolev
pullback. Their inverses follow from spatial reflection twice, so subsequent
response covariance does not need an assumed correspondence of competitors.
-/
open MeasureTheory Set TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {U Ω : Opens (SpatialCoordinates d)}

/-- The actual coordinate reflection is a bijection of killed Sobolev competitors. -/
def reflectionKilledEquiv (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U) :
    killedSobolevGraph Ω ≃ killedSobolevGraph U where
  toFun u := ⟨reflectionSobolevData z I hU u.val,
    reflectionSobolevData_mem_killed z I hU u.property⟩
  invFun u := ⟨reflectionSobolevData z I (coordinateReflection_preimage_reverse z I hU) u.val,
    reflectionSobolevData_mem_killed z I (coordinateReflection_preimage_reverse z I hU) u.property⟩
  left_inv u := Subtype.ext (reflectionSobolevData_inverse z I hU u.val)
  right_inv u := Subtype.ext (reflectionSobolevData_inverse z I
    (coordinateReflection_preimage_reverse z I hU) u.val)

/-- The killed-space bijection uses precisely the Sobolev pullback already constructed. -/
theorem reflectionKilledEquiv_coe (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (u : killedSobolevGraph Ω) :
    (reflectionKilledEquiv z I hU u : SobolevData U) = reflectionSobolevData z I hU u.val := rfl

variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
variable [IsFiniteMeasure (volume.restrict (U : Set (SpatialCoordinates d)))]

/-- Reflection is also a bijection of the actual mean-zero Neumann competitors. -/
def reflectionMeanZeroEquiv (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U) :
    meanZeroSobolevGraph Ω ≃ meanZeroSobolevGraph U where
  toFun u := ⟨reflectionSobolevData z I hU u.val,
    (reflectionSobolevData_mem_meanZero_iff z I hU u.val).mpr u.property⟩
  invFun u := ⟨reflectionSobolevData z I (coordinateReflection_preimage_reverse z I hU) u.val,
    (reflectionSobolevData_mem_meanZero_iff z I
      (coordinateReflection_preimage_reverse z I hU) u.val).mpr u.property⟩
  left_inv u := Subtype.ext (reflectionSobolevData_inverse z I hU u.val)
  right_inv u := Subtype.ext (reflectionSobolevData_inverse z I
    (coordinateReflection_preimage_reverse z I hU) u.val)

/-- The mean-zero bijection has the same literal Sobolev pullback. -/
theorem reflectionMeanZeroEquiv_coe (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (u : meanZeroSobolevGraph Ω) :
    (reflectionMeanZeroEquiv z I hU u : SobolevData U) = reflectionSobolevData z I hU u.val := rfl

end SubdiffusiveProcess
