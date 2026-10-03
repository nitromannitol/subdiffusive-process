module

public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Actual signed-coordinate reflections and volume

Reflect the selected coordinates about their fixed center coordinates.
This is the affine isometry used on each retained cell of the original-grid
fold. The map, its domain preimages and restricted-volume preservation are
proved explicitly, without assigning a stationary law to the folded field.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- Reflect exactly the coordinates in `I` across the corresponding planes through `z`. -/
def coordinateReflection (z : SpatialCoordinates d) (I : Finset (Fin d))
    (x : SpatialCoordinates d) : SpatialCoordinates d :=
  fun i => if i ∈ I then 2 * z i - x i else x i

/-- A coordinate reflection is its own inverse on the entire spatial carrier. -/
theorem coordinateReflection_involutive (z : SpatialCoordinates d) (I : Finset (Fin d)) :
    Function.Involutive (coordinateReflection z I) := by
  intro x
  funext i
  simp only [coordinateReflection]
  split_ifs <;> ring

/-- Each reflected coordinate preserves scalar distances. -/
theorem coordinateReflection_dist_apply (z : SpatialCoordinates d) (I : Finset (Fin d))
    (x y : SpatialCoordinates d) (i : Fin d) :
    dist (coordinateReflection z I x i) (coordinateReflection z I y i) = dist (x i) (y i) := by
  unfold coordinateReflection
  split_ifs
  · rw [Real.dist_eq, Real.dist_eq]
    have he : (2 * z i - x i) - (2 * z i - y i) = -(x i - y i) := by ring
    rw [he, abs_neg]
  · rfl

/-- The whole coordinate map is an isometry for the spatial maximum norm. -/
theorem coordinateReflection_isometry (z : SpatialCoordinates d) (I : Finset (Fin d)) :
    Isometry (coordinateReflection z I) := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [dist_pi_def]
  congr 1
  apply Finset.sup_congr rfl
  intro i _
  apply Subtype.ext
  exact coordinateReflection_dist_apply z I x y i

/-- The actual reflection packaged as an involutive isometric equivalence. -/
def coordinateReflectionEquiv (z : SpatialCoordinates d) (I : Finset (Fin d)) :
    SpatialCoordinates d ≃ᵢ SpatialCoordinates d where
  toFun := coordinateReflection z I
  invFun := coordinateReflection z I
  left_inv := coordinateReflection_involutive z I
  right_inv := coordinateReflection_involutive z I
  isometry_toFun := coordinateReflection_isometry z I

/-- The equivalence retains the literal coordinate formula. -/
theorem coordinateReflectionEquiv_apply (z : SpatialCoordinates d) (I : Finset (Fin d))
    (x : SpatialCoordinates d) : coordinateReflectionEquiv z I x = coordinateReflection z I x := rfl

/-- A reflected cube has the reflected center and the same side. -/
theorem coordinateReflection_preimage_cube (z : SpatialCoordinates d) (I : Finset (Fin d))
    (w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    coordinateReflection z I ⁻¹'
      (centeredCube (coordinateReflection z I w) r hr : Set (SpatialCoordinates d)) =
      (centeredCube w r hr : Set (SpatialCoordinates d)) := by
  ext x
  change dist (coordinateReflection z I x) (coordinateReflection z I w) < r / 2 ↔ dist x w < r / 2
  rw [(coordinateReflection_isometry z I).dist_eq]

/-- Coordinate reflection preserves Lebesgue volume on the actual product space. -/
theorem coordinateReflection_measurePreserving (z : SpatialCoordinates d) (I : Finset (Fin d)) :
    MeasurePreserving (coordinateReflection z I) volume volume := by
  apply volume_preserving_pi (f := fun i (x : ℝ) => if i ∈ I then 2 * z i - x else x)
  intro i
  by_cases hi : i ∈ I
  · simpa only [coordinateReflection, hi, if_pos] using
      Measure.measurePreserving_sub_left (volume : Measure ℝ) (2 * z i)
  · simpa only [coordinateReflection, hi, if_neg, ite_false] using!
      (MeasurePreserving.id (volume : Measure ℝ))

/-- Volume restricted to corresponding actual cubes is also preserved. -/
theorem coordinateReflection_cube_measurePreserving (z : SpatialCoordinates d)
    (I : Finset (Fin d)) (w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    MeasurePreserving (coordinateReflection z I)
      (volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d)))
      (volume.restrict (centeredCube (coordinateReflection z I w) r hr : Set (SpatialCoordinates d))) := by
  have h := (coordinateReflection_measurePreserving z I).restrict_preimage
    (centeredCube (coordinateReflection z I w) r hr).isOpen.measurableSet
  rwa [coordinateReflection_preimage_cube] at h

/-- The reflected cube integral is exactly the original change of variables. -/
theorem integral_coordinateReflection_cube (z : SpatialCoordinates d) (I : Finset (Fin d))
    (w : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (f : SpatialCoordinates d → ℝ) :
    (∫ x in (centeredCube w r hr : Set (SpatialCoordinates d)), f (coordinateReflection z I x)) =
      ∫ y in (centeredCube (coordinateReflection z I w) r hr : Set (SpatialCoordinates d)), f y :=
  (coordinateReflection_cube_measurePreserving z I w hr).integral_comp
    (coordinateReflectionEquiv z I).toHomeomorph.measurableEmbedding f

/-- The reverse domain identity follows from the same coordinate involution. -/
theorem coordinateReflection_preimage_reverse (z : SpatialCoordinates d) (I : Finset (Fin d))
    {U Ω : Opens (SpatialCoordinates d)}
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U) :
    coordinateReflection z I ⁻¹' (U : Set (SpatialCoordinates d)) = Ω := by
  ext x
  have h := Set.ext_iff.mp hU (coordinateReflection z I x)
  simpa only [mem_preimage, coordinateReflection_involutive z I x] using h.symm

/-- The actual reflection preserves volume on any pair of corresponding open domains. -/
theorem coordinateReflection_domain_measurePreserving (z : SpatialCoordinates d)
    (I : Finset (Fin d)) {U Ω : Opens (SpatialCoordinates d)}
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U) :
    MeasurePreserving (coordinateReflection z I)
      (volume.restrict (U : Set (SpatialCoordinates d)))
      (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  have h := (coordinateReflection_measurePreserving z I).restrict_preimage Ω.isOpen.measurableSet
  rwa [hU] at h

end SubdiffusiveProcess
