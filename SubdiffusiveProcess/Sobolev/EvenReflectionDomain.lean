module

public import SubdiffusiveProcess.Geometry.CoordinateReflection
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-!
# Half domains and their doubled reflection domains

`Ω` is the part of an open set `U` strictly below the coordinate plane
`{x i = z i}`, and `U` is invariant under reflection across that plane.
The reflected half is `R ⁻¹' Ω`; the plane itself has Lebesgue measure zero,
so `U` is covered almost everywhere by the two halves. Nothing about traces
or boundary values of Sobolev functions is asserted here.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- An open set `U` symmetric under one coordinate reflection, with `Ω` its lower half. -/
structure EvenReflectionDomain (d : ℕ) where
  /-- A point of the reflection plane. -/
  z : SpatialCoordinates d
  /-- The reflected coordinate. -/
  i : Fin d
  /-- The lower half domain. -/
  Ω : Opens (SpatialCoordinates d)
  /-- The doubled domain. -/
  U : Opens (SpatialCoordinates d)
  /-- The lower half is exactly the part of `U` strictly below the plane. -/
  mem_iff : ∀ x, x ∈ Ω ↔ x ∈ U ∧ x i < z i
  /-- The doubled domain is invariant under the reflection. -/
  symm : coordinateReflection z {i} ⁻¹' (U : Set (SpatialCoordinates d)) = U

/-- The reflected coordinate of a single-coordinate reflection. -/
theorem coordinateReflection_single_apply_self (z : SpatialCoordinates d) (i : Fin d)
    (x : SpatialCoordinates d) : coordinateReflection z {i} x i = 2 * z i - x i := by
  simp [coordinateReflection]

/-- The other coordinates of a single-coordinate reflection are unchanged. -/
theorem coordinateReflection_single_apply_of_ne (z : SpatialCoordinates d) {i j : Fin d}
    (hj : j ≠ i) (x : SpatialCoordinates d) : coordinateReflection z {i} x j = x j := by
  simp [coordinateReflection, hj]

/-- Points of the reflection plane are fixed by the reflection. -/
theorem coordinateReflection_single_eq_self (z : SpatialCoordinates d) (i : Fin d)
    {x : SpatialCoordinates d} (hx : x i = z i) : coordinateReflection z {i} x = x := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [coordinateReflection_single_apply_self, hx]
    ring
  · exact coordinateReflection_single_apply_of_ne z hj x

namespace EvenReflectionDomain
variable (D : EvenReflectionDomain d)

/-- The upper half: the preimage of the lower half under the reflection. -/
def reflected : Opens (SpatialCoordinates d) :=
  ⟨coordinateReflection D.z {D.i} ⁻¹' (D.Ω : Set (SpatialCoordinates d)),
    D.Ω.isOpen.preimage (coordinateReflection_isometry D.z {D.i}).continuous⟩

/-- The literal preimage identity for the lower half. -/
theorem preimage_Ω :
    coordinateReflection D.z {D.i} ⁻¹' (D.Ω : Set (SpatialCoordinates d)) = D.reflected := rfl

/-- The preimage identity for the upper half. -/
theorem preimage_reflected :
    coordinateReflection D.z {D.i} ⁻¹' (D.reflected : Set (SpatialCoordinates d)) = D.Ω :=
  coordinateReflection_preimage_reverse D.z {D.i} D.preimage_Ω

/-- Reflection preserves membership in the doubled domain. -/
theorem reflection_mem_U_iff (x : SpatialCoordinates d) :
    coordinateReflection D.z {D.i} x ∈ D.U ↔ x ∈ D.U := by
  change coordinateReflection D.z {D.i} x ∈ (D.U : Set (SpatialCoordinates d)) ↔ _
  rw [← mem_preimage, D.symm]
  rfl

/-- The upper half is exactly the part of `U` strictly above the plane. -/
theorem mem_reflected_iff (x : SpatialCoordinates d) :
    x ∈ D.reflected ↔ x ∈ D.U ∧ D.z D.i < x D.i := by
  change coordinateReflection D.z {D.i} x ∈ D.Ω ↔ _
  rw [D.mem_iff, reflection_mem_U_iff, coordinateReflection_single_apply_self]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith⟩

/-- The lower half lies in the doubled domain. -/
theorem Ω_le : D.Ω ≤ D.U := fun x hx => ((D.mem_iff x).mp hx).1

/-- The upper half lies in the doubled domain. -/
theorem reflected_le : D.reflected ≤ D.U := fun x hx => ((D.mem_reflected_iff x).mp hx).1

/-- The two halves are disjoint. -/
theorem disjoint_Ω_reflected :
    Disjoint (D.Ω : Set (SpatialCoordinates d)) (D.reflected : Set (SpatialCoordinates d)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 := ((D.mem_iff x).mp hx).2
  have h2 := ((D.mem_reflected_iff x).mp hx').2
  linarith

/-- Points of the upper half are not in the lower half. -/
theorem notMem_Ω_of_mem_reflected {x : SpatialCoordinates d} (hx : x ∈ D.reflected) :
    x ∉ (D.Ω : Set (SpatialCoordinates d)) := fun h => D.disjoint_Ω_reflected.notMem_of_mem_left h hx

/-- Points of the lower half are not in the upper half. -/
theorem notMem_reflected_of_mem_Ω {x : SpatialCoordinates d} (hx : x ∈ D.Ω) :
    x ∉ (D.reflected : Set (SpatialCoordinates d)) := fun h => D.disjoint_Ω_reflected.notMem_of_mem_left hx h

/-- Off the null reflection plane, every point of `U` lies in one of the two halves. -/
theorem ae_mem_or_mem :
    ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))), x ∈ D.Ω ∨ x ∈ D.reflected := by
  have hplane : ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)), x D.i ≠ D.z D.i :=
    Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) D.i (D.z D.i)
  filter_upwards [ae_restrict_mem D.U.isOpen.measurableSet, ae_restrict_of_ae hplane] with x hU hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inl ((D.mem_iff x).mpr ⟨hU, h⟩)
  · exact Or.inr ((D.mem_reflected_iff x).mpr ⟨hU, h⟩)

/-- The doubled domain agrees with the union of the halves up to a null set. -/
theorem union_ae_eq :
    ((D.Ω : Set (SpatialCoordinates d)) ∪ D.reflected : Set (SpatialCoordinates d))
      =ᵐ[volume] (D.U : Set (SpatialCoordinates d)) := by
  rw [ae_eq_set]
  constructor
  · rw [Set.sdiff_eq_empty.mpr (union_subset D.Ω_le D.reflected_le), measure_empty]
  · apply measure_mono_null _ (Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) D.i (D.z D.i))
    intro x hx
    rw [Set.mem_sdiff, mem_union] at hx
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hx.2 (Or.inl ((D.mem_iff x).mpr ⟨hx.1, h⟩))
    · exact hx.2 (Or.inr ((D.mem_reflected_iff x).mpr ⟨hx.1, h⟩))

end EvenReflectionDomain
end SubdiffusiveProcess
end
