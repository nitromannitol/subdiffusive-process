import SubdiffusiveProcess.Sobolev.ReflectionObjectives
import SubdiffusiveProcess.Sobolev.ReflectionSpaces

/-! # Covariance of the actual affine responses

Attained variational formulas and actual Sobolev bijections give response
covariance. No invariance of an unspecified response is a hypothesis.
Ordinary Poincare inequalities supply existence of the variational solutions.
-/
open MeasureTheory Set TopologicalSpace
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {U Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
variable [IsFiniteMeasure (volume.restrict (U : Set (SpatialCoordinates d)))]

/-- The true affine Dirichlet minimum is unchanged by reflecting the domain, coefficient and slope. -/
theorem affineDirichletResponse_reflection (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hUb : Bornology.IsBounded (U : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
    (hDU : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph U,
      ‖(u : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) u‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) :
    affineDirichletResponse hUb hDU (reflectionCoefficient z I hU a)
      (coordinateReflectionDerivative I p) = affineDirichletResponse hΩ hD a p := by
  let f : killedSobolevGraph U → ℝ := fun u =>
    ∑ i : Fin d, ∫ x in (U : Set (SpatialCoordinates d)),
      (reflectionCoefficient z I hU a).val x *
        (coordinateReflectionDerivative I p i + (u : SobolevData U).2 i x)^2
  have he : Set.range f = Set.range (fun u : killedSobolevGraph Ω =>
      ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        a.val x * (p i + (u : SobolevData Ω).2 i x)^2) := by
    rw [← (reflectionKilledEquiv z I hU).surjective.range_comp f]
    congr 1
    funext u
    exact affineDirichletObjective_reflection z I hU a p u.val
  apply (affineDirichletResponse_isLeast hUb hDU
    (reflectionCoefficient z I hU a) (coordinateReflectionDerivative I p)).unique
  change IsLeast (Set.range f) _
  rw [he]
  exact affineDirichletResponse_isLeast hΩ hD a p

/-- The true inverse affine Neumann response obeys the same reflection identity. -/
theorem affineInverseNeumannResponse_reflection (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (hN : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) u‖)
    (hNU : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph U,
      ‖(u : SobolevData U).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph U) u‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ) :
    affineInverseNeumannResponse hNU (reflectionCoefficient z I hU a)
      (coordinateReflectionDerivative I p) = affineInverseNeumannResponse hN a p := by
  let f : meanZeroSobolevGraph U → ℝ := fun u =>
    2 * (∑ i : Fin d, ∫ x in (U : Set (SpatialCoordinates d)),
      coordinateReflectionDerivative I p i * (u : SobolevData U).2 i x) -
    ∑ i : Fin d, ∫ x in (U : Set (SpatialCoordinates d)),
      (reflectionCoefficient z I hU a).val x *
        ((u : SobolevData U).2 i x * (u : SobolevData U).2 i x)
  have he : Set.range f = Set.range (fun u : meanZeroSobolevGraph Ω =>
      2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        p i * (u : SobolevData Ω).2 i x) -
      ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        a.val x * ((u : SobolevData Ω).2 i x * (u : SobolevData Ω).2 i x)) := by
    rw [← (reflectionMeanZeroEquiv z I hU).surjective.range_comp f]
    congr 1
    funext u
    exact affineInverseNeumannObjective_reflection z I hU a p u.val
  apply (affineInverseNeumannResponse_isGreatest hNU
    (reflectionCoefficient z I hU a) (coordinateReflectionDerivative I p)).unique
  change IsGreatest (Set.range f) _
  rw [he]
  exact affineInverseNeumannResponse_isGreatest hN a p

end SubdiffusiveProcess
