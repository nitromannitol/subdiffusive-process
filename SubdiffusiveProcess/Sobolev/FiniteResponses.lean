module

public import SubdiffusiveProcess.Sobolev.WeightedGradient
public import SubdiffusiveProcess.Sobolev.MeanZero

@[expose] public section

/-!
# Finite-cutoff killed and Neumann weak solutions

The variation spaces and loads here are concrete. The only analytic input
left explicit in these declarations is the ordinary Poincare inequality on
the chosen domain (or its mean-zero version). Coefficients are genuine L∞
functions with a positive lower bound. No limit operator or model regularity
estimate is assumed.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- The killed source equation on the actual H1_0 completion. -/
theorem existsUnique_killed_source_solution (K : ℝ≥0)
    (hP : ∀ z : killedSobolevGraph Ω, ‖(z : SobolevData Ω).1‖ ≤
      K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    {c : ℝ} (hc : 0 < c)
    (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a x)
    (f : DomainL2 Ω) :
    ∃! u : killedSobolevGraph Ω, ∀ v : killedSobolevGraph Ω,
      weightedGradientForm a (sobolevGradient (u : SobolevData Ω))
        (sobolevGradient (v : SobolevData Ω)) =
        ∫ x in (Ω : Set (SpatialCoordinates d)), f x * (v : SobolevData Ω).1 x := by
  have h := existsUnique_gradient_subspace_solution (killedSobolevGraph Ω)
    isClosed_killedSobolevGraph K hP a hc ha
    ((sobolevVolumeLoad f).comp (killedSobolevGraph Ω).subtypeL)
  simpa only [subspaceGradient, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    sobolevVolumeLoad_apply] using h

variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

/-- The Neumann volume-source equation on the actual mean-zero H1 space.
Only mean-zero tests occur; compatibility of a source with constants is a
separate statement when expressing the equation on all H1 tests. -/
theorem existsUnique_meanZero_source_solution (K : ℝ≥0)
    (hP : ∀ z : meanZeroSobolevGraph Ω, ‖(z : SobolevData Ω).1‖ ≤
      K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    {c : ℝ} (hc : 0 < c)
    (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a x)
    (f : DomainL2 Ω) :
    ∃! u : meanZeroSobolevGraph Ω, ∀ v : meanZeroSobolevGraph Ω,
      weightedGradientForm a (sobolevGradient (u : SobolevData Ω))
        (sobolevGradient (v : SobolevData Ω)) =
        ∫ x in (Ω : Set (SpatialCoordinates d)), f x * (v : SobolevData Ω).1 x := by
  have h := existsUnique_gradient_subspace_solution (meanZeroSobolevGraph Ω)
    isClosed_meanZeroSobolevGraph K hP a hc ha
    ((sobolevVolumeLoad f).comp (meanZeroSobolevGraph Ω).subtypeL)
  simpa only [subspaceGradient, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    sobolevVolumeLoad_apply] using h

/-- The primitive affine Neumann response uses its actual gradient volume load. -/
theorem existsUnique_affineNeumann_solution (K : ℝ≥0)
    (hP : ∀ z : meanZeroSobolevGraph Ω, ‖(z : SobolevData Ω).1‖ ≤
      K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    {c : ℝ} (hc : 0 < c)
    (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a x)
    (p : Fin d → ℝ) :
    ∃! u : meanZeroSobolevGraph Ω, ∀ v : meanZeroSobolevGraph Ω,
      weightedGradientForm a (sobolevGradient (u : SobolevData Ω))
        (sobolevGradient (v : SobolevData Ω)) = ∑ i : Fin d,
          ∫ x in (Ω : Set (SpatialCoordinates d)), p i * (v : SobolevData Ω).2 i x := by
  have h := existsUnique_gradient_subspace_solution (meanZeroSobolevGraph Ω)
    isClosed_meanZeroSobolevGraph K hP a hc ha
    ((affineNeumannLoad p).comp (subspaceGradient (meanZeroSobolevGraph Ω)))
  have hgradient_apply (z : SobolevData Ω) (i : Fin d) :
      sobolevGradient z i = z.2 i := rfl
  simpa only [subspaceGradient, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    affineNeumannLoad_apply, hgradient_apply] using h

end SubdiffusiveProcess
