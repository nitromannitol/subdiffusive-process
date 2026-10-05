module

public import SubdiffusiveProcess.Geometry.CoordinateReflection
public import SubdiffusiveProcess.Sobolev.WeakGradient

@[expose] public section

/-! # Actual Lp pullback by coordinate reflection

The only domain premise is the literal geometric preimage identity. The
map is composition on the actual restricted-volume equivalence classes.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {U Ω : Opens (SpatialCoordinates d)}

/-- Pull back an Lp class along the actual coordinate reflection. -/
def reflectionLp (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d))) →ₗᵢ[ℝ]
      Lp ℝ p (volume.restrict (U : Set (SpatialCoordinates d))) :=
  Lp.compMeasurePreservingₗᵢ ℝ (coordinateReflection z I)
    (coordinateReflection_domain_measurePreserving z I hU)

/-- Composition identifies the representative almost everywhere on the destination. -/
theorem reflectionLp_coeFn (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    (reflectionLp z I hU f : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))] f ∘ coordinateReflection z I :=
  Lp.coeFn_compMeasurePreserving f (coordinateReflection_domain_measurePreserving z I hU)

/-- Pullback to the reflected domain and back is exactly the original Lp class. -/
theorem reflectionLp_inverse (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    reflectionLp z I (coordinateReflection_preimage_reverse z I hU)
      (reflectionLp z I hU f) = f := by
  apply Lp.ext
  have hm := coordinateReflection_domain_measurePreserving z I
    (coordinateReflection_preimage_reverse z I hU)
  filter_upwards [reflectionLp_coeFn z I
    (coordinateReflection_preimage_reverse z I hU) (reflectionLp z I hU f),
    hm.quasiMeasurePreserving.ae_eq_comp (reflectionLp_coeFn z I hU f)] with x hx hy
  exact hx.trans (hy.trans (congrArg f (coordinateReflection_involutive z I x)))

/-- Reflection preserves the Lp norm, including the essential supremum. -/
theorem reflectionLp_norm (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    ‖reflectionLp z I hU f‖ = ‖f‖ := (reflectionLp z I hU).norm_map f

/-- Integral change of variables for the actual reflected L2 class. -/
theorem integral_reflectionLp (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (f : DomainL2 Ω) :
    (∫ x in (U : Set (SpatialCoordinates d)), reflectionLp z I hU f x) =
      ∫ y in (Ω : Set (SpatialCoordinates d)), f y := by
  calc
    _ = ∫ x in (U : Set (SpatialCoordinates d)), f (coordinateReflection z I x) :=
      integral_congr_ae (reflectionLp_coeFn z I hU f)
    _ = _ := (coordinateReflection_domain_measurePreserving z I hU).integral_comp
      (coordinateReflectionEquiv z I).toHomeomorph.measurableEmbedding f

end SubdiffusiveProcess
