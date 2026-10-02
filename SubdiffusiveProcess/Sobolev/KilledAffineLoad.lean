import SubdiffusiveProcess.Sobolev.AffineData

/-!
# Affine loads vanish on killed variations

For a compactly supported smooth function, each coordinate derivative has
zero volume integral. Continuity passes this identity to the concrete H1_0
completion. Thus affine boundary perturbations have the prescribed average
gradient, with no boundary-flux identity imported as an assumption.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

/-- A compactly supported test has zero integral of each coordinate derivative. -/
theorem integral_testPartialL2_eq_zero
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (φ : 𝓓(Ω, ℝ)) (i : Fin d) :
    (∫ x in (Ω : Set (SpatialCoordinates d)), testPartialL2 φ i x) = 0 := by
  have he := (mem_weakSobolevGraph_iff (affineSobolevData hΩ 0 1)).mp
    (affineSobolevData_mem hΩ 0 1) φ i
  have hleft : (∫ x in (Ω : Set (SpatialCoordinates d)),
      φ x * domainConstantL2 (Ω := Ω) 0 x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [domainConstantL2_coeFn (Ω := Ω) 0] with x hx
    simp only [hx, mul_zero, Pi.zero_apply]
  have hright : (∫ x in (Ω : Set (SpatialCoordinates d)),
      fderiv ℝ φ x (Pi.single i 1) * affineL2 hΩ 0 1 x) =
      ∫ x in (Ω : Set (SpatialCoordinates d)), testPartialL2 φ i x := by
    apply integral_congr_ae
    filter_upwards [affineL2_coeFn hΩ 0 1, testPartialL2_coeFn φ i] with x hx hy
    simp only [hx, hy, affineSlope_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
      zero_add, mul_one]
  change (∫ x in (Ω : Set (SpatialCoordinates d)), φ x * domainConstantL2 (Ω := Ω) 0 x) +
    (∫ x in (Ω : Set (SpatialCoordinates d)),
      fderiv ℝ φ x (Pi.single i 1) * affineL2 hΩ 0 1 x) = 0 at he
  simpa only [hleft, hright, zero_add] using he

/-- The affine load annihilates every killed Sobolev variation, by closure. -/
theorem affineNeumannLoad_killed_eq_zero
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p : Fin d → ℝ) (w : killedSobolevGraph Ω) :
    affineNeumannLoad p (subspaceGradient (killedSobolevGraph Ω) w) = 0 := by
  let L : SobolevData Ω →L[ℝ] ℝ := (affineNeumannLoad p).comp sobolevGradient
  have hk : killedSobolevGraph Ω ≤ LinearMap.ker L := by
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨φ, rfl⟩
      change affineNeumannLoad p (sobolevGradient (smoothSobolevData φ)) = 0
      rw [affineNeumannLoad_apply]
      change (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        p i * testPartialL2 φ i x) = 0
      simp only [integral_const_mul, integral_testPartialL2_eq_zero hΩ,
        mul_zero, Finset.sum_const_zero]
    · exact isClosed_eq L.continuous continuous_const
  exact hk w.property

end SubdiffusiveProcess
