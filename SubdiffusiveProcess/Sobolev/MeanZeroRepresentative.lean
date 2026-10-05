module

public import SubdiffusiveProcess.Sobolev.AffineData

@[expose] public section

/-!
# The mean-zero representative of a Sobolev function

Subtracting the actual volume mean identifies a local H1 function with an
admissible competitor in the mean-zero Neumann space, preserving its weak
gradient. This is used to test the inverse response with the Dirichlet
minimizer in the nonnegativity proof for the diagonal response defect.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

/-- Subtract the volume mean from the function, using its actual constant Sobolev data. -/
def meanZeroSobolevRepresentative
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : volume.real (Ω : Set (SpatialCoordinates d)) ≠ 0)
    (u : weakSobolevGraph Ω) : meanZeroSobolevGraph Ω := by
  let c := (∫ x in (Ω : Set (SpatialCoordinates d)), u.val.1 x) /
    volume.real (Ω : Set (SpatialCoordinates d))
  refine ⟨u.val - (affineSobolev hΩ 0 c).val, ?_⟩
  rw [mem_meanZeroSobolevGraph_iff]
  refine ⟨(weakSobolevGraph Ω).sub_mem u.property (affineSobolev hΩ 0 c).property, ?_⟩
  change (∫ x in (Ω : Set (SpatialCoordinates d)), (u.val.1 - affineL2 hΩ 0 c) x) = 0
  calc
    _ = ∫ x in (Ω : Set (SpatialCoordinates d)), u.val.1 x - c := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub u.val.1 (affineL2 hΩ 0 c), affineL2_coeFn hΩ 0 c]
        with x hs hc
      simp only [hs, Pi.sub_apply, hc, affineSlope_apply, Pi.zero_apply, zero_mul,
        Finset.sum_const_zero, zero_add]
    _ = 0 := by
      rw [integral_sub ((Lp.memLp u.val.1).integrable (by norm_num)) (integrable_const _), integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
      change (∫ x in (Ω : Set (SpatialCoordinates d)), u.val.1 x) -
        volume.real (Ω : Set (SpatialCoordinates d)) *
          ((∫ x in (Ω : Set (SpatialCoordinates d)), u.val.1 x) /
            volume.real (Ω : Set (SpatialCoordinates d))) = 0
      field_simp
      ring

/-- Its function is the original function minus its volume mean, almost everywhere. -/
theorem meanZeroSobolevRepresentative_coeFn
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : volume.real (Ω : Set (SpatialCoordinates d)) ≠ 0)
    (u : weakSobolevGraph Ω) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (meanZeroSobolevRepresentative hΩ hvol u).val.1 x = u.val.1 x -
        (∫ y in (Ω : Set (SpatialCoordinates d)), u.val.1 y) /
          volume.real (Ω : Set (SpatialCoordinates d)) := by
  let c := (∫ y in (Ω : Set (SpatialCoordinates d)), u.val.1 y) /
    volume.real (Ω : Set (SpatialCoordinates d))
  filter_upwards [Lp.coeFn_sub u.val.1 (affineL2 hΩ 0 c), affineL2_coeFn hΩ 0 c]
    with x hs hc
  change (u.val.1 - affineL2 hΩ 0 c) x = u.val.1 x - c
  simp only [hs, Pi.sub_apply, hc, affineSlope_apply, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add]

/-- Mean subtraction preserves the whole actual weak gradient. -/
theorem meanZeroSobolevRepresentative_gradient
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : volume.real (Ω : Set (SpatialCoordinates d)) ≠ 0)
    (u : weakSobolevGraph Ω) :
    subspaceGradient (meanZeroSobolevGraph Ω) (meanZeroSobolevRepresentative hΩ hvol u) =
      sobolevGradient u.val := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => DomainL2 Ω)).injective
  funext i
  change u.val.2 i - domainConstantL2 (Ω := Ω) 0 = u.val.2 i
  have hz : domainConstantL2 (Ω := Ω) 0 = 0 := by
    apply Lp.ext
    filter_upwards [domainConstantL2_coeFn (Ω := Ω) 0,
      Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volume.restrict (Ω : Set (SpatialCoordinates d)))]
      with x hx hzero
    rw [hx, hzero]
    rfl
  rw [hz, sub_zero]

end SubdiffusiveProcess
