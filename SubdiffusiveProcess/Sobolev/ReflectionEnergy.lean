module

public import SubdiffusiveProcess.Sobolev.ReflectionGraph
public import SubdiffusiveProcess.Sobolev.AffineResponses

@[expose] public section

/-! # Reflected coefficients, mean-zero data and their actual energies

The coefficient is composed with the same spatial map as the Sobolev
function. The two gradient signs cancel in the scalar bilinear energy.
All statements are finite-cutoff identities, without a random-law premise.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {U Ω : Opens (SpatialCoordinates d)}

/-- The actual reflected positive bounded scalar coefficient. -/
def reflectionCoefficient (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (a : PositiveCoefficient Ω) : PositiveCoefficient U := by
  refine ⟨reflectionLp z I hU a.val, ?_⟩
  obtain ⟨c, hc, ha⟩ := a.property
  refine ⟨c, hc, ?_⟩
  have hm := coordinateReflection_domain_measurePreserving z I hU
  filter_upwards [reflectionLp_coeFn z I hU a.val,
    hm.quasiMeasurePreserving.ae ha] with x he hx
  exact he.symm ▸ hx

/-- The coefficient pullback has precisely the composed original values almost everywhere. -/
theorem reflectionCoefficient_coeFn (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (a : PositiveCoefficient Ω) :
    ((reflectionCoefficient z I hU a).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))] a.val ∘ coordinateReflection z I :=
  reflectionLp_coeFn z I hU a.val

/-- Reflection back gives the original coefficient, including its L-infinity class. -/
theorem reflectionCoefficient_inverse (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (a : PositiveCoefficient Ω) :
    reflectionCoefficient z I (coordinateReflection_preimage_reverse z I hU)
      (reflectionCoefficient z I hU a) = a :=
  Subtype.ext (reflectionLp_inverse z I hU a.val)

/-- The complete scalar bilinear energy is unchanged by reflection of all its inputs. -/
theorem sobolevCoefficientForm_reflection (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (a : PositiveCoefficient Ω) (u v : SobolevData Ω) :
    sobolevCoefficientForm (reflectionCoefficient z I hU a)
      (reflectionSobolevData z I hU u) (reflectionSobolevData z I hU v) =
      sobolevCoefficientForm a u v := by
  rw [sobolevCoefficientForm_apply, sobolevCoefficientForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∫ x in (U : Set (SpatialCoordinates d)),
        a.val (coordinateReflection z I x) *
          (u.2 i (coordinateReflection z I x) * v.2 i (coordinateReflection z I x)) := by
      apply integral_congr_ae
      filter_upwards [reflectionCoefficient_coeFn z I hU a,
        Lp.coeFn_smul (coordinateReflectionSign I i) (reflectionLp z I hU (u.2 i)),
        Lp.coeFn_smul (coordinateReflectionSign I i) (reflectionLp z I hU (v.2 i)),
        reflectionLp_coeFn z I hU (u.2 i), reflectionLp_coeFn z I hU (v.2 i)]
        with x ha hs ht hu hv
      change (reflectionCoefficient z I hU a).val x *
        ((coordinateReflectionSign I i • reflectionLp z I hU (u.2 i)) x *
         (coordinateReflectionSign I i • reflectionLp z I hU (v.2 i)) x) = _
      rw [ha, hs, ht]
      simp only [Pi.smul_apply, smul_eq_mul, hu, hv, Function.comp_apply]
      calc
        _ = coordinateReflectionSign I i ^ 2 *
          (a.val (coordinateReflection z I x) *
            (u.2 i (coordinateReflection z I x) * v.2 i (coordinateReflection z I x))) := by ring
        _ = _ := by rw [coordinateReflectionSign_sq, one_mul]
    _ = _ := (coordinateReflection_domain_measurePreserving z I hU).integral_comp
      (coordinateReflectionEquiv z I).toHomeomorph.measurableEmbedding
      (fun y => a.val y * (u.2 i y * v.2 i y))

/-- Reflection preserves the actual mean-zero condition on finite-volume domains. -/
theorem reflectionSobolevData_mem_meanZero_iff (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    [IsFiniteMeasure (volume.restrict (U : Set (SpatialCoordinates d)))]
    (u : SobolevData Ω) :
    reflectionSobolevData z I hU u ∈ meanZeroSobolevGraph U ↔ u ∈ meanZeroSobolevGraph Ω := by
  rw [mem_meanZeroSobolevGraph_iff, mem_meanZeroSobolevGraph_iff,
    reflectionSobolevData_mem_weak_iff]
  change (u ∈ weakSobolevGraph Ω ∧
    (∫ x in (U : Set (SpatialCoordinates d)), reflectionLp z I hU u.1 x) = 0) ↔ _
  rw [integral_reflectionLp]

end SubdiffusiveProcess
