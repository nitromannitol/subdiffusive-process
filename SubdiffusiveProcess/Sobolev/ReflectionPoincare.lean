module

public import SubdiffusiveProcess.Sobolev.ReflectionSpaces

@[expose] public section

/-! # Ordinary Poincare inequalities survive reflection with the same constant

Both the function L2 norm and the Hilbert gradient norm are unchanged.
The actual competitor bijections then transport coercivity; it need not be
assumed separately on the reflected domain.
-/
open MeasureTheory Set TopologicalSpace
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {U Ω : Opens (SpatialCoordinates d)}

/-- Reflection preserves the function component's actual L2 norm. -/
theorem reflectionSobolevData_fst_norm (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (u : SobolevData Ω) :
    ‖(reflectionSobolevData z I hU u).1‖ = ‖u.1‖ := reflectionLp_norm z I hU u.1

/-- The sum-of-squares Hilbert norm of the actual gradient is preserved. -/
theorem reflectionSobolevData_gradient_norm (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (u : SobolevData Ω) :
    ‖sobolevGradient (reflectionSobolevData z I hU u)‖ = ‖sobolevGradient u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [sobolevGradient_norm_sq, sobolevGradient_norm_sq]
  apply Finset.sum_congr rfl
  intro i _
  change ‖coordinateReflectionSign I i • reflectionLp z I hU (u.2 i)‖^2 = ‖u.2 i‖^2
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, coordinateReflectionSign_sq,
    one_mul, reflectionLp_norm]

/-- Killed Poincare coercivity transfers through the actual reflection bijection. -/
theorem killed_poincare_reflection (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖) :
    ∃ K : ℝ≥0, ∀ u : killedSobolevGraph U,
      ‖(u : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) u‖ := by
  obtain ⟨K, hK⟩ := hP
  refine ⟨K, ?_⟩
  intro u
  obtain ⟨v, rfl⟩ := (reflectionKilledEquiv z I hU).surjective u
  change ‖(reflectionSobolevData z I hU v.val).1‖ ≤
    K * ‖sobolevGradient (reflectionSobolevData z I hU v.val)‖
  rw [reflectionSobolevData_fst_norm, reflectionSobolevData_gradient_norm]
  exact hK v

/-- Mean-zero Poincare coercivity transfers with the same original constant. -/
theorem meanZero_poincare_reflection (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    [IsFiniteMeasure (volume.restrict (U : Set (SpatialCoordinates d)))]
    (hP : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) u‖) :
    ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph U,
      ‖(u : SobolevData U).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph U) u‖ := by
  obtain ⟨K, hK⟩ := hP
  refine ⟨K, ?_⟩
  intro u
  obtain ⟨v, rfl⟩ := (reflectionMeanZeroEquiv z I hU).surjective u
  change ‖(reflectionSobolevData z I hU v.val).1‖ ≤
    K * ‖sobolevGradient (reflectionSobolevData z I hU v.val)‖
  rw [reflectionSobolevData_fst_norm, reflectionSobolevData_gradient_norm]
  exact hK v

end SubdiffusiveProcess
