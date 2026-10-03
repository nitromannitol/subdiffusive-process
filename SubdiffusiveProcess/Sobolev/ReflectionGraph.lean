module

public import SubdiffusiveProcess.Sobolev.ReflectionTest
public import SubdiffusiveProcess.Sobolev.KilledGraph

@[expose] public section

/-! # Reflection preserves the actual Sobolev graphs

Weak derivatives are transported using the smooth-test chain rule and L2
inner products. The killed space is then transported by continuity and its
literal definition as the closure of compactly supported smooth data.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {U Ω : Opens (SpatialCoordinates d)}

/-- Pull back the function and the signed coordinate gradients as a continuous linear map. -/
def reflectionSobolevData (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U) :
    SobolevData Ω →L[ℝ] SobolevData U :=
  ((reflectionLp z I hU).toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (ContinuousLinearMap.pi fun i => coordinateReflectionSign I i •
      ((reflectionLp z I hU).toContinuousLinearMap.comp
        ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _))))

/-- The smooth-data graph is transported by the actual smooth test pullback. -/
theorem reflectionSobolevData_smooth (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) :
    reflectionSobolevData z I hU (smoothSobolevData φ) =
      smoothSobolevData (reflectionTest z I hU φ) := by
  apply Prod.ext
  · exact (testL2_reflectionTest z I hU φ).symm
  · funext i
    exact (testPartialL2_reflectionTest z I hU φ i).symm

/-- Reflection transforms the distributional derivative test by its coordinate sign. -/
theorem weakGradientTest_reflection (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) (i : Fin d) (u : SobolevData Ω) :
    weakGradientTest (reflectionTest z I hU φ) i (reflectionSobolevData z I hU u) =
      coordinateReflectionSign I i * weakGradientTest φ i u := by
  change inner ℝ (testL2 (reflectionTest z I hU φ))
      (coordinateReflectionSign I i • reflectionLp z I hU (u.2 i)) +
    inner ℝ (testPartialL2 (reflectionTest z I hU φ) i) (reflectionLp z I hU u.1) =
      coordinateReflectionSign I i * (inner ℝ (testL2 φ) (u.2 i) +
        inner ℝ (testPartialL2 φ i) u.1)
  rw [testL2_reflectionTest, testPartialL2_reflectionTest,
    real_inner_smul_right, real_inner_smul_left,
    (reflectionLp z I hU (p := 2)).inner_map_map (testL2 φ) (u.2 i),
    (reflectionLp z I hU (p := 2)).inner_map_map (testPartialL2 φ i) u.1, mul_add]

/-- The pullback of any actual weak-gradient pair again has actual weak derivatives. -/
theorem reflectionSobolevData_mem_weak (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {u : SobolevData Ω} (hu : u ∈ weakSobolevGraph Ω) :
    reflectionSobolevData z I hU u ∈ weakSobolevGraph U := by
  simp only [weakSobolevGraph, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe] at hu ⊢
  intro ψ i
  let φ := reflectionTest z I (coordinateReflection_preimage_reverse z I hU) ψ
  have hinv : reflectionTest z I hU φ = ψ :=
    reflectionTest_inverse z I (coordinateReflection_preimage_reverse z I hU) ψ
  have h := weakGradientTest_reflection z I hU φ i u
  rw [hinv, hu φ i, mul_zero] at h
  exact h

/-- Expose the killed graph as the closure of the literal smooth-data range. -/
theorem killedSobolevGraph_coe_eq_closure :
    (killedSobolevGraph Ω : Set (SobolevData Ω)) =
      closure (Set.range (smoothSobolevData (Ω := Ω))) := by
  rw [killedSobolevGraph, Submodule.topologicalClosure_coe, LinearMap.coe_range]
  rfl

/-- Continuity transports the whole killed closure, not just its smooth generators. -/
theorem reflectionSobolevData_mem_killed (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {u : SobolevData Ω} (hu : u ∈ killedSobolevGraph Ω) :
    reflectionSobolevData z I hU u ∈ killedSobolevGraph U := by
  have hm : Set.MapsTo (reflectionSobolevData z I hU)
      (Set.range (smoothSobolevData (Ω := Ω)))
      (killedSobolevGraph U : Set (SobolevData U)) := by
    rintro v ⟨φ, rfl⟩
    rw [reflectionSobolevData_smooth]
    exact smoothSobolevData_mem_killed _
  apply hm.closure_left (reflectionSobolevData z I hU).continuous
    (isClosed_killedSobolevGraph (Ω := U))
  rw [← killedSobolevGraph_coe_eq_closure]
  exact hu

/-- Applying the Sobolev pullback twice restores both the function and gradient. -/
theorem reflectionSobolevData_inverse (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (u : SobolevData Ω) :
    reflectionSobolevData z I (coordinateReflection_preimage_reverse z I hU)
      (reflectionSobolevData z I hU u) = u := by
  apply Prod.ext
  · exact reflectionLp_inverse z I hU u.1
  · funext i
    change coordinateReflectionSign I i •
      reflectionLp z I (coordinateReflection_preimage_reverse z I hU)
        (coordinateReflectionSign I i • reflectionLp z I hU (u.2 i)) = u.2 i
    rw [map_smul, smul_smul, ← pow_two, coordinateReflectionSign_sq, one_smul,
      reflectionLp_inverse]

/-- Reflection gives an equivalence of weak-gradient membership. -/
theorem reflectionSobolevData_mem_weak_iff (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (u : SobolevData Ω) :
    reflectionSobolevData z I hU u ∈ weakSobolevGraph U ↔ u ∈ weakSobolevGraph Ω := by
  constructor
  · intro hu
    have h := reflectionSobolevData_mem_weak z I
      (coordinateReflection_preimage_reverse z I hU) hu
    rwa [reflectionSobolevData_inverse] at h
  · exact reflectionSobolevData_mem_weak z I hU

/-- Reflection gives an equivalence of zero-boundary Sobolev membership. -/
theorem reflectionSobolevData_mem_killed_iff (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (u : SobolevData Ω) :
    reflectionSobolevData z I hU u ∈ killedSobolevGraph U ↔ u ∈ killedSobolevGraph Ω := by
  constructor
  · intro hu
    have h := reflectionSobolevData_mem_killed z I
      (coordinateReflection_preimage_reverse z I hU) hu
    rwa [reflectionSobolevData_inverse] at h
  · exact reflectionSobolevData_mem_killed z I hU

end SubdiffusiveProcess
