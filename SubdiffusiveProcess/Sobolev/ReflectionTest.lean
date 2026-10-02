import SubdiffusiveProcess.Geometry.ReflectionCalculus
import SubdiffusiveProcess.Sobolev.ReflectionLp

/-! # Reflection of smooth compactly supported tests

Support, smoothness and coordinate derivatives are transported explicitly.
These are the tests used to prove reflection of weak Sobolev derivatives.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {U Ω : Opens (SpatialCoordinates d)}

/-- Compose a smooth test with the actual reflection of its domain. -/
def reflectionTest (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) : 𝓓(U, ℝ) where
  toFun := φ ∘ coordinateReflection z I
  contDiff' := φ.contDiff.comp (coordinateReflection_contDiff z I)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph
    (coordinateReflectionEquiv z I).toHomeomorph
  tsupport_subset' := by
    change tsupport (φ ∘ (coordinateReflectionEquiv z I).toHomeomorph) ⊆ U
    rw [tsupport_comp_eq_preimage]
    intro x hx
    rw [← hU]
    exact φ.tsupport_subset hx

/-- The test pullback has the literal composed values. -/
theorem reflectionTest_apply (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) (x : SpatialCoordinates d) :
    reflectionTest z I hU φ x = φ (coordinateReflection z I x) := rfl

/-- The reflected classical partial derivative has its coordinate sign. -/
theorem reflectionTest_fderiv (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) (x : SpatialCoordinates d) (i : Fin d) :
    fderiv ℝ (reflectionTest z I hU φ) x (Pi.single i 1) =
      coordinateReflectionSign I i * fderiv ℝ φ (coordinateReflection z I x) (Pi.single i 1) :=
  fderiv_comp_coordinateReflection z I φ.contDiff x i

/-- Smooth tests and actual L2 classes give the same pullback. -/
theorem testL2_reflectionTest (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) :
    testL2 (reflectionTest z I hU φ) = reflectionLp z I hU (testL2 φ) := by
  apply Lp.ext
  have hm := coordinateReflection_domain_measurePreserving z I hU
  filter_upwards [testL2_coeFn (reflectionTest z I hU φ),
    reflectionLp_coeFn z I hU (testL2 φ),
    hm.quasiMeasurePreserving.ae_eq (testL2_coeFn φ)] with x hx hy hz
  exact hx.trans (hz.symm.trans hy.symm)

/-- Smooth derivative classes give the signed L2 pullback. -/
theorem testPartialL2_reflectionTest (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) (i : Fin d) :
    testPartialL2 (reflectionTest z I hU φ) i =
      coordinateReflectionSign I i • reflectionLp z I hU (testPartialL2 φ i) := by
  apply Lp.ext
  have hm := coordinateReflection_domain_measurePreserving z I hU
  filter_upwards [testPartialL2_coeFn (reflectionTest z I hU φ) i,
    Lp.coeFn_smul (coordinateReflectionSign I i) (reflectionLp z I hU (testPartialL2 φ i)),
    reflectionLp_coeFn z I hU (testPartialL2 φ i),
    hm.quasiMeasurePreserving.ae_eq (testPartialL2_coeFn φ i)] with x hx hs hy hz
  simp only [Function.comp_apply] at hy hz
  rw [hx, hs]
  simp only [Pi.smul_apply, smul_eq_mul, hy, hz, reflectionTest_fderiv]

/-- Two successive test pullbacks restore the original test function. -/
theorem reflectionTest_inverse (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) :
    reflectionTest z I (coordinateReflection_preimage_reverse z I hU)
      (reflectionTest z I hU φ) = φ := by
  apply TestFunction.ext
  intro x
  exact congrArg φ (coordinateReflection_involutive z I x)

end SubdiffusiveProcess
