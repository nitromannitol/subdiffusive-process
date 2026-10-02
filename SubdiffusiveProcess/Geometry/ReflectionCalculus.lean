import SubdiffusiveProcess.Geometry.CoordinateReflection
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Smooth coordinate-reflection calculus

The derivative is the same fixed diagonal sign map at every point. This
chain rule will be used on actual compactly supported smooth tests in the
weak-gradient equation, rather than assumed as Sobolev invariance.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- The derivative sign in each coordinate selected for reflection. -/
def coordinateReflectionSign (I : Finset (Fin d)) (i : Fin d) : ℝ :=
  if i ∈ I then -1 else 1

/-- Every reflection derivative sign has squared value one. -/
theorem coordinateReflectionSign_sq (I : Finset (Fin d)) (i : Fin d) :
    coordinateReflectionSign I i ^ 2 = 1 := by
  unfold coordinateReflectionSign
  split_ifs <;> norm_num

/-- The literal diagonal derivative map, on the original coordinate space. -/
def coordinateReflectionDerivative (I : Finset (Fin d)) :
    SpatialCoordinates d →L[ℝ] SpatialCoordinates d :=
  ContinuousLinearMap.pi (fun i => coordinateReflectionSign I i • ContinuousLinearMap.proj i)

/-- Its action on each coordinate basis vector keeps only that coordinate's sign. -/
theorem coordinateReflectionDerivative_single (I : Finset (Fin d)) (i : Fin d) :
    coordinateReflectionDerivative I (Pi.single i 1) =
      coordinateReflectionSign I i • (Pi.single i 1 : SpatialCoordinates d) := by
  funext j
  by_cases h : j = i
  · subst j
    simp only [coordinateReflectionDerivative, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_same,
      Pi.smul_apply, smul_eq_mul]
  · simp only [coordinateReflectionDerivative, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_of_ne h,
      Pi.smul_apply, smul_eq_mul, mul_zero]

/-- The reflection has the displayed derivative at every spatial point. -/
theorem coordinateReflection_hasFDerivAt (z : SpatialCoordinates d) (I : Finset (Fin d))
    (x : SpatialCoordinates d) :
    HasFDerivAt (coordinateReflection z I) (coordinateReflectionDerivative I) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  by_cases hi : i ∈ I
  · have he : coordinateReflectionSign I i •
        (ContinuousLinearMap.proj i : SpatialCoordinates d →L[ℝ] ℝ) =
        -ContinuousLinearMap.proj i := by
      ext y
      simp [coordinateReflectionSign, hi]
    change HasFDerivAt (fun y : SpatialCoordinates d => coordinateReflection z I y i)
      (coordinateReflectionSign I i • ContinuousLinearMap.proj i) x
    rw [he]
    simpa only [coordinateReflection, hi, if_true] using
      (hasFDerivAt_apply (𝕜 := ℝ) i x).const_sub (2 * z i)
  · simpa [coordinateReflection, coordinateReflectionSign, hi] using
      hasFDerivAt_apply (𝕜 := ℝ) i x

/-- The affine coordinate reflection is smooth on the full spatial carrier. -/
theorem coordinateReflection_contDiff (z : SpatialCoordinates d) (I : Finset (Fin d)) :
    ContDiff ℝ ∞ (coordinateReflection z I) := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i ∈ I
  · simpa only [coordinateReflection, hi, if_pos] using
      (contDiff_const.sub (contDiff_apply ℝ ℝ i) :
        ContDiff ℝ ∞ (fun x : SpatialCoordinates d => 2 * z i - x i))
  · simpa only [coordinateReflection, hi, if_neg] using (contDiff_apply ℝ ℝ i :
      ContDiff ℝ ∞ (fun x : SpatialCoordinates d => x i))

/-- The actual smooth-test chain rule, with the correct derivative sign. -/
theorem fderiv_comp_coordinateReflection (z : SpatialCoordinates d) (I : Finset (Fin d))
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : SpatialCoordinates d) (i : Fin d) :
    fderiv ℝ (f ∘ coordinateReflection z I) x (Pi.single i 1) =
      coordinateReflectionSign I i * fderiv ℝ f (coordinateReflection z I x) (Pi.single i 1) := by
  rw [fderiv_comp x (hf.differentiable (by norm_num) _) (coordinateReflection_hasFDerivAt z I x).differentiableAt,
    (coordinateReflection_hasFDerivAt z I x).fderiv, ContinuousLinearMap.comp_apply,
    coordinateReflectionDerivative_single, map_smul, smul_eq_mul]

end SubdiffusiveProcess
