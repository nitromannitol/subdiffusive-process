module

public import SubdiffusiveProcess.Analysis.ContinuousCubeCoefficient
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

/-! A continuous positive representative on a cube gives the corresponding
coefficient on a dilated cube, with its exact almost-everywhere pullback.
The construction supplies no estimate uniform over coefficients.
-/
open MeasureTheory Set
noncomputable section
namespace SubdiffusiveProcess

/-- Positive dilation maps a centered cube into the corresponding dilated cube. -/
theorem smul_mem_dilatedCube {d : ℕ} (z : SpatialCoordinates d) (r l : ℝ)
    (hr : 0 < r) (hl : 0 < l) (y : SpatialCoordinates d)
    (hy : y ∈ (centeredCube z r hr : Set (SpatialCoordinates d))) :
    l • y ∈ (centeredCube (l • z) (l * r) (mul_pos hl hr) : Set (SpatialCoordinates d)) := by
  change dist (l • y) (l • z) < l * r / 2
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hl]
  have hh := mul_lt_mul_of_pos_left hy hl
  change l * dist y z < l * (r / 2) at hh
  linarith only [hh]

/-- The dilated coefficient has the continuous pulled-back representative and exact scaling identity. -/
theorem exists_dilatedCubeCoefficient {d : ℕ} (z : SpatialCoordinates d) (r l : ℝ)
    (hr : 0 < r) (hl : 0 < l) (a : PositiveCoefficient (centeredCube z r hr))
    (f : SpatialCoordinates d → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (hrep : (a.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f) :
    ∃ A : PositiveCoefficient (centeredCube (l • z) (l * r) (mul_pos hl hr)),
      ((A.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube (l • z) (l * r) (mul_pos hl hr) : Set (SpatialCoordinates d))]
          fun x => f (l⁻¹ • x)) ∧
      (∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        a.val y = A.val (l • y)) := by
  let A := continuousCubeCoefficient (l • z) (l * r) (mul_pos hl hr)
    (fun x => f (l⁻¹ • x)) (hf.comp (continuous_const_smul _)) (fun x => hpos _)
  have hA := continuousCubeCoefficient_ae (l • z) (l * r) (mul_pos hl hr)
    (fun x => f (l⁻¹ • x)) (hf.comp (continuous_const_smul _)) (fun x => hpos _)
  refine ⟨A, hA, ?_⟩
  have hAr := (ae_restrict_iff' (centeredCube (l • z) (l * r) (mul_pos hl hr)).isOpen.measurableSet).mp hA
  have hpull := (Measure.quasiMeasurePreserving_smul volume hl.ne').ae hAr
  filter_upwards [hrep, ae_restrict_of_ae hpull,
    ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with y hy hAy hymem
  have hh := hAy (smul_mem_dilatedCube z r l hr hl y hymem)
  rw [smul_smul, inv_mul_cancel₀ hl.ne', one_smul] at hh
  exact hy.trans hh.symm

/-- A specified side length can be used without transporting a dependent coefficient after construction. -/
theorem exists_dilatedCubeCoefficient_of_side {d : ℕ} (z : SpatialCoordinates d) (r l R : ℝ)
    (hr : 0 < r) (hl : 0 < l) (hR : 0 < R) (hRl : R = l * r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (f : SpatialCoordinates d → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (hrep : (a.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f) :
    ∃ A : PositiveCoefficient (centeredCube (l • z) R hR),
      ((A.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube (l • z) R hR : Set (SpatialCoordinates d))]
          fun x => f (l⁻¹ • x)) ∧
      (∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        a.val y = A.val (l • y)) := by
  subst R
  exact exists_dilatedCubeCoefficient z r l hr hl a f hf hpos hrep

end SubdiffusiveProcess
