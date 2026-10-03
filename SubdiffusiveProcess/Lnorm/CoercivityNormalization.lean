module

public import SubdiffusiveProcess.Lane4.Carriers

@[expose] public section

/-! Convert normalized fractional coercivity to the physical-volume energy bound.
This algebraic conversion does not assert a uniform pathwise coercivity constant. -/

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace SubdiffusiveProcess.Lnorm
open SubdiffusiveProcess.Lane4

/-- Multiplying the normalized scalar fractional square norm by the volume restores the unnormalized L2 term. -/
theorem volume_mul_cubeFractionalSqNorm {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (v : DomainL2 (centeredCube z r hr))
    (hV : volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ 0) :
    volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
      cubeFractionalSqNorm hd z r hr s v =
    ‖v‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
      ((cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v)).toReal) ^ 2 := by
  simp only [cubeFractionalSqNorm, cubeFractionalVecSqNorm,
    cubeFractionalVecSeminormSq, Fin.sum_univ_one]
  rw [mul_add, mul_div_cancel₀ _ hV, add_comm]

/-- The cube's positive finite volume converts a normalized coercivity estimate into the compactness carrier. -/
theorem fractional_coercivity_unnormalized {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (v : DomainL2 (centeredCube z r hr)) (K e : ℝ)
    (h : cubeFractionalSqNorm hd z r hr threeQuarterOrder v ≤ K * e) :
    ‖v‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
      ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
        (fun _ : Fin 1 => v)).toReal) ^ 2 ≤
      (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) * K) * e := by
  have hV : 0 < volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    centeredCube_volume_pos z hr
  rw [← volume_mul_cubeFractionalSqNorm hd z r hr threeQuarterOrder v hV.ne', mul_assoc]
  exact mul_le_mul_of_nonneg_left h hV.le

end SubdiffusiveProcess.Lnorm
