module

public import SubdiffusiveProcess.Geometry.Cube
public import Homogenization.Ambient.Euclidean


@[expose] public section

/-! # Euclidean diameter of a centered cube

The spatial carrier uses the sup norm. This estimate explicitly computes
Euclidean distance for the fractional-energy kernel in the trace proof.
-/

open MeasureTheory Set TopologicalSpace
open Homogenization
noncomputable section
namespace SubdiffusiveProcess

/-- Two points of a cube of side r have Euclidean distance at most sqrt(d) times r. -/
theorem euclideanDist_le_sqrt_dim_mul_side_of_mem_centeredCube
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {x y : SpatialCoordinates d}
    (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hy : y ∈ (centeredCube z r hr : Set (SpatialCoordinates d))) :
    Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) ≤ Real.sqrt d * r := by
  rw [centeredCube_eq_pi z hr] at hx hy
  have hcoord : ∀ i : Fin d, |x i - y i| ≤ r := by
    intro i
    rw [abs_le]
    have hxi := hx i (Set.mem_univ i)
    have hyi := hy i (Set.mem_univ i)
    exact ⟨by linarith [hxi.1, hxi.2, hyi.1, hyi.2],
      by linarith [hxi.1, hxi.2, hyi.1, hyi.2]⟩
  have hsum : (∑ i : Fin d, (x i - y i) ^ 2) ≤ (d : ℝ) * r ^ 2 := by
    calc
      (∑ i : Fin d, (x i - y i) ^ 2) ≤ ∑ _i : Fin d, r ^ 2 := by
        exact Finset.sum_le_sum fun i _ => by
          have hi := hcoord i
          nlinarith [sq_abs (x i - y i), abs_nonneg (x i - y i)]
      _ = (d : ℝ) * r ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) ≤
        Real.sqrt ((d : ℝ) * r ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * r := by
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hr.le]

end SubdiffusiveProcess
