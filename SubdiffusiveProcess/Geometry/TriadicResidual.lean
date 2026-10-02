import SubdiffusiveProcess.Geometry.OddGridResidual
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Vanishing geometric remainder on the actual triadic grid

The odd grid with middle index `3^J / 2` has exactly `3^J` intervals per
coordinate. Its actual unresolved volume fraction is at most `d / 3^J`
and tends to zero. This limit is geometric and deterministic; it is taken
before any cutoff-uniform moment estimate in the reflection argument.
-/

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- The middle label in a coordinate subdivision of depth `J`. -/
def triadicHalf (J : ℕ) : ℕ := 3 ^ J / 2

/-- Every triadic subdivision has an odd number of coordinate intervals. -/
theorem two_mul_triadicHalf_add_one (J : ℕ) : 2 * triadicHalf J + 1 = 3 ^ J := by
  have ho : Odd (3 ^ J : ℕ) := (show Odd (3 : ℕ) by decide).pow
  have hm := Nat.odd_iff.mp ho
  have hdiv := Nat.mod_add_div (3 ^ J) 2
  unfold triadicHalf
  omega

/-- The real-valued coordinate denominator is the literal power `3^J`. -/
theorem triadic_denominator (J : ℕ) : 2 * (triadicHalf J : ℝ) + 1 = (3 : ℝ) ^ J := by
  exact_mod_cast two_mul_triadicHalf_add_one J

/-- The selected-plane remainder is bounded using the actual number of active directions. -/
theorem triadicUnresolved_volume_fraction_le_card (hd : 0 < d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (I : Finset (Fin d)) (J : ℕ) :
    volume.real (⋃ k ∈ oddGridUnresolved (triadicHalf J) I,
      (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))) /
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
        (I.card : ℝ) / (3 : ℝ) ^ J := by
  simpa only [triadic_denominator] using
    oddGridUnresolved_volume_fraction_le hd z hr (triadicHalf J) I

/-- The actual geometric remainder has the source bound `d * 3^(-J)`. -/
theorem triadicUnresolved_volume_fraction_le (hd : 0 < d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (I : Finset (Fin d)) (J : ℕ) :
    volume.real (⋃ k ∈ oddGridUnresolved (triadicHalf J) I,
      (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))) /
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
        (d : ℝ) / (3 : ℝ) ^ J := by
  apply (triadicUnresolved_volume_fraction_le_card hd z hr I J).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (I.card_le_univ.trans_eq (Fintype.card_fin d))

/-- The unresolved fraction vanishes on the concrete triadic cells. -/
theorem triadicUnresolved_volume_fraction_tendsto_zero (hd : 0 < d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (I : Finset (Fin d)) :
    Tendsto (fun J : ℕ =>
      volume.real (⋃ k ∈ oddGridUnresolved (triadicHalf J) I,
        (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d))) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) atTop (𝓝 0) := by
  apply squeeze_zero (fun J => div_nonneg (measureReal_nonneg) (centeredCube_volume_pos z hr).le)
    (triadicUnresolved_volume_fraction_le hd z hr I)
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 < 1)).const_mul (d : ℝ)
  simpa only [div_eq_mul_inv, one_mul, inv_pow, mul_zero] using h

end SubdiffusiveProcess
