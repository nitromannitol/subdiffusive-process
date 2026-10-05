module

public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Sobolev.CoordinatePairing
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
@[expose] public section

open MeasureTheory Set TopologicalSpace
namespace SubdiffusiveProcess

/-- Every normalized dual test quotient is bounded by the scaled averaged vector L2 norm of the field. The denominator is positive for a nonzero test; the nonnegative additional term will be the fractional seminorm in M. -/
theorem normalized_coordinate_pairing_div_bound
    {d k : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : ℝ) (F φ : Fin k → DomainL2 (centeredCube z r hr))
    (A : ℝ) (hA : 0 ≤ A) :
    (φ ≠ 0 → 0 < A + r ^ (-s) *
      (Real.sqrt (∑ i : Fin k, ‖φ i‖ ^ 2) /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))) ∧
    |(volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∑ i : Fin k, F i x * φ i x| /
      (A + r ^ (-s) *
        (Real.sqrt (∑ i : Fin k, ‖φ i‖ ^ 2) /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))) ≤
      r ^ s * (Real.sqrt (∑ i : Fin k, ‖F i‖ ^ 2) /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
  constructor
  · intro hφ
    have hex : ∃ i : Fin k, φ i ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hφ
      funext i
      exact hn i
    obtain ⟨i, hi⟩ := hex
    have hsum : 0 < ∑ j : Fin k, ‖φ j‖ ^ 2 := by
      apply Finset.sum_pos'
      · intro j hj
        positivity
      · exact ⟨i, Finset.mem_univ i, sq_pos_of_pos (norm_pos_iff.mpr hi)⟩
    have hp : 0 < Real.sqrt (∑ j : Fin k, ‖φ j‖ ^ 2) := Real.sqrt_pos.2 hsum
    have hV : 0 < volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      centeredCube_volume_pos z hr
    have hsV : 0 < Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      Real.sqrt_pos.2 hV
    have hrs : 0 < r ^ (-s) := Real.rpow_pos_of_pos hr _
    positivity
  · by_cases hφ : φ = 0
    · subst φ
      have hright : 0 ≤ r ^ s *
          (Real.sqrt (∑ i : Fin k, ‖F i‖ ^ 2) /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
        positivity
      have hzero :
          (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∑ i : Fin k, F i x * (0 : Fin k → DomainL2 (centeredCube z r hr)) i x) = 0 := by
        have hzabs :
            |∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∑ i : Fin k, F i x * (0 : Fin k → DomainL2 (centeredCube z r hr)) i x| ≤ 0 := by
          simpa using abs_integral_coordinate_pairing_le F
            (0 : Fin k → DomainL2 (centeredCube z r hr))
        exact abs_eq_zero.mp (le_antisymm hzabs (abs_nonneg _))
      rw [hzero]
      simpa only [abs_zero, mul_zero, zero_div] using hright
    · have hV : 0 < volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
        centeredCube_volume_pos z hr
      have hsV : 0 < Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) :=
        Real.sqrt_pos.2 hV
      have hex : ∃ i : Fin k, φ i ≠ 0 := by
        by_contra hn
        push Not at hn
        apply hφ
        funext i
        exact hn i
      obtain ⟨i, hi⟩ := hex
      have hsum : 0 < ∑ j : Fin k, ‖φ j‖ ^ 2 := by
        apply Finset.sum_pos'
        · intro j hj
          positivity
        · exact ⟨i, Finset.mem_univ i, sq_pos_of_pos (norm_pos_iff.mpr hi)⟩
      have hp : 0 < Real.sqrt (∑ j : Fin k, ‖φ j‖ ^ 2) := Real.sqrt_pos.2 hsum
      have hrs : 0 < r ^ (-s) := Real.rpow_pos_of_pos hr _
      have hden : 0 < A + r ^ (-s) *
          (Real.sqrt (∑ i : Fin k, ‖φ i‖ ^ 2) /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
        positivity
      have hpair := abs_integral_coordinate_pairing_le F φ
      rw [div_le_iff₀ hden]
      calc
        |(volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
            ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∑ i : Fin k, F i x * φ i x|
          ≤ (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
              (Real.sqrt (∑ i : Fin k, ‖F i‖ ^ 2) *
                Real.sqrt (∑ i : Fin k, ‖φ i‖ ^ 2)) := by
            rw [abs_mul, abs_of_pos (inv_pos.mpr hV)]
            exact mul_le_mul_of_nonneg_left hpair (inv_nonneg.mpr hV.le)
        _ ≤ (r ^ s * (Real.sqrt (∑ i : Fin k, ‖F i‖ ^ 2) /
              Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))) *
            (A + r ^ (-s) *
              (Real.sqrt (∑ i : Fin k, ‖φ i‖ ^ 2) /
                Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))) := by
            have hq : 0 ≤ Real.sqrt (∑ i : Fin k, ‖F i‖ ^ 2) := Real.sqrt_nonneg _
            have hrs' : r ^ s * r ^ (-s) = 1 := by
              rw [← Real.rpow_add hr]
              norm_num
            have hsV2 : Real.sqrt (volume.real
                (centeredCube z r hr : Set (SpatialCoordinates d))) ^ 2 =
                volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
              Real.sq_sqrt hV.le
            have hRHS : 0 ≤ r ^ s *
                (Real.sqrt (∑ i : Fin k, ‖F i‖ ^ 2) /
                  Real.sqrt (volume.real
                    (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
              positivity
            have hbase :
                (r ^ s * (Real.sqrt (∑ i : Fin k, ‖F i‖ ^ 2) /
                  Real.sqrt (volume.real
                    (centeredCube z r hr : Set (SpatialCoordinates d))))) *
                  (r ^ (-s) * (Real.sqrt (∑ i : Fin k, ‖φ i‖ ^ 2) /
                    Real.sqrt (volume.real
                      (centeredCube z r hr : Set (SpatialCoordinates d))))) =
                (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
                  (Real.sqrt (∑ i : Fin k, ‖F i‖ ^ 2) *
                    Real.sqrt (∑ i : Fin k, ‖φ i‖ ^ 2)) := by
              field_simp
              calc
                r ^ s * Real.sqrt (∑ x, ‖F x‖ ^ 2) * r ^ (-s) *
                    volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
                    = (r ^ s * r ^ (-s)) *
                        (Real.sqrt (∑ x, ‖F x‖ ^ 2) *
                          volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by ring
                _ = _ := by rw [hrs', hsV2, one_mul]
            rw [← hbase]
            exact mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_left hA) hRHS

end SubdiffusiveProcess
