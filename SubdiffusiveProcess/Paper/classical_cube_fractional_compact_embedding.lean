import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Paper.inputs_classical_e4_rellich

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory
open SubdiffusiveProcess

namespace Paper

/-- Classical Rellich compactness for the fractional Sobolev space on a fixed cube.
PROVED as the `s = 3/4` case of `inputs_classical_e4_rellich`: the carrier norm bounds both
the seminorm and the normalized `L²` norm. -/
theorem classical_cube_fractional_compact_embedding
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (threeQuarters : Set.Ioo (0 : ℝ) 1)
    (hthreeQuarters : (threeQuarters : ℝ) = 3 / 4)
    (w : ℕ → CubeFractionalL2 (k := 1) hd z r hr threeQuarters) (M : ℝ)
    (hbound : ∀ n : ℕ,
      cubeFractionalL2Norm hd z r hr threeQuarters (w n) ≤ M) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ wlim : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => ‖(w (sigma n)).val 0 - wlim‖) atTop (nhds 0) := by
  classical
  have hvol := SubdiffusiveProcess.centeredCube_volume_pos z hr
  have hrs : 0 < r ^ (-(threeQuarters : ℝ)) := Real.rpow_pos_of_pos hr _
  let v : ℕ → DomainL2 (centeredCube z r hr) := fun n => (w n).val 0
  have hval : ∀ n, (fun _ : Fin 1 => v n) = (w n).val := fun n => by
    funext i; rw [Subsingleton.elim i 0]
  have hsemi_fin : ∀ n, cubeFractionalL2Seminorm hd z r hr threeQuarters
      (fun _ : Fin 1 => v n) < ⊤ := fun n => by rw [hval n]; exact (w n).property
  have hparts : ∀ n,
      (cubeFractionalL2Seminorm hd z r hr threeQuarters (fun _ : Fin 1 => v n)).toReal ≤ M ∧
      ‖v n‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
        M * r ^ (threeQuarters : ℝ) := by
    intro n
    have h := hbound n
    unfold cubeFractionalL2Norm at h
    have hsum : Real.sqrt (∑ i : Fin 1, ‖(w n).val i‖ ^ 2) = ‖v n‖ := by
      rw [Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]
    rw [hsum, ← hval n] at h
    have h1 : 0 ≤ (cubeFractionalL2Seminorm hd z r hr threeQuarters
        (fun _ : Fin 1 => v n)).toReal := ENNReal.toReal_nonneg
    have h2 : 0 ≤ ‖v n‖ / Real.sqrt (volume.real (centeredCube z r hr :
        Set (SpatialCoordinates d))) := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    have h3 := mul_nonneg hrs.le h2
    refine ⟨by linarith, ?_⟩
    have h4 : r ^ (-(threeQuarters : ℝ)) * (‖v n‖ / Real.sqrt (volume.real (centeredCube z r hr :
        Set (SpatialCoordinates d)))) ≤ M := by linarith
    calc ‖v n‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))
        = r ^ (threeQuarters : ℝ) * (r ^ (-(threeQuarters : ℝ)) * (‖v n‖ /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))) := by
          rw [← mul_assoc, ← Real.rpow_add hr, add_neg_cancel, Real.rpow_zero, one_mul]
      _ ≤ r ^ (threeQuarters : ℝ) * M :=
          mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hr.le _)
      _ = M * r ^ (threeQuarters : ℝ) := mul_comm _ _
  have hbound' : ∀ n, SubdiffusiveProcess.Lane4.cubeFractionalSqNorm hd z r hr threeQuarters (v n) ≤
      M ^ 2 + (M * r ^ (threeQuarters : ℝ)) ^ 2 := by
    intro n
    obtain ⟨hA, hB⟩ := hparts n
    have hA0 : 0 ≤ (cubeFractionalL2Seminorm hd z r hr threeQuarters
        (fun _ : Fin 1 => v n)).toReal := ENNReal.toReal_nonneg
    have hB0 : 0 ≤ ‖v n‖ / Real.sqrt (volume.real (centeredCube z r hr :
        Set (SpatialCoordinates d))) := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    have hsq : (∑ i : Fin 1, ‖(fun _ : Fin 1 => v n) i‖ ^ 2) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) =
        (‖v n‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^ 2 := by
      rw [Fin.sum_univ_one, div_pow, Real.sq_sqrt hvol.le]
    unfold SubdiffusiveProcess.Lane4.cubeFractionalSqNorm SubdiffusiveProcess.Lane4.cubeFractionalVecSqNorm
      SubdiffusiveProcess.Lane4.cubeFractionalVecSeminormSq
    rw [hsq]
    exact add_le_add (pow_le_pow_left₀ hA0 hA 2) (pow_le_pow_left₀ hB0 hB 2)
  obtain ⟨phi, w0, hphi, hconv⟩ := inputs_classical_e4_rellich d hd threeQuarters z r hr v
    (M ^ 2 + (M * r ^ (threeQuarters : ℝ)) ^ 2) hsemi_fin hbound'
  exact ⟨phi, hphi, w0, tendsto_iff_norm_sub_tendsto_zero.mp hconv⟩

end Paper
