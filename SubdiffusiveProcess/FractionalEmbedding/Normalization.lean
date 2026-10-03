module

public import SubdiffusiveProcess.Lane4.Carriers

@[expose] public section

open MeasureTheory Set
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.FractionalEmbedding

/-- The scalar, unnormalized Euclidean Gagliardo energy on a centered cube. -/
def scalarGagliardoEnergy {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1) (f : SpatialCoordinates d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
    ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((f x - f y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (s : ℝ))

/-- The frozen scalar seminorm is the square root of the normalized raw energy. -/
theorem scalarSeminorm_eq {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (v : DomainL2 (centeredCube z r hr)) :
    cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) =
      (ENNReal.ofReal (s : ℝ) /
        volume (centeredCube z r hr : Set (SpatialCoordinates d)) *
        scalarGagliardoEnergy z r hr s v) ^ (1 / 2 : ℝ) := by
  simp only [cubeFractionalL2Seminorm, Fin.sum_univ_one, scalarGagliardoEnergy]

/-- There is no normalization loss when the scalar seminorm is squared. -/
theorem scalarSeminorm_toReal_sq {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (v : DomainL2 (centeredCube z r hr)) :
    ((cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v)).toReal) ^ 2 =
      (s : ℝ) / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        (scalarGagliardoEnergy z r hr s v).toReal := by
  rw [scalarSeminorm_eq, ← ENNReal.toReal_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num only [one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one]
  rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofReal s.2.1.le]
  rfl

/-- Exact raw-energy formula for the norm in the frozen leaf. -/
theorem cubeFractionalSqNorm_eq_raw {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (v : DomainL2 (centeredCube z r hr)) :
    cubeFractionalSqNorm hd z r hr s v =
      ((s : ℝ) * (scalarGagliardoEnergy z r hr s v).toReal + ‖v‖ ^ 2) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  simp only [cubeFractionalSqNorm, cubeFractionalVecSqNorm,
    cubeFractionalVecSeminormSq, Fin.sum_univ_one, scalarSeminorm_toReal_sq]
  rw [div_mul_eq_mul_div, ← add_div]

/-- The frozen finiteness premise is exactly raw Gagliardo-energy finiteness. -/
theorem scalarSeminorm_lt_top_iff {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (v : DomainL2 (centeredCube z r hr)) :
    cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) < ⊤ ↔
      scalarGagliardoEnergy z r hr s v < ⊤ := by
  have hvolume : volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ ⊤ := by
    rw [centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  have hvolumeZero : volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ 0 := by
    rw [centeredCube_volume]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hr d))
  have hfactor : ENNReal.ofReal (s : ℝ) /
      volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨ne_of_gt (ENNReal.ofReal_pos.mpr s.2.1), hvolume⟩
  have hfactorTop : ENNReal.ofReal (s : ℝ) /
      volume (centeredCube z r hr : Set (SpatialCoordinates d)) < ⊤ :=
    ENNReal.div_lt_top ENNReal.ofReal_ne_top hvolumeZero
  rw [scalarSeminorm_eq, ENNReal.rpow_lt_top_iff_of_pos (by norm_num),
    ENNReal.mul_lt_top_iff]
  constructor
  · rintro (⟨_, h⟩ | h | h)
    · exact h
    · exact (hfactor h).elim
    · rw [h]
      exact ENNReal.zero_lt_top
  · intro h
    exact Or.inl ⟨hfactorTop, h⟩

end SubdiffusiveProcess.FractionalEmbedding
