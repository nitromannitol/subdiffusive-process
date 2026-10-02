import SubdiffusiveProcess.Analysis.CubeFractionalCellError
import SubdiffusiveProcess.Lane4.Carriers
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Filter Set TopologicalSpace Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-- Finiteness identifies the real seminorm square with its defining extended integral. -/
theorem ofReal_cubeFractionalSeminormSq {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : DomainL2 (centeredCube z r hr))
    (hfinite : cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => f) < ⊤) :
    ENNReal.ofReal (cubeFractionalVecSeminormSq hd z r hr s (fun _ : Fin 1 => f)) =
      (ENNReal.ofReal (s : ℝ) / volume (centeredCube z r hr : Set (SpatialCoordinates d))) *
        cubeGagliardoIntegral z r hr s f := by
  rw [cubeFractionalVecSeminormSq,
    ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfinite.ne,
    cubeFractionalL2Seminorm, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num only [one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), ENNReal.rpow_one]
  simp only [cubeGagliardoIntegral, Fin.sum_univ_one,
    euclideanDist, euclideanNorm, vecNormSq, vecDot, Pi.sub_apply, ← pow_two]

/-- A bounded normalized fractional norm bounds the unnormalized Gagliardo integral. -/
theorem cubeGagliardoIntegral_le_of_cubeFractionalSqNorm_le {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : DomainL2 (centeredCube z r hr)) (B : ℝ)
    (hfinite : cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => f) < ⊤)
    (hbound : cubeFractionalSqNorm hd z r hr s f ≤ B) :
    cubeGagliardoIntegral z r hr s f ≤
      ENNReal.ofReal B /
        (ENNReal.ofReal (s : ℝ) / volume (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  let c : ℝ≥0∞ := ENNReal.ofReal (s : ℝ) /
    volume (centeredCube z r hr : Set (SpatialCoordinates d))
  have hc0 : c ≠ 0 := by
    exact ENNReal.div_ne_zero.mpr ⟨ENNReal.ofReal_ne_zero_iff.mpr s.property.1,
      by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top⟩
  have hct : c ≠ ⊤ := by
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top
      (by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hr d))
  have hl2 : 0 ≤ ‖f‖ ^ 2 /
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    div_nonneg (sq_nonneg _) (centeredCube_volume_pos z hr).le
  have hsemi : cubeFractionalVecSeminormSq hd z r hr s (fun _ : Fin 1 => f) ≤ B := by
    have hb := hbound
    simp only [cubeFractionalSqNorm, cubeFractionalVecSqNorm, Fin.sum_univ_one] at hb
    linarith
  apply (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)).mpr
  rw [mul_comm, ← ofReal_cubeFractionalSeminormSq hd z r hr s f hfinite]
  exact ENNReal.ofReal_le_ofReal hsemi

/-- The normalized fractional norm also controls the ordinary `L²` norm. -/
theorem norm_le_of_cubeFractionalSqNorm_le {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : DomainL2 (centeredCube z r hr)) (B : ℝ)
    (hbound : cubeFractionalSqNorm hd z r hr s f ≤ B) :
    ‖f‖ ≤ Real.sqrt (B * volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hv := centeredCube_volume_pos z hr
  apply Real.le_sqrt_of_sq_le
  apply (div_le_iff₀ hv).mp
  have hb := hbound
  simp only [cubeFractionalSqNorm, cubeFractionalVecSqNorm,
    cubeFractionalVecSeminormSq, Fin.sum_univ_one] at hb
  have hnonneg := sq_nonneg ((cubeFractionalL2Seminorm hd z r hr s
    (fun _ : Fin 1 => f)).toReal)
  linarith

/-- The explicit averaging-error coefficient tends to zero as the grid is refined. -/
theorem tendsto_cubeCellErrorCoefficient_zero {d : ℕ} (r : ℝ) (hr : 0 < r)
    (s : ℝ) (hs : 0 < s) (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    Tendsto (fun m : ℕ =>
      (ENNReal.ofReal ((r / (2 * (m : ℝ) + 1)) ^ d))⁻¹ *
        (ENNReal.ofReal (Real.sqrt d * (r / (2 * (m : ℝ) + 1)))) ^ ((d : ℝ) + 2 * s) * K)
      atTop (𝓝 0) := by
  let delta : ℕ → ℝ := fun m => r / (2 * (m : ℝ) + 1)
  have hdelta (m : ℕ) : 0 < delta m := div_pos hr (by positivity)
  have hlim : Tendsto delta atTop (𝓝 0) := by
    apply squeeze_zero (fun m : ℕ => (hdelta m).le)
      (g := fun m : ℕ => r * (1 / ((m : ℝ) + 1)))
    · intro m
      dsimp [delta]
      rw [mul_one_div]
      apply div_le_div_of_nonneg_left hr.le (by positivity)
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    · simpa only [mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul r
  let c : ℝ≥0∞ := (ENNReal.ofReal (Real.sqrt d)) ^ ((d : ℝ) + 2 * s) * K
  have hc : c ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top) hK
  have heq (m : ℕ) :
      (ENNReal.ofReal ((delta m) ^ d))⁻¹ *
        (ENNReal.ofReal (Real.sqrt d * delta m)) ^ ((d : ℝ) + 2 * s) * K =
      c * (ENNReal.ofReal (delta m)) ^ (2 * s) := by
    have ha0 : ENNReal.ofReal (delta m) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (hdelta m)
    have hap0 : ENNReal.ofReal (delta m) ^ d ≠ 0 := pow_ne_zero d ha0
    have hapt : ENNReal.ofReal (delta m) ^ d ≠ ⊤ := by
      rw [← ENNReal.ofReal_pow (hdelta m).le]
      exact ENNReal.ofReal_ne_top
    rw [ENNReal.ofReal_pow (hdelta m).le,
      ENNReal.ofReal_mul (Real.sqrt_nonneg d),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (d : ℝ) + 2 * s),
      ENNReal.rpow_add (d : ℝ) (2 * s) ha0 ENNReal.ofReal_ne_top,
      ENNReal.rpow_natCast]
    calc
      _ = (ENNReal.ofReal (Real.sqrt d)) ^ ((d : ℝ) + 2 * s) * K *
          ((ENNReal.ofReal (delta m) ^ d)⁻¹ * ENNReal.ofReal (delta m) ^ d) *
          (ENNReal.ofReal (delta m)) ^ (2 * s) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel hap0 hapt, mul_one]
  simp_rw [show (fun m : ℕ =>
    (ENNReal.ofReal ((r / (2 * (m : ℝ) + 1)) ^ d))⁻¹ *
      (ENNReal.ofReal (Real.sqrt d * (r / (2 * (m : ℝ) + 1)))) ^ ((d : ℝ) + 2 * s) * K) =
      (fun m => c * ENNReal.ofReal (delta m) ^ (2 * s)) from funext heq]
  apply (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hc (by positivity)).comp
  simpa only [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto 0 |>.comp hlim

end SubdiffusiveProcess
