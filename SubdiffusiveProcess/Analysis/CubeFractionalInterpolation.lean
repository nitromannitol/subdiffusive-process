module

public import SubdiffusiveProcess.Analysis.CubeFractionalSplit
public import SubdiffusiveProcess.Analysis.FractionalScaleOptimization

@[expose] public section

open MeasureTheory Filter Set Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-- Finiteness of the normalized seminorm gives finiteness of the original integral. -/
theorem cubeGagliardoIntegral_ne_top_of_fractional_finite {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (v : DomainL2 (centeredCube z r hr))
    (hv : cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) < ⊤) :
    cubeGagliardoIntegral z r hr s v ≠ ⊤ := by
  have hc0 : ENNReal.ofReal (s : ℝ) /
      volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨ENNReal.ofReal_ne_zero_iff.mpr s.property.1,
      by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top⟩
  intro htop
  have h := ofReal_cubeFractionalSeminormSq hd z r hr s v hv
  rw [htop, ENNReal.mul_top hc0] at h
  exact ENNReal.ofReal_ne_top h

/-- Scalar form of the defining extended-integral normalization. -/
theorem cubeFractionalL2Seminorm_eq_gagliardo {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (v : DomainL2 (centeredCube z r hr)) :
    cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) =
      ((ENNReal.ofReal (s : ℝ) / volume (centeredCube z r hr : Set (SpatialCoordinates d))) *
        cubeGagliardoIntegral z r hr s v) ^ (1 / 2 : ℝ) := by
  simp only [cubeFractionalL2Seminorm, cubeGagliardoIntegral, Fin.sum_univ_one,
    euclideanDist, euclideanNorm, vecNormSq, vecDot, Pi.sub_apply, ← pow_two]

/-- The exact inhomogeneous interpolation estimate on the unit cube. -/
theorem exists_unit_cube_fractional_interpolation (d : ℕ) (hd : 2 ≤ d)
    (s t : Set.Ioo (0 : ℝ) 1) (hts : (t : ℝ) < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos s (fun _ : Fin 1 => v) < ⊤ →
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos t (fun _ : Fin 1 => v) < ⊤ ∧
      Real.sqrt (cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos t v) ≤
        C * (‖v‖ / Real.sqrt (volume.real
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))) ^
            (1 - (t : ℝ) / s) *
          Real.sqrt (cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos s v) ^ ((t : ℝ) / s) := by
  have ht : 0 < (t : ℝ) := t.property.1
  have hs : 0 < (s : ℝ) := s.property.1
  have hq : 0 ≤ 2 * ((s : ℝ) - t) := by linarith
  let M : ℝ := (cubeInterpolationKernelMass d t).toReal
  have hMass : cubeInterpolationKernelMass d t ≠ ⊤ :=
    cubeInterpolationKernelMass_ne_top (by omega) t ht
  let A : ℝ := ((t : ℝ) / s) * (d : ℝ) ^ (2 * ((s : ℝ) - t))
  let F : ℝ := 4 * (t : ℝ) * M
  have hA : 0 ≤ A := mul_nonneg (div_nonneg ht.le hs.le)
    (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hF : 0 ≤ F := by dsimp [F, M]; positivity
  refine ⟨Real.sqrt (1 + A + F), Real.sqrt_pos.mpr (by linarith), ?_⟩
  intro v hv
  have hGs := cubeGagliardoIntegral_ne_top_of_fractional_finite hd 0 1 one_pos s v hv
  have hsplit1 := cubeGagliardoIntegral_le_split (0 : SpatialCoordinates d) 1 one_pos
    s t 1 ht hts one_pos v
  have hGt : cubeGagliardoIntegral (0 : SpatialCoordinates d) 1 one_pos t v ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ hsplit1
    finiteness
  have htfin : cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos t
      (fun _ : Fin 1 => v) < ⊤ := by
    rw [cubeFractionalL2Seminorm_eq_gagliardo, centeredCube_volume, one_pow, ENNReal.ofReal_one, div_one]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGt)
  refine ⟨htfin, ?_⟩
  have hvolume : volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)) = 1 := by rw [centeredCube_volume_real, one_pow]
  have hsemi (sigma : Set.Ioo (0 : ℝ) 1)
      (hfin : cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos sigma
        (fun _ : Fin 1 => v) < ⊤) :
      cubeFractionalVecSeminormSq hd (0 : SpatialCoordinates d) 1 one_pos sigma
        (fun _ : Fin 1 => v) = (sigma : ℝ) *
          (cubeGagliardoIntegral (0 : SpatialCoordinates d) 1 one_pos sigma v).toReal := by
    have he := ofReal_cubeFractionalSeminormSq hd (0 : SpatialCoordinates d) 1 one_pos sigma v hfin
    rw [centeredCube_volume, one_pow, ENNReal.ofReal_one, div_one] at he
    have h := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_ofReal (by unfold cubeFractionalVecSeminormSq; positivity),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal sigma.property.1.le] at h
    exact h
  have hnorm (sigma : Set.Ioo (0 : ℝ) 1)
      (hfin : cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 one_pos sigma
        (fun _ : Fin 1 => v) < ⊤) :
      cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos sigma v =
        (sigma : ℝ) * (cubeGagliardoIntegral (0 : SpatialCoordinates d) 1 one_pos sigma v).toReal +
          ‖v‖ ^ 2 := by
    rw [cubeFractionalSqNorm, cubeFractionalVecSqNorm, hsemi sigma hfin]
    simp only [Fin.sum_univ_one, hvolume, div_one]
  have hnonneg (sigma : Set.Ioo (0 : ℝ) 1) :
      0 ≤ cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos sigma v := by
    unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
    simp only [Fin.sum_univ_one, hvolume, div_one]
    positivity
  let b : ℝ := Real.sqrt (cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos s v)
  have hbsq : b ^ 2 = (s : ℝ) *
      (cubeGagliardoIntegral (0 : SpatialCoordinates d) 1 one_pos s v).toReal + ‖v‖ ^ 2 := by
    rw [Real.sq_sqrt (hnonneg s), hnorm s hv]
  have hab : ‖v‖ ≤ b := Real.le_sqrt_of_sq_le (by
    rw [hnorm s hv]
    exact le_add_of_nonneg_left (mul_nonneg hs.le ENNReal.toReal_nonneg))
  rw [hvolume, Real.sqrt_one, div_one]
  apply interpolation_le_of_scale_bounds s t A F ‖v‖ b
    (Real.sqrt (cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos t v))
    ht hts hA hF (norm_nonneg _) hab (Real.sqrt_nonneg _)
  intro delta hdelt
  have hsplit := cubeGagliardoIntegral_le_split (0 : SpatialCoordinates d) 1 one_pos
    s t delta ht hts hdelt v
  have hNear : ENNReal.ofReal ((d : ℝ) * delta) ^ (2 * ((s : ℝ) - t)) *
      cubeGagliardoIntegral (0 : SpatialCoordinates d) 1 one_pos s v ≠ ⊤ := by finiteness
  have hFar : 4 * (ENNReal.ofReal delta ^ (-(2 * (t : ℝ))) * cubeInterpolationKernelMass d t) *
      ENNReal.ofReal (‖v‖ ^ 2) ≠ ⊤ := by
    have hd0 : ENNReal.ofReal delta ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hdelt
    finiteness
  have hi := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hNear, hFar⟩) hsplit
  rw [ENNReal.toReal_add hNear hFar] at hi
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg d) hdelt.le),
    ENNReal.toReal_ofReal hdelt.le, ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofNat] at hi
  have htGs : (t : ℝ) * (cubeGagliardoIntegral (0 : SpatialCoordinates d) 1 one_pos s v).toReal ≤
      ((t : ℝ) / s) * b ^ 2 := by
    calc
      _ = ((t : ℝ) / s) * ((s : ℝ) *
          (cubeGagliardoIntegral (0 : SpatialCoordinates d) 1 one_pos s v).toReal) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by rw [hbsq]; exact le_add_of_nonneg_right (sq_nonneg _))
        (div_nonneg ht.le hs.le)
  rw [Real.sq_sqrt (hnonneg t), hnorm t htfin]
  calc
    (t : ℝ) * (cubeGagliardoIntegral (0 : SpatialCoordinates d) 1 one_pos t v).toReal + ‖v‖ ^ 2 ≤
        (t : ℝ) * (((d : ℝ) * delta) ^ (2 * ((s : ℝ) - t)) *
          (cubeGagliardoIntegral (0 : SpatialCoordinates d) 1 one_pos s v).toReal +
            4 * (delta ^ (-(2 * (t : ℝ))) * M) * ‖v‖ ^ 2) + ‖v‖ ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hi ht.le) le_rfl
    _ = ‖v‖ ^ 2 + ((d : ℝ) ^ (2 * ((s : ℝ) - t)) * delta ^ (2 * ((s : ℝ) - t))) *
        ((t : ℝ) * (cubeGagliardoIntegral (0 : SpatialCoordinates d) 1 one_pos s v).toReal) +
          F * delta ^ (-(2 * (t : ℝ))) * ‖v‖ ^ 2 := by
      rw [Real.mul_rpow (Nat.cast_nonneg d) hdelt.le]
      dsimp [F]
      ring
    _ ≤ ‖v‖ ^ 2 + ((d : ℝ) ^ (2 * ((s : ℝ) - t)) * delta ^ (2 * ((s : ℝ) - t))) *
        (((t : ℝ) / s) * b ^ 2) + F * delta ^ (-(2 * (t : ℝ))) * ‖v‖ ^ 2 := by
      exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left htGs
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (Real.rpow_nonneg hdelt.le _)))) le_rfl
    _ = _ := by dsimp [A]; ring

end SubdiffusiveProcess
