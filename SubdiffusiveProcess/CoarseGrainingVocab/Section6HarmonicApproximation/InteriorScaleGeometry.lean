import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCellPrice

/-!
# Scale arithmetic for the interior-cell price

The projected parent has scale `n-2`, while the manuscript window has scale
`n`.  Their normalized-volume loss is therefore at most `9^d`.

PROVENANCE: the same fixed-gap volume calculation as
`Algsuperdiff/Section4/Provider/ExcessDecay/CaccioppoliInteriorDatum.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A scale-`n` truncated window costs at most `9^d` relative to any translated
full cube of scale `n-2`. -/
theorem volume_ratio_truncatedCube_translated_predTwo_le
    {m n : ℤ} {x c : Vec d} (hx : x ∈ cube d m) (hnm : n - 1 ≤ m) :
    (volume (truncatedCube d m n x)).toReal /
        (volume (translatedCube d (n - 2) c)).toReal ≤ (9 : ℝ) ^ d := by
  have hU := (Section6ExcessDecay.volume_toReal_truncatedCube_bounds x hx hnm).2
  have hP : (volume (translatedCube d (n - 2) c)).toReal =
      ((3 : ℝ) ^ (n - 2)) ^ d := by
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet,
      volume_translateSet_eq, volume_openCubeSet_toReal, cubeVolume_eq_pow_scale]
    simp only [originCube]
  have hPpos : 0 < ((3 : ℝ) ^ (n - 2)) ^ d := by positivity
  have hratio : ((3 : ℝ) ^ n) ^ d / ((3 : ℝ) ^ (n - 2)) ^ d =
      (9 : ℝ) ^ d := by
    rw [← div_pow, ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  rw [hP, ← hratio]
  exact div_le_div_of_nonneg_right hU hPpos.le

/-- The Caccioppoli scale factor at the projected scale is the ambient
`3^{-2n}` factor times the fixed gap `81`. -/
theorem rpow_projected_predTwo_scale (n : ℕ) :
    Real.rpow (3 : ℝ)
        (-2 * ((((originCube d ((n : ℤ) - 2)).scale : ℤ) : ℝ))) =
      81 * (3 : ℝ) ^ (-(2 * (n : ℤ))) := by
  rw [show (originCube d ((n : ℤ) - 2)).scale = (n : ℤ) - 2 by rfl]
  have hcast : (-2 : ℝ) * ((((n : ℤ) - 2 : ℤ) : ℝ)) =
      (((-(2 * (n : ℤ)) + 4 : ℤ) : ℝ)) := by push_cast; ring
  rw [hcast]
  calc
    Real.rpow (3 : ℝ) (((-(2 * (n : ℤ)) + 4 : ℤ) : ℝ)) =
        (3 : ℝ) ^ (-(2 * (n : ℤ)) + 4 : ℤ) := Real.rpow_intCast 3 _
    _ = (3 : ℝ) ^ (-(2 * (n : ℤ))) * (3 : ℝ) ^ (4 : ℤ) := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    _ = 81 * (3 : ℝ) ^ (-(2 * (n : ℤ))) := by norm_num; ring

/-- The negative Besov weight on the projected cube is the manuscript's
`3^{s(n-2)}` factor. -/
theorem cubeBesovScaleWeight_neg_origin_predTwo (s : ℝ) (n : ℕ) :
    cubeBesovScaleWeight (-s) (originCube d ((n : ℤ) - 2)) =
      Real.rpow (3 : ℝ) (s * (((n : ℤ) - 2 : ℤ) : ℝ)) := by
  rw [cubeBesovScaleWeight, cubeScaleFactor_originCube]
  simp only [neg_neg]
  have hbase : (3 : ℝ) ^ ((n : ℤ) - 2) =
      Real.rpow (3 : ℝ) ((((n : ℤ) - 2 : ℤ) : ℝ)) := by
    exact (Real.rpow_intCast 3 ((n : ℤ) - 2)).symm
  rw [hbase]
  calc
    Real.rpow (3 : ℝ) ((((n : ℤ) - 2 : ℤ) : ℝ)) ^ s =
        Real.rpow (3 : ℝ) (((((n : ℤ) - 2 : ℤ) : ℝ)) * s) :=
      (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
    _ = Real.rpow (3 : ℝ) (s * (((n : ℤ) - 2 : ℤ) : ℝ)) := by
      congr 1
      ring

/-- The fixed factor incurred by replacing `s / 2` with `s` in the interior
Caccioppoli prefactor. -/
theorem rpow_half_neg_eleven {s : ℝ} (hs : 0 < s) :
    Real.rpow (s / 2) (-11 : ℝ) =
      (2 : ℝ) ^ (11 : ℕ) * Real.rpow s (-11 : ℝ) := by
  calc
    Real.rpow (s / 2) (-11 : ℝ) =
        Real.rpow s (-11 : ℝ) / Real.rpow 2 (-11 : ℝ) :=
      Real.div_rpow hs.le (by norm_num : (0 : ℝ) ≤ 2) _
    _ = (2 : ℝ) ^ (11 : ℕ) * Real.rpow s (-11 : ℝ) := by
      have htwo : Real.rpow (2 : ℝ) (-11 : ℝ) =
          ((2 : ℝ) ^ (11 : ℕ))⁻¹ := by
        calc
          Real.rpow (2 : ℝ) (-11 : ℝ) = Real.rpow 2 (-(11 : ℝ)) := by norm_num
          _ = (Real.rpow 2 (11 : ℝ))⁻¹ := Real.rpow_neg (by norm_num) _
          _ = ((2 : ℝ) ^ (11 : ℕ))⁻¹ := by
            congr 1
            exact Real.rpow_natCast 2 11
      rw [htwo]
      norm_num
      ring

/-- Squaring the fractional Poincare loss contributes exactly `s⁻¹`. -/
theorem sq_rpow_neg_half {s : ℝ} (hs : 0 < s) :
    Real.rpow s (-(1 / 2 : ℝ)) ^ 2 = s⁻¹ := by
  calc
    Real.rpow s (-(1 / 2 : ℝ)) ^ 2 =
        Real.rpow s (-(1 / 2 : ℝ)) * Real.rpow s (-(1 / 2 : ℝ)) := pow_two _
    _ = Real.rpow s (-(1 / 2 : ℝ) + -(1 / 2 : ℝ)) :=
      (Real.rpow_add hs _ _).symm
    _ = Real.rpow s (-1 : ℝ) := by norm_num
    _ = s⁻¹ := Real.rpow_neg_one _

/-- Moving the projected scale `n-2` back to the manuscript scale `n` only
increases the positive fractional weight. -/
theorem rpow_projected_fractional_le {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Real.rpow (3 : ℝ) (s * (((n : ℤ) - 2 : ℤ) : ℝ)) ≤
      Real.rpow (3 : ℝ) (s * (n : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hcast : ((((n : ℤ) - 2 : ℤ) : ℝ)) ≤ (n : ℝ) := by
    push_cast
    norm_num
  exact mul_le_mul_of_nonneg_left hcast hs.le

/-- The entire projected negative-Besov source factor collapses to the
manuscript's `s⁻¹² 3^(2sn)` square budget, with only a dimension-dependent
fixed-gap loss. -/
theorem projected_source_factor_le {n : ℕ} {s K ratio G : ℝ}
    (hs : 0 < s) (hK : 0 ≤ K) (hratio : 0 ≤ ratio)
    (hratio_le : ratio ≤ (9 : ℝ) ^ d) (hG : 0 ≤ G) :
    Real.rpow (s / 2) (-11 : ℝ) *
        (K * Real.rpow (3 : ℝ) (s * (((n : ℤ) - 2 : ℤ) : ℝ)) *
          (Real.rpow s (-(1 / 2 : ℝ)) * (Real.sqrt ratio * G))) ^ 2 ≤
      ((2 : ℝ) ^ (11 : ℕ) * K ^ 2 * (9 : ℝ) ^ d) *
        Real.rpow s (-12 : ℝ) *
        Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * G ^ 2 := by
  have hw := rpow_projected_fractional_le hs n
  have hweight0 : 0 ≤ Real.rpow (3 : ℝ)
      (s * (((n : ℤ) - 2 : ℤ) : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hW0 : 0 ≤ Real.rpow (3 : ℝ) (s * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hrs0 : 0 ≤ Real.rpow s (-(1 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have hsqrt0 : 0 ≤ Real.sqrt ratio := Real.sqrt_nonneg _
  have hinside :
      K * Real.rpow (3 : ℝ) (s * (((n : ℤ) - 2 : ℤ) : ℝ)) *
          (Real.rpow s (-(1 / 2 : ℝ)) * (Real.sqrt ratio * G)) ≤
        K * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
          (Real.rpow s (-(1 / 2 : ℝ)) * (Real.sqrt ratio * G)) := by
    gcongr
  have hins0 : 0 ≤ K * Real.rpow (3 : ℝ)
      (s * (((n : ℤ) - 2 : ℤ) : ℝ)) *
        (Real.rpow s (-(1 / 2 : ℝ)) * (Real.sqrt ratio * G)) := by positivity
  have hinBig0 : 0 ≤ K * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
      (Real.rpow s (-(1 / 2 : ℝ)) * (Real.sqrt ratio * G)) := by positivity
  have hsq := pow_le_pow_left₀ hins0 hinside 2
  have hfac0 : 0 ≤ Real.rpow (s / 2) (-11 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hstep := mul_le_mul_of_nonneg_left hsq hfac0
  have hWsq : Real.rpow (3 : ℝ) (s * (n : ℝ)) ^ 2 =
      Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) := by
    calc
      Real.rpow (3 : ℝ) (s * (n : ℝ)) ^ 2 =
          Real.rpow (3 : ℝ) (s * (n : ℝ)) *
            Real.rpow (3 : ℝ) (s * (n : ℝ)) := pow_two _
      _ = Real.rpow (3 : ℝ) (s * (n : ℝ) + s * (n : ℝ)) :=
        (Real.rpow_add (by norm_num) _ _).symm
      _ = Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) := by
        congr 1
        ring
  have hsprod : Real.rpow s (-11 : ℝ) * s⁻¹ = Real.rpow s (-12 : ℝ) := by
    calc
      Real.rpow s (-11 : ℝ) * s⁻¹ =
          Real.rpow s (-11 : ℝ) * Real.rpow s (-1 : ℝ) := by
        congr 1
        exact (Real.rpow_neg_one s).symm
      _ = Real.rpow s ((-11 : ℝ) + (-1 : ℝ)) :=
        (Real.rpow_add hs _ _).symm
      _ = Real.rpow s (-12 : ℝ) := by norm_num
  have hrawEq :
      Real.rpow (s / 2) (-11 : ℝ) *
          (K * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
            (Real.rpow s (-(1 / 2 : ℝ)) * (Real.sqrt ratio * G))) ^ 2 =
        (2 : ℝ) ^ (11 : ℕ) * K ^ 2 * Real.rpow s (-12 : ℝ) *
          Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * ratio * G ^ 2 := by
    rw [rpow_half_neg_eleven hs]
    calc
      (2 : ℝ) ^ (11 : ℕ) * Real.rpow s (-11 : ℝ) *
          (K * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
            (Real.rpow s (-(1 / 2 : ℝ)) * (Real.sqrt ratio * G))) ^ 2 =
          (2 : ℝ) ^ (11 : ℕ) * K ^ 2 *
            (Real.rpow s (-11 : ℝ) *
              Real.rpow s (-(1 / 2 : ℝ)) ^ 2) *
            Real.rpow (3 : ℝ) (s * (n : ℝ)) ^ 2 *
            Real.sqrt ratio ^ 2 * G ^ 2 := by ring
      _ = (2 : ℝ) ^ (11 : ℕ) * K ^ 2 * Real.rpow s (-12 : ℝ) *
            Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * ratio * G ^ 2 := by
        rw [sq_rpow_neg_half hs, hWsq, Real.sq_sqrt hratio, hsprod]
  have hcoef :
      (2 : ℝ) ^ (11 : ℕ) * K ^ 2 * Real.rpow s (-12 : ℝ) *
          Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * ratio * G ^ 2 ≤
        (2 : ℝ) ^ (11 : ℕ) * K ^ 2 * Real.rpow s (-12 : ℝ) *
          Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * (9 : ℝ) ^ d * G ^ 2 := by
    let P : ℝ := (2 : ℝ) ^ (11 : ℕ) * K ^ 2 * Real.rpow s (-12 : ℝ) *
      Real.rpow (3 : ℝ) (2 * s * (n : ℝ))
    have hP0 : 0 ≤ P := by
      dsimp [P]
      positivity
    have hmono : P * ratio * G ^ 2 ≤ P * (9 : ℝ) ^ d * G ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio_le hP0) (sq_nonneg G)
    simpa only [P] using hmono
  calc
    Real.rpow (s / 2) (-11 : ℝ) *
        (K * Real.rpow (3 : ℝ) (s * (((n : ℤ) - 2 : ℤ) : ℝ)) *
          (Real.rpow s (-(1 / 2 : ℝ)) * (Real.sqrt ratio * G))) ^ 2 ≤
        Real.rpow (s / 2) (-11 : ℝ) *
          (K * Real.rpow (3 : ℝ) (s * (n : ℝ)) *
            (Real.rpow s (-(1 / 2 : ℝ)) * (Real.sqrt ratio * G))) ^ 2 := hstep
    _ = (2 : ℝ) ^ (11 : ℕ) * K ^ 2 * Real.rpow s (-12 : ℝ) *
          Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * ratio * G ^ 2 := hrawEq
    _ ≤ (2 : ℝ) ^ (11 : ℕ) * K ^ 2 * Real.rpow s (-12 : ℝ) *
          Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * (9 : ℝ) ^ d * G ^ 2 := hcoef
    _ = ((2 : ℝ) ^ (11 : ℕ) * K ^ 2 * (9 : ℝ) ^ d) *
          Real.rpow s (-12 : ℝ) *
          Real.rpow (3 : ℝ) (2 * s * (n : ℝ)) * G ^ 2 := by ring

/-- The projected parent-oscillation factor has only the fixed depth-two
volume loss and the fixed `81` scale loss. -/
theorem projected_parent_factor_le {n : ℕ} {B sigma ratio X : ℝ}
    (hB : 0 ≤ B) (hsigma : 0 ≤ sigma)
    (hratio_le : ratio ≤ (9 : ℝ) ^ d) :
    B * sigma *
        Real.rpow (3 : ℝ)
          (-2 * ((((originCube d ((n : ℤ) - 2)).scale : ℤ) : ℝ))) *
        ratio * X ^ 2 ≤
      (81 * B * (9 : ℝ) ^ d) * sigma *
        (3 : ℝ) ^ (-(2 * (n : ℤ))) * X ^ 2 := by
  rw [rpow_projected_predTwo_scale]
  let P : ℝ := 81 * B * sigma * (3 : ℝ) ^ (-(2 * (n : ℤ)))
  have hP0 : 0 ≤ P := by
    dsimp [P]
    positivity
  have hmono : P * ratio * X ^ 2 ≤ P * (9 : ℝ) ^ d * X ^ 2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio_le hP0) (sq_nonneg X)
  dsimp [P] at hmono
  convert hmono using 1 <;> ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
