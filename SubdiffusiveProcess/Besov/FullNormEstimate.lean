module

public import SubdiffusiveProcess.Besov.HattedNorm
public import SubdiffusiveProcess.Besov.MultiscaleSum
public import SubdiffusiveProcess.Besov.SymmetricCoefficients

@[expose] public section

namespace SubdiffusiveProcess.Besov
open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch05.Section53
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped BigOperators ENNReal
noncomputable section
variable {d : ℕ} [NeZero d]

/-- The literal weak norm is bounded by the existing multiscale sum. -/
theorem scaled_hHatNorm_maximizerGradientDefect_le (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (m : ℤ) (p q : Vec d) :
    (3 : ℝ) ^ (-m) * (hHatNorm (originCube d m)
      (maximizerGradientDefect a ha (originCube d m) p q)).toReal ≤
      (hHatBesovConstant d * (d : ℝ)) * centredMultiscaleAverageSum a ha m p q := by
  have hnorm := hHatNorm_toReal_le_sum_circ (originCube d m)
    (maximizerGradientDefect a ha (originCube d m) p q)
    (maximizerGradientDefect_component_memLp a ha (originCube d m) p q)
  have hmult := sum_cubeBesovCircNorm_maximizerGradientDefect_le a ha m p q
  calc
    _ ≤ (3 : ℝ) ^ (-m) *
        (hHatBesovConstant d * ∑ i : Fin d, cubeBesovCircNorm (originCube d m) 1 2 1
          (fun x => maximizerGradientDefect a ha (originCube d m) p q x i)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = hHatBesovConstant d *
        ((3 : ℝ) ^ (-m) * ∑ i : Fin d, cubeBesovCircNorm (originCube d m) 1 2 1
          (fun x => maximizerGradientDefect a ha (originCube d m) p q x i)) := by ring
    _ ≤ hHatBesovConstant d * ((d : ℝ) * centredMultiscaleAverageSum a ha m p q) :=
      mul_le_mul_of_nonneg_left hmult (hHatBesovConstant_pos d).le
    _ = _ := by ring

/-- One dimensional constant can serve in all four nonnegative terms. -/
theorem unify_four_terms {b x₁ x₂ x₃ x₄ : ℝ} (hb : 0 ≤ b)
    (h₁ : 0 ≤ x₁) (h₂ : 0 ≤ x₂) (h₃ : 0 ≤ x₃) (h₄ : 0 ≤ x₄) :
    b * (2 * x₁ + Real.sqrt 2 * x₂ + 2 * Real.sqrt 2 * x₃ + 2 * Real.sqrt 2 * x₄) ≤
      (4 * b + 1) * x₁ + (4 * b + 1) * x₂ + (4 * b + 1) * x₃ + (4 * b + 1) * x₄ := by
  have hsqrt : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have hcoeff : b * Real.sqrt 2 ≤ 2 * b := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsqrt hb
  have hcoeff₁ : b * 2 ≤ 4 * b + 1 := by linarith
  have hcoeff₂ : b * Real.sqrt 2 ≤ 4 * b + 1 := by linarith
  have hcoeff₃ : b * (2 * Real.sqrt 2) ≤ 4 * b + 1 := by linarith
  have hterm₁ := mul_le_mul_of_nonneg_right hcoeff₁ h₁
  have hterm₂ := mul_le_mul_of_nonneg_right hcoeff₂ h₂
  have hterm₃ := mul_le_mul_of_nonneg_right hcoeff₃ h₃
  have hterm₄ := mul_le_mul_of_nonneg_right hcoeff₃ h₄
  nlinarith only [hterm₁, hterm₂, hterm₃, hterm₄]

/-- Full paper range, with the literal weak norm and one dimensional constant. -/
theorem scaled_hHatNorm_maximizerGradientDefect_le_fourTerm_full
    (a : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField a)
    {m L₀ : ℤ} (hLm : L₀ ≤ m) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {r : Ch02.MultiscaleExponent} (hr : r.IsAdmissible) (p q : Vec d) :
    (3 : ℝ) ^ (-m) * (hHatNorm (originCube d m)
      (maximizerGradientDefect a ha (originCube d m) p q)).toReal ≤
      (4 * (hHatBesovConstant d * (d : ℝ)) + 1) *
          Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
          (∑ n ∈ Finset.Icc L₀ m,
            (3 : ℝ) ^ (-(1 - s) * ((m - n : ℤ) : ℝ)) *
              Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) +
        (4 * (hHatBesovConstant d * (d : ℝ)) + 1) *
          (∑ n ∈ Finset.Icc L₀ m,
            (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
              Real.sqrt (descendantsAverage (originCube d m) (m - n).toNat
                (coarseMatrixVariationSq a ha (originCube d m) p q))) +
        (4 * (hHatBesovConstant d * (d : ℝ)) + 1) *
          Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) / (1 - s) *
          (3 : ℝ) ^ (-(1 - s) * ((m - L₀ : ℤ) : ℝ)) *
            maximizerEnergyL2Norm a ha (originCube d m) p q +
        (4 * (hHatBesovConstant d * (d : ℝ)) + 1) *
          (3 : ℝ) ^ (-((m - L₀ : ℤ) : ℝ)) *
            Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q)) := by
  let b : ℝ := hHatBesovConstant d * (d : ℝ)
  have hb : 0 ≤ b := mul_nonneg (hHatBesovConstant_pos d).le (Nat.cast_nonneg d)
  have hnorm := scaled_hHatNorm_maximizerGradientDefect_le a ha m p q
  have hfour := centredMultiscaleAverageSum_le_fourTerm_full a ha hLm hs hs1 hr p q
  have hbound := hnorm.trans (mul_le_mul_of_nonneg_left hfour hb)
  set x₁ : ℝ := Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
    (∑ n ∈ Finset.Icc L₀ m, (3 : ℝ) ^ (-(1 - s) * ((m - n : ℤ) : ℝ)) *
      Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a))
  set x₂ : ℝ := ∑ n ∈ Finset.Icc L₀ m, (3 : ℝ) ^ (-((m - n : ℤ) : ℝ)) *
    Real.sqrt (descendantsAverage (originCube d m) (m - n).toNat
      (coarseMatrixVariationSq a ha (originCube d m) p q))
  set x₃ : ℝ := (Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) / (1 - s)) *
    (3 : ℝ) ^ (-(1 - s) * ((m - L₀ : ℤ) : ℝ)) *
      maximizerEnergyL2Norm a ha (originCube d m) p q
  set x₄ : ℝ := (3 : ℝ) ^ (-((m - L₀ : ℤ) : ℝ)) *
    Real.sqrt (vecNormSq (coarseScaleSeparation a ha (originCube d m) p q))
  have hx₁ : 0 ≤ x₁ := by dsimp [x₁]; positivity
  have hx₂ : 0 ≤ x₂ := by dsimp [x₂]; positivity
  have hx₃ : 0 ≤ x₃ := mul_nonneg
    (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by linarith)) (by positivity))
    (maximizerEnergyL2Norm_nonneg a ha _ _ _)
  have hx₄ : 0 ≤ x₄ := by dsimp [x₄]; positivity
  have heq :
      b * (2 * Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
        (∑ n ∈ Finset.Icc L₀ m, (3 : ℝ) ^ (-(1 - s) * ((m - n : ℤ) : ℝ)) *
          Real.sqrt (WeakNormsMaximizer.responseDefectAverageAtScale m n p q a)) +
        Real.sqrt 2 * x₂ + (2 * Real.sqrt 2 / (1 - s)) *
          ((3 : ℝ) ^ (-(1 - s) * ((m - L₀ : ℤ) : ℝ)) *
            Real.sqrt ((Ch04.lambdaSqCoeffField (originCube d m) s r a)⁻¹) *
              maximizerEnergyL2Norm a ha (originCube d m) p q) + 2 * Real.sqrt 2 * x₄) =
        b * (2 * x₁ + Real.sqrt 2 * x₂ + 2 * Real.sqrt 2 * x₃ + 2 * Real.sqrt 2 * x₄) := by
    dsimp [x₁, x₃]
    ring
  change _ ≤ b * _ at hbound
  rw [heq] at hbound
  refine (hbound.trans (unify_four_terms hb hx₁ hx₂ hx₃ hx₄)).trans_eq ?_
  dsimp [b, x₁, x₂, x₃, x₄]
  ring

end
end SubdiffusiveProcess.Besov
