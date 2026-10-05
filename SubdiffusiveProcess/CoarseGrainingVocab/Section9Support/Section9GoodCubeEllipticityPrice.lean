module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHighCutoffEllipticity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.EllipticityErrorAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.EllipticitySpecialization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSobolevCoefficient
@[expose] public section

/-!
# High-cutoff ellipticity on a good-cube descendant

The response test at scale `m` controls the coefficient cut off at the outer
scale `n`. The price retains `ahom M n`, as required before the clock comparison.
-/

set_option autoImplicit false
open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison
open _root_.SubdiffusiveProcess.Model
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A descendant response test bounds the inverse ellipticity at the outer cutoff. -/
theorem goodCube_cutoff_lambda_price_le_of_ellipticity_test
    {d : ℕ} [NeZero d] (M : GMCModel d) (n m : ℕ) (hmn : m ≤ n)
    (z : Vec d) (omega : PotentialSample d) {e : ℝ} (he : 0 ≤ e)
    (hE : ellipticityMomentObservable M n (m : ℤ) (1 / 8)
      (translatePotentialSample z omega) ≤ ENNReal.ofReal e) :
    ahom M n * (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
      (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ ≤
        (1 + Real.sqrt 2 * e) ^ 2 := by
  have hσ : 0 < ahom M n := ahom_pos M n
  have hs : (0 : ℝ) < 1 / 8 := by norm_num
  have hroot := sqrt_mul_lambdaSq_inv_le_one_add_sqrt_two_mul_error
    (originCube d (m : ℤ))
    (aCutoffFamily M n (translatePotentialSample z omega)) hs hσ
  have hcompare := ofReal_homogenizationErrorOnCube_le_paperHomogenizationError
    (originCube d (m : ℤ))
    (aCutoffFamily M n (translatePotentialSample z omega))
    (fun R => (aCutoffTriadicData M n (translatePotentialSample z omega)).onCube R |>.isSymmetric)
    hs hσ
  have hscale : (originCube d (m : ℤ)).scale = (m : ℤ) := by simp [originCube]
  have hsrc := sourceCell_paperError_le_ellipticityMomentObservable M n 0 m hmn
    (1 / 8) (translatePotentialSample z omega)
  rw [Nat.add_zero] at hsrc
  rw [tailCoefficientCubeAverage_self] at hsrc
  have hErrLe : Ch02.HomogenizationErrorOnCube (originCube d (m : ℤ)) (1 / 8)
      .infinity (.finite 1)
      (aCutoffFamily M n (translatePotentialSample z omega))
      (scalarMatrix (d := d) (ahom M n)) ≤ e := by
    refine (ENNReal.ofReal_le_ofReal_iff he).mp ?_
    calc ENNReal.ofReal (Ch02.HomogenizationErrorOnCube (originCube d (m : ℤ)) (1 / 8)
        .infinity (.finite 1)
        (aCutoffFamily M n (translatePotentialSample z omega))
        (scalarMatrix (d := d) (ahom M n))) ≤
        paperHomogenizationError (originCube d (m : ℤ)) (originCube d (m : ℤ)).scale
          (1 / 8) .infinity (.finite 1)
          (aCutoffFamily M n (translatePotentialSample z omega)) (ahom M n) := hcompare
      _ ≤ paperHomogenizationErrorDefault (originCube d (m : ℤ)) ((m : ℤ)) (1 / 8)
          .infinity
          (aCutoffFamily M n (translatePotentialSample z omega)) (ahom M n) := by
          rw [hscale]
      _ ≤ ellipticityMomentObservable M n ((m : ℤ)) (1 / 8)
          (translatePotentialSample z omega) := hsrc
      _ ≤ ENNReal.ofReal e := hE
  have hbound : Real.sqrt (ahom M n * (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 8)
      (.finite 1) (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹) ≤
      1 + Real.sqrt 2 * e := by
    have hmul := mul_le_mul_of_nonneg_left hErrLe (Real.sqrt_nonneg 2)
    linarith [hroot, hmul]
  have hx0 : 0 ≤ ahom M n * (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 8) (.finite 1)
      (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ :=
    mul_nonneg hσ.le (inv_nonneg.2 (Ch02.lambdaSq_nonneg (originCube d (m : ℤ))
      (aCutoffFamily M n (translatePotentialSample z omega)) hs (by norm_num)))
  have hy0 : 0 ≤ 1 + Real.sqrt 2 * e :=
    add_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg 2) he)
  have hfinal : ahom M n * (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 8) (.finite 1)
      (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ ≤
      (1 + Real.sqrt 2 * e) ^ 2 := by
    rw [← Real.sq_sqrt hx0]
    have hd1 : 0 ≤ (1 + Real.sqrt 2 * e) - Real.sqrt (ahom M n *
        (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 8) (.finite 1)
          (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹) := by
      linarith [hbound]
    have hd2 : 0 ≤ (1 + Real.sqrt 2 * e) + Real.sqrt (ahom M n *
        (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 8) (.finite 1)
          (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹) := by
      linarith [hy0, Real.sqrt_nonneg (ahom M n * (Ch02.lambdaSq (originCube d (m : ℤ))
        (1 / 8) (.finite 1)
        (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹)]
    have hprod := mul_nonneg hd1 hd2
    nlinarith
  have hmono := Ch02.lambdaSq_finite_mono (originCube d (m : ℤ))
    (aCutoffFamily M n (translatePotentialSample z omega))
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1 / 2)
    (by norm_num : (1 : ℝ) ≤ 1)
  have hpos8 := Ch02.lambdaSq_finite_pos (originCube d (m : ℤ))
    (aCutoffFamily M n (translatePotentialSample z omega))
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 : ℝ) ≤ 1)
  calc ahom M n * (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
      (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹
      ≤ ahom M n * (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 8) (.finite 1)
        (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ hpos8 hmono) hσ.le
    _ ≤ (1 + Real.sqrt 2 * e) ^ 2 := hfinal

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
