import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeEllipticityPrice
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSobolevDisplay
import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock

/-!
# The intrinsic-clock Sobolev display at positive descendant scales

A response test at the outer cutoff, a bounded cube average, a normalized
Besov test, and the annealed scale comparison give the exact Sobolev display.
The constant depends only on dimension, independently of the template depth.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open Homogenization.Book Set MeasureTheory SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Purely scalar price algebra: with `a ≤ 2 * b`, `lam ≤ 9 / b` and `avg ≤ 3 / 2`,
the cutoff price is bounded by `A * s^2 / a` whenever `A ≥ 27 * C * 2^(2/p)`. -/
theorem goodCube_price_algebra (p C A s a b lam avg : ℝ)
    (_hp : 0 < p) (hC : 0 < C) (hs : 0 < s) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ 2 * b) (hlam : 0 ≤ lam) (hlam9 : lam ≤ 9 / b)
    (havg : avg ≤ 3 / 2) (hA : 27 * C * (2 : ℝ) ^ (2 / p) ≤ A) :
    C * (2 : ℝ) ^ (2 / p) * s ^ 2 * lam * avg ≤ A * s ^ 2 / a := by
  have h2 : 0 < (2 : ℝ) ^ (2 / p) := Real.rpow_pos_of_pos (by norm_num) (2 / p)
  have hK : 0 < C * (2 : ℝ) ^ (2 / p) * s ^ 2 :=
    mul_pos (mul_pos hC h2) (pow_pos hs 2)
  have hainv : 0 < a⁻¹ := inv_pos.mpr ha
  have hbinv : 0 < b⁻¹ := inv_pos.mpr hb
  have h5 : a * b⁻¹ ≤ (2 * b) * b⁻¹ := mul_le_mul_of_nonneg_right hab (le_of_lt hbinv)
  rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hb), mul_one] at h5
  have h6 : b⁻¹ ≤ 2 * a⁻¹ := by
    have h7 : a * b⁻¹ * a⁻¹ ≤ 2 * a⁻¹ := mul_le_mul_of_nonneg_right h5 (le_of_lt hainv)
    rw [mul_assoc, mul_comm b⁻¹ a⁻¹, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt ha), one_mul] at h7
    exact h7
  have h1 : lam * avg ≤ 9 / b * (3 / 2) := by
    rcases lt_or_ge avg 0 with h0 | h0
    · have h0' : avg ≤ 0 := le_of_lt h0
      have hle : lam * avg ≤ 0 := by nlinarith [hlam, h0']
      have hpos : (0 : ℝ) < 9 / b * (3 / 2) :=
        mul_pos (div_pos (by norm_num) hb) (by norm_num)
      linarith
    · calc lam * avg ≤ (9 / b) * avg := mul_le_mul_of_nonneg_right hlam9 h0
        _ ≤ (9 / b) * (3 / 2) :=
          mul_le_mul_of_nonneg_left havg (le_of_lt (div_pos (by norm_num) hb))
  have h2b : 9 / b * (3 / 2) ≤ 27 / a := by
    rw [div_eq_mul_inv 9 b, div_eq_mul_inv 27 a]
    calc 9 * b⁻¹ * (3 / 2) = (27 / 2) * b⁻¹ := by ring
      _ ≤ (27 / 2) * (2 * a⁻¹) :=
        mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ 27 / 2)
      _ = 27 * a⁻¹ := by ring
  calc C * (2 : ℝ) ^ (2 / p) * s ^ 2 * lam * avg
      = C * (2 : ℝ) ^ (2 / p) * s ^ 2 * (lam * avg) := by ring
    _ ≤ C * (2 : ℝ) ^ (2 / p) * s ^ 2 * (9 / b * (3 / 2)) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hK)
    _ ≤ C * (2 : ℝ) ^ (2 / p) * s ^ 2 * (27 / a) :=
      mul_le_mul_of_nonneg_left h2b (le_of_lt hK)
    _ = (27 * C * (2 : ℝ) ^ (2 / p)) * (s ^ 2 / a) := by ring
    _ ≤ A * (s ^ 2 / a) := mul_le_mul_of_nonneg_right hA (le_of_lt (div_pos (pow_pos hs 2) ha))
    _ = A * s ^ 2 / a := by ring

theorem goodCube_sobolev_of_positive_scale_tests (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p A : ℝ, 2 < p ∧ 1 ≤ A ∧
      ∀ (M : GMCModel d) (n m : ℕ), m ≤ n →
      ∀ (omega : PotentialSample d) (z : Vec d),
        ellipticityMomentObservable M n (m : ℤ) (1 / 8)
          (translatePotentialSample z omega) ≤ 1 →
        cubeAverage (originCube d (m : ℤ)) (fun x => aCutoff M n omega (x + z)) ≤ 3 / 2 →
        ahom M m ≤ 2 * ahom M n →
        let Q0 := originCube d (m : ℤ)
        let b0 : Vec d → ℝ := fun x => aCutoff M n omega (x + z)
        ∀ hb : ExactCircIntegrable Q0 (fun x => b0 x / cubeAverage Q0 b0 - 1),
          ENNReal.ofReal (Real.rpow 3 (-(1 / 8 : ℝ) * (m : ℝ))) *
            paperNegativeBesovCircDiagonal Q0 (1 / 8) (4 * (d : ℝ))
              (fun x => b0 x / cubeAverage Q0 b0 - 1) hb ≤ 1 →
          GoodCubeSobolevDisplay (aCutoff M n omega) p A
            (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M))
            (z, (3 : ℝ) ^ m) := by
  obtain ⟨p, C, hp, hC, hbridge⟩ := goodCube_weighted_local_sobolev_cutoff d hd
  refine ⟨p, max 1 (27 * C * (2 : ℝ) ^ (2 / p)), hp, le_max_left _ _, ?_⟩
  intro M n m hmn omega z hE1 havg hscale Q0 b0 hb hbesov
  have h1A : (1 : ℝ) ≤ max 1 (27 * C * (2 : ℝ) ^ (2 / p)) := le_max_left _ _
  have hA0 : 0 ≤ max 1 (27 * C * (2 : ℝ) ^ (2 / p)) := by linarith
  have hahomn : 0 < ahom M n := ahom_pos M n
  have hahomm : 0 < ahom M m := ahom_pos M m
  have hE : ellipticityMomentObservable M n (m : ℤ) (1 / 8)
      (translatePotentialSample z omega) ≤ ENNReal.ofReal (1 : ℝ) := by
    rw [ENNReal.ofReal_one]; exact hE1
  have hlam9' : ahom M n * (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
      (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ ≤ 9 := by
    have h1 := goodCube_cutoff_lambda_price_le_of_ellipticity_test M n m hmn z omega
      (by norm_num : (0 : ℝ) ≤ 1) hE
    have hsqrt : Real.sqrt 2 ≤ 2 := by
      have hs1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      have hs3 : 0 < 2 + Real.sqrt 2 := by linarith
      nlinarith
    have h3 : (1 + Real.sqrt 2 * 1) ^ 2 ≤ 9 := by
      have hs1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [hsqrt, hs1]
    linarith
  have hlam0 : 0 ≤ (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
      (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ :=
    inv_nonneg.mpr (le_of_lt (Ch02.lambdaSq_pos (originCube d (m : ℤ))
      (aCutoffFamily M n (translatePotentialSample z omega)) (by norm_num) (by norm_num [Ch02.MultiscaleExponent.IsAdmissible])))
  have hlamle : (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
      (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ ≤ 9 / ahom M n := by
    have h2 : (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
        (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ * ahom M n ≤ 9 := by
      rw [mul_comm]; exact hlam9'
    have hinv : 0 < (ahom M n)⁻¹ := inv_pos.mpr hahomn
    have h3 : (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
        (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ * ahom M n * (ahom M n)⁻¹
        ≤ 9 * (ahom M n)⁻¹ := mul_le_mul_of_nonneg_right h2 (le_of_lt hinv)
    have h4 : (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
        (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ * ahom M n * (ahom M n)⁻¹
        = (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
        (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hahomn), mul_one]
    rw [div_eq_mul_inv 9 (ahom M n), ← h4]
    exact h3
  have hs : 0 < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num : (0 : ℝ) < 3) (m : ℤ)
  have hprice : C * (1 + 1) ^ (2 / p) * ((3 : ℝ) ^ (m : ℤ)) ^ 2 *
      (Ch02.lambdaSq (originCube d (m : ℤ)) (1 / 2) (.finite 1)
        (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ *
      cubeAverage Q0 b0 ≤
      max 1 (27 * C * (2 : ℝ) ^ (2 / p)) *
        SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M) ((3 : ℝ) ^ (m : ℤ)) := by
    have h2p : (1 + 1 : ℝ) ^ (2 / p) = (2 : ℝ) ^ (2 / p) := by norm_num
    have hclock : SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)
        ((3 : ℝ) ^ (m : ℤ)) = ((3 : ℝ) ^ (m : ℤ)) ^ 2 / ahom M m := by
      rw [zpow_natCast, SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale_triadic]
      show (3 : ℝ) ^ (2 * m) / ahom M m = ((3 : ℝ) ^ m) ^ 2 / ahom M m
      rw [← pow_mul, mul_comm m 2]
    rw [h2p, hclock, ← mul_div_assoc]
    exact goodCube_price_algebra p C (max 1 (27 * C * (2 : ℝ) ^ (2 / p)))
      ((3 : ℝ) ^ (m : ℤ)) (ahom M m) (ahom M n) _ (cubeAverage Q0 b0)
      (by linarith) hC hs hahomm hahomn hscale hlam0 hlamle havg (le_max_right _ _)
  have hbound : ENNReal.ofReal (Real.rpow 3 (-(1 / 8 : ℝ) * (m : ℝ))) *
      paperNegativeBesovCircDiagonal Q0 (1 / 8) (4 * (d : ℝ))
        (fun x => b0 x / cubeAverage Q0 b0 - 1) hb ≤ ENNReal.ofReal (1 : ℝ) := by
    rw [ENNReal.ofReal_one]; exact hbesov
  have hdisp := hbridge M n omega (m : ℤ) z hb 1 le_rfl hbound
    (max 1 (27 * C * (2 : ℝ) ^ (2 / p)))
    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (ahom M)) hA0 hprice
  rw [zpow_natCast] at hdisp
  exact hdisp

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
