module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEllipticityCaps
public import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.Prefactors

@[expose] public section

/-!
# Pricing the interior Caccioppoli prefactor

This is the `(1/2,s/2)` companion of `BoundaryPrefactorPrice`.  On the
range `s ≤ 1/4`, the entropy gap is uniformly at least `3/8`.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03

noncomputable section

variable {d : ℕ}

/-- Uniform interior prefactor bound at `(1/2,s/2)`. -/
theorem caccioppoliWithRHSPrefactor_interiorHalf_le [NeZero d]
    {Q : TriadicCube d} {A : CoeffFamily d} {C s Theta₀ : ℝ}
    (hC : 0 < C) (hs : 0 < s) (hs4 : s ≤ 1 / 4)
    (hTheta : Ch02.ThetaRatio Q (1 / 2) (s / 2) A ≤ Theta₀) :
    caccioppoliWithRHSPrefactor C Q A (1 / 2) (s / 2) ≤
      (4 * max 1 C) ^ (8 : ℕ) * 8 * Theta₀ ^ (3 : ℕ) := by
  have hCm : (1 : ℝ) ≤ max 1 C := le_max_left _ _
  have hCle : C ≤ max 1 C := le_max_right _ _
  have hTh1 : 1 ≤ Ch02.ThetaRatio Q (1 / 2) (s / 2) A :=
    Ch02.one_le_ThetaRatio_of_pos Q A (by norm_num) (by linarith only [hs])
  have hgap : (3 / 8 : ℝ) ≤ 1 - 1 / 2 - s / 2 := by
    linarith only [hs4]
  have hgapPos : 0 < 1 - 1 / 2 - s / 2 := by linarith only [hgap]
  have hinv : (1 - 1 / 2 - s / 2)⁻¹ ≤ 8 / 3 := by
    have h := inv_anti₀ (show (0 : ℝ) < 3 / 8 by norm_num) hgap
    rw [show ((3 : ℝ) / 8)⁻¹ = 8 / 3 by norm_num] at h
    exact h
  have hbase0 : 0 ≤ C / (1 - 1 / 2 - s / 2) :=
    div_nonneg hC.le hgapPos.le
  have hbase : C / (1 - 1 / 2 - s / 2) ≤ 4 * max 1 C := by
    rw [div_le_iff₀ hgapPos]
    have hmul := mul_le_mul_of_nonneg_left hgap
      (by positivity : 0 ≤ 4 * max 1 C)
    calc
      C ≤ max 1 C := hCle
      _ ≤ 4 * max 1 C * (1 - 1 / 2 - s / 2) := by
        nlinarith only [hmul, hCm]
  have hexp1 : 2 + 4 * (1 / 2 : ℝ) / (1 - 1 / 2 - s / 2) ≤ 8 := by
    have h : 2 / (1 - 1 / 2 - s / 2) ≤ 16 / 3 := by
      rw [div_eq_mul_inv]
      have hh := mul_le_mul_of_nonneg_left hinv (show (0 : ℝ) ≤ 2 by norm_num)
      norm_num at hh ⊢
      exact hh
    linarith only [h]
  have hexp1nn : 0 ≤ 2 + 4 * (1 / 2 : ℝ) / (1 - 1 / 2 - s / 2) := by
    positivity
  have hT1 : Real.rpow (C / (1 - 1 / 2 - s / 2))
      (2 + 4 * (1 / 2) / (1 - 1 / 2 - s / 2)) ≤
        (4 * max 1 C) ^ (8 : ℕ) := by
    calc
      _ ≤ Real.rpow (4 * max 1 C)
          (2 + 4 * (1 / 2) / (1 - 1 / 2 - s / 2)) :=
        Real.rpow_le_rpow hbase0 hbase hexp1nn
      _ ≤ Real.rpow (4 * max 1 C) (8 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith only [hCm]) hexp1
      _ = (4 * max 1 C) ^ (8 : ℕ) := by
        rw [Real.rpow_eq_pow, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
  have hexp2 : (-3 : ℝ) ≤
      -(2 * (1 / 2 : ℝ) / (1 - 1 / 2 - s / 2)) := by
    have h := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 1)
    norm_num at h ⊢
    linarith only [h]
  have hT2 : Real.rpow (1 / 2 : ℝ)
      (-(2 * (1 / 2) / (1 - 1 / 2 - s / 2))) ≤ 8 := by
    calc
      _ ≤ Real.rpow (1 / 2 : ℝ) (-3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hexp2
      _ = 8 := by
        rw [Real.rpow_eq_pow, show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num,
          Real.rpow_intCast]
        norm_num
  have hexp3 : (1 - s / 2) / (1 - 1 / 2 - s / 2) ≤ 3 := by
    rw [div_le_iff₀ hgapPos]
    linarith only [hs4]
  have hT3 : Real.rpow (Ch02.ThetaRatio Q (1 / 2) (s / 2) A)
      ((1 - s / 2) / (1 - 1 / 2 - s / 2)) ≤ Theta₀ ^ (3 : ℕ) := by
    calc
      _ ≤ Real.rpow (Ch02.ThetaRatio Q (1 / 2) (s / 2) A) (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hTh1 hexp3
      _ ≤ Real.rpow Theta₀ (3 : ℝ) :=
        Real.rpow_le_rpow (zero_le_one.trans hTh1) hTheta (by norm_num)
      _ = Theta₀ ^ (3 : ℕ) := by
        rw [Real.rpow_eq_pow, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
  rw [caccioppoliWithRHSPrefactor]
  exact mul_le_mul (mul_le_mul hT1 hT2
      (Real.rpow_nonneg (by norm_num) _) (by positivity)) hT3
    (Real.rpow_nonneg (zero_le_one.trans hTh1) _) (by positivity)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
