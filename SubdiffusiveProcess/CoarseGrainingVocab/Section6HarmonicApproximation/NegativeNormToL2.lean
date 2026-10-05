
module

public import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.Theory

@[expose] public section

/-!
# The negative-norm-to-`L²` step for harmonic approximation

This is the specialization at `t = s / 4` of CoarseGraining's zero-trace
negative-Besov Poincaré theorem.  It is the concrete form used in the proof of
`l.harmonic.approximation.good.scales.GMC`.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem rpow_three_neg_half_le :
    Real.rpow (3 : ℝ) (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
  have hsqrt3 : (4 : ℝ) / 3 ≤ Real.sqrt 3 := by
    have hstep : ((4 : ℝ) / 3) ^ 2 ≤ (3 : ℝ) := by norm_num
    calc
      (4 : ℝ) / 3 = Real.sqrt (((4 : ℝ) / 3) ^ 2) :=
        (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt 3 := Real.sqrt_le_sqrt hstep
  rw [Real.rpow_eq_pow, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.sqrt_eq_rpow]
  have h := inv_anti₀ (show (0 : ℝ) < 4 / 3 by norm_num) hsqrt3
  rw [show ((4 : ℝ) / 3)⁻¹ = 3 / 4 by norm_num] at h
  exact h

private theorem one_sub_rpow_tail_ge {s : ℝ} (hs1 : s ≤ 1) :
    (1 : ℝ) / 4 ≤ 1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)) := by
  have hmono : Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)) ≤
      Real.rpow (3 : ℝ) (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hs1])
  linarith only [hmono, rpow_three_neg_half_le]

private theorem negNormSqrtFactor_le_two {s : ℝ} (hs1 : s ≤ 1) :
    Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)))⁻¹) ≤ 2 := by
  have hinv : (1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)))⁻¹ ≤ 4 := by
    have h := inv_anti₀ (show (0 : ℝ) < 1 / 4 by norm_num)
      (one_sub_rpow_tail_ge hs1)
    rw [show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num] at h
    exact h
  calc
    Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)))⁻¹)
        ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hinv
    _ = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private theorem negNormSqrtFactor_pos {s : ℝ} (hs1 : s ≤ 1) :
    0 < Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)))⁻¹) := by
  refine Real.sqrt_pos.mpr (inv_pos.mpr ?_)
  linarith only [one_sub_rpow_tail_ge hs1]

/-- The dimension-only constant in the zero-trace negative-Besov Poincaré
estimate. -/
noncomputable def negativeNormToL2Constant (d : ℕ) [NeZero d] : ℝ :=
  2 * (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
      (3 : ℝ) ^ ((d : ℝ) + 1) * (d : ℝ)) +
    2 * (3 : ℝ) ^ ((d : ℝ) + 1))

theorem negativeNormToL2Constant_pos (d : ℕ) [NeZero d] :
    0 < negativeNormToL2Constant d := by
  have hcz : 0 ≤ Legacy.cubeNeumannW22CalderonZygmundConstant d :=
    Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d
  have h3 : (0 : ℝ) < (3 : ℝ) ^ ((d : ℝ) + 1) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h1 : (0 : ℝ) ≤
      (d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
        (3 : ℝ) ^ ((d : ℝ) + 1) * (d : ℝ) := by positivity
  unfold negativeNormToL2Constant
  positivity

/-- At exponent `s / 2`, the normalized `L²` value of an `H¹₀` function is
controlled by the concrete negative-Besov seminorm of its gradient. -/
theorem cubeLpNorm_h10_le_negativeBesov_half [NeZero d] (Q : TriadicCube d)
    (u : H10Function (cubeSet Q)) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    cubeBesovScaleWeight 1 Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.toH1Function.toFun x) ≤
      negativeNormToL2Constant d *
        cubeBesovNegativeVectorSeminormTwo Q (s / 2)
          (fun x => u.toH1Function.grad x) := by
  have h := cubeBesovScaleWeight_one_mul_cubeLpNorm_h10_le_grad_negativeBesovTwo
    Q u (t := s / 4) (by linarith only [hs]) (by linarith only [hs1])
  rw [show (2 : ℝ) * (s / 4) = s / 2 by ring] at h
  let C0 : ℝ :=
    ((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
        (3 : ℝ) ^ ((d : ℝ) + 1) * (d : ℝ)) +
      2 * (3 : ℝ) ^ ((d : ℝ) + 1)
  have hC0 : 0 < C0 := by
    have hcz : 0 ≤ Legacy.cubeNeumannW22CalderonZygmundConstant d :=
      Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d
    have h3 : (0 : ℝ) < (3 : ℝ) ^ ((d : ℝ) + 1) :=
      Real.rpow_pos_of_pos (by norm_num) _
    dsimp [C0]
    positivity
  have hfac := negNormSqrtFactor_pos hs1
  have hleft : 0 ≤ cubeBesovScaleWeight 1 Q *
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.toH1Function.toFun x) :=
    mul_nonneg (cubeBesovScaleWeight_nonneg 1 Q)
      (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) _)
  have h' : cubeBesovScaleWeight 1 Q *
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.toH1Function.toFun x) ≤
      C0 * Real.sqrt
          ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)))⁻¹) *
        cubeBesovNegativeVectorSeminormTwo Q (s / 2)
          (fun x => u.toH1Function.grad x) := by
    dsimp [C0]
    exact h
  have hseminorm : 0 ≤ cubeBesovNegativeVectorSeminormTwo Q (s / 2)
      (fun x => u.toH1Function.grad x) := by
    by_contra hneg
    push Not at hneg
    have hrhs : C0 * Real.sqrt
          ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)))⁻¹) *
        cubeBesovNegativeVectorSeminormTwo Q (s / 2)
          (fun x => u.toH1Function.grad x) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hC0 hfac) hneg
    linarith only [hleft, h', hrhs]
  refine h'.trans (mul_le_mul_of_nonneg_right ?_ hseminorm)
  have hcoeff : C0 * Real.sqrt
        ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - s / 4)))⁻¹) ≤
      C0 * 2 :=
    mul_le_mul_of_nonneg_left (negNormSqrtFactor_le_two hs1) hC0.le
  simpa [negativeNormToL2Constant, C0, mul_comm] using hcoeff

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
