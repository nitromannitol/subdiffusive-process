import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BalancedPrebalance
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.SourceEnergyPrice

/-!
# Source-scale arithmetic for the Dirichlet prebalance row

This file isolates the two exact cancellations which turn the physical
coarse-graining right-hand side into the optimizing-scale stochastic core.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- The coefficient normalization in the first prebalance term cancels the
two square-root factors supplied by coarse graining and physical energy. -/
theorem inv_mul_sqrt_mul_sqrt_eq_one {a : ℝ} (ha : 0 < a) :
    a⁻¹ * Real.sqrt a * Real.sqrt a = 1 := by
  calc
    a⁻¹ * Real.sqrt a * Real.sqrt a =
        a⁻¹ * (Real.sqrt a * Real.sqrt a) := by ring
    _ = a⁻¹ * a := by rw [Real.mul_self_sqrt ha.le]
    _ = 1 := inv_mul_cancel₀ ha.ne'

/-- The physical cube factor and the positive-datum dilation factor leave
exactly the `3^(-s₂ k)` optimizing-scale decay. -/
theorem centeredCubeScale_sourceDecay_cancel
    (N k : ℕ) (s2 : ℝ) :
    centeredCubeScale (N : ℤ) *
          (centeredCubeScale (N : ℤ)) ^ (-s2) *
          (centeredCubeScale (N : ℤ))⁻¹ *
          Real.rpow 3 (s2 * (((N : ℤ) - (k : ℤ) : ℤ) : ℝ)) =
      Real.rpow 3 (-s2 * (k : ℝ)) := by
  have hthree : (0 : ℝ) < 3 := by norm_num
  simp only [centeredCubeScale, zpow_natCast]
  rw [← Real.rpow_natCast]
  rw [show ((N : ℤ) - (k : ℤ) : ℤ) = (N : ℤ) - (k : ℤ) by rfl]
  push_cast
  rw [show ((3 : ℝ) ^ (N : ℝ))⁻¹ = (3 : ℝ) ^ (-(N : ℝ)) by
    rw [Real.rpow_neg hthree.le]]
  rw [← Real.rpow_mul hthree.le]
  rw [← Real.rpow_add hthree, ← Real.rpow_add hthree]
  change Real.rpow 3 ((N : ℝ) + (N : ℝ) * -s2 + -(N : ℝ)) *
      Real.rpow 3 (s2 * ((N : ℝ) - (k : ℝ))) = _
  calc
    _ = Real.rpow 3 (((N : ℝ) + (N : ℝ) * -s2 + -(N : ℝ)) +
          s2 * ((N : ℝ) - (k : ℝ))) :=
      (Real.rpow_add hthree _ _).symm
    _ = _ := by congr 1; ring

/-- The exact source-scale normal form of the physical prebalance RHS. -/
def sourceDirichletPrebalanceRHS
    (C s s1 s2 : ℝ) (k : ℕ) (E1 E2 W Y G D : ℝ) : ℝ :=
  C * Real.rpow s (-(3 / 2 : ℝ)) *
      Real.rpow 3 (s1 * (k : ℝ)) * E1 * W * Y * G +
    C * Real.rpow s (-11 / 2) * (s2 - s)⁻¹ *
      Real.rpow 3 (-s2 * (k : ℝ)) *
        (1 + Real.rpow 3 (s1 * (k : ℝ)) * E2 ^ (2 : ℕ)) * D

/-- Substitution of the physical energy and fractional-datum source forms
into `dirichletCoarseGrainingRHS` yields the exact optimizing-scale form. -/
theorem physicalDirichletPrebalanceRHS_eq_source
    {a : ℝ} (ha : 0 < a) (N k : ℕ)
    (C s s1 s2 E1 E2 W Y G D : ℝ) :
    centeredCubeScale (N : ℤ) * a⁻¹ *
        dirichletCoarseGrainingRHS C a s s2
          (Real.rpow 3 (s1 * (k : ℝ)) * E1)
          (Real.rpow 3 ((s1 / 2) * (k : ℝ)) * E2)
          (W * (Y * Real.sqrt a * (centeredCubeScale (N : ℤ))⁻¹ * G))
          ((centeredCubeScale (N : ℤ)) ^ (-s2) *
            (a * (centeredCubeScale (N : ℤ))⁻¹) * D)
          ((N : ℤ) - (k : ℤ)) =
      sourceDirichletPrebalanceRHS C s s1 s2 k E1 E2 W Y G D := by
  unfold dirichletCoarseGrainingRHS sourceDirichletPrebalanceRHS
  have hcoeff := inv_mul_sqrt_mul_sqrt_eq_one ha
  have hscale := centeredCubeScale_sourceDecay_cancel N k s2
  have hgrowth :
      (Real.rpow 3 ((s1 / 2) * (k : ℝ)) * E2) ^ (2 : ℕ) =
        Real.rpow 3 (s1 * (k : ℝ)) * E2 ^ (2 : ℕ) := by
    rw [mul_pow, pow_two]
    calc
      (Real.rpow 3 ((s1 / 2) * (k : ℝ)) *
          Real.rpow 3 ((s1 / 2) * (k : ℝ))) * E2 ^ (2 : ℕ) =
        Real.rpow 3
          (((s1 / 2) * (k : ℝ)) + ((s1 / 2) * (k : ℝ))) *
            E2 ^ (2 : ℕ) := by
          exact congrArg (fun z : ℝ ↦ z * E2 ^ (2 : ℕ))
            (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
      _ = _ := by congr 2; ring
  rw [hgrowth]
  calc
    _ = C * Real.rpow s (-(3 / 2 : ℝ)) *
          Real.rpow 3 (s1 * (k : ℝ)) * E1 * W * Y * G *
            (a⁻¹ * Real.sqrt a * Real.sqrt a) +
        C * Real.rpow s (-11 / 2) * (s2 - s)⁻¹ *
          (centeredCubeScale (N : ℤ) *
            (centeredCubeScale (N : ℤ)) ^ (-s2) *
            (centeredCubeScale (N : ℤ))⁻¹ *
            Real.rpow 3 (s2 * (((N : ℤ) - (k : ℤ) : ℤ) : ℝ))) *
          (1 + Real.rpow 3 (s1 * (k : ℝ)) * E2 ^ (2 : ℕ)) * D := by
      field_simp [ha.ne', centeredCubeScale_ne_zero]
    _ = _ := by rw [hcoeff, hscale, mul_one]

/-- Deterministic coefficient which prices both datum slots of the
source-scale prebalance row by one common source size. -/
def sourceDirichletPrebalanceConstant
    (C s s2 W CG CD : ℝ) : ℝ :=
  C * Real.rpow s (-(3 / 2 : ℝ)) * W * CG +
    C * Real.rpow s (-11 / 2) * (s2 - s)⁻¹ * CD

theorem sourceDirichletPrebalanceConstant_nonneg
    {C s s2 W CG CD : ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (hss2 : s < s2)
    (hW : 0 ≤ W) (hCG : 0 ≤ CG) (hCD : 0 ≤ CD) :
    0 ≤ sourceDirichletPrebalanceConstant C s s2 W CG CD := by
  unfold sourceDirichletPrebalanceConstant
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (Real.rpow_nonneg hs.le _)) hW) hCG)
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg hC (Real.rpow_nonneg hs.le _))
          (inv_nonneg.mpr (sub_nonneg.mpr hss2.le))) hCD)

/-- If the physical energy price and the fractional forcing price are both
bounded by one source size, then the exact source RHS is bounded by the
manuscript prebalance core times that size. -/
theorem sourceDirichletPrebalanceRHS_le_constant_mul_core_mul
    {C s s1 s2 E1 E2 W Y G D CG CD H : ℝ} {k : ℕ}
    (hC : 0 ≤ C) (hs : 0 < s) (hss2 : s < s2)
    (hE1 : 0 ≤ E1) (hW : 0 ≤ W) (hY : 0 ≤ Y)
    (hCG : 0 ≤ CG) (hCD : 0 ≤ CD)
    (hH : 0 ≤ H) (hGprice : G ≤ CG * H) (hDprice : D ≤ CD * H) :
    sourceDirichletPrebalanceRHS C s s1 s2 k E1 E2 W Y G D ≤
      sourceDirichletPrebalanceConstant C s s2 W CG CD *
        dirichletPrebalanceCore s1 s2 k E1 E2 Y * H := by
  let A := C * Real.rpow s (-(3 / 2 : ℝ)) * W
  let B := C * Real.rpow s (-11 / 2) * (s2 - s)⁻¹
  let X := Real.rpow 3 (s1 * (k : ℝ)) * E1 * Y
  let T := Real.rpow 3 (-s2 * (k : ℝ)) *
    (1 + Real.rpow 3 (s1 * (k : ℝ)) * E2 ^ (2 : ℕ))
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg hC (Real.rpow_nonneg hs.le _)) hW
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg hC (Real.rpow_nonneg hs.le _))
      (inv_nonneg.mpr (sub_nonneg.mpr hss2.le))
  have hX : 0 ≤ X := by
    dsimp only [X]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hE1) hY
  have hT : 0 ≤ T := by
    dsimp only [T]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (add_nonneg zero_le_one
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg E2)))
  have hnormalize :
      sourceDirichletPrebalanceRHS C s s1 s2 k E1 E2 W Y G D =
        A * X * G + B * T * D := by
    unfold sourceDirichletPrebalanceRHS
    dsimp only [A, B, X, T]
    ring
  rw [hnormalize]
  calc
    A * X * G + B * T * D ≤
        A * X * (CG * H) + B * T * (CD * H) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hGprice (mul_nonneg hA hX))
        (mul_le_mul_of_nonneg_left hDprice (mul_nonneg hB hT))
    _ = (A * CG * X + B * CD * T) * H := by ring
    _ ≤ ((A * CG + B * CD) * (X + T)) * H := by
      apply mul_le_mul_of_nonneg_right _ hH
      nlinarith [mul_nonneg (mul_nonneg hA hCG) hT,
        mul_nonneg (mul_nonneg hB hCD) hX]
    _ = sourceDirichletPrebalanceConstant C s s2 W CG CD *
        dirichletPrebalanceCore s1 s2 k E1 E2 Y * H := by
      unfold sourceDirichletPrebalanceConstant dirichletPrebalanceCore
      dsimp only [A, B, X, T]

/-- Fixed coefficient of the source forcing in the fractional-datum slot. -/
noncomputable def sourceDirichletFractionalDatumConstant
    (d : ℕ) [NeZero d] (s2 : FractionalOrder) : ℝ :=
  sourceForcingFractionalConstant d s2 * unitDivergenceLiftConstant d

theorem sourceDirichletFractionalDatumConstant_nonneg
    (d : ℕ) [NeZero d] (s2 : FractionalOrder) :
    0 ≤ sourceDirichletFractionalDatumConstant d s2 :=
  mul_nonneg (sourceForcingFractionalConstant_nonneg d s2)
    (unitDivergenceLiftConstant_nonneg d)

/-- The canonical lift and the boundary datum discharge both source slots of
the normalized prebalance RHS against the literal real datum size. -/
theorem sourceDirichletPrebalanceRHS_le_core_mul_sourceSizes
    {d : ℕ} [NeZero d]
    {Ccg Cenergy s1 E1 E2 W Y sourceSize : ℝ} {k : ℕ}
    (hCcg : 0 ≤ Ccg) (hCenergy : 0 ≤ Cenergy)
    (s s2 : FractionalOrder) (hss2 : s.1 < s2.1)
    (hE1 : 0 ≤ E1) (hW : 0 ≤ W) (hY : 0 ≤ Y)
    (hsource : 0 ≤ sourceSize)
    (F : CubeVectorH1Function (originCube d 0))
    (h : H2Datum (originCube d 0))
    (hbudget : (unitCubeVectorH1ENormBudget F).toReal ≤
      unitDivergenceLiftConstant d * sourceSize) :
    sourceDirichletPrebalanceRHS Ccg s.1 s1 s2.1 k E1 E2 W Y
        (sourceDirichletEnergyDatumPrice Cenergy s F h)
        (sourceForcingFractionalConstant d s2 *
          (unitCubeVectorH1ENormBudget F).toReal) ≤
      sourceDirichletPrebalanceConstant Ccg s.1 s2.1 W
          (sourceDirichletEnergyConstant d Cenergy s)
          (sourceDirichletFractionalDatumConstant d s2) *
        dirichletPrebalanceCore s1 s2.1 k E1 E2 Y *
          (sourceSize + h.norm.toReal) := by
  have hH : 0 ≤ sourceSize + h.norm.toReal :=
    add_nonneg hsource ENNReal.toReal_nonneg
  have hGprice : sourceDirichletEnergyDatumPrice Cenergy s F h ≤
      sourceDirichletEnergyConstant d Cenergy s *
        (sourceSize + h.norm.toReal) :=
    sourceDirichletEnergyDatumPrice_le_sourceSizes hCenergy s F h
      hsource hbudget
  have hDprice : sourceForcingFractionalConstant d s2 *
        (unitCubeVectorH1ENormBudget F).toReal ≤
      sourceDirichletFractionalDatumConstant d s2 *
        (sourceSize + h.norm.toReal) := by
    calc
      _ ≤ sourceForcingFractionalConstant d s2 *
          (unitDivergenceLiftConstant d * sourceSize) :=
        mul_le_mul_of_nonneg_left hbudget
          (sourceForcingFractionalConstant_nonneg d s2)
      _ ≤ (sourceForcingFractionalConstant d s2 *
          unitDivergenceLiftConstant d) *
            (sourceSize + h.norm.toReal) := by
        calc
          sourceForcingFractionalConstant d s2 *
              (unitDivergenceLiftConstant d * sourceSize) =
            (sourceForcingFractionalConstant d s2 *
              unitDivergenceLiftConstant d) * sourceSize := by ring
          _ ≤ (sourceForcingFractionalConstant d s2 *
              unitDivergenceLiftConstant d) *
                (sourceSize + h.norm.toReal) :=
            mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right
                (show 0 ≤ h.norm.toReal from ENNReal.toReal_nonneg))
              (sourceDirichletFractionalDatumConstant_nonneg d s2)
      _ = _ := rfl
  exact sourceDirichletPrebalanceRHS_le_constant_mul_core_mul
    hCcg s.2.1 hss2 hE1 hW hY
    (sourceDirichletEnergyConstant_nonneg d hCenergy s)
    (sourceDirichletFractionalDatumConstant_nonneg d s2)
    hH hGprice hDprice

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
