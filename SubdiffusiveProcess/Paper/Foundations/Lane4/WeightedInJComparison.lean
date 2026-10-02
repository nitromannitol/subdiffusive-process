import SubdiffusiveProcess.Paper.in_J
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Properties

/-!
# Weighted comparison on `in_J`

The `q = 2, s0` weighted ellipticity quantities control the `q = 1, t` quantities
when `0 < s0` and `2 * s0 ≤ t ≤ 1`.
-/

open MeasureTheory
open scoped ENNReal

namespace Homogenization
namespace Book
namespace Ch02
namespace WeightedInJComparison
noncomputable section

private theorem weight_le {s s0 : ℝ} (hs0 : 0 < s0) (hs : 2 * s0 ≤ s) (n : ℕ) :
    geometricWeight s 1 n ≤
      (geometricDiscount s 1 / geometricDiscount s0 2) * geometricWeight s0 2 n := by
  have hc2 : 0 < geometricDiscount s0 2 := book_geometricDiscount_pos (by positivity)
  have hc1 : 0 ≤ geometricDiscount s 1 := book_geometricDiscount_nonneg (by nlinarith)
  unfold geometricWeight
  have hpow : Real.rpow (3 : ℝ) (-s * 1 * (n : ℝ)) ≤ Real.rpow (3 : ℝ) (-s0 * 2 * (n : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  calc geometricDiscount s 1 * Real.rpow (3 : ℝ) (-s * 1 * (n : ℝ))
      ≤ geometricDiscount s 1 * Real.rpow (3 : ℝ) (-s0 * 2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow hc1
    _ = (geometricDiscount s 1 / geometricDiscount s0 2) *
          (geometricDiscount s0 2 * Real.rpow (3 : ℝ) (-s0 * 2 * (n : ℝ))) := by
        field_simp

theorem LambdaSq_one_le_two {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    {s s0 : ℝ} (hs0 : 0 < s0) (hs : 2 * s0 ≤ s) :
    LambdaSq Q s (.finite 1) a ≤
      (geometricDiscount s 1 / geometricDiscount s0 2) * LambdaSq Q s0 (.finite 2) a := by
  have hspos : 0 < s := by linarith
  set B : ℕ → ℝ := fun n => maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a with hBdef
  have hB0 : ∀ n, 0 ≤ B n := fun n =>
    maxDescendantBMatrixNormAtScale_nonneg Q (by omega) a
  have hJ := LambdaSq_finite_one_le_tsum_weighted_maxDescendantBMatrixNormAtScale Q a hspos
  have hsum1 := summable_geometricWeight_one_mul_maxDescendantBMatrixNormAtScale Q a hspos
  have hsum2 := summable_B_series_pointwiseCoeffField Q a hs0 (q := 2) two_pos
  have hr : ∀ x : ℝ, Real.rpow x ((2 : ℝ) / 2) = x := fun x => by norm_num
  simp only [hr] at hsum2
  have hL2 : LambdaSq Q s0 (.finite 2) a = ∑' n : ℕ, geometricWeight s0 2 n * B n := by
    rw [LambdaSq_finite, LambdaSqFinite]
    simp only [hr]
    rfl
  rw [hL2, ← tsum_mul_left]
  refine hJ.trans (Summable.tsum_le_tsum (fun n => ?_) hsum1 (hsum2.mul_left _))
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (weight_le hs0 hs n) (hB0 n)

theorem lambdaSq_one_inv_le_two_inv {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) {s s0 : ℝ} (hs0 : 0 < s0) (hs : 2 * s0 ≤ s) :
    (lambdaSq Q s (.finite 1) a)⁻¹ ≤
      (geometricDiscount s 1 / geometricDiscount s0 2) * (lambdaSq Q s0 (.finite 2) a)⁻¹ := by
  have hspos : 0 < s := by linarith
  set S : ℕ → ℝ := fun n =>
    maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a with hSdef
  have hS0 : ∀ n, 0 ≤ S n := fun n =>
    maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q (by omega) a
  have hJ :=
    lambdaSq_finite_one_inv_le_tsum_weighted_maxDescendantSigmaStarInvMatrixNormAtScale Q a hspos
  have hsum1 :=
    summable_geometricWeight_one_mul_maxDescendantSigmaStarInvMatrixNormAtScale Q a hspos
  have hsum2 := summable_sigmaStarInv_series_pointwiseCoeffField Q a hs0 (q := 2) two_pos
  have hr : ∀ x : ℝ, Real.rpow x ((2 : ℝ) / 2) = x := fun x => by norm_num
  simp only [hr] at hsum2
  have hl2 : (lambdaSq Q s0 (.finite 2) a)⁻¹ = ∑' n : ℕ, geometricWeight s0 2 n * S n := by
    rw [lambdaSq_finite, lambdaSqFinite]
    simp only [hr]
    rw [show (-((2 : ℝ) / 2)) = -1 by norm_num, Real.rpow_eq_pow, Real.rpow_neg_one, inv_inv]
  rw [hl2, ← tsum_mul_left]
  refine hJ.trans (Summable.tsum_le_tsum (fun n => ?_) hsum1 (hsum2.mul_left _))
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (weight_le hs0 hs n) (hS0 n)

end
end WeightedInJComparison
end Ch02
end Book
end Homogenization

open SubdiffusiveProcess
namespace Paper
noncomputable section
open Homogenization.Book.Ch02

/-- in_J form: at admissible arguments, `Λ_{t,1} ≤ K Λ_{s0,2}` and `c λ_{s0,2} ≤ λ_{t,1}`, with
`K = c_{t,1}/c_{s0,2}`, for `0 < s0`, `2 s0 ≤ t ≤ 1`. -/
theorem inJ_q_comparison {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    {t s0 : ℝ} (hs0 : 0 < s0) (hts : 2 * s0 ≤ t) (ht1 : t ≤ 1) :
    E.Lam z r hr a w r' t 1 ≤
        (geometricDiscount t 1 / geometricDiscount s0 2) * E.Lam z r hr a w r' s0 2 ∧
      (geometricDiscount s0 2 / geometricDiscount t 1) * E.lam z r hr a w r' s0 2 ≤
        E.lam z r hr a w r' t 1 := by
  haveI : NeZero d := ⟨by omega⟩
  have htpos : 0 < t := by linarith
  have hs01 : s0 ∈ Set.Ioc (0 : ℝ) 1 := ⟨hs0, by linarith⟩
  have ht : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨htpos, ht1⟩
  have hL1 := E.Lam_eq z r hr a w r' hr' hsub t ht 1 le_rfl
  have hL2 := E.Lam_eq z r hr a w r' hr' hsub s0 hs01 2 (by norm_num)
  have hl1 := E.lam_eq z r hr a w r' hr' hsub t ht 1 le_rfl
  have hl2 := E.lam_eq z r hr a w r' hr' hsub s0 hs01 2 (by norm_num)
  simp only [ENNReal.one_ne_top, ENNReal.ofNat_ne_top, if_false, ENNReal.toReal_one,
    ENNReal.toReal_ofNat] at hL1 hL2 hl1 hl2
  refine ⟨?_, ?_⟩
  · rw [hL1, hL2]
    exact WeightedInJComparison.LambdaSq_one_le_two _ _ hs0 hts
  · have hc2 : 0 < geometricDiscount s0 2 := book_geometricDiscount_pos (by positivity)
    have hc1 : 0 < geometricDiscount t 1 := book_geometricDiscount_pos (by simpa using htpos)
    have hx := E.lam_pos z r hr a w r' t 1
    have hy := E.lam_pos z r hr a w r' s0 2
    have hinv := WeightedInJComparison.lambdaSq_one_inv_le_two_inv
      (Homogenization.originCube d 0) (E.chart z r hr a w r') hs0 hts
    rw [← hl1, ← hl2] at hinv
    set x := E.lam z r hr a w r' t 1
    set y := E.lam z r hr a w r' s0 2
    have hK : 0 < geometricDiscount t 1 / geometricDiscount s0 2 := div_pos hc1 hc2
    have h' : x⁻¹ ≤ (y / (geometricDiscount t 1 / geometricDiscount s0 2))⁻¹ := by
      rw [inv_div]; rwa [div_eq_mul_inv] at *
    have := (inv_le_inv₀ hx (div_pos hy hK)).1 h'
    calc (geometricDiscount s0 2 / geometricDiscount t 1) * y
        = y / (geometricDiscount t 1 / geometricDiscount s0 2) := by field_simp
      _ ≤ x := this

end
end Paper

