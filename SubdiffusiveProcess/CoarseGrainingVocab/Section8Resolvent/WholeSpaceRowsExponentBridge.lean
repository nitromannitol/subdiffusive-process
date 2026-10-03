/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsOffGridEllipticity
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Representatives

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization Homogenization.Book Homogenization.Book.Ch02
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Weighted Cauchy–Schwarz for a summable probability mass and a summable
nonnegative first moment.

PROVENANCE: `Section6Dirichlet/EnergyFactor.lean`, where it is private. -/
theorem tsum_mul_sqrt_le_sqrt_tsum_mul
    (w D : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hD : ∀ n, 0 ≤ D n)
    (hsumW : Summable w) (hsumD : Summable fun n ↦ w n * D n) :
    (∑' n, w n * Real.sqrt (D n)) ≤
      Real.sqrt ((∑' n, w n) * ∑' n, w n * D n) := by
  have hroot : Summable fun n ↦ w n * Real.sqrt (D n) := by
    apply Summable.of_nonneg_of_le
      (fun n ↦ mul_nonneg (hw n) (Real.sqrt_nonneg _))
      (fun n ↦ ?_)
      (hsumW.add hsumD)
    have hsqrt : Real.sqrt (D n) ≤ 1 + D n := by
      nlinarith [Real.sq_sqrt (hD n), Real.sqrt_nonneg (D n)]
    calc
      w n * Real.sqrt (D n) ≤ w n * (1 + D n) :=
        mul_le_mul_of_nonneg_left hsqrt (hw n)
      _ = w n + w n * D n := by ring
  apply hroot.tsum_le_of_sum_le
  intro s
  have hsumW_le : (∑ n ∈ s, w n) ≤ ∑' n, w n :=
    hsumW.sum_le_tsum s fun n _ ↦ hw n
  have hsumD_le : (∑ n ∈ s, w n * D n) ≤ ∑' n, w n * D n :=
    hsumD.sum_le_tsum s fun n _ ↦ mul_nonneg (hw n) (hD n)
  have hcs : (∑ n ∈ s, w n * Real.sqrt (D n)) ≤
      Real.sqrt (∑ n ∈ s, w n) * Real.sqrt (∑ n ∈ s, w n * D n) := by
    have h := Real.sum_sqrt_mul_sqrt_le
      (s := s) (f := w) (g := fun n ↦ w n * D n)
      hw (fun n ↦ mul_nonneg (hw n) (hD n))
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl ?_
    intro n _
    calc
      w n * Real.sqrt (D n) = (Real.sqrt (w n)) ^ 2 * Real.sqrt (D n) := by
        rw [Real.sq_sqrt (hw n)]
      _ = Real.sqrt (w n) * (Real.sqrt (w n) * Real.sqrt (D n)) := by ring
      _ = Real.sqrt (w n) * Real.sqrt (w n * D n) := by
        rw [Real.sqrt_mul (hw n)]
  calc
    (∑ n ∈ s, w n * Real.sqrt (D n)) ≤
        Real.sqrt (∑ n ∈ s, w n) * Real.sqrt (∑ n ∈ s, w n * D n) := hcs
    _ ≤ Real.sqrt (∑' n, w n) * Real.sqrt (∑' n, w n * D n) := by
      gcongr
    _ = Real.sqrt ((∑' n, w n) * ∑' n, w n * D n) := by
      rw [Real.sqrt_mul (tsum_nonneg hw)]

/-- The two geometric weight sequences coincide. -/
theorem geometricWeight_one_eq_two_half (s : ℝ) (n : ℕ) :
    Ch02.geometricWeight s 1 n = Ch02.geometricWeight (s / 2) 2 n := by
  unfold Ch02.geometricWeight Ch02.geometricDiscount
  have h1 : -s * 1 = -(s / 2) * 2 := by ring
  have h2 : -s * 1 * (n : ℝ) = -(s / 2) * 2 * (n : ℝ) := by ring
  rw [h1]

theorem summable_geometricWeight_one {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => Ch02.geometricWeight s 1 n) := by
  by_contra hcon
  have hzero : ∑' n : ℕ, Ch02.geometricWeight s 1 n = 0 :=
    tsum_eq_zero_of_not_summable hcon
  have hone : ∑' n : ℕ, Ch02.geometricWeight s 1 n = 1 := by
    simpa [Ch02.geometricWeight_eq_old] using
      Homogenization.tsum_geometricWeight_one_eq_one hs
  rw [hzero] at hone
  exact absurd hone (by norm_num)

theorem tsum_geometricWeight_one {s : ℝ} (hs : 0 < s) :
    ∑' n : ℕ, Ch02.geometricWeight s 1 n = 1 := by
  simpa [Ch02.geometricWeight_eq_old] using
    Homogenization.tsum_geometricWeight_one_eq_one hs

/-! ## The two comparisons -/

private theorem geometricWeight_one_nonneg {s : ℝ} (hs : 0 < s) (n : ℕ) :
    0 ≤ Ch02.geometricWeight s 1 n := by
  unfold Ch02.geometricWeight
  refine mul_nonneg ?_ (Real.rpow_nonneg (by norm_num) _)
  exact Ch02.book_geometricDiscount_nonneg (by positivity)

private theorem rpow_half_eq_sqrt (x : ℝ) :
    Real.rpow x (1 / 2) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm

/-- **`Lambda_{s,1}` is dominated by `Lambda_{s/2,2}`, with constant one.** -/
theorem LambdaS_le_LambdaSq_two_half [NeZero d] (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) :
    Ch02.LambdaS Q s a ≤ Ch02.LambdaSq Q (s / 2) (.finite 2) a := by
  have hs2 : 0 < s / 2 := by linarith only [hs]
  have hM0 : ∀ n : ℕ,
      0 ≤ Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
    fun n => Ch02.maxDescendantBMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hw0 : ∀ n : ℕ, 0 ≤ Ch02.geometricWeight s 1 n :=
    fun n => geometricWeight_one_nonneg hs n
  have hsum2 : Summable (fun n : ℕ => Ch02.geometricWeight s 1 n *
      Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) := by
    have h := Ch02.summable_B_series_pointwiseCoeffField Q a hs2
      (by norm_num : (0 : ℝ) < 2)
    have hone : ∀ x : ℝ, Real.rpow x 1 = x := fun x => Real.rpow_one x
    simp only [show (2 : ℝ) / 2 = 1 by norm_num, hone,
      ← geometricWeight_one_eq_two_half] at h
    exact h
  have hser1 : Real.rpow (Ch02.LambdaS Q s a) (1 / 2) =
      ∑' n : ℕ, Ch02.geometricWeight s 1 n *
        Real.rpow
          (Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2) :=
    Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum Q s 1 a
      (by norm_num : (0 : ℝ) < 1) (by positivity : 0 ≤ s * 1)
  have hser2 : Ch02.LambdaSq Q (s / 2) (.finite 2) a =
      ∑' n : ℕ, Ch02.geometricWeight s 1 n *
        Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a := by
    have h := Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum Q (s / 2) 2 a
      (by norm_num : (0 : ℝ) < 2) (by positivity : 0 ≤ s / 2 * 2)
    have hone : ∀ x : ℝ, Real.rpow x 1 = x := fun x => Real.rpow_one x
    simp only [show (2 : ℝ) / 2 = 1 by norm_num, hone,
      ← geometricWeight_one_eq_two_half] at h
    exact h
  have hTeq : (∑' n : ℕ, Ch02.geometricWeight s 1 n *
      Real.rpow
        (Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
        (1 / 2)) =
      ∑' n : ℕ, Ch02.geometricWeight s 1 n *
        Real.sqrt
          (Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) :=
    tsum_congr fun n => by rw [rpow_half_eq_sqrt]
  have hCS := tsum_mul_sqrt_le_sqrt_tsum_mul
    (fun n : ℕ => Ch02.geometricWeight s 1 n)
    (fun n : ℕ => Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a)
    hw0 hM0 (summable_geometricWeight_one hs) hsum2
  rw [tsum_geometricWeight_one hs, one_mul] at hCS
  have hS0 : 0 ≤ ∑' n : ℕ, Ch02.geometricWeight s 1 n *
      Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
    tsum_nonneg fun n => mul_nonneg (hw0 n) (hM0 n)
  have hT0 : 0 ≤ ∑' n : ℕ, Ch02.geometricWeight s 1 n *
      Real.sqrt
        (Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) :=
    tsum_nonneg fun n => mul_nonneg (hw0 n) (Real.sqrt_nonneg _)
  have hX0 : 0 ≤ Ch02.LambdaS Q s a :=
    Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num)
  have hXsqrt : Real.sqrt (Ch02.LambdaS Q s a) =
      ∑' n : ℕ, Ch02.geometricWeight s 1 n *
        Real.sqrt
          (Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) := by
    rw [Real.sqrt_eq_rpow]
    rw [show ((1 : ℝ) / 2) = 1 / 2 from rfl] at hser1
    rw [← hTeq]
    exact hser1
  rw [hser2]
  calc
    Ch02.LambdaS Q s a = Real.sqrt (Ch02.LambdaS Q s a) ^ 2 :=
      (Real.sq_sqrt hX0).symm
    _ ≤ Real.sqrt (∑' n : ℕ, Ch02.geometricWeight s 1 n *
          Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a) ^ 2 := by
        rw [hXsqrt]
        nlinarith [hT0, Real.sqrt_nonneg (∑' n : ℕ, Ch02.geometricWeight s 1 n *
          Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a), hCS]
    _ = _ := Real.sq_sqrt hS0

/-- **`lambda_{t,1}^{-1}` is dominated by `lambda_{t/2,2}^{-1}`, with constant
one.** -/
theorem lambdaS_inv_le_lambdaSq_two_half_inv [NeZero d] (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) {t : ℝ} (ht : 0 < t) :
    (Ch02.lambdaS Q t a)⁻¹ ≤ (Ch02.lambdaSq Q (t / 2) (.finite 2) a)⁻¹ := by
  have ht2 : 0 < t / 2 := by linarith only [ht]
  have hN0 : ∀ n : ℕ,
      0 ≤ Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
        (Q.scale - (n : ℤ)) a :=
    fun n => Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a
  have hw0 : ∀ n : ℕ, 0 ≤ Ch02.geometricWeight t 1 n :=
    fun n => geometricWeight_one_nonneg ht n
  have hsum2 : Summable (fun n : ℕ => Ch02.geometricWeight t 1 n *
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
        (Q.scale - (n : ℤ)) a) := by
    have h := Ch02.summable_sigmaStarInv_series_pointwiseCoeffField Q a ht2
      (by norm_num : (0 : ℝ) < 2)
    have hone : ∀ x : ℝ, Real.rpow x 1 = x := fun x => Real.rpow_one x
    simp only [show (2 : ℝ) / 2 = 1 by norm_num, hone,
      ← geometricWeight_one_eq_two_half] at h
    exact h
  have hser1 : Real.rpow (Ch02.lambdaS Q t a) (-1 / 2) =
      ∑' n : ℕ, Ch02.geometricWeight t 1 n *
        Real.rpow
          (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a) (1 / 2) :=
    Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q t 1 a
      (by norm_num : (0 : ℝ) < 1) (by positivity : 0 ≤ t * 1)
  have hser2 : (Ch02.lambdaSq Q (t / 2) (.finite 2) a)⁻¹ =
      ∑' n : ℕ, Ch02.geometricWeight t 1 n *
        Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) a := by
    have h := Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q (t / 2) 2 a
      (by norm_num : (0 : ℝ) < 2) (by positivity : 0 ≤ t / 2 * 2)
    have hone : ∀ x : ℝ, Real.rpow x 1 = x := fun x => Real.rpow_one x
    rw [show (-2 : ℝ) / 2 = -1 by norm_num] at h
    have hinv : Real.rpow (Ch02.lambdaSq Q (t / 2) (.finite 2) a) (-1) =
        (Ch02.lambdaSq Q (t / 2) (.finite 2) a)⁻¹ := Real.rpow_neg_one _
    rw [hinv] at h
    simp only [show (2 : ℝ) / 2 = 1 by norm_num, hone,
      ← geometricWeight_one_eq_two_half] at h
    exact h
  have hTeq : (∑' n : ℕ, Ch02.geometricWeight t 1 n *
      Real.rpow
        (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) a) (1 / 2)) =
      ∑' n : ℕ, Ch02.geometricWeight t 1 n *
        Real.sqrt
          (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a) :=
    tsum_congr fun n => by rw [rpow_half_eq_sqrt]
  have hCS := tsum_mul_sqrt_le_sqrt_tsum_mul
    (fun n : ℕ => Ch02.geometricWeight t 1 n)
    (fun n : ℕ => Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
      (Q.scale - (n : ℤ)) a)
    hw0 hN0 (summable_geometricWeight_one ht) hsum2
  rw [tsum_geometricWeight_one ht, one_mul] at hCS
  have hS0 : 0 ≤ ∑' n : ℕ, Ch02.geometricWeight t 1 n *
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
        (Q.scale - (n : ℤ)) a :=
    tsum_nonneg fun n => mul_nonneg (hw0 n) (hN0 n)
  have hT0 : 0 ≤ ∑' n : ℕ, Ch02.geometricWeight t 1 n *
      Real.sqrt
        (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) a) :=
    tsum_nonneg fun n => mul_nonneg (hw0 n) (Real.sqrt_nonneg _)
  have hX0 : 0 ≤ Ch02.lambdaS Q t a :=
    Ch02.lambdaSq_finite_nonneg Q a ht (by norm_num)
  have hsq : (Ch02.lambdaS Q t a)⁻¹ =
      Real.rpow (Ch02.lambdaS Q t a) (-1 / 2) ^ 2 := by
    calc (Ch02.lambdaS Q t a)⁻¹
        = Real.rpow (Ch02.lambdaS Q t a) (-1) := (Real.rpow_neg_one _).symm
      _ = Real.rpow (Ch02.lambdaS Q t a) ((-1 / 2) * 2) := by norm_num
      _ = Real.rpow (Real.rpow (Ch02.lambdaS Q t a) (-1 / 2)) 2 :=
          Real.rpow_mul hX0 _ _
      _ = Real.rpow (Ch02.lambdaS Q t a) (-1 / 2) ^ 2 := by
          rw [← Real.rpow_natCast (Real.rpow (Ch02.lambdaS Q t a) (-1 / 2)) 2]
          norm_num
  rw [hsq, hser1, hTeq, hser2]
  calc
    (∑' n : ℕ, Ch02.geometricWeight t 1 n *
        Real.sqrt (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) a)) ^ 2 ≤
        Real.sqrt (∑' n : ℕ, Ch02.geometricWeight t 1 n *
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a) ^ 2 := by
      nlinarith [hT0, hCS, Real.sqrt_nonneg (∑' n : ℕ,
        Ch02.geometricWeight t 1 n *
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a)]
    _ = _ := Real.sq_sqrt hS0

/-- The ratio form: `Ch02.ThetaRatio` at `q = 1` is dominated by the `q = 2`
ratio at half the indices, which is the form the off-grid transfer bounds. -/
theorem thetaRatio_le_two_half [NeZero d] (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Ch02.ThetaRatio Q s t a ≤
      Ch02.LambdaSq Q (s / 2) (.finite 2) a *
        (Ch02.lambdaSq Q (t / 2) (.finite 2) a)⁻¹ := by
  have hU := LambdaS_le_LambdaSq_two_half Q a hs
  have hL := lambdaS_inv_le_lambdaSq_two_half_inv Q a ht
  have hU0 : 0 ≤ Ch02.LambdaS Q s a :=
    Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num)
  have hL0 : 0 ≤ (Ch02.lambdaS Q t a)⁻¹ :=
    inv_nonneg.mpr (Ch02.lambdaSq_finite_nonneg Q a ht (by norm_num))
  have hRU : 0 ≤ Ch02.LambdaSq Q (s / 2) (.finite 2) a := le_trans hU0 hU
  rw [Ch02.ThetaRatio, div_eq_mul_inv]
  exact mul_le_mul hU hL hL0 hRU

/-- **The Caccioppoli ellipticity ratio of a half-grid cell.**

Composing `thetaRatio_le_two_half` with
`WholeSpaceRowsOffGridEllipticity.thetaRatio_two_translated_le`: the ratio
`Theta_{s,t}` that `caccioppoliWithRHSPrefactor` is built from, evaluated on a
translate of a triadic cube `P` for the translated coefficient family, is
controlled by the `q = 2` ratio of any triadic cube `K` containing the
translate. -/
theorem thetaRatio_translated_le [NeZero d]
    {w : Vec d} {P K : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (A Aw : Ch02.TriadicCoeffFamily d) {s t u : ℝ}
    (hs0 : 0 < s) (ht0 : 0 < t) (hu0 : 0 < u)
    (hus : u < s / 2) (hut : u < t / 2)
    (hs : s / 2 ≤ 1 / 2) (ht : t / 2 ≤ 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hgw : ∀ S : TriadicCube d,
      (Aw.coeffOn S).toCoeffField = translateCoeffField w g)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w (cubeSet P)) g)
    (hcontain : translateSet w (cubeSet P) ⊆ cubeSet K) :
    Ch02.ThetaRatio P s t Aw ≤
      (LambdaStabilitySupport.offGridStabilityConst d (s / 2) u *
          LambdaStabilitySupport.offGridStabilityConst d (t / 2) u) *
        ((3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
            (3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
          (Ch02.LambdaSq K u (.finite 2) A *
            (Ch02.lambdaSq K u (.finite 2) A)⁻¹)) :=
  le_trans (thetaRatio_le_two_half P Aw hs0 ht0)
    (thetaRatio_two_translated_le A Aw hu0 hus hut hs ht hg hgw hEll hcontain)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
