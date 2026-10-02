import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! The geometric outer sum for every positive finite exponent. -/
open Homogenization.Book
open scoped BigOperators

noncomputable section
namespace SubdiffusiveProcess.LambdaStability

/-- The exact ratio of geometric normalizations costs at most the ratio of indices. -/
theorem geometricDiscount_ratio_le {s t q : ℝ} (hs : 0 < s) (hst : s < t)
    (hq : 0 < q) :
    Ch02.geometricDiscount t q / Ch02.geometricDiscount (t - s) q ≤ t / (t - s) := by
  have hdiff : 0 < t - s := sub_pos.mpr hst
  have ht : 0 < t := hs.trans hst
  have hp : 1 ≤ t / (t - s) := (le_div_iff₀ hdiff).2 (by linarith)
  let r : ℝ := (3 : ℝ) ^ (-(t - s) * q)
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
  have hpow : r ^ (t / (t - s)) = (3 : ℝ) ^ (-t * q) := by
    dsimp [r]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    field_simp
  have hb := one_add_mul_self_le_rpow_one_add
    (s := r - 1) (by linarith : -1 ≤ r - 1) hp
  rw [show 1 + (r - 1) = r by ring, hpow] at hb
  unfold Ch02.geometricDiscount
  apply (div_le_iff₀ (by change 0 < 1 - r; linarith)).2
  change 1 - (3 : ℝ) ^ (-t * q) ≤ t / (t - s) * (1 - r)
  linarith

/-- A shell cap gives the finite-exponent norm estimate with its exact normalization. -/
theorem finite_norm_le_of_shell_cap {s t q A : ℝ}
    (hs : 0 < s) (hst : s < t) (hq : 0 < q) (hA : 0 ≤ A)
    (M : ℕ → ℝ) (hM0 : ∀ l, 0 ≤ M l)
    (hM : ∀ l, M l ≤ A * (3 : ℝ) ^ (2 * s * (l : ℝ))) :
    (∑' l : ℕ, Ch02.geometricWeight t q l * (M l) ^ (q / 2)) ^ (2 / q) ≤
      (t / (t - s)) ^ (2 / q) * A := by
  have hdiff : 0 < t - s := sub_pos.mpr hst
  have ht : 0 < t := hs.trans hst
  let r : ℝ := (3 : ℝ) ^ (-(t - s) * q)
  let D : ℝ := Ch02.geometricDiscount t q
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
  have hD0 : 0 ≤ D := by
    dsimp [D, Ch02.geometricDiscount]
    have := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ)) (by norm_num)
      (show -t * q < 0 by nlinarith)
    linarith
  have hgeom : Summable (fun l : ℕ => r ^ l) := summable_geometric_of_lt_one hr0 hr1
  have hmajor : Summable (fun l : ℕ => D * A ^ (q / 2) * r ^ l) :=
    hgeom.mul_left (D * A ^ (q / 2))
  have hterm : ∀ l : ℕ,
      Ch02.geometricWeight t q l * (M l) ^ (q / 2) ≤ D * A ^ (q / 2) * r ^ l := by
    intro l
    have hpow := Real.rpow_le_rpow (hM0 l) (hM l) (by positivity : 0 ≤ q / 2)
    have hweight : Ch02.geometricWeight t q l = D * (3 : ℝ) ^ (-t * q * (l : ℝ)) := rfl
    have hw : 0 ≤ Ch02.geometricWeight t q l := by
      rw [hweight]
      exact mul_nonneg hD0 (Real.rpow_nonneg (by norm_num) _)
    calc
      Ch02.geometricWeight t q l * (M l) ^ (q / 2) ≤
          Ch02.geometricWeight t q l * (A * (3 : ℝ) ^ (2 * s * (l : ℝ))) ^ (q / 2) :=
        mul_le_mul_of_nonneg_left hpow hw
      _ = D * A ^ (q / 2) * r ^ l := by
        rw [hweight, Real.mul_rpow hA (Real.rpow_nonneg (by norm_num) _),
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
        rw [show D * (3 : ℝ) ^ (-t * q * (l : ℝ)) *
            (A ^ (q / 2) * (3 : ℝ) ^ (2 * s * (l : ℝ) * (q / 2))) =
            D * A ^ (q / 2) * ((3 : ℝ) ^ (-t * q * (l : ℝ)) *
              (3 : ℝ) ^ (2 * s * (l : ℝ) * (q / 2))) by ring]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        dsimp [r]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
        congr 2
        ring
  have hterm0 : ∀ l : ℕ, 0 ≤ Ch02.geometricWeight t q l * (M l) ^ (q / 2) := by
    intro l
    exact mul_nonneg (mul_nonneg hD0 (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg (hM0 l) _)
  have hsum : Summable (fun l : ℕ => Ch02.geometricWeight t q l * (M l) ^ (q / 2)) :=
    Summable.of_nonneg_of_le hterm0 hterm hmajor
  have hsumle := Summable.tsum_le_tsum hterm hsum hmajor
  have hmajor_eq : (∑' l : ℕ, D * A ^ (q / 2) * r ^ l) =
      (D / (1 - r)) * A ^ (q / 2) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    ring
  rw [hmajor_eq] at hsumle
  have hratio : D / (1 - r) ≤ t / (t - s) := geometricDiscount_ratio_le hs hst hq
  have hfull := hsumle.trans (mul_le_mul_of_nonneg_right hratio
    (Real.rpow_nonneg hA _))
  calc
    (∑' l : ℕ, Ch02.geometricWeight t q l * (M l) ^ (q / 2)) ^ (2 / q) ≤
        ((t / (t - s)) * A ^ (q / 2)) ^ (2 / q) :=
      Real.rpow_le_rpow (tsum_nonneg hterm0) hfull (by positivity)
    _ = (t / (t - s)) ^ (2 / q) * A := by
      rw [Real.mul_rpow (div_nonneg ht.le hdiff.le) (Real.rpow_nonneg hA _),
        ← Real.rpow_mul hA]
      rw [show q / 2 * (2 / q) = 1 by field_simp]
      rw [Real.rpow_one]

end SubdiffusiveProcess.LambdaStability
