import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Strict scalar margins for transferring original primitive-score prefixes.
The estimates control the error per level and the number of buffered levels;
they do not supply any random-variable comparison.
-/
open Filter Set
open scoped BigOperators Topology
namespace SubdiffusiveProcess

/-- An arbitrarily small positive response tolerance fits both the ramp and clipped-square-root margins. -/
theorem exists_score_comparison_tolerance (eps loss : ℝ) (hloss : 0 < loss) :
    ∃ tol : ℝ, 0 < tol ∧ tol ≤ 1 ∧
      (2 * tol) * (1 + eps ^ 2) / (eps ^ 2 - eps ^ 2 / 4) < loss ∧
      Real.sqrt (2 * tol) + 2 * tol < loss := by
  have hZ : Continuous (fun t : ℝ => (2 * t) * (1 + eps ^ 2) / (eps ^ 2 - eps ^ 2 / 4)) := by
    fun_prop
  have hD : Continuous (fun t : ℝ => Real.sqrt (2 * t) + 2 * t) := by fun_prop
  have hZlim : Tendsto (fun t : ℝ => (2 * t) * (1 + eps ^ 2) / (eps ^ 2 - eps ^ 2 / 4))
      (𝓝 0) (𝓝 0) := by simpa only [mul_zero, zero_mul, zero_div] using hZ.tendsto 0
  have hDlim : Tendsto (fun t : ℝ => Real.sqrt (2 * t) + 2 * t) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero, Real.sqrt_zero, add_zero] using hD.tendsto 0
  obtain ⟨r, hr, hbound⟩ := Metric.eventually_nhds_iff.mp
    ((hZlim.eventually (gt_mem_nhds hloss)).and (hDlim.eventually (gt_mem_nhds hloss)))
  let tol : ℝ := min (1 / 2) (r / 2)
  have htol : 0 < tol := lt_min (by norm_num) (by positivity)
  have htolr : tol < r := (min_le_right _ _).trans_lt (by linarith only [hr])
  have hd : dist tol 0 < r := by simpa only [Real.dist_eq, sub_zero, abs_of_pos htol] using htolr
  exact ⟨tol, htol, (min_le_left _ _).trans (by norm_num), (hbound hd).1, (hbound hd).2⟩

/-- A buffered prefix has at most twice buffer-plus-one times its positive length many levels. -/
theorem buffered_prefix_card_le (buffer D : ℕ) (hD : 1 ≤ D) :
    ((Finset.Icc (-(buffer : ℤ)) ((D : ℤ) + buffer)).card : ℝ) ≤
      (2 * ((buffer : ℝ) + 1)) * D := by
  have heq : (Finset.Icc (-(buffer : ℤ)) ((D : ℤ) + buffer)).card = D + 2 * buffer + 1 := by
    rw [Int.card_Icc]
    omega
  rw [heq]
  push_cast
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hb : 0 ≤ (buffer : ℝ) := Nat.cast_nonneg buffer
  nlinarith only [hd, hb, mul_nonneg hb (sub_nonneg.mpr hd)]

/-- A half-threshold limiting prefix absorbs a sufficiently small error at every buffered level. -/
theorem buffered_prefix_le_of_comparison (buffer D : ℕ) (hD : 1 ≤ D)
    (V W : ℤ → ℝ) (lam loss : ℝ) (hloss : 0 ≤ loss)
    (hmargin : 2 * ((buffer : ℝ) + 1) * loss ≤ lam / 2)
    (hpoint : ∀ j ∈ Finset.Icc (-(buffer : ℤ)) ((D : ℤ) + buffer), V j ≤ W j + loss)
    (hlimit : (∑ j ∈ Finset.Icc (-(buffer : ℤ)) ((D : ℤ) + buffer), W j) ≤ lam * D / 2) :
    (∑ j ∈ Finset.Icc (-(buffer : ℤ)) ((D : ℤ) + buffer), V j) ≤ lam * D := by
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard := mul_le_mul_of_nonneg_right (buffered_prefix_card_le buffer D hD) hloss
  have hrate := mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg (α := ℝ) D)
  nlinarith only [hsum, hcard, hrate, hlimit]

end SubdiffusiveProcess
