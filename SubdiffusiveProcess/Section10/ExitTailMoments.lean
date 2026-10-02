import SubdiffusiveProcess.Probability.ExponentialTailMoment
import MarkovProcess.Kernel.KernelSemigroup
import Mathlib

/-! Uniform mean exits give killed-semigroup geometric survival. The law/row
identification is explicit and is discharged for the physical path consumer. -/
open Filter MeasureTheory ProbabilityTheory MarkovProcess Set Topology
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.ExitTailMoments

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

/-- Actual Chapman–Kolmogorov induction, with no restart oracle. -/
lemma row_mass_nsmul_le (S : SubMarkovKernelSemigroup α) (T : ℝ≥0)
    (q : ℝ≥0∞) (hstep : ∀ x, S T x univ ≤ q) (n : ℕ) (x : α) :
    S (n • T) x univ ≤ q ^ n := by
  induction n generalizing x with
  | zero => simpa only [zero_nsmul, pow_zero] using S.measure_univ_le_one 0 x
  | succ n ih =>
    rw [succ_nsmul, S.add_apply' (n • T) T x MeasurableSet.univ]
    calc (∫⁻ y, S T y univ ∂S (n • T) x)
        ≤ ∫⁻ _, q ∂S (n • T) x := lintegral_mono hstep
      _ = q * S (n • T) x univ := lintegral_const q
      _ ≤ q * q ^ n := mul_le_mul_right (ih x) q
      _ = q ^ (n + 1) := by rw [pow_succ, mul_comm]

/-- The initial half-probability is derived solely from the mean estimate. -/
lemma survival_two_mean_le_half (law : Kernel α Ω) (tau : Ω → ℝ≥0∞)
    (htau : Measurable tau) (K : ℝ≥0) (hK : 0 < K)
    (hmean : ∀ x, (∫⁻ w, tau w ∂law x) ≤ (K : ℝ≥0∞)) (x : α) :
    law x {w | ((2 * K : ℝ≥0) : ℝ≥0∞) < tau w} ≤ (1 / 2 : ℝ≥0∞) := by
  have hbound := mul_meas_ge_le_lintegral₀ (μ := law x) htau.aemeasurable
    ((2 * K : ℝ≥0) : ℝ≥0∞)
  have hcalc : ((2 * K : ℝ≥0) : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) = K := by
    rw [ENNReal.coe_mul, ENNReal.coe_ofNat]
    rw [mul_comm (2 : ℝ≥0∞), mul_assoc, one_div,
      ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) ENNReal.ofNat_ne_top, mul_one]
  have hle : ((2 * K : ℝ≥0) : ℝ≥0∞) *
      law x {w | ((2 * K : ℝ≥0) : ℝ≥0∞) ≤ tau w} ≤
      ((2 * K : ℝ≥0) : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) := by
    rw [hcalc]
    exact hbound.trans (hmean x)
  have hcancel := (ENNReal.mul_le_mul_iff_right
    (ENNReal.coe_ne_zero.mpr (mul_pos (by norm_num) hK).ne') ENNReal.coe_ne_top).mp hle
  exact (measure_mono (fun w (h : ((2 * K : ℝ≥0) : ℝ≥0∞) < tau w) => h.le)).trans hcancel

/-- Generic semigroup supplier. Row mass is identified with survival at every
positive deterministic time, rather than assumed to satisfy a restart bound. -/
theorem geometric_survival_of_mean (S : SubMarkovKernelSemigroup α)
    (law : Kernel α Ω) [IsMarkovKernel law] (tau : Ω → ℝ≥0∞)
    (htau : Measurable tau) (K : ℝ≥0) (hK : 1 ≤ K)
    (hrow : ∀ t : ℝ≥0, 0 < t → ∀ x,
      S t x univ = law x {w | (t : ℝ≥0∞) < tau w})
    (hmean : ∀ x, (∫⁻ w, tau w ∂law x) ≤ (K : ℝ≥0∞))
    (n : ℕ) (x : α) :
    law x {w | ((n • (2 * K) : ℝ≥0) : ℝ≥0∞) < tau w} ≤
      (1 / 2 : ℝ≥0∞) ^ n := by
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hstep : ∀ y, S (2 * K) y univ ≤ (1 / 2 : ℝ≥0∞) := by
    intro y
    rw [hrow (2 * K) (mul_pos (by norm_num) hK0)]
    exact survival_two_mean_le_half law tau htau K hK0 hmean y
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero]
    exact prob_le_one
  · have hpos : 0 < n • (2 * K) := by
      rw [nsmul_eq_mul]
      exact mul_pos (by exact_mod_cast hn) (mul_pos (by norm_num) hK0)
    rw [← hrow (n • (2 * K)) hpos]
    exact row_mass_nsmul_le S (2 * K) (1 / 2) hstep n x

end SubdiffusiveProcess.Section10.ExitTailMoments
