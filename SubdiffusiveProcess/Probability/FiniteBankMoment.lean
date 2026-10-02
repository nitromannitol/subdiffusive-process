import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess

/-- The maximum over a finite bank costs only the qth root of its cardinality in Lq. No independence or finite measure assumption is used. -/
theorem eLpNorm_finite_bank_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞)
    (F : Fin k → Ω → ℝ)
    (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (K : ℝ≥0∞) (hK : ∀ i, eLpNorm (F i) q μ ≤ K) :
    eLpNorm (fun ω => ‖fun i : Fin k => F i ω‖) q μ ≤
      (k : ℝ≥0∞) ^ (1 / q.toReal) * K := by
  have hq0 : q ≠ 0 := ne_of_gt (zero_lt_one.trans_le hq)
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  rw [eLpNorm_eq_lintegral_rpow_enorm hq0 hqt]
  calc
    (∫⁻ ω, ‖‖fun i : Fin k => F i ω‖‖ₑ ^ q.toReal ∂μ) ^ (1 / q.toReal)
        ≤ (∫⁻ ω, ∑ i : Fin k, ‖F i ω‖ₑ ^ q.toReal ∂μ) ^ (1 / q.toReal) := by
          gcongr with ω
          by_cases hk : k = 0
          · subst k
            have hempty : (fun i : Fin 0 => F i ω) = 0 := by
              funext i
              exact Fin.elim0 i
            rw [hempty, norm_zero, enorm_zero, ENNReal.zero_rpow_of_pos hqr]
            simp
          · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
            have huniv : (Finset.univ : Finset (Fin k)).Nonempty :=
              ⟨⟨0, hkpos⟩, Finset.mem_univ _⟩
            obtain ⟨i, hi, hsup⟩ :=
              Finset.exists_mem_eq_sup Finset.univ huniv (fun i : Fin k => ‖F i ω‖₊)
            rw [enorm_eq_nnnorm, Real.nnnorm_of_nonneg (norm_nonneg _)]
            change ((↑(Finset.univ.sup fun i : Fin k => ‖F i ω‖₊) : ℝ≥0∞) ^ q.toReal) ≤ _
            rw [hsup]
            exact Finset.single_le_sum
              (fun j _ => show (0 : ℝ≥0∞) ≤ ‖F j ω‖ₑ ^ q.toReal from zero_le _)
              (Finset.mem_univ i)
    _ = (∑ i : Fin k, ∫⁻ ω, ‖F i ω‖ₑ ^ q.toReal ∂μ) ^ (1 / q.toReal) := by
          congr 1
          exact lintegral_finset_sum' Finset.univ fun i hi =>
            (hF i).enorm.pow_const q.toReal
    _ ≤ ((k : ℝ≥0∞) * K ^ q.toReal) ^ (1 / q.toReal) := by
          apply ENNReal.rpow_le_rpow
          · calc
              ∑ i : Fin k, ∫⁻ ω, ‖F i ω‖ₑ ^ q.toReal ∂μ
                  = ∑ i : Fin k, eLpNorm (F i) q μ ^ q.toReal := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      rw [eLpNorm_eq_lintegral_rpow_enorm hq0 hqt,
                        ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hqr.ne',
                        ENNReal.rpow_one]
              _ ≤ ∑ _i : Fin k, K ^ q.toReal := Finset.sum_le_sum fun i hi =>
                    ENNReal.rpow_le_rpow (hK i) hqr.le
              _ = (k : ℝ≥0∞) * K ^ q.toReal := by simp [mul_comm]
          · exact (one_div_pos.mpr hqr).le
    _ = (k : ℝ≥0∞) ^ (1 / q.toReal) * K := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hqr).le,
            ← ENNReal.rpow_mul, one_div, mul_inv_cancel₀ hqr.ne', ENNReal.rpow_one]

end SubdiffusiveProcess
