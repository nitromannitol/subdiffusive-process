import Mathlib

open Filter MeasureTheory Topology
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Multiplication by the diffusive clock leaves the strict-decay geometric rate. -/
theorem nonbrownian_weighted_exit_bound (C eta : ℝ) (k : ℕ) :
    (3 : ℝ≥0∞) ^ (2*k) * ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ)))) =
      ENNReal.ofReal C * (ENNReal.ofReal ((3 : ℝ)^(-eta)))^k := by
  have hpow : (3 : ℝ≥0∞)^(2*k) = ENNReal.ofReal ((3 : ℝ)^(2*k)) := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [hpow, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _),
    ← ENNReal.ofReal_mul' (p := C) (q := ((3 : ℝ)^(-eta))^k) (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  push_cast
  calc
    _ = C * ((3 : ℝ)^(2*(k : ℝ)) * (3 : ℝ)^(-((2+eta)*(k : ℝ)))) := by ring
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 2
      ring

/-- A literal mean exit bound with positive eta makes the diffusive weighted
exit integrals summable, without any moment-order change or endpoint deletion. -/
theorem nonbrownian_weighted_exit_tsum_ne_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : ℕ → Ω → ℝ≥0∞) (hs : ∀ k, Measurable (s k))
    (C eta : ℝ) (heta : 0 < eta)
    (hbound : ∀ k, (∫⁻ w, s k w ∂P) ≤
      ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ))))) :
    (∑' k, ∫⁻ w, (3 : ℝ≥0∞)^(2*k) * s k w ∂P) ≠ ⊤ := by
  have hr : (3 : ℝ)^(-eta) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos heta)
  have hr0 : 0 ≤ (3 : ℝ)^(-eta) := Real.rpow_nonneg (by norm_num) _
  have hsum : Summable (fun k : ℕ => C * ((3 : ℝ)^(-eta))^k) :=
    (summable_geometric_of_lt_one hr0 hr).mul_left C
  have hupper : (∑' k, ENNReal.ofReal C * (ENNReal.ofReal ((3 : ℝ)^(-eta)))^k) ≠ ⊤ := by
    simp_rw [← ENNReal.ofReal_pow hr0]
    simp_rw [← ENNReal.ofReal_mul' (p := C) (q := ((3 : ℝ)^(-eta))^_) (pow_nonneg hr0 _)]
    exact hsum.tsum_ofReal_ne_top
  apply ne_top_of_le_ne_top hupper
  apply ENNReal.tsum_le_tsum
  intro k
  rw [lintegral_const_mul _ (hs k)]
  calc
    _ ≤ (3 : ℝ≥0∞)^(2*k) *
        ENNReal.ofReal (C * (3 : ℝ)^(-((2+eta)*(k : ℝ)))) :=
      mul_le_mul_right (hbound k) _
    _ = _ := nonbrownian_weighted_exit_bound C eta k

end SubdiffusiveProcess.Section10
