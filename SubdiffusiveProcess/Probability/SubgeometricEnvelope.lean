import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.Probability.BorelCantelli
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A uniform first-moment bound gives an almost-sure subgeometric envelope for a sequence. -/
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess

/-- Uniform first moments give one pathwise subgeometric majorant for every index. -/
theorem ae_subgeometric_envelope_of_memLp_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : ℕ → Ω → ℝ) (C : ℝ)
    (hmem : ∀ N, MemLp (K N) 1 P)
    (hnorm : ∀ N, eLpNorm (K N) 1 P ≤ ENNReal.ofReal C)
    (xi : ℝ) (hxi : 0 < xi) :
    ∀ᵐ om ∂P, ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, K N om ≤ B * (3 : ℝ) ^ (xi * (N : ℝ)) := by
  set q : ℝ := (3 : ℝ) ^ (-xi) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set s : ℕ → Set Ω :=
    fun N => {om | ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))) ≤ ‖K N om‖ₑ} with hs
  have hpow (N : ℕ) : 0 < (3 : ℝ) ^ (xi * (N : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hqN (N : ℕ) : ((3 : ℝ) ^ (xi * (N : ℝ)))⁻¹ = q ^ N := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
    ring_nf
  have hmeasN (N : ℕ) : P (s N) ≤ ENNReal.ofReal (max C 0 * q ^ N) := by
    have hM := mul_meas_ge_le_lintegral₀ (μ := P) ((hmem N).aestronglyMeasurable.enorm)
      (ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))))
    rw [← eLpNorm_one_eq_lintegral_enorm] at hM
    have hM2 : ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))) * P (s N) ≤
        ENNReal.ofReal (max C 0) :=
      hM.trans ((hnorm N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    have hne0 : ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact hpow N
    have hnetop : ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc P (s N)
        = (ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))))⁻¹ *
            (ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))) * P (s N)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hne0 hnetop, one_mul]
      _ ≤ (ENNReal.ofReal ((3 : ℝ) ^ (xi * (N : ℝ))))⁻¹ * ENNReal.ofReal (max C 0) := by
          gcongr
      _ = ENNReal.ofReal (max C 0 * q ^ N) := by
          rw [← ENNReal.ofReal_inv_of_pos (hpow N),
            ← ENNReal.ofReal_mul (inv_nonneg.2 (hpow N).le), hqN, mul_comm]
  have hsum : ∑' N, P (s N) ≠ ⊤ := by
    have hsumm : Summable (fun N : ℕ => max C 0 * q ^ N) :=
      (summable_geometric_of_lt_one hq0 hq1).mul_left _
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hmeasN)
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun N => mul_nonneg (le_max_right _ _) (pow_nonneg hq0 N)) hsumm]
    exact ENNReal.ofReal_ne_top
  have hae := ae_eventually_notMem (μ := P) hsum
  filter_upwards [hae] with om hom
  rcases eventually_atTop.1 hom with ⟨N0, hN0⟩
  have hS0 : 0 ≤ ∑ N ∈ Finset.range N0, |K N om| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨1 + ∑ N ∈ Finset.range N0, |K N om|, by linarith, ?_⟩
  intro N
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (xi * (N : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hxi.le (Nat.cast_nonneg N))
  by_cases hN : N < N0
  · have hle : |K N om| ≤ ∑ N ∈ Finset.range N0, |K N om| :=
      Finset.single_le_sum (f := fun N => |K N om|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 hN)
    calc K N om ≤ |K N om| := le_abs_self _
      _ ≤ (1 + ∑ N ∈ Finset.range N0, |K N om|) * 1 := by linarith
      _ ≤ (1 + ∑ N ∈ Finset.range N0, |K N om|) * (3 : ℝ) ^ (xi * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
  · have hnot := hN0 N (not_lt.1 hN)
    simp only [hs, Set.mem_setOf_eq, not_le] at hnot
    rw [Real.enorm_eq_ofReal_abs] at hnot
    have hlt := (ENNReal.ofReal_lt_ofReal_iff (hpow N)).1 hnot
    calc K N om ≤ |K N om| := le_abs_self _
      _ ≤ 1 * (3 : ℝ) ^ (xi * (N : ℝ)) := by linarith
      _ ≤ (1 + ∑ N ∈ Finset.range N0, |K N om|) * (3 : ℝ) ^ (xi * (N : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) (hpow N).le


end SubdiffusiveProcess
