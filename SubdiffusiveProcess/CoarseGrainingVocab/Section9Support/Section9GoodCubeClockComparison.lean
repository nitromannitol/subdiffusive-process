module

public import SubdiffusiveProcess.Frozen.Section3.AnnealedMatrixBounds
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum
public import Mathlib.Analysis.Complex.ExponentialBounds
@[expose] public section

/-!
# Annealed clocks over a bounded range of scales

The Section 3 annealed comparison gives a factor two once the disorder
pays for the fixed descendant depth.
-/

set_option autoImplicit false
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The annealed clock changes by at most a factor two over a fixed depth
when the disorder pays for that depth. -/
theorem goodCube_ahom_scale_comparison
    {d : ℕ} (M : GMCModel d) (n m J : ℕ)
    (hmn : m ≤ n) (hdepth : n - m ≤ J)
    (hsmall : 2 * M.delta ^ 2 * (J : ℝ) ≤ Real.log 2) :
    ahom M m ≤ 2 * ahom M n := by
  rcases eq_or_lt_of_le hmn with heq | hlt
  · subst m
    have hpos := ahom_pos M n
    linarith only [hpos]
  · have htau : tauSq M.P ≤ M.delta ^ 2 :=
      (tauSq_le_delta_sq M).trans (by
        have hlog : Real.log 2 / 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hlog (sq_nonneg M.delta))
    have hdepthReal : ((n - m : ℕ) : ℝ) ≤ (J : ℝ) := by exact_mod_cast hdepth
    have hexp : 2 * tauSq M.P * ((n - m : ℕ) : ℝ) ≤ Real.log 2 :=
      (mul_le_mul (mul_le_mul_of_nonneg_left htau (by norm_num)) hdepthReal
        (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (sq_nonneg _))).trans hsmall
    have hfactor : Real.exp (2 * tauSq M.P * ((n - m : ℕ) : ℝ)) ≤ 2 :=
      (Real.exp_le_exp.mpr hexp).trans_eq (Real.exp_log (by norm_num))
    exact (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds.2 M n m hlt).2.trans
      (mul_le_mul_of_nonneg_right hfactor (ahom_pos M n).le)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
