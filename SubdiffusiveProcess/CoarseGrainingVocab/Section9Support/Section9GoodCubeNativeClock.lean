module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeBoundedScaleClock
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeUniformSobolevClock
@[expose] public section

/-! One scalar comparator pays the intrinsic clock in both the positive-scale and bounded-cutoff regimes, including every negative native scale. -/

set_option autoImplicit false
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
theorem goodCube_native_clock_le_comparison_clock
    {d : ℕ} (M : GMCModel d) (J n : ℕ) (m : ℤ)
    (hmn : m ≤ (n : ℤ))
    (hbudget : 2 * M.delta^2 * ((J : ℝ) + 1) ≤ Real.log 2) :
    let sigma : ℝ := if J ≤ n then ahom M n else 1
    0 < sigma ∧ Section7Process.timeScale (ahom M) ((3 : ℝ)^m) ≤
      2 * ((3 : ℝ)^m)^2 / sigma
:= by
  have hmN : m.toNat ≤ n := by omega
  dsimp only
  split_ifs with hJn
  · refine ⟨ahom_pos M n, ?_⟩
    rw [goodCube_timeScale_triadic_int]
    have hmono : ahom M n ≤ ahom M m.toNat := by
      rcases eq_or_lt_of_le hmN with heq | hlt
      · rw [heq]
      · exact (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds.2 M n m.toNat hlt).1
    calc ((3 : ℝ)^m)^2 / ahom M m.toNat
        ≤ ((3 : ℝ)^m)^2 / ahom M n :=
          div_le_div_of_nonneg_left (sq_nonneg _) (ahom_pos M n) hmono
      _ ≤ 2 * ((3 : ℝ)^m)^2 / ahom M n := by
          apply div_le_div_of_nonneg_right _ (ahom_pos M n).le
          nlinarith only [sq_nonneg ((3 : ℝ)^m)]
  · refine ⟨by norm_num, ?_⟩
    rw [goodCube_timeScale_triadic_int, div_one]
    have hmJ : m.toNat ≤ J := by omega
    have ha := goodCube_boundedScale_ahom_ge_half M m.toNat J hmJ hbudget
    apply (div_le_iff₀ (ahom_pos M m.toNat)).2
    have hmul := mul_le_mul_of_nonneg_left ha (sq_nonneg ((3 : ℝ)^m))
    nlinarith only [hmul]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
