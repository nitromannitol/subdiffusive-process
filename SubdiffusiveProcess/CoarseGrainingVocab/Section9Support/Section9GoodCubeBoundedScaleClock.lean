module

public import SubdiffusiveProcess.Frozen.Section5.HomogenizedCoefficientReciprocalLower
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeClockComparison
@[expose] public section

/-! Uniform clock comparisons over a fixed reference depth, with the disorder threshold chosen before the model. -/

set_option autoImplicit false
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The annealed coefficient stays above one half throughout a fixed bounded cutoff range. -/
theorem goodCube_boundedScale_ahom_ge_half {d : ℕ} (M : GMCModel d) (n J : ℕ)
    (hn : n ≤ J) (hsmall : 2 * M.delta^2 * ((J : ℝ) + 1) ≤ Real.log 2) :
    (1 / 2 : ℝ) ≤ ahom M n := by
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htau : tauSq M.P ≤ M.delta^2 :=
    (tauSq_le_delta_sq M).trans (by
      have hlog : Real.log 2 / 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hlog (sq_nonneg M.delta))
  have hnj : (n : ℝ) + 1 ≤ (J : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hn 1
  have hprod : ((n : ℝ) + 1) * tauSq M.P ≤ Real.log 2 := by
    have hle := mul_le_mul htau hnj (by positivity : 0 ≤ (n : ℝ) + 1)
      (sq_nonneg M.delta)
    have hnn : 0 ≤ M.delta^2 * ((J : ℝ) + 1) := by positivity
    nlinarith only [hle, hnn, hsmall]
  calc
    (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    _ ≤ Real.exp (-((n : ℝ) + 1) * tauSq M.P) :=
      Real.exp_le_exp.mpr (by linarith only [hprod])
    _ ≤ ahom M n := SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M n

/-- A disorder threshold chosen before the model pays every clock comparison up to the fixed depth. -/
theorem exists_goodCube_depth_clock_threshold (J : ℕ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ c →
        2 * delta^2 * ((J : ℝ) + 1) ≤ Real.log 2 := by
  have hJ : 0 < (J : ℝ) + 1 := by positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c : ℝ := min (1 / 2) (Real.sqrt (Real.log 2 / (2 * ((J : ℝ) + 1))))
  have hc : 0 < c := lt_min (by norm_num)
    (Real.sqrt_pos.2 (div_pos hlog (by positivity)))
  refine ⟨c, hc, min_le_left _ _, ?_⟩
  intro delta hd hdc
  have hds : delta ≤ Real.sqrt (Real.log 2 / (2 * ((J : ℝ) + 1))) :=
    hdc.trans (min_le_right _ _)
  have hs : delta^2 ≤ Real.log 2 / (2 * ((J : ℝ) + 1)) := by
    nlinarith only [Real.sq_sqrt (div_pos hlog (show 0 < 2 * ((J : ℝ) + 1) by positivity)).le,
      mul_nonneg (sub_nonneg.2 hds)
        (add_nonneg (Real.sqrt_nonneg (Real.log 2 / (2 * ((J : ℝ) + 1)))) hd.le)]
  have hmul := (le_div_iff₀ (show 0 < 2 * ((J : ℝ) + 1) by positivity)).mp hs
  nlinarith only [hmul]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
