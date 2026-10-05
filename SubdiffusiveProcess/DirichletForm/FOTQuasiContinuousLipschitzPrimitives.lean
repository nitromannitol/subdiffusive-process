module

public import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousC1
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ContDiff NNReal Interval

noncomputable section
namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

/-- C¹ primitives whose derivatives equal one on a closed null set,
while the primitives themselves tend to zero. -/
theorem lipschitz_null_primitives {K : Set ℝ} (hK : IsClosed K)
    (hKne : K.Nonempty) (hK0 : volume K = 0) :
    ∃ T : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ 1 (T n)) ∧ (∀ n, LipschitzWith 1 (T n)) ∧
      (∀ n, T n 0 = 0) ∧ (∀ n s, deriv (T n) s ∈ Icc 0 1) ∧
      (∀ n s, s ∈ K → deriv (T n) s = 1) ∧
      (∀ s, Tendsto (fun n => T n s) atTop (𝓝 0)) := by
  let χ : ℕ → ℝ → ℝ := fun n s => max 0 (1 - ((n : ℝ) + 1) * Metric.infDist s K)
  have hχcont : ∀ n, Continuous (χ n) := fun n =>
    continuous_const.max (continuous_const.sub
      (continuous_const.mul (Metric.continuous_infDist_pt K)))
  have hχ01 : ∀ n s, χ n s ∈ Icc 0 1 := by
    intro n s
    refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
    have hp : 0 ≤ ((n : ℝ) + 1) * Metric.infDist s K :=
      mul_nonneg (by positivity) Metric.infDist_nonneg
    linarith
  have hχK : ∀ n s, s ∈ K → χ n s = 1 := by
    intro n s hs
    simp only [χ, Metric.infDist_zero_of_mem hs, mul_zero, sub_zero, max_eq_right zero_le_one]
  have hχlim : ∀ᵐ s : ℝ, Tendsto (fun n => χ n s) atTop (𝓝 0) := by
    have hnot : ∀ᵐ s : ℝ, s ∉ K := by
      rw [ae_iff]
      simpa only [not_not, mem_ofPred_eq, ofPred_mem_eq] using! hK0
    filter_upwards [hnot] with s hs
    have hdist : 0 < Metric.infDist s K := (hK.notMem_iff_infDist_pos hKne).mp hs
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / Metric.infDist s K)
    have hzero : ∀ᶠ n : ℕ in atTop, χ n s = 0 := by
      filter_upwards [eventually_ge_atTop N] with n hn
      apply max_eq_left
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hm : 1 < (N : ℝ) * Metric.infDist s K := (div_lt_iff₀ hdist).mp hN
      have hmul := mul_le_mul_of_nonneg_right hn' hdist.le
      nlinarith
    exact tendsto_const_nhds.congr' (hzero.mono fun n hn => hn.symm)
  let T : ℕ → ℝ → ℝ := fun n s => ∫ t in (0 : ℝ)..s, χ n t
  have hderiv : ∀ n s, HasDerivAt (T n) (χ n s) s :=
    fun n s => (hχcont n).integral_hasStrictDerivAt 0 s |>.hasDerivAt
  have hderiv_eq : ∀ n, deriv (T n) = χ n := fun n => funext fun s => (hderiv n s).deriv
  have hdiff : ∀ n, Differentiable ℝ (T n) := fun n s => (hderiv n s).differentiableAt
  refine ⟨T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [contDiff_one_iff_deriv, hderiv_eq]
    exact ⟨hdiff n, hχcont n⟩
  · intro n
    apply lipschitzWith_of_nnnorm_deriv_le (hdiff n)
    intro s
    rw [← NNReal.coe_le_coe, coe_nnnorm, hderiv_eq n, NNReal.coe_one,
      Real.norm_eq_abs, abs_of_nonneg (hχ01 n s).1]
    exact (hχ01 n s).2
  · intro n
    exact intervalIntegral.integral_same
  · intro n s
    rw [hderiv_eq n]
    exact hχ01 n s
  · intro n s hs
    rw [hderiv_eq n]
    exact hχK n s hs
  · intro s
    let : IsFiniteMeasure (volume.restrict (Ι (0 : ℝ) s)) := ⟨by
      rw [Measure.restrict_apply_univ, uIoc, Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top⟩
    have hlim : Tendsto (fun n => ∫ t in Ι (0 : ℝ) s, χ n t) atTop (𝓝 0) := by
      have hi : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ι (0 : ℝ) s)) :=
        integrable_const 1
      simpa only [integral_zero] using
        (tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1 : ℝ))
          (fun n => (hχcont n).measurable.aestronglyMeasurable) hi
          (fun n => Eventually.of_forall fun t => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hχ01 n t).1]
            exact (hχ01 n t).2)
          (ae_restrict_of_ae hχlim))
    by_cases hs : (0 : ℝ) ≤ s
    · simpa only [T, intervalIntegral.integral_of_le hs, uIoc_of_le hs] using hlim
    · have hs' : s ≤ (0 : ℝ) := le_of_not_ge hs
      simpa only [T, intervalIntegral.integral_of_ge hs', uIoc_of_ge hs', neg_zero]
        using hlim.neg

end SubdiffusiveProcess.DirichletForm.FOTConstruction
