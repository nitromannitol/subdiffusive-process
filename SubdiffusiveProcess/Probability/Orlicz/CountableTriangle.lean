module

public import Mathlib
public import SubdiffusiveProcess.Probability.Orlicz.FiniteTriangle

@[expose] public section

/-! Countable exact-scale Orlicz summation, including almost-sure convergence. -/
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess.Probability.Orlicz
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma ae_summable_of_ogammaLE {σ : ℝ} (hσ : 1 ≤ σ) {X : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (hX0 : ∀ k ω, 0 ≤ X k ω) (ha : ∀ k, 0 < a k) (hasum : Summable a)
    (hm : ∀ k, AEMeasurable (X k) μ) (hX : ∀ k, SubdiffusiveProcess.OGammaLE μ σ (a k) (X k)) :
    ∀ᵐ ω ∂μ, Summable fun k => X k ω := by
  have hi := fun k => SubdiffusiveProcess.CoarseGrainingVocab.OGamma.integral_le_of_ogammaLE_nonneg
    (hX k) (ha k) hσ (hm k) (hX0 k)
  have hL : ∫⁻ ω, ∑' k, ENNReal.ofReal (X k ω) ∂μ ≤ ENNReal.ofReal (∑' k, 2 * a k) := by
    rw [lintegral_tsum (fun k => (hm k).ennreal_ofReal)]
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (by norm_num) (ha k).le) (hasum.mul_left 2)]
    apply ENNReal.tsum_le_tsum
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hi k).1 (Filter.Eventually.of_forall (hX0 k))]
    exact ENNReal.ofReal_le_ofReal (hi k).2
  have hfinite := ae_lt_top' (AEMeasurable.ennreal_tsum (fun k => (hm k).ennreal_ofReal))
    (ne_of_lt (hL.trans_lt ENNReal.ofReal_lt_top))
  filter_upwards [hfinite] with ω hω
  have hsum : Summable fun k => ((X k ω).toNNReal : ℝ) :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hω.ne
  simpa only [Real.coe_toNNReal', max_eq_left (hX0 _ ω)] using hsum

lemma ogammaLE_tsum {σ : ℝ} (hσ : 1 ≤ σ) {X : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (hX0 : ∀ k ω, 0 ≤ X k ω) (ha : ∀ k, 0 < a k) (hasum : Summable a)
    (hm : ∀ k, AEMeasurable (X k) μ) (hX : ∀ k, SubdiffusiveProcess.OGammaLE μ σ (a k) (X k)) :
    (∀ᵐ ω ∂μ, Summable fun k => X k ω) ∧
      SubdiffusiveProcess.OGammaLE μ σ (∑' k, a k) (fun ω => ∑' k, X k ω) := by
  have hsum := ae_summable_of_ogammaLE hσ hX0 ha hasum hm hX
  refine ⟨hsum, ?_⟩
  let A : ℝ := ∑' k, a k
  let S : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, X k ω
  let T : Ω → ℝ := fun ω => ∑' k, X k ω
  have hA : 0 < A := (ha 0).trans_le (hasum.le_tsum 0 (fun k _ => (ha k).le))
  have hSm : ∀ n, AEMeasurable (S n) μ := by
    intro n
    convert Finset.aemeasurable_sum (Finset.range n) (fun k _ => hm k) using 1
    ext ω
    simp only [S, Finset.sum_apply]
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => S n ω) atTop (𝓝 (T ω)) := by
    filter_upwards [hsum] with ω hω
    exact hω.hasSum.tendsto_sum_nat
  have hTm : AEMeasurable T μ := aemeasurable_of_tendsto_metrizable_ae' hSm hlim
  have hO : ∀ n, SubdiffusiveProcess.OGammaLE μ σ A (S n) := by
    intro n
    cases n with
    | zero =>
      simpa only [S, Finset.range_zero, Finset.sum_empty] using
        SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_zero (mu := μ) σ A (by linarith : σ ≠ 0)
    | succ n =>
      have hne : (Finset.range (n + 1)).Nonempty := Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)
      have hpos := Finset.sum_pos (fun k (_ : k ∈ Finset.range (n + 1)) => ha k) hne
      have hf := ogammaLE_finset_sum hσ (Finset.range (n + 1)) hne
        (fun k _ => ha k) (fun k _ => hm k) (fun k _ => hX k)
      exact SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_mono_scale hpos
        (hasum.sum_le_tsum _ (fun k _ => (ha k).le)) (by linarith) (hSm _) hf
  let F : ℕ → Ω → ENNReal := fun n ω => ENNReal.ofReal
    (SubdiffusiveProcess.CoarseGrainingVocab.OGamma.integrand σ A (S n) ω)
  let G : Ω → ENNReal := fun ω => ENNReal.ofReal
    (SubdiffusiveProcess.CoarseGrainingVocab.OGamma.integrand σ A T ω)
  have hFm : ∀ n, AEMeasurable (F n) μ := fun n =>
    (SubdiffusiveProcess.CoarseGrainingVocab.OGamma.aemeasurable_integrand σ A (hSm n)).ennreal_ofReal
  have hmono : ∀ᵐ ω ∂μ, Monotone fun n => F n ω := by
    filter_upwards with ω
    intro n m hnm
    apply ENNReal.ofReal_le_ofReal
    exact SubdiffusiveProcess.CoarseGrainingVocab.OGamma.integrand_mono hA (by linarith)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hnm)
        (fun k _ _ => hX0 k ω))
  have hcont : Continuous (fun x : ℝ => ENNReal.ofReal (Real.exp ((A⁻¹ * max x 0) ^ σ))) := by
    apply ENNReal.continuous_ofReal.comp
    apply Real.continuous_exp.comp
    exact (Real.continuous_rpow_const (by linarith)).comp
      (continuous_const.mul (continuous_id.max continuous_const))
  have hFlim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (G ω)) := by
    filter_upwards [hlim] with ω hω
    exact hcont.continuousAt.tendsto.comp hω
  have hconv := lintegral_tendsto_of_tendsto_of_monotone hFm hmono hFlim
  have hbound : ∀ n, ∫⁻ ω, F n ω ∂μ ≤ ENNReal.ofReal 2 := by
    intro n
    change ∫⁻ ω, ENNReal.ofReal (Real.exp ((A⁻¹ * max (S n ω) 0) ^ σ)) ∂μ ≤ ENNReal.ofReal 2
    rw [← ofReal_integral_eq_lintegral_ofReal (hO n).1
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (hO n).2
  have hG : ∫⁻ ω, G ω ∂μ ≤ ENNReal.ofReal 2 := le_of_tendsto' hconv hbound
  have hi : Integrable (SubdiffusiveProcess.CoarseGrainingVocab.OGamma.integrand σ A T) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (SubdiffusiveProcess.CoarseGrainingVocab.OGamma.aemeasurable_integrand σ A hTm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).mp
    exact ne_of_lt (hG.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hi, ?_⟩
  have hn : 0 ≤ᵐ[μ] SubdiffusiveProcess.CoarseGrainingVocab.OGamma.integrand σ A T :=
    Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le
  change ∫⁻ ω, ENNReal.ofReal (SubdiffusiveProcess.CoarseGrainingVocab.OGamma.integrand σ A T ω) ∂μ ≤ ENNReal.ofReal 2 at hG
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn] at hG
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).mp hG

end SubdiffusiveProcess.Probability.Orlicz
