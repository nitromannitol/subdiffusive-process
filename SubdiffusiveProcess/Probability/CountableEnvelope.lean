module

public import SubdiffusiveProcess.Probability.AbsoluteSeries
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace SubdiffusiveProcess

/-- Summable Lp norms give a single actual Lp random envelope simultaneously dominating the countable family almost everywhere. -/
theorem exists_memLp_dominating_of_summable_eLpNorm
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (_hpt : p ≠ ∞)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, MemLp (F n) p μ)
    (hs : Summable (fun n => (eLpNorm (F n) p μ).toReal)) :
    ∃ W : Ω → ℝ, MemLp W p μ ∧
      (∀ᵐ ω ∂μ, 0 ≤ W ω ∧ ∀ n : ℕ, |F n ω| ≤ W ω) ∧
      eLpNorm W p μ ≤ ∑' n : ℕ, eLpNorm (F n) p μ := by
  let W : Ω → ℝ := fun ω => ∑' n, ‖F n ω‖
  have hInt : ∀ n, Integrable (F n) μ := fun n => (hF n).integrable hp
  have hInt_le : ∀ n, ∫ ω, ‖F n ω‖ ∂μ ≤ (eLpNorm (F n) p μ).toReal := by
    intro n
    calc
      ∫ ω, ‖F n ω‖ ∂μ = (eLpNorm (F n) 1 μ).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm (hF n).aestronglyMeasurable, integral_norm_eq_lintegral_enorm (hF n).aestronglyMeasurable]
      _ ≤ (eLpNorm (F n) p μ).toReal := ENNReal.toReal_mono (hF n).ne
        (eLpNorm_le_eLpNorm_of_exponent_le hp)
  have hsInt : Summable (fun n => ∫ ω, ‖F n ω‖ ∂μ) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun ω => norm_nonneg (F n ω))) hInt_le hs
  have hPoint : ∀ᵐ ω ∂μ, Summable (fun n => ‖F n ω‖) :=
    ae_summable_norm_of_summable_integral_norm hInt hsInt
  let S : ℕ → Ω → ℝ := fun n => ∑ i ∈ Finset.range n, fun ω => ‖F i ω‖
  have hBound : ∀ n, eLpNorm (S n) p μ ≤
      ∑' i, eLpNorm (F i) p μ := by
    intro n
    calc
      eLpNorm (S n) p μ ≤
          ∑ i ∈ Finset.range n, eLpNorm (fun ω => ‖F i ω‖) p μ :=
        eLpNorm_sum_le hp
      _ = ∑ i ∈ Finset.range n, eLpNorm (F i) p μ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact eLpNorm_norm (p := p) (F i) (hF i).aestronglyMeasurable
      _ ≤ ∑' i, eLpNorm (F i) p μ := ENNReal.sum_le_tsum _
  have hTendsto : ∀ᵐ ω ∂μ,
      Tendsto (fun n => S n ω) atTop (𝓝 (W ω)) := by
    filter_upwards [hPoint] with ω hω
    simpa only [S, Finset.sum_apply] using hω.hasSum.tendsto_sum_nat
  have hWmeas : AEStronglyMeasurable W μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (memLp_finsetSum' (Finset.range n) fun i hi => (hF i).norm).aestronglyMeasurable) hTendsto
  have hWnorm : eLpNorm W p μ ≤ ∑' i, eLpNorm (F i) p μ :=
    Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hBound)
      (fun n => (memLp_finsetSum' (Finset.range n) fun i hi => (hF i).norm).aestronglyMeasurable) hWmeas hTendsto
  have hsum_norms : (∑' i, eLpNorm (F i) p μ) ≠ ∞ := by
    have heq : (fun i => eLpNorm (F i) p μ) =
        fun i => ENNReal.ofReal (eLpNorm (F i) p μ).toReal := by
      funext n
      exact (ENNReal.ofReal_toReal (hF n).ne).symm
    rw [heq, ← ENNReal.ofReal_tsum_of_nonneg (fun n => ENNReal.toReal_nonneg) hs]
    exact ENNReal.ofReal_ne_top
  have hW : MemLp W p μ :=
    hWnorm.trans_lt (lt_top_iff_ne_top.2 hsum_norms)
  refine ⟨W, hW, ?_, hWnorm⟩
  filter_upwards [hPoint] with ω hω
  constructor
  · exact tsum_nonneg fun n => norm_nonneg _
  · intro n
    simpa only [W, Real.norm_eq_abs] using
      hω.le_tsum n (fun j hj => norm_nonneg (F j ω))

end SubdiffusiveProcess
