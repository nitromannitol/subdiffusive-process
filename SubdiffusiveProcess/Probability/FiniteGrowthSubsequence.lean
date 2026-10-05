module

public import SubdiffusiveProcess.Probability.GrowthSubsequence

@[expose] public section

/-! Simultaneous pathwise bounds for a finite family of random sequences.
Uniform moment bounds give a common further subsequence, with no assertion that
the subsequence is measurable or that the original sequences are bounded. -/

open Filter MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess

/-- The sum of the norms of finitely many random variables has the sum moment bound. -/
theorem eLpNorm_sum_norm_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (p : ℝ≥0) (hp : 1 ≤ p)
    (f : ι → Ω → ℝ) (C : ι → ℝ≥0)
    (hf : ∀ i, Measurable (f i)) (hb : ∀ i, eLpNorm (f i) p P ≤ C i) :
    eLpNorm (fun om => ∑ i, ‖f i om‖) p P ≤ (∑ i, C i : ℝ≥0) := by
  have hs := eLpNorm_sum_le (μ := P) (p := (p : ℝ≥0∞))
    (s := Finset.univ) (f := fun i om => ‖f i om‖)
    (by exact_mod_cast hp)
  have hnorm (i : ι) : eLpNorm (fun om => ‖f i om‖) p P = eLpNorm (f i) p P :=
    eLpNorm_norm _ (hf i).aestronglyMeasurable
  simp only [hnorm] at hs
  rw [show (∑ i, fun om => ‖f i om‖) = (fun om => ∑ i, ‖f i om‖) by
    funext om; exact Finset.sum_apply om Finset.univ (fun i om => ‖f i om‖)] at hs
  refine hs.trans ?_
  rw [ENNReal.ofNNReal_finsetSum]
  exact Finset.sum_le_sum fun i _ => hb i

/-- Finite families with uniform moments share a bounded samplewise further subsequence. -/
theorem exists_common_bounded_subsequence_of_eLpNorm_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ι → ℕ → Ω → ℝ) (p eps : ℝ≥0) (C : ι → ℝ≥0)
    (hp : 1 ≤ p) (heps : 0 < eps)
    (hf : ∀ i n, Measurable (f i n))
    (hb : ∀ i n, eLpNorm (f i n) p P ≤ C i) :
    ∃ K : Ω → ℝ, Measurable K ∧ (∀ om, 0 < K om) ∧
      eLpNorm K p P ≤ ((∑ i, C i) + eps : ℝ≥0) ∧
      ∀ᵐ om ∂P, ∃ seq : ℕ → ℕ, StrictMono seq ∧
        ∀ i n, ‖f i (seq n) om‖ < K om := by
  classical
  let g : ℕ → Ω → ℝ := fun n om => ∑ i, ‖f i n om‖
  have hg (n : ℕ) : Measurable (g n) :=
    Finset.measurable_sum Finset.univ fun i _ => (hf i n).norm
  have hgb (n : ℕ) : eLpNorm (g n) p P ≤ (∑ i, C i : ℝ≥0) :=
    eLpNorm_sum_norm_le P p hp (fun i => f i n) C (fun i => hf i n) (fun i => hb i n)
  obtain ⟨K, hKm, hKpos, hKn, hseq⟩ := exists_bounded_subsequence_of_eLpNorm_bound
    P g p (∑ i, C i) eps hp heps hg hgb
  refine ⟨K, hKm, hKpos, hKn, ?_⟩
  filter_upwards [hseq] with om hom
  obtain ⟨seq, hmono, hs⟩ := hom
  refine ⟨seq, hmono, fun i n => ?_⟩
  have hle : ‖f i (seq n) om‖ ≤ g (seq n) om :=
    Finset.single_le_sum (fun j _ => norm_nonneg (f j (seq n) om)) (Finset.mem_univ i)
  have hnonneg : 0 ≤ g (seq n) om :=
    Finset.sum_nonneg fun j _ => norm_nonneg (f j (seq n) om)
  exact hle.trans_lt ((Real.norm_of_nonneg hnonneg) ▸ hs n)

end SubdiffusiveProcess
