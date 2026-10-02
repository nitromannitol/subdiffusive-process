import SubdiffusiveProcess.Probability.SameLawComposition

/-! Identification of actual responses under changing correct-law environments.
These lemmas use convergence in measure, with no original-space a.s. premise. -/

open Filter MeasureTheory
open scoped Topology

namespace SubdiffusiveProcess.Section9

/-- Continuous tests of a sequence converging in measure also converge in measure. -/
theorem tendstoInMeasure_continuous_test
    {Ω F E : Type*} [MeasurableSpace Ω]
    [PseudoEMetricSpace F] [PseudoEMetricSpace E]
    (P : Measure Ω) [IsFiniteMeasure P]
    (X : ℕ → Ω → F) (G : Ω → F) (test : F → E) (htest : Continuous test)
    (hmeas : ∀ n, AEStronglyMeasurable (fun ω => test (X n ω)) P)
    (hconv : TendstoInMeasure P X atTop G) :
    TendstoInMeasure P (fun n ω => test (X n ω)) atTop (fun ω => test (G ω)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff hmeas).mpr
  intro seq hseq
  obtain ⟨subseq, hsubseq, hae⟩ := (hconv.comp hseq.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨subseq, hsubseq, ?_⟩
  filter_upwards [hae] with ω hω
  exact (htest.tendsto (G ω)).comp hω

/-- A represented scalar response limit is the canonical limit at the limiting field. -/
theorem ae_eq_canonical_response
    {Ω S : Type*} [MeasurableSpace Ω]
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace.PseudoMetrizableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S) [IsProbabilityMeasure μ]
    (env : ℕ → Ω → S) (field : Ω → S)
    (hmp : ∀ n, MeasurePreserving (env n) P μ)
    (hfield : MeasurePreserving field P μ)
    (henv : ∀ᵐ ω ∂P, Tendsto (fun n => env n ω) atTop (𝓝 (field ω)))
    (X : ℕ → S → ℝ) (G : S → ℝ) (L : Ω → ℝ)
    (hX : ∀ n, AEStronglyMeasurable (X n) μ) (hG : AEStronglyMeasurable G μ)
    (hconv : TendstoInMeasure μ X atTop G)
    (hrep : ∀ᵐ ω ∂P, Tendsto (fun n => X n (env n ω)) atTop (𝓝 (L ω))) :
    ∀ᵐ ω ∂P, L ω = G (field ω) := by
  have hrepProb := tendstoInMeasure_of_tendsto_ae
    (fun n => (hX n).comp_measurePreserving (hmp n)) hrep
  have hcanon := SubdiffusiveProcess.tendstoInMeasure_comp_of_sameLaw_of_tendstoInMeasure
    hmp hfield henv hG hX hconv
  exact tendstoInMeasure_ae_unique hrepProb hcanon

end SubdiffusiveProcess.Section9
