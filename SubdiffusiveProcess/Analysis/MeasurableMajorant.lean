module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

/-! A measurable pointwise majorant with exactly the original a.e. values. -/
namespace SubdiffusiveProcess.Analysis
open MeasureTheory Set Filter

/-- If an a.e. measurable real function has a measurable pointwise upper bound,
choose a measurable version that still dominates it at every point. The version
agrees a.e. with the original, so it preserves every moment simultaneously. -/
theorem exists_measurable_majorant_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : AEMeasurable f μ)
    (hg : Measurable g) (hfg : ∀ ω, f ω ≤ g ω) :
    ∃ k : Ω → ℝ, Measurable k ∧ (∀ ω, f ω ≤ k ω) ∧ f =ᵐ[μ] k := by
  classical
  have hnull : μ {ω | f ω ≠ hf.mk f ω} = 0 := by
    exact ae_iff.mp hf.ae_eq_mk
  obtain ⟨s, hsub, hs, hμs⟩ := exists_measurable_superset_of_null hnull
  let k : Ω → ℝ := s.piecewise g (hf.mk f)
  refine ⟨k, hg.piecewise hs hf.measurable_mk, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ s
    · simpa only [k, piecewise_eq_of_mem s g (hf.mk f) hω] using hfg ω
    · have heq : f ω = hf.mk f ω := by
        by_contra hne
        exact hω (hsub hne)
      simpa only [k, piecewise_eq_of_notMem s g (hf.mk f) hω] using heq.le
  · have houtside : ∀ᵐ ω ∂μ, ω ∉ s := by
      rw [ae_iff]
      simpa only [not_not, Set.setOf_mem_eq] using hμs
    filter_upwards [houtside, hf.ae_eq_mk] with ω hω heq
    simpa only [k, piecewise_eq_of_notMem s g (hf.mk f) hω] using heq

end SubdiffusiveProcess.Analysis
