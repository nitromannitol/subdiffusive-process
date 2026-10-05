module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section

/-! Relative compactness in a finite `Lᵖ` space gives almost-sure subsubsequences.
This module does not assert uniqueness of the resulting limits. -/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace SubdiffusiveProcess.Lnorm

/-- A relatively compact `Lᵖ` family has an almost-surely convergent refinement of any sequence. -/
theorem ae_subseq_of_lp_compact {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (_hpfin : p ≠ ∞)
    (X : ℕ → Ω → ℝ) (hmem : ∀ n, MemLp (X n) p μ)
    (hcompact : IsCompact (closure (range (fun n => (hmem n).toLp (X n)))))
    (ψ : ℕ → ℕ) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ L : Ω → ℝ,
      AEStronglyMeasurable L μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => X (ψ (τ n)) ω) atTop (𝓝 (L ω)) := by
  obtain ⟨L, _, σ, hσ, hL⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self (ψ n)))
  have hmeasure := tendstoInMeasure_of_tendsto_Lp hL
  obtain ⟨ρ, hρ, hρL⟩ := hmeasure.exists_seq_tendsto_ae
  refine ⟨σ ∘ ρ, hσ.comp hρ, (L : Ω → ℝ), Lp.aestronglyMeasurable L, ?_⟩
  have hrep : ∀ᵐ ω ∂μ, ∀ n,
      ((hmem (ψ (σ (ρ n)))).toLp (X (ψ (σ (ρ n)))) : Ω → ℝ) ω =
        X (ψ (σ (ρ n))) ω :=
    ae_all_iff.mpr (fun n => (hmem (ψ (σ (ρ n)))).coeFn_toLp)
  filter_upwards [hρL, hrep] with ω hω hωrep
  exact hω.congr hωrep

end SubdiffusiveProcess.Lnorm
