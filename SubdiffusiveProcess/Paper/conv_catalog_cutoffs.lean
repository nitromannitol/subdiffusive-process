module

public import SubdiffusiveProcess.VariationalResponses.LimitForm

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem conv_catalog_cutoffs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ι : Type*} [Countable ι]
    (resp : ι → ℕ → Ω → ℝ) (respLim : ι → Ω → ℝ)
    (const : ι → ℕ → Ω → ℝ) (G : Set Ω)
    (hfull : P Gᶜ = 0)
    (hresp : ∀ i : ι, ∀ ω ∈ G,
      Tendsto (fun N : ℕ => resp i N ω) atTop (𝓝 (respLim i ω)))
    (hconst : ∀ i : ι, ∀ ω ∈ G, ∃ M : ℝ, ∀ N : ℕ, |const i N ω| ≤ M)
    (k : Ω → ι) :
    P Gᶜ = 0 ∧
      (∀ ω ∈ G, Tendsto (fun N : ℕ => resp (k ω) N ω) atTop (𝓝 (respLim (k ω) ω))) ∧
      (∀ ω ∈ G, ∃ M : ℝ, ∀ N : ℕ, |const (k ω) N ω| ≤ M) :=
  ⟨hfull, fun ω hω => hresp (k ω) ω hω, fun ω hω => hconst (k ω) ω hω⟩

end SubdiffusiveProcess.Paper
