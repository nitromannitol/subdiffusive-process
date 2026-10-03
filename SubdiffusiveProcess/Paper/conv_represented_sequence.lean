module

public import SubdiffusiveProcess.Lane2.LimitForm

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



def conv_represented_sequence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {ι : Type*}
    (resp : ι → ℕ → Ω → ℝ) (respLim : ι → Ω → ℝ)
    (const : ι → ℕ → Ω → ℝ) (G : Set Ω) : Prop :=
  -- the catalog `C` is countable
  Countable ι ∧
  -- the pathwise statements are made on one measurable event
  MeasurableSet G ∧
  -- of probability one
  P Gᶜ = 0 ∧
  -- along the represented sequence every response converges, pathwise
  (∀ i : ι, ∀ ω ∈ G,
    Tendsto (fun N : ℕ => resp i N ω) atTop (𝓝 (respLim i ω))) ∧
  -- every constant attached to a fixed object is bounded -- for each fixed object, and only so
  -- convergence of the constants on the represented space is sufficient for this clause
  (∀ i : ι, ∀ ω ∈ G, ∃ M : ℝ, ∀ N : ℕ, |const i N ω| ≤ M)

end Paper
