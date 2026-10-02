import SubdiffusiveProcess.Paper.conv_represented_sequence

open Filter MeasureTheory Set
open scoped Topology

namespace Paper

/-- Almost-sure convergence of the countable response and constant coordinates on a
represented probability space supplies the represented-sequence convention. This theorem
does not construct the representation or assert boundedness on the original space. -/
theorem conv_represented_sequence_of_ae_tendsto
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω)
    (resp const : ι → ℕ → Ω → ℝ) (respLim constLim : ι → Ω → ℝ)
    (hresp : ∀ i, ∀ᵐ ω ∂P,
      Tendsto (fun n => resp i n ω) atTop (𝓝 (respLim i ω)))
    (hconst : ∀ i, ∀ᵐ ω ∂P,
      Tendsto (fun n => const i n ω) atTop (𝓝 (constLim i ω))) :
    ∃ G : Set Ω, conv_represented_sequence P resp respLim const G := by
  let s : Set Ω := {ω | ∀ i,
    Tendsto (fun n => resp i n ω) atTop (𝓝 (respLim i ω)) ∧
    Tendsto (fun n => const i n ω) atTop (𝓝 (constLim i ω))}
  have hs : ∀ᵐ ω ∂P, ω ∈ s := ae_all_iff.mpr fun i => (hresp i).and (hconst i)
  let G := (toMeasurable P sᶜ)ᶜ
  have hGs : G ⊆ s := by
    intro ω hω
    by_contra hnot
    exact hω (subset_toMeasurable P sᶜ hnot)
  have hGnull : P Gᶜ = 0 := by
    simpa only [G, compl_compl, measure_toMeasurable] using (ae_iff.mp hs)
  refine ⟨G, inferInstance, (measurableSet_toMeasurable P sᶜ).compl, hGnull,
    fun i ω hω => (hGs hω i).1, ?_⟩
  intro i ω hω
  obtain ⟨M, hM⟩ := (hGs hω i).2.abs.bddAbove_range
  exact ⟨M, fun n => hM (mem_range_self n)⟩

end Paper
