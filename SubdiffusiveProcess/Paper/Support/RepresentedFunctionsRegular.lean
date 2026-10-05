module

public import Mathlib
public import SubdiffusiveProcess.Paper.Support.RepresentedCoordinatesRegular
public import SubdiffusiveProcess.Probability.JointLawLimits

@[expose] public section





set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology

noncomputable section
namespace SubdiffusiveProcess.WeightedLimitIdentification
open _root_.SubdiffusiveProcess.Paper

/-- **Represented functions of the environment.** Countably many measurable real functions
`Y i n` of the environment, each with a tight family of laws under the environment law `P0`,
are represented along one common strictly increasing `seq`: there is a probability space with
environments `env n` of the original law (each `env n` measure preserving) and a limit
environment of the same law such that, almost surely, `env n → envLim` and every
`Y i (seq n) (env n ·)` converges. The represented terms are exactly functions of `env n`;
the law of the vector at index `n` is the original law, and nothing is asserted across
different indices. -/
theorem represented_environment_functions_with_ae_descent
    {E : Type} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type} [Countable ι]
    (P0 : Measure E) [IsProbabilityMeasure P0]
    (Y : ι → ℕ → E → ℝ) (hY : ∀ i n, Measurable (Y i n))
    (htight : ∀ i, IsTightMeasureSet (Set.range fun n => Measure.map (Y i n) P0)) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧
      ∃ (Ωh : Type) (_ : MeasurableSpace Ωh) (Ph : Measure Ωh) (_ : IsProbabilityMeasure Ph)
        (env : ℕ → Ωh → E) (envLim : Ωh → E) (Ylim : ι → Ωh → ℝ),
        (∀ n, MeasurePreserving (env n) Ph P0) ∧ MeasurePreserving envLim Ph P0 ∧
        (∀ i, Measurable (Ylim i)) ∧
        (∀ᵐ ω ∂Ph, Tendsto (fun n => env n ω) atTop (𝓝 (envLim ω)) ∧
          ∀ i, Tendsto (fun n => Y i (seq n) (env n ω)) atTop (𝓝 (Ylim i ω))) ∧
        (∀ p : E → Prop, (∀ᵐ ω ∂Ph, p (envLim ω)) → ∀ᵐ β ∂P0, p β) := by
  obtain ⟨seq, hseq, Ωh, mΩh, Ph, hPh, env, envLim, Yh, Ylim, henv, henvLim, hYh, hYlim,
    hlaw, hconv, htop⟩ := represented_environment_coordinates_regular P0 id measurable_id Y hY htight
  have hlaw' : ∀ n, Measure.map (fun ω => (env n ω, fun i => Yh i n ω)) Ph =
      Measure.map (fun β : E => (β, fun i => Y i (seq n) β)) P0 := hlaw
  have hm1 : ∀ n, Measurable (fun ω => (env n ω, fun i => Yh i n ω)) := fun n =>
    (henv n).prodMk (measurable_pi_iff.mpr (fun i => hYh i n))
  have hm2 : ∀ n, Measurable (fun β : E => (β, fun i => Y i (seq n) β)) := fun n =>
    measurable_id.prodMk (measurable_pi_iff.mpr (fun i => hY i _))
  have hmp : ∀ n, Measure.map (env n) Ph = P0 := by
    intro n
    have h1 := congrArg (Measure.map Prod.fst) (hlaw' n)
    rw [Measure.map_map measurable_fst (hm1 n), Measure.map_map measurable_fst (hm2 n)] at h1
    simpa [Function.comp_def] using h1
  have hmpLim : MeasurePreserving envLim Ph P0 := by
    refine ⟨henvLim, ?_⟩
    have := SubdiffusiveProcess.Probability.map_eq_of_ae_tendsto_of_map_eq Ph P0
      env envLim (fun _ => id) id (fun n => (henv n).aemeasurable) henvLim.aemeasurable
      (fun _ => measurable_id.aemeasurable) measurable_id.aemeasurable
      (fun n => by simpa using hmp n)
      (hconv.mono fun ω h => h.1) (Filter.Eventually.of_forall fun _ => tendsto_const_nhds)
    simpa using this
  obtain ⟨topΩh, hborel, hpolish, hcont⟩ := htop
  let : TopologicalSpace Ωh := topΩh
  have : BorelSpace Ωh := hborel
  have : PolishSpace Ωh := hpolish
  refine ⟨seq, hseq, Ωh, mΩh, Ph, hPh, env, envLim, Ylim,
    fun n => ⟨henv n, hmp n⟩, hmpLim, hYlim, ?_, ?_⟩
  · have hgraph : ∀ i n, ∀ᵐ ω ∂Ph, Yh i n ω = Y i (seq n) (env n ω) := by
      intro i n
      have h1 := congrArg (Measure.map (fun p : E × (ι → ℝ) => (p.1, p.2 i))) (hlaw' n)
      have hproj : Measurable (fun p : E × (ι → ℝ) => (p.1, p.2 i)) :=
        measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
      rw [Measure.map_map hproj (hm1 n), Measure.map_map hproj (hm2 n)] at h1
      exact SubdiffusiveProcess.Probability.ae_eq_of_map_graph Ph P0 (env n) (Yh i n)
        (henv n) (hYh i n) (Y i (seq n)) (hY i _) (by simpa [Function.comp_def] using h1)
    have hall : ∀ᵐ ω ∂Ph, ∀ i n, Yh i n ω = Y i (seq n) (env n ω) :=
      ae_all_iff.2 fun i => ae_all_iff.2 fun n => hgraph i n
    filter_upwards [hconv, hall] with ω hω hg
    refine ⟨hω.1, fun i => ?_⟩
    have : (fun n => Y i (seq n) (env n ω)) = fun n => Yh i n ω := funext fun n => (hg i n).symm
    rw [this]
    exact hω.2 i

  · exact fun p hp => ae_of_ae_comp_continuous Ph P0 envLim hcont hmpLim p hp

end SubdiffusiveProcess.WeightedLimitIdentification
