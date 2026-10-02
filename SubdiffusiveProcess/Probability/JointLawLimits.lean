import Mathlib




open Filter MeasureTheory Set TopologicalSpace
open scoped Topology BoundedContinuousFunction

namespace SubdiffusiveProcess.Probability

/-- Bounded continuous test functions pass to almost-sure limits under the integral. -/
theorem tendsto_integral_boundedContinuous_of_ae_tendsto {α β : Type*} [MeasurableSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
    (ν : Measure α) [IsFiniteMeasure ν] (X : ℕ → α → β) (X' : α → β)
    (hX : ∀ N, AEMeasurable (X N) ν)
    (hXlim : ∀ᵐ a ∂ν, Tendsto (fun N => X N a) atTop (𝓝 (X' a))) (φ : β →ᵇ ℝ) :
    Tendsto (fun N => ∫ a, φ (X N a) ∂ν) atTop (𝓝 (∫ a, φ (X' a) ∂ν)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
    (fun N => AEMeasurable.aestronglyMeasurable
      ((φ.continuous.aemeasurable (μ := Measure.map (X N) ν)).comp_aemeasurable (hX N)))
    (integrable_const _)
    (fun N => Eventually.of_forall fun a => φ.norm_coe_le_norm _) ?_
  filter_upwards [hXlim] with a ha
  exact (φ.continuous.tendsto (X' a)).comp ha

/-- Almost-sure limits of sequences with equal laws have equal laws. -/
theorem map_eq_of_ae_tendsto_of_map_eq {α γ β : Type*}
    [MeasurableSpace α] [MeasurableSpace γ]
    [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β]
    [BorelSpace β]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure γ) [IsProbabilityMeasure μ]
    (X : ℕ → α → β) (X' : α → β) (Y : ℕ → γ → β) (Y' : γ → β)
    (hX : ∀ N, AEMeasurable (X N) ν) (hX' : AEMeasurable X' ν)
    (hY : ∀ N, AEMeasurable (Y N) μ) (hY' : AEMeasurable Y' μ)
    (hlaw : ∀ N, Measure.map (X N) ν = Measure.map (Y N) μ)
    (hXlim : ∀ᵐ a ∂ν, Tendsto (fun N => X N a) atTop (𝓝 (X' a)))
    (hYlim : ∀ᵐ c ∂μ, Tendsto (fun N => Y N c) atTop (𝓝 (Y' c))) :
    Measure.map X' ν = Measure.map Y' μ := by
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  rw [MeasureTheory.integral_map hX' φ.continuous.aestronglyMeasurable,
    MeasureTheory.integral_map hY' φ.continuous.aestronglyMeasurable]
  have hν := tendsto_integral_boundedContinuous_of_ae_tendsto ν X X' hX hXlim φ
  have hμ := tendsto_integral_boundedContinuous_of_ae_tendsto μ Y Y' hY hYlim φ
  have hseq : (fun N => ∫ a, φ (X N a) ∂ν) = fun N => ∫ c, φ (Y N c) ∂μ := by
    funext N
    rw [← MeasureTheory.integral_map (hX N) φ.continuous.aestronglyMeasurable,
      ← MeasureTheory.integral_map (hY N) φ.continuous.aestronglyMeasurable, hlaw N]
  rw [hseq] at hν
  exact tendsto_nhds_unique hν hμ

/-- If `(A, B)` has the law of the graph of a measurable map, then `B = ψ ∘ A` almost surely. -/
theorem ae_eq_of_map_graph {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure α) (μ : Measure β)
    (A : α → β) (B : α → E) (hA : Measurable A) (hB : Measurable B)
    (ψ : β → E) (hψ : Measurable ψ)
    (hlaw : Measure.map (fun a => (A a, B a)) ν = Measure.map (fun c => (c, ψ c)) μ) :
    ∀ᵐ a ∂ν, B a = ψ (A a) := by
  rw [MeasureTheory.ae_iff]
  set S : Set (β × E) := {p : β × E | p.2 = ψ p.1} with hSdef
  have hmeas1 : Measurable (fun a : α => (A a, B a)) := hA.prodMk hB
  have hmeas2 : Measurable (fun c : β => (c, ψ c)) := measurable_id.prodMk hψ
  have hS : MeasurableSet S := by
    rw [hSdef]
    exact measurableSet_eq_fun measurable_snd (hψ.comp measurable_fst)
  have hbad : {a : α | ¬ B a = ψ (A a)} = (fun a : α => (A a, B a)) ⁻¹' Sᶜ := by
    ext a
    simp [hSdef]
  have hempty : (fun c : β => (c, ψ c)) ⁻¹' Sᶜ = ∅ := by
    ext c
    simp [hSdef]
  rw [hbad, ← Measure.map_apply hmeas1 hS.compl, hlaw, Measure.map_apply hmeas2 hS.compl,
    hempty]
  exact measure_empty


/-- A represented limit agrees with the measurable original limit evaluated at the represented
environment, provided the finite joint laws agree and both sequences converge almost surely. -/
theorem ae_eq_of_joint_map_eq_of_ae_tendsto
    {Ω Ωhat E : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [PseudoMetrizableSpace Ω] [BorelSpace Ω]
    [MeasurableSpace Ωhat]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Phat : Measure Ωhat) [IsProbabilityMeasure Phat]
    (X : ℕ → Ω → E) (Xlim : Ω → E)
    (env : ℕ → Ωhat → Ω) (envLim : Ωhat → Ω)
    (Y : ℕ → Ωhat → E) (Ylim : Ωhat → E)
    (hX : ∀ n, Measurable (X n)) (hXlim : Measurable Xlim)
    (henv : ∀ n, Measurable (env n)) (henvLim : Measurable envLim)
    (hY : ∀ n, Measurable (Y n)) (hYlim : Measurable Ylim)
    (hlaw : ∀ n, Measure.map (fun ω => (env n ω, Y n ω)) Phat =
      Measure.map (fun ω => (ω, X n ω)) P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Xlim ω)))
    (hconvHat : ∀ᵐ ω ∂Phat,
      Tendsto (fun n => env n ω) atTop (𝓝 (envLim ω)) ∧
      Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) :
    ∀ᵐ ω ∂Phat, Ylim ω = Xlim (envLim ω) := by
  have hpair : Measure.map (fun ω => (envLim ω, Ylim ω)) Phat =
      Measure.map (fun ω => (ω, Xlim ω)) P := by
    apply map_eq_of_ae_tendsto_of_map_eq Phat P
      (fun n ω => (env n ω, Y n ω)) (fun ω => (envLim ω, Ylim ω))
      (fun n ω => (ω, X n ω)) (fun ω => (ω, Xlim ω))
      (fun n => ((henv n).prodMk (hY n)).aemeasurable)
      (henvLim.prodMk hYlim).aemeasurable
      (fun n => (measurable_id.prodMk (hX n)).aemeasurable)
      (measurable_id.prodMk hXlim).aemeasurable hlaw
    · filter_upwards [hconvHat] with ω hω
      exact hω.1.prodMk_nhds hω.2
    · filter_upwards [hconv] with ω hω
      exact tendsto_const_nhds.prodMk_nhds hω
  exact ae_eq_of_map_graph Phat P envLim Ylim henvLim hYlim Xlim hXlim hpair

end SubdiffusiveProcess.Probability
