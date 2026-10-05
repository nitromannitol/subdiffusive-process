module

public import SubdiffusiveProcess.WeightedLimitIdentification.RepresentedPairTransfer
public import SubdiffusiveProcess.Probability.SameLawComposition

@[expose] public section

/-! Original-space convergence to a constructed, initially nonmeasurable limit.
Joint representations first construct a measurable limit and then identify it. -/

open Filter MeasureTheory
open scoped Topology

namespace SubdiffusiveProcess.WeightedLimitIdentification

/-- Equal represented pair limits construct an original-space measurable limit. The
same finite laws and limit-field descent identify it with the prescribed function;
measurability of that prescribed function is a conclusion of the construction. -/
theorem tendsto_in_measure_of_identified_represented_pairs
    {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace.PseudoMetrizableSpace S]
    (P : Measure S) [IsProbabilityMeasure P]
    (X : ℕ → S → ℝ) (hX : ∀ n, Measurable (X n)) (V : S → ℝ)
    (hpair : ∀ u v : ℕ → ℕ, StrictMono u → StrictMono v →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ (Ωh : Type) (_ : MeasurableSpace Ωh) (Ph : Measure Ωh),
          IsProbabilityMeasure Ph ∧
          ∃ (env : ℕ → Ωh → S) (field : Ωh → S),
            (∀ n, MeasurePreserving (env n) Ph P) ∧
            MeasurePreserving field Ph P ∧
            (∀ᵐ ω ∂Ph, Tendsto (fun n => env n ω) atTop (𝓝 (field ω))) ∧
            (∀ p : S → Prop, (∀ᵐ ω ∂Ph, p (field ω)) → ∀ᵐ s ∂P, p s) ∧
            (∀ᵐ ω ∂Ph, Tendsto (fun n => X (u (σ n)) (env n ω)) atTop
              (𝓝 (V (field ω)))) ∧
            (∀ᵐ ω ∂Ph, Tendsto (fun n => X (v (σ n)) (env n ω)) atTop
              (𝓝 (V (field ω))))) :
    TendstoInMeasure P X atTop V := by
  have hpair' : ∀ u v : ℕ → ℕ, StrictMono u → StrictMono v →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ (Ωh : Type) (_ : MeasurableSpace Ωh) (Ph : Measure Ωh),
          IsProbabilityMeasure Ph ∧
          ∃ (env : ℕ → Ωh → S) (L : Ωh → ℝ),
            (∀ n, MeasurePreserving (env n) Ph P) ∧
            (∀ᵐ ω ∂Ph, Tendsto (fun n => X (u (σ n)) (env n ω)) atTop (𝓝 (L ω))) ∧
            (∀ᵐ ω ∂Ph, Tendsto (fun n => X (v (σ n)) (env n ω)) atTop (𝓝 (L ω))) := by
    intro u v hu hv
    obtain ⟨σ, hσ, Ωh, mΩh, Ph, hPh, env, field, henv, _, _, _, h1, h2⟩ :=
      hpair u v hu hv
    exact ⟨σ, hσ, Ωh, mΩh, Ph, hPh, env, fun ω => V (field ω), henv, h1, h2⟩
  obtain ⟨Y, hYmeas, hYconv, _⟩ := exists_measurable_limit_of_represented_pairs P X hX hpair'
  obtain ⟨σ, hσ, Ωh, mΩh, Ph, hPh, env, field, henv, hfield,
    hfieldconv, hdescent, hpath, _⟩ := hpair id id strictMono_id strictMono_id
  have : IsProbabilityMeasure Ph := hPh
  have htransfer :=
    SubdiffusiveProcess.tendstoInMeasure_comp_of_sameLaw_of_tendstoInMeasure
      henv hfield hfieldconv hYmeas.aestronglyMeasurable
      (fun n => (hX (σ n)).aestronglyMeasurable) (hYconv.comp hσ.tendsto_atTop)
  have heq : (fun ω => Y (field ω)) =ᵐ[Ph] fun ω => V (field ω) :=
    SubdiffusiveProcess.Probability.ae_eq_of_tendstoInMeasure_of_subseq_tendsto_ae
      htransfer tendsto_id hpath
  have horiginal : Y =ᵐ[P] V := hdescent (fun s => Y s = V s) heq
  exact TendstoInMeasure.congr_right horiginal hYconv

/-- Finitely many nonmeasurable initial responses do not affect the probability limit. -/
theorem tendsto_in_measure_of_eventually_measurable_identified_pairs
    {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace.PseudoMetrizableSpace S]
    (P : Measure S) [IsProbabilityMeasure P]
    (X : ℕ → S → ℝ) (hX : ∀ᶠ n in atTop, Measurable (X n)) (V : S → ℝ)
    (hpair : ∀ u v : ℕ → ℕ, StrictMono u → StrictMono v →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ (Ωh : Type) (_ : MeasurableSpace Ωh) (Ph : Measure Ωh),
          IsProbabilityMeasure Ph ∧
          ∃ (env : ℕ → Ωh → S) (field : Ωh → S),
            (∀ n, MeasurePreserving (env n) Ph P) ∧
            MeasurePreserving field Ph P ∧
            (∀ᵐ ω ∂Ph, Tendsto (fun n => env n ω) atTop (𝓝 (field ω))) ∧
            (∀ p : S → Prop, (∀ᵐ ω ∂Ph, p (field ω)) → ∀ᵐ s ∂P, p s) ∧
            (∀ᵐ ω ∂Ph, Tendsto (fun n => X (u (σ n)) (env n ω)) atTop
              (𝓝 (V (field ω)))) ∧
            (∀ᵐ ω ∂Ph, Tendsto (fun n => X (v (σ n)) (env n ω)) atTop
              (𝓝 (V (field ω))))) :
    TendstoInMeasure P X atTop V := by
  classical
  let X' : ℕ → S → ℝ := fun n s => if Measurable (X n) then X n s else 0
  have hX' : ∀ n, Measurable (X' n) := by
    intro n
    by_cases hn : Measurable (X n)
    · simpa only [X', ite_eq_left hn] using hn
    · simp only [X', ite_eq_right hn]
      exact measurable_const
  have heq : ∀ᶠ n in atTop, X' n = X n := by
    filter_upwards [hX] with n hn
    simp only [X', ite_eq_left hn]
  have hconv : TendstoInMeasure P X' atTop V := by
    apply tendsto_in_measure_of_identified_represented_pairs P X' hX' V
    intro u v hu hv
    obtain ⟨σ, hσ, Ωh, mΩh, Ph, hPh, env, field, henv, hfield,
      hfieldconv, hdescent, h1, h2⟩ := hpair u v hu hv
    refine ⟨σ, hσ, Ωh, mΩh, Ph, hPh, env, field, henv, hfield,
      hfieldconv, hdescent, ?_, ?_⟩
    · filter_upwards [h1] with ω hω
      apply hω.congr'
      filter_upwards [(hu.comp hσ).tendsto_atTop.eventually heq] with n hn
      exact (congrFun hn (env n ω)).symm
    · filter_upwards [h2] with ω hω
      apply hω.congr'
      filter_upwards [(hv.comp hσ).tendsto_atTop.eventually heq] with n hn
      exact (congrFun hn (env n ω)).symm
  exact TendstoInMeasure.congr'
    (heq.mono fun n hn => Filter.Eventually.of_forall fun s => congrFun hn s)
    Filter.EventuallyEq.rfl hconv

end SubdiffusiveProcess.WeightedLimitIdentification
