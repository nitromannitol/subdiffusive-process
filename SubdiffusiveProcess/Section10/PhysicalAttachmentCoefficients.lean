import SubdiffusiveProcess.Assumptions.CoefficientRegularity
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationFamily
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrierGrowth
import SubdiffusiveProcess.Section10.PhysicalAttachmentMeasurableCore
import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalAttachment

/-- The source probability on the exact anchored C11 carrier. -/
def physicalLaw {d : ℕ} (M : GMCModel d) : ProbabilityMeasure (AnchoredC11Sample d) :=
  anchoredC11SampleLaw M (Section6Anchored.measurableSet_anchoredC11GoodSet d)
    (Section6Anchored.measure_anchoredC11GoodSet_eq_one M)

/-- The literal logarithm of the actual coefficient, finite and top. -/
def physicalPotential {d : ℕ} (M : GMCModel d) (L : WithTop ℕ)
    (omega : AnchoredC11Sample d) : C(Vec d, ℝ) :=
  match L with
  | ⊤ => (anchoredLog omega).1.1
  | (n : ℕ) =>
      ∑ k ∈ Finset.range (n + 1),
        ((omega.val k).1.1 - ContinuousMap.const _ (tauSq M.P))

theorem exp_physicalPotential {d : ℕ} (M : GMCModel d) (L : WithTop ℕ)
    (omega : AnchoredC11Sample d) (x : Vec d) :
    Real.exp (physicalPotential M L omega x) = coefficientAt M L omega x := by
  cases L with
  | top => rfl
  | coe n =>
      simp only [physicalPotential, ContinuousMap.sum_apply, ContinuousMap.sub_apply,
        ContinuousMap.const_apply]
      rfl

theorem measurable_physicalPotential {d : ℕ}
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    (M : GMCModel d) (L : WithTop ℕ) : Measurable (physicalPotential M L) := by
  let forget : C(PotentialField d, C(Vec d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  have hforget : Measurable (fun g : PotentialField d => g.1.1) :=
    forget.continuous.measurable
  have hcoord : ∀ k, Measurable (fun omega : AnchoredC11Sample d => (omega.val k).1.1) :=
    fun k => hforget.comp ((measurable_pi_apply k).comp measurable_subtype_coe)
  cases L with
  | coe n =>
      change Measurable (fun omega : AnchoredC11Sample d =>
        ∑ k ∈ Finset.range (n + 1), ((omega.val k).1.1 - ContinuousMap.const _ (tauSq M.P)))
      exact Finset.measurable_sum _ fun k _ => (hcoord k).sub measurable_const
  | top =>
      let P : ℕ → AnchoredC11Sample d → C(Vec d, ℝ) := fun n omega =>
        ∑ k ∈ Finset.range (n + 1),
          ((omega.val k).1.1 - ContinuousMap.const _ (omega.val k 0))
      have hP : ∀ n, Measurable (P n) := by
        intro n
        dsimp only [P]
        apply Finset.measurable_sum
        intro k _
        exact (hcoord k).sub
          (ContinuousMap.continuous_const'.measurable.comp
            ((PotentialField.measurable_eval 0).comp
              ((measurable_pi_apply k).comp measurable_subtype_coe)))
      apply measurable_of_tendsto_metrizable hP
      apply tendsto_pi_nhds.mpr
      intro omega
      apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
      intro K hK
      have h := (anchoredLog_spec omega).value_tendsto K hK
      convert h using 1
      funext n x
      simp only [P, ContinuousMap.sum_apply, ContinuousMap.sub_apply, ContinuousMap.const_apply]
      rfl

theorem locallyC11_coefficientAt {d : ℕ} (M : GMCModel d) (L : WithTop ℕ)
    (omega : AnchoredC11Sample d) :
    SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11 (coefficientAt M L omega) := by
  have h : Section9SupportInput.CoefficientC11On univ (coefficientAt M L omega) := by
    cases L with
    | top => exact coefficientC11On_aAnchored M omega univ
    | coe n => exact coefficientC11On_aCutoff M n omega.val univ
  obtain ⟨Da, hDa, hLip⟩ := h
  exact ⟨Da, fun x => hDa x (mem_univ x), fun K hK => hLip K hK (subset_univ K)⟩

end SubdiffusiveProcess.Section10.PhysicalAttachment
