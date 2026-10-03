module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSeries
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.Metrizable.Urysohn

@[expose] public section

namespace SubdiffusiveProcess

open MeasureTheory
open SubdiffusiveProcess.Frozen.Assumptions
open Homogenization
open Filter Topology

noncomputable section

private theorem continuous_potentialAdd {d : ℕ} :
    Continuous (fun q : PotentialField d × PotentialField d =>
      PotentialField.add q.1 q.2) := by
  apply Continuous.subtype_mk
  exact
    (((continuous_subtype_val.comp continuous_fst).fst.add
        (continuous_subtype_val.comp continuous_snd).fst).prodMk
      ((continuous_subtype_val.comp continuous_fst).snd.add
        (continuous_subtype_val.comp continuous_snd).snd))

private theorem measurable_potentialAdd {d : ℕ} :
    Measurable (fun q : PotentialField d × PotentialField d =>
      PotentialField.add q.1 q.2) := by
  let hInd : Topology.IsInducing (Subtype.val : PotentialField d →
      C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ)) := ⟨rfl⟩
  letI : SecondCountableTopology (PotentialField d) :=
    hInd.secondCountableTopology
  exact continuous_potentialAdd.measurable

private theorem continuous_potentialAnchor {d : ℕ} :
    Continuous (fun g : PotentialField d => PotentialField.anchor g) := by
  apply Continuous.subtype_mk
  · let hval : Continuous (fun g : C(Vec d, ℝ) =>
        g - ContinuousMap.const (Vec d) (g 0)) :=
      continuous_id.sub ((ContinuousMap.continuous_const' (X := Vec d) (Y := ℝ)).comp
        (continuous_eval_const (0 : Vec d)))
    exact (hval.comp continuous_subtype_val.fst).prodMk continuous_subtype_val.snd

private theorem measurable_anchoredPartialSumField {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → PotentialSample d) (hf : Measurable f) (L : ℕ) :
    Measurable (fun ω => anchoredPartialSumField (f ω) L) := by
  induction L with
  | zero =>
      exact (continuous_potentialAnchor.measurable.comp
        ((measurable_pi_apply 0).comp hf))
  | succ L ih =>
      have hnext : Measurable (fun ω => PotentialField.anchor (f ω (L + 1))) :=
        continuous_potentialAnchor.measurable.comp
          ((measurable_pi_apply (L + 1)).comp hf)
      simpa only [anchoredPartialSumField, Function.comp_def] using
        measurable_potentialAdd.comp (ih.prodMk hnext)

private def zeroPotentialField (d : ℕ) : PotentialField d := by
  refine ⟨(0, 0), ?_, ?_⟩
  · intro x
    change HasFDerivAt (fun _ : Vec d => (0 : ℝ)) 0 x
    exact hasFDerivAt_const (x := x) (c := (0 : ℝ))
  · intro K _
    exact ⟨0, by simp [LipschitzOnWith]⟩

private theorem tendsto_anchoredPartialSumField {d : ℕ}
    {omega : PotentialSample d}
    (h : SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.AnchoredC11Cauchy omega) :
    Tendsto (fun L => anchoredPartialSumField omega L)
      atTop (nhds (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.cauchyLimitField h)) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun L =>
      ((anchoredPartialSumField omega L).1.1,
        (anchoredPartialSumField omega L).1.2)) atTop
    (nhds ((SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.cauchyLimitField h).1.1,
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.cauchyLimitField h).1.2))
  rw [nhds_prod_eq]
  apply Tendsto.prodMk
  · rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
    intro K hK
    have hv :=
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.isAnchoredC11Limit_cauchyLimitField h).value_tendsto
        K hK
    simpa only [anchoredPartialSumField_apply] using hv
  · rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
    intro K hK
    have hd :=
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.isAnchoredC11Limit_cauchyLimitField h).deriv_tendsto
        K hK
    simpa only [PotentialField.deriv,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.cauchyLimitField_deriv] using hd

theorem exists_measurable_anchoredC11Limit
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → PotentialSample d)
    (hf : Measurable f)
    (hShell : ∀ᵐ ω ∂μ,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellC11Summable (f ω)) :
    ∃ H : Ω → PotentialField d, Measurable H ∧
      ∀ᵐ ω ∂μ,
        SubdiffusiveProcess.Frozen.Assumptions.IsAnchoredC11Limit (f ω) (H ω) := by
  let hInd : Topology.IsInducing (Subtype.val : PotentialField d →
      C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ)) := ⟨rfl⟩
  letI : SecondCountableTopology (PotentialField d) :=
    hInd.secondCountableTopology
  letI : TopologicalSpace.MetrizableSpace (PotentialField d) :=
    @TopologicalSpace.MetrizableSpace.subtype
      (C(Vec d, ℝ) × C(Vec d, Vec d →L[ℝ] ℝ)) _ _ _
  classical
  let good : Set (PotentialSample d) :=
    SubdiffusiveProcess.Frozen.Assumptions.anchoredC11GoodSet d
  have hgood_meas : MeasurableSet good := by
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d
  have hcauchy : ∀ {ω : Ω}, f ω ∈ good →
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.AnchoredC11Cauchy (f ω) := by
    intro ω hω
    apply SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.anchoredC11Cauchy_of_mem_anchoredCauchySet
    rw [← SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.anchoredC11GoodSet_eq_anchoredCauchySet]
    exact hω
  let G : ℕ → Ω → PotentialField d := fun L ω =>
    if hω : f ω ∈ good then
      SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField (f ω) L
    else zeroPotentialField d
  have hG : ∀ L : ℕ, Measurable (G L) := by
    intro L
    dsimp [G]
    exact Measurable.ite (hgood_meas.preimage hf)
      (measurable_anchoredPartialSumField f hf L) measurable_const
  let H : Ω → PotentialField d := fun ω =>
    if hω : f ω ∈ good then
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.cauchyLimitField (hcauchy hω)
    else zeroPotentialField d
  have hlim : Tendsto G atTop (nhds H) := by
    rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : f ω ∈ good
    · simpa only [G, H, dif_pos hω] using
        tendsto_anchoredPartialSumField (hcauchy hω)
    · simp only [G, H, dif_neg hω]
      exact tendsto_const_nhds
  have hH : Measurable H := measurable_of_tendsto_metrizable hG hlim
  have haeGood : ∀ᵐ ω ∂μ, f ω ∈ good := by
    filter_upwards [hShell] with ω hω
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.mem_anchoredC11GoodSet_of_shellC11Summable
      hω
  refine ⟨H, hH, haeGood.mono ?_⟩
  intro ω hω
  simp only [H, dif_pos hω]
  exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.isAnchoredC11Limit_cauchyLimitField
    (hcauchy hω)


end
end SubdiffusiveProcess
