import Mathlib

/-!
# Continuous representatives from vanishing essential intervals

The construction uses the neighborhood filter intersected with the
almost-everywhere filter. The Lindelöf property identifies the resulting
continuous function almost everywhere, without differentiating averages.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Every neighborhood meets every conull set for an open-positive measure. -/
theorem essential_nhds_neBot {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (mu : Measure X) [mu.IsOpenPosMeasure] (x : X) :
    NeBot (nhds x ⊓ ae mu) := by
  rw [inf_neBot_iff]
  intro V hV S hS
  exact Measure.exists_mem_of_measure_ne_zero_of_ae
    (mu.measure_pos_of_mem_nhds hV).ne' (ae_restrict_of_ae hS)

/-- A continuous essential limit is a representative. The countable
intersection property of the a.e. filter replaces pointwise evaluation. -/
theorem essential_limit_ae_eq {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [HereditarilyLindelofSpace X] [OpensMeasurableSpace X] {mu : Measure X}
    {U : Set X} (hU : IsOpen U) {f g : X → ℝ} (hg : ContinuousOn g U)
    (hlim : ∀ x ∈ U, Tendsto f (nhds x ⊓ ae mu) (nhds (g x))) :
    g =ᵐ[mu.restrict U] f := by
  have hsmall (n : ℕ) : ∀ᵐ x ∂mu, x ∈ U → dist (g x) (f x) < 1 / ((n : ℝ) + 1) := by
    let S : Set X := {x | x ∈ U ∧ ¬ dist (g x) (f x) < 1 / ((n : ℝ) + 1)}
    have hS : IsLindelof S := HereditarilyLindelof_LindelofSets S
    have hcomp : Sᶜ ∈ ae mu := hS.compl_mem_sets (fun x hx => by
      have hgc : Tendsto g (nhds x ⊓ ae mu) (nhds (g x)) :=
        (hg.continuousAt (hU.mem_nhds hx.1)).mono_left inf_le_left
      have hd := hgc.dist (hlim x hx.1)
      have he : ∀ᶠ y in nhds x ⊓ ae mu, dist (g y) (f y) < 1 / ((n : ℝ) + 1) :=
        hd.eventually (gt_mem_nhds (by simp; positivity))
      exact he.mono fun y hy hys => hys.2 hy)
    filter_upwards [hcomp] with x hx hxu
    exact not_not.mp (fun hn => hx ⟨hxu, hn⟩)
  have hall := ae_all_iff.2 hsmall
  apply (ae_restrict_iff' hU.measurableSet).2
  filter_upwards [hall] with x hx hxu
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto ht (Eventually.of_forall fun n => (hx n hxu).le)

/-- Vanishing essential intervals on neighborhoods give a continuous
representative on the open carrier. -/
theorem exists_continuousRepresentative_of_essential_intervals
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [HereditarilyLindelofSpace X] [OpensMeasurableSpace X]
    (mu : Measure X) [mu.IsOpenPosMeasure]
    {U : Set X} (hU : IsOpen U) (f : X → ℝ)
    (hlocal : ∀ x ∈ U, ∀ eps : ℝ, 0 < eps →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
        ∃ l H : ℝ, H - l < eps ∧ ∀ᵐ y ∂mu.restrict V, l ≤ f y ∧ f y ≤ H) :
    ∃ g : X → ℝ, ContinuousOn g U ∧ g =ᵐ[mu.restrict U] f := by
  have hne (x : X) : NeBot (nhds x ⊓ ae mu) := essential_nhds_neBot mu x
  let g : X → ℝ := fun x => limUnder (nhds x ⊓ ae mu) f
  have hlim (x : X) (hx : x ∈ U) : Tendsto f (nhds x ⊓ ae mu) (nhds (g x)) := by
    haveI := hne x
    apply tendsto_nhds_limUnder
    apply CompleteSpace.complete
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, ?_⟩
    intro eps heps
    obtain ⟨V, hVo, hxV, l, H, hwidth, hbound⟩ := hlocal x hx eps heps
    refine ⟨Icc l H, ?_, ?_⟩
    · change (fun y => f y) ⁻¹' Icc l H ∈ nhds x ⊓ ae mu
      have hcond := (ae_restrict_iff' hVo.measurableSet).1 hbound
      filter_upwards [Eventually.filter_mono inf_le_left (hVo.mem_nhds hxV),
        Eventually.filter_mono inf_le_right hcond] with y hy hyb
      exact hyb hy
    · intro v hv w hw
      rw [Real.dist_eq]
      exact (abs_le.mpr ⟨by linarith [hv.1, hw.2], by linarith [hv.2, hw.1]⟩).trans_lt hwidth
  have hg : ContinuousOn g U := by
    intro x hx
    suffices ∀ S ∈ nhds (g x), IsClosed S → g ⁻¹' S ∈ nhdsWithin x U by
      simpa [ContinuousWithinAt, (closed_nhds_basis (g x)).tendsto_right_iff]
    intro S hS hSc
    obtain ⟨V, hV, A, hA, hsub⟩ := mem_inf_iff_superset.1 ((hlim x hx) hS)
    obtain ⟨W, hWV, hWo, hxW⟩ := mem_nhds_iff.1 hV
    refine mem_of_superset (inter_mem_inf (hWo.mem_nhds hxW) (mem_principal_self U)) ?_
    intro y hy
    haveI := hne y
    apply hSc.mem_of_tendsto (hlim y hy.2)
    filter_upwards [Eventually.filter_mono inf_le_left (hWo.mem_nhds hy.1),
      Eventually.filter_mono inf_le_right hA] with z hz hzA
    exact hsub ⟨hWV hz, hzA⟩
  exact ⟨g, hg, essential_limit_ae_eq hU hg hlim⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
