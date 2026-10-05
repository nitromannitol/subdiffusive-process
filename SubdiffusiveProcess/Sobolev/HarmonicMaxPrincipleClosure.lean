module

public import SubdiffusiveProcess.Sobolev.HarmonicDiffMaxPrinciple
public import SubdiffusiveProcess.Sobolev.HarmonicityTransfer
public import Mathlib.Topology.Sequences

@[expose] public section

/-!
# Continuous representatives of the difference maximum principle

This module upgrades the a.e. weak maximum principle for two harmonic
functions to a pointwise bound on the closure when their representatives are
continuous. It does not construct the comparison data or zero-trace witnesses.
-/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization

namespace SubdiffusiveProcess

variable {d : ℕ}

/-- A continuous function bounded a.e. on an open set obeys the same bound at
every point of that open set, provided volume assigns positive measure to
every ball. -/
theorem abs_le_of_ae_abs_le_of_continuousOn_open
    {K : Set (SpatialCoordinates d)} (hK : IsOpen K)
    (f : SpatialCoordinates d → ℝ) (hf : ContinuousOn f K) (C : ℝ)
    (hfae : ∀ᵐ x ∂(volume.restrict K), |f x| ≤ C) :
    ∀ x ∈ K, |f x| ≤ C := by
  intro x hx
  by_contra hnot
  have hgt : C < |f x| := lt_of_not_ge hnot
  have hcont : ContinuousAt f x := hf.continuousAt (hK.mem_nhds hx)
  have hbadNhd : {y | C < |f y|} ∈ nhds x := by
    have hIoi : Set.Ioi C ∈ nhds |f x| := isOpen_Ioi.mem_nhds hgt
    simpa only [Set.preimage, Function.comp_def, Set.mem_Ioi] using
      (continuous_abs.continuousAt.comp hcont).preimage_mem_nhds hIoi
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hbadNhd
  obtain ⟨s, hs, hssub⟩ := Metric.mem_nhds_iff.mp (hK.mem_nhds hx)
  let t : ℝ := min r s
  have ht : 0 < t := by dsimp [t]; exact lt_min hr hs
  have hballK : Metric.ball x t ⊆ K := by
    intro y hy
    exact hssub (Metric.ball_subset_ball (min_le_right _ _) hy)
  have hballBad : Metric.ball x t ⊆ {y | ¬ |f y| ≤ C} := by
    intro y hy
    exact not_le_of_gt (hrsub (Metric.ball_subset_ball (min_le_left _ _) hy))
  have hbad0 : (volume.restrict K) {y | ¬ |f y| ≤ C} = 0 := by
    exact (ae_iff.mp hfae)
  have hball0 : (volume.restrict K) (Metric.ball x t) = 0 :=
    measure_mono_null hballBad hbad0
  rw [Measure.restrict_apply (measurableSet_ball)] at hball0
  rw [inter_eq_left.mpr hballK] at hball0
  exact (ne_of_gt (Metric.measure_ball_pos volume x ht)) hball0

/-- The weak maximum principle for two weakly harmonic functions gives the
same pointwise comparison for continuous representatives, including on the
boundary of the cell. -/
theorem abs_sub_le_on_closure_of_isWeaklyHarmonicOn
    [NeZero d] {K : Set (SpatialCoordinates d)}
    (hK : IsOpenBoundedConvexDomain K)
    (w1 w2 : Homogenization.H1Function K)
    (hw1 : IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) K w1)
    (hw2 : IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) K w2)
    (phi1 phi2 : Homogenization.H1Function K)
    (hzero1 : HasZeroTraceDifferenceOn K w1 phi1)
    (hzero2 : HasZeroTraceDifferenceOn K w2 phi2)
    {C : ℝ} (hC : 0 ≤ C)
    (hphi : ∀ x ∈ K, |phi1.toFun x - phi2.toFun x| ≤ C)
    (V1 V2 : SpatialCoordinates d → ℝ)
    (hV1 : ContinuousOn V1 (closure K))
    (hV2 : ContinuousOn V2 (closure K))
    (hrep1 : w1.toFun =ᵐ[volume.restrict K] V1)
    (hrep2 : w2.toFun =ᵐ[volume.restrict K] V2) :
    ∀ x ∈ closure K, |V1 x - V2 x| ≤ C := by
  have hdiff1 : MemH10 K (fun y => w1.toFun y - phi1.toFun y) := by
    obtain ⟨rho, hrho, _⟩ := hzero1
    refine ⟨rho, ?_⟩
    funext y
    rw [hrho y]
    ring
  have hdiff2 : MemH10 K (fun y => w2.toFun y - phi2.toFun y) := by
    obtain ⟨rho, hrho, _⟩ := hzero2
    refine ⟨rho, ?_⟩
    funext y
    rw [hrho y]
    ring
  have hae := ae_abs_sub_le_of_isWeaklyHarmonicOn hK hw1 hw2 hdiff1 hdiff2 hC hphi
  have hVae : ∀ᵐ x ∂(volume.restrict K), |V1 x - V2 x| ≤ C := by
    filter_upwards [hae, hrep1, hrep2] with x h h1 h2
    rw [← h1, ← h2]
    exact h
  have hVopen : ContinuousOn (fun x => V1 x - V2 x) K :=
    (hV1.sub hV2).mono subset_closure
  have hpoint : ∀ x ∈ K, |V1 x - V2 x| ≤ C :=
    abs_le_of_ae_abs_le_of_continuousOn_open hK.isOpen _ hVopen C hVae
  intro x hx
  obtain ⟨q, hqK, hq⟩ := mem_closure_iff_seq_limit.mp hx
  have hqWithin : Tendsto q atTop (nhdsWithin x (closure K)) := by
    rw [nhdsWithin]
    exact tendsto_inf.2 ⟨hq, tendsto_principal.2
      (Filter.Eventually.of_forall fun n => subset_closure (hqK n))⟩
  have hlim : Tendsto (fun n => |V1 (q n) - V2 (q n)|) atTop
      (nhds |V1 x - V2 x|) := by
    have hcont1 := hV1.continuousWithinAt hx
    have hcont2 := hV2.continuousWithinAt hx
    exact ((hcont1.sub hcont2).abs).tendsto.comp hqWithin
  exact isClosed_Iic.mem_of_tendsto hlim (Filter.Eventually.of_forall fun n => hpoint _ (hqK n))

end SubdiffusiveProcess
