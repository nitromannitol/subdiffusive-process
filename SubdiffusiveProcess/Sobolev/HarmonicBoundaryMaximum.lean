import SubdiffusiveProcess.Sobolev.WeakGraphMaxPrinciple
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.AffineHarmonic

/-!+# Boundary bounds for continuous weakly harmonic representatives

A pointwise bound on the frontier of a bounded convex open set controls a
continuous weakly harmonic representative on its closure. This module does
not construct harmonic replacements or supply their energy bounds.
-/

open Filter MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped Topology

namespace SubdiffusiveProcess

/-- A strict frontier bound makes the corresponding positive part have zero trace. -/
theorem hasBoundaryUpperBoundOn_of_continuous_frontier_lt
    {d : ℕ} {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W) (u : H1Function W)
    (U : SpatialCoordinates d → ℝ) (hU : ContinuousOn U (closure W))
    (hrep : u.toFun =ᵐ[volume.restrict W] U)
    (M : ℝ) (hbd : ∀ x ∈ frontier W, U x < M) :
    HasBoundaryUpperBoundOn W u M := by
  classical
  let K : Set (SpatialCoordinates d) := closure W ∩ U ⁻¹' Set.Ici M
  have hKclosed : IsClosed K :=
    hU.preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici
  have hKcompact : IsCompact K :=
    hW.isBoundedDomain.isBounded.isCompact_closure.of_isClosed_subset
      hKclosed inter_subset_left
  have hKW : K ⊆ W := by
    intro x hx
    by_contra hn
    have hfront : x ∈ frontier W := by
      rw [hW.isOpen.frontier_eq]
      exact ⟨hx.1, hn⟩
    exact (not_lt_of_ge hx.2) (hbd x hfront)
  obtain ⟨w, hwval, hwgrad⟩ := exists_h1_max_sub_const hW u M
  let F : SpatialCoordinates d → ℝ := W.indicator (fun x => max (U x - M) 0)
  have hFw : F =ᵐ[volume.restrict W] w.toFun := by
    filter_upwards [hrep, ae_restrict_mem hW.isOpen.measurableSet] with x hx hxW
    simp only [F, Set.indicator_of_mem hxW, hwval, hx]
  let w' : H1Function W := H1Function.ofAEEq w F hFw
  have hwzero : ∀ x, x ∉ K → w'.toFun x = 0 := by
    intro x hx
    change F x = 0
    by_cases hxW : x ∈ W
    · have hxlt : U x < M := by
        by_contra hn
        exact hx ⟨subset_closure hxW, le_of_not_gt hn⟩
      simp only [F, Set.indicator_of_mem hxW, max_eq_right (sub_nonpos.mpr hxlt.le)]
    · exact Set.indicator_of_notMem hxW _
  have hmemF : MemH10 W F := memH10_of_compactSupport hW w' hKcompact hKW hwzero
  obtain ⟨psi, hpsi⟩ := memH10_congr hmemF hFw
  have hgrad : psi.toH1Function.grad =ᵐ[volume.restrict W] w.grad :=
    Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq hW.isOpen
      (Filter.Eventually.of_forall fun x => congrFun hpsi x)
  refine ⟨psi, hpsi.trans hwval, ?_⟩
  exact hgrad.trans hwgrad

/-- A continuous representative inherits an almost-everywhere upper bound on the closure. -/
theorem le_on_closure_of_continuousOn_of_ae_le
    {d : ℕ} {W : Set (SpatialCoordinates d)} (hW : IsOpen W)
    (U : SpatialCoordinates d → ℝ) (hU : ContinuousOn U (closure W))
    (M : ℝ) (hae : ∀ᵐ x ∂(volume.restrict W), U x ≤ M) :
    ∀ x ∈ closure W, U x ≤ M := by
  have heq : U =ᵐ[volume.restrict W] fun x => min (U x) M := by
    filter_upwards [hae] with x hx
    exact (min_eq_left hx).symm
  have hpoint := Measure.eqOn_open_of_ae_eq heq hW (hU.mono subset_closure)
    ((continuous_id.min continuous_const).comp_continuousOn (hU.mono subset_closure))
  have hclosed : IsClosed (closure W ∩ U ⁻¹' Set.Iic M) :=
    hU.preimage_isClosed_of_isClosed isClosed_closure isClosed_Iic
  have hsub : W ⊆ closure W ∩ U ⁻¹' Set.Iic M := by
    intro x hx
    exact ⟨subset_closure hx, (hpoint hx).trans_le (min_le_right _ _)⟩
  intro x hx
  exact (closure_minimal hsub hclosed hx).2

/-- A continuous weakly harmonic representative is bounded above by its frontier values. -/
theorem le_on_closure_of_unit_harmonic_of_frontier_le
    {d : ℕ} [NeZero d] {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W) (u : H1Function W)
    (hu : IsUnitWeaklyHarmonicOn W u)
    (U : SpatialCoordinates d → ℝ) (hU : ContinuousOn U (closure W))
    (hrep : u.toFun =ᵐ[volume.restrict W] U)
    (M : ℝ) (hbd : ∀ x ∈ frontier W, U x ≤ M) :
    ∀ x ∈ closure W, U x ≤ M := by
  intro x hx
  apply le_of_forall_pos_le_add
  intro eps heps
  have hb : HasBoundaryUpperBoundOn W u (M + eps) :=
    hasBoundaryUpperBoundOn_of_continuous_frontier_lt hW u U hU hrep (M + eps)
      (fun y hy => lt_of_le_of_lt (hbd y hy) (lt_add_of_pos_right M heps))
  have hae : ∀ᵐ y ∂(volume.restrict W), U y ≤ M + eps := by
    filter_upwards [ae_le_of_isUnitWeaklyHarmonicOn hW hu hb, hrep] with y hy hry
    exact hry ▸ hy
  exact le_on_closure_of_continuousOn_of_ae_le hW.isOpen U hU (M + eps) hae x hx

/-- Absolute frontier bounds propagate to the closure for continuous weak harmonic functions. -/
theorem abs_le_on_closure_of_unit_harmonic_of_frontier_le
    {d : ℕ} [NeZero d] {W : Set (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain W) (u : H1Function W)
    (hu : IsUnitWeaklyHarmonicOn W u)
    (U : SpatialCoordinates d → ℝ) (hU : ContinuousOn U (closure W))
    (hrep : u.toFun =ᵐ[volume.restrict W] U)
    (M : ℝ) (hbd : ∀ x ∈ frontier W, |U x| ≤ M) :
    ∀ x ∈ closure W, |U x| ≤ M := by
  have hup := le_on_closure_of_unit_harmonic_of_frontier_le hW u hu U hU hrep M
    (fun x hx => (abs_le.mp (hbd x hx)).2)
  have hrepneg : (-u).toFun =ᵐ[volume.restrict W] fun x => -U x := by
    filter_upwards [hrep] with x hx
    simp only [H1Function.neg_toFun, hx]
  have hlow := le_on_closure_of_unit_harmonic_of_frontier_le hW (-u)
    (isUnitWeaklyHarmonicOn_neg hu) (fun x => -U x) hU.neg hrepneg M
    (fun x hx => neg_le.mpr (abs_le.mp (hbd x hx)).1)
  intro x hx
  exact abs_le.mpr ⟨neg_le.mp (hlow x hx), hup x hx⟩

/-- Two weak harmonic graph representatives satisfy the difference maximum principle from frontier data alone. -/
theorem abs_sub_le_on_closure_of_weakSobolevGraph_frontier
    {d : ℕ} [NeZero d] {W : Opens (SpatialCoordinates d)}
    (hW : IsOpenBoundedConvexDomain (W : Set (SpatialCoordinates d)))
    (v1 v2 : weakSobolevGraph W)
    (hv1 : ∀ psi : killedSobolevGraph W,
      inner ℝ (sobolevGradient v1.val)
        (subspaceGradient (killedSobolevGraph W) psi) = 0)
    (hv2 : ∀ psi : killedSobolevGraph W,
      inner ℝ (sobolevGradient v2.val)
        (subspaceGradient (killedSobolevGraph W) psi) = 0)
    (V1 V2 : SpatialCoordinates d → ℝ)
    (hV1 : ContinuousOn V1 (closure (W : Set (SpatialCoordinates d))))
    (hV2 : ContinuousOn V2 (closure (W : Set (SpatialCoordinates d))))
    (hrep1 : (v1.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (W : Set (SpatialCoordinates d))] V1)
    (hrep2 : (v2.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (W : Set (SpatialCoordinates d))] V2)
    (M : ℝ)
    (hbd : ∀ x ∈ frontier (W : Set (SpatialCoordinates d)), |V1 x - V2 x| ≤ M) :
    ∀ x ∈ closure (W : Set (SpatialCoordinates d)), |V1 x - V2 x| ≤ M := by
  obtain ⟨w1, hw1, hh1⟩ := isWeaklyHarmonicOn_of_weakSobolevGraph_harm v1 hv1
  obtain ⟨w2, hw2, hh2⟩ := isWeaklyHarmonicOn_of_weakSobolevGraph_harm v2 hv2
  have hrep : (w1 - w2).toFun =ᵐ[
      volume.restrict (W : Set (SpatialCoordinates d))] fun x => V1 x - V2 x := by
    filter_upwards [hrep1, hrep2] with x h1 h2
    rw [H1Function.sub_toFun]
    exact congrArg₂ (· - ·) ((congrFun hw1 x).trans h1) ((congrFun hw2 x).trans h2)
  exact abs_le_on_closure_of_unit_harmonic_of_frontier_le hW (w1 - w2)
    (isUnitWeaklyHarmonicOn_sub (isUnitWeaklyHarmonicOn_iff.mpr hh1)
      (isUnitWeaklyHarmonicOn_iff.mpr hh2))
    (fun x => V1 x - V2 x) (hV1.sub hV2) hrep M hbd

end SubdiffusiveProcess
