import SubdiffusiveProcess.Paper.killed_continuous_boundary_zero
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Sobolev.DirichletResponse

/-! Extracted local form data for the relative concentration proof.
This module proves the stated deterministic implications; it does not construct random bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set Topology TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4 Homogenization SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace Paper
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- The Dirichlet `C^{1/2}` estimate, in the form `lem_as_regularity` gives it, for one
coefficient. -/
def aux_prop_conc_form_cutoff_continuity_DirProp (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
    (a : PositiveCoefficient (centeredCube z s hs)) (K : ℝ) : Prop :=
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
    AEMeasurable F (volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))) →
    (∀ᵐ x ∂(volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
    ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
      ContDiff ℝ 2 phi →
      c2Norm (closedCube z s hs : Set (SpatialCoordinates d)) phi ≤ Cphi →
      ∀ (b u : weakSobolevGraph (centeredCube z s hs)),
        ((b : SobolevData (centeredCube z s hs)).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))] phi →
        SolvesDirichlet a F b u →
        ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
          ((u : SobolevData (centeredCube z s hs)).1 : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))] U ∧
          IsHolderOn (1 / 2) (closedCube z s hs : Set (SpatialCoordinates d)) U ∧
          cAlphaNorm (1 / 2) (closedCube z s hs : Set (SpatialCoordinates d)) U ≤
            K * (Kf + Cphi)

/-- The `C²` norm of the zero function on a nonempty set vanishes (copied from
`torsion_bound`). -/
theorem aux_prop_conc_form_cutoff_continuity_c2Norm_zero (S : Set (SpatialCoordinates d))
    (hS : S.Nonempty) : c2Norm S (fun _ => (0 : ℝ)) ≤ 0 := by
  have h1 : {v : ℝ | ∃ x ∈ S, v = |(fun _ : SpatialCoordinates d => (0 : ℝ)) x|} = {0} := by
    ext v; simp only [abs_zero, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, _, hv⟩; exact hv
    · intro hv; obtain ⟨x, hx⟩ := hS; exact ⟨x, hx, hv⟩
  have hd1 : fderiv ℝ (fun _ : SpatialCoordinates d => (0 : ℝ)) = 0 := by
    funext x; simp only [fderiv_fun_const, Pi.zero_apply]
  have hd2 : fderiv ℝ (fderiv ℝ (fun _ : SpatialCoordinates d => (0 : ℝ))) = 0 := by
    rw [hd1]; funext x; simp only [fderiv_zero, Pi.zero_apply]
  have h2 : {v : ℝ | ∃ x ∈ S, v = ‖fderiv ℝ (fun _ : SpatialCoordinates d => (0 : ℝ)) x‖} =
      {0} := by
    rw [hd1]
    ext v; simp only [Pi.zero_apply, norm_zero, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, _, hv⟩; exact hv
    · intro hv; obtain ⟨x, hx⟩ := hS; exact ⟨x, hx, hv⟩
  have h3 : {v : ℝ | ∃ x ∈ S,
      v = ‖fderiv ℝ (fderiv ℝ (fun _ : SpatialCoordinates d => (0 : ℝ))) x‖} = {0} := by
    rw [hd2]
    ext v; simp only [Pi.zero_apply, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, _, hv⟩; rw [hv]; exact ContinuousLinearMap.opNorm_zero
    · intro hv; obtain ⟨x, hx⟩ := hS
      exact ⟨x, hx, by rw [hv]; exact ContinuousLinearMap.opNorm_zero.symm⟩
  unfold c2Norm
  rw [h1, h2, h3, csSup_singleton]
  norm_num

/-- Pointwise Hölder bound (Euclidean form) from a finite `C^{1/2}` norm on a compact set. -/
theorem aux_prop_conc_form_cutoff_continuity_holder_pt (S : Set (SpatialCoordinates d)) (hS : IsCompact S)
    (U : SpatialCoordinates d → ℝ) (hU : Continuous U) (C : ℝ)
    (hH : IsHolderOn (1 / 2) S U) (hC : cAlphaNorm (1 / 2) S U ≤ C) :
    ∀ x ∈ S, ∀ y ∈ S,
      |U x - U y| ≤ C * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ (1 / 2 : ℝ) := by
  intro x hx y hy
  have hA : BddAbove {v : ℝ | ∃ x ∈ S, v = |U x|} := by
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hU.continuousOn
    refine ⟨B, ?_⟩
    rintro v ⟨w, hw, rfl⟩
    have := hB w hw
    rwa [Real.norm_eq_abs] at this
  have hA0 : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |U x|} :=
    (abs_nonneg (U x)).trans (le_csSup hA ⟨x, hx, rfl⟩)
  have hsemi : holderSeminorm (1 / 2) S U ≤ C := by
    unfold cAlphaNorm at hC
    linarith only [hC, hA0]
  by_cases hxy : x = y
  · subst hxy
    have : (Real.sqrt (∑ j : Fin d, (x j - x j) ^ 2)) = 0 := by simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, Real.sqrt_zero]
    rw [sub_self, abs_zero, this, Real.zero_rpow (by norm_num), mul_zero]
  · have hpos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      rw [Real.sqrt_pos]
      by_contra hle
      push_neg at hle
      apply hxy
      funext j
      have h0 : ∑ j : Fin d, (x j - y j) ^ 2 = 0 :=
        le_antisymm hle (Finset.sum_nonneg (fun j _ => sq_nonneg _))
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j - y j))).1 h0 j
        (Finset.mem_univ j)
      have h2 : x j - y j = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      exact sub_eq_zero.mp h2
    have hden : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hpos _
    have hmem : |U x - U y| / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ (1 / 2 : ℝ) ∈
        holderRatioSet (1 / 2) S U := ⟨x, hx, y, hy, hxy, rfl⟩
    have hle : |U x - U y| / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ (1 / 2 : ℝ) ≤
        holderSeminorm (1 / 2) S U := le_csSup hH hmem
    have h1 : |U x - U y| ≤ holderSeminorm (1 / 2) S U *
        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ (1 / 2 : ℝ) := by
      rwa [div_le_iff₀ hden] at hle
    exact h1.trans (mul_le_mul_of_nonneg_right hsemi hden.le)

/-- The closure of the open cube is the corresponding closed cube. -/
theorem aux_prop_conc_form_cutoff_continuity_closure_cube (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    closure (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (closedCube z r hr : Set (SpatialCoordinates d)) := by
  change closure (Metric.ball z (r / 2)) = Metric.closedBall z (r / 2)
  exact closure_ball z (half_pos hr).ne'

/-- The sup distance is at most the Euclidean distance. -/
theorem aux_prop_conc_form_cutoff_continuity_dist_le_euclid (x y : SpatialCoordinates d) :
    dist x y ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
  refine (dist_pi_le_iff (Real.sqrt_nonneg _)).mpr fun j => ?_
  rw [Real.dist_eq]
  refine Real.abs_le_sqrt ?_
  exact Finset.single_le_sum (f := fun j => (x j - y j) ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ j)

/-- **Killed solutions of bounded sources are continuous up to the boundary and vanish there**
(the `lem_as_regularity` Dirichlet estimate with zero datum + `killed_continuous_boundary_zero`;
adapted from `torsion_bound`). -/
theorem aux_prop_conc_form_cutoff_continuity_killed_holder (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (K : ℝ)
    (hD : Paper.aux_prop_conc_form_cutoff_continuity_DirProp z r hr a K)
    (F0 : SpatialCoordinates d → ℝ) (hF0 : Measurable F0) (MF : ℝ) (hMF : 0 ≤ MF)
    (hF0b : ∀ x, |F0 x| ≤ MF)
    (v : killedSobolevGraph (centeredCube z r hr))
    (hv : ∀ w : killedSobolevGraph (centeredCube z r hr), sobolevCoefficientForm a v.val w.val =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        F0 x * (w : SobolevData (centeredCube z r hr)).1 x) :
    ∃ vc : SpatialCoordinates d → ℝ, Continuous vc ∧
      (((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc) ∧
      (∀ x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)), vc x = 0) ∧
      (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∀ y ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          |vc x - vc y| ≤ (K * MF) * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ (1 / 2 : ℝ)) := by
  classical
  let u : weakSobolevGraph (centeredCube z r hr) :=
    ⟨v.val, killedSobolevGraph_le_weakSobolevGraph v.property⟩
  have hsolve : SolvesDirichlet a F0 0 u := by
    refine ⟨?_, ?_⟩
    · have : ((u : SobolevData (centeredCube z r hr)) -
          ((0 : weakSobolevGraph (centeredCube z r hr)) : SobolevData (centeredCube z r hr))) =
          (v : SobolevData (centeredCube z r hr)) := by
        simp only [ZeroMemClass.coe_zero, sub_zero, u]
      rw [this]
      exact v.property
    · intro ψ
      exact hv ψ
  have hb : (((0 : weakSobolevGraph (centeredCube z r hr)) :
      SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun _ => (0 : ℝ)) := by
    have h0 : (((0 : weakSobolevGraph (centeredCube z r hr)) :
        SobolevData (centeredCube z r hr)).1) = 0 := rfl
    rw [h0]
    exact Lp.coeFn_zero _ _ _
  have hne : (closedCube z r hr : Set (SpatialCoordinates d)).Nonempty :=
    ⟨z, Metric.mem_closedBall_self (half_pos hr).le⟩
  obtain ⟨U, hUc, hUae, hUhol, hUnorm⟩ := hD F0 MF hMF hF0.aemeasurable
    (Eventually.of_forall hF0b)
    (fun _ => (0 : ℝ)) 0 contDiff_const (Paper.aux_prop_conc_form_cutoff_continuity_c2Norm_zero _ hne) 0 u hb hsolve
  rw [add_zero] at hUnorm
  have hbd : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0 := by
    intro x hx
    have hxc : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
      rw [← Paper.aux_prop_conc_form_cutoff_continuity_closure_cube z r hr]
      exact frontier_subset_closure hx
    have hxo : x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      rw [(centeredCube z r hr).isOpen.frontier_eq] at hx
      exact hx.2
    exact killed_continuous_boundary_zero d z r hr v.val v.property U hUc hUae x hxc hxo
  have hcont : Continuous (fun x => if x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
      then U x else 0) := by
    refine continuous_if ?_ hUc.continuousOn continuous_const.continuousOn
    intro x hx
    exact hbd x hx
  have hvcU : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      (if x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) then U x else 0) = U x := by
    intro x hx
    by_cases hxQ : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
    · rw [if_pos hxQ]
    · rw [if_neg hxQ]
      have : x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)) := by
        rw [(centeredCube z r hr).isOpen.frontier_eq]
        exact ⟨hx, hxQ⟩
      exact (hbd x this).symm
  refine ⟨fun x => if x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) then U x else 0,
    hcont, ?_, ?_, ?_⟩
  · filter_upwards [hUae, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
      with x hx hxQ
    rw [hx]
    exact (hvcU x (subset_closure hxQ)).symm
  · intro x hx
    change (if x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) then U x else 0) = 0
    rw [if_neg hx]
  · intro x hx y hy
    change |(if x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) then U x else 0) -
      (if y ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) then U y else 0)| ≤ _
    rw [hvcU x hx, hvcU y hy]
    have hcomp : IsCompact (closedCube z r hr : Set (SpatialCoordinates d)) :=
      (closedCube z r hr).isCompact
    rw [Paper.aux_prop_conc_form_cutoff_continuity_closure_cube] at hx hy
    exact Paper.aux_prop_conc_form_cutoff_continuity_holder_pt _ hcomp U hUc (K * MF) hUhol hUnorm x hx y hy



theorem prop_conc_form_cutoff_continuity (_hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr)) (K : ℝ) (_hK : 0 ≤ K)
    (hD : ∀ N, Paper.aux_prop_conc_form_cutoff_continuity_DirProp z r hr (a N) K)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ (n : ℕ) (f : DomainL2 (centeredCube z r hr)), GN n f =
      (responseSolution (killedResponseSpace hP) (a n)
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1)
    (f : DomainL2 (centeredCube z r hr))
    (fc : SpatialCoordinates d → ℝ) (hfs : ContDiff ℝ (⊤ : ℕ∞) fc)
    (_hfc : HasCompactSupport fc)
    (hfae : (f : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc)
    (MF : ℝ) (hMF : 0 ≤ MF) (hfb : ∀ x, |fc x| ≤ MF) :
    ∀ N, ∃ vc : SpatialCoordinates d → ℝ, Continuous vc ∧
      ((GN N f : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc ∧
      (∀ x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)), vc x = 0) ∧
      (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∀ y ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          |vc x - vc y| ≤ (K * MF) * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ (1 / 2 : ℝ)) := by
  -- weak equation of each response
  have hweak : ∀ N (w : killedSobolevGraph (centeredCube z r hr)),
      sobolevCoefficientForm (a N)
          (responseSolution (killedResponseSpace hP) (a N)
            ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val w.val =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          fc x * (w : SobolevData (centeredCube z r hr)).1 x := by
    intro N w
    have h := responseSolution_spec (killedResponseSpace hP) (a N)
      ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL) w
    rw [responseForm_apply] at h
    rw [sobolevCoefficientForm_apply, h, ContinuousLinearMap.comp_apply, sobolevVolumeLoad_apply]
    refine integral_congr_ae ?_
    filter_upwards [hfae] with x hx
    rw [hx]
    rfl
  intro N
  have := Paper.aux_prop_conc_form_cutoff_continuity_killed_holder z r hr (a N) K (hD N) fc
    hfs.continuous.measurable MF hMF hfb
    ⟨(responseSolution (killedResponseSpace hP) (a N)
      ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val,
      (responseSolution (killedResponseSpace hP) (a N)
      ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).property⟩
    (hweak N)
  rw [hGN]
  exact this

end Paper
