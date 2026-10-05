module

public import SubdiffusiveProcess.Paper.lfgc_root_base

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Zero-disorder tail of the root statistic

`rootX_tail`: at small disorder, uniformly in the cutoff, root level and centre,
`P(t < aux_lfgc_root_impl_rootX H) ≤ #coords · (C δ^c / (t/K)²)^p`.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02 SubdiffusiveProcess
open scoped ENNReal

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_lfgc_root_tail_measurable_reference (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ) (m : ℤ)
    (w : SpatialCoordinates d) :
    Measurable (fun omega => _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference M H N m w omega) := by
  unfold _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_retained
  have hev : ∀ j : ℤ, Measurable (fun omega : BilateralField d => omega j w) := fun j =>
    (continuous_eval_const w).measurable.comp (measurable_pi_apply j)
  refine measurable_const.mul (Real.measurable_exp.comp ?_)
  refine ((continuous_eval_const w).measurable.comp hH).add ?_
  by_cases hm : 0 ≤ m
  · simp only [hm, ite_true]
    exact Finset.measurable_sum _ fun j _ => hev (-j)
  · simp only [hm, ite_false]
    exact (Finset.measurable_sum _ fun j _ => hev (-j)).neg

/-- A real that is at most one: the squared threshold dominates the linear one. -/
theorem aux_lfgc_root_tail_div_sq_ge_div {B s : ℝ} (hB : 0 ≤ B) (hs : 0 < s) (hs1 : s ≤ 1) : B / s ≤ B / s ^ 2 := by
  apply div_le_div_of_nonneg_left hB (by positivity)
  nlinarith

end SubdiffusiveProcess.Paper
namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_lfgc_root_tail_rpow_le_rpow_of_small {δ c c' : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hcc : c ≤ c') :
    δ ^ c' ≤ δ ^ c :=
  Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hcc

/-- The four base moment bounds of the unit chart, with common constants. -/
theorem lfgc_root_tail (hd : 2 ≤ d) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I) (Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (Perturbation : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sobolev : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d) (Cresp : ℝ) (hCresp : 0 < Cresp)
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℝ, 1 ≤ p → ∃ delta0 C : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ 0 ≤ C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ K : ℕ,
        eLpNorm (fun omega => (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma
            (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_unitChart I M H omega K))⁻¹ - 1)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * M.delta ^ c) ∧
        eLpNorm (fun omega => _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF sigma
            (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_unitChart I M H omega K) - 1)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * M.delta ^ c) ∧
        eLpNorm (fun omega => aux_lfgc_base_moments_probeSeries sigma (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_unitChart I M H omega K))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * M.delta ^ c) ∧
        ∀ a b : Fin d,
          eLpNorm (fun omega => _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_sigF a b
              (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_unitChart I M H omega K) - (if a = b then (1 : ℝ) else 0))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * M.delta ^ c) := by
  obtain ⟨a1, c1, ha1, hc1, w1, hw1, h1⟩ := _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_invlam_core d hd I Poincare Extension
    Perturbation Sobolev D Cresp hCresp sigma hsigma
  obtain ⟨c2, hc2, h2⟩ := aux_lfgc_base_moments_base_Lam_dev hd I Poincare Extension Perturbation Sobolev D Cresp hCresp
    sigma hsigma
  obtain ⟨c3, hc3, h3⟩ := lfgc_base_moments hd I Poincare Extension Perturbation Sobolev D Cresp hCresp
    sigma hsigma
  obtain ⟨a4, c4, ha4, hc4, w4, hw4, h4⟩ := _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_cellE d hd I Poincare Extension
    Perturbation Sobolev D Cresp hCresp
  set c := min (min c1 c2) (min c3 c4)
  have hc : 0 < c := lt_min (lt_min hc1 hc2) (lt_min hc3 hc4)
  refine ⟨c, hc, fun p hp => ?_⟩
  obtain ⟨δ1, C1, hδ1, hC1, g1⟩ := h1 p hp
  obtain ⟨δ2, C2, hδ2, hC2, g2⟩ := h2 p hp
  obtain ⟨δ3, C3, hδ3, hC3, g3⟩ := h3 p hp
  obtain ⟨δ4, C4, hδ4, hC4, g4⟩ := h4 1 one_pos p hp
  refine ⟨min (min (min δ1 δ2) (min δ3 δ4)) 1, max (max C1 C2) (max C3 C4),
    lt_min (lt_min (lt_min hδ1 hδ2) (lt_min hδ3 hδ4)) one_pos, min_le_right _ _,
    le_max_of_le_left (le_max_of_le_left hC1), ?_⟩
  intro M hM Rm hRm Sreg It H hH K
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδ1' : M.delta ≤ 1 := hM.trans (min_le_right _ _)
  have hMδ : M.delta ≤ min (min δ1 δ2) (min δ3 δ4) := hM.trans (min_le_left _ _)
  set C := max (max C1 C2) (max C3 C4)
  have key : ∀ (Ci ci : ℝ), 0 ≤ Ci → Ci ≤ C → c ≤ ci →
      ENNReal.ofReal (Ci * M.delta ^ ci) ≤ ENNReal.ofReal (C * M.delta ^ c) := by
    intro Ci ci hCi hCiC hcci
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul hCiC (aux_lfgc_root_tail_rpow_le_rpow_of_small hδpos hδ1' hcci)
      (Real.rpow_nonneg hδpos.le _) (hCi.trans hCiC)
  refine ⟨?_, ?_, ?_, fun a b => ?_⟩
  · exact (g1 M (hMδ.trans ((min_le_left _ _).trans (min_le_left _ _))) Rm hRm Sreg It H hH K).2.1.trans
      (key C1 c1 hC1 (le_max_of_le_left (le_max_left _ _))
        ((min_le_left _ _).trans (min_le_left _ _)))
  · exact (g2 M (hMδ.trans ((min_le_left _ _).trans (min_le_right _ _))) Rm hRm Sreg It H hH K).trans
      (key C2 c2 hC2 (le_max_of_le_left (le_max_right _ _))
        ((min_le_left _ _).trans (min_le_right _ _)))
  · exact (g3 M (hMδ.trans ((min_le_right _ _).trans (min_le_left _ _))) Rm hRm Sreg It H hH K).trans
      (key C3 c3 hC3 (le_max_of_le_right (le_max_left _ _))
        ((min_le_right _ _).trans (min_le_left _ _)))
  · have hmem : Homogenization.originCube d 0 ∈ _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_D (d := d) 0 := by
      rw [_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_D_eq]; simp [Homogenization.descendantsAtDepth]
    have := (g4 M (hMδ.trans ((min_le_right _ _).trans (min_le_right _ _))) Rm hRm Sreg It H hH K 0
      _ hmem a b).2.2.1
    have e : (3 : ℝ) ^ ((1 : ℝ) * ((0 : ℕ) : ℝ)) = 1 := by simp
    rw [e, mul_one] at this
    exact this.trans (key C4 c4 hC4 (le_max_of_le_right (le_max_right _ _))
        ((min_le_right _ _).trans (min_le_right _ _)))

end SubdiffusiveProcess.Paper
