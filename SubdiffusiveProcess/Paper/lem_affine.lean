import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane3.Forms
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Lane4.Carriers
import Homogenization.Book.Ch02.Matrices
import Homogenization.Book.Ch02.MultiscaleEllipticity
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.cutoff_good_scale_input
import SubdiffusiveProcess.Paper.candidate_good_event
import SubdiffusiveProcess.Paper.candidate_good_estimates
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.lem_affine_gcn_competitor
import SubdiffusiveProcess.Paper.cell_catalogue
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.lem_interp
import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Paper.prop_growth
import SubdiffusiveProcess.Paper.conv_represented_estimates
import SubdiffusiveProcess.Paper.conv_represented_sequence
import SubdiffusiveProcess.Paper.cor_energy_measures
import SubdiffusiveProcess.Paper.reference_coefficients
import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
import SubdiffusiveProcess.Paper.order_of_parameters
import SubdiffusiveProcess.Paper.parameter_chain
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.prop_killed_inverse
import SubdiffusiveProcess.Paper.prop_21
import SubdiffusiveProcess.Paper.in_deterministic
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.primitive_scores
import SubdiffusiveProcess.Paper.lem_affine_exponent_limit
import SubdiffusiveProcess.Paper.lem_affine_gap_stmt
import SubdiffusiveProcess.Paper.lem_affine_gap_core

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper




theorem aux_lem_affine_pow_gt_one (H1 : ℕ) (hH1 : 0 < H1) :
    (1 : ℝ) < (3 : ℝ) ^ H1 :=
  one_lt_pow₀ (show (1 : ℝ) < 3 by norm_num) hH1.ne'



theorem aux_lem_affine_gap_bound (gamma : ℝ) (H1 : ℝ)
    (hgamma1 : gamma < 1) (hH1 : (6 : ℝ) / (1 - gamma) < H1) :
    gamma * H1 + 6 < H1 := by
  have hpos : 0 < 1 - gamma := by linarith
  have hdiv := (div_lt_iff₀ hpos).mp hH1
  nlinarith



theorem aux_lem_affine_floor_le (gamma : ℝ) (H1 : ℕ)
    (hgamma0 : 0 ≤ gamma) :
    (Nat.floor (gamma * (H1 : ℝ)) : ℝ) ≤ gamma * (H1 : ℝ) :=
  Nat.floor_le (mul_nonneg hgamma0 (Nat.cast_nonneg H1))



theorem aux_lem_affine_floor_gap (gamma : ℝ) (H1 : ℕ)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1)
    (hH1 : (6 : ℝ) / (1 - gamma) < (H1 : ℝ)) :
    Nat.floor (gamma * (H1 : ℝ)) + 6 < H1 := by
  have hfloor := aux_lem_affine_floor_le gamma H1 hgamma0
  have hgap := aux_lem_affine_gap_bound gamma (H1 : ℝ) hgamma1 hH1
  have h_real : ((Nat.floor (gamma * (H1 : ℝ)) + 6 : ℕ) : ℝ) < (H1 : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h_real



theorem aux_lem_affine_H0_exists (gamma : ℝ) (hgamma0 : 0 < gamma) (hgamma1 : gamma < 1) :
    ∃ H0 : ℕ, ∀ H1 : ℕ, H0 ≤ H1 → 0 < H1 ∧
      (1 : ℝ) < (3 : ℝ) ^ H1 ∧
      Nat.floor (gamma * (H1 : ℝ)) + 6 < H1 := by
  refine ⟨Nat.ceil (6 / (1 - gamma)) + 1, fun H1 hH1 => ?_⟩
  have hH1pos : 0 < H1 := by omega
  have hceil : (6 : ℝ) / (1 - gamma) ≤ (Nat.ceil (6 / (1 - gamma)) : ℝ) := Nat.le_ceil _
  have hH1R : ((Nat.ceil (6 / (1 - gamma)) + 1 : ℕ) : ℝ) ≤ (H1 : ℝ) := by
    exact_mod_cast hH1
  have hgt : (6 : ℝ) / (1 - gamma) < (H1 : ℝ) := by
    push_cast at hH1R
    linarith
  exact ⟨hH1pos, aux_lem_affine_pow_gt_one H1 hH1pos,
    aux_lem_affine_floor_gap gamma H1 hgamma0.le hgamma1 hgt⟩



theorem aux_lem_affine_gridCover_center (d m : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) :
    oddGridCenter z r m (fun _ => (⟨m, by omega⟩ : Fin (2 * m + 1))) = z := by
  funext i; simp [oddGridCenter]



theorem aux_lem_affine_gridCover_powLt (H1 j : ℕ) (hj : j < H1) :
    (3 : ℝ) ^ j < (3 : ℝ) ^ H1 :=
  pow_lt_pow_right₀ (by norm_num : 1 < (3 : ℝ)) hj



theorem aux_lem_affine_gridCover_radiusLt (H1 j : ℕ) (parentSide : ℝ)
    (hparentSide : 0 < parentSide) (hpow : (3 : ℝ) ^ j < (3 : ℝ) ^ H1) :
    (3 : ℝ) ^ j * (parentSide / (3 : ℝ) ^ H1) / 2 < parentSide / 2 := by
  have hH1pos : (0 : ℝ) < (3 : ℝ) ^ H1 := by positivity
  rw [div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)]
  rw [← mul_div_assoc, div_lt_iff₀ hH1pos]
  nlinarith



theorem aux_lem_affine_gridCover (d H1 : ℕ) (gamma parentSide : ℝ)
    (hgap : Nat.floor (gamma * (H1 : ℝ)) + 4 < H1)
    (hparentSide : 0 < parentSide) (zParent : SpatialCoordinates d) :
    ∃ idx : OddGridIndex d (Lane3.subdivisionHalfWidth H1),
      oddGridCenter zParent parentSide (Lane3.subdivisionHalfWidth H1) idx
        = zParent ∧
      Metric.closedBall
        (oddGridCenter zParent parentSide (Lane3.subdivisionHalfWidth H1) idx)
        ((3 : ℝ) ^ (Nat.floor (gamma * (H1 : ℝ)) + 4) *
          (parentSide / (3 : ℝ) ^ H1) / 2)
        ⊆ Metric.ball zParent (parentSide / 2) := by
  refine ⟨fun _ =>
    (⟨Lane3.subdivisionHalfWidth H1, by omega⟩ :
      Fin (2 * Lane3.subdivisionHalfWidth H1 + 1)), ?_, ?_⟩
  · exact aux_lem_affine_gridCover_center d (Lane3.subdivisionHalfWidth H1)
      zParent parentSide
  · rw [aux_lem_affine_gridCover_center d (Lane3.subdivisionHalfWidth H1)
      zParent parentSide]
    exact Metric.closedBall_subset_ball
      (aux_lem_affine_gridCover_radiusLt H1
        (Nat.floor (gamma * (H1 : ℝ)) + 4) parentSide hparentSide
        (aux_lem_affine_gridCover_powLt H1
          (Nat.floor (gamma * (H1 : ℝ)) + 4) hgap))



theorem aux_lem_affine_moreover_eq (d : ℕ) (hd : 2 ≤ d) (beta : ℝ)
    (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1) :
    affineExponent (d : ℝ) 1 beta 1 0 = -((1 - beta) / (1 + (d : ℝ) / 2)) :=
  (lem_affine_exponent_limit d hd beta hbeta hbeta1).1



theorem aux_lem_affine_moreover_neg (d : ℕ) (hd : 2 ≤ d) (beta : ℝ)
    (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1) :
    affineExponent (d : ℝ) 1 beta 1 0 < 0 :=
  (lem_affine_exponent_limit d hd beta hbeta hbeta1).2.1



theorem aux_lem_affine_moreover_tendsto (d : ℕ) (hd : 2 ≤ d) (beta : ℝ)
    (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1) :
    Tendsto
      (fun v : ℝ × (ℝ × ℝ) => affineExponent (d : ℝ) v.1 beta v.2.1 v.2.2)
      (nhdsWithin ((1 : ℝ), ((1 : ℝ), (0 : ℝ)))
        {v : ℝ × (ℝ × ℝ) |
          beta < v.1 ∧ v.1 < 1 ∧ 0 < v.2.1 ∧ v.2.1 < 1 ∧ 0 < v.2.2})
      (𝓝 (-((1 - beta) / (1 + (d : ℝ) / 2)))) :=
  (lem_affine_exponent_limit d hd beta hbeta hbeta1).2.2.1



theorem aux_lem_affine_moreover_exists (d : ℕ) (hd : 2 ≤ d) (beta : ℝ)
    (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1) :
    ∃ a g z0 : ℝ,
      beta < a ∧ a < 1 ∧ 0 < g ∧ g < 1 ∧ 0 < z0 ∧
        affineExponent (d : ℝ) a beta g z0 < 0 :=
  (lem_affine_exponent_limit d hd beta hbeta hbeta1).2.2.2



theorem aux_lem_affine_moreover (d : ℕ) (hd : 2 ≤ d) (beta : ℝ)
    (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1) :
    (affineExponent (d : ℝ) 1 beta 1 0 =
        -((1 - beta) / (1 + (d : ℝ) / 2)) ∧
      affineExponent (d : ℝ) 1 beta 1 0 < 0 ∧
      Tendsto
        (fun v : ℝ × (ℝ × ℝ) =>
          affineExponent (d : ℝ) v.1 beta v.2.1 v.2.2)
        (nhdsWithin ((1 : ℝ), ((1 : ℝ), (0 : ℝ)))
          {v : ℝ × (ℝ × ℝ) |
            beta < v.1 ∧ v.1 < 1 ∧ 0 < v.2.1 ∧ v.2.1 < 1 ∧ 0 < v.2.2})
        (𝓝 (-((1 - beta) / (1 + (d : ℝ) / 2)))) ∧
      ∃ a g z0 : ℝ,
        beta < a ∧ a < 1 ∧ 0 < g ∧ g < 1 ∧ 0 < z0 ∧
        affineExponent (d : ℝ) a beta g z0 < 0) :=
  ⟨aux_lem_affine_moreover_eq d hd beta hbeta hbeta1,
    aux_lem_affine_moreover_neg d hd beta hbeta hbeta1,
    aux_lem_affine_moreover_tendsto d hd beta hbeta hbeta1,
    aux_lem_affine_moreover_exists d hd beta hbeta hbeta1⟩



theorem aux_lem_affine_factor_cancel (s Sq rExp : ℝ) (hs : s ≠ 0)
    (hRexp : rExp ≠ 0) :
    s * rExp * (rExp⁻¹ * Sq / s) = Sq := by
  field_simp



theorem aux_lem_affine_vartheta_range (d : ℝ) (alpha beta : ℝ)
    (hd : 0 ≤ d) (hba : beta < alpha) (hbpos : 0 < beta) :
    0 < (alpha - beta) / (alpha + d / 2) ∧
      (alpha - beta) / (alpha + d / 2) < 1 := by
  have halpha : 0 < alpha := lt_trans hbpos hba
  have hden : 0 < alpha + d / 2 := by linarith
  constructor
  · exact div_pos (by linarith) hden
  · rw [div_lt_one hden]; linarith



theorem aux_lem_affine_vartheta_exponent_eq (d alpha beta gamma zeta : ℝ) :
    ((alpha - beta) / (alpha + d / 2)) *
        ((d + zeta) / 2 - gamma * (d - 2) / 2 - 2 * gamma) +
      (1 - (alpha - beta) / (alpha + d / 2)) *
        ((d + zeta) / 2 - gamma * (d - 2) / 2 - alpha * gamma)
      = affineExponent d alpha beta gamma zeta := by
  unfold affineExponent; ring



theorem aux_lem_affine_quantitative_core (d : ℕ) (hd : 2 ≤ d)
    (alpha beta gamma zeta : ℝ) (hba : beta < alpha) (hbpos : 0 < beta) :
    (0 < (alpha - beta) / (alpha + (d : ℝ) / 2) ∧
        (alpha - beta) / (alpha + (d : ℝ) / 2) < 1) ∧
      ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
          ((d + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - 2 * gamma) +
        (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) *
          ((d + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - alpha * gamma)
        = affineExponent (d : ℝ) alpha beta gamma zeta := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  exact ⟨aux_lem_affine_vartheta_range (d : ℝ) alpha beta hd0 hba hbpos,
    aux_lem_affine_vartheta_exponent_eq (d : ℝ) alpha beta gamma zeta⟩



theorem aux_lem_affine_h_choose_L (e_d rho C : ℝ) (he_d : e_d < 0) (hrho : 0 < rho)
    (hC : 0 < C) :
    ∃ L0 : ℝ, 1 < L0 ∧ ∀ L : ℝ, L0 ≤ L → C * L ^ (2 * e_d) ≤ rho / 4 := by
  have hy : 0 < -(2 * e_d) := by linarith
  have h_tendsto : Tendsto (fun (x : ℝ) => x ^ (2 * e_d)) atTop (𝓝 (0 : ℝ)) := by
    simpa [neg_neg] using tendsto_rpow_neg_atTop hy
  have h_tendsto_mul : Tendsto (fun (x : ℝ) => C * x ^ (2 * e_d)) atTop (𝓝 (C * (0 : ℝ))) :=
    h_tendsto.const_mul C
  simp [mul_zero] at h_tendsto_mul
  have h_metric := (Metric.tendsto_atTop.mp h_tendsto_mul) (rho / 4) (by linarith)
  rcases h_metric with ⟨L0', hL0'⟩
  refine ⟨max L0' 2, by
    have h2 : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le h2 (le_max_right _ _), ?_⟩
  intro L hL
  have hL_L0' : L0' ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : (2 : ℝ) ≤ L := le_trans (le_max_right _ _) hL
  have h_dist : dist (C * L ^ (2 * e_d)) (0 : ℝ) < rho / 4 := hL0' L hL_L0'
  rw [Real.dist_eq, sub_zero] at h_dist
  have h_nonneg : 0 ≤ C * L ^ (2 * e_d) := by
    have hL_nonneg : 0 ≤ L := by linarith
    have h_rpow_nonneg : 0 ≤ L ^ (2 * e_d) := Real.rpow_nonneg hL_nonneg _
    exact mul_nonneg (by linarith) h_rpow_nonneg
  rw [abs_of_nonneg h_nonneg] at h_dist
  exact le_of_lt h_dist



theorem aux_lem_affine_h_source_decay (K c eta rho : ℝ) (hc : 0 < c) (hK : 0 ≤ K)
    (heta : eta < 2) (hrho : 0 < rho) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 →
      K * c ^ (-(1 : ℝ) / 2) * r ^ (1 - eta / 2) ≤ rho / 4 := by
  by_cases hKzero : K = 0
  · subst hKzero
    refine ⟨1, by norm_num, fun r _ _ => ?_⟩
    simp
    positivity
  · have hKpos : 0 < K := by
      by_contra! h_notpos
      have h_eq : K = 0 := by linarith
      exact hKzero h_eq
    have hc_inv_pos : 0 < c ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hc _
    set A := K * c ^ (-(1 : ℝ) / 2) with hA_def
    have hA_pos : 0 < A := mul_pos hKpos hc_inv_pos
    have hs_pos : 0 < 1 - eta / 2 := by linarith
    have h_cont : ContinuousAt (fun (r : ℝ) => r ^ (1 - eta / 2)) 0 :=
      Real.continuousAt_rpow_const 0 (1 - eta / 2) (.inr (by linarith))
    have h_tendsto : Tendsto (fun (r : ℝ) => r ^ (1 - eta / 2)) (𝓝 0) (𝓝 0) := by
      simpa [Real.zero_rpow hs_pos.ne'] using h_cont.tendsto
    have h_tendsto_mul : Tendsto (fun (r : ℝ) => A * r ^ (1 - eta / 2)) (𝓝 0) (𝓝 (A * 0)) :=
      h_tendsto.const_mul A
    simp [mul_zero] at h_tendsto_mul
    have h_metric := (Metric.tendsto_nhds.mp h_tendsto_mul) (rho / 4) (by linarith)
    have h_mem : {r : ℝ | dist (A * r ^ (1 - eta / 2)) 0 < rho / 4} ∈ 𝓝 (0 : ℝ) := h_metric
    rcases Metric.mem_nhds_iff.mp h_mem with ⟨ε, hε, h_ball⟩
    refine ⟨ε / 2, by linarith, ?_⟩
    intro r hr_pos hr_le
    have hr_lt_ε : r < ε := by linarith
    have hr_mem_ball : r ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr_pos]
      linarith
    have h_dist_lt : dist (A * r ^ (1 - eta / 2)) 0 < rho / 4 := h_ball hr_mem_ball
    rw [Real.dist_eq, sub_zero] at h_dist_lt
    have h_pos : 0 < A * r ^ (1 - eta / 2) := by
      have h_rpow_pos : 0 < r ^ (1 - eta / 2) := Real.rpow_pos_of_pos hr_pos _
      exact mul_pos hA_pos h_rpow_pos
    rw [abs_of_pos h_pos] at h_dist_lt
    simpa [hA_def] using le_of_lt h_dist_lt



theorem aux_lem_affine_h_glb_witness (eSet : Set ℝ) (hne : eSet.Nonempty)
    (hnonneg : ∀ e ∈ eSet, 0 ≤ e) (bound : ℝ) (hwitness : ∃ e ∈ eSet, e ≤ bound) :
    ∃ Lambda : ℝ, IsGLB eSet Lambda ∧ eSet.Nonempty ∧ Lambda ≤ bound := by
  have h_bdd_below : BddBelow eSet := by
    refine ⟨0, ?_⟩
    intro e he
    exact hnonneg e he
  set Lambda := sInf eSet with hLambda_def
  have h_isGLB : IsGLB eSet Lambda := Real.isGLB_sInf hne h_bdd_below
  have h_Lambda_le_bound : Lambda ≤ bound := by
    rcases hwitness with ⟨e, he, he_bound⟩
    have h_sInf_le_e : Lambda ≤ e := csInf_le h_bdd_below he
    exact le_trans h_sInf_le_e he_bound
  exact ⟨Lambda, h_isGLB, hne, h_Lambda_le_bound⟩



theorem aux_lem_affine_h_trace_rep_boundary (d : ℕ) (hd : 2 ≤ d)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (S : ResponseSpace (centeredCube Qcentre Qside hQside))
    (hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
    (a : PositiveCoefficient (centeredCube Qcentre Qside hQside))
    (Lf : S.space →L[ℝ] ℝ)
    (U : SpatialCoordinates d → ℝ)
    (hUcont : ContinuousOn U (closure (centeredCube Qcentre Qside hQside :
      Set (SpatialCoordinates d))))
    (hUae : ((responseSolution S a Lf).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) :
    ∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
      U x = 0 := by
  let Q := centeredCube Qcentre Qside hQside
  have hQ_open : IsOpen (Q : Set (SpatialCoordinates d)) := Q.isOpen
  have hQ_closed : IsClosed (closure (Q : Set (SpatialCoordinates d))) :=
    isClosed_closure
  let w := (responseSolution S a Lf).val
  have hw_mem : w ∈ killedSobolevGraph Q := by
    rw [← hS]
    exact Subtype.mem (responseSolution S a Lf)
  have hUae' : (w.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U := hUae
  -- Build a globally continuous extension V of U via Tietze
  let f : C(closure (Q : Set (SpatialCoordinates d)), ℝ) :=
    ⟨fun x => U x, by
      rw [continuousOn_iff_continuous_restrict] at hUcont
      exact hUcont⟩
  obtain ⟨V, hVrestrict⟩ := ContinuousMap.exists_restrict_eq hQ_closed f
  have hV_on_closure : ∀ x, x ∈ closure (Q : Set (SpatialCoordinates d)) → V x = U x := by
    intro x hx
    have h_eq := congrArg (fun (g : C(closure (Q : Set (SpatialCoordinates d)), ℝ)) => g ⟨x, hx⟩) hVrestrict
    simpa [f] using h_eq
  have hUV_on_Q : U =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V := by
    filter_upwards [self_mem_ae_restrict hQ_open.measurableSet] with x hx
    exact (hV_on_closure x (subset_closure hx)).symm
  have hV_on_Q : (w.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V :=
    hUae'.trans hUV_on_Q
  have hV_cont : Continuous V := V.continuous
  have h_boundary_zero := killed_continuous_boundary_zero d Qcentre Qside hQside w hw_mem V
    hV_cont hV_on_Q
  intro x hx_frontier
  have h_frontier_eq : frontier (Q : Set (SpatialCoordinates d)) = (closure (Q : Set (SpatialCoordinates d))) \ (Q : Set (SpatialCoordinates d)) :=
    hQ_open.frontier_eq
  rw [h_frontier_eq] at hx_frontier
  have hx_closed : x ∈ (closedCube Qcentre Qside hQside : Set (SpatialCoordinates d)) := by
    have hx_closure : x ∈ closure (Q : Set (SpatialCoordinates d)) := hx_frontier.1
    have h_closure_eq : closure (Q : Set (SpatialCoordinates d)) = (closedCube Qcentre Qside hQside : Set (SpatialCoordinates d)) := by
      -- Q is centeredCube, which is Metric.ball z (r/2); closure = Metric.closedBall = closedCube
      have hpos : Qside / 2 ≠ 0 := by linarith
      calc
        closure (Q : Set (SpatialCoordinates d)) = closure (Metric.ball (Qcentre : SpatialCoordinates d) (Qside / 2)) := rfl
        _ = Metric.closedBall (Qcentre : SpatialCoordinates d) (Qside / 2) := closure_ball (Qcentre : SpatialCoordinates d) hpos
        _ = (closedCube Qcentre Qside hQside : Set (SpatialCoordinates d)) := rfl
    rw [h_closure_eq] at hx_closure
    exact hx_closure
  have hx_notin_Q : x ∉ (Q : Set (SpatialCoordinates d)) := hx_frontier.2
  have hx_closure : x ∈ closure (Q : Set (SpatialCoordinates d)) := hx_frontier.1
  have hVx_zero := h_boundary_zero x hx_closed hx_notin_Q
  rw [← hV_on_closure x hx_closure]
  exact hVx_zero



theorem aux_lem_affine_h_trace_rep (d : ℕ) (hd : 2 ≤ d)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside) (hQside1 : Qside ≤ 1)
    (S : ResponseSpace (centeredCube Qcentre Qside hQside))
    (hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
    (a : PositiveCoefficient (centeredCube Qcentre Qside hQside))
    (Lf : S.space →L[ℝ] ℝ)
    (Cp : Lane4.CampanatoInput d)
    (alpha : ℝ) (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (K : ℝ) (hK : 0 ≤ K)
    (hdecay : ∀ x ∈ centeredCube Qcentre Qside hQside, ∀ rad : ℝ, 0 < rad → rad ≤ Qside →
        ∫ y in Metric.ball x rad ∩ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
            ((responseSolution S a Lf).val.1 y -
                setAverage (Metric.ball x rad ∩
                  (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
                  (responseSolution S a Lf).val.1) ^ 2
            ∂volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) ≤
          K ^ 2 * rad ^ (2 * alpha) *
            volume.real (Metric.ball x rad ∩
              (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))) :
    ∃ U : SpatialCoordinates d → ℝ,
      ContinuousOn U (closure (centeredCube Qcentre Qside hQside :
        Set (SpatialCoordinates d))) ∧
      (((responseSolution S a Lf).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) ∧
      (∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
        U x = 0) := by
  obtain ⟨U, hUcont, hUae, -, -⟩ :=
    Cp.holder_of_campanato alpha halpha0 halpha1 Qcentre Qside hQside hQside1
      (responseSolution S a Lf).val.1 K hK hdecay
  refine ⟨U, hUcont.continuousOn, hUae, ?_⟩
  exact aux_lem_affine_h_trace_rep_boundary d hd Qcentre Qside hQside S hS a Lf U
    hUcont.continuousOn hUae



theorem aux_lem_affine_h_holder_bound (d : ℕ) (hd : 2 ≤ d)
    (Cp : Lane4.CampanatoInput d)
    (alpha : ℝ) (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (u : DomainL2 (centeredCube z r hr))
    (K : ℝ) (hK : 0 ≤ K)
    (hdecay : ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad → rad ≤ r →
        ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
            (u y - setAverage (Metric.ball x rad ∩
                (centeredCube z r hr : Set (SpatialCoordinates d))) u) ^ 2
            ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
          K ^ 2 * rad ^ (2 * alpha) *
            volume.real (Metric.ball x rad ∩
              (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] U) ∧
      Lane4.IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U := by
  obtain ⟨U, hUcont, hUae, hHolder, -⟩ :=
    Cp.holder_of_campanato alpha halpha0 halpha1 z r hr hr1 u K hK hdecay
  exact ⟨U, hUcont, hUae, hHolder⟩







theorem lem_affine
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_Step : Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (D : Paper.lane4_deterministic_good_scale_input d) (Cp : Lane4.CampanatoInput d)
    (beta : ℝ) (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1) :
    (∀ (alpha gamma zeta rho s sigma cell : ℝ)
    (hba : beta < alpha) (halpha : alpha < 1)
    (hgamma : 0 < gamma) (hgamma1 : gamma < 1) (hzeta : 0 < zeta)
    (hrho : 0 < rho)
    (hneg : affineExponent (d : ℝ) alpha beta gamma zeta < 0)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hsSmall : s ≤ (1 / 32 : ℝ))
    (hsigma_eq : sigma = (beta - 1 / 2) / 4)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hcell : cell ∈ Set.Ioo (0 : ℝ) 1)
    (cbuf k0 : ℕ),
    ∃ H0 : ℕ, ∀ H1 : ℕ, H0 ≤ H1 → 0 < H1 ∧
      (let L : ℝ := (3 : ℝ) ^ H1
       (1 : ℝ) < L ∧
       Nat.floor (gamma * (H1 : ℝ)) + 6 < H1 ∧
       (∀ (parentSide : ℝ), 0 < parentSide → ∀ zParent : SpatialCoordinates d,
         ∃ idx : OddGridIndex d (subdivisionHalfWidth H1),
           oddGridCenter zParent parentSide (subdivisionHalfWidth H1) idx = zParent ∧
           Metric.closedBall
             (oddGridCenter zParent parentSide (subdivisionHalfWidth H1) idx)
             ((3 : ℝ) ^ (Nat.floor (gamma * (H1 : ℝ)) + 4) *
               (parentSide / L) / 2) ⊆ Metric.ball zParent (parentSide / 2)) ∧
       ∃ epshom : ℝ, ∃ (_hepshom : 0 < epshom),
       ∃ Cbound eps0 lam0 delta0 : ℝ,
         (1 : ℝ) ≤ Cbound ∧ 0 < eps0 ∧ 0 < lam0 ∧ 0 < delta0 ∧
         ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
           (H : BilateralField d → C(SpatialCoordinates d, ℝ))
           (hMH : InfraredCharacterization M H)
           (Rm : Paper.in_responses d M)
           (Sreg : Paper.in_6_16 d M)
           (_It : Paper.in_iteration d M I Sreg)
           (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
           (field : Ω → BilateralField d)
           (hfieldMeas : Measurable field)
           (hfieldLaw : Measure.map field P = (chaosSampleLaw M).toMeasure)
           (env : PUnit → ℕ → Ω → BilateralField d)
           (hEnvMeas : ∀ (a : PUnit) (n : ℕ), Measurable (env a n))
           (hEnvLaw : ∀ (a : PUnit) (n : ℕ),
             Measure.map (env a n) P = (chaosSampleLaw M).toMeasure)
           (hEnvConv : ∀ᵐ omega ∂P, ∀ a : PUnit,
             Tendsto (fun n => env a n omega) atTop (𝓝 (field omega))),
           M.delta ≤ delta0 →
           ∀ (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
             (S : ResponseSpace (centeredCube Qcentre Qside hQside))
             (hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
             (GN : ℕ → BilateralField d →
               DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
                 DomainL2 (centeredCube Qcentre Qside hQside))
             (hGN : ∀ N omega f, GN N omega f =
               (responseSolution S
                 (Lane4.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                 ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
             (phi : ℕ → ℕ) (hphi : StrictMono phi)
             (RootIndex : Type) [Countable RootIndex] [DecidableEq RootIndex]
             (root0 : RootIndex)
             (zCat : RootIndex → SpatialCoordinates d) (rCat : RootIndex → ℝ)
             (hrCat : ∀ j, 0 < rCat j)
             (SCat : ∀ j, ResponseSpace (centeredCube (zCat j) (rCat j) (hrCat j)))
             (DCat : ∀ j,
               Submodule ℚ (DomainL2 (centeredCube (zCat j) (rCat j) (hrCat j))))
             [hDCatc : ∀ j, Countable (DCat j)]
             (fCat : ∀ j, (DCat j) → SpatialCoordinates d → ℝ)
             (TCat : RootIndex → Type) [hTCatc : ∀ j, Countable (TCat j)]
             (thetaCat : ∀ j, TCat j → SpatialCoordinates d → ℝ)
             (thetaH1Cat : ∀ j, TCat j →
               Homogenization.H1Function
                 (centeredCube (zCat j) (rCat j) (hrCat j) : Set (SpatialCoordinates d)))
             (usrc : PUnit → ∀ j, (DCat j) → ℕ → Ω → (SCat j).space)
             (srcRep : PUnit → ∀ j, (DCat j) → ℕ → Ω → SpatialCoordinates d → ℝ)
             (ucell : PUnit → ∀ j, TCat j → ℕ → Ω →
               Homogenization.H1Function
                 (centeredCube (zCat j) (rCat j) (hrCat j) : Set (SpatialCoordinates d)))
             (Cext : ℝ) (etaCat : ℝ) (t : ℝ) (orders : Finset ℝ)
             (Index : Type) [Countable Index]
             (resp : PUnit → Index → ℕ → Ω → ℝ)
             (respLim : PUnit → Index → Ω → ℝ)
             (constants : PUnit → Index → ℕ → Ω → ℝ) (Gcat : Set Ω)
             (coercivityKey extensionKey lambdaKey : RootIndex → Index)
             (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (DCat j) → Index)
             (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, TCat j → Index)
             (Grid : Type) [Countable Grid]
             (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → RootIndex)
             (gridKey : Grid → Index)
             (hRootCatalogue : zCat root0 = Qcentre ∧ rCat root0 = Qside)
             (hRep : ∀ a : PUnit,
               conv_represented_estimates d hd M H Ω P phi (env a)
                 RootIndex root0 zCat rCat hrCat SCat DCat fCat TCat thetaCat
                 thetaH1Cat (usrc a) (srcRep a) (ucell a) Cext beta alpha etaCat t
                 orders I Index (resp a) (respLim a) (constants a) Gcat
                 coercivityKey extensionKey lambdaKey sourceResponseKey
                 sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
                 cellHolderKey Grid origin gridRoot gridKey)
             (GE : Ω → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
               DomainL2 (centeredCube Qcentre Qside hQside))
             (hGE : ∀ᵐ omega ∂P,
               Tendsto (fun n => GN (phi n) (env PUnit.unit n omega)) atTop (𝓝 (GE omega)))
             (E : Ω → DirichletForm.ClosedForm
               (volume.restrict
                 (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
             (hE : ∀ omega u, (E omega).energy u = limitFormEnergy (GE omega) u)
             (GammaE : ∀ omega : Ω, DirichletForm.EnergyMeasure (E omega))
             (eRef : ℕ → ℝ)
             (heRefPos : ∀ k : ℕ, 0 < eRef k)
             (heRefLim : ∀ k : ℕ,
               Tendsto (fun n : ℕ =>
                 (let kappa : ℕ → ℝ := fun J =>
                    Real.exp (((J : ℝ) + 1) *
                      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
                      SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
                  kappa (((phi n : ℤ) - (k : ℤ)).toNat) / kappa (phi n)))
                 atTop (𝓝 (eRef k)))
             (c : ℝ) (hc : 0 < c),
           let Q : Opens (SpatialCoordinates d) := centeredCube Qcentre Qside hQside
           ∀ (J : ℕ) (gridChoice : Fin J → Grid)
             (hGridChoice : ∀ j, gridRoot (gridChoice j) = root0),
           let origins : Fin J → SpatialCoordinates d := fun j => origin (gridChoice j)
           ∃ baseMesh : Ω → (SpatialCoordinates d → ℝ) → ℝ,
           (∀ᵐ omega ∂P,
             ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
               0 < baseMesh omega f) ∧
           ∀ (n : ℕ) (z zP : SpatialCoordinates d) (gridIndex : Fin J)
             (parentIndex : Fin d → ℤ)
             (idx : OddGridIndex d (subdivisionHalfWidth H1)),
             (let k : ℕ := H1 * (n + 1)
              let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
              let q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
              let parentCell : Set (SpatialCoordinates d) := Metric.ball zP (L * r / 2)
              zP = (fun i => origins gridIndex i + (L * r) * ((parentIndex i : ℝ))) →
              z = oddGridCenter zP (L * r) (subdivisionHalfWidth H1) idx →
              parentCell ⊆ (Q : Set (SpatialCoordinates d)) →
              ∀ (qside : ℝ)
                (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
                (qcenter : SpatialCoordinates d)
                (hqcenter : qcenter = z)
                (Enl Shift Cmp : Type)
                [Fintype Enl] [Fintype Shift] [Fintype Cmp]
                (selfE : Enl) (selfShift : Shift)
                (qRoot : Enl × Shift)
                (hqRoot : qRoot = (selfE, selfShift))
                (factor : Enl → ℕ)
                (hfactor : factor selfE = 0)
                (padE : Enl) (hpad : factor padE = 1)
                (shift : Shift → SpatialCoordinates d)
                (hshift : shift selfShift = 0)
                (rootLevel : Enl × Shift → ℤ)
                (hrootLevel : ∀ (e : Enl) (t : Shift),
                  rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
                (rootSide : Enl × Shift → ℝ)
                (hrootSide : ∀ (U : Enl × Shift),
                  rootSide U = (3 : ℝ) ^ (-rootLevel U))
                (rootCentre : Enl × Shift → SpatialCoordinates d)
                (hrootCentre : ∀ (e : Enl) (t : Shift),
                  rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
                (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
                (hGridCover : ∀ (x : SpatialCoordinates d),
                  x ∈ Metric.closedBall z (qside / 2) →
                  ∀ rho : ℝ, 0 < rho → rho ≤ qside →
                    ∃ (U : Enl × Shift) (D : ℕ)
                      (w : Fin D → OddGridIndex d 1),
                      Metric.ball x (rho / 2) ⊆
                        Metric.ball
                          (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                          (descendantSide 1 D (rootSide U) / 2) ∧
                      descendantSide 1 D (rootSide U) ≤ 9 * rho)
                (parent : Cmp → Enl × Shift)
                (depth : Cmp → ℕ)
                (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
                (cmpCentre : Cmp → SpatialCoordinates d)
                (hcmpCentre : ∀ (c : Cmp),
                  cmpCentre c =
                    descendantCenter 1 (rootCentre (parent c))
                      (rootSide (parent c)) (depth c) (word c))
                (cmpLevel : Cmp → ℤ)
                (hcmpLevel : ∀ (c : Cmp),
                  cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
                (cmpSide : Cmp → ℝ)
                (hcmpSide : ∀ (c : Cmp),
                  cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
                (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
                (chosen : Cmp)
                (hcmpChosenCentre : cmpCentre chosen = z)
                (hcmpChosenLevel : cmpLevel chosen =
                  (k : ℤ) - (Nat.floor (gamma * (H1 : ℝ)) : ℤ) - 4)
                (hcmpChosenPad : Metric.closedBall z (cmpSide chosen / 2) ⊆
                  parentCell)
                (observationCentre :
                  ∀ (U : Enl × Shift) (D : ℕ),
                    ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
                      SpatialCoordinates d)
                (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
                  (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
                  observationCentre U D code =
                    Sum.elim
                      (fun w => descendantCenter 1 (rootCentre U)
                        (rootSide U) D w)
                      (fun V => rootCentre V) code)
                (eta : ℕ → BilateralField d →
                  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
                (hEta : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                  ∀ (N i : ℕ) (y : Vec d),
                    eta N omega i y =
                      omega ((i : ℤ) - (N : ℤ))
                        (((3 : ℝ) ^ (-(N : ℤ))) • y)))
                (F Praw Rraw Draw :
                  ℕ → ℕ → Vec d → BilateralField d → ENNReal)
                (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
                (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
                (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
                (hepsSmall : eps ≤ eps0)
                (hPrimitive : (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                  ∀ N : ℕ,
                    primitive_scores d M s eps (eta N omega)
                      (fun m y => F N m y omega)
                      (fun m y => Praw N m y omega)
                      (fun m y => Rraw N m y omega)
                      (fun m y => Draw N m y omega)
                      (fun m y => Z N m y omega)
                      (fun m y => rawGood N m y omega)))
                (lambdaCut lambdaLim lambdaDet cdet : ℝ)
                (hThresholds :
                  0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
                  lambdaLim < lambdaDet ∧ lambdaDet < 1)
                (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
                (hlamSmall : lambdaDet ≤ lam0)
                (prefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
                  ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
                    BilateralField d → ℝ)
                (prefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
                  ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
                    BilateralField d → ℝ)
                (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
                  (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
                  (omega : BilateralField d),
                  prefixZ N U D code omega =
                    if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
                      ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                        (rootLevel U + (D : ℤ)),
                        if 0 ≤ (N : ℤ) - j then
                          Z N ((N : ℤ) - j).toNat
                            (((3 : ℝ) ^ N) • observationCentre U D code)
                            omega
                        else 0
                    else 0)
                (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
                  (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
                  (omega : BilateralField d),
                  prefixD N U D code omega =
                    if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
                      ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                        (rootLevel U + (D : ℤ)),
                        if 0 ≤ (N : ℤ) - j then
                          (Draw N ((N : ℤ) - j).toNat
                            (((3 : ℝ) ^ N) • observationCentre U D code)
                            omega).toReal
                        else 0
                    else 0)
                (hFiniteScoreGuard :
                  (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                  ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
                    (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
                    rootLevel U + (D : ℤ) ≤ (N : ℤ) →
                    ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                      (rootLevel U + (D : ℤ)),
                      Draw N ((N : ℤ) - j).toNat
                        (((3 : ℝ) ^ N) • observationCentre U D code)
                        omega ≠ ⊤))
                (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
                (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
                  (omega : BilateralField d),
                  sN N l w omega =
                    if l ≤ (N : ℤ) then
                      (let kappa : ℕ → ℝ := fun J =>
                        Real.exp (((J : ℝ) + 1) *
                          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
                          SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
                       let retained :
                         ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                         fun ell v beta =>
                           if 0 ≤ ell then
                             ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                           else
                             -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
                       kappa ((N : ℤ) - l).toNat / kappa N *
                         Real.exp (H omega w + retained l w omega))
                    else 1)
                (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
                (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift)
                  (omega : BilateralField d),
                  ellLoN N U omega =
                    I.lam (rootCentre U) (rootSide U) (rootPos U)
                      (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient
                        M H omega N (rootCentre U) (rootPos U))
                      (rootCentre U) (rootSide U) sigma 2 /
                      sN N (rootLevel U) (rootCentre U) omega)
                (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift)
                  (omega : BilateralField d),
                  ellHiN N U omega =
                    I.Lam (rootCentre U) (rootSide U) (rootPos U)
                      (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient
                        M H omega N (rootCentre U) (rootPos U))
                      (rootCentre U) (rootSide U) sigma 2 /
                      sN N (rootLevel U) (rootCentre U) omega)
                (AEN : ℕ → Enl × Shift → BilateralField d →
                  Matrix (Fin d) (Fin d) ℝ)
                (hAEN : ∀ (N : ℕ) (U : Enl × Shift)
                  (omega : BilateralField d),
                  AEN N U omega =
                    (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
                      Homogenization.Book.Ch02.sigmaCoarse
                        (Homogenization.Book.Ch02.cubeDomain
                          (Homogenization.originCube d 0))
                        ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                          (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient
                            M H omega N (rootCentre U) (rootPos U))
                          (rootCentre U) (rootSide U)).coeffOn
                          (Homogenization.originCube d 0)))
                (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
                (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
                  errN N c omega =
                    I.err (cmpCentre c) (cmpSide c) (cmpPos c)
                      (SubdiffusiveProcess.Lane4.cutoffPositiveCoefficient
                        M H omega N (cmpCentre c) (cmpPos c))
                      (cmpCentre c) (cmpSide c)
                      (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
                (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
                  ratioN N c omega =
                    sN N (k : ℤ) qcenter omega /
                      sN N (cmpLevel c) (cmpCentre c) omega)
                (sE : Ω → ℝ)
                (sCmp : Cmp → Ω → ℝ)
                (hsE : (∀ᵐ omega ∂P,
                    0 < sE omega ∧
                    Tendsto (fun n => sN (phi n) (k : ℤ) z (env PUnit.unit n omega))
                      atTop (𝓝 (sE omega))) ∧
                  (∀ᵐ omega ∂P,
                    sE omega = eRef k *
                      Real.exp (H (field omega) z +
                        ∑ j ∈ Finset.range k, (field omega) (-(j : ℤ)) z)))
                (hsCmp : ∀ᵐ omega ∂P,
                  ∀ c' : Cmp,
                    0 < sCmp c' omega ∧
                    Tendsto
                      (fun n => sN (phi n) (cmpLevel c') (cmpCentre c')
                        (env PUnit.unit n omega))
                      atTop (𝓝 (sCmp c' omega)))
                (prefixZLim : ∀ (U : Enl × Shift) (D : ℕ),
                  ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) → Ω → ℝ)
                (prefixDLim : ∀ (U : Enl × Shift) (D : ℕ),
                  ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) → Ω → ℝ)
                (ellLoLim ellHiLim : (Enl × Shift) → Ω → ℝ)
                (AE_Lim : (Enl × Shift) → Ω → Matrix (Fin d) (Fin d) ℝ)
                (errLim ratioLim : Cmp → Ω → ℝ)
                (hPrefixZLim : ∀ (U : Enl × Shift) (D : ℕ)
                  (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
                  TendstoInMeasure P
                    (fun n omega =>
                      prefixZ (phi n) U D code (env PUnit.unit n omega))
                    atTop (prefixZLim U D code))
                (hPrefixDLim : ∀ (U : Enl × Shift) (D : ℕ)
                  (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
                  TendstoInMeasure P
                    (fun n omega =>
                      prefixD (phi n) U D code (env PUnit.unit n omega))
                    atTop (prefixDLim U D code))
                (hEllLoLim : ∀ (U : Enl × Shift),
                  TendstoInMeasure P
                    (fun n omega => ellLoN (phi n) U (env PUnit.unit n omega)) atTop
                    (ellLoLim U))
                (hEllHiLim : ∀ (U : Enl × Shift),
                  TendstoInMeasure P
                    (fun n omega => ellHiN (phi n) U (env PUnit.unit n omega)) atTop
                    (ellHiLim U))
                (hAELim : ∀ (U : Enl × Shift) (i j : Fin d),
                  TendstoInMeasure P
                    (fun n omega => AEN (phi n) U (env PUnit.unit n omega) i j) atTop
                    (fun omega => AE_Lim U omega i j))
                (hErrLim : ∀ (c : Cmp),
                  TendstoInMeasure P
                    (fun n omega => errN (phi n) c (env PUnit.unit n omega)) atTop
                    (errLim c))
                (hRatioLim : ∀ (c : Cmp),
                  TendstoInMeasure P
                    (fun n omega => ratioN (phi n) c (env PUnit.unit n omega)) atTop
                    (ratioLim c))
                (hRootsQ : ∀ U : Enl × Shift,
                  closure
                    (centeredCube (rootCentre U) (rootSide U)
                      (rootPos U) : Set (SpatialCoordinates d)) ⊆
                    (Q : Set (SpatialCoordinates d))),
                let Good : Set Ω :=
                  {omega |
                    (∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
                      ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                        prefixZLim U D code omega < lambdaLim * (D : ℝ) ∧
                        prefixDLim U D code omega < lambdaLim * (D : ℝ)) ∧
                    (∀ U : Enl × Shift,
                      cell ≤ ellLoLim U omega ∧ ellHiLim U omega ≤ cell⁻¹) ∧
                    errLim chosen omega ≤ epshom * cdet ∧
                    (∀ c : Cmp, ratioLim c omega ∈ Set.Ioo (1 / 2 : ℝ) 2)}
                ∀ᵐ omega ∂P,
                  ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
                  ∀ (fL2 : DomainL2 Q),
                    ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                      (Q : Set (SpatialCoordinates d))] f) →
                    (let u := GE omega fL2
                     ∃ U : SpatialCoordinates d → ℝ,
                       ContinuousOn U (closure (Q : Set (SpatialCoordinates d))) ∧
                       ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                         (Q : Set (SpatialCoordinates d))] U) ∧
                       (∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), U x = 0) ∧
                       (r ≤ baseMesh omega f → omega ∈ Good →
                         Lane4.IsHolderOn alpha (closure q) U ∧
                         (let lambda : Set (SpatialCoordinates d) → ℝ :=
                            fun A => ((GammaE omega).measure u A).toReal +
                              c * (volume A).toReal
                          lambda parentCell ≤
                            L ^ ((d : ℝ) + zeta) * lambda q →
                          ∃ pc : (Fin d → ℝ) × ℝ,
                            (let ell : SpatialCoordinates d → ℝ :=
                               fun x => (∑ i, pc.1 i * x i) + pc.2
                             let b : SpatialCoordinates d → ℝ :=
                               fun x => U x - ell x
                             let eSet : Set ℝ :=
                               {e : ℝ |
                                 ∃ (v : DomainL2 Q)
                                   (V : SpatialCoordinates d → ℝ),
                                   v ∈ (E omega).domain ∧
                                   ContinuousOn V
                                     (closure (Q : Set (SpatialCoordinates d))) ∧
                                   ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                                     (Q : Set (SpatialCoordinates d))] V) ∧
                                   (∀ x ∈ frontier q, V x = b x) ∧
                                   e = ((GammaE omega).measure v q).toReal}
                             ∃ Lambda : ℝ,
                               IsGLB eSet Lambda ∧
                               eSet.Nonempty ∧
                               Lambda ≤ rho * lambda q))))))) ∧
    (affineExponent (d : ℝ) 1 beta 1 0 =
        -((1 - beta) / (1 + (d : ℝ) / 2)) ∧
      affineExponent (d : ℝ) 1 beta 1 0 < 0 ∧
      Tendsto
        (fun v : ℝ × (ℝ × ℝ) =>
          affineExponent (d : ℝ) v.1 beta v.2.1 v.2.2)
        (nhdsWithin ((1 : ℝ), ((1 : ℝ), (0 : ℝ)))
          {v : ℝ × (ℝ × ℝ) |
            beta < v.1 ∧ v.1 < 1 ∧ 0 < v.2.1 ∧ v.2.1 < 1 ∧ 0 < v.2.2})
        (𝓝 (-((1 - beta) / (1 + (d : ℝ) / 2)))) ∧
      ∃ a g z0 : ℝ,
        beta < a ∧ a < 1 ∧ 0 < g ∧ g < 1 ∧ 0 < z0 ∧
        affineExponent (d : ℝ) a beta g z0 < 0) := by
  constructor
  · intro alpha gamma zeta rho s sigma cell hba halpha hgamma hgamma1 hzeta hrho hneg hs hsSmall hsigma_eq hsigma hcell cbuf k0
    obtain ⟨H0a, hH0a⟩ := aux_lem_affine_H0_exists gamma hgamma hgamma1
    obtain ⟨H0b, hH0b⟩ := lem_affine_gap_core d hd I _X _Sob _Step _MeyersMorrey Pin D Cp beta
      hbeta hbeta1 alpha gamma zeta rho s sigma cell hba halpha hgamma hgamma1 hzeta hrho hneg hs
      hsSmall hsigma_eq hsigma hcell cbuf k0
    refine ⟨max H0a H0b, fun H1 hH1 => ?_⟩
    obtain ⟨hH1pos, hLgt1, hfloorgap⟩ := hH0a H1 (le_trans (le_max_left _ _) hH1)
    have hgap4 : Nat.floor (gamma * (H1 : ℝ)) + 4 < H1 := by omega
    refine ⟨hH1pos, hLgt1, hfloorgap, ?_, ?_⟩
    · exact fun parentSide hps zParent =>
        aux_lem_affine_gridCover d H1 gamma parentSide hgap4 hps zParent
    · obtain ⟨epshom, hepshom, Cbound, eps0, lam0, delta0, hC1, he0, hl0, hd0, hstmt⟩ :=
        hH0b H1 (le_trans (le_max_right _ _) hH1) hfloorgap
      exact ⟨epshom, hepshom, Cbound, eps0, lam0, delta0, hC1, he0, hl0, hd0, hstmt⟩
  · exact aux_lem_affine_moreover d hd beta hbeta hbeta1

end Paper
