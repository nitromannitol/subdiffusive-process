module

public import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_chart_compact
public import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_unit_chart_moment
public import SubdiffusiveProcess.Paper.in_deterministic_matrix_bounds
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Localization
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Properties

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Deterministic entry bound: every entry of `sigmaCoarse` is dominated by `LambdaSq`. -/
theorem aux_rm_sigF_abs_le_LamF {d : ℕ} [NeZero d] (Q : Homogenization.TriadicCube d)
    (a : Homogenization.Book.Ch02.TriadicCoeffFamily d) {t : ℝ} (ht : 0 < t) (i j : Fin d) :
    |sigmaCoarse (cubeDomain Q) (a.coeffOn Q) i j| ≤
      LambdaSq Q t (MultiscaleExponent.finite 2) a := by
  have hσpsd : (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)).PosSemidef :=
    posSemidef_of_matLoewnerLE_of_posSemidef_of_isSymm
      (sigmaStarCoarse_posDef (cubeDomain Q) (a.coeffOn Q)).posSemidef
      (sigmaCoarse_isSymm (cubeDomain Q) (a.coeffOn Q))
      (sigmaStarCoarse_le_sigmaCoarse (cubeDomain Q) (a.coeffOn Q))
  have hnorm : matrixNorm (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) ≤
      matrixNorm (bCoarse (cubeDomain Q) (a.coeffOn Q)) :=
    matrixNorm_le_of_matLoewnerLE_of_posSemidef hσpsd
      (bCoarse_posSemidef (cubeDomain Q) (a.coeffOn Q))
      (sigmaCoarse_le_bCoarse (cubeDomain Q) (a.coeffOn Q))
  have hb : coarseBMatrixNorm Q a ≤ LambdaSq Q t (MultiscaleExponent.finite 2) a :=
    oneCube_b_le_LambdaSq Q a ht aux_in_deterministic_matrix_bounds_two_admissible
  have hentry : sigmaCoarse (cubeDomain Q) (a.coeffOn Q) i j ≤
      matrixNorm (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) := by
    rw [matrixNorm_eq_matrixOperatorNorm]
    exact (le_abs_self _).trans (abs_entry_le_matrixOperatorNorm _ i j)
  have hentry' : -sigmaCoarse (cubeDomain Q) (a.coeffOn Q) i j ≤
      matrixNorm (sigmaCoarse (cubeDomain Q) (a.coeffOn Q)) := by
    rw [matrixNorm_eq_matrixOperatorNorm]
    calc -sigmaCoarse (cubeDomain Q) (a.coeffOn Q) i j ≤
        |sigmaCoarse (cubeDomain Q) (a.coeffOn Q) i j| := neg_le_abs _
      _ ≤ _ := abs_entry_le_matrixOperatorNorm _ i j
  rw [abs_le]
  refine ⟨by linarith [hentry'.trans (hnorm.trans hb)], hentry.trans (hnorm.trans hb)⟩

/-- Deterministic entry bound: every entry of `sigmaStarInvCoarse` is dominated by `lambdaSq⁻¹`. -/
theorem aux_rm_sigStarInvF_abs_le_lamF_inv {d : ℕ} [NeZero d] (Q : Homogenization.TriadicCube d)
    (a : Homogenization.Book.Ch02.TriadicCoeffFamily d) {t : ℝ} (ht : 0 < t) (i j : Fin d) :
    |sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q) i j| ≤
      (lambdaSq Q t (MultiscaleExponent.finite 2) a)⁻¹ := by
  have hnorm : coarseSigmaStarInvMatrixNorm Q a ≤ (lambdaSq Q t (MultiscaleExponent.finite 2) a)⁻¹ :=
    oneCube_sigmaStarInv_le_lambdaSq_finite_inv Q a ht (by norm_num)
  have hentry : sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q) i j ≤
      coarseSigmaStarInvMatrixNorm Q a := by
    unfold coarseSigmaStarInvMatrixNorm
    rw [matrixNorm_eq_matrixOperatorNorm]
    exact (le_abs_self _).trans (abs_entry_le_matrixOperatorNorm _ i j)
  have hentry' : -sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q) i j ≤
      coarseSigmaStarInvMatrixNorm Q a := by
    unfold coarseSigmaStarInvMatrixNorm
    rw [matrixNorm_eq_matrixOperatorNorm]
    calc -sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q) i j ≤
        |sigmaStarInvCoarse (cubeDomain Q) (a.coeffOn Q) i j| := neg_le_abs _
      _ ≤ _ := abs_entry_le_matrixOperatorNorm _ i j
  rw [abs_le]
  exact ⟨by linarith [hentry'.trans hnorm], hentry.trans hnorm⟩

theorem aux_rm_moving_chart_bank {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I) (_Perturbation : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Sobolev : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (sigma p : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hp : 1 ≤ p) :
    ∃ deltaS K : ℝ, 0 < deltaS ∧ 0 < K ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ deltaS →
      ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (N : ℕ) (m : ℤ) (_hm : m ≤ (N : ℤ)) (w : SpatialCoordinates d)
        (hr : 0 < (3 : ℝ) ^ (-m)),
      let μ := (chaosSampleLaw M).toMeasure
      let ref : BilateralField d → ℝ := fun omega =>
        aux_g9chart_transport_reference M H N m w omega
      let aN : BilateralField d → PositiveCoefficient (centeredCube w ((3:ℝ)^(-m)) hr) :=
        fun omega => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr
      (MemLp (fun omega => I.lam w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m)) sigma 2 / ref omega)
          (ENNReal.ofReal p) μ ∧
        eLpNorm (fun omega => I.lam w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m)) sigma 2 / ref omega)
          (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K) ∧
      (MemLp (fun omega => I.Lam w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m)) sigma 2 / ref omega)
          (ENNReal.ofReal p) μ ∧
        eLpNorm (fun omega => I.Lam w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m)) sigma 2 / ref omega)
          (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K) ∧
      (MemLp (fun omega => ref omega / I.lam w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m)) sigma 2)
          (ENNReal.ofReal p) μ ∧
        eLpNorm (fun omega => ref omega / I.lam w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m)) sigma 2)
          (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K) ∧
      (∀ i j : Fin d,
        MemLp (fun omega => Homogenization.Book.Ch02.sigmaCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((I.chart w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m))).coeffOn
              (Homogenization.originCube d 0)) i j / ref omega) (ENNReal.ofReal p) μ ∧
        eLpNorm (fun omega => Homogenization.Book.Ch02.sigmaCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((I.chart w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m))).coeffOn
              (Homogenization.originCube d 0)) i j / ref omega) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal K) ∧
      (∀ i j : Fin d,
        MemLp (fun omega => ref omega * Homogenization.Book.Ch02.sigmaStarInvCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((I.chart w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m))).coeffOn
              (Homogenization.originCube d 0)) i j) (ENNReal.ofReal p) μ ∧
        eLpNorm (fun omega => ref omega * Homogenization.Book.Ch02.sigmaStarInvCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((I.chart w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m))).coeffOn
              (Homogenization.originCube d 0)) i j) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal K) := by
  obtain ⟨deltaS, KLam, Klaminv, hdeltaS, hKLam, hKlaminv, hbank⟩ :=
    lem_prefix_limit_g9_unit_chart_moment hd I _Poincare _Extension _Perturbation _Sobolev D
      Cresp hCresp sigma p hsigma hp
  set K : ℝ := max KLam Klaminv with hKdef
  have hKpos : 0 < K := lt_max_of_lt_left hKLam
  refine ⟨deltaS, K, hdeltaS, hKpos, ?_⟩
  intro M hM Rm hRm Sreg _It H hH N m hm w hr μ ref aN
  have hbankM := hbank M hM Rm hRm Sreg _It H hH
  dsimp only at hbankM
  set r : ℝ := (3 : ℝ) ^ (-m) with hrdef
  set Kc : ℕ := ((N : ℤ) - m).toNat with hKcdef
  have hT4 := aux_U2_T4_chart_identity I M H hH N m hm w hr
  have hSmp : MeasurePreserving (aux_g9chart_transport_S m w) μ μ :=
    aux_g9chart_transport_S_measurePreserving M m w
  -- Lam
  set g_Lam : BilateralField d → ℝ := fun omega => aux_U2_LamF sigma
    (aux_U2_unitChart I M H omega Kc) with hg_Lam_def
  have hLam_ae : (fun omega => I.Lam w r hr (aN omega) w r sigma 2 / ref omega) =ᵐ[μ]
      g_Lam ∘ (aux_g9chart_transport_S m w) := by
    filter_upwards [hT4] with omega hscaled
    have hrefpos := aux_g9chart_transport_reference_pos M H N m w omega
    show I.Lam w r hr (aN omega) w r sigma 2 / ref omega =
      aux_U2_LamF sigma (aux_U2_unitChart I M H (aux_g9chart_transport_S m w omega) Kc)
    rw [aux_U2_Lam_eq I w r hr (aN omega) sigma hsigma,
      aux_U2_LamF_scaled sigma (ref omega) hrefpos _ _ hscaled, hKcdef]
    exact mul_div_cancel_left₀ _ hrefpos.ne'
  have hLam_mem_u : MemLp g_Lam (ENNReal.ofReal p) μ := (hbankM Kc).1
  have hLam_norm_u : eLpNorm g_Lam (ENNReal.ofReal p) μ ≤ ENNReal.ofReal KLam :=
    (hbankM Kc).2.1
  have hLam_mem : MemLp (fun omega => I.Lam w r hr (aN omega) w r sigma 2 / ref omega)
      (ENNReal.ofReal p) μ :=
    (memLp_congr_ae hLam_ae).2 (hLam_mem_u.comp_measurePreserving hSmp)
  have hLam_norm : eLpNorm (fun omega => I.Lam w r hr (aN omega) w r sigma 2 / ref omega)
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K := by
    rw [eLpNorm_congr_ae hLam_ae,
      eLpNorm_comp_measurePreserving hLam_mem_u.aestronglyMeasurable hSmp]
    exact hLam_norm_u.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  -- lam⁻¹ (ref / I.lam)
  set g_laminv : BilateralField d → ℝ := fun omega =>
    (aux_U2_lamF sigma (aux_U2_unitChart I M H omega Kc))⁻¹ with hg_laminv_def
  have hlaminv_ae : (fun omega => ref omega / I.lam w r hr (aN omega) w r sigma 2) =ᵐ[μ]
      g_laminv ∘ (aux_g9chart_transport_S m w) := by
    filter_upwards [hT4] with omega hscaled
    have hrefpos := aux_g9chart_transport_reference_pos M H N m w omega
    show ref omega / I.lam w r hr (aN omega) w r sigma 2 =
      (aux_U2_lamF sigma (aux_U2_unitChart I M H (aux_g9chart_transport_S m w omega) Kc))⁻¹
    rw [aux_U2_lam_eq I w r hr (aN omega) sigma hsigma,
      aux_U2_lamF_scaled sigma (ref omega) hrefpos _ _ hscaled, hKcdef]
    have hlamFpos : 0 < aux_U2_lamF sigma
        (aux_U2_unitChart I M H (aux_g9chart_transport_S m w omega) ((N : ℤ) - m).toNat) := by
      unfold aux_U2_unitChart
      rw [← aux_U2_lam_eq I 0 1 one_pos
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (aux_g9chart_transport_S m w omega)
          ((N : ℤ) - m).toNat 0 one_pos) sigma hsigma]
      exact I.lam_pos 0 1 one_pos
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (aux_g9chart_transport_S m w omega)
          ((N : ℤ) - m).toNat 0 one_pos) 0 1 sigma 2
    rw [eq_comm, inv_eq_one_div,
      div_eq_div_iff hlamFpos.ne' (mul_ne_zero hrefpos.ne' hlamFpos.ne'), one_mul]
  have hlaminv_mem_u : MemLp g_laminv (ENNReal.ofReal p) μ := (hbankM Kc).2.2.1
  have hlaminv_norm_u : eLpNorm g_laminv (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Klaminv :=
    (hbankM Kc).2.2.2
  have hlaminv_mem : MemLp (fun omega => ref omega / I.lam w r hr (aN omega) w r sigma 2)
      (ENNReal.ofReal p) μ :=
    (memLp_congr_ae hlaminv_ae).2 (hlaminv_mem_u.comp_measurePreserving hSmp)
  have hlaminv_norm : eLpNorm (fun omega => ref omega / I.lam w r hr (aN omega) w r sigma 2)
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K := by
    rw [eLpNorm_congr_ae hlaminv_ae,
      eLpNorm_comp_measurePreserving hlaminv_mem_u.aestronglyMeasurable hSmp]
    exact hlaminv_norm_u.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  -- sigF entries and sigStarInv entries (both exact, no leftover ref factor)
  have hsigF_bound : ∀ i j : Fin d,
      MemLp (fun omega => Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart w r hr (aN omega) w r).coeffOn (Homogenization.originCube d 0)) i j /
            ref omega) (ENNReal.ofReal p) μ ∧
        eLpNorm (fun omega => Homogenization.Book.Ch02.sigmaCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((I.chart w r hr (aN omega) w r).coeffOn (Homogenization.originCube d 0)) i j /
              ref omega) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K := by
    intro i j
    set g_sigF : BilateralField d → ℝ := fun omega => Homogenization.Book.Ch02.sigmaCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
      ((aux_U2_unitChart I M H omega Kc).coeffOn (Homogenization.originCube d 0)) i j
      with hg_sigF_def
    have hsigF_ae : (fun omega => Homogenization.Book.Ch02.sigmaCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((I.chart w r hr (aN omega) w r).coeffOn (Homogenization.originCube d 0)) i j /
          ref omega) =ᵐ[μ] g_sigF ∘ (aux_g9chart_transport_S m w) := by
      filter_upwards [hT4] with omega hscaled
      have hrefpos := aux_g9chart_transport_reference_pos M H N m w omega
      show Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart w r hr (aN omega) w r).coeffOn (Homogenization.originCube d 0)) i j /
            ref omega =
        Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((aux_U2_unitChart I M H (aux_g9chart_transport_S m w omega) Kc).coeffOn
            (Homogenization.originCube d 0)) i j
      have hkey := aux_U2_sigF_scaled (ref omega) hrefpos
        (aux_U2_unitChart I M H (aux_g9chart_transport_S m w omega) Kc)
        (I.chart w r hr (aN omega) w r) hscaled i j
      rw [hKcdef]
      unfold aux_U2_sigF at hkey
      rw [hkey, mul_div_cancel_left₀ _ hrefpos.ne']
    have hsigF_mem_u : MemLp g_sigF (ENNReal.ofReal p) μ := by
      refine hLam_mem_u.mono' ?_ ?_
      · exact (aux_core_sigmaCoarse_measurable_HOLE_gen hd I M H hH.1 Kc 0 1 one_pos i j
          |>.aestronglyMeasurable : AEStronglyMeasurable g_sigF μ)
      · filter_upwards with omega
        rw [Real.norm_eq_abs]
        exact aux_rm_sigF_abs_le_LamF (Homogenization.originCube d 0)
          (aux_U2_unitChart I M H omega Kc) hsigma.1 i j
    have hsigF_norm_u : eLpNorm g_sigF (ENNReal.ofReal p) μ ≤ ENNReal.ofReal KLam := by
      refine eLpNorm_mono_real hsigF_mem_u.aestronglyMeasurable (fun omega => ?_) |>.trans hLam_norm_u
      rw [Real.norm_eq_abs]
      exact aux_rm_sigF_abs_le_LamF (Homogenization.originCube d 0)
        (aux_U2_unitChart I M H omega Kc) hsigma.1 i j
    refine ⟨(memLp_congr_ae hsigF_ae).2 (hsigF_mem_u.comp_measurePreserving hSmp), ?_⟩
    rw [eLpNorm_congr_ae hsigF_ae,
      eLpNorm_comp_measurePreserving hsigF_mem_u.aestronglyMeasurable hSmp]
    exact hsigF_norm_u.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hsigStarInv_bound : ∀ i j : Fin d,
      MemLp (fun omega => ref omega * Homogenization.Book.Ch02.sigmaStarInvCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart w r hr (aN omega) w r).coeffOn (Homogenization.originCube d 0)) i j)
        (ENNReal.ofReal p) μ ∧
        eLpNorm (fun omega => ref omega * Homogenization.Book.Ch02.sigmaStarInvCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((I.chart w r hr (aN omega) w r).coeffOn (Homogenization.originCube d 0)) i j)
          (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K := by
    intro i j
    set g_sigStarInv : BilateralField d → ℝ := fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse
      (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
      ((aux_U2_unitChart I M H omega Kc).coeffOn (Homogenization.originCube d 0)) i j
      with hg_sigStarInv_def
    have hsigStarInv_ae : (fun omega => ref omega * Homogenization.Book.Ch02.sigmaStarInvCoarse
        (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
        ((I.chart w r hr (aN omega) w r).coeffOn (Homogenization.originCube d 0)) i j) =ᵐ[μ]
        g_sigStarInv ∘ (aux_g9chart_transport_S m w) := by
      filter_upwards [hT4] with omega hscaled
      have hrefpos := aux_g9chart_transport_reference_pos M H N m w omega
      show ref omega * Homogenization.Book.Ch02.sigmaStarInvCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart w r hr (aN omega) w r).coeffOn (Homogenization.originCube d 0)) i j =
        Homogenization.Book.Ch02.sigmaStarInvCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((aux_U2_unitChart I M H (aux_g9chart_transport_S m w omega) Kc).coeffOn
            (Homogenization.originCube d 0)) i j
      have hkey := aux_U2_sigStarInvF_scaled (ref omega) hrefpos
        (aux_U2_unitChart I M H (aux_g9chart_transport_S m w omega) Kc)
        (I.chart w r hr (aN omega) w r) hscaled i j
      rw [hKcdef]
      unfold aux_U2_sigStarInvF at hkey
      rw [hkey, mul_inv_cancel_left₀ hrefpos.ne']
    have hsigStarInv_mem_u : MemLp g_sigStarInv (ENNReal.ofReal p) μ := by
      refine hlaminv_mem_u.mono' ?_ ?_
      · exact (aux_core_sigmaStarInvCoarse_measurable_R_gen hd I M H hH.1 Kc 0 1 one_pos
          (Homogenization.originCube d 0) subset_rfl i j
          |>.aestronglyMeasurable : AEStronglyMeasurable g_sigStarInv μ)
      · filter_upwards with omega
        rw [Real.norm_eq_abs]
        exact aux_rm_sigStarInvF_abs_le_lamF_inv (Homogenization.originCube d 0)
          (aux_U2_unitChart I M H omega Kc) hsigma.1 i j
    have hsigStarInv_norm_u : eLpNorm g_sigStarInv (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Klaminv := by
      refine eLpNorm_mono_real hsigStarInv_mem_u.aestronglyMeasurable (fun omega => ?_) |>.trans hlaminv_norm_u
      rw [Real.norm_eq_abs]
      exact aux_rm_sigStarInvF_abs_le_lamF_inv (Homogenization.originCube d 0)
        (aux_U2_unitChart I M H omega Kc) hsigma.1 i j
    refine ⟨(memLp_congr_ae hsigStarInv_ae).2 (hsigStarInv_mem_u.comp_measurePreserving hSmp), ?_⟩
    rw [eLpNorm_congr_ae hsigStarInv_ae,
      eLpNorm_comp_measurePreserving hsigStarInv_mem_u.aestronglyMeasurable hSmp]
    exact hsigStarInv_norm_u.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  -- lam (I.lam.../ref), via lamF ≤ LamF deterministically, needs lamF's own measurability
  have hlamFAllMeas : Measurable (fun omega => aux_U2_lamF sigma
      (aux_U2_unitChart I M H omega Kc)) := by
    have hcell : ∀ n : ℕ, Measurable (fun omega =>
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (n : ℤ))
          (aux_U2_unitChart I M H omega Kc)) := by
      intro n
      apply aux_measlam_finsetSupReal
      intro R hR
      unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
      apply aux_measlam_matrixNorm
      intro i j
      simpa [aux_U2_unitChart] using
        aux_core_sigmaStarInvCoarse_measurable_R_gen hd I M H hH.1 Kc
          (0 : SpatialCoordinates d) 1 one_pos R
          (Homogenization.openCubeSet_subset_of_mem_descendantsAtScale
            (by simp [Homogenization.originCube]) hR) i j
    have := aux_measlam_lambdaSqFinite (Homogenization.originCube d 0) sigma 2 hsigma.1
      (by norm_num) (fun omega => aux_U2_unitChart I M H omega Kc) hcell
    simpa [aux_U2_lamF, Homogenization.Book.Ch02.lambdaSq] using this
  set g_lam : BilateralField d → ℝ := fun omega =>
    aux_U2_lamF sigma (aux_U2_unitChart I M H omega Kc) with hg_lam_def
  have hlam_ae : (fun omega => I.lam w r hr (aN omega) w r sigma 2 / ref omega) =ᵐ[μ]
      g_lam ∘ (aux_g9chart_transport_S m w) := by
    filter_upwards [hT4] with omega hscaled
    have hrefpos := aux_g9chart_transport_reference_pos M H N m w omega
    show I.lam w r hr (aN omega) w r sigma 2 / ref omega =
      aux_U2_lamF sigma (aux_U2_unitChart I M H (aux_g9chart_transport_S m w omega) Kc)
    rw [aux_U2_lam_eq I w r hr (aN omega) sigma hsigma,
      aux_U2_lamF_scaled sigma (ref omega) hrefpos _ _ hscaled, hKcdef]
    exact mul_div_cancel_left₀ _ hrefpos.ne'
  have hlam_mem_u : MemLp g_lam (ENNReal.ofReal p) μ := by
    refine hLam_mem_u.mono' hlamFAllMeas.aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_pos (by
      have h1 : g_lam omega = I.lam 0 1 one_pos
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega Kc 0 one_pos) 0 1 sigma 2 := by
        rw [hg_lam_def]
        exact (aux_U2_lam_eq I 0 1 one_pos
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega Kc 0 one_pos) sigma hsigma).symm
      rw [h1]
      exact I.lam_pos 0 1 one_pos
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega Kc 0 one_pos) 0 1 sigma 2)]
    exact aux_in_deterministic_matrix_bounds_lam_le_Lam (Homogenization.originCube d 0)
      (aux_U2_unitChart I M H omega Kc) hsigma.1 aux_in_deterministic_matrix_bounds_two_admissible
  have hlam_norm_u : eLpNorm g_lam (ENNReal.ofReal p) μ ≤ ENNReal.ofReal KLam := by
    refine eLpNorm_mono_real hlam_mem_u.aestronglyMeasurable (fun omega => ?_) |>.trans hLam_norm_u
    rw [Real.norm_eq_abs, abs_of_pos (by
      have h1 : g_lam omega = I.lam 0 1 one_pos
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega Kc 0 one_pos) 0 1 sigma 2 := by
        rw [hg_lam_def]
        exact (aux_U2_lam_eq I 0 1 one_pos
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega Kc 0 one_pos) sigma hsigma).symm
      rw [h1]
      exact I.lam_pos 0 1 one_pos
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega Kc 0 one_pos) 0 1 sigma 2)]
    exact aux_in_deterministic_matrix_bounds_lam_le_Lam (Homogenization.originCube d 0)
      (aux_U2_unitChart I M H omega Kc) hsigma.1 aux_in_deterministic_matrix_bounds_two_admissible
  have hlam_mem : MemLp (fun omega => I.lam w r hr (aN omega) w r sigma 2 / ref omega)
      (ENNReal.ofReal p) μ :=
    (memLp_congr_ae hlam_ae).2 (hlam_mem_u.comp_measurePreserving hSmp)
  have hlam_norm : eLpNorm (fun omega => I.lam w r hr (aN omega) w r sigma 2 / ref omega)
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K := by
    rw [eLpNorm_congr_ae hlam_ae,
      eLpNorm_comp_measurePreserving hlam_mem_u.aestronglyMeasurable hSmp]
    exact hlam_norm_u.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  exact ⟨⟨hlam_mem, hlam_norm⟩, ⟨hLam_mem, hLam_norm⟩, ⟨hlaminv_mem, hlaminv_norm⟩,
    hsigF_bound, hsigStarInv_bound⟩



theorem lem_prefix_limit_g9_moving_chart_moment {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (_Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I) (_Perturbation : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Sobolev : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cresp : ℝ) (hCresp : 0 < Cresp) (sigma p : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (hp : 1 ≤ p) :
    ∃ deltaS K : ℝ, 0 < deltaS ∧ 0 < K ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ deltaS →
      ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (N : ℕ) (m : ℤ) (_hm : m ≤ (N : ℤ)) (w : SpatialCoordinates d)
        (hr : 0 < (3 : ℝ) ^ (-m)),
      let μ := (chaosSampleLaw M).toMeasure
      let ref : BilateralField d → ℝ := fun omega =>
        aux_g9chart_transport_reference M H N m w omega
      let aN : BilateralField d → PositiveCoefficient (centeredCube w ((3:ℝ)^(-m)) hr) :=
        fun omega => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr
      (MemLp (fun omega => I.lam w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m)) sigma 2 / ref omega)
          (ENNReal.ofReal p) μ ∧
        eLpNorm (fun omega => I.lam w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m)) sigma 2 / ref omega)
          (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K) ∧
      (MemLp (fun omega => I.Lam w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m)) sigma 2 / ref omega)
          (ENNReal.ofReal p) μ ∧
        eLpNorm (fun omega => I.Lam w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m)) sigma 2 / ref omega)
          (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K) ∧
      (MemLp (fun omega => ref omega / I.lam w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m)) sigma 2)
          (ENNReal.ofReal p) μ ∧
        eLpNorm (fun omega => ref omega / I.lam w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m)) sigma 2)
          (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K) ∧
      (∀ i j : Fin d,
        MemLp (fun omega => Homogenization.Book.Ch02.sigmaCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((I.chart w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m))).coeffOn
              (Homogenization.originCube d 0)) i j / ref omega) (ENNReal.ofReal p) μ ∧
        eLpNorm (fun omega => Homogenization.Book.Ch02.sigmaCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((I.chart w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m))).coeffOn
              (Homogenization.originCube d 0)) i j / ref omega) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal K) ∧
      (∀ i j : Fin d,
        MemLp (fun omega => ref omega * Homogenization.Book.Ch02.sigmaStarInvCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((I.chart w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m))).coeffOn
              (Homogenization.originCube d 0)) i j) (ENNReal.ofReal p) μ ∧
        eLpNorm (fun omega => ref omega * Homogenization.Book.Ch02.sigmaStarInvCoarse
            (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
            ((I.chart w ((3:ℝ)^(-m)) hr (aN omega) w ((3:ℝ)^(-m))).coeffOn
              (Homogenization.originCube d 0)) i j) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal K) := by
  exact aux_rm_moving_chart_bank hd I _Poincare _Extension _Perturbation _Sobolev D Cresp hCresp sigma p hsigma hp

end SubdiffusiveProcess.Paper
