module

public import SubdiffusiveProcess.Paper.lfgc_root_tail

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Tail of each selected root coordinate, and of the root statistic

At small disorder, uniformly in `N, n, z` and the root, each selected coordinate satisfies
`P(s < |coord|) ≤ (C δ^c / s²)^p` for `0 < s ≤ 1`; hence
`P(t < aux_lfgc_root_impl_rootX H) ≤ T (3 + d²) (C δ^c / (tθ₀/2)²)^p`.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02 SubdiffusiveProcess
open scoped ENNReal

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_lfgc_root_tail2_ennreal_div_rpow_le {B s : ℝ} (_hB : 0 ≤ B) (hs : 0 < s) (hs1 : s ≤ 1) {p : ℝ} (hp : 0 ≤ p) :
    (ENNReal.ofReal B / ENNReal.ofReal s) ^ p ≤ (ENNReal.ofReal B / ENNReal.ofReal (s ^ 2)) ^ p := by
  apply ENNReal.rpow_le_rpow _ hp
  apply ENNReal.div_le_div_left
  exact ENNReal.ofReal_le_ofReal (by nlinarith)

/-- Tail of one selected coordinate of lem_band's root vector. -/
theorem lfgc_root_tail2 (hd : 2 ≤ d) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I) (Extension : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (Perturbation : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Sobolev : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (D : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d) (Cresp : ℝ) (hCresp : 0 < Cresp)
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℝ, 1 ≤ p → ∃ delta0 C : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ 0 ≤ C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ (T : ℕ) (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) (N : ℕ) (n : ℤ)
        (z : SpatialCoordinates d), (∀ i : Fin T, n + offset i ≤ (N : ℤ)) →
      ∀ (q : Fin T × aux_lfgc_root_stat_SelIdx d) (s : ℝ), 0 < s → s ≤ 1 →
        (chaosSampleLaw M).toMeasure
          {omega | s < |aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega) q|} ≤
          (ENNReal.ofReal (C * M.delta ^ c) / ENNReal.ofReal (s ^ 2)) ^ p := by
  obtain ⟨c, hc, hbase⟩ := lfgc_root_tail hd I Poincare Extension Perturbation Sobolev D Cresp hCresp
    sigma hsigma
  refine ⟨c, hc, fun p hp => ?_⟩
  obtain ⟨δ0, C, hδ0, hδ1, hC, hB⟩ := hbase p hp
  refine ⟨δ0, C, hδ0, hδ1, hC, ?_⟩
  intro M hM Rm hRm Sreg It H hH T offset shift N n z hoff q s hs hs1
  obtain ⟨i, j⟩ := q
  set m := n + offset i
  set w := z + ((3 : ℝ) ^ (-n)) • shift i
  have hm : m ≤ (N : ℤ) := hoff i
  have hr : (0 : ℝ) < (3 : ℝ) ^ (-m) := by positivity
  have e := fun omega => lfgc_root_stat I M H sigma hsigma T offset shift N n z omega i
  have htr := aux_lfgc_root_base_root_coords_transport I M H hH sigma N m hm w
  obtain ⟨b1, b2, b3, b4⟩ := hB M hM Rm hRm Sreg It H hH ((N : ℤ) - m).toNat
  have hHm : Measurable H := hH.1
  obtain ⟨cm1, cm2, cm3, -, cm5⟩ := _root_.SubdiffusiveProcess.Paper.chart_coords_measurable d hd I M H hHm N w _ hr
  have href := aux_lfgc_root_tail_measurable_reference M H hHm N m w
  have hrefpos := _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference_pos M H N m w
  have hlamm : Measurable (fun omega => _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma (aux_lfgc_root_stat_rootChart I M H omega N m w)) := by
    have ee : (fun omega => _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma (aux_lfgc_root_stat_rootChart I M H omega N m w)) =
        (fun omega => I.lam w ((3 : ℝ) ^ (-m)) hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr)
          w ((3 : ℝ) ^ (-m)) sigma 2) :=
      funext fun omega => (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lam_eq I w _ hr _ sigma hsigma).symm
    rw [ee]; exact cm1 sigma hsigma
  have hLamm : Measurable (fun omega => _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF sigma (aux_lfgc_root_stat_rootChart I M H omega N m w)) := by
    have ee : (fun omega => _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF sigma (aux_lfgc_root_stat_rootChart I M H omega N m w)) =
        (fun omega => I.Lam w ((3 : ℝ) ^ (-m)) hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr)
          w ((3 : ℝ) ^ (-m)) sigma 2) :=
      funext fun omega => (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_Lam_eq I w _ hr _ sigma hsigma).symm
    rw [ee]; exact cm2 sigma hsigma
  have hbnd := aux_lfgc_root_tail2_ennreal_div_rpow_le (mul_nonneg hC (Real.rpow_nonneg M.shellPrefix.delta_pos.le c))
    hs hs1 (by linarith : (0 : ℝ) ≤ p)
  rcases j with j | ⟨a, b⟩
  · fin_cases j
    · -- inverse lower ellipticity
      simp only [Fin.zero_eta]
      have hset : {omega | s < |aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega)
          (i, Sum.inl 0)|} = {omega | s < |_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference M H N m w omega /
            _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma (aux_lfgc_root_stat_rootChart I M H omega N m w) - 1|} := by
        ext omega; simp only [Set.mem_ofPred_eq, (e omega).1]; exact Iff.rfl
      rw [hset]
      refine (lfgc_root_base M m w _
        (fun omega => (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_unitChart I M H
          omega ((N : ℤ) - m).toNat))⁻¹ - 1)
        ((href.div hlamm).sub_const 1).aestronglyMeasurable ?_ (by linarith) b1 hs).trans hbnd
      filter_upwards [htr] with omega hom
      simp only [Pi.div_apply]
      rw [hom.1]
    · -- upper ellipticity
      simp only [Fin.mk_one]
      have hset : {omega | s < |aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega)
          (i, Sum.inl 1)|} = {omega | s < |_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF sigma
            (aux_lfgc_root_stat_rootChart I M H omega N m w) / _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference M H N m w omega - 1|} := by
        ext omega; simp only [Set.mem_ofPred_eq, (e omega).2.1]; exact Iff.rfl
      rw [hset]
      refine (lfgc_root_base M m w _
        (fun omega => _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_LamF sigma (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_unitChart I M H
          omega ((N : ℤ) - m).toNat) - 1)
        ((hLamm.div href).sub_const 1).aestronglyMeasurable ?_ (by linarith) b2 hs).trans hbnd
      filter_upwards [htr] with omega hom
      simp only [Pi.div_apply]
      rw [hom.2.1]
    · -- homogenization error, through its square
      have hsq : {omega | s < |aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega)
          (i, Sum.inl ⟨2, by norm_num⟩)|} ⊆ {omega | s ^ 2 < |_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_errF sigma
            (aux_lfgc_root_stat_rootChart I M H omega N m w) (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference M H N m w omega) ^ 2|} := by
        intro omega hom
        simp only [Set.mem_ofPred_eq] at hom ⊢
        have : ((⟨2, by norm_num⟩ : Fin 3)) = 2 := rfl
        rw [this, (e omega).2.2.1] at hom
        have h0 := abs_nonneg (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_errF sigma (aux_lfgc_root_stat_rootChart I M H omega N m w)
          (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference M H N m w omega))
        rw [abs_pow, pow_two, pow_two]
        exact mul_lt_mul'' hom hom hs.le hs.le
      have herrm : Measurable (fun omega => _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_errF sigma
          (aux_lfgc_root_stat_rootChart I M H omega N m w) (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference M H N m w omega)) := by
        have ee : (fun omega => _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_errF sigma
            (aux_lfgc_root_stat_rootChart I M H omega N m w) (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference M H N m w omega)) =
            (fun omega => I.err w ((3 : ℝ) ^ (-m)) hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr)
              w ((3 : ℝ) ^ (-m)) (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference M H N m w omega) sigma 2) :=
          funext fun omega => (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_err_eq I w _ hr _ _ (hrefpos omega) sigma hsigma).symm
        rw [ee]; exact cm5 sigma hsigma _ href (fun omega => hrefpos omega)
      refine (measure_mono hsq).trans ((lfgc_root_base M m w _
        (fun omega => aux_lfgc_base_moments_probeSeries sigma (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_unitChart I M H
          omega ((N : ℤ) - m).toNat))
        (herrm.pow_const 2).aestronglyMeasurable ?_ (by linarith) b3 (by positivity)).trans ?_)
      · filter_upwards [htr] with omega hom
        rw [hom.2.2.1]
        set G := _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_unitChart I M H (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_shift m w omega)
          ((N : ℤ) - m).toNat
        have hfin : SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
            (Homogenization.originCube d 0) 0 sigma MultiscaleExponent.infinity 2 G 1 < ⊤ := by
          have h := I.err_finite 0 1 one_pos (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H
            (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_shift m w omega) (((N : ℤ) - m).toNat) 0 one_pos)
            0 1 one_pos subset_rfl sigma hsigma 2 (by norm_num) 1 one_pos
          simpa using! h
        obtain ⟨hsum, heq⟩ := _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_errF_eq sigma hsigma.1 G hfin
        rw [heq, Real.sq_sqrt]
        · rfl
        · refine tsum_nonneg fun k => mul_nonneg (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_gw_nonneg sigma hsigma.1.le k) ?_
          obtain ⟨R, hR⟩ := _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_D_nonempty (d := d) k
          exact le_trans ENNReal.toReal_nonneg (Finset.le_sup' (fun R =>
            (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R G 1).toReal) hR)
      · exact le_of_eq rfl
  · -- top-cube σ entries
    have hset : {omega | s < |aux_lfgc_root_stat_selOf (aux_lfgc_root_stat_bandCoords I M H sigma sigma T offset shift N n z omega)
        (i, Sum.inr (a, b))|} = {omega | s < |_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_sigF a b
          (aux_lfgc_root_stat_rootChart I M H omega N m w) / _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference M H N m w omega -
          (if a = b then (1 : ℝ) else 0)|} := by
      ext omega; simp only [Set.mem_ofPred_eq, ((e omega).2.2.2 a b)]; exact Iff.rfl
    rw [hset]
    refine (lfgc_root_base M m w _
      (fun omega => _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_sigF a b (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_unitChart I M H
        omega ((N : ℤ) - m).toNat) - (if a = b then (1 : ℝ) else 0))
      (((cm3 a b).div href).sub_const _).aestronglyMeasurable ?_ (by linarith) (b4 a b) hs).trans hbnd
    filter_upwards [htr] with omega hom
    exact congrArg (· - (if a = b then (1 : ℝ) else 0)) (hom.2.2.2 a b)

end SubdiffusiveProcess.Paper
