import SubdiffusiveProcess.Paper.lem_band

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Base deviation moments of the unit-root chart quantities

For the unit-root chart of the cutoff coefficient with `K` layers, at small disorder:
`‖LamF - 1‖_p ≤ C δ^c` and `‖T‖_p ≤ C δ^c` where `T` is the discounted series of scalar
probes whose square root is the homogenization error.  These are the deviation components
of lem_band's aggregation lemma `aux_lem_band_U2_agg`, taken with no band (`L = 0`).
Together with `aux_lem_band_U2_invlam_core` and `aux_lem_band_U2_cellE` they give the
zero-disorder smallness of every coordinate used in the single-point tests.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02 SubdiffusiveProcess
open scoped ENNReal

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Deviation moment of the upper ellipticity of the unit chart. -/
theorem aux_lfgc_base_moments_base_Lam_dev (hd : 2 ≤ d) [NeZero d] (I : Paper.in_J d)
    (Poincare : Paper.in_poincare d hd I) (Extension : Paper.in_extension d hd I)
    (Perturbation : Lane4.SmallPerturbationInput d) (Sobolev : Lane4.SobolevFoundationalInput d hd)
    (D : Paper.lane4_deterministic_good_scale_input d) (Cresp : ℝ) (hCresp : 0 < Cresp)
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℝ, 1 ≤ p → ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 ≤ C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ K : ℕ,
        eLpNorm (fun omega => Paper.aux_lem_band_U2_LamF sigma
            (Paper.aux_lem_band_U2_unitChart I M H omega K) - 1)
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * M.delta ^ c) := by
  obtain ⟨a, c, ha, hc, w', hw', hcell⟩ := Paper.aux_lem_band_U2_cell_bNorm d hd I Poincare
    Extension Perturbation Sobolev D Cresp hCresp
  have hs0 : 0 < sigma := hsigma.1
  refine ⟨c, hc, fun p hp => ?_⟩
  have hpq : p ≤ max p (2 * (d : ℝ) / sigma) := le_max_left _ _
  have hq1 : 1 ≤ max p (2 * (d : ℝ) / sigma) := hp.trans hpq
  obtain ⟨δ0, C, hδ0, hC, hcell'⟩ := hcell (sigma / 2) (by linarith) _ hq1
  have hCβ := Paper.aux_lem_band_U2_Cbeta_pos sigma hs0
  refine ⟨δ0, (1 - (3 : ℝ) ^ (-(2 * sigma / 2)))⁻¹ * C, hδ0, by positivity, ?_⟩
  intro M hM Rm hRm Sreg It H hH K
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδc : 0 ≤ M.delta ^ c := Real.rpow_nonneg hδpos.le c
  have hLampos : ∀ omega, 0 < Paper.aux_lem_band_U2_LamF sigma
      (Paper.aux_lem_band_U2_unitChart I M H omega K) := by
    intro omega
    have := I.Lam_pos 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos) 0 1
      sigma 2
    rwa [Paper.aux_lem_band_U2_Lam_eq I 0 1 one_pos _ sigma hsigma] at this
  have hsum : ∀ omega, Summable (fun k => Book.Ch02.geometricWeight sigma 2 k *
      (Paper.aux_lem_band_U2_D (d := d) k).sup' (Paper.aux_lem_band_U2_D_nonempty k)
        (fun R => coarseBMatrixNorm R (Paper.aux_lem_band_U2_unitChart I M H omega K))) := by
    intro omega
    by_contra hns
    have h0 := tsum_eq_zero_of_not_summable hns
    have h1 := Paper.aux_lem_band_U2_LamF_eq (d := d) sigma
      (Paper.aux_lem_band_U2_unitChart I M H omega K)
    rw [h0] at h1
    exact (hLampos omega).ne' h1
  have hsumE : Summable (fun k => Book.Ch02.geometricWeight sigma 2 k *
      (Paper.aux_lem_band_U2_D (d := d) k).sup' (Paper.aux_lem_band_U2_D_nonempty k)
        (fun _ => (1 : ℝ))) := by
    simp only [Finset.sup'_const, mul_one]; exact (Paper.aux_lem_band_U2_gw_tsum sigma hs0).summable
  have hTE : ∑' k, Book.Ch02.geometricWeight sigma 2 k *
      (Paper.aux_lem_band_U2_D (d := d) k).sup' (Paper.aux_lem_band_U2_D_nonempty k)
        (fun _ => (1 : ℝ)) = 1 := by
    simp only [Finset.sup'_const, mul_one]; exact (Paper.aux_lem_band_U2_gw_tsum sigma hs0).tsum_eq
  have hfun : (fun omega => Paper.aux_lem_band_U2_LamF sigma
      (Paper.aux_lem_band_U2_unitChart I M H omega K) - 1) =
      (fun omega => (∑' k, Book.Ch02.geometricWeight sigma 2 k *
        (Paper.aux_lem_band_U2_D (d := d) k).sup' (Paper.aux_lem_band_U2_D_nonempty k)
          (fun R => coarseBMatrixNorm R (Paper.aux_lem_band_U2_unitChart I M H omega K))) -
        ∑' k, Book.Ch02.geometricWeight sigma 2 k *
          (Paper.aux_lem_band_U2_D (d := d) k).sup' (Paper.aux_lem_band_U2_D_nonempty k)
            (fun _ => (1 : ℝ))) := by
    funext omega
    rw [Paper.aux_lem_band_U2_LamF_eq, hTE]
  obtain ⟨-, hdev, -⟩ := Paper.aux_lem_band_U2_agg (chaosSampleLaw M).toMeasure
      (inferInstance : MeasurableSpace (BilateralField d)) le_rfl
      (Paper.aux_lem_band_U2_D (d := d)) Paper.aux_lem_band_U2_D_nonempty (d : ℝ)
      (Nat.cast_nonneg d) Paper.aux_lem_band_U2_D_card (Book.Ch02.geometricWeight sigma 2)
      (2 * sigma) (by linarith) (Paper.aux_lem_band_U2_gw_nonneg sigma hs0.le)
      (Paper.aux_lem_band_U2_gw_le sigma hs0.le)
      (fun k R omega => coarseBMatrixNorm R (Paper.aux_lem_band_U2_unitChart I M H omega K))
      (fun _ _ => (1 : ℝ))
      (fun k R hR => (hcell' M hM Rm hRm Sreg It H hH K k R hR).1) hsum hsumE
      p (max p (2 * (d : ℝ) / sigma)) (sigma / 2) hp hpq (by linarith)
      (Paper.aux_lem_band_U2_q_bound d p sigma hp hs0)
      (C * M.delta ^ c) 0 (mul_nonneg hC hδc) le_rfl 0
      (fun k R hR => (hcell' M hM Rm hRm Sreg It H hH K k R hR).2.1)
      (fun k hk => absurd hk (Nat.not_lt_zero k))
  rw [hfun]
  refine hdev.trans (le_of_eq ?_)
  congr 1; ring

/-- The discounted probe series of the unit chart. -/
noncomputable def aux_lfgc_base_moments_probeSeries (s : ℝ) (F : TriadicCoeffFamily d) : ℝ :=
  ∑' k, Book.Ch02.geometricWeight s 2 k *
    (Paper.aux_lem_band_U2_D (d := d) k).sup' (Paper.aux_lem_band_U2_D_nonempty k)
      (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R F 1).toReal)

/-- Moment of the probe series (the squared homogenization error). -/
theorem lfgc_base_moments (hd : 2 ≤ d) [NeZero d] (I : Paper.in_J d)
    (Poincare : Paper.in_poincare d hd I) (Extension : Paper.in_extension d hd I)
    (Perturbation : Lane4.SmallPerturbationInput d) (Sobolev : Lane4.SobolevFoundationalInput d hd)
    (D : Paper.lane4_deterministic_good_scale_input d) (Cresp : ℝ) (hCresp : 0 < Cresp)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : ℝ, 1 ≤ p → ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 ≤ C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d M), Rm.C ≤ Cresp →
      ∀ (Sreg : Paper.in_6_16 d M) (_It : Paper.in_iteration d M I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
      ∀ K : ℕ,
        eLpNorm (fun omega => aux_lfgc_base_moments_probeSeries s (Paper.aux_lem_band_U2_unitChart I M H omega K))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * M.delta ^ c) := by
  obtain ⟨a, c, ha, hc, w', hw', hcell⟩ := Paper.aux_lem_band_U2_cell_probe d hd I Poincare
    Extension Perturbation Sobolev D Cresp hCresp
  have hs0 : 0 < s := hs.1
  refine ⟨c, hc, fun p hp => ?_⟩
  have hpq : p ≤ max p (2 * (d : ℝ) / s) := le_max_left _ _
  have hq1 : 1 ≤ max p (2 * (d : ℝ) / s) := hp.trans hpq
  obtain ⟨δ0, C, hδ0, hC, hcell'⟩ := hcell (s / 2) (by linarith) _ hq1
  have hCβ := Paper.aux_lem_band_U2_Cbeta_pos s hs0
  refine ⟨δ0, (1 - (3 : ℝ) ^ (-(2 * s / 2)))⁻¹ * C, hδ0, by positivity, ?_⟩
  intro M hM Rm hRm Sreg It H hH K
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδc : 0 ≤ M.delta ^ c := Real.rpow_nonneg hδpos.le c
  have hfin : ∀ omega, SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
      (Homogenization.originCube d 0) 0 s MultiscaleExponent.infinity 2
      (Paper.aux_lem_band_U2_unitChart I M H omega K) 1 < ⊤ := by
    intro omega
    have h := I.err_finite 0 1 one_pos (Lane4.cutoffPositiveCoefficient M H omega K 0 one_pos)
      0 1 one_pos subset_rfl s hs 2 (by norm_num) 1 one_pos
    simpa using h
  have hsum : ∀ omega, Summable (fun k => Book.Ch02.geometricWeight s 2 k *
      (Paper.aux_lem_band_U2_D (d := d) k).sup' (Paper.aux_lem_band_U2_D_nonempty k)
        (fun R => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
          (Paper.aux_lem_band_U2_unitChart I M H omega K) 1).toReal)) :=
    fun omega => (Paper.aux_lem_band_U2_errF_eq s hs0 _ (hfin omega)).1
  have hsumE : Summable (fun k => Book.Ch02.geometricWeight s 2 k *
      (Paper.aux_lem_band_U2_D (d := d) k).sup' (Paper.aux_lem_band_U2_D_nonempty k)
        (fun _ => (0 : ℝ))) := by
    simp only [Finset.sup'_const, mul_zero]; exact summable_zero
  have hTE : ∑' k, Book.Ch02.geometricWeight s 2 k *
      (Paper.aux_lem_band_U2_D (d := d) k).sup' (Paper.aux_lem_band_U2_D_nonempty k)
        (fun _ => (0 : ℝ)) = 0 := by
    simp only [Finset.sup'_const, mul_zero, tsum_zero]
  obtain ⟨-, hdev, -⟩ := Paper.aux_lem_band_U2_agg (chaosSampleLaw M).toMeasure
      (inferInstance : MeasurableSpace (BilateralField d)) le_rfl
      (Paper.aux_lem_band_U2_D (d := d)) Paper.aux_lem_band_U2_D_nonempty (d : ℝ)
      (Nat.cast_nonneg d) Paper.aux_lem_band_U2_D_card (Book.Ch02.geometricWeight s 2)
      (2 * s) (by linarith) (Paper.aux_lem_band_U2_gw_nonneg s hs0.le)
      (Paper.aux_lem_band_U2_gw_le s hs0.le)
      (fun k R omega => (SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax R
        (Paper.aux_lem_band_U2_unitChart I M H omega K) 1).toReal) (fun _ _ => (0 : ℝ))
      (fun k R hR => (hcell' M hM Rm hRm Sreg It H hH K k R hR).1) hsum hsumE
      p (max p (2 * (d : ℝ) / s)) (s / 2) hp hpq (by linarith)
      (Paper.aux_lem_band_U2_q_bound d p s hp hs0)
      (C * M.delta ^ c) 0 (mul_nonneg hC hδc) le_rfl 0
      (fun k R hR => by
        have := (hcell' M hM Rm hRm Sreg It H hH K k R hR).2.1
        simpa only [sub_zero] using this)
      (fun k hk => absurd hk (Nat.not_lt_zero k))
  rw [hTE] at hdev
  simp only [sub_zero] at hdev
  refine hdev.trans (le_of_eq ?_)
  congr 1; ring

end Paper
