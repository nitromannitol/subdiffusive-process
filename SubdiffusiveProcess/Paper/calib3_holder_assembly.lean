import Mathlib
import SubdiffusiveProcess.Paper.calib3_HT
import SubdiffusiveProcess.Paper.calib3_envelope
import SubdiffusiveProcess.Paper.calib3_energy_assembly
import SubdiffusiveProcess.Paper.calib3_holder_macro
import SubdiffusiveProcess.Paper.prop_growth_trunc_holder_assembly
import SubdiffusiveProcess.Paper.prop_growth_holder_micro_campanato
import SubdiffusiveProcess.Paper.prop_growth_holder_assembly
import SubdiffusiveProcess.Paper.killed_continuous_boundary_zero

/-! Stage 3 (calibration): the Hölder half of `mfd:prop-growth` on the unit cube for the top-block-removed model `HT_j`
(coefficient level `N + j`): micro Campanato decay below the wavelength from `calib3_energy_assembly`, macro decay from
`calib3_holder_macro`, and the boundary trace, assembled as in `prop_growth_holder_assembly`. -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_calib3_holder_assembly_micro :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E) (_X : in_extension d hd E)
    (_W : SmallPerturbationInput d) (_Cp : CampanatoInput d)
    (_S : SobolevFoundationalInput d hd) (alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M), M.delta ≤ delta0 →
      ∀ (j : ℕ), 0 < j → ∀ (z : SpatialCoordinates d),
      ∃ (Kosc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kosc N om) ∧
        (∀ i N, MemLp (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z 1 one_pos : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z 1 one_pos)),
          ((b : SobolevData (centeredCube z 1 one_pos)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) z one_pos) F b u →
          ∀ x ∈ centeredCube z 1 one_pos, ∀ rad : ℝ, 0 < rad →
            rad < (3 : ℝ) ^ (-((N + j : ℕ) : ℤ)) → rad ≤ 1 →
            ∫ y in Metric.ball x rad ∩ (centeredCube z 1 one_pos : Set (SpatialCoordinates d)),
                ((u : SobolevData (centeredCube z 1 one_pos)).1 y - setAverage
                  (Metric.ball x rad ∩ (centeredCube z 1 one_pos : Set (SpatialCoordinates d)))
                  (u : SobolevData (centeredCube z 1 one_pos)).1) ^ 2
                ∂volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d)) ≤
              (Kosc N om * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) := by
  intro d hd _ _ E P X W Cp S alpha k ps ha0 ha1 hps
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  -- the energy exponent `t` and the excess `e = 2 + t - 2α - d > 0`
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) + d) / 2 :=
    ⟨_, rfl⟩
  have hmax1 := le_max_left ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha)
  have hmax2 := le_max_right ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha)
  have hmaxd : max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) < d :=
    max_lt (by linarith) (by linarith)
  have ht1 : (d : ℝ) - 1 < t := by rw [htdef]; linarith
  have htd : t < d := by rw [htdef]; linarith
  have hte : (d : ℝ) - 2 + 2 * alpha < t := by rw [htdef]; linarith
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 2 + t - 2 * alpha - d := ⟨_, rfl⟩
  have he : 0 < e := by rw [hedef]; linarith
  have hexp : 2 + t = 2 * alpha + d + e := by rw [hedef]; ring
  -- suppliers, all fixed before the model
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 + ∑ i, ps i := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => le_trans zero_le_one (hps i)
  have hq : 1 ≤ q := by rw [hqdef]; linarith
  have hpq : ∀ i, ps i ≤ q := by
    intro i
    have := Finset.single_le_sum (fun j _ => le_trans zero_le_one (hps j)) (Finset.mem_univ i)
    rw [hqdef]; linarith
  have hq0 : 0 < 2 * q := by linarith
  obtain ⟨deltaE, hdeltaE, hEA⟩ :=
    calib3_energy_assembly d hd E P X W Cp S t alpha k ps ht1 htd ha0 ha1 hps
  obtain ⟨Cpe, Cd, cd, hCpe, hCd, hcd, hroot⟩ :=
    calib3_envelope d hd q hq
  obtain ⟨CP, hCP0, hPoinc⟩ :=
    aux_prop_growth_holder_micro_campanato_scaled_poincare d (by omega)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨dabs, hdabs⟩ : ∃ s : ℝ, s = min 1 ((e / 2) * Real.log 3 / (Cd + Cpe)) := ⟨_, rfl⟩
  have hdabs0 : 0 < dabs := by
    rw [hdabs]
    exact lt_min one_pos (div_pos (mul_pos (half_pos he) hlog3) (add_pos hCd hCpe))
  refine ⟨min deltaE (min (cd / (2 * q)) dabs),
    lt_min hdeltaE (lt_min (div_pos hcd hq0) hdabs0), ?_⟩
  intro M Rm hdelta j hj z
  have hdE : M.delta ≤ deltaE := hdelta.trans (min_le_left _ _)
  have hdc : M.delta ≤ cd / (2 * q) :=
    hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hda : M.delta ≤ dabs := hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  -- the exponential growth rate of the coefficient envelope is absorbed
  have hrate : Cd * M.delta + Cpe * M.delta ^ 2 ≤ (e / 2) * Real.log 3 :=
    aux_prop_growth_holder_micro_campanato_rate Cd Cpe e M.delta hCd hCpe hdpos
      (hda.trans_eq hdabs)
  obtain ⟨K, CbK, hKL, hKB, -, hen⟩ := hEA M Rm hdE j hj z
  obtain ⟨D, Mx, CD, CE, hCD, hCE, hDMx0, hext, hmem, -, hMxmom⟩ := hroot M hdc j hj z
  have hfac := aux_prop_growth_holder_micro_campanato_fac e _ he hrate
  have hCP1 : 0 ≤ 1 + CP := add_nonneg zero_le_one hCP0
  refine ⟨fun N om => (1 + CP) * (Mx (N + j) om + |K N om|) * ((3 : ℝ) ^ (-((N + j : ℕ) : ℤ))) ^ (e / 2),
    fun i => (1 + CP) * (CE + max (CbK i) 0), ?_, ?_, ?_, ?_⟩
  · intro N om
    have := (hDMx0 (N + j) om).2
    have := (hfac (N + j)).1
    positivity
  · intro i N
    exact (aux_prop_growth_holder_micro_campanato_moment (chaosSampleLaw M).toMeasure (ps i) q
      (hps i) (hpq i) (Mx (N + j)) (K N) (1 + CP) _ ((Cd * M.delta + Cpe * M.delta ^ 2) * ((N + j : ℕ) : ℝ)) CE
      (CbK i) hCP1 (hfac (N + j)).1 (hfac (N + j)).2.1 (hfac (N + j)).2.2 hCE (hmem (N + j)).2 (hMxmom (N + j))
      (hKL i N) (hKB i N)).1
  · intro i N
    exact (aux_prop_growth_holder_micro_campanato_moment (chaosSampleLaw M).toMeasure (ps i) q
      (hps i) (hpq i) (Mx (N + j)) (K N) (1 + CP) _ ((Cd * M.delta + Cpe * M.delta ^ 2) * ((N + j : ℕ) : ℝ)) CE
      (CbK i) hCP1 (hfac (N + j)).1 (hfac (N + j)).2.1 (hfac (N + j)).2.2 hCE (hmem (N + j)).2 (hMxmom (N + j))
      (hKL i N) (hKB i N)).2
  · filter_upwards [hen, hext] with om hom hext'
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol x hx rad hrad hradN hradr
    obtain ⟨hMxpos, hbounds, -⟩ := hext' (N + j)
    have hlow : ∀ᵐ y ∂volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d)),
        1 ≤ Mx (N + j) om * (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) z one_pos).val y := by
      filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae M (calib3_HT d j) om (N + j) z one_pos,
        ae_restrict_mem (centeredCube z 1 one_pos).isOpen.measurableSet] with y hy hyQ
      rw [hy]
      have hlo := (hbounds y (centeredCube_subset_closedCube z one_pos hyQ)).1
      calc (1 : ℝ) = Mx (N + j) om * (Mx (N + j) om)⁻¹ := (mul_inv_cancel₀ hMxpos.ne').symm
        _ ≤ Mx (N + j) om * cutoffCoefficient M (calib3_HT d j) om (N + j) y :=
          mul_le_mul_of_nonneg_left hlo hMxpos.le
    have hrad1 : rad ≤ 1 := hradr
    have hpw := aux_prop_growth_holder_micro_campanato_pathwise CP hCP0 hPoinc z one_pos
      (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) z one_pos) (Mx (N + j) om) hMxpos.le hlow u rad
      (K N om * (Kf + Cphi) ^ 2 * rad ^ t) hrad
      (fun c hc => hom N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol c rad hc hrad hrad1)
      x hx
    have hV := aux_prop_growth_holder_micro_campanato_volume_ge z x (R := 1 / 2) hrad
      (hradr.trans_eq (by ring)) hx
    exact aux_prop_growth_holder_micro_campanato_final_alg d CP (Mx (N + j) om) (K N om) (Kf + Cphi)
      rad ((3 : ℝ) ^ (-((N + j : ℕ) : ℤ))) _ t alpha e _ hCP0 hMxpos.le hrad hradN.le he.le hexp hV hpw

theorem calib3_holder_assembly :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (_Cp : CampanatoInput d)
    (_S : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M), M.delta ≤ delta0 →
      ∀ (j : ℕ), 0 < j → ∀ (z : SpatialCoordinates d),
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z 1 one_pos : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z 1 one_pos)),
          ((b : SobolevData (centeredCube z 1 one_pos)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) z one_pos) F b u →
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube z 1 one_pos)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha (closedCube z 1 one_pos : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube z 1 one_pos : Set (SpatialCoordinates d)) U ≤
              K N om * (Kf + Cphi)) := by
  intro d hd _ _ E P X W Cp S t alpha k ps _ht _htd ha0 ha1 hps
  obtain ⟨delta1, hdelta1, hmac'⟩ := calib3_holder_macro d hd E P X S alpha k ps ha0 ha1 hps
  obtain ⟨delta2, hdelta2, hmic'⟩ := aux_calib3_holder_assembly_micro d hd E P X W Cp S alpha k ps ha0 ha1 hps
  refine ⟨min delta1 delta2, lt_min hdelta1 hdelta2, ?_⟩
  intro M Rm hdelta j hj z
  obtain ⟨Kmac, Cmac, hKmac0, hKmacL, hKmacB, hmacE⟩ :=
    hmac' M Rm (hdelta.trans (min_le_left _ _)) j hj z
  obtain ⟨Kmic, Cmic, hKmic0, hKmicL, hKmicB, hmicE⟩ :=
    hmic' M Rm (hdelta.trans (min_le_right _ _)) j hj z
  have hCa : 0 < Cp.C alpha := Cp.C_pos alpha ha0 ha1
  have hsd : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (2 + Real.sqrt d) * Cp.C alpha := ⟨_, rfl⟩
  have hc : 0 ≤ c := by
    rw [hcdef]; exact mul_nonneg (by positivity) hCa.le
  refine ⟨fun N om => 1 + c * (Kmac N om + Kmic N om),
    fun i => 1 + c * (max (Cmac i) 0 + max (Cmic i) 0), ?_, ?_, ?_, ?_⟩
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (Kmac N) (Kmic N) hc
      (hKmacL i N) (hKmicL i N) (hKmacB i N) (hKmicB i N)).1
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (Kmac N) (Kmic N) hc
      (hKmacL i N) (hKmicL i N) (hKmacB i N) (hKmicB i N)).2
  · refine Filter.Eventually.of_forall fun om N => ?_
    show 1 ≤ 1 + c * (Kmac N om + Kmic N om)
    have := mul_nonneg hc (add_nonneg (hKmac0 N om) (hKmic0 N om))
    linarith
  · filter_upwards [hmacE, hmicE] with om hom1 hom2
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    have hCphi0 : 0 ≤ Cphi :=
      (aux_prop_growth_holder_assembly_c2Norm_nonneg _ _).trans hCphi
    have hKfC : 0 ≤ Kf + Cphi := add_nonneg hKf hCphi0
    have hKc : 0 ≤ Kmac N om + Kmic N om := add_nonneg (hKmac0 N om) (hKmic0 N om)
    have hcamp : ∀ x ∈ centeredCube z 1 one_pos, ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
        ∫ y in Metric.ball x rad ∩ (centeredCube z 1 one_pos : Set (SpatialCoordinates d)),
            ((u : SobolevData (centeredCube z 1 one_pos)).1 y - setAverage
              (Metric.ball x rad ∩ (centeredCube z 1 one_pos : Set (SpatialCoordinates d)))
              (u : SobolevData (centeredCube z 1 one_pos)).1) ^ 2
            ∂volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d)) ≤
          ((Kmac N om + Kmic N om) * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
            volume.real (Metric.ball x rad ∩
              (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) := by
      intro x hx rad hrad hradr
      by_cases hN : (3 : ℝ) ^ (-((N + j : ℕ) : ℤ)) ≤ rad
      · have h1 := hom1 N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve x hx rad hN hradr
        have hsq : (Kmac N om * (Kf + Cphi)) ^ 2 ≤ ((Kmac N om + Kmic N om) * (Kf + Cphi)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (hKmac0 N om) hKfC)
            (mul_le_mul_of_nonneg_right (by linarith [hKmic0 N om]) hKfC) 2
        calc _ ≤ (Kmac N om * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
              volume.real (Metric.ball x rad ∩
                (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) := h1
          _ ≤ _ := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hrad.le _)) measureReal_nonneg
      · have hN' : rad < (3 : ℝ) ^ (-((N + j : ℕ) : ℤ)) := lt_of_not_ge hN
        have h2 := hom2 N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve x hx rad hrad
          hN' hradr
        have hsq : (Kmic N om * (Kf + Cphi)) ^ 2 ≤ ((Kmac N om + Kmic N om) * (Kf + Cphi)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (hKmic0 N om) hKfC)
            (mul_le_mul_of_nonneg_right (by linarith [hKmac0 N om]) hKfC) 2
        calc _ ≤ (Kmic N om * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
              volume.real (Metric.ball x rad ∩
                (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) := h2
          _ ≤ _ := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hrad.le _)) measureReal_nonneg
    obtain ⟨U, hUc, hUae, hUH, hUn⟩ :=
      aux_prop_growth_holder_assembly_whole_norm hd Cp killed_continuous_boundary_zero z one_pos le_rfl ha0 ha1 b u hsolve.1
        (hphi.continuous) hb hKc hKf hCphi hcamp
    refine ⟨U, hUc, hUae, hUH, hUn.trans (le_of_eq ?_)⟩
    simp only [hcdef]

end Paper
