import SubdiffusiveProcess.Paper.aux_rem_bank_neumann_growth_block_uniform
import SubdiffusiveProcess.Paper.rem_bank_neumann_coercive_uniform
import SubdiffusiveProcess.Paper.g9_neumann_error_instantiation_uniform
import SubdiffusiveProcess.Paper.g9_neumann_facebump_bridge
import SubdiffusiveProcess.Paper.prop_16




set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.Lane4

noncomputable section
namespace Paper



theorem aux_g9_neumann_band_uniform_log_cond (p Cresp : ℝ) (hp : 0 < p) (hC : 0 < Cresp) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hδ2 : δ ≤ 1 / (4 * p * Cresp)) :
    4 * p ≤ Cresp⁻¹ * (δ ^ 2)⁻¹ * |Real.log δ|⁻¹ := by
  have hlog : Real.log δ < 0 := Real.log_neg hδ0 (by linarith)
  have habs : 0 < |Real.log δ| := abs_pos.2 hlog.ne
  have key : |Real.log δ * δ| < 1 := Real.abs_log_mul_self_lt δ hδ0 (by linarith)
  rw [abs_mul, abs_of_pos hδ0] at key
  have hprod : 0 < Cresp * δ * (δ * |Real.log δ|) := by positivity
  have heq : Cresp⁻¹ * (δ ^ 2)⁻¹ * |Real.log δ|⁻¹ = 1 / (Cresp * δ * (δ * |Real.log δ|)) := by
    field_simp
  rw [heq, le_div_iff₀ hprod]
  have h4 : 4 * p * Cresp * δ ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hδ2
    linarith
  have h5 : δ * |Real.log δ| ≤ 1 := by linarith
  calc 4 * p * (Cresp * δ * (δ * |Real.log δ|)) = (4 * p * Cresp * δ) * (δ * |Real.log δ|) := by ring
    _ ≤ 1 * 1 := mul_le_mul h4 h5 (by positivity) zero_le_one
    _ = 1 := one_mul 1

theorem g9_neumann_band_uniform (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : Paper.in_J d) (P : Paper.in_poincare d hd E) (X : Paper.in_extension d hd E)
    (W : SubdiffusiveProcess.Lane4.SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Sfi : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (Cresp : ℝ) (hCresp : 0 < Cresp)
    (t : ℝ) (ht0 : (d : ℝ) - 1 < t) (ht1 : t < (d : ℝ))
    (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho) (hrho0 : ∀ v : ℝ, 0 ≤ rho v)
    (hrhos : ∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) (hrhoi : (∫ v, rho v) = 1)
    (pvec : Fin d → ℝ) (hpvec : (∑ i : Fin d, (pvec i) ^ 2) = 1)
    (hPn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖) :
    let Q := unitNeumannCube d
    let S := meanZeroResponseSpace hPn
    let L0 : S.space →L[ℝ] ℝ :=
      (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph Q))
    ∀ (fL2 : ℝ → DomainL2 Q),
      (∀ eps : ℝ, (0 < eps ∧ eps < 1 / 8) →
        ((fL2 eps : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (Q : Set (SpatialCoordinates d))]
          faceBump rho pvec eps)) →
      ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
        ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
        ∀ (Rm : in_responses d M), Rm.C ≤ Cresp →
        ∀ (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
        ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
          let Pm : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
          let aN : ℕ → BilateralField d → PositiveCoefficient Q := fun N om =>
            cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos
          let yN : ℕ → BilateralField d → ℝ := fun N om =>
            inverseResponse S (aN N om) L0
          (∀ h N : ℕ,
            eLpNorm (fun om => yN N om - (Pm[yN N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) om)
                (ENNReal.ofReal 2) Pm ≤
              ENNReal.ofReal
                (C * Real.sqrt M.delta *
                  (3 : ℝ) ^ (-((t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) / 32) * (h : ℝ))))) ∧
          (∀ h N : ℕ, N < h →
            eLpNorm (fun om => yN N om - (Pm[yN N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) om)
                (ENNReal.ofReal 2) Pm ≤
              ENNReal.ofReal (C * M.delta * (3 : ℝ) ^ (-(h : ℝ)))) := by
  intro Q S L0 fL2 hfL2
  obtain ⟨δg, hδg, hmg⟩ := aux_rem_bank_neumann_growth_block_uniform d hd E P X W D t ht0 ht1 2
  obtain ⟨B13, hB13_0, hmg2⟩ := hmg le_rfl rho hrho hrho0 hrhos hrhoi pvec hpvec
  obtain ⟨δc, hδc, B9, Bsm, hB9_0, hBsm_0, hmc⟩ :=
    rem_bank_neumann_coercive_uniform d hd E P Sfi 2 3 le_rfl (by norm_num) rho hrho hrho0
      hrhos hrhoi pvec hpvec hPn
  obtain ⟨δe, Ke, Cerr, Cunif, hδe0, hKe0, hCerr0, hCunif0, hme⟩ :=
    g9_neumann_error_instantiation_uniform d hd E P Sfi 2 (by norm_num) rho hrho hrho0 hrhos hrhoi
      pvec hpvec hPn
  set B : ℝ := max (max B13 Bsm) (max B9 Cerr) with hBdef
  have hB0 : 0 ≤ B := le_trans hB13_0 ((le_max_left _ _).trans (le_max_left _ _))
  obtain ⟨delta0N, C, hdelta0N, _hdelta0N1, hC, hmainN⟩ :=
    aux_prop_16_neumann d hd E Cresp hCresp rho hrho hrho0 hrhos hrhoi pvec hpvec hPn fL2 hfL2
      t 2 B ⟨ht0, ht1, le_rfl, hB0⟩
  set δL : ℝ := min (1 / 2) (1 / (4 * 2 * Cresp)) with hδL
  have hδLpos : 0 < δL := lt_min (by norm_num) (by positivity)
  refine ⟨min (min (min δg 1) (min δc δe)) (min delta0N δL), C,
    lt_min (lt_min (lt_min hδg one_pos) (lt_min hδc hδe0)) (lt_min hdelta0N hδLpos), hC, ?_⟩
  intro M hMδ Rm hRC Sreg It H hIC
  have hMg : M.delta ≤ δg := hMδ.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hMc' : M.delta ≤ min 1 δc :=
    le_min (hMδ.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))))
      (hMδ.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hMe : M.delta ≤ δe := hMδ.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hMδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hMN : M.delta ≤ delta0N := hMδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hML : M.delta ≤ δL := hMδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlog := aux_g9_neumann_band_uniform_log_cond 2 Cresp (by norm_num) hCresp M.delta hMδpos
    (hML.trans (min_le_left _ _)) (hML.trans (min_le_right _ _))
  obtain ⟨K13, hK13ae, hK13mom⟩ := hmg2 M Rm Sreg It H hIC hMg
  obtain ⟨Kcoerc, hKcoerc, hKmem, hKnorm, hys⟩ := hmc M Rm H hIC hMc'
  have hKm : ∀ N, AEStronglyMeasurable (K13 N) (chaosSampleLaw M).toMeasure :=
    fun N => (hK13mom N).1.aestronglyMeasurable
  have hK0 : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 0 ≤ K13 N om := by
    filter_upwards [hK13ae] with omega hom N using (hom N).1
  have hgrowth : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (eps : ℝ), (0 < eps ∧ eps < 1 / 8) →
        ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ (Q : Set (SpatialCoordinates d)) →
          (0 < rad ∧ rad ≤ 1) →
            localGradientEnergy (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                (s := Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d)))
                (Metric.isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
                (subspaceGradient S.space
                  (responseSolution S (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                    ((sobolevVolumeLoad (fL2 eps)).comp S.space.subtypeL))) ≤
              K13 N om * eps ^ (-2 : ℝ) * rad ^ t := by
    filter_upwards [hK13ae] with omega hom N eps heps x rad hx hrad
    have hbridge := g9_neumann_facebump_bridge rho hrho hrho0 hrhos hrhoi pvec hPn
      (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos)
      eps heps.1 heps.2 (fL2 eps) (hfL2 eps heps)
    exact (hom N).2 eps heps.1 heps.2
      (responseSolution (meanZeroResponseSpace hPn)
        (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos)
        ((sobolevVolumeLoad (fL2 eps)).comp S.space.subtypeL))
      hbridge x hx rad hrad.1 hrad.2
  have hKmom : ∀ N, MemLp (K13 N) (ENNReal.ofReal (3 * 2)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (K13 N) (ENNReal.ofReal (3 * 2)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B :=
    fun N => ⟨(hK13mom N).1, (hK13mom N).2.trans
      (ENNReal.ofReal_le_ofReal ((le_max_left B13 Bsm).trans (le_max_left _ _)))⟩
  have hyepsB : ∀ N eps, (0 < eps ∧ eps < 1 / 8) →
      MemLp (fun om => inverseResponse S (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
          ((sobolevVolumeLoad (fL2 eps)).comp S.space.subtypeL)) (ENNReal.ofReal (3 * 2))
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => inverseResponse S (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
          ((sobolevVolumeLoad (fL2 eps)).comp S.space.subtypeL)) (ENNReal.ofReal (3 * 2))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
    intro N eps heps
    obtain ⟨hysmem, -, hysnorm⟩ := hys eps heps.1 heps.2 (fL2 eps) (hfL2 eps heps) N
    exact ⟨hysmem, (le_self_add.trans hysnorm).trans
      (ENNReal.ofReal_le_ofReal ((le_max_right B13 Bsm).trans (le_max_left _ _)))⟩
  have hyNB : ∀ N, MemLp (fun om => inverseResponse S (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) L0)
        (ENNReal.ofReal (4 * 2)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => inverseResponse S (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) L0)
        (ENNReal.ofReal (4 * 2)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
    intro N
    have hyn4p : eLpNorm (fun om => inverseResponse (meanZeroResponseSpace hPn)
          (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) L0)
        (ENNReal.ofReal (4 * 2)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B9 := by
      have h4 : (4 : ℝ) * 2 ≤ 4 * 3 := by norm_num
      refine (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal h4) ?_).trans ?_
      · exact (hKmem N).2.2.2.aestronglyMeasurable
      · exact le_add_self.trans (hKnorm N)
    refine ⟨(hKmem N).2.2.2.mono_exponent (ENNReal.ofReal_le_ofReal (by norm_num : (4:ℝ)*2 ≤ 4*3)), ?_⟩
    exact hyn4p.trans (ENNReal.ofReal_le_ofReal ((le_max_left B9 Cerr).trans (le_max_right _ _)))
  have hsmooth : ∀ N eps, (0 < eps ∧ eps < 1 / 8) →
      eLpNorm (fun om => inverseResponse S (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) L0 -
          inverseResponse S (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
            ((sobolevVolumeLoad (fL2 eps)).comp S.space.subtypeL))
        (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (B * eps ^ (1 / 4 : ℝ)) := by
    intro N eps heps
    have herr := hme M Rm H hIC hMe eps heps.1 heps.2 (fun _ om => fL2 eps)
      (fun _ om => hfL2 eps heps) N (Classical.arbitrary (BilateralField d))
    have hCB : Cerr ≤ B := (le_max_right B9 Cerr).trans (le_max_right _ _)
    exact herr.trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg heps.1.le _)))
  exact hmainN M ⟨hMδpos, hMN⟩ Rm hRC hlog H hIC K13 hKm hK0 hgrowth hKmom hyepsB hyNB hsmooth

end Paper
