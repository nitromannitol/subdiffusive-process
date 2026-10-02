import SubdiffusiveProcess.Paper.large_cube_killed_inverse_band
import SubdiffusiveProcess.Paper.prop_growth
import SubdiffusiveProcess.Paper.prop_growth_large_root
import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy




open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology InnerProductSpace ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

local instance aux_response_l1_compact_model_l1_fact : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 1) := ⟨by norm_num⟩

/-- Transport a killed-graph element to the weak Sobolev graph, with the membership explicitly
supplied by the response space's `le_weak` field. -/
def aux_response_l1_compact_model_killedToWeak {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ Kp : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
        Kp * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (w : (killedResponseSpace hP).space) : weakSobolevGraph (centeredCube z r hr) :=
  ⟨w.val, (killedResponseSpace hP).le_weak w.2⟩



theorem aux_response_l1_compact_model_killed_response_solves_dirichlet
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {z : SpatialCoordinates d} {r : ℝ} (hr : 0 < r)
    (hP : ∃ Kp : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
        Kp * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (f : DomainL2 (centeredCube z r hr)) :
    SolvesDirichlet a (f : SpatialCoordinates d → ℝ)
      (0 : weakSobolevGraph (centeredCube z r hr))
      (aux_response_l1_compact_model_killedToWeak z r hr hP (responseSolution (killedResponseSpace hP) a
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL))) := by
  refine ⟨?_, ?_⟩
  · have hsub :
        ((↑(aux_response_l1_compact_model_killedToWeak z r hr hP (responseSolution (killedResponseSpace hP) a
              ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL))) :
            SobolevData (centeredCube z r hr)) -
          ((↑(0 : weakSobolevGraph (centeredCube z r hr))) :
            SobolevData (centeredCube z r hr))) =
        (responseSolution (killedResponseSpace hP) a
          ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val := by
      simp [aux_response_l1_compact_model_killedToWeak]
    rw [hsub]
    exact (responseSolution (killedResponseSpace hP) a
      ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).2
  · intro ψ
    have hform :
        (sobolevCoefficientForm a)
            (↑(aux_response_l1_compact_model_killedToWeak z r hr hP (responseSolution (killedResponseSpace hP) a
              ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL))) :
              SobolevData (centeredCube z r hr))
            (↑ψ : SobolevData (centeredCube z r hr)) =
          responseForm (killedResponseSpace hP) a
            (responseSolution (killedResponseSpace hP) a
              ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL))
            (⟨(ψ : SobolevData (centeredCube z r hr)), ψ.2⟩ :
              ↥((killedResponseSpace hP).space)) := by
      simp only [sobolevCoefficientForm_apply, responseForm_apply, aux_response_l1_compact_model_killedToWeak,
        Subtype.coe_mk]
    rw [hform, SubdiffusiveProcess.responseSolution_spec, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, SubdiffusiveProcess.sobolevVolumeLoad_apply]

/-- **Localization conversion**: the coefficient energy localized to `Metric.ball x ρ` equals the
one localized to `Metric.ball x ρ ∩ Q`, since both integrate against `volume.restrict Q`. -/
theorem aux_response_l1_compact_model_localGradientEnergy_ball_eq_inter
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Q) (g : HilbertGradient Q) (x : SpatialCoordinates d) (ρ : ℝ) :
    localGradientEnergy a (s := Metric.ball x ρ) (Metric.isOpen_ball.measurableSet) g =
      localGradientEnergy a (s := Metric.ball x ρ ∩ (Q : Set (SpatialCoordinates d)))
        (Metric.isOpen_ball.measurableSet.inter Q.isOpen.measurableSet) g := by
  have hball : (volume.restrict (Q : Set (SpatialCoordinates d))).restrict (Metric.ball x ρ) =
      volume.restrict (Metric.ball x ρ ∩ (Q : Set (SpatialCoordinates d))) :=
    Measure.restrict_restrict (μ := volume) (Metric.isOpen_ball.measurableSet)
  have hball2 : (volume.restrict (Q : Set (SpatialCoordinates d))).restrict
        (Metric.ball x ρ ∩ (Q : Set (SpatialCoordinates d))) =
      volume.restrict ((Metric.ball x ρ ∩ (Q : Set (SpatialCoordinates d))) ∩
        (Q : Set (SpatialCoordinates d))) :=
    Measure.restrict_restrict (μ := volume)
      (Metric.isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
  have hsq : ((Metric.ball x ρ ∩ (Q : Set (SpatialCoordinates d))) ∩
        (Q : Set (SpatialCoordinates d))) =
      Metric.ball x ρ ∩ (Q : Set (SpatialCoordinates d)) := by
    rw [Set.inter_assoc, Set.inter_self]
  rw [localGradientEnergy_eq_integral, localGradientEnergy_eq_integral]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hball, hball2, hsq]

/-- **Identification**: the consumer's quadratic test at the volume source `f` is exactly the
original potential response of `inverseResponseData` at the induced load. -/
theorem aux_response_l1_compact_model_quadraticTest_eq_potentialResponse
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {z : SpatialCoordinates d} {r : ℝ} (hr : 0 < r)
    (hP : ∃ Kp : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
        Kp * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (om : BilateralField d)
    (f : DomainL2 (centeredCube z r hr)) :
    ⟪f, (responseSolution (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr)
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1⟫_ℝ =
      SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
        (inverseResponseData (killedResponseSpace hP)
          ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)) M H N om := by
  rw [SubdiffusiveProcess.Lnorm.potentialResponseOriginal_inverse]
  rw [SubdiffusiveProcess.inverseResponse]
  rw [SubdiffusiveProcess.responseSolution_spec (killedResponseSpace hP)
    (cutoffPositiveCoefficient M H om N z hr)
    ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)]
  rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [L2.inner_def, SubdiffusiveProcess.sobolevVolumeLoad_apply]
  refine integral_congr_ae ?_
  filter_upwards with a
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

/-- **The actual-model local-energy profile** (constructed from the installed growth theorems, not
assumed), for every cube radius `r > 0`: `prop_growth` covers `r ≤ 1` and `prop_growth_large_root`
covers `r > 1`; both have the same statement, so the profile is obtained by a case split.  The
disorder threshold is fixed before the model, the cube and the source. -/
theorem aux_response_l1_compact_model_local_energy_profile
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M) (Sreg : in_6_16 d M)
        (_It : in_iteration d M E Sreg) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ0 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
          (hP : ∃ Kp : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
            ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
              Kp * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
          (Idx : Type) [Countable Idx]
          (fL2 : Idx → DomainL2 (centeredCube z r hr)) (Kf : Idx → ℝ)
          (_hKf0 : ∀ i, 0 ≤ Kf i)
          (_hKf : ∀ i, ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
            |(fL2 i : SpatialCoordinates d → ℝ) y| ≤ Kf i),
        ∃ K : Idx → ℕ → BilateralField d → ℝ, ∃ BK : Idx → ℝ,
          (∀ i, 0 ≤ BK i) ∧
          (∀ i N, AEStronglyMeasurable (K i N) (chaosSampleLaw M).toMeasure) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ i N, 0 ≤ K i N om) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ i N (x : SpatialCoordinates d),
            x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) →
            ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
              localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x ρ) (Metric.isOpen_ball.measurableSet)
                (subspaceGradient (killedResponseSpace hP).space
                  (responseSolution (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr)
                    ((sobolevVolumeLoad (fL2 i)).comp (killedResponseSpace hP).space.subtypeL))) ≤
                K i N om * ρ ^ ((d : ℝ) - 1 / 2)) ∧
          (∀ i N, MemLp (K i N) (ENNReal.ofReal (3 * 2)) (chaosSampleLaw M).toMeasure ∧
            eLpNorm (K i N) (ENNReal.ofReal (3 * 2)) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal (BK i)) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  obtain ⟨δ1, hδ1, hgrow1⟩ := prop_growth d hd E Pc Xc W Cp Sf
    ((d : ℝ) - 1 / 2) (1 / 2) 1 (fun _ : Fin 1 => 6)
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨δ2, hδ2, hgrow2⟩ := prop_growth_large_root d hd E Pc Xc W Cp Sf
    ((d : ℝ) - 1 / 2) (1 / 2) 1 (fun _ : Fin 1 => 6)
    (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro M Rm Sreg It H hH hδ z r hr hP Idx _ fL2 Kf hKf0 hKf
  obtain ⟨Kg, Cb, hKgMem, hKgBound, hKg1, hKgloc⟩ := (le_or_gt r 1).elim
    (fun h => hgrow1 M Rm Sreg It H hH (hδ.trans (min_le_left _ _)) z r hr h)
    (fun h => hgrow2 M Rm Sreg It H hH (hδ.trans (min_le_right _ _)) z r hr h)
  let Cphi : ℝ := c2Norm (closedCube z r hr : Set (SpatialCoordinates d))
    (fun _ : SpatialCoordinates d => (0 : ℝ))
  refine ⟨fun i N => ((Kf i + Cphi) ^ 2) • (Kg N),
      fun i => max (Cb 0) 1 * (Kf i + Cphi) ^ 2, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have h0 : (0 : ℝ) ≤ max (Cb 0) 1 := le_max_of_le_right zero_le_one
    positivity
  · intro i N
    exact ((hKgMem 0 N).1.const_smul ((Kf i + Cphi) ^ 2))
  · filter_upwards [hKg1] with om hom
    intro i N
    have h1 : (1 : ℝ) ≤ Kg N om := hom N
    have h2 : (0 : ℝ) ≤ (Kf i + Cphi) ^ 2 := sq_nonneg _
    simpa only [Pi.smul_apply, smul_eq_mul] using mul_nonneg h2 (by linarith)
  · filter_upwards [hKgloc] with om hom
    intro i N x hx ρ hρ0 hρ1
    have hloc := (hom N (fL2 i : SpatialCoordinates d → ℝ) (Kf i) (hKf0 i)
      ((Lp.aestronglyMeasurable (fL2 i)).aemeasurable) (hKf i)
      (fun _ : SpatialCoordinates d => (0 : ℝ)) Cphi
      contDiff_const (le_of_eq rfl)
      (0 : weakSobolevGraph (centeredCube z r hr))
      (aux_response_l1_compact_model_killedToWeak z r hr hP
        (responseSolution (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr)
          ((sobolevVolumeLoad (fL2 i)).comp (killedResponseSpace hP).space.subtypeL)))
      (by
        simpa only [aux_response_l1_compact_model_killedToWeak, Subtype.coe_mk] using
          (Lp.coeFn_zero ℝ 2
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))))
      (aux_response_l1_compact_model_killed_response_solves_dirichlet hr hP
        (cutoffPositiveCoefficient M H om N z hr) (fL2 i))).1 x ρ hx hρ0 hρ1
    calc localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
          (s := Metric.ball x ρ) (Metric.isOpen_ball.measurableSet)
          (subspaceGradient (killedResponseSpace hP).space
            (responseSolution (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr)
              ((sobolevVolumeLoad (fL2 i)).comp (killedResponseSpace hP).space.subtypeL)))
        = localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
            (s := Metric.ball x ρ ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
            (Metric.isOpen_ball.measurableSet.inter
              (centeredCube z r hr).isOpen.measurableSet)
            (subspaceGradient (killedResponseSpace hP).space
              (responseSolution (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr)
                ((sobolevVolumeLoad (fL2 i)).comp (killedResponseSpace hP).space.subtypeL))) :=
          aux_response_l1_compact_model_localGradientEnergy_ball_eq_inter _ _ x ρ
      _ ≤ Kg N om * (Kf i + Cphi) ^ 2 * ρ ^ ((d : ℝ) - 1 / 2) := hloc
      _ = ((((Kf i + Cphi) ^ 2) • (Kg N)) om) * ρ ^ ((d : ℝ) - 1 / 2) := by
          simp only [Pi.smul_apply, smul_eq_mul]; ring
  · intro i N
    have hb : (0 : ℝ) ≤ (Kf i + Cphi) ^ 2 := sq_nonneg _
    have hscaled := (hKgMem 0 N).const_smul ((Kf i + Cphi) ^ 2)
    refine ⟨by simpa only [show (3 : ℝ) * 2 = 6 by norm_num] using hscaled, ?_⟩
    rw [show (3 : ℝ) * 2 = 6 from by norm_num]
    show eLpNorm (((Kf i + Cphi) ^ 2) • (Kg N)) (ENNReal.ofReal 6)
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (max (Cb 0) 1 * (Kf i + Cphi) ^ 2)
    refine (eLpNorm_const_smul_le (c := (Kf i + Cphi) ^ 2) (f := Kg N)).trans ?_
    rw [Real.enorm_eq_ofReal hb]
    refine (mul_le_mul_right (hKgBound 0 N) (ENNReal.ofReal ((Kf i + Cphi) ^ 2))).trans ?_
    rw [← ENNReal.ofReal_mul hb]
    exact ENNReal.ofReal_le_ofReal (by
      rw [mul_comm ((Kf i + Cphi) ^ 2) (Cb 0)]
      exact mul_le_mul_of_nonneg_right (le_max_left (Cb 0) 1) hb)

/-- Transport of relative compactness of an `L^p` sequence along an equality of exponents and an
everywhere equality of the representing functions. -/
theorem aux_response_l1_compact_model_compact_transport
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p = q)
    (f g : ℕ → α → ℝ) (hfg : ∀ n, f n = g n)
    (hp : ∀ n, MemLp (f n) p μ) (hq : ∀ n, MemLp (g n) q μ)
    (h : IsCompact (closure (Set.range fun n => (hp n).toLp (f n)))) :
    IsCompact (closure (Set.range fun n => (hq n).toLp (g n))) := by
  subst hpq
  have hfun : f = g := funext hfg
  subst hfun
  exact h



theorem aux_response_l1_compact_model_source_l1_compact
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M) (Sreg : in_6_16 d M)
        (_It : in_iteration d M E Sreg) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ0 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
          (hP : ∃ Kp : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
            ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
              Kp * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
          (F : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ F → HasCompactSupport F →
          tsupport F ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (fL2 : DomainL2 (centeredCube z r hr)),
            (fL2 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] F →
          ∃ hmem : (∀ N, MemLp (fun om : BilateralField d => ⟪fL2,
              (responseSolution (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr)
                ((sobolevVolumeLoad fL2).comp
                  (killedResponseSpace hP).space.subtypeL)).val.1⟫_ℝ)
            1 (chaosSampleLaw M).toMeasure),
            IsCompact (closure (Set.range (fun N => (hmem N).toLp
              (fun om : BilateralField d => ⟪fL2,
                (responseSolution (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr)
                  ((sobolevVolumeLoad fL2).comp
                    (killedResponseSpace hP).space.subtypeL)).val.1⟫_ℝ)))) := by
  obtain ⟨δp, hδp, hprof⟩ :=
    aux_response_l1_compact_model_local_energy_profile hd E Pc Xc W Cp Sf
  obtain ⟨δb, hδb, hband⟩ := large_cube_killed_inverse_band d hd E Pc Xc W
  refine ⟨min 1 (min δp δb), lt_min one_pos (lt_min hδp hδb), ?_⟩
  intro M Rm Sreg It H hH hδ z r hr hP F hF hFc hFsupp fL2 hfL2
  have hle1 : M.delta ≤ 1 := hδ.trans (min_le_left _ _)
  have hlep : M.delta ≤ δp := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hleb : M.delta ≤ δb := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  by_cases hF0 : ∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), F x ≠ 0
  · 
    obtain ⟨C, hC⟩ := hF.continuous.bounded_above_of_compact_support hFc
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    have hKf : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        |(fL2 : SpatialCoordinates d → ℝ) y| ≤ C := by
      filter_upwards [hfL2] with y hy
      rw [hy]
      simpa only [Real.norm_eq_abs] using hC y
    obtain ⟨K, BK, hBK, hKmeas, hKnonneg, hKlocal, hKmem⟩ :=
      hprof M Rm Sreg It H hH hlep z r hr hP Unit (fun _ => fL2) (fun _ => C)
        (fun _ => hC0) (fun _ => hKf)
    obtain ⟨Cmom, Cband, hCmom, hCband, hmoment, hbandRN⟩ :=
      hband M Rm Sreg It H hH (le_min hle1 hleb) z r hr hP F hF hFc hFsupp hF0 fL2 hfL2
        (K ()) (BK ()) (hBK ()) (fun N => hKmeas () N)
        (hKnonneg.mono fun om ho => ho ()) (hKlocal.mono fun om ho => ho ())
        (fun N => by
          simpa only [show (3 : ℝ) * 2 = 6 by norm_num] using hKmem () N)
    have haD : 0 < aux_prop16_aD d := by
      have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have hnum : 0 < (d : ℝ) - 1 / 2 := by linarith
      have hcrosspos : 0 < ((d : ℝ) - 1 / 2) - (d : ℝ) + 1 := by linarith
      have hden : 0 < ((d : ℝ) - 1 / 2) + 1 := by linarith
      have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
      dsimp [aux_prop16_aD]
      positivity
    let S := killedResponseSpace hP
    let Lx : S.space →L[ℝ] ℝ := (sobolevVolumeLoad fL2).comp S.space.subtypeL
    have hfun : ∀ N, SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
        (inverseResponseData S Lx) M H N =
        fun om => inverseResponse S (cutoffPositiveCoefficient M H om N z hr) Lx := fun N =>
      funext fun om =>
        SubdiffusiveProcess.Lnorm.potentialResponseOriginal_inverse z r hr S Lx M H N om
    have hmem6 : ∀ (i : Unit) N,
        MemLp (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
          (inverseResponseData S ((fun _ : Unit => Lx) i)) M H N)
          (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure := by
      intro _ N
      show MemLp (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
          (inverseResponseData S Lx) M H N) (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure
      rw [hfun N]
      exact (hmoment N).1
    have hmom6 : ∀ (i : Unit) N,
        eLpNorm (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
          (inverseResponseData S ((fun _ : Unit => Lx) i)) M H N)
          (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cmom := by
      intro _ N
      show eLpNorm (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
          (inverseResponseData S Lx) M H N) (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal Cmom
      rw [hfun N]
      exact (hmoment N).2
    have hband2 : ∀ (i : Unit) (h N : ℕ),
        eLpNorm
          (fun omega =>
            SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
                (inverseResponseData S ((fun _ : Unit => Lx) i)) M H N omega -
              (((chaosSampleLaw M).toMeasure)[
                SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
                  (inverseResponseData S ((fun _ : Unit => Lx) i)) M H N |
                bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
          (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-aux_prop16_aD d * (h : ℝ))) := by
      intro _ h N
      show eLpNorm
          (fun omega =>
            SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
                (inverseResponseData S Lx) M H N omega -
              (((chaosSampleLaw M).toMeasure)[
                SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
                  (inverseResponseData S Lx) M H N |
                bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
          (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-aux_prop16_aD d * (h : ℝ)))
      rw [hfun N]
      exact hbandRN h N
    obtain ⟨hl1mem, hl1compact⟩ :=
      aux_large_cube_killed_inverse_response_l1_compact d z r hr M H hH Unit S
        (fun _ => Lx) (fun _ => Cmom) (fun _ => Cband) (aux_prop16_aD d)
        (fun _ => hCmom) (fun _ => hCband.le) haD hmem6 hmom6 hband2
    have hpt : ∀ N, (fun om : BilateralField d => ⟪fL2,
        (responseSolution S (cutoffPositiveCoefficient M H om N z hr) Lx).val.1⟫_ℝ) =
        SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
          (inverseResponseData S Lx) M H N := fun N =>
      funext fun om => aux_response_l1_compact_model_quadraticTest_eq_potentialResponse hr hP M H
        N om fL2
    have hmem1 : ∀ N, MemLp (fun om : BilateralField d => ⟪fL2,
        (responseSolution S (cutoffPositiveCoefficient M H om N z hr) Lx).val.1⟫_ℝ)
        1 (chaosSampleLaw M).toMeasure := fun N => by
      rw [hpt N]
      exact hl1mem () N
    refine ⟨hmem1, ?_⟩
    exact aux_response_l1_compact_model_compact_transport (p := ENNReal.ofReal 1) (q := 1)
      (by simp)
      (fun N => SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
        (inverseResponseData S Lx) M H N)
      (fun N om => ⟪fL2, (responseSolution S (cutoffPositiveCoefficient M H om N z hr) Lx).val.1⟫_ℝ)
      (fun N => (hpt N).symm)
      (fun N => (hmem6 () N).mono_exponent (by norm_num : ENNReal.ofReal 1 ≤ ENNReal.ofReal 6))
      hmem1 (hl1compact ())
  · -- zero source: the test function vanishes identically
    push_neg at hF0
    have hzero : fL2 = 0 := by
      have hF0ae : F =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
          (0 : SpatialCoordinates d → ℝ) := by
        rw [Filter.EventuallyEq, ae_restrict_iff' (centeredCube z r hr).isOpen.measurableSet]
        exact Filter.Eventually.of_forall fun x hx => hF0 x hx
      exact Lp.eq_zero_iff_ae_eq_zero.2 (hfL2.trans hF0ae)
    have hfun0 : ∀ N, (fun om : BilateralField d => ⟪fL2,
        (responseSolution (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr)
          ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL)).val.1⟫_ℝ) =
        (0 : BilateralField d → ℝ) := fun N =>
      funext fun om => by simp [hzero]
    have hmem0 : ∀ N, MemLp (fun om : BilateralField d => ⟪fL2,
        (responseSolution (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr)
          ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL)).val.1⟫_ℝ)
        1 (chaosSampleLaw M).toMeasure := fun N => by
      rw [hfun0 N]
      exact MemLp.zero'
    refine ⟨hmem0, ?_⟩
    refine IsCompact.of_isClosed_subset (isCompact_singleton (x := (0 : Lp ℝ 1
      (chaosSampleLaw M).toMeasure))) isClosed_closure ?_
    refine closure_minimal ?_ isClosed_singleton
    rintro _ ⟨N, rfl⟩
    rw [Set.mem_singleton_iff, Lp.eq_zero_iff_ae_eq_zero]
    refine (MemLp.coeFn_toLp (hmem0 N)).trans ?_
    rw [hfun0 N]

/-- Transfer of relative `L¹` compactness along a measure-preserving map: an everywhere
representation `f n = g n ∘ field` of the tests on the source space transports `L¹` membership and
compact closure of the `L¹` classes from the target law to the source measure. -/
theorem aux_response_l1_compact_model_field_transfer
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω] {Pm : Measure α} {P : Measure Ω}
    {field : Ω → α} (hmp : MeasurePreserving field P Pm)
    (g : ℕ → α → ℝ) (f : ℕ → Ω → ℝ) (hfg : ∀ n, f n = g n ∘ field)
    (hg : ∀ n, MemLp (g n) 1 Pm)
    (hc : IsCompact (closure (Set.range fun n => (hg n).toLp (g n)))) :
    ∃ hf : (∀ n, MemLp (f n) 1 P),
      IsCompact (closure (Set.range fun n => (hf n).toLp (f n))) := by
  have hf : ∀ n, MemLp (f n) 1 P := fun n => by
    rw [hfg n]
    exact (hg n).comp_measurePreserving hmp
  refine ⟨hf, ?_⟩
  let T : Lp ℝ 1 Pm → Lp ℝ 1 P := Lp.compMeasurePreserving field hmp
  have hT : Continuous T := (Lp.isometry_compMeasurePreserving (p := 1) hmp).continuous
  have hK : IsCompact (T '' closure (Set.range fun n => (hg n).toLp (g n))) := hc.image hT
  have hsub : (Set.range fun n => (hf n).toLp (f n)) ⊆
      T '' closure (Set.range fun n => (hg n).toLp (g n)) := by
    rintro _ ⟨n, rfl⟩
    refine ⟨(hg n).toLp (g n), subset_closure ⟨n, rfl⟩, ?_⟩
    have hfn : f n = g n ∘ field := hfg n
    simp only [T, Lp.toLp_compMeasurePreserving]
    congr 1
    exact hfn.symm
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hK.isClosed)

/-- A response space with the killed-graph carrier is the killed response space (the remaining
fields are propositions). -/
theorem aux_response_l1_compact_model_space_eq
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (hP : ∃ Kp : ℝ≥0, ∀ w : killedSobolevGraph Q,
      ‖(w : SobolevData Q).1‖ ≤ Kp * ‖subspaceGradient (killedSobolevGraph Q) w‖)
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q) :
    S = killedResponseSpace hP := by
  obtain ⟨sp, a, b, c⟩ := S
  simp only at hS
  subst hS
  rfl

/-- **Principal: actual-model `L¹` compactness of the killed quadratic responses.**

The premises are exactly the frozen data of `in_joint_extraction_inprob` that concern the actual
killed inverse family (`Sspace`/`GN`/`hGN`/`hS`, the test sets `D`, the law transfer `field`/`hmap`)
plus the standing inputs of the growth theorems, and the catalogue premise that every test in `D i`
has a smooth compactly supported representative in its cube.  The zero test is included.  The
disorder threshold `δ0` is chosen before the model, the (countable family of) cubes and the test
sources.  The conclusion is the frozen principal's `hmem` and (for that `hmem`) `hcompact`. -/
theorem response_l1_compact_model
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M) (Sreg : in_6_16 d M)
        (_It : in_iteration d M E Sreg) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ0 →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d),
        Measurable field → Measure.map field P = (chaosSampleLaw M).toMeasure →
      ∀ (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (D : (i : ℕ) → Set (DomainL2 (centeredCube (z i) (r i) (hr i))))
        (_hDsmooth : ∀ i, ∀ x ∈ D i, ∃ F : SpatialCoordinates d → ℝ,
          ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
          tsupport F ⊆ (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) ∧
          (x : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))] F)
        (_hGN : ∀ i N om f, GN i N om f =
          (responseSolution (Sspace i)
            (Lane4.cutoffPositiveCoefficient M H (field om) N (z i) (hr i))
            ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1)
        (_hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i))),
      ∃ hmem : (∀ i (x : D i) n,
          MemLp (fun om => inner ℝ (x : DomainL2 (centeredCube (z i) (r i) (hr i)))
            (GN i n om x)) 1 P),
        ∀ i (x : D i), IsCompact (closure (Set.range (fun n =>
          (hmem i x n).toLp (fun om => inner ℝ
            (x : DomainL2 (centeredCube (z i) (r i) (hr i))) (GN i n om x))))) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨δ0, hδ0, hsrc⟩ := aux_response_l1_compact_model_source_l1_compact hd E Pc Xc W Cp Sf
  refine ⟨δ0, hδ0, ?_⟩
  intro M Rm Sreg It H hH hδ Ω _ P field hfield hmap z r hr Sspace GN D hDsmooth hGN hS
  have hmp : MeasurePreserving field P (chaosSampleLaw M).toMeasure := ⟨hfield, hmap⟩
  have hSeq : ∀ i, Sspace i = killedResponseSpace (centeredCube_killedPoincare (z i) (hr i)) :=
    fun i => aux_response_l1_compact_model_space_eq _ (Sspace i) (hS i)
  have hper : ∀ i (x : D i), ∃ hf : (∀ n, MemLp (fun om => inner ℝ
        (x : DomainL2 (centeredCube (z i) (r i) (hr i))) (GN i n om x)) 1 P),
      IsCompact (closure (Set.range (fun n => (hf n).toLp (fun om => inner ℝ
        (x : DomainL2 (centeredCube (z i) (r i) (hr i))) (GN i n om x))))) := by
    intro i x
    obtain ⟨F, hF, hFc, hFsupp, hFx⟩ := hDsmooth i x.1 x.2
    obtain ⟨hg, hc⟩ := hsrc M Rm Sreg It H hH hδ (z i) (r i) (hr i)
      (centeredCube_killedPoincare (z i) (hr i)) F hF hFc hFsupp x.1 hFx
    refine aux_response_l1_compact_model_field_transfer hmp _ _ ?_ hg hc
    intro n
    funext om
    have hGNx := hGN i n om x.1
    rw [hSeq i] at hGNx
    simp only [Function.comp_apply]
    rw [hGNx]
  exact ⟨fun i x => (hper i x).choose, fun i x => (hper i x).choose_spec⟩

end Paper
