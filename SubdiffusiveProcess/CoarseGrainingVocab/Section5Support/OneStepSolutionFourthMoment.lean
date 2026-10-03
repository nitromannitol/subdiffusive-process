module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMixedNorm
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepShellDerivativeAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSolutionLawTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.NegativeBesovSupport

@[expose] public section

/-!
# Fourth moments of the finite-volume one-step solution operators

The measurable Dirichlet and Neumann solution gradients are contractions of
the suffix forcing.  This file combines that samplewise fact with the
fixed-point lognormal moment estimate and Tonelli.  The result is the
normalized parent-gradient budget required after translating the Neumann
cell problem.

The proof mirrors the solution-operator moment passage in
`Algsuperdiff/Section3/Provider/Diffusivity/Corrector/
CorrectorMeasurableQuartic.lean`.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


private theorem normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet
    {d : ℕ} (m : ℤ) :
    normalizedCubeMeasure (originCube d m) =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) := by
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

/-- Normalizing the cube measure is the same as multiplying the Hilbert
`L²` norm by `|Q|⁻¹ᴵ²`. -/
theorem toReal_eLpNorm_hilbertify_grad_two_normalizedCubeMeasure
    {d : ℕ} (m : ℤ) (u : H1Function (openCubeSet (originCube d m))) :
    (eLpNorm (hilbertifyVecField u.grad) 2
      (normalizedCubeMeasure (originCube d m))).toReal =
        (cubeVolume (originCube d m))⁻¹ ^ (1 / 2 : ℝ) *
          ‖u.gradToHilbertVectorL2‖ := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)
  have hc : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.2
    (inv_pos.mpr (cubeVolume_pos (originCube d m)))
  rw [normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet]
  change (eLpNorm (hilbertifyVecField u.grad) 2
    (c • volume.restrict (openCubeSet (originCube d m)))).toReal = _
  rw [eLpNorm_smul_measure_of_ne_zero hc,
    CubeCalderonZygmund.eLpNorm_hilbertify_grad_two_eq_ofReal_norm_gradToHilbertVectorL2]
  norm_num only [ENNReal.toReal_ofNat]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  simp only [c, ENNReal.toReal_ofReal, inv_nonneg, cubeVolume_nonneg]
  rw [ENNReal.toReal_ofReal (norm_nonneg _)]
  congr 2
  norm_num

/-- The same normalization identity for an arbitrary vector `L²` class. -/
theorem toReal_eLpNorm_hilbertifyVecField_two_normalizedCubeMeasure
    {d : ℕ} (m : ℤ) {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet (originCube d m)) F) :
    (eLpNorm (hilbertifyVecField F) 2
      (normalizedCubeMeasure (originCube d m))).toReal =
        (cubeVolume (originCube d m))⁻¹ ^ (1 / 2 : ℝ) *
          ‖toHilbertVectorL2OfVecField hF‖ := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)
  have hc : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.2
    (inv_pos.mpr (cubeVolume_pos (originCube d m)))
  rw [normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet]
  change (eLpNorm (hilbertifyVecField F) 2
    (c • volume.restrict (openCubeSet (originCube d m)))).toReal = _
  rw [eLpNorm_smul_measure_of_ne_zero hc,
    CubeCalderonZygmund.eLpNorm_hilbertifyVecField_two_eq_ofReal_norm_toHilbertVectorL2 hF]
  norm_num only [ENNReal.toReal_ofNat]
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  simp only [c, ENNReal.toReal_ofReal, inv_nonneg, cubeVolume_nonneg]
  rw [ENNReal.toReal_ofReal (norm_nonneg _)]
  congr 2
  norm_num

/-- Joint spatial--random fourth moment of the centered suffix multiplier on
an arbitrary origin cube. -/
theorem lintegral_lintegral_oneStepMultiplier_four_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (m : ℤ)
    (hh : 0 < h) :
    ∫⁻ omega, ∫⁻ x, ‖oneStepMultiplierAt M n h x omega‖ₑ ^ (4 : ℝ)
        ∂normalizedCubeMeasure (originCube d m) ∂M.P.toMeasure ≤
      (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
  let Q := originCube d m
  let X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d → ℝ := fun q ↦
    oneStepMultiplierAt M n h q.2 q.1
  have hX : Measurable X := measurable_oneStepMultiplierAt_uncurry M n h
  have hjoint : AEMeasurable
      (Function.uncurry fun omega x ↦ ‖X (omega, x)‖ₑ ^ (4 : ℝ))
      (M.P.toMeasure.prod (normalizedCubeMeasure Q)) := by
    simpa only [Function.uncurry_apply_pair] using!
      (hX.enorm.pow_const (4 : ℝ)).aemeasurable
  have hswap := lintegral_lintegral_swap hjoint
  rw [hswap]
  have hpoint : ∀ᵐ x ∂normalizedCubeMeasure Q,
      (∫⁻ omega, ‖X (omega, x)‖ₑ ^ (4 : ℝ) ∂M.P.toMeasure) ≤
        (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
    filter_upwards with x
    let R : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega ↦ X (omega, x)
    have hRmeas : AEStronglyMeasurable R M.P.toMeasure :=
      ((hX.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
    have h48 : eLpNorm R 4 M.P.toMeasure ≤ eLpNorm R 8 M.P.toMeasure :=
      eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    have h8 : eLpNorm R 8 M.P.toMeasure ≤
        ENNReal.ofReal (oneStepRatioMinusOneEightBound M h) := by
      have hrepr : R = fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d ↦
          Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
            (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) - 1 := by
        funext omega
        dsimp only [R, X]
        rw [← oneStepMultiplierContinuousMap_apply M n h omega x hh]
        rfl
      rw [hrepr]
      exact eLpNorm_oneStepRatioMinusOne_eight_le M n h x hh
    have h4 := h48.trans h8
    have hpow := ENNReal.rpow_le_rpow h4 (by norm_num : (0 : ℝ) ≤ 4)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hRmeas] at hpow
    norm_num only [ENNReal.toReal_ofNat] at hpow
    have hquarter : (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num
    rw [hquarter, ENNReal.rpow_inv_rpow (by norm_num : (4 : ℝ) ≠ 0)] at hpow
    simpa only [R, X, ENNReal.rpow_natCast] using hpow
  calc
    (∫⁻ x, ∫⁻ omega, ‖X (omega, x)‖ₑ ^ (4 : ℝ)
        ∂M.P.toMeasure ∂normalizedCubeMeasure Q) ≤
      ∫⁻ _x, (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^
          (4 : ℝ) ∂normalizedCubeMeasure Q := lintegral_mono_ae hpoint
    _ = (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
      rw [lintegral_const]
      simp [normalizedCubeMeasure_apply_univ]

/-- For a Euclidean unit probe, the Hilbert-vector shell forcing has exactly
the scalar multiplier's normalized spatial `L²` norm. -/
theorem eLpNorm_oneStepShellForcing_eq_multiplier_of_unit {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    eLpNorm (hilbertifyVecField
        (oneStepShellForcingH1 M n h omega p (originCube d m) hh).toField)
        2 (normalizedCubeMeasure (originCube d m)) =
      eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega)
        2 (normalizedCubeMeasure (originCube d m)) := by
  apply eLpNorm_congr_norm_ae
  · simpa only [hilbertifyVecField] using!
      (HilbertVec.continuousLinearEquivVec d).symm.continuous.comp_aestronglyMeasurable
        (memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet (originCube d m)
          (oneStepShellForcingH1 M n h omega p (originCube d m) hh
            ).memVectorL2_toField_openCubeSet).aestronglyMeasurable
  · simpa using!
      ((measurable_oneStepMultiplierAt_uncurry M n h).comp
        ((measurable_const (a := omega)).prodMk measurable_id)).aestronglyMeasurable
  filter_upwards with x
  simp only [hilbertifyVecField]
  rw [oneStepShellForcing_paired_toField M n h omega p
    (originCube d m) hh, oneStepShellForcingW14_toField_apply]
  have hpnorm : ‖HilbertVec.ofVec p‖ = 1 := by
    have hsq := HilbertVec.norm_sq_ofVec p
    have hp' : vecDot p p = 1 := by
      simpa [vecNormSq, vecDot] using hp
    rw [hp'] at hsq
    nlinarith [norm_nonneg (HilbertVec.ofVec p)]
  change ‖HilbertVec.ofVec (oneStepMultiplierAt M n h x omega • p)‖ = _
  rw [show HilbertVec.ofVec (oneStepMultiplierAt M n h x omega • p) =
      oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p by rfl,
    norm_smul, hpnorm, mul_one, Real.norm_eq_abs]

/-- Samplewise normalized Dirichlet-gradient control by the scalar suffix
multiplier. -/
theorem oneStepOriginDirichletNormalizedGradient_le_multiplier {d : ℕ}
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    oneStepOriginDirichletNormalizedGradient M n h p m omega ≤
      (eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega) 2
        (normalizedCubeMeasure (originCube d m))).toReal := by
  let Q := originCube d m
  let G := oneStepShellForcingH1 M n h omega p Q hh
  let hG : MemVectorL2 (openCubeSet Q) G.toField :=
    G.memVectorL2_toField_openCubeSet
  have hfactor : 0 ≤ (cubeVolume Q)⁻¹ ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _
  have hcontract := norm_oneStepOriginDirichletGradientL2_le_forcing
    M n h p m omega hh
  calc
    oneStepOriginDirichletNormalizedGradient M n h p m omega ≤
        (cubeVolume Q)⁻¹ ^ (1 / 2 : ℝ) *
          ‖oneStepShellForcingL2 M n h p Q omega‖ := by
      exact mul_le_mul_of_nonneg_left hcontract hfactor
    _ = (eLpNorm (hilbertifyVecField G.toField) 2
        (normalizedCubeMeasure Q)).toReal := by
      rw [toReal_eLpNorm_hilbertifyVecField_two_normalizedCubeMeasure m hG]
      apply congrArg fun t : ℝ ↦ (cubeVolume Q)⁻¹ ^ (1 / 2 : ℝ) * t
      exact congrArg norm
        (oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
          M n h p Q omega hh)
    _ = _ := congrArg ENNReal.toReal
      (eLpNorm_oneStepShellForcing_eq_multiplier_of_unit
        M n h p m omega hh hp)

/-- Neumann counterpart of
`oneStepOriginDirichletNormalizedGradient_le_multiplier`. -/
theorem oneStepOriginNeumannNormalizedGradient_le_multiplier {d : ℕ}
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    oneStepOriginNeumannNormalizedGradient M n h p m omega ≤
      (eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega) 2
        (normalizedCubeMeasure (originCube d m))).toReal := by
  let Q := originCube d m
  let G := oneStepShellForcingH1 M n h omega p Q hh
  let hG : MemVectorL2 (openCubeSet Q) G.toField :=
    G.memVectorL2_toField_openCubeSet
  have hfactor : 0 ≤ (cubeVolume Q)⁻¹ ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _
  have hcontract := norm_oneStepOriginNeumannGradientL2_le_forcing
    M n h p m omega hh
  calc
    oneStepOriginNeumannNormalizedGradient M n h p m omega ≤
        (cubeVolume Q)⁻¹ ^ (1 / 2 : ℝ) *
          ‖oneStepShellForcingL2 M n h p Q omega‖ := by
      exact mul_le_mul_of_nonneg_left hcontract hfactor
    _ = (eLpNorm (hilbertifyVecField G.toField) 2
        (normalizedCubeMeasure Q)).toReal := by
      rw [toReal_eLpNorm_hilbertifyVecField_two_normalizedCubeMeasure m hG]
      apply congrArg fun t : ℝ ↦ (cubeVolume Q)⁻¹ ^ (1 / 2 : ℝ) * t
      exact congrArg norm
        (oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
          M n h p Q omega hh)
    _ = _ := congrArg ENNReal.toReal
      (eLpNorm_oneStepShellForcing_eq_multiplier_of_unit
        M n h p m omega hh hp)

private theorem memLp_two_oneStepMultiplier_spatial {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    MemLp (fun x ↦ oneStepMultiplierAt M n h x omega) 2
      (normalizedCubeMeasure (originCube d m)) := by
  have hcont := (oneStepMultiplierContinuousMap M n h omega).continuous
  have hmem := memLp_normalizedCubeMeasure_of_continuous
    (originCube d m) (2 : ℝ≥0∞) hcont
  convert hmem using 1
  funext x
  rw [oneStepMultiplierContinuousMap_apply M n h omega x hh]

/-- ENNReal fourth-moment budget for the normalized origin Dirichlet
solution gradient. -/
theorem lintegral_oneStepOriginDirichletNormalizedGradient_four_le
    {d : ℕ} [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (p : Vec d) (m : ℤ) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    ∫⁻ omega,
        (ENNReal.ofReal
          (oneStepOriginDirichletNormalizedGradient M n h p m omega)) ^
            (4 : ℝ) ∂M.P.toMeasure ≤
      (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
  letI : IsProbabilityMeasure (normalizedCubeMeasure (originCube d m)) :=
    ⟨normalizedCubeMeasure_apply_univ (originCube d m)⟩
  let f : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Vec d → ℝ := fun omega x ↦
    oneStepMultiplierAt M n h x omega
  have hf : ∀ omega, AEStronglyMeasurable (f omega)
      (normalizedCubeMeasure (originCube d m)) := by
    intro omega
    exact (memLp_two_oneStepMultiplier_spatial M n h m omega hh).aestronglyMeasurable
  calc
    _ ≤ ∫⁻ omega,
        (eLpNorm (f omega) 2
          (normalizedCubeMeasure (originCube d m))) ^ (4 : ℝ)
          ∂M.P.toMeasure := by
      apply lintegral_mono
      intro omega
      have htop :=
        (memLp_two_oneStepMultiplier_spatial M n h m omega hh).eLpNorm_ne_top
      have hreal := oneStepOriginDirichletNormalizedGradient_le_multiplier
        M n h p m omega hh hp
      have hENN : ENNReal.ofReal
          (oneStepOriginDirichletNormalizedGradient M n h p m omega) ≤
          eLpNorm (f omega) 2
            (normalizedCubeMeasure (originCube d m)) :=
        (ENNReal.ofReal_le_iff_le_toReal htop).2 hreal
      exact ENNReal.rpow_le_rpow hENN (by norm_num)
    _ ≤ ∫⁻ omega, ∫⁻ x, ‖f omega x‖ₑ ^ (4 : ℝ)
          ∂normalizedCubeMeasure (originCube d m) ∂M.P.toMeasure :=
      lintegral_eLpNorm_two_rpow_four_le_lintegral_lintegral_four
        M.P.toMeasure (normalizedCubeMeasure (originCube d m)) f hf
    _ ≤ _ := by
      simpa only [f] using
        lintegral_lintegral_oneStepMultiplier_four_le M n h m hh

/-- Neumann counterpart of the normalized origin fourth-moment budget. -/
theorem lintegral_oneStepOriginNeumannNormalizedGradient_four_le
    {d : ℕ} [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (p : Vec d) (m : ℤ) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    ∫⁻ omega,
        (ENNReal.ofReal
          (oneStepOriginNeumannNormalizedGradient M n h p m omega)) ^
            (4 : ℝ) ∂M.P.toMeasure ≤
      (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (4 : ℝ) := by
  letI : IsProbabilityMeasure (normalizedCubeMeasure (originCube d m)) :=
    ⟨normalizedCubeMeasure_apply_univ (originCube d m)⟩
  let f : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Vec d → ℝ := fun omega x ↦
    oneStepMultiplierAt M n h x omega
  have hf : ∀ omega, AEStronglyMeasurable (f omega)
      (normalizedCubeMeasure (originCube d m)) := by
    intro omega
    exact (memLp_two_oneStepMultiplier_spatial M n h m omega hh).aestronglyMeasurable
  calc
    _ ≤ ∫⁻ omega,
        (eLpNorm (f omega) 2
          (normalizedCubeMeasure (originCube d m))) ^ (4 : ℝ)
          ∂M.P.toMeasure := by
      apply lintegral_mono
      intro omega
      have htop :=
        (memLp_two_oneStepMultiplier_spatial M n h m omega hh).eLpNorm_ne_top
      have hreal := oneStepOriginNeumannNormalizedGradient_le_multiplier
        M n h p m omega hh hp
      have hENN : ENNReal.ofReal
          (oneStepOriginNeumannNormalizedGradient M n h p m omega) ≤
          eLpNorm (f omega) 2
            (normalizedCubeMeasure (originCube d m)) :=
        (ENNReal.ofReal_le_iff_le_toReal htop).2 hreal
      exact ENNReal.rpow_le_rpow hENN (by norm_num)
    _ ≤ ∫⁻ omega, ∫⁻ x, ‖f omega x‖ₑ ^ (4 : ℝ)
          ∂normalizedCubeMeasure (originCube d m) ∂M.P.toMeasure :=
      lintegral_eLpNorm_two_rpow_four_le_lintegral_lintegral_four
        M.P.toMeasure (normalizedCubeMeasure (originCube d m)) f hf
    _ ≤ _ := by
      simpa only [f] using
        lintegral_lintegral_oneStepMultiplier_four_le M n h m hh

private theorem integrable_four_of_lintegral_ofReal_four_lt_top
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (f : Omega → ℝ) (hf : Measurable f) (hf0 : ∀ omega, 0 ≤ f omega)
    (hfin : (∫⁻ omega, (ENNReal.ofReal (f omega)) ^ (4 : ℝ) ∂mu) < ∞) :
    Integrable (fun omega ↦ f omega ^ 4) mu := by
  refine ⟨(hf.pow_const 4).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  convert hfin using 1
  apply lintegral_congr
  intro omega
  rw [Real.enorm_eq_ofReal (pow_nonneg (hf0 omega) 4)]
  calc
    ENNReal.ofReal (f omega ^ 4) =
        ENNReal.ofReal (f omega) ^ (4 : ℕ) :=
      ENNReal.ofReal_pow (hf0 omega) 4
    _ = ENNReal.ofReal (f omega) ^ (4 : ℝ) :=
      (ENNReal.rpow_natCast _ 4).symm

/-- The normalized Dirichlet fourth-power observable is integrable under the
GMC cutoff law. -/
theorem integrable_oneStepOriginDirichletNormalizedGradientFourth
    {d : ℕ} [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (p : Vec d) (m : ℤ) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    Integrable (oneStepOriginDirichletNormalizedGradientFourth M n h p m)
      M.P.toMeasure := by
  apply integrable_four_of_lintegral_ofReal_four_lt_top
    (oneStepOriginDirichletNormalizedGradient M n h p m)
  · exact (measurable_oneStepOriginDirichletGradientL2 M n h p m hh).norm.const_mul _
  · intro omega
    unfold oneStepOriginDirichletNormalizedGradient
    exact mul_nonneg
      (Real.rpow_nonneg
        (inv_nonneg.mpr (cubeVolume_nonneg (originCube d m))) _)
      (norm_nonneg _)
  · exact (lintegral_oneStepOriginDirichletNormalizedGradient_four_le
      M n h p m hh hp).trans_lt
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)

/-- The normalized Neumann fourth-power observable is integrable under the
GMC cutoff law. -/
theorem integrable_oneStepOriginNeumannNormalizedGradientFourth
    {d : ℕ} [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (p : Vec d) (m : ℤ) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    Integrable (oneStepOriginNeumannNormalizedGradientFourth M n h p m)
      M.P.toMeasure := by
  apply integrable_four_of_lintegral_ofReal_four_lt_top
    (oneStepOriginNeumannNormalizedGradient M n h p m)
  · exact (measurable_oneStepOriginNeumannGradientL2 M n h p m hh).norm.const_mul _
  · intro omega
    unfold oneStepOriginNeumannNormalizedGradient
    exact mul_nonneg
      (Real.rpow_nonneg
        (inv_nonneg.mpr (cubeVolume_nonneg (originCube d m))) _)
      (norm_nonneg _)
  · exact (lintegral_oneStepOriginNeumannNormalizedGradient_four_le
      M n h p m hh hp).trans_lt
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)

private theorem integral_four_le_toReal_of_lintegral_ofReal_four_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    (f : Omega → ℝ) (hf : Measurable f) (hf0 : ∀ omega, 0 ≤ f omega)
    {B : ℝ≥0∞}
    (hbound : ∫⁻ omega, (ENNReal.ofReal (f omega)) ^ (4 : ℝ) ∂mu ≤ B)
    (hB : B ≠ ∞) :
    ∫ omega, f omega ^ 4 ∂mu ≤ B.toReal := by
  have hmeas : AEStronglyMeasurable (fun omega ↦ f omega ^ 4) mu :=
    (hf.pow_const 4).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[mu] fun omega ↦ f omega ^ 4 :=
    Filter.Eventually.of_forall fun omega ↦ pow_nonneg (hf0 omega) 4
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]
  have htoReal := ENNReal.toReal_mono hB hbound
  convert htoReal using 1
  apply congrArg ENNReal.toReal
  apply lintegral_congr
  intro omega
  rw [ENNReal.ofReal_pow (hf0 omega)]
  exact (ENNReal.rpow_natCast _ 4).symm

/-- Real-valued normalized Dirichlet fourth-moment budget. -/
theorem integral_oneStepOriginDirichletNormalizedGradientFourth_le
    {d : ℕ} [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (p : Vec d) (m : ℤ) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    ∫ omega, oneStepOriginDirichletNormalizedGradientFourth
        M n h p m omega ∂M.P.toMeasure ≤
      ((ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^
        (4 : ℝ)).toReal := by
  apply integral_four_le_toReal_of_lintegral_ofReal_four_le
    (oneStepOriginDirichletNormalizedGradient M n h p m)
  · exact (measurable_oneStepOriginDirichletGradientL2 M n h p m hh).norm.const_mul _
  · intro omega
    unfold oneStepOriginDirichletNormalizedGradient
    exact mul_nonneg
      (Real.rpow_nonneg
        (inv_nonneg.mpr (cubeVolume_nonneg (originCube d m))) _)
      (norm_nonneg _)
  · exact lintegral_oneStepOriginDirichletNormalizedGradient_four_le
      M n h p m hh hp
  · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top

/-- Real-valued normalized Neumann fourth-moment budget. -/
theorem integral_oneStepOriginNeumannNormalizedGradientFourth_le
    {d : ℕ} [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (p : Vec d) (m : ℤ) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    ∫ omega, oneStepOriginNeumannNormalizedGradientFourth
        M n h p m omega ∂M.P.toMeasure ≤
      ((ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^
        (4 : ℝ)).toReal := by
  apply integral_four_le_toReal_of_lintegral_ofReal_four_le
    (oneStepOriginNeumannNormalizedGradient M n h p m)
  · exact (measurable_oneStepOriginNeumannGradientL2 M n h p m hh).norm.const_mul _
  · intro omega
    unfold oneStepOriginNeumannNormalizedGradient
    exact mul_nonneg
      (Real.rpow_nonneg
        (inv_nonneg.mpr (cubeVolume_nonneg (originCube d m))) _)
      (norm_nonneg _)
  · exact lintegral_oneStepOriginNeumannNormalizedGradient_four_le
      M n h p m hh hp
  · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top

/-- Quantitative fourth-moment budget for every finite normalized family of
translated Dirichlet parent cubes. -/
theorem normalized_finset_integral_oneStepTranslatedDirichletNormalizedGradientFourth_le
    {d : ℕ} [NeZero d] {iota : Type*} [DecidableEq iota]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (center : iota → Vec d) (s : Finset iota) (hs : s.Nonempty)
    (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, oneStepTranslatedDirichletNormalizedGradientFourth
          M n h p (center i) m omega hh ∂M.P.toMeasure ≤
      ((ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^
        (4 : ℝ)).toReal := by
  rw [normalized_finset_integral_oneStepTranslatedDirichletNormalizedGradientFourth_eq
    M n h p center s hs m hh]
  exact integral_oneStepOriginDirichletNormalizedGradientFourth_le
    M n h p m hh hp

/-- Quantitative fourth-moment budget for every finite normalized family of
translated Neumann parent cubes. -/
theorem normalized_finset_integral_oneStepTranslatedNeumannNormalizedGradientFourth_le
    {d : ℕ} [NeZero d] {iota : Type*} [DecidableEq iota]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (center : iota → Vec d) (s : Finset iota) (hs : s.Nonempty)
    (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, oneStepTranslatedNeumannNormalizedGradientFourth
          M n h p (center i) m omega hh ∂M.P.toMeasure ≤
      ((ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^
        (4 : ℝ)).toReal := by
  rw [normalized_finset_integral_oneStepTranslatedNeumannNormalizedGradientFourth_eq
    M n h p center s hs m hh]
  exact integral_oneStepOriginNeumannNormalizedGradientFourth_le
    M n h p m hh hp

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
