module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceWeightReplacement
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepWeightedPrincipalClosure
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteDirichletInfimum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.MeanOneFubini

@[expose] public section

/-!
# Parent-cube weighted-energy identities

This file identifies the literal exponentially weighted energy of the
canonical finite-volume shell corrector with the measurable principal-factor
carrier.  It is the exact weak-equation junction.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The literal cutoff multiplier is the centered-shell exponential minus
one. -/
theorem oneStepMultiplierAt_eq_exp_centeredShell_sub_one
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (x : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    oneStepMultiplierAt M n h x omega =
      Real.exp (oneStepCenteredShellAt M n h x omega) - 1 := by
  unfold oneStepMultiplierAt
  rw [cutoffRatioMinusOne_eq_exp_shell]
  · dsimp only [oneStepCenteredShellAt]
    congr 2
    push_cast
    ring
  · omega
  · exact_mod_cast Nat.lt_add_of_pos_right hh

private theorem integrableOn_centeredShellMultiplier_mul_vecNormSq
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (F : Vec d → Vec d)
    (hF : IntegrableOn (fun x ↦ vecNormSq (F x)) (openCubeSet Q) volume) :
    IntegrableOn (fun x ↦
      (Real.exp (oneStepCenteredShellAt M n h x omega) - 1) *
        vecNormSq (F x)) (openCubeSet Q) volume := by
  let B : Vec d → ℝ := fun x ↦
    Real.exp (oneStepCenteredShellAt M n h x omega) - 1
  let C : ℝ := oneStepUpperSourceCellWeight M n h Q omega + 1
  have hBmeas : Measurable B :=
    (measurable_oneStepCenteredShellAt_space M n h omega).exp.sub_const 1
  have hBbd : ∀ x ∈ openCubeSet Q, ‖B x‖ ≤ C := by
    intro x hx
    have hb0 : 0 ≤ Real.exp (oneStepCenteredShellAt M n h x omega) :=
      (Real.exp_pos _).le
    have hupper := exp_oneStepCenteredShellAt_le_upperSourceCellWeight
      M n h Q omega hh hx
    dsimp only [B, C]
    rw [Real.norm_eq_abs]
    calc
      |Real.exp (oneStepCenteredShellAt M n h x omega) - 1| ≤
          Real.exp (oneStepCenteredShellAt M n h x omega) + 1 := by
        exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hb0, abs_one])
      _ ≤ oneStepUpperSourceCellWeight M n h Q omega + 1 :=
        add_le_add hupper le_rfl
  exact integrableOn_mul_of_integrableOn_vecNormSq
    (measurableSet_openCubeSet Q) hBmeas hBbd hF

private theorem integrableOn_centeredShellMultiplier_mul_vecDot
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (p : Vec d) (F : Vec d → Vec d)
    (hF : MemVectorL2 (openCubeSet Q) F) :
    IntegrableOn (fun x ↦
      (Real.exp (oneStepCenteredShellAt M n h x omega) - 1) *
        vecDot p (F x)) (openCubeSet Q) volume := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let B : Vec d → ℝ := fun x ↦
    Real.exp (oneStepCenteredShellAt M n h x omega) - 1
  let C : ℝ := oneStepUpperSourceCellWeight M n h Q omega + 1
  have hbase : IntegrableOn (fun x ↦ vecDot p (F x))
      (openCubeSet Q) volume :=
    integrableOn_vecDot_of_memVectorL2 (memLp_const p) hF
  have hBmeas : Measurable B :=
    (measurable_oneStepCenteredShellAt_space M n h omega).exp.sub_const 1
  have hBbd : ∀ᵐ x ∂volume.restrict (openCubeSet Q), ‖B x‖ ≤ C := by
    rw [ae_restrict_iff' (measurableSet_openCubeSet Q)]
    filter_upwards with x hx
    have hb0 : 0 ≤ Real.exp (oneStepCenteredShellAt M n h x omega) :=
      (Real.exp_pos _).le
    have hupper := exp_oneStepCenteredShellAt_le_upperSourceCellWeight
      M n h Q omega hh hx
    dsimp only [B, C]
    rw [Real.norm_eq_abs]
    calc
      |Real.exp (oneStepCenteredShellAt M n h x omega) - 1| ≤
          Real.exp (oneStepCenteredShellAt M n h x omega) + 1 := by
        exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hb0, abs_one])
      _ ≤ oneStepUpperSourceCellWeight M n h Q omega + 1 :=
        add_le_add hupper le_rfl
  exact hbase.bdd_mul hBmeas.aestronglyMeasurable hBbd

/-- The literal finite-volume primal energy equals its mean-one base term,
minus the corrector energy, plus the weighted quadratic remainder. -/
theorem oneStepOriginDirichlet_weightedEnergy_identity
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    let Q := originCube d m
    let w := oneStepOriginDirichletSolution M n h p m omega hh
    ∫ x in openCubeSet Q,
        Real.exp (oneStepCenteredShellAt M n h x omega) *
          vecNormSq (p + w.toH1Function.grad x) ∂volume =
      (∫ x in openCubeSet Q,
        Real.exp (oneStepCenteredShellAt M n h x omega) *
          vecNormSq p ∂volume) -
        (∫ x in openCubeSet Q,
          vecNormSq (w.toH1Function.grad x) ∂volume) +
        oneStepQuadraticRemainderOn (openCubeSet Q)
          (fun x ↦ Real.exp (oneStepCenteredShellAt M n h x omega))
          w.toH1Function.grad := by
  let Q := originCube d m
  let w := oneStepOriginDirichletSolution M n h p m omega hh
  let b : Vec d → ℝ := fun x ↦
    Real.exp (oneStepCenteredShellAt M n h x omega)
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hpSq : IntegrableOn (fun _ : Vec d ↦ vecNormSq p)
      (openCubeSet Q) volume :=
    integrableOn_vecNormSq_of_memLp fun i ↦ memLp_const (p i)
  have hb0 : IntegrableOn (fun x ↦ b x * vecNormSq p)
      (openCubeSet Q) volume := by
    have hweight : IntegrableOn (fun x ↦
        (b x - 1) * vecNormSq p)
        (openCubeSet Q) volume := by
      simpa only [b] using
        integrableOn_centeredShellMultiplier_mul_vecNormSq
          M n h Q omega hh (fun _ ↦ p) hpSq
    have heq : (fun x ↦ b x * vecNormSq p) =
        fun x ↦ vecNormSq p + (b x - 1) * vecNormSq p := by
      funext x
      ring
    rw [heq]
    exact hpSq.add hweight
  have hcross :=
    integrableOn_centeredShellMultiplier_mul_vecDot
      M n h Q omega hh p w.toH1Function.grad
        w.toH1Function.grad_memVectorL2
  have hquad :=
    integrableOn_centeredShellMultiplier_mul_vecNormSq
      M n h Q omega hh w.toH1Function.grad
        (integrableOn_vecNormSq_zeroTraceGrad w)
  have hweak0 := oneStepOriginDirichletSolution_isWeakSolution
    M n h p m omega hh
  have hforce : (fun x ↦ -oneStepMultiplierAt M n h x omega • p) =
      fun x ↦ -((b x - 1) • p) := by
    funext x
    unfold oneStepMultiplierAt
    rw [cutoffRatioMinusOne_eq_exp_shell]
    · dsimp only [b, oneStepCenteredShellAt]
      have hexponent :
          cutoffShellSum (n + h) (n : ℤ) x omega -
              ((((n + h : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) *
                _root_.SubdiffusiveProcess.Model.tauSq M.P =
            cutoffShellSum (n + h) (n : ℤ) x omega -
              (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P := by
        push_cast
        ring
      rw [hexponent]
      ext i
      simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring
    · omega
    · exact_mod_cast Nat.lt_add_of_pos_right hh
  have hweak : IsZeroTraceDirichletRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q) w
      (fun x ↦ -((b x - 1) • p)) := by
    rw [← hforce]
    simpa only [Q, w] using hweak0
  simpa only [Q, w, b] using
    oneStep_weightedDirichletEnergy_identity p hb0 hcross hquad hweak

/-- The Borel cubic is the normalized literal quadratic remainder for a unit
probe. -/
theorem oneStepOriginDirichletWeightedCubicBorel_eq_cubeAverage
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    oneStepOriginDirichletWeightedCubicBorel M n h p m omega =
      cubeAverage (originCube d m) (fun x ↦
        (Real.exp (oneStepCenteredShellAt M n h x omega) - 1) *
          vecNormSq
            ((oneStepOriginDirichletSolution M n h p m omega hh).toH1Function
              |>.grad x)) := by
  let Q := originCube d m
  let w := oneStepOriginDirichletSolution M n h p m omega hh
  let u := oneStepOriginDirichletGradientL2 M n h p m omega
  let z := oneStepShellForcingL2 M n h p Q omega
  obtain ⟨_C, _hC, hCZ⟩ := exists_oneStepOriginDirichlet_gradient_four_cz d
  have huRaw := (hCZ M n h omega p m hh hp).1
  have hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hmem := memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure
      Q w.toH1Function huRaw
    rw [oneStepOriginDirichletSolution_gradient_eq M n h p m omega hh] at hmem
    exact hmem
  have hz4 : MemLp (z : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    exact memLp_four_oneStepContinuousScalarForcingL2 Q p
      (oneStepMultiplierContinuousMap M n h omega)
  have huCoe : (u : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      fun x ↦ HilbertVec.ofVec (w.toH1Function.grad x) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    have hcoe := w.toH1Function.coeFn_gradToHilbertVectorL2
    rw [oneStepOriginDirichletSolution_gradient_eq
      M n h p m omega hh] at hcoe
    simpa only [u, w, Q, hilbertifyVecField] using! hcoe
  have hzCoe : (z : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      fun x ↦ oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    have hcoe := coeFn_toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepMultiplierContinuousMap M n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p)))
    filter_upwards [hcoe] with x hx
    rw [show z = oneStepContinuousScalarForcingL2 Q p
      (oneStepMultiplierContinuousMap M n h omega) by rfl]
    rw [show (oneStepContinuousScalarForcingL2 Q p
      (oneStepMultiplierContinuousMap M n h omega) :
        Vec d → HilbertVec d) x =
      HilbertVec.ofVec (oneStepMultiplierContinuousMap M n h omega x • p) by
        exact hx]
    rw [oneStepMultiplierContinuousMap_apply M n h omega x hh]
    rfl
  rw [oneStepOriginDirichletWeightedCubicBorel,
    oneStepNormalizedWeightedCubicBorel_eq_cubeAverage Q
      (HilbertVec.ofVec p) u z hu4 hz4]
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  apply integral_congr_ae
  filter_upwards [huCoe, hzCoe] with x hux hzx
  unfold oneStepWeightedCubicIntegrand
  rw [hux, hzx, HilbertVec.norm_sq_ofVec,
    inner_smul_right, HilbertVec.inner_def,
    oneStepMultiplierAt_eq_exp_centeredShell_sub_one M n h x omega hh]
  rw [show vecDot p p = vecNormSq p by rfl, hp]
  dsimp only [w]
  simp only [vecNormSq]
  ring

/-- The finite corrector energy can be read from the canonical origin
solution rather than the translation-covariant triadic realization. -/
theorem oneStepDirichletCorrectorEnergy_eq_origin_setIntegral
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    oneStepDirichletCorrectorEnergy M n h p (originCube d m) omega hh =
      (cubeVolume (originCube d m))⁻¹ *
        ∫ x in openCubeSet (originCube d m),
          vecNormSq
            ((oneStepOriginDirichletSolution M n h p m omega hh).toH1Function
              |>.grad x) ∂volume := by
  let w := oneStepOriginDirichletSolution M n h p m omega hh
  rw [oneStepDirichletCorrectorEnergy_eq_originGradient
    M n h p m omega hh,
    ← oneStepOriginDirichletSolution_gradient_eq M n h p m omega hh]
  congr 1
  rw [← real_inner_self_eq_norm_sq]
  simpa only [w, H1Function.gradToHilbertVectorL2, vecNormSq] using
    inner_toHilbertVectorL2OfVecField_eq_integral
      w.toH1Function.grad_memVectorL2 w.toH1Function.grad_memVectorL2

/-- Samplewise normalized primal parent energy in the exact measurable
principal-factor decomposition. -/
theorem oneStepOriginDirichlet_weightedCubeAverage_identity
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    cubeAverage (originCube d m) (fun x ↦
        Real.exp (oneStepCenteredShellAt M n h x omega) *
          vecNormSq
            (p + ((oneStepOriginDirichletSolution M n h p m omega hh)
              |>.toH1Function.grad x))) =
      cubeAverage (originCube d m) (fun x ↦
        Real.exp (oneStepCenteredShellAt M n h x omega)) -
        oneStepDirichletCorrectorEnergy M n h p
          (originCube d m) omega hh +
        oneStepOriginDirichletWeightedCubicBorel M n h p m omega := by
  let Q := originCube d m
  let w := oneStepOriginDirichletSolution M n h p m omega hh
  have hraw := oneStepOriginDirichlet_weightedEnergy_identity
    M n h p m omega hh
  have hscaled := congrArg (fun r : ℝ ↦ (cubeVolume Q)⁻¹ * r) hraw
  rw [oneStepDirichletCorrectorEnergy_eq_origin_setIntegral
      M n h p m omega hh,
    oneStepOriginDirichletWeightedCubicBorel_eq_cubeAverage
      M n h p m omega hh hp,
    cubeAverage, cubeAverage, cubeAverage,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet] at ⊢
  dsimp only [Q, w] at hscaled ⊢
  have hbase :
      ∫ x in openCubeSet (originCube d m),
          Real.exp (oneStepCenteredShellAt M n h x omega) * vecNormSq p
          ∂volume =
        ∫ x in openCubeSet (originCube d m),
          Real.exp (oneStepCenteredShellAt M n h x omega) ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hp, mul_one]
  rw [hbase] at hscaled
  unfold oneStepQuadraticRemainderOn at hscaled
  calc
    _ = (cubeVolume (originCube d m))⁻¹ *
        (((∫ x in openCubeSet (originCube d m),
            Real.exp (oneStepCenteredShellAt M n h x omega) ∂volume) -
          ∫ x in openCubeSet (originCube d m),
            vecNormSq ((oneStepOriginDirichletSolution
              M n h p m omega hh).toH1Function.grad x) ∂volume) +
          ∫ x in openCubeSet (originCube d m),
            (Real.exp (oneStepCenteredShellAt M n h x omega) - 1) *
              vecNormSq ((oneStepOriginDirichletSolution
                M n h p m omega hh).toH1Function.grad x) ∂volume) := hscaled
    _ = _ := by ring

/-- The normalized spatial average of the centered shell exponential has
expectation one. -/
theorem integral_cubeAverage_exp_oneStepCenteredShellAt_eq_one
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (Q : TriadicCube d) (hh : 0 < h) :
    (∫ omega, cubeAverage Q (fun x ↦
        Real.exp (oneStepCenteredShellAt M n h x omega)) ∂M.P.toMeasure) = 1 ∧
      Integrable (fun omega ↦ cubeAverage Q (fun x ↦
        Real.exp (oneStepCenteredShellAt M n h x omega))) M.P.toMeasure := by
  let B : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → ℝ := fun omega x ↦
    Real.exp (oneStepCenteredShellAt M n h x omega)
  have hjoint : Measurable fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d ↦ B z.1 z.2 := by
    unfold B oneStepCenteredShellAt
    exact ((measurable_cutoffShellSum_uncurry n h).sub_const _).exp
  have hB0 : ∀ omega x, 0 ≤ B omega x := fun _ _ ↦ (Real.exp_pos _).le
  have hcont : ∀ omega, Continuous (B omega) := by
    intro omega
    unfold B oneStepCenteredShellAt cutoffShellSum
    exact Real.continuous_exp.comp
      ((continuous_finsetSum _ fun k _ ↦ (omega k).1.1.continuous).sub
        continuous_const)
  have hmean : ∀ x, ∫ omega, B omega x ∂M.P.toMeasure = 1 := by
    intro x
    have hraw := integral_cutoffRatio M (n + h) (n : ℤ) x (by omega)
      (by exact_mod_cast Nat.lt_add_of_pos_right hh)
    calc
      ∫ omega, B omega x ∂M.P.toMeasure =
          ∫ omega, cutoffRatioMinusOne M (n + h) (n : ℤ) omega x + 1
            ∂M.P.toMeasure := by
        apply integral_congr_ae
        filter_upwards with omega
        unfold B
        calc
          Real.exp (oneStepCenteredShellAt M n h x omega) =
              (Real.exp (oneStepCenteredShellAt M n h x omega) - 1) + 1 := by
            ring
          _ = oneStepMultiplierAt M n h x omega + 1 := by
            rw [oneStepMultiplierAt_eq_exp_centeredShell_sub_one
              M n h x omega hh]
          _ = cutoffRatioMinusOne M (n + h) (n : ℤ) omega x + 1 := by
            rfl
      _ = 1 := hraw
  have hset := integral_setIntegral_of_mean_one hjoint hB0 hcont hmean
    (measurableSet_cubeSet Q) (isBounded_cubeSet Q)
  have hvolume : (volume (cubeSet Q)).toReal = cubeVolume Q := by
    rw [volume_cubeSet_toReal]
  constructor
  · unfold cubeAverage
    rw [integral_const_mul, hset.1, hvolume]
    exact inv_mul_cancel₀ (cubeVolume_pos Q).ne'
  · unfold cubeAverage
    exact hset.2.const_mul _

/-- Pointwise representative of the measurable shell-forcing class. -/
theorem oneStepShellForcingL2_coeFn_eq_multiplier
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hh : 0 < h) :
    (oneStepShellForcingL2 M n h p Q omega : Vec d → HilbertVec d) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      fun x ↦ oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p := by
  have hcoe := coeFn_toHilbertVectorL2OfVecField
    (memVectorL2_openCubeSet_of_continuous Q
      ((oneStepMultiplierContinuousMap M n h omega).continuous.smul
        (continuous_const : Continuous fun _ : Vec d ↦ p)))
  filter_upwards [hcoe] with x hx
  rw [show (oneStepShellForcingL2 M n h p Q omega :
      Vec d → HilbertVec d) x =
      (toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepMultiplierContinuousMap M n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p))) :
          Vec d → HilbertVec d) x by rfl, hx]
  change HilbertVec.ofVec
      ((oneStepMultiplierContinuousMap M n h omega) x • p) = _
  rw [oneStepMultiplierContinuousMap_apply M n h omega x hh]
  rfl

/-- Fubini integrability for a fixed weak probe of the finite-volume shell
forcing. -/
private theorem integrable_oneStepShellForcing_inner_prod
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (hh : 0 < h)
    (Y : HilbertVectorL2 (openCubeSet Q)) :
    Integrable (fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d ↦
      inner ℝ
        (oneStepMultiplierAt M n h z.2 z.1 • HilbertVec.ofVec p)
        ((Y : Vec d → HilbertVec d) z.2))
      (M.P.toMeasure.prod (volumeMeasureOn (openCubeSet Q))) := by
  let F : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVectorL2 (openCubeSet Q) :=
    oneStepShellForcingL2 M n h p Q
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d → ℝ := fun z ↦
    inner ℝ
      (oneStepMultiplierAt M n h z.2 z.1 • HilbertVec.ofVec p)
      ((Y : Vec d → HilbertVec d) z.2)
  have hYmeas : Measurable fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d ↦
      (Y : Vec d → HilbertVec d) z.2 :=
    (Lp.stronglyMeasurable Y).measurable.comp measurable_snd
  have hfmeas : Measurable f := by
    exact ((measurable_oneStepMultiplierAt_uncurry M n h).smul_const
      (HilbertVec.ofVec p)).inner hYmeas
  have hFmem : MemLp F 2 M.P.toMeasure := by
    simpa only [F] using memLp_two_oneStepShellForcingL2 M n h p Q hh
  apply (integrable_prod_iff hfmeas.aestronglyMeasurable).2
  constructor
  · filter_upwards with omega
    have hrep := oneStepShellForcingL2_coeFn_eq_multiplier
      M n h p Q omega hh
    have hliteral : MemLp
        (fun x ↦ oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p)
        2 (volumeMeasureOn (openCubeSet Q)) :=
      (Lp.memLp (F omega)).ae_eq hrep
    have hprod := hliteral.norm.integrable_mul (Lp.memLp Y).norm
    apply hprod.mono' (hfmeas.comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    filter_upwards with x
    change |inner ℝ
      (oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p)
      ((Y : Vec d → HilbertVec d) x)| ≤
        ‖oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p‖ *
          ‖(Y : Vec d → HilbertVec d) x‖
    exact abs_real_inner_le_norm _ _
  · let major : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
      (1 / 2 : ℝ) * (‖F omega‖ ^ 2 + ‖Y‖ ^ 2)
    have hmajor : Integrable major M.P.toMeasure := by
      have hFsq : Integrable (fun omega ↦ ‖F omega‖ ^ 2) M.P.toMeasure :=
        hFmem.norm.integrable_sq
      exact (hFsq.add (integrable_const (‖Y‖ ^ 2))).const_mul (1 / 2)
    have hgmeas : AEStronglyMeasurable (fun omega ↦
        ∫ x, ‖f (omega, x)‖ ∂volumeMeasureOn (openCubeSet Q))
        M.P.toMeasure :=
      hfmeas.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    apply hmajor.mono' hgmeas
    filter_upwards with omega
    have hrep := oneStepShellForcingL2_coeFn_eq_multiplier
      M n h p Q omega hh
    have hliteral : MemLp
        (fun x ↦ oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p)
        2 (volumeMeasureOn (openCubeSet Q)) :=
      (Lp.memLp (F omega)).ae_eq hrep
    have hYsq : Integrable
        (fun x ↦ ‖(Y : Vec d → HilbertVec d) x‖ ^ 2)
        (volumeMeasureOn (openCubeSet Q)) := (Lp.memLp Y).norm.integrable_sq
    have hXsq : Integrable
        (fun x ↦ ‖oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p‖ ^ 2)
        (volumeMeasureOn (openCubeSet Q)) := hliteral.norm.integrable_sq
    have hpoint : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
        ‖f (omega, x)‖ ≤ (1 / 2 : ℝ) *
          (‖oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p‖ ^ 2 +
            ‖(Y : Vec d → HilbertVec d) x‖ ^ 2) := by
      filter_upwards with x
      rw [Real.norm_eq_abs]
      have hcs := abs_real_inner_le_norm
        (oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p)
        ((Y : Vec d → HilbertVec d) x)
      nlinarith [sq_nonneg
        (‖oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p‖ -
          ‖(Y : Vec d → HilbertVec d) x‖)]
    have hright : Integrable (fun x ↦ (1 / 2 : ℝ) *
        (‖oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p‖ ^ 2 +
          ‖(Y : Vec d → HilbertVec d) x‖ ^ 2))
        (volumeMeasureOn (openCubeSet Q)) :=
      (hXsq.add hYsq).const_mul (1 / 2)
    have habsInt : Integrable (fun x ↦ ‖f (omega, x)‖)
        (volumeMeasureOn (openCubeSet Q)) := by
      apply (hliteral.norm.integrable_mul (Lp.memLp Y).norm).mono'
        (hfmeas.comp (measurable_const.prodMk measurable_id)).norm.aestronglyMeasurable
      filter_upwards with x
      simpa only [Function.comp_apply, id_eq, f, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), abs_abs, Pi.mul_apply] using
        (abs_real_inner_le_norm
          (oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p)
          ((Y : Vec d → HilbertVec d) x))
    have hle := integral_mono_ae habsInt hright hpoint
    have hXnorm :
        ∫ x, ‖oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p‖ ^ 2
            ∂volumeMeasureOn (openCubeSet Q) = ‖F omega‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hrep] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
    have hYnorm :
        ∫ x, ‖(Y : Vec d → HilbertVec d) x‖ ^ 2
            ∂volumeMeasureOn (openCubeSet Q) = ‖Y‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards with x
      rw [real_inner_self_eq_norm_sq]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    simpa only [f, major, integral_const_mul,
      integral_add hXsq hYsq, hXnorm, hYnorm] using hle

/-- The finite-volume shell forcing has zero Bochner expectation.  This is
the precise linearity/Fubini form of the manuscript's `E W = 0` sentence. -/
theorem integral_oneStepShellForcingL2_eq_zero
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (hh : 0 < h) :
    ∫ omega, oneStepShellForcingL2 M n h p Q omega ∂M.P.toMeasure = 0 := by
  let F : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVectorL2 (openCubeSet Q) :=
    oneStepShellForcingL2 M n h p Q
  have hFmem : MemLp F 2 M.P.toMeasure := by
    simpa only [F] using memLp_two_oneStepShellForcingL2 M n h p Q hh
  have hFint : Integrable F M.P.toMeasure := hFmem.integrable (by norm_num)
  apply ext_inner_left ℝ
  intro Y
  have hzero : inner ℝ Y (0 : HilbertVectorL2 (openCubeSet Q)) = 0 := by simp
  rw [hzero]
  rw [← integral_inner hFint Y]
  have hprod := integrable_oneStepShellForcing_inner_prod M n h p Q hh Y
  have hprod' : Integrable (Function.uncurry fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      fun x : Vec d ↦ inner ℝ
        (oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p)
        ((Y : Vec d → HilbertVec d) x))
      (M.P.toMeasure.prod (volumeMeasureOn (openCubeSet Q))) := by
    simpa only [Function.uncurry] using! hprod
  have hfub := integral_integral_swap hprod'
  have hleft :
      ∫ omega, inner ℝ Y (F omega) ∂M.P.toMeasure =
        ∫ omega, ∫ x,
          inner ℝ
            (oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p)
            ((Y : Vec d → HilbertVec d) x)
          ∂volumeMeasureOn (openCubeSet Q) ∂M.P.toMeasure := by
    apply integral_congr_ae
    filter_upwards with omega
    rw [real_inner_comm, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [oneStepShellForcingL2_coeFn_eq_multiplier
      M n h p Q omega hh] with x hx
    rw [hx]
  rw [hleft, hfub]
  have hinner : ∀ x : Vec d,
      ∫ omega,
          inner ℝ
            (oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p)
            ((Y : Vec d → HilbertVec d) x) ∂M.P.toMeasure = 0 := by
    intro x
    calc
      _ = ∫ omega, oneStepMultiplierAt M n h x omega *
          inner ℝ (HilbertVec.ofVec p)
            ((Y : Vec d → HilbertVec d) x) ∂M.P.toMeasure := by
        apply integral_congr_ae
        filter_upwards with omega
        rw [inner_smul_left]
        rfl
      _ = (∫ omega, oneStepMultiplierAt M n h x omega ∂M.P.toMeasure) *
          inner ℝ (HilbertVec.ofVec p)
            ((Y : Vec d → HilbertVec d) x) := by
        rw [integral_mul_const]
      _ = 0 := by rw [integral_oneStepMultiplierAt_eq_zero M n h x hh, zero_mul]
  simp only [hinner, integral_zero]

/-- The fixed-coefficient Neumann gradient solution operator as an explicit
continuous linear map. -/
def oneStepNeumannGradientOfForcingCLM
    {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField d} {lam Lam : ℝ}
    (hC : H1CoerciveEstimate U) (hne : Set.Nonempty U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    HilbertVectorL2 U →L[ℝ] HilbertVectorL2 U :=
  ContinuousLinearMap.mk
    ({ toFun := oneStepNeumannGradientOfForcingClass hC hne hEll
       map_add' := by
        intro G H
        unfold oneStepNeumannGradientOfForcingClass oneStepNeumannForcingRieszOfClass
        rw [map_add, ContinuousLinearMap.add_comp]
        unfold H1CoerciveHilbert.forcingRieszMap
        simp only [map_add, ← H1CoerciveHilbert.gradientCLM_apply]
       map_smul' := by
        intro c G
        unfold oneStepNeumannGradientOfForcingClass oneStepNeumannForcingRieszOfClass
        rw [map_smul, ContinuousLinearMap.smul_comp]
        unfold H1CoerciveHilbert.forcingRieszMap
        simp only [map_smul, RingHom.id_apply, ← H1CoerciveHilbert.gradientCLM_apply] } :
      HilbertVectorL2 U →ₗ[ℝ] HilbertVectorL2 U)
    (continuous_oneStepNeumannGradientOfForcingClass hC hne hEll)

theorem oneStepNeumannGradientOfForcingCLM_apply
    {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField d} {lam Lam : ℝ}
    (hC : H1CoerciveEstimate U) (hne : Set.Nonempty U)
    (hEll : IsEllipticFieldOn lam Lam U a) (G : HilbertVectorL2 U) :
    oneStepNeumannGradientOfForcingCLM hC hne hEll G =
      oneStepNeumannGradientOfForcingClass hC hne hEll G := rfl

/-- The canonical finite-volume Neumann gradient has zero Bochner
expectation. -/
theorem integral_oneStepOriginNeumannGradientL2_eq_zero
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    ∫ omega, oneStepOriginNeumannGradientL2 M n h p m omega
        ∂M.P.toMeasure = 0 := by
  let Q := originCube d m
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q)
      (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  let D : HilbertVectorL2 (openCubeSet Q) →L[ℝ]
      HilbertVectorL2 (openCubeSet Q) :=
    oneStepNeumannGradientOfForcingCLM
      (translatedCubeMeanZeroH1CoerciveEstimate Q)
      (openCubeSet_nonempty_internal Q) hEll
  let F : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVectorL2 (openCubeSet Q) :=
    oneStepShellForcingL2 M n h p Q
  have hFmem : MemLp F 2 M.P.toMeasure := by
    simpa only [F] using memLp_two_oneStepShellForcingL2 M n h p Q hh
  have hFint : Integrable F M.P.toMeasure := hFmem.integrable (by norm_num)
  have hFzero : ∫ omega, F omega ∂M.P.toMeasure = 0 := by
    simpa only [F] using integral_oneStepShellForcingL2_eq_zero M n h p Q hh
  have hcomm := D.integral_comp_comm hFint.neg
  have hcomm' : ∫ omega, D (-F omega) ∂M.P.toMeasure =
      D (∫ omega, -F omega ∂M.P.toMeasure) := by
    simpa only [Pi.neg_apply] using hcomm
  have hnegInt : ∫ omega, -F omega ∂M.P.toMeasure =
      -(∫ omega, F omega ∂M.P.toMeasure) := by
    simpa only [Pi.neg_apply] using integral_neg F
  change ∫ omega, D (-F omega) ∂M.P.toMeasure = 0
  rw [hcomm', hnegInt, hFzero, neg_zero, map_zero]

/-- The spatial constant-gradient cross term has zero expectation. -/
theorem integral_cubeAverage_vecDot_oneStepOriginNeumannGradient_eq_zero
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    ∫ omega, cubeAverage (originCube d m) (fun x ↦
        vecDot p ((oneStepOriginNeumannSolution M n h p m omega hh)
          |>.toH1Function.grad x)) ∂M.P.toMeasure = 0 := by
  let Q := originCube d m
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q)
      (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  let D : HilbertVectorL2 (openCubeSet Q) →L[ℝ]
      HilbertVectorL2 (openCubeSet Q) :=
    oneStepNeumannGradientOfForcingCLM
      (translatedCubeMeanZeroH1CoerciveEstimate Q)
      (openCubeSet_nonempty_internal Q) hEll
  let G : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVectorL2 (openCubeSet Q) :=
    oneStepOriginNeumannGradientL2 M n h p m
  let e : HilbertVectorL2 (openCubeSet Q) := oneStepConstantVectorL2 Q p
  let L : HilbertVectorL2 (openCubeSet Q) →L[ℝ] ℝ := innerSL ℝ e
  have hFmem := memLp_two_oneStepShellForcingL2 M n h p Q hh
  have hGaestrong : AEStronglyMeasurable G M.P.toMeasure := by
    change AEStronglyMeasurable (fun omega =>
      D (-(oneStepShellForcingL2 M n h p Q omega))) M.P.toMeasure
    exact D.continuous.comp_aestronglyMeasurable hFmem.aestronglyMeasurable.neg
  have hGmem : MemLp G 2 M.P.toMeasure := by
    apply hFmem.norm.mono' hGaestrong
    filter_upwards with omega
    exact norm_oneStepOriginNeumannGradientL2_le_forcing
      M n h p m omega hh
  have hGint : Integrable G M.P.toMeasure := hGmem.integrable (by norm_num)
  have hGzero : ∫ omega, G omega ∂M.P.toMeasure = 0 := by
    simpa only [G, Q] using
      integral_oneStepOriginNeumannGradientL2_eq_zero M n h p m hh
  have hinnerZero : ∫ omega, L (G omega) ∂M.P.toMeasure = 0 := by
    rw [L.integral_comp_comm hGint, hGzero, map_zero]
  have hpoint : ∀ omega,
      cubeAverage Q (fun x ↦
        vecDot p ((oneStepOriginNeumannSolution M n h p m omega hh)
          |>.toH1Function.grad x)) =
        (cubeVolume Q)⁻¹ * L (G omega) := by
    intro omega
    have heCoe := coeFn_toHilbertVectorL2OfVecField
      (memVectorL2_const (U := openCubeSet Q) p)
    have hGCoe := (oneStepOriginNeumannSolution M n h p m omega hh)
      |>.toH1Function.coeFn_gradToHilbertVectorL2
    have hGeq : G omega =
        H1Function.gradToHilbertVectorL2
          (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function := by
      dsimp only [G]
      rw [← oneStepOriginNeumannSolution_gradient_eq M n h p m omega hh]
      rfl
    have hinner : L (G omega) =
        ∫ x in openCubeSet Q,
          vecDot p ((oneStepOriginNeumannSolution M n h p m omega hh)
            |>.toH1Function.grad x) ∂volume := by
      dsimp only [L]
      rw [innerSL_apply_apply, L2.inner_def, hGeq]
      apply integral_congr_ae
      filter_upwards [heCoe, hGCoe] with x hex hgx
      rw [show (e : Vec d → HilbertVec d) x = HilbertVec.ofVec p by
        simpa only [e, oneStepConstantVectorL2, hilbertifyVecField] using! hex,
        show (H1Function.gradToHilbertVectorL2
              (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function :
                Vec d → HilbertVec d) x =
            HilbertVec.ofVec
              ((oneStepOriginNeumannSolution M n h p m omega hh)
                |>.toH1Function.grad x) by
          simpa only [G, Q, H1MeanZeroFunction.gradToHilbertVectorL2, hilbertifyVecField] using! hgx,
        HilbertVec.inner_def]
    unfold cubeAverage
    rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet, hinner]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_const_mul, hinnerZero, mul_zero]

/-- Expectation of the literal primal parent energy is exactly expectation
of the measurable principal-factor carrier. -/
theorem integral_oneStepOriginDirichlet_weightedCubeAverage_eq_principalFactor
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ∫ omega, cubeAverage (originCube d m) (fun x ↦
        Real.exp (oneStepCenteredShellAt M n h x omega) *
          vecNormSq
            (p + ((oneStepOriginDirichletSolution M n h p m omega hh)
              |>.toH1Function.grad x))) ∂M.P.toMeasure =
      ∫ omega, oneStepDirichletWeightedPrincipalFactor
        M n h p m omega hh ∂M.P.toMeasure := by
  let base : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
    cubeAverage (originCube d m) (fun x ↦
      Real.exp (oneStepCenteredShellAt M n h x omega))
  let energy : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
    oneStepDirichletCorrectorEnergy M n h p
      (originCube d m) omega hh
  let cubic : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
    oneStepOriginDirichletWeightedCubicBorel M n h p m
  let full : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
    cubeAverage (originCube d m) (fun x ↦
      Real.exp (oneStepCenteredShellAt M n h x omega) *
        vecNormSq (p + ((oneStepOriginDirichletSolution
          M n h p m omega hh).toH1Function.grad x)))
  have hbase := integral_cubeAverage_exp_oneStepCenteredShellAt_eq_one
    M n h (originCube d m) hh
  have henergy : Integrable energy M.P.toMeasure := by
    exact integrable_oneStepDirichletCorrectorEnergy
      M n h p (originCube d m) hh hp
  obtain ⟨_C, _hC, hcubic⟩ :=
    exists_integral_oneStepOriginDirichletWeightedCubicBorel_le d
  have hcubicInt : Integrable cubic M.P.toMeasure :=
    (hcubic M n h p m hh hp hscale).1
  have hpoint : full = fun omega ↦ base omega - energy omega + cubic omega := by
    funext omega
    exact oneStepOriginDirichlet_weightedCubeAverage_identity
      M n h p m omega hh hp
  have hrhsInt : Integrable (fun omega ↦
      base omega - energy omega + cubic omega) M.P.toMeasure :=
    (hbase.2.sub henergy).add hcubicInt
  have hfullInt : Integrable full M.P.toMeasure := by
    exact hrhsInt.congr (Filter.Eventually.of_forall fun omega ↦
      (congrFun hpoint omega).symm)
  change ∫ omega, full omega ∂M.P.toMeasure = _
  rw [integral_congr_ae (Filter.Eventually.of_forall fun omega ↦
      congrFun hpoint omega)]
  have hsplitL :
      ∫ omega, base omega - energy omega + cubic omega ∂M.P.toMeasure =
        (∫ omega, base omega - energy omega ∂M.P.toMeasure) +
          ∫ omega, cubic omega ∂M.P.toMeasure := by
    exact integral_add (hbase.2.sub henergy) hcubicInt
  have hsubL :
      ∫ omega, base omega - energy omega ∂M.P.toMeasure =
        (∫ omega, base omega ∂M.P.toMeasure) -
          ∫ omega, energy omega ∂M.P.toMeasure :=
    integral_sub hbase.2 henergy
  have hbaseEq : ∫ omega, base omega ∂M.P.toMeasure = 1 := by
    simpa only [base] using hbase.1
  rw [hsplitL, hsubL, hbaseEq]
  unfold oneStepDirichletWeightedPrincipalFactor
  have hsplitR := integral_add ((integrable_const 1).sub henergy) hcubicInt
  have hsubR := integral_sub (integrable_const 1) henergy
  change 1 - ∫ omega, energy omega ∂M.P.toMeasure +
      ∫ omega, cubic omega ∂M.P.toMeasure =
    ∫ omega, 1 - energy omega + cubic omega ∂M.P.toMeasure
  calc
    _ = ((∫ _omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, (1 : ℝ) ∂M.P.toMeasure) -
          ∫ omega, energy omega ∂M.P.toMeasure) +
        ∫ omega, cubic omega ∂M.P.toMeasure := by
      rw [integral_const]
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    _ = (∫ omega, 1 - energy omega ∂M.P.toMeasure) +
        ∫ omega, cubic omega ∂M.P.toMeasure := by rw [hsubR]
    _ = _ := by
      simpa only [Pi.sub_apply] using hsplitR.symm

/-- On an origin parent cube, the translation-covariant triadic solution and
the canonical origin solution give the same weighted slope energy. -/
theorem cubeAverage_oneStepDirichletSlopeField_origin_eq_originSolution
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    cubeAverage (originCube d m) (fun x ↦
        Real.exp (oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepDirichletSlopeField M n h p
            (originCube d m) omega hh x)) =
      cubeAverage (originCube d m) (fun x ↦
        Real.exp (oneStepCenteredShellAt M n h x omega) *
          vecNormSq
            (p + ((oneStepOriginDirichletSolution M n h p m omega hh)
              |>.toH1Function.grad x))) := by
  let Q := originCube d m
  let u := oneStepOriginDirichletGradientL2 M n h p m omega
  let v := H1Function.gradToHilbertVectorL2
    (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
  have huv : u = v :=
    oneStepOriginDirichletGradientL2_eq_triadic M n h p m omega hh
  have huCoe : (u : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      fun x ↦ HilbertVec.ofVec
        ((oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad x) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    have hcoe := (oneStepOriginDirichletSolution M n h p m omega hh)
      |>.toH1Function.coeFn_gradToHilbertVectorL2
    rw [oneStepOriginDirichletSolution_gradient_eq
      M n h p m omega hh] at hcoe
    simpa only [u, Q, hilbertifyVecField] using! hcoe
  have hvCoe : (v : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      fun x ↦ HilbertVec.ofVec
        ((oneStepTriadicDirichletSolution M n h p Q omega hh)
          |>.toH1Function.grad x) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    simpa only [v, H1Function.gradToHilbertVectorL2, hilbertifyVecField] using!
      (oneStepTriadicDirichletSolution M n h p Q omega hh)
        |>.toH1Function.coeFn_gradToHilbertVectorL2
  have hgrad : (fun x ↦
      (oneStepTriadicDirichletSolution M n h p Q omega hh)
        |>.toH1Function.grad x) =ᵐ[normalizedCubeMeasure Q]
      fun x ↦ (oneStepOriginDirichletSolution M n h p m omega hh)
        |>.toH1Function.grad x := by
    rw [huv] at huCoe
    filter_upwards [hvCoe, huCoe] with x hvx hux
    have h := congrArg HilbertVec.toVec (hvx.symm.trans hux)
    simpa only [HilbertVec.toVec_ofVec] using h
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  apply integral_congr_ae
  filter_upwards [hgrad] with x hx
  unfold oneStepDirichletSlopeField
  rw [hx]

/-- The literal parent weighted-slope expectation is the already-controlled
principal factor. -/
theorem integral_oneStepDirichletSlopeField_weightedCubeAverage_eq_principalFactor
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ∫ omega, cubeAverage (originCube d m) (fun x ↦
        Real.exp (oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepDirichletSlopeField M n h p
            (originCube d m) omega hh x)) ∂M.P.toMeasure =
      ∫ omega, oneStepDirichletWeightedPrincipalFactor
        M n h p m omega hh ∂M.P.toMeasure := by
  calc
    _ = ∫ omega, cubeAverage (originCube d m) (fun x ↦
        Real.exp (oneStepCenteredShellAt M n h x omega) *
          vecNormSq
            (p + ((oneStepOriginDirichletSolution M n h p m omega hh)
              |>.toH1Function.grad x))) ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      exact cubeAverage_oneStepDirichletSlopeField_origin_eq_originSolution
        M n h p m omega hh
    _ = _ :=
      integral_oneStepOriginDirichlet_weightedCubeAverage_eq_principalFactor
        M n h p m hh hp hscale

/-- Uniform thermodynamic upper bound for the literal parent weighted slope. -/
theorem exists_eventually_integral_oneStepDirichletSlopeField_weightedCubeAverage_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (hh : 0 < h) (_hp : vecNormSq p = 1)
        (_hscale : (h : ℝ) ≤ M.delta⁻¹) {epsilon : ℝ}, 0 < epsilon →
        ∀ᶠ K : ℕ in Filter.atTop,
          ∫ omega, cubeAverage (originCube d (K : ℤ)) (fun x ↦
              Real.exp (oneStepCenteredShellAt M n h x omega) *
                vecNormSq (oneStepDirichletSlopeField M n h p
                  (originCube d (K : ℤ)) omega hh x)) ∂M.P.toMeasure ≤
            1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
              C * M.delta ^ 4 * (h : ℝ) ^ 2 + epsilon := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_eventually_integral_oneStepDirichletWeightedPrincipalFactor_le d
  refine ⟨C, hC, ?_⟩
  intro M n h p hh hp hscale epsilon hepsilon
  filter_upwards [hbound M n h p hh hp hscale hepsilon] with K hK
  rw [integral_oneStepDirichletSlopeField_weightedCubeAverage_eq_principalFactor
    M n h p (K : ℤ) hh hp hscale]
  exact hK

/-! ## Reciprocal parent energy -/

private theorem vecNormSq_smul_sub_expand {d : ℕ}
    (r : ℝ) (p G : Vec d) :
    vecNormSq (r • p - G) =
      r ^ 2 * vecNormSq p - 2 * r * vecDot p G + vecNormSq G := by
  simp only [vecNormSq, sub_eq_add_neg, vecDot_add_left, vecDot_add_right,
    vecDot_neg_left, vecDot_neg_right, vecDot_smul_left, vecDot_smul_right,
    vecDot_comm G p]
  ring

theorem integrableOn_inverseCenteredShell_mul_vecNormSq
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (F : Vec d → Vec d)
    (hF : IntegrableOn (fun x ↦ vecNormSq (F x))
      (openCubeSet Q) volume) :
    IntegrableOn (fun x ↦
      Real.exp (-oneStepCenteredShellAt M n h x omega) *
        vecNormSq (F x)) (openCubeSet Q) volume := by
  let B : Vec d → ℝ := fun x ↦
    Real.exp (-oneStepCenteredShellAt M n h x omega)
  let C : ℝ := oneStepLowerSourceCellWeight M n h Q omega
  have hBmeas : Measurable B :=
    (measurable_oneStepCenteredShellAt_space M n h omega).neg.exp
  have hBbd : ∀ᵐ x ∂volume.restrict (openCubeSet Q), ‖B x‖ ≤ C := by
    rw [ae_restrict_iff' (measurableSet_openCubeSet Q)]
    filter_upwards with x hx
    dsimp only [B, C]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_neg_oneStepCenteredShellAt_le_lowerSourceCellWeight
      M n h Q omega hh hx
  exact hF.bdd_mul hBmeas.aestronglyMeasurable hBbd

/-- The reciprocal cubic carrier is the normalized literal
`(exp (-H) - 1) |grad W|^2` term. -/
theorem oneStepOriginNeumannInverseWeightedCubicBorel_eq_cubeAverage
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    oneStepOriginNeumannInverseWeightedCubicBorel M n h p m omega =
      cubeAverage (originCube d m) (fun x ↦
        (Real.exp (-oneStepCenteredShellAt M n h x omega) - 1) *
          vecNormSq
            ((oneStepOriginNeumannSolution M n h p m omega hh).toH1Function
              |>.grad x)) := by
  let Q := originCube d m
  let u := oneStepOriginNeumannGradientL2 M n h p m omega
  let z := oneStepInverseShellForcingL2 M n h p Q omega
  obtain ⟨_C, _hC, hCZ⟩ := exists_oneStepOriginNeumann_gradient_four_cz d
  have huRaw := (hCZ M n h omega p m hh hp).1
  have hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hmem := memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure
      Q (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function huRaw
    have hmem' : MemLp
        ((oneStepOriginNeumannSolution M n h p m omega hh)
          |>.gradToHilbertVectorL2 : Vec d → HilbertVec d) 4
          (normalizedCubeMeasure Q) := by
      simpa only [H1MeanZeroFunction.gradToHilbertVectorL2] using hmem
    rw [oneStepOriginNeumannSolution_gradient_eq M n h p m omega hh] at hmem'
    exact hmem'
  have hz4 : MemLp (z : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    have hz4pos : MemLp
        (oneStepLinearShellForcingL2 Q p n h omega : Vec d → HilbertVec d) 4
        (normalizedCubeMeasure Q) :=
      memLp_four_oneStepContinuousScalarForcingL2 Q p
        (oneStepShellSumContinuousMap n h omega)
    have he4 : MemLp
        (oneStepInverseExpRemainderForcingL2 M n h p Q omega :
          Vec d → HilbertVec d) 4 (normalizedCubeMeasure Q) :=
      memLp_four_oneStepContinuousScalarForcingL2 Q p
        (oneStepInverseExpRemainderContinuousMap M n h omega)
    have hneg : MemLp
        ((-oneStepLinearShellForcingL2 Q p n h omega :
          HilbertVectorL2 (openCubeSet Q)) : Vec d → HilbertVec d)
          4 (normalizedCubeMeasure Q) := by
      have hcoe : ((-oneStepLinearShellForcingL2 Q p n h omega :
          HilbertVectorL2 (openCubeSet Q)) : Vec d → HilbertVec d) =ᵐ[
            normalizedCubeMeasure Q]
          -(oneStepLinearShellForcingL2 Q p n h omega :
            Vec d → HilbertVec d) := by
        apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
        exact Lp.coeFn_neg (oneStepLinearShellForcingL2 Q p n h omega)
      exact hz4pos.neg.ae_eq (by
        simpa only [Pi.neg_apply] using hcoe.symm)
    have hadd : ((-oneStepLinearShellForcingL2 Q p n h omega +
        oneStepInverseExpRemainderForcingL2 M n h p Q omega :
          HilbertVectorL2 (openCubeSet Q)) : Vec d → HilbertVec d) =ᵐ[
            normalizedCubeMeasure Q]
        (((-oneStepLinearShellForcingL2 Q p n h omega :
          HilbertVectorL2 (openCubeSet Q)) : Vec d → HilbertVec d) +
          (oneStepInverseExpRemainderForcingL2 M n h p Q omega :
            Vec d → HilbertVec d)) := by
      apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      exact Lp.coeFn_add _ _
    exact (hneg.add he4).ae_eq (by simpa only [z,
      oneStepInverseShellForcingL2] using hadd.symm)
  have huCoe : (u : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      fun x ↦ HilbertVec.ofVec
        ((oneStepOriginNeumannSolution M n h p m omega hh).toH1Function.grad x) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    have hcoe := (oneStepOriginNeumannSolution M n h p m omega hh)
      |>.toH1Function.coeFn_gradToHilbertVectorL2
    have hcoe' : ((oneStepOriginNeumannSolution M n h p m omega hh)
        |>.gradToHilbertVectorL2 : Vec d → HilbertVec d) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
        fun x ↦ HilbertVec.ofVec
          ((oneStepOriginNeumannSolution M n h p m omega hh).toH1Function.grad x) := by
      simpa only [Q, H1MeanZeroFunction.gradToHilbertVectorL2, hilbertifyVecField] using! hcoe
    rw [oneStepOriginNeumannSolution_gradient_eq M n h p m omega hh] at hcoe'
    simpa only [u] using hcoe'
  have hzCoe : (z : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      fun x ↦ (Real.exp (-oneStepCenteredShellAt M n h x omega) - 1) •
        HilbertVec.ofVec p := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    have hlin := coeFn_toHilbertVectorL2OfVecField
      (memVectorL2_openCubeSet_of_continuous Q
        ((oneStepShellSumContinuousMap n h omega).continuous.smul
          (continuous_const : Continuous fun _ : Vec d ↦ p)))
    have hrem := coeFn_toHilbertVectorL2OfVecField
      (memVectorL2_openCubeSet_of_continuous Q
        ((oneStepInverseExpRemainderContinuousMap M n h omega).continuous.smul
          (continuous_const : Continuous fun _ : Vec d ↦ p)))
    have hneg := Lp.coeFn_neg (oneStepLinearShellForcingL2 Q p n h omega)
    have hadd := Lp.coeFn_add
      (-oneStepLinearShellForcingL2 Q p n h omega)
      (oneStepInverseExpRemainderForcingL2 M n h p Q omega)
    filter_upwards [hlin, hrem, hneg, hadd] with x hlinx hremx hnegx haddx
    rw [show z = -oneStepLinearShellForcingL2 Q p n h omega +
      oneStepInverseExpRemainderForcingL2 M n h p Q omega by rfl, haddx,
      Pi.add_apply, hnegx]
    simp only [Pi.neg_apply]
    change -((toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepShellSumContinuousMap n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p))) :
          Vec d → HilbertVec d) x) +
      ((toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepInverseExpRemainderContinuousMap M n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p))) :
          Vec d → HilbertVec d) x) = _
    rw [hlinx, hremx]
    apply HilbertVec.ext
    intro i
    rw [oneStepInverseMultiplierAt_eq_negShell_add_remainder M n h x omega]
    simp [hilbertifyVecField, oneStepShellSumContinuousMap,
      oneStepInverseExpRemainderContinuousMap]
    ring
  rw [oneStepOriginNeumannInverseWeightedCubicBorel,
    oneStepNormalizedWeightedCubicBorel_eq_cubeAverage Q
      (HilbertVec.ofVec p) u z hu4 hz4]
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  apply integral_congr_ae
  filter_upwards [huCoe, hzCoe] with x hux hzx
  unfold oneStepWeightedCubicIntegrand
  rw [hux, hzx, HilbertVec.norm_sq_ofVec,
    inner_smul_right, HilbertVec.inner_def]
  rw [show vecDot p p = vecNormSq p by rfl, hp]
  simp only [vecNormSq]
  ring

/-- Samplewise reciprocal weighted energy.  The spatial cross term is kept
explicit: as in the manuscript, it vanishes only after expectation. -/
theorem oneStepOriginNeumann_weightedCubeAverage_identity
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hp : vecNormSq p = 1) :
    cubeAverage (originCube d m) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq
            (p + oneStepMultiplierAt M n h x omega • p -
              ((oneStepOriginNeumannSolution M n h p m omega hh).toH1Function.grad x))) =
      cubeAverage (originCube d m) (fun x ↦
        Real.exp (oneStepCenteredShellAt M n h x omega)) -
        2 * cubeAverage (originCube d m) (fun x ↦
          vecDot p ((oneStepOriginNeumannSolution M n h p m omega hh).toH1Function.grad x)) +
        oneStepNeumannCorrectorEnergy M n h p
          (originCube d m) omega hh +
        oneStepOriginNeumannInverseWeightedCubicBorel M n h p m omega := by
  let Q := originCube d m
  let G : Vec d → Vec d := fun x ↦
    (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function.grad x
  let b : Vec d → ℝ := fun x ↦
    Real.exp (oneStepCenteredShellAt M n h x omega)
  let c : Vec d → ℝ := fun x ↦
    Real.exp (-oneStepCenteredShellAt M n h x omega)
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hb : IntegrableOn b (openCubeSet Q) volume := by
    apply integrableOn_of_continuous _ (isBounded_openCubeSet Q)
    dsimp only [b, oneStepCenteredShellAt, cutoffShellSum]
    exact Real.continuous_exp.comp
      ((continuous_finsetSum _ fun k _ ↦ (omega k).1.1.continuous).sub
        continuous_const)
  have hG : MemVectorL2 (openCubeSet Q) G :=
    (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function
      |>.grad_memVectorL2
  have hGsq : IntegrableOn (fun x ↦ vecNormSq (G x))
      (openCubeSet Q) volume := by
    simpa only [vecNormSq] using
      integrableOn_vecDot_of_memVectorL2 hG hG
  have hqG : IntegrableOn (fun x ↦ vecDot p (G x))
      (openCubeSet Q) volume :=
    integrableOn_vecDot_of_memVectorL2 (memLp_const p) hG
  have hcG : IntegrableOn (fun x ↦ c x * vecNormSq (G x))
      (openCubeSet Q) volume := by
    simpa only [c, G] using
      integrableOn_inverseCenteredShell_mul_vecNormSq
        M n h Q omega hh G hGsq
  have hrem : IntegrableOn (fun x ↦ (c x - 1) * vecNormSq (G x))
      (openCubeSet Q) volume := by
    have heq : (fun x ↦ (c x - 1) * vecNormSq (G x)) =
        fun x ↦ c x * vecNormSq (G x) - vecNormSq (G x) := by
      funext x
      ring
    rw [heq]
    exact hcG.sub hGsq
  have hraw :
      ∫ x in openCubeSet Q,
          c x * vecNormSq
            (p + oneStepMultiplierAt M n h x omega • p - G x) ∂volume =
        (∫ x in openCubeSet Q, b x ∂volume) -
          2 * (∫ x in openCubeSet Q, vecDot p (G x) ∂volume) +
          (∫ x in openCubeSet Q, vecNormSq (G x) ∂volume) +
          ∫ x in openCubeSet Q,
            (c x - 1) * vecNormSq (G x) ∂volume := by
    have hpoint : (fun x ↦
        c x * vecNormSq
          (p + oneStepMultiplierAt M n h x omega • p - G x)) =
        fun x ↦ b x - 2 * vecDot p (G x) + vecNormSq (G x) +
          (c x - 1) * vecNormSq (G x) := by
      funext x
      rw [oneStepMultiplierAt_eq_exp_centeredShell_sub_one
        M n h x omega hh]
      dsimp only [b, c]
      have hbc : Real.exp (-oneStepCenteredShellAt M n h x omega) *
          Real.exp (oneStepCenteredShellAt M n h x omega) = 1 := by
        rw [← Real.exp_add]
        simp
      have hcb2 : Real.exp (-oneStepCenteredShellAt M n h x omega) *
          Real.exp (oneStepCenteredShellAt M n h x omega) ^ 2 =
          Real.exp (oneStepCenteredShellAt M n h x omega) := by
        calc
          _ = (Real.exp (-oneStepCenteredShellAt M n h x omega) *
              Real.exp (oneStepCenteredShellAt M n h x omega)) *
                Real.exp (oneStepCenteredShellAt M n h x omega) := by ring
          _ = _ := by rw [hbc, one_mul]
      have hbpos := Real.exp_pos (oneStepCenteredShellAt M n h x omega)
      have hcpos := Real.exp_pos (-oneStepCenteredShellAt M n h x omega)
      have hslope : p +
          (Real.exp (oneStepCenteredShellAt M n h x omega) - 1) • p - G x =
          Real.exp (oneStepCenteredShellAt M n h x omega) • p - G x := by
        ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hslope, vecNormSq_smul_sub_expand, hp]
      calc
        _ = Real.exp (-oneStepCenteredShellAt M n h x omega) *
              Real.exp (oneStepCenteredShellAt M n h x omega) ^ 2 -
            2 * (Real.exp (-oneStepCenteredShellAt M n h x omega) *
              Real.exp (oneStepCenteredShellAt M n h x omega)) *
                vecDot p (G x) +
            Real.exp (-oneStepCenteredShellAt M n h x omega) *
              vecNormSq (G x) := by ring
        _ = _ := by rw [hcb2, hbc]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall fun x ↦
      congrFun hpoint x)]
    have h1 := integral_sub hb (hqG.const_mul 2)
    have h2 := integral_add (hb.sub (hqG.const_mul 2)) hGsq
    have h3 := integral_add ((hb.sub (hqG.const_mul 2)).add hGsq) hrem
    simpa only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply,
      integral_const_mul] using h3.trans (congrArg (fun r ↦ r +
        ∫ x in openCubeSet Q, (c x - 1) * vecNormSq (G x) ∂volume)
          (h2.trans (congrArg (fun r ↦ r +
            ∫ x in openCubeSet Q, vecNormSq (G x) ∂volume) h1)))
  have hscaled := congrArg (fun r : ℝ ↦ (cubeVolume Q)⁻¹ * r) hraw
  rw [oneStepNeumannCorrectorEnergy_eq_originGradient
      M n h p m omega hh,
    oneStepOriginNeumannInverseWeightedCubicBorel_eq_cubeAverage
      M n h p m omega hh hp,
    cubeAverage, cubeAverage, cubeAverage, cubeAverage,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet] at ⊢
  have henergy :
      ‖oneStepOriginNeumannGradientL2 M n h p m omega‖ ^ 2 =
        ∫ x in openCubeSet Q, vecNormSq (G x) ∂volume := by
    rw [← oneStepOriginNeumannSolution_gradient_eq M n h p m omega hh,
      ← real_inner_self_eq_norm_sq]
    simpa only [Q, G, H1MeanZeroFunction.gradToHilbertVectorL2,
      H1Function.gradToHilbertVectorL2, vecNormSq] using
      (inner_toHilbertVectorL2OfVecField_eq_integral hG hG)
  rw [henergy]
  dsimp only [Q, G, b, c] at hscaled ⊢
  calc
    _ = (cubeVolume (originCube d m))⁻¹ *
        (((∫ x in openCubeSet (originCube d m),
            Real.exp (oneStepCenteredShellAt M n h x omega) ∂volume) -
          2 * ∫ x in openCubeSet (originCube d m),
            vecDot p ((oneStepOriginNeumannSolution M n h p m omega hh)
              |>.toH1Function.grad x) ∂volume) +
          (∫ x in openCubeSet (originCube d m),
            vecNormSq ((oneStepOriginNeumannSolution M n h p m omega hh)
              |>.toH1Function.grad x) ∂volume) +
          ∫ x in openCubeSet (originCube d m),
            (Real.exp (-oneStepCenteredShellAt M n h x omega) - 1) *
              vecNormSq ((oneStepOriginNeumannSolution M n h p m omega hh)
                |>.toH1Function.grad x) ∂volume) := hscaled
    _ = _ := by ring

/-- The constant-gradient pairing is the continuous linear readout of the
canonical Neumann gradient in `HilbertVectorL2`. -/
theorem cubeAverage_vecDot_oneStepOriginNeumannGradient_eq_inner
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    cubeAverage (originCube d m) (fun x ↦
        vecDot p ((oneStepOriginNeumannSolution M n h p m omega hh)
          |>.toH1Function.grad x)) =
      (cubeVolume (originCube d m))⁻¹ *
        (innerSL ℝ (oneStepConstantVectorL2 (originCube d m) p))
          (oneStepOriginNeumannGradientL2 M n h p m omega) := by
  let Q := originCube d m
  let G := oneStepOriginNeumannGradientL2 M n h p m omega
  let e : HilbertVectorL2 (openCubeSet Q) := oneStepConstantVectorL2 Q p
  have heCoe := coeFn_toHilbertVectorL2OfVecField
    (memVectorL2_const (U := openCubeSet Q) p)
  have hGCoe := (oneStepOriginNeumannSolution M n h p m omega hh)
    |>.toH1Function.coeFn_gradToHilbertVectorL2
  have hGeq : G = H1Function.gradToHilbertVectorL2
      (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function := by
    dsimp only [G]
    rw [← oneStepOriginNeumannSolution_gradient_eq M n h p m omega hh]
    rfl
  have hinner : (innerSL ℝ e) G =
      ∫ x in openCubeSet Q,
        vecDot p ((oneStepOriginNeumannSolution M n h p m omega hh)
          |>.toH1Function.grad x) ∂volume := by
    rw [innerSL_apply_apply, L2.inner_def, hGeq]
    apply integral_congr_ae
    filter_upwards [heCoe, hGCoe] with x hex hgx
    rw [show (e : Vec d → HilbertVec d) x = HilbertVec.ofVec p by
      simpa only [e, oneStepConstantVectorL2, hilbertifyVecField] using! hex,
      show (H1Function.gradToHilbertVectorL2
          (oneStepOriginNeumannSolution M n h p m omega hh).toH1Function :
            Vec d → HilbertVec d) x =
          HilbertVec.ofVec
            ((oneStepOriginNeumannSolution M n h p m omega hh)
              |>.toH1Function.grad x) by
        simpa only [H1Function.gradToHilbertVectorL2, hilbertifyVecField] using! hgx,
      HilbertVec.inner_def]
  unfold cubeAverage
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet, hinner]

/-- The constant-gradient cross observable is integrable. -/
theorem integrable_cubeAverage_vecDot_oneStepOriginNeumannGradient
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) :
    Integrable (fun omega ↦ cubeAverage (originCube d m) (fun x ↦
      vecDot p ((oneStepOriginNeumannSolution M n h p m omega hh)
        |>.toH1Function.grad x))) M.P.toMeasure := by
  let Q := originCube d m
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q)
      (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  let D : HilbertVectorL2 (openCubeSet Q) →L[ℝ]
      HilbertVectorL2 (openCubeSet Q) :=
    oneStepNeumannGradientOfForcingCLM
      (translatedCubeMeanZeroH1CoerciveEstimate Q)
      (openCubeSet_nonempty_internal Q) hEll
  let F : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVectorL2 (openCubeSet Q) :=
    oneStepShellForcingL2 M n h p Q
  let G : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVectorL2 (openCubeSet Q) :=
    oneStepOriginNeumannGradientL2 M n h p m
  let e : HilbertVectorL2 (openCubeSet Q) := oneStepConstantVectorL2 Q p
  let L : HilbertVectorL2 (openCubeSet Q) →L[ℝ] ℝ := innerSL ℝ e
  have hFmem : MemLp F 2 M.P.toMeasure := by
    simpa only [F] using memLp_two_oneStepShellForcingL2 M n h p Q hh
  have hGaestrong : AEStronglyMeasurable G M.P.toMeasure := by
    change AEStronglyMeasurable (fun omega ↦
      D (-(oneStepShellForcingL2 M n h p Q omega))) M.P.toMeasure
    exact D.continuous.comp_aestronglyMeasurable hFmem.aestronglyMeasurable.neg
  have hGmem : MemLp G 2 M.P.toMeasure := by
    apply hFmem.norm.mono' hGaestrong
    filter_upwards with omega
    exact norm_oneStepOriginNeumannGradientL2_le_forcing
      M n h p m omega hh
  have hGint : Integrable G M.P.toMeasure := hGmem.integrable (by norm_num)
  have hLint : Integrable (fun omega ↦ L (G omega)) M.P.toMeasure :=
    L.integrable_comp hGint
  refine (hLint.const_mul (cubeVolume Q)⁻¹).congr ?_
  filter_upwards with omega
  exact (cubeAverage_vecDot_oneStepOriginNeumannGradient_eq_inner
    M n h p m omega hh).symm

/-- Expectation of the literal reciprocal parent energy is exactly the
measurable reciprocal principal-factor expectation. -/
theorem integral_oneStepOriginNeumann_weightedCubeAverage_eq_principalFactor
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ∫ omega, cubeAverage (originCube d m) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq
            (p + oneStepMultiplierAt M n h x omega • p -
              ((oneStepOriginNeumannSolution M n h p m omega hh)
                |>.toH1Function.grad x))) ∂M.P.toMeasure =
      ∫ omega, oneStepNeumannWeightedPrincipalFactor
        M n h p m omega hh ∂M.P.toMeasure := by
  let base : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
    cubeAverage (originCube d m) (fun x ↦
      Real.exp (oneStepCenteredShellAt M n h x omega))
  let cross : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
    cubeAverage (originCube d m) (fun x ↦
      vecDot p ((oneStepOriginNeumannSolution M n h p m omega hh)
        |>.toH1Function.grad x))
  let energy : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
    oneStepNeumannCorrectorEnergy M n h p (originCube d m) omega hh
  let cubic : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
    oneStepOriginNeumannInverseWeightedCubicBorel M n h p m
  let full : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
    cubeAverage (originCube d m) (fun x ↦
      Real.exp (-oneStepCenteredShellAt M n h x omega) *
        vecNormSq
          (p + oneStepMultiplierAt M n h x omega • p -
            ((oneStepOriginNeumannSolution M n h p m omega hh)
              |>.toH1Function.grad x)))
  have hbase := integral_cubeAverage_exp_oneStepCenteredShellAt_eq_one
    M n h (originCube d m) hh
  have hcrossInt : Integrable cross M.P.toMeasure := by
    simpa only [cross] using
      integrable_cubeAverage_vecDot_oneStepOriginNeumannGradient
        M n h p m hh
  have hcrossZero : ∫ omega, cross omega ∂M.P.toMeasure = 0 := by
    simpa only [cross] using
      integral_cubeAverage_vecDot_oneStepOriginNeumannGradient_eq_zero
        M n h p m hh
  have henergy : Integrable energy M.P.toMeasure := by
    exact integrable_oneStepNeumannCorrectorEnergy
      M n h p (originCube d m) hh hp
  obtain ⟨_C, _hC, hcubic⟩ :=
    exists_integral_oneStepOriginNeumannInverseWeightedCubicBorel_le d
  have hcubicInt : Integrable cubic M.P.toMeasure :=
    (hcubic M n h p m hh hp hscale).1
  have hpoint : full = fun omega ↦
      base omega - 2 * cross omega + energy omega + cubic omega := by
    funext omega
    exact oneStepOriginNeumann_weightedCubeAverage_identity
      M n h p m omega hh hp
  have hsplit :
      ∫ omega, base omega - 2 * cross omega + energy omega + cubic omega
          ∂M.P.toMeasure =
        ((∫ omega, base omega ∂M.P.toMeasure) -
            2 * ∫ omega, cross omega ∂M.P.toMeasure) +
          ∫ omega, energy omega ∂M.P.toMeasure +
          ∫ omega, cubic omega ∂M.P.toMeasure := by
    calc
      _ = (∫ omega, base omega - 2 * cross omega + energy omega
            ∂M.P.toMeasure) +
          ∫ omega, cubic omega ∂M.P.toMeasure :=
        integral_add ((hbase.2.sub (hcrossInt.const_mul 2)).add henergy)
          hcubicInt
      _ = ((∫ omega, base omega - 2 * cross omega ∂M.P.toMeasure) +
            ∫ omega, energy omega ∂M.P.toMeasure) +
          ∫ omega, cubic omega ∂M.P.toMeasure := by
        congr 1
        exact integral_add (hbase.2.sub (hcrossInt.const_mul 2)) henergy
      _ = _ := by
        rw [integral_sub hbase.2 (hcrossInt.const_mul 2),
          integral_const_mul]
  change ∫ omega, full omega ∂M.P.toMeasure = _
  rw [integral_congr_ae (Filter.Eventually.of_forall fun omega ↦
      congrFun hpoint omega), hsplit, hcrossZero, mul_zero, sub_zero]
  unfold oneStepNeumannWeightedPrincipalFactor
  have hbaseEq : ∫ omega, base omega ∂M.P.toMeasure = 1 := by
    simpa only [base] using hbase.1
  rw [hbaseEq]
  symm
  calc
    _ = (∫ omega, 1 + energy omega ∂M.P.toMeasure) +
        ∫ omega, cubic omega ∂M.P.toMeasure :=
      integral_add ((integrable_const 1).add henergy) hcubicInt
    _ = ((∫ _omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, (1 : ℝ) ∂M.P.toMeasure) +
          ∫ omega, energy omega ∂M.P.toMeasure) +
        ∫ omega, cubic omega ∂M.P.toMeasure := by
      rw [integral_add (integrable_const 1) henergy]
    _ = _ := by
      rw [integral_const]
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

/-- On an origin parent cube, the translation-covariant Neumann solution and
the canonical origin solution give the same reciprocal weighted slope. -/
theorem cubeAverage_oneStepNeumannSlopeField_origin_eq_originSolution
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    cubeAverage (originCube d m) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepNeumannSlopeField M n h p
            (originCube d m) omega hh x)) =
      cubeAverage (originCube d m) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq
            (p + oneStepMultiplierAt M n h x omega • p -
              ((oneStepOriginNeumannSolution M n h p m omega hh)
                |>.toH1Function.grad x))) := by
  let Q := originCube d m
  let u := oneStepOriginNeumannGradientL2 M n h p m omega
  let v := H1MeanZeroFunction.gradToHilbertVectorL2
    (oneStepTriadicNeumannSolution M n h p Q omega hh)
  have huv : u = v :=
    oneStepOriginNeumannGradientL2_eq_triadic M n h p m omega hh
  have huCoe : (u : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      fun x ↦ HilbertVec.ofVec
        ((oneStepOriginNeumannSolution M n h p m omega hh).toH1Function.grad x) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    have hcoe := (oneStepOriginNeumannSolution M n h p m omega hh)
      |>.toH1Function.coeFn_gradToHilbertVectorL2
    have hcoe' : ((oneStepOriginNeumannSolution M n h p m omega hh)
        |>.gradToHilbertVectorL2 : Vec d → HilbertVec d) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
        fun x ↦ HilbertVec.ofVec
          ((oneStepOriginNeumannSolution M n h p m omega hh).toH1Function.grad x) := by
      simpa only [Q, H1MeanZeroFunction.gradToHilbertVectorL2, hilbertifyVecField] using! hcoe
    rw [oneStepOriginNeumannSolution_gradient_eq M n h p m omega hh] at hcoe'
    simpa only [u] using hcoe'
  have hvCoe : (v : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      fun x ↦ HilbertVec.ofVec
        ((oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function.grad x) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    simpa only [v, H1MeanZeroFunction.gradToHilbertVectorL2,
      H1Function.gradToHilbertVectorL2, hilbertifyVecField] using!
      (oneStepTriadicNeumannSolution M n h p Q omega hh)
        |>.toH1Function.coeFn_gradToHilbertVectorL2
  have hgrad : (fun x ↦
      (oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function.grad x) =ᵐ[
        normalizedCubeMeasure Q]
      fun x ↦ (oneStepOriginNeumannSolution M n h p m omega hh)
        |>.toH1Function.grad x := by
    rw [huv] at huCoe
    filter_upwards [hvCoe, huCoe] with x hvx hux
    have hx := congrArg HilbertVec.toVec (hvx.symm.trans hux)
    simpa only [HilbertVec.toVec_ofVec] using hx
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  apply integral_congr_ae
  filter_upwards [hgrad] with x hx
  unfold oneStepNeumannSlopeField
  rw [hx]

/-- The literal reciprocal parent weighted-slope expectation is the
controlled reciprocal principal factor. -/
theorem integral_oneStepNeumannSlopeField_weightedCubeAverage_eq_principalFactor
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ∫ omega, cubeAverage (originCube d m) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepNeumannSlopeField M n h p
            (originCube d m) omega hh x)) ∂M.P.toMeasure =
      ∫ omega, oneStepNeumannWeightedPrincipalFactor
        M n h p m omega hh ∂M.P.toMeasure := by
  calc
    _ = ∫ omega, cubeAverage (originCube d m) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq
            (p + oneStepMultiplierAt M n h x omega • p -
              ((oneStepOriginNeumannSolution M n h p m omega hh)
                |>.toH1Function.grad x))) ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      exact cubeAverage_oneStepNeumannSlopeField_origin_eq_originSolution
        M n h p m omega hh
    _ = _ :=
      integral_oneStepOriginNeumann_weightedCubeAverage_eq_principalFactor
        M n h p m hh hp hscale

/-- Uniform thermodynamic bound for the literal reciprocal parent slope. -/
theorem exists_eventually_integral_oneStepNeumannSlopeField_weightedCubeAverage_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (hh : 0 < h) (_hp : vecNormSq p = 1)
        (_hscale : (h : ℝ) ≤ M.delta⁻¹) {epsilon : ℝ}, 0 < epsilon →
        ∀ᶠ K : ℕ in Filter.atTop,
          ∫ omega, cubeAverage (originCube d (K : ℤ)) (fun x ↦
              Real.exp (-oneStepCenteredShellAt M n h x omega) *
                vecNormSq (oneStepNeumannSlopeField M n h p
                  (originCube d (K : ℤ)) omega hh x)) ∂M.P.toMeasure ≤
            1 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
              C * M.delta ^ 4 * (h : ℝ) ^ 2 + epsilon := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_eventually_integral_oneStepNeumannWeightedPrincipalFactor_le d
  refine ⟨C, hC, ?_⟩
  intro M n h p hh hp hscale epsilon hepsilon
  filter_upwards [hbound M n h p hh hp hscale hepsilon] with K hK
  rw [integral_oneStepNeumannSlopeField_weightedCubeAverage_eq_principalFactor
    M n h p (K : ℤ) hh hp hscale]
  exact hK

theorem integrable_oneStepDirichletSlopeField_weightedCubeAverage
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (K : ℕ) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    Integrable (fun omega => cubeAverage (originCube d (K : ℤ)) (fun x =>
      Real.exp (oneStepCenteredShellAt M n h x omega) *
        vecNormSq (oneStepDirichletSlopeField M n h p
          (originCube d (K : ℤ)) omega hh x))) M.P.toMeasure := by
  let m : ℤ := K
  let Q := originCube d m
  let base : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => cubeAverage Q (fun x =>
    Real.exp (oneStepCenteredShellAt M n h x omega))
  let energy : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    oneStepDirichletCorrectorEnergy M n h p Q omega hh
  let cubic : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
    oneStepOriginDirichletWeightedCubicBorel M n h p m
  let fullOrigin : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => cubeAverage Q (fun x =>
    Real.exp (oneStepCenteredShellAt M n h x omega) *
      vecNormSq (p + ((oneStepOriginDirichletSolution M n h p m omega hh)
        |>.toH1Function.grad x)))
  let full : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => cubeAverage Q (fun x =>
    Real.exp (oneStepCenteredShellAt M n h x omega) *
      vecNormSq (oneStepDirichletSlopeField M n h p Q omega hh x))
  have hbase := integral_cubeAverage_exp_oneStepCenteredShellAt_eq_one
    M n h Q hh
  have henergy : Integrable energy M.P.toMeasure :=
    integrable_oneStepDirichletCorrectorEnergy M n h p Q hh hp
  obtain ⟨_C, _hC, hcubic⟩ :=
    exists_integral_oneStepOriginDirichletWeightedCubicBorel_le d
  have hcubicInt : Integrable cubic M.P.toMeasure :=
    (hcubic M n h p m hh hp hscale).1
  have hpointOrigin : fullOrigin = fun omega =>
      base omega - energy omega + cubic omega := by
    funext omega
    exact oneStepOriginDirichlet_weightedCubeAverage_identity
      M n h p m omega hh hp
  have hfullOrigin : Integrable fullOrigin M.P.toMeasure := by
    exact ((hbase.2.sub henergy).add hcubicInt).congr
      (Filter.Eventually.of_forall fun omega =>
        (congrFun hpointOrigin omega).symm)
  have hfull : full = fullOrigin := by
    funext omega
    exact cubeAverage_oneStepDirichletSlopeField_origin_eq_originSolution
      M n h p m omega hh
  change Integrable full M.P.toMeasure
  rw [hfull]
  exact hfullOrigin

theorem integrable_oneStepNeumannSlopeField_weightedCubeAverage
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (q : Vec d) (K : ℕ) (hh : 0 < h) (hq : vecNormSq q = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    Integrable (fun omega => cubeAverage (originCube d (K : ℤ)) (fun x =>
      Real.exp (-oneStepCenteredShellAt M n h x omega) *
        vecNormSq (oneStepNeumannSlopeField M n h q
          (originCube d (K : ℤ)) omega hh x))) M.P.toMeasure := by
  let m : ℤ := K
  let Q := originCube d m
  let base : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => cubeAverage Q (fun x =>
    Real.exp (oneStepCenteredShellAt M n h x omega))
  let cross : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => cubeAverage Q (fun x =>
    vecDot q ((oneStepOriginNeumannSolution M n h q m omega hh)
      |>.toH1Function.grad x))
  let energy : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    oneStepNeumannCorrectorEnergy M n h q Q omega hh
  let cubic : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
    oneStepOriginNeumannInverseWeightedCubicBorel M n h q m
  let fullOrigin : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => cubeAverage Q (fun x =>
    Real.exp (-oneStepCenteredShellAt M n h x omega) *
      vecNormSq (q + oneStepMultiplierAt M n h x omega • q -
        (oneStepOriginNeumannSolution M n h q m omega hh).toH1Function.grad x))
  let full : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => cubeAverage Q (fun x =>
    Real.exp (-oneStepCenteredShellAt M n h x omega) *
      vecNormSq (oneStepNeumannSlopeField M n h q Q omega hh x))
  have hbase := integral_cubeAverage_exp_oneStepCenteredShellAt_eq_one
    M n h Q hh
  have hcross : Integrable cross M.P.toMeasure := by
    simpa only [cross, Q, m] using
      integrable_cubeAverage_vecDot_oneStepOriginNeumannGradient
        M n h q m hh
  have henergy : Integrable energy M.P.toMeasure :=
    integrable_oneStepNeumannCorrectorEnergy M n h q Q hh hq
  obtain ⟨_C, _hC, hcubic⟩ :=
    exists_integral_oneStepOriginNeumannInverseWeightedCubicBorel_le d
  have hcubicInt : Integrable cubic M.P.toMeasure :=
    (hcubic M n h q m hh hq hscale).1
  have hpointOrigin : fullOrigin = fun omega =>
      base omega - 2 * cross omega + energy omega + cubic omega := by
    funext omega
    exact oneStepOriginNeumann_weightedCubeAverage_identity
      M n h q m omega hh hq
  have hfullOrigin : Integrable fullOrigin M.P.toMeasure := by
    exact (((hbase.2.sub (hcross.const_mul 2)).add henergy).add hcubicInt).congr
      (Filter.Eventually.of_forall fun omega =>
        (congrFun hpointOrigin omega).symm)
  have hfull : full = fullOrigin := by
    funext omega
    exact cubeAverage_oneStepNeumannSlopeField_origin_eq_originSolution
      M n h q m omega hh
  change Integrable full M.P.toMeasure
  rw [hfull]
  exact hfullOrigin


end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
