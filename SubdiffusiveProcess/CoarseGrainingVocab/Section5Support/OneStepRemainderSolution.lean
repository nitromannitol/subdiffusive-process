module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepExponentialRemainder
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNestedMomentSweep

@[expose] public section




open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Joint measurability of the scalar exponential forcing remainder. -/
theorem measurable_oneStepExpRemainderAt_uncurry {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) :
    Measurable fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d ↦
      oneStepExpRemainderAt M n h q.2 q.1 := by
  have hs : Measurable fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d ↦
      cutoffShellSum (n + h) (n : ℤ) q.2 q.1 :=
    measurable_cutoffShellSum_uncurry n h
  simpa only [oneStepExpRemainderAt, oneStepCenteredShellAt] using!
    ((hs.sub_const _).exp.sub_const _).sub hs

/-- The remainder is spatially `L⁴` on every finite cube. -/
theorem memLp_four_oneStepExpRemainderAt_spatial {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    MemLp (fun x ↦ oneStepExpRemainderAt M n h x omega) 4
      (normalizedCubeMeasure (originCube d m)) := by
  have hcont : Continuous fun x ↦
      oneStepExpRemainderAt M n h x omega := by
    exact (((Real.continuous_exp.comp
      ((continuous_finset_sum _ fun k _ ↦
        (omega k).1.1.continuous).sub continuous_const)).sub
          continuous_const).sub
      (continuous_finset_sum _ fun k _ ↦ (omega k).1.1.continuous))
  exact SubdiffusiveProcess.CoarseGrainingVocab.memLp_normalizedCubeMeasure_of_continuous
    (originCube d m) (4 : ℝ≥0∞) hcont

/-- Joint spatial--random fourth moment of the exponential forcing remainder.
The estimate is uniform in the cube scale and lower cutoff. -/
theorem lintegral_lintegral_oneStepExpRemainder_four_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (m : ℤ)
    (hh : 0 < h) (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ∫⁻ omega, ∫⁻ x,
        ‖oneStepExpRemainderAt M n h x omega‖ₑ ^ (4 : ℝ)
          ∂normalizedCubeMeasure (originCube d m) ∂M.P.toMeasure ≤
      (oneStepExpRemainderConst *
        ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ) := by
  let Q := originCube d m
  let R : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d → ℝ := fun q ↦
    oneStepExpRemainderAt M n h q.2 q.1
  have hR : Measurable R := by
    simpa only [R] using! measurable_oneStepExpRemainderAt_uncurry M n h
  have hjoint : AEMeasurable
      (Function.uncurry fun omega x ↦ ‖R (omega, x)‖ₑ ^ (4 : ℝ))
      (M.P.toMeasure.prod (normalizedCubeMeasure Q)) := by
    simpa only [Function.uncurry_apply_pair] using!
      (hR.enorm.pow_const (4 : ℝ)).aemeasurable
  rw [lintegral_lintegral_swap hjoint]
  have hpoint : ∀ᵐ x ∂normalizedCubeMeasure Q,
      ∫⁻ omega, ‖R (omega, x)‖ₑ ^ (4 : ℝ) ∂M.P.toMeasure ≤
        (oneStepExpRemainderConst *
          ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ) := by
    filter_upwards with x
    let F : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega ↦ R (omega, x)
    have hmem := memLp_four_oneStepExpRemainderAt_spatial M n h m
    have hnorm : eLpNorm F 4 M.P.toMeasure ≤
        oneStepExpRemainderConst *
          ENNReal.ofReal (M.delta ^ 2 * (h : ℝ)) := by
      exact (eLpNorm_oneStepExpRemainderAt_four_le M n h x hh).trans
        (oneStepExpRemainderFourBound_le M h hh hscale)
    have hpow := ENNReal.rpow_le_rpow hnorm (by norm_num : (0 : ℝ) ≤ 4)
    have hFmeas : AEStronglyMeasurable F M.P.toMeasure := by
      simpa only [F, R, Function.comp_apply] using!
        (hR.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hFmeas] at hpow
    norm_num only [ENNReal.toReal_ofNat] at hpow
    have hquarter : (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num
    rw [hquarter, ENNReal.rpow_inv_rpow (by norm_num : (4 : ℝ) ≠ 0)] at hpow
    simpa only [F, R, ENNReal.rpow_natCast] using hpow
  calc
    (∫⁻ x, ∫⁻ omega, ‖R (omega, x)‖ₑ ^ (4 : ℝ)
        ∂M.P.toMeasure ∂normalizedCubeMeasure Q) ≤
      ∫⁻ _x, (oneStepExpRemainderConst *
        ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ)
          ∂normalizedCubeMeasure Q := lintegral_mono_ae hpoint
    _ = _ := by
      rw [lintegral_const]
      simp [normalizedCubeMeasure_apply_univ]

/-! ## Canonical cube solutions for the residual forcing -/

theorem continuous_oneStepExpRemainder_smul {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Continuous fun x ↦ oneStepExpRemainderAt M n h x omega • p := by
  change Continuous ((fun x ↦ oneStepExpRemainderAt M n h x omega) • (fun _ : Vec d ↦ p))
  apply Continuous.smul
  · exact (((Real.continuous_exp.comp
      ((continuous_finset_sum _ fun k _ ↦
        (omega k).1.1.continuous).sub continuous_const)).sub
          continuous_const).sub
      (continuous_finset_sum _ fun k _ ↦ (omega k).1.1.continuous))
  · exact continuous_const

/-- The canonical square-integrability certificate for the residual vector
forcing.  Naming it keeps the solution and weak-equation proofs
definitionally aligned. -/
def oneStepExpRemainderMemVectorL2 {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    MemVectorL2 (openCubeSet (originCube d m))
      (fun x ↦ oneStepExpRemainderAt M n h x omega • p) :=
  memVectorL2_openCubeSet_of_continuous (originCube d m)
    (continuous_oneStepExpRemainder_smul M n h p omega)

theorem oneStepSigmaOnePos : (0 : ℝ) < 1 := by norm_num

/-- Canonical zero-Dirichlet solution driven by the exponential forcing
remainder. -/
def oneStepExpRemainderDirichletSolution {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    H10Function (openCubeSet (originCube d m)) := by
  exact CubeCalderonZygmund.openCubeSetScalarDivergenceSolution
    (originCube d m) (sigma0 := 1) oneStepSigmaOnePos
      (fun x ↦ oneStepExpRemainderAt M n h x omega • p)
      (oneStepExpRemainderMemVectorL2 M n h p m omega)

theorem oneStepExpRemainderDirichletSolution_isWeakSolution
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d)
      (openCubeSet (originCube d m))
      (oneStepExpRemainderDirichletSolution M n h p m omega)
      (fun x ↦ -oneStepExpRemainderAt M n h x omega • p) := by
  have hw := CubeCalderonZygmund.openCubeSetScalarDivergenceSolution_weak
    (originCube d m) (sigma0 := 1) oneStepSigmaOnePos
      (fun x ↦ oneStepExpRemainderAt M n h x omega • p)
      (oneStepExpRemainderMemVectorL2 M n h p m omega)
  intro phi
  have hwphi := hw phi
  simp only [oneStepExpRemainderDirichletSolution,
    matVecMul_identityCoeffField] at hwphi ⊢
  calc
    _ = -∫ x in openCubeSet (originCube d m),
        vecDot (oneStepExpRemainderAt M n h x omega • p)
          (phi.toH1Function.grad x) ∂volume := by simpa using hwphi
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      simpa only [neg_smul] using (vecDot_neg_left
        (oneStepExpRemainderAt M n h x omega • p)
        (phi.toH1Function.grad x)).symm

/-- Canonical mean-zero Neumann solution driven by the same remainder. -/
def oneStepExpRemainderNeumannSolution {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    H1MeanZeroFunction (openCubeSet (originCube d m)) := by
  exact CubeCalderonZygmund.centeredCubeMeanZeroScalarDivergenceSolution
    m (sigma0 := 1) oneStepSigmaOnePos
      (fun x ↦ oneStepExpRemainderAt M n h x omega • p)
      (oneStepExpRemainderMemVectorL2 M n h p m omega)

theorem oneStepExpRemainderNeumannSolution_isWeakSolution
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d)
      (openCubeSet (originCube d m))
      (oneStepExpRemainderNeumannSolution M n h p m omega)
      (fun x ↦ -oneStepExpRemainderAt M n h x omega • p) := by
  have hw :=
    CubeCalderonZygmund.centeredCubeMeanZeroScalarDivergenceSolution_isWeakSolution
      m (sigma0 := 1) oneStepSigmaOnePos
        (fun x ↦ oneStepExpRemainderAt M n h x omega • p)
        (oneStepExpRemainderMemVectorL2 M n h p m omega)
  have ha : identityCoeffField d = (fun _ : Vec d ↦ (1 : Mat d)) := by
    funext x i j
    simp [identityCoeffField, scalarMatrix, Matrix.one_apply]
  rw [ha]
  simpa only [oneStepExpRemainderNeumannSolution, scalarMatrix,
    one_smul, neg_smul] using hw

private theorem eLpNorm_oneStepExpRemainder_smul_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hp : vecNormSq p = 1) :
    eLpNorm (fun x ↦ oneStepExpRemainderAt M n h x omega • p) 4
        (normalizedCubeMeasure (originCube d m)) ≤
      eLpNorm (fun x ↦ oneStepExpRemainderAt M n h x omega) 4
        (normalizedCubeMeasure (originCube d m)) := by
  have hscalar : AEStronglyMeasurable (fun x ↦ oneStepExpRemainderAt M n h x omega)
      (normalizedCubeMeasure (originCube d m)) := by
    simpa only [Function.comp_apply] using!
      ((measurable_oneStepExpRemainderAt_uncurry M n h).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂normalizedCubeMeasure (originCube d m),
      ‖oneStepExpRemainderAt M n h x omega • p‖ ≤ ‖oneStepExpRemainderAt M n h x omega‖ := by
    filter_upwards with x
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |oneStepExpRemainderAt M n h x omega| * ‖p‖ ≤
          |oneStepExpRemainderAt M n h x omega| * 1 :=
        mul_le_mul_of_nonneg_left
          (norm_le_one_of_vecNormSq_eq_one hp) (abs_nonneg _)
      _ = |oneStepExpRemainderAt M n h x omega| := mul_one _
  simpa only using! (eLpNorm_mono_ae (hscalar.smul_const p) hbound)

private theorem memLp_four_oneStepExpRemainder_smul {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hp : vecNormSq p = 1) :
    MemLp (fun x ↦ oneStepExpRemainderAt M n h x omega • p) 4
      (normalizedCubeMeasure (originCube d m)) := by
  let f : Vec d → Vec d := fun x ↦
    oneStepExpRemainderAt M n h x omega • p
  have hfmeas : AEStronglyMeasurable f
      (normalizedCubeMeasure (originCube d m)) :=
    (continuous_oneStepExpRemainder_smul M n h p omega).aestronglyMeasurable
  have hs := memLp_four_oneStepExpRemainderAt_spatial M n h m omega
  exact (eLpNorm_oneStepExpRemainder_smul_le M n h p m omega hp).trans_lt hs.eLpNorm_lt_top

/-! ## Exact nonlinear--linear splitting in the Hilbert carrier -/

/-- Bundled continuous residual multiplier. -/
def oneStepExpRemainderContinuousMap {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : C(Vec d, ℝ) where
  toFun := fun x ↦ oneStepExpRemainderAt M n h x omega
  continuous_toFun := by
    exact (((Real.continuous_exp.comp
      ((continuous_finset_sum _ fun k _ ↦
        (omega k).1.1.continuous).sub continuous_const)).sub
          continuous_const).sub
      (continuous_finset_sum _ fun k _ ↦ (omega k).1.1.continuous))

/-- Hilbert `L²` class of the residual vector forcing. -/
def oneStepExpRemainderForcingL2 {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    HilbertVectorL2 (openCubeSet Q) :=
  oneStepContinuousScalarForcingL2 Q p
    (oneStepExpRemainderContinuousMap M n h omega)

/-- The literal multiplier forcing is exactly the uncentered linear shell
plus the exponential residual. -/
theorem oneStepShellForcingL2_eq_linear_add_remainder {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    oneStepShellForcingL2 M n h p Q omega =
      oneStepLinearShellForcingL2 Q p n h omega +
        oneStepExpRemainderForcingL2 M n h p Q omega := by
  change toHilbertVectorL2OfVecField
      (memVectorL2_openCubeSet_of_continuous Q
        ((oneStepMultiplierContinuousMap M n h omega).continuous.smul
          (continuous_const : Continuous fun _ : Vec d ↦ p))) =
    toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepShellSumContinuousMap n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p))) +
      toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepExpRemainderContinuousMap M n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p)))
  apply MeasureTheory.Lp.ext
  filter_upwards
    [coeFn_toHilbertVectorL2OfVecField
      (memVectorL2_openCubeSet_of_continuous Q
        ((oneStepMultiplierContinuousMap M n h omega).continuous.smul
          (continuous_const : Continuous fun _ : Vec d ↦ p))),
     coeFn_toHilbertVectorL2OfVecField
      (memVectorL2_openCubeSet_of_continuous Q
        ((oneStepShellSumContinuousMap n h omega).continuous.smul
          (continuous_const : Continuous fun _ : Vec d ↦ p))),
     coeFn_toHilbertVectorL2OfVecField
      (memVectorL2_openCubeSet_of_continuous Q
        ((oneStepExpRemainderContinuousMap M n h omega).continuous.smul
          (continuous_const : Continuous fun _ : Vec d ↦ p))),
     Lp.coeFn_add
      (toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepShellSumContinuousMap n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p))))
      (toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepExpRemainderContinuousMap M n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p))))]
      with x hfull hlin hrem hadd
  rw [hfull, hadd]
  change hilbertifyVecField
      (fun x ↦ oneStepMultiplierContinuousMap M n h omega x • p) x =
    (toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepShellSumContinuousMap n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p))) :
      Vec d → HilbertVec d) x +
    (toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepExpRemainderContinuousMap M n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p))) :
      Vec d → HilbertVec d) x
  rw [hlin, hrem]
  change HilbertVec.ofVec
      (oneStepMultiplierContinuousMap M n h omega x • p) =
    HilbertVec.ofVec (oneStepShellSumContinuousMap n h omega x • p) +
      HilbertVec.ofVec (oneStepExpRemainderContinuousMap M n h omega x • p)
  rw [oneStepMultiplierContinuousMap_apply M n h omega x hh,
    oneStepMultiplierAt_eq_shell_add_remainder M n h x omega hh]
  apply HilbertVec.ext
  intro i
  simp [oneStepShellSumContinuousMap,
    oneStepExpRemainderContinuousMap]
  ring

private theorem h1Coercive_gradient_add {d : ℕ} {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (x y : H1CoerciveHilbertSpace (U := U)) :
    H1CoerciveHilbert.gradient (x + y) =
      H1CoerciveHilbert.gradient x + H1CoerciveHilbert.gradient y := by
  simpa only [← H1CoerciveHilbert.gradientCLM_apply] using
    (H1CoerciveHilbert.gradientCLM (U := U)).map_add x y

private theorem h1Coercive_gradient_neg {d : ℕ} {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (x : H1CoerciveHilbertSpace (U := U)) :
    H1CoerciveHilbert.gradient (-x) = -H1CoerciveHilbert.gradient x := by
  simpa only [← H1CoerciveHilbert.gradientCLM_apply] using
    (H1CoerciveHilbert.gradientCLM (U := U)).map_neg x

theorem oneStepExpRemainderDirichletSolution_gradient_eq {d : ℕ}
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    (oneStepExpRemainderDirichletSolution M n h p m omega).toH1Function.gradToHilbertVectorL2 =
      oneStepDirichletGradientOfForcingClass
        (PotentialSolenoidalL2Data.ofSubmoduleClosures
          (openCubeSet (originCube d m)))
        (openCubeSet_nonempty_internal (originCube d m))
        (isEllipticFieldOn_identityCoeffField
          (measurableSet_openCubeSet (originCube d m)))
        (-oneStepExpRemainderForcingL2 M n h p (originCube d m) omega) := by
  let Q := originCube d m
  let f : Vec d → Vec d := fun x ↦
    oneStepExpRemainderAt M n h x omega • p
  let hf : MemVectorL2 (openCubeSet Q) f :=
    oneStepExpRemainderMemVectorL2 M n h p m omega
  let hEll := isEllipticFieldOn_identityCoeffField
    (measurableSet_openCubeSet Q)
  have hweak := oneStepExpRemainderDirichletSolution_isWeakSolution
    M n h p m omega
  have hweak' : IsZeroTraceDirichletRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q)
      (oneStepExpRemainderDirichletSolution M n h p m omega) (-f) := by
    simpa only [Q, f, Pi.neg_apply, neg_smul] using! hweak
  calc
    _ = oneStepDirichletGradientOfForcingClass
        (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q))
        (openCubeSet_nonempty_internal Q) hEll
        (toHilbertVectorL2OfVecField hf.neg) := by
      exact gradToHilbertVectorL2_eq_oneStepDirichletGradientOfForcingClass
        hf.neg
        (PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
          (isOpenBoundedConvexDomain_openCubeSet Q))
        (openCubeSet_nonempty_internal Q) hEll hweak'
    _ = _ := by
      apply congrArg (oneStepDirichletGradientOfForcingClass
        (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q))
        (openCubeSet_nonempty_internal Q) hEll)
      rw [toHilbertVectorL2OfVecField_neg_oneStep hf]
      congr 1

theorem oneStepExpRemainderNeumannSolution_gradient_eq {d : ℕ}
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    (oneStepExpRemainderNeumannSolution M n h p m omega).gradToHilbertVectorL2 =
      oneStepNeumannGradientOfForcingClass
        (translatedCubeMeanZeroH1CoerciveEstimate (originCube d m))
        (openCubeSet_nonempty_internal (originCube d m))
        (isEllipticFieldOn_identityCoeffField
          (measurableSet_openCubeSet (originCube d m)))
        (-oneStepExpRemainderForcingL2 M n h p (originCube d m) omega) := by
  let Q := originCube d m
  let f : Vec d → Vec d := fun x ↦
    oneStepExpRemainderAt M n h x omega • p
  let hf : MemVectorL2 (openCubeSet Q) f :=
    oneStepExpRemainderMemVectorL2 M n h p m omega
  let hEll := isEllipticFieldOn_identityCoeffField
    (measurableSet_openCubeSet Q)
  have hweak := oneStepExpRemainderNeumannSolution_isWeakSolution
    M n h p m omega
  have hweak' : IsMeanZeroNeumannRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q)
      (oneStepExpRemainderNeumannSolution M n h p m omega) (-f) := by
    simpa only [Q, f, Pi.neg_apply, neg_smul] using! hweak
  calc
    _ = oneStepNeumannGradientOfForcingClass
        (translatedCubeMeanZeroH1CoerciveEstimate Q)
        (openCubeSet_nonempty_internal Q) hEll
        (toHilbertVectorL2OfVecField hf.neg) := by
      exact gradToHilbertVectorL2_eq_oneStepNeumannGradientOfForcingClass
        hf.neg (translatedCubeMeanZeroH1CoerciveEstimate Q)
        (openCubeSet_nonempty_internal Q) hEll hweak'
    _ = _ := by
      apply congrArg (oneStepNeumannGradientOfForcingClass
        (translatedCubeMeanZeroH1CoerciveEstimate Q)
        (openCubeSet_nonempty_internal Q) hEll)
      rw [toHilbertVectorL2OfVecField_neg_oneStep hf]
      congr 1

/-- Exact Dirichlet split `grad w = -grad v₀ + grad wbar`. -/
theorem oneStepOriginDirichletGradientL2_eq_linear_add_remainder {d : ℕ}
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    oneStepOriginDirichletGradientL2 M n h p m omega =
      -oneStepLinearDirichletGradient (originCube d m) p n h omega +
        (oneStepExpRemainderDirichletSolution M n h p m omega).toH1Function.gradToHilbertVectorL2 := by
  let Q := originCube d m
  rw [oneStepOriginDirichletGradientL2,
    oneStepExpRemainderDirichletSolution_gradient_eq]
  have hforce := oneStepShellForcingL2_eq_linear_add_remainder
    M n h p Q omega hh
  rw [hforce]
  simp [oneStepLinearDirichletGradient,
    oneStepDirichletGradientOfForcingClass,
    oneStepDirichletForcingRieszOfClass,
    Homogenization.PotentialZeroTraceHilbert.forcingRieszMap]
  abel

/-- Exact Neumann split in the same sign convention. -/
theorem oneStepOriginNeumannGradientL2_eq_linear_add_remainder {d : ℕ}
    [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    oneStepOriginNeumannGradientL2 M n h p m omega =
      -oneStepLinearNeumannGradient (originCube d m) p n h omega +
        (oneStepExpRemainderNeumannSolution M n h p m omega).gradToHilbertVectorL2 := by
  let Q := originCube d m
  rw [oneStepOriginNeumannGradientL2,
    oneStepExpRemainderNeumannSolution_gradient_eq]
  have hforce := oneStepShellForcingL2_eq_linear_add_remainder
    M n h p Q omega hh
  rw [hforce]
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hRieszAdd (G H : HilbertVectorL2 (openCubeSet Q)) :
      oneStepNeumannForcingRieszOfClass (G + H) =
        oneStepNeumannForcingRieszOfClass G + oneStepNeumannForcingRieszOfClass H := by
    unfold oneStepNeumannForcingRieszOfClass
    rw [map_add, ContinuousLinearMap.add_comp]
    unfold Homogenization.H1CoerciveHilbert.forcingRieszMap
    exact map_add _ _ _
  have hRieszNeg (G : HilbertVectorL2 (openCubeSet Q)) :
      oneStepNeumannForcingRieszOfClass (-G) = -oneStepNeumannForcingRieszOfClass G := by
    unfold oneStepNeumannForcingRieszOfClass
    rw [map_neg, ContinuousLinearMap.neg_comp]
    unfold Homogenization.H1CoerciveHilbert.forcingRieszMap
    exact map_neg _ _
  simp only [oneStepLinearNeumannGradient, oneStepNeumannGradientOfForcingClass,
    hRieszAdd, hRieszNeg, map_add, map_neg,
    ← Homogenization.H1CoerciveHilbert.gradientCLM_apply]
  abel

/-- Dirichlet `L⁴` control of the nonlinear-minus-linear solution. -/
theorem exists_oneStepExpRemainderDirichlet_gradient_four_cz
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (p : Vec d) (m : ℤ),
        vecNormSq p = 1 →
        MemLp
            (hilbertifyVecField
              (oneStepExpRemainderDirichletSolution
                M n h p m omega).toH1Function.grad)
            4 (normalizedCubeMeasure (originCube d m)) ∧
          eLpNorm
              (hilbertifyVecField
                (oneStepExpRemainderDirichletSolution
                  M n h p m omega).toH1Function.grad)
              4 (normalizedCubeMeasure (originCube d m)) ≤
            C * eLpNorm
              (fun x ↦ oneStepExpRemainderAt M n h x omega) 4
              (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨C, hCpos, hCZ⟩ :=
    CubeCalderonZygmund.exists_cubeDirichletDivergence_cz
      d oneStepFourExponent
  let C4 : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ) * C)
  refine ⟨C4, ENNReal.ofReal_lt_top, ?_⟩
  intro M n h omega p m hp
  let Q := originCube d m
  let f : Vec d → Vec d := fun x ↦
    oneStepExpRemainderAt M n h x omega • p
  let u := oneStepExpRemainderDirichletSolution M n h p m omega
  have hf : MemLp f 4 (normalizedCubeMeasure Q) := by
    simpa only [f, Q] using
      memLp_four_oneStepExpRemainder_smul M n h p m omega hp
  have hu : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d ↦ (1 : Mat d)) (openCubeSet Q) u (fun x ↦ -f x) := by
    have ha : identityCoeffField d = (fun _ : Vec d ↦ (1 : Mat d)) := by
      funext x i j
      simp [identityCoeffField, scalarMatrix, Matrix.one_apply]
    rw [← ha]
    simpa only [Q, f, u, neg_smul] using
      oneStepExpRemainderDirichletSolution_isWeakSolution M n h p m omega
  obtain ⟨hgradRaw, hgradBound⟩ := hCZ Q f hf u hu
  have hgradHilbert : MemLp (hilbertifyVecField u.toH1Function.grad) 4
      (normalizedCubeMeasure Q) := by
    simpa only [hilbertifyVecField, Function.comp_apply,
      HilbertVec.ofVecL_apply] using!
      (HilbertVec.ofVecL d).comp_memLp' hgradRaw
  refine ⟨by simpa only [Q, u] using hgradHilbert, ?_⟩
  have hrawENN : eLpNorm u.toH1Function.grad 4 (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal C * eLpNorm f 4 (normalizedCubeMeasure Q) := by
    apply (ENNReal.toReal_le_toReal hgradRaw.eLpNorm_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top)).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCpos.le]
    simpa only [cubeLpNorm, Q, f, u, oneStepFourExponent_exponent] using hgradBound
  calc
    eLpNorm (hilbertifyVecField u.toH1Function.grad) 4
        (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal (d : ℝ) *
        eLpNorm u.toH1Function.grad 4 (normalizedCubeMeasure Q) :=
      eLpNorm_hilbertifyVecField_le_dimension_mul_of_aestronglyMeasurable u.toH1Function.grad
        (memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q
          u.toH1Function.grad_memVectorL2).aestronglyMeasurable
    _ ≤ ENNReal.ofReal (d : ℝ) *
        (ENNReal.ofReal C * eLpNorm f 4 (normalizedCubeMeasure Q)) := by
      gcongr
    _ = C4 * eLpNorm f 4 (normalizedCubeMeasure Q) := by
      dsimp only [C4]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg d)]
      ac_rfl
    _ ≤ C4 * eLpNorm
        (fun x ↦ oneStepExpRemainderAt M n h x omega) 4
        (normalizedCubeMeasure Q) := by
      gcongr
      exact eLpNorm_oneStepExpRemainder_smul_le M n h p m omega hp

/-- Neumann `L⁴` control of the nonlinear-minus-linear solution. -/
theorem exists_oneStepExpRemainderNeumann_gradient_four_cz
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (p : Vec d) (m : ℤ),
        vecNormSq p = 1 →
        MemLp
            (hilbertifyVecField
              (oneStepExpRemainderNeumannSolution
                M n h p m omega).toH1Function.grad)
            4 (normalizedCubeMeasure (originCube d m)) ∧
          eLpNorm
              (hilbertifyVecField
                (oneStepExpRemainderNeumannSolution
                  M n h p m omega).toH1Function.grad)
              4 (normalizedCubeMeasure (originCube d m)) ≤
            C * eLpNorm
              (fun x ↦ oneStepExpRemainderAt M n h x omega) 4
              (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨C, hCpos, hCZ⟩ :=
    CubeCalderonZygmund.exists_cubeH1MeanZeroNeumannDivergence_cz
      d oneStepFourExponent
  let C4 : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ) * C)
  refine ⟨C4, ENNReal.ofReal_lt_top, ?_⟩
  intro M n h omega p m hp
  let Q := originCube d m
  let f : Vec d → Vec d := fun x ↦
    oneStepExpRemainderAt M n h x omega • p
  let u := oneStepExpRemainderNeumannSolution M n h p m omega
  have hf : MemLp f 4 (normalizedCubeMeasure Q) := by
    simpa only [f, Q] using
      memLp_four_oneStepExpRemainder_smul M n h p m omega hp
  have hu : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ (1 : Mat d)) (openCubeSet Q) u (fun x ↦ -f x) := by
    have ha : identityCoeffField d = (fun _ : Vec d ↦ (1 : Mat d)) := by
      funext x i j
      simp [identityCoeffField, scalarMatrix, Matrix.one_apply]
    rw [← ha]
    simpa only [Q, f, u, neg_smul] using
      oneStepExpRemainderNeumannSolution_isWeakSolution M n h p m omega
  obtain ⟨hgradRaw, hgradBound⟩ := hCZ Q f hf u hu
  have hgradHilbert : MemLp (hilbertifyVecField u.toH1Function.grad) 4
      (normalizedCubeMeasure Q) := by
    simpa only [hilbertifyVecField, Function.comp_apply,
      HilbertVec.ofVecL_apply] using!
      (HilbertVec.ofVecL d).comp_memLp' hgradRaw
  refine ⟨by simpa only [Q, u] using hgradHilbert, ?_⟩
  have hrawENN : eLpNorm u.toH1Function.grad 4 (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal C * eLpNorm f 4 (normalizedCubeMeasure Q) := by
    apply (ENNReal.toReal_le_toReal hgradRaw.eLpNorm_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top)).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCpos.le]
    simpa only [cubeLpNorm, Q, f, u, oneStepFourExponent_exponent] using hgradBound
  calc
    eLpNorm (hilbertifyVecField u.toH1Function.grad) 4
        (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal (d : ℝ) *
        eLpNorm u.toH1Function.grad 4 (normalizedCubeMeasure Q) :=
      eLpNorm_hilbertifyVecField_le_dimension_mul_of_aestronglyMeasurable u.toH1Function.grad
        (memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q
          u.toH1Function.grad_memVectorL2).aestronglyMeasurable
    _ ≤ ENNReal.ofReal (d : ℝ) *
        (ENNReal.ofReal C * eLpNorm f 4 (normalizedCubeMeasure Q)) := by
      gcongr
    _ = C4 * eLpNorm f 4 (normalizedCubeMeasure Q) := by
      dsimp only [C4]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg d)]
      ac_rfl
    _ ≤ C4 * eLpNorm
        (fun x ↦ oneStepExpRemainderAt M n h x omega) 4
        (normalizedCubeMeasure Q) := by
      gcongr
      exact eLpNorm_oneStepExpRemainder_smul_le M n h p m omega hp

/-! ## Mixed spatial--random solution moments -/

/-- The residual Dirichlet solution has the manuscript's
`O(delta² h)` mixed `L⁴` gradient scale. -/
theorem exists_lintegral_oneStepExpRemainderDirichlet_gradient_four_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (_hh : 0 < h),
        vecNormSq p = 1 → (h : ℝ) ≤ M.delta⁻¹ →
        ∫⁻ omega,
            (eLpNorm
              (hilbertifyVecField
                (oneStepExpRemainderDirichletSolution
                  M n h p m omega).toH1Function.grad)
              4 (normalizedCubeMeasure (originCube d m))) ^ (4 : ℝ)
            ∂M.P.toMeasure ≤
          C * (oneStepExpRemainderConst *
            ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ) := by
  obtain ⟨C, hCtop, hCZ⟩ :=
    exists_oneStepExpRemainderDirichlet_gradient_four_cz d
  refine ⟨C ^ (4 : ℝ),
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hCtop.ne, ?_⟩
  intro M n h p m hh hp hscale
  let nu := normalizedCubeMeasure (originCube d m)
  let R : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Vec d → ℝ := fun omega x ↦
    oneStepExpRemainderAt M n h x omega
  have hRmeas : Measurable (Function.uncurry R) := by
    simpa only [R] using! measurable_oneStepExpRemainderAt_uncurry M n h
  have hnormMeas : Measurable fun omega ↦ eLpNorm (R omega) 4 nu :=
    measurable_eLpNorm_four_prod_right nu R hRmeas
  have hRmoment :
      ∫⁻ omega, (eLpNorm (R omega) 4 nu) ^ (4 : ℝ) ∂M.P.toMeasure ≤
        (oneStepExpRemainderConst *
          ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ) := by
    calc
      _ = ∫⁻ omega, ∫⁻ x, ‖R omega x‖ₑ ^ (4 : ℝ)
          ∂nu ∂M.P.toMeasure := by
        apply lintegral_congr
        intro omega
        have hspatial : AEStronglyMeasurable (R omega) nu := by
          simpa only [Function.uncurry_apply_pair, Function.comp_apply] using!
            (hRmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hspatial]
        norm_num only [ENNReal.toReal_ofNat]
        have hquarter : (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num
        rw [hquarter, ENNReal.rpow_inv_rpow (by norm_num : (4 : ℝ) ≠ 0)]
      _ ≤ _ := by
        simpa only [R, nu, ENNReal.rpow_natCast] using
          lintegral_lintegral_oneStepExpRemainder_four_le M n h m hh hscale
  calc
    _ ≤ ∫⁻ omega, (C * eLpNorm (R omega) 4 nu) ^ (4 : ℝ)
        ∂M.P.toMeasure := by
      apply lintegral_mono
      intro omega
      exact ENNReal.rpow_le_rpow (hCZ M n h omega p m hp).2 (by norm_num)
    _ = C ^ (4 : ℝ) *
        ∫⁻ omega, (eLpNorm (R omega) 4 nu) ^ (4 : ℝ)
          ∂M.P.toMeasure := by
      rw [← lintegral_const_mul'' _
        (hnormMeas.pow_const (4 : ℝ)).aemeasurable]
      apply lintegral_congr
      intro omega
      exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ _ := by gcongr

/-- Neumann counterpart of the mixed residual-solution estimate. -/
theorem exists_lintegral_oneStepExpRemainderNeumann_gradient_four_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (_hh : 0 < h),
        vecNormSq p = 1 → (h : ℝ) ≤ M.delta⁻¹ →
        ∫⁻ omega,
            (eLpNorm
              (hilbertifyVecField
                (oneStepExpRemainderNeumannSolution
                  M n h p m omega).toH1Function.grad)
              4 (normalizedCubeMeasure (originCube d m))) ^ (4 : ℝ)
            ∂M.P.toMeasure ≤
          C * (oneStepExpRemainderConst *
            ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ) := by
  obtain ⟨C, hCtop, hCZ⟩ :=
    exists_oneStepExpRemainderNeumann_gradient_four_cz d
  refine ⟨C ^ (4 : ℝ),
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hCtop.ne, ?_⟩
  intro M n h p m hh hp hscale
  let nu := normalizedCubeMeasure (originCube d m)
  let R : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Vec d → ℝ := fun omega x ↦
    oneStepExpRemainderAt M n h x omega
  have hRmeas : Measurable (Function.uncurry R) := by
    simpa only [R] using! measurable_oneStepExpRemainderAt_uncurry M n h
  have hnormMeas : Measurable fun omega ↦ eLpNorm (R omega) 4 nu :=
    measurable_eLpNorm_four_prod_right nu R hRmeas
  have hRmoment :
      ∫⁻ omega, (eLpNorm (R omega) 4 nu) ^ (4 : ℝ) ∂M.P.toMeasure ≤
        (oneStepExpRemainderConst *
          ENNReal.ofReal (M.delta ^ 2 * (h : ℝ))) ^ (4 : ℝ) := by
    calc
      _ = ∫⁻ omega, ∫⁻ x, ‖R omega x‖ₑ ^ (4 : ℝ)
          ∂nu ∂M.P.toMeasure := by
        apply lintegral_congr
        intro omega
        have hspatial : AEStronglyMeasurable (R omega) nu := by
          simpa only [Function.uncurry_apply_pair, Function.comp_apply] using!
            (hRmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hspatial]
        norm_num only [ENNReal.toReal_ofNat]
        have hquarter : (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num
        rw [hquarter, ENNReal.rpow_inv_rpow (by norm_num : (4 : ℝ) ≠ 0)]
      _ ≤ _ := by
        simpa only [R, nu, ENNReal.rpow_natCast] using
          lintegral_lintegral_oneStepExpRemainder_four_le M n h m hh hscale
  calc
    _ ≤ ∫⁻ omega, (C * eLpNorm (R omega) 4 nu) ^ (4 : ℝ)
        ∂M.P.toMeasure := by
      apply lintegral_mono
      intro omega
      exact ENNReal.rpow_le_rpow (hCZ M n h omega p m hp).2 (by norm_num)
    _ = C ^ (4 : ℝ) *
        ∫⁻ omega, (eLpNorm (R omega) 4 nu) ^ (4 : ℝ)
          ∂M.P.toMeasure := by
      rw [← lintegral_const_mul'' _
        (hnormMeas.pow_const (4 : ℝ)).aemeasurable]
      apply lintegral_congr
      intro omega
      exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ _ := by gcongr

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
