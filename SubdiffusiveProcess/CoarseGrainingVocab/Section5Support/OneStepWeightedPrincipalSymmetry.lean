module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCorrectorEnergyBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMeasurableForcing
public import SubdiffusiveProcess.CoarseGrainingVocab.ReciprocalLowerSupport

@[expose] public section




open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- Simultaneous potential negation reverses every finite shell block. -/
theorem cutoffShellSum_negatePotentialSequence {d : ℕ}
    (m : ℕ) (n : ℤ) (x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    cutoffShellSum m n x (negatePotentialSequence omega) =
      -cutoffShellSum m n x omega := by
  unfold cutoffShellSum negatePotentialSequence
  simp only [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.negate_apply,
    Finset.sum_neg_distrib]

/-- A measurable scalar observable which is odd under simultaneous potential
negation has zero expectation. -/
theorem integral_eq_zero_of_negatePotentialSequence_odd {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (f : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ)
    (hf : AEStronglyMeasurable f M.P.toMeasure)
    (hodd : ∀ omega, f (negatePotentialSequence omega) = -f omega) :
    ∫ omega, f omega ∂M.P.toMeasure = 0 := by
  have hsame :
      ∫ omega, f omega ∂M.P.toMeasure =
        ∫ omega, f (negatePotentialSequence omega) ∂M.P.toMeasure := by
    exact (Homogenization.integral_comp_eq_of_map_eq
      measurable_negatePotentialSequence (potentialSequenceLaw_negation M)
      f hf).symm
  have hneg :
      ∫ omega, f (negatePotentialSequence omega) ∂M.P.toMeasure =
        -∫ omega, f omega ∂M.P.toMeasure := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall hodd)
  linarith

/-- The uncentered one-step shell block as a continuous spatial field. -/
def oneStepShellSumContinuousMap {d : ℕ}
    (n h : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : C(Vec d, ℝ) where
  toFun := fun x ↦ cutoffShellSum (n + h) (n : ℤ) x omega
  continuous_toFun := by
    exact continuous_finset_sum _ fun k _ ↦ (omega k).1.1.continuous

theorem oneStepShellSumContinuousMap_negate {d : ℕ}
    (n h : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    oneStepShellSumContinuousMap n h (negatePotentialSequence omega) =
      -oneStepShellSumContinuousMap n h omega := by
  ext x
  exact cutoffShellSum_negatePotentialSequence (n + h) (n : ℤ) x omega

/-- The uncentered shell block is jointly measurable in the sample and
spatial variables.  This is the weak-probe substitute for a measurable-space
instance on the global compact-open continuous-map carrier. -/
theorem measurable_cutoffShellSum_uncurry {d : ℕ} (n h : ℕ) :
    Measurable fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d ↦
      cutoffShellSum (n + h) (n : ℤ) q.2 q.1 := by
  have hEvalRaw : Measurable
      (Function.uncurry fun x : Vec d ↦
        fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d ↦ g x) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun g ↦ g.1.1.continuous)
      (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x)
  have hEval : Measurable fun q :
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField d × Vec d ↦ q.1 q.2 := by
    simpa only [Function.comp_apply] using! hEvalRaw.comp measurable_swap
  unfold cutoffShellSum
  exact Finset.measurable_sum _ fun k _ ↦
    hEval.comp
      (((SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k).comp
        measurable_fst).prodMk measurable_snd)

/-- Negation commutes with the continuous-scalar forcing realization. -/
theorem oneStepContinuousScalarForcingL2_neg {d : ℕ}
    (Q : TriadicCube d) (p : Vec d) (f : C(Vec d, ℝ)) :
    oneStepContinuousScalarForcingL2 Q p (-f) =
      -oneStepContinuousScalarForcingL2 Q p f := by
  unfold oneStepContinuousScalarForcingL2
  apply MeasureTheory.Lp.ext
  filter_upwards
    [coeFn_toHilbertVectorL2OfVecField
      (memVectorL2_openCubeSet_of_continuous Q
        ((-f).continuous.smul (continuous_const : Continuous fun _ : Vec d ↦ p))),
     coeFn_toHilbertVectorL2OfVecField
      (memVectorL2_openCubeSet_of_continuous Q
        (f.continuous.smul (continuous_const : Continuous fun _ : Vec d ↦ p))),
     Lp.coeFn_neg (toHilbertVectorL2OfVecField
      (memVectorL2_openCubeSet_of_continuous Q
        (f.continuous.smul (continuous_const : Continuous fun _ : Vec d ↦ p))))]
      with x hxneg hx hminus
  rw [hxneg, hminus]
  calc
    hilbertifyVecField (fun x ↦ (-f) x • p) x =
        -hilbertifyVecField (fun x ↦ f x • p) x := by
          apply HilbertVec.ext
          intro i
          simp [hilbertifyVecField]
    _ = -((toHilbertVectorL2OfVecField
      (memVectorL2_openCubeSet_of_continuous Q
        (f.continuous.smul (continuous_const : Continuous fun _ : Vec d ↦ p))) :
          Vec d → HilbertVec d) x) := congrArg Neg.neg hx.symm

/-- `L²` forcing class for the uncentered, linear shell block. -/
def oneStepLinearShellForcingL2 {d : ℕ}
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    HilbertVectorL2 (openCubeSet Q) :=
  oneStepContinuousScalarForcingL2 Q p
    (oneStepShellSumContinuousMap n h omega)

/-- Every fixed Hilbert `L²` probe of the linear shell forcing is measurable.
The proof is the same Fubini interface as for the nonlinear shell forcing in
`OneStepMeasurableForcing`. -/
theorem measurable_inner_oneStepLinearShellForcingL2 {d : ℕ}
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ)
    (Y : HilbertVectorL2 (openCubeSet Q)) :
    Measurable fun omega ↦
      inner ℝ (oneStepLinearShellForcingL2 Q p n h omega) Y := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hY : Measurable fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d ↦
      (Y : Vec d → HilbertVec d) q.2 :=
    (MeasureTheory.Lp.stronglyMeasurable Y).measurable.comp measurable_snd
  have hint : Measurable fun q : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d ↦
      inner ℝ
        (cutoffShellSum (n + h) (n : ℤ) q.2 q.1 • HilbertVec.ofVec p)
        ((Y : Vec d → HilbertVec d) q.2) :=
    ((measurable_cutoffShellSum_uncurry n h).smul_const
      (HilbertVec.ofVec p)).inner hY
  have hparam : Measurable fun omega ↦
      ∫ x, inner ℝ
        (cutoffShellSum (n + h) (n : ℤ) x omega • HilbertVec.ofVec p)
        ((Y : Vec d → HilbertVec d) x)
        ∂(volumeMeasureOn (openCubeSet Q)) :=
    hint.stronglyMeasurable.integral_prod_right'.measurable
  have heq : (fun omega ↦
      inner ℝ (oneStepLinearShellForcingL2 Q p n h omega) Y) =
      fun omega ↦
        ∫ x, inner ℝ
          (cutoffShellSum (n + h) (n : ℤ) x omega • HilbertVec.ofVec p)
          ((Y : Vec d → HilbertVec d) x)
          ∂(volumeMeasureOn (openCubeSet Q)) := by
    funext omega
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards
      [coeFn_toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepShellSumContinuousMap n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p)))]
      with x hx
    change inner ℝ
      ((toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepShellSumContinuousMap n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p))) :
          Vec d → HilbertVec d) x) ((Y : Vec d → HilbertVec d) x) = _
    rw [hx]
    rfl
  rw [heq]
  exact hparam

/-- The linear shell forcing is a Borel Hilbert-`L²` random variable. -/
theorem measurable_oneStepLinearShellForcingL2 {d : ℕ}
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) :
    Measurable (oneStepLinearShellForcingL2 Q p n h) := by
  letI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  exact measurable_of_forall_real_inner_right fun Y ↦
    measurable_inner_oneStepLinearShellForcingL2 Q p n h Y

/-- Fixed-cube Dirichlet gradient for the uncentered, linear shell forcing. -/
def oneStepLinearDirichletGradient {d : ℕ}
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    HilbertVectorL2 (openCubeSet Q) :=
  oneStepDirichletGradientOfForcingClass
    (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q))
    (openCubeSet_nonempty_internal Q)
    (isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q))
    (oneStepLinearShellForcingL2 Q p n h omega)

/-- The linearized Dirichlet gradient is a Borel `L²`-valued random
variable. -/
theorem measurable_oneStepLinearDirichletGradient {d : ℕ}
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) :
    Measurable (oneStepLinearDirichletGradient Q p n h) := by
  exact (continuous_oneStepDirichletGradientOfForcingClass
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q))
      (openCubeSet_nonempty_internal Q)
      (isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)))
    |>.measurable.comp (measurable_oneStepLinearShellForcingL2 Q p n h)

/-- The linearized Dirichlet gradient is odd under shell sign reversal. -/
theorem oneStepLinearDirichletGradient_negate {d : ℕ}
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    oneStepLinearDirichletGradient Q p n h
        (negatePotentialSequence omega) =
      -oneStepLinearDirichletGradient Q p n h omega := by
  rw [oneStepLinearDirichletGradient, oneStepLinearShellForcingL2,
    oneStepShellSumContinuousMap_negate,
    oneStepContinuousScalarForcingL2_neg]
  simp [oneStepLinearDirichletGradient, oneStepLinearShellForcingL2,
    oneStepDirichletGradientOfForcingClass,
    oneStepDirichletForcingRieszOfClass,
    Homogenization.PotentialZeroTraceHilbert.forcingRieszMap]

/-- Fixed-cube Neumann gradient for the same linear shell forcing. -/
def oneStepLinearNeumannGradient {d : ℕ}
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    HilbertVectorL2 (openCubeSet Q) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact oneStepNeumannGradientOfForcingClass
    (translatedCubeMeanZeroH1CoerciveEstimate Q)
    (openCubeSet_nonempty_internal Q)
    (isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q))
    (oneStepLinearShellForcingL2 Q p n h omega)

/-- The linearized Neumann gradient is a Borel `L²`-valued random
variable. -/
theorem measurable_oneStepLinearNeumannGradient {d : ℕ}
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) :
    Measurable (oneStepLinearNeumannGradient Q p n h) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact (continuous_oneStepNeumannGradientOfForcingClass
      (translatedCubeMeanZeroH1CoerciveEstimate Q)
      (openCubeSet_nonempty_internal Q)
      (isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)))
    |>.measurable.comp (measurable_oneStepLinearShellForcingL2 Q p n h)

/-- The linearized Neumann gradient is odd under shell sign reversal. -/
theorem oneStepLinearNeumannGradient_negate {d : ℕ}
    (Q : TriadicCube d) (p : Vec d) (n h : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    oneStepLinearNeumannGradient Q p n h
        (negatePotentialSequence omega) =
      -oneStepLinearNeumannGradient Q p n h omega := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  rw [oneStepLinearNeumannGradient, oneStepLinearShellForcingL2,
    oneStepShellSumContinuousMap_negate,
    oneStepContinuousScalarForcingL2_neg]
  have hRieszNeg (G : HilbertVectorL2 (openCubeSet Q)) :
      oneStepNeumannForcingRieszOfClass (-G) =
        -oneStepNeumannForcingRieszOfClass G := by
    unfold oneStepNeumannForcingRieszOfClass
    rw [map_neg, ContinuousLinearMap.neg_comp]
    unfold Homogenization.H1CoerciveHilbert.forcingRieszMap
    exact map_neg _ _
  simp only [oneStepLinearNeumannGradient, oneStepLinearShellForcingL2,
    oneStepNeumannGradientOfForcingClass, hRieszNeg, map_neg,
    ← Homogenization.H1CoerciveHilbert.gradientCLM_apply]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
