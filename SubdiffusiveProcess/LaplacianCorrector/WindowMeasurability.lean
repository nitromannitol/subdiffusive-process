import SubdiffusiveProcess.LaplacianCorrector.ShiftLaw

/-! # Measurable forcing and solution energies for arbitrary layer windows -/

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.LaplacianCorrector

/-- A layer-window multiplier as a continuous spatial function. -/
def windowContinuousMap {d : ℕ} (M : Model d) (a h : ℕ) (omega : Sample d) :
    C(Vec d, ℝ) where
  toFun := windowMultiplier M a h omega
  continuous_toFun := by
    exact (Real.continuous_exp.comp
      (continuous_finset_sum _ fun k _ =>
        (omega k).1.1.continuous.sub continuous_const)).sub continuous_const

theorem measurable_windowMultiplier_uncurry {d : ℕ} (M : Model d) (a h : ℕ) :
    Measurable fun q : Sample d × Vec d => windowMultiplier M a h q.1 q.2 := by
  have hEvalRaw : Measurable
      (Function.uncurry fun x : Vec d => fun g : Field d => g x) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun g => g.1.1.continuous)
      (fun x => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x)
  have hEval : Measurable fun q : Field d × Vec d => q.1 q.2 :=
    hEvalRaw.comp measurable_swap
  exact (Finset.measurable_sum _ fun k _ =>
    (hEval.comp (((SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k).comp
      measurable_fst).prodMk measurable_snd)).sub_const _).exp.sub_const _

/-- Hilbert `L²` forcing of an arbitrary layer window. -/
def windowForcingL2 {d : ℕ} (M : Model d) (a h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : Sample d) : HilbertVectorL2 (openCubeSet Q) :=
  oneStepContinuousScalarForcingL2 Q p (windowContinuousMap M a h omega)

theorem measurable_windowForcingL2 {d : ℕ} (M : Model d) (a h : ℕ)
    (p : Vec d) (Q : TriadicCube d) : Measurable (windowForcingL2 M a h p Q) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  letI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  apply measurable_of_forall_real_inner_right
  intro Y
  have hY : Measurable fun q : Sample d × Vec d => (Y : Vec d → HilbertVec d) q.2 :=
    (Lp.stronglyMeasurable Y).measurable.comp measurable_snd
  have hint : Measurable fun q : Sample d × Vec d =>
      inner ℝ (windowMultiplier M a h q.1 q.2 • HilbertVec.ofVec p)
        ((Y : Vec d → HilbertVec d) q.2) :=
    ((measurable_windowMultiplier_uncurry M a h).smul_const (HilbertVec.ofVec p)).inner hY
  have hparam : Measurable fun omega => ∫ x, inner ℝ
      (windowMultiplier M a h omega x • HilbertVec.ofVec p) (Y x)
      ∂volumeMeasureOn (openCubeSet Q) :=
    hint.stronglyMeasurable.integral_prod_right'.measurable
  have heq : (fun omega => inner ℝ (windowForcingL2 M a h p Q omega) Y) =
      fun omega => ∫ x, inner ℝ
        (windowMultiplier M a h omega x • HilbertVec.ofVec p) (Y x)
        ∂volumeMeasureOn (openCubeSet Q) := by
    funext omega
    rw [L2.inner_def]
    apply integral_congr_ae
    let hg := memVectorL2_openCubeSet_of_continuous Q
      ((windowContinuousMap M a h omega).continuous.smul
        (continuous_const : Continuous fun _ : Vec d => p))
    filter_upwards [coeFn_toHilbertVectorL2OfVecField hg] with x hx
    change inner ℝ (((toHilbertVectorL2OfVecField hg) : Vec d → HilbertVec d) x) (Y x) = _
    rw [hx]
    rfl
  rw [heq]
  exact hparam

theorem measurable_windowDirichletGradL2 {d : ℕ} [NeZero d] (M : Model d) (a h : ℕ)
    (p : Vec d) (Q : TriadicCube d)
    (u : Sample d → H10Function (openCubeSet Q))
    (hu : ∀ omega, IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d)
      (openCubeSet Q) (u omega) (fun x => -windowMultiplier M a h omega x • p)) :
    Measurable fun omega => (u omega).toH1Function.gradToHilbertVectorL2 := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q) (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  let D := oneStepDirichletGradientOfForcingClass
    (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q))
    (openCubeSet_nonempty_internal Q) hEll
  have heq : (fun omega => (u omega).toH1Function.gradToHilbertVectorL2) =
      D ∘ fun omega => -windowForcingL2 M a h p Q omega := by
    funext omega
    let hg := memVectorL2_openCubeSet_of_continuous Q
      ((windowContinuousMap M a h omega).continuous.smul
        (continuous_const : Continuous fun _ : Vec d => p))
    have hweak : IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d)
        (openCubeSet Q) (u omega) (fun x => -(windowMultiplier M a h omega x • p)) := by
      simpa only [neg_smul] using hu omega
    have hgrad := gradToHilbertVectorL2_eq_oneStepDirichletGradientOfForcingClass
      hg.neg
      (PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
        (isOpenBoundedConvexDomain_openCubeSet Q))
      (openCubeSet_nonempty_internal Q) hEll hweak
    rw [toHilbertVectorL2OfVecField_neg_oneStep hg] at hgrad
    exact hgrad
  rw [heq]
  exact (continuous_oneStepDirichletGradientOfForcingClass _ _ _).measurable.comp
    (measurable_windowForcingL2 M a h p Q).neg

theorem measurable_windowNeumannGradL2 {d : ℕ} (M : Model d) (a h : ℕ)
    (p : Vec d) (Q : TriadicCube d)
    (u : Sample d → H1MeanZeroFunction (openCubeSet Q))
    (hu : ∀ omega, IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d)
      (openCubeSet Q) (u omega) (fun x => windowMultiplier M a h omega x • p)) :
    Measurable fun omega => (u omega).gradToHilbertVectorL2 := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q) (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  let D := oneStepNeumannGradientOfForcingClass
    (translatedCubeMeanZeroH1CoerciveEstimate Q)
    (openCubeSet_nonempty_internal Q) hEll
  have heq : (fun omega => (u omega).gradToHilbertVectorL2) =
      D ∘ windowForcingL2 M a h p Q := by
    funext omega
    let hg := memVectorL2_openCubeSet_of_continuous Q
      ((windowContinuousMap M a h omega).continuous.smul
        (continuous_const : Continuous fun _ : Vec d => p))
    exact gradToHilbertVectorL2_eq_oneStepNeumannGradientOfForcingClass hg
      (translatedCubeMeanZeroH1CoerciveEstimate Q)
      (openCubeSet_nonempty_internal Q) hEll (hu omega)
  rw [heq]
  exact (continuous_oneStepNeumannGradientOfForcingClass _ _ _).measurable.comp
    (measurable_windowForcingL2 M a h p Q)

end SubdiffusiveProcess.LaplacianCorrector
