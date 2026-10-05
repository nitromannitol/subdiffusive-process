module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFiniteMajorantAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCellObservableMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMeasurableForcing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNestedRecentering
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SharpSuffixRepresentative
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffRatioSup

@[expose] public section




open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-! ## Strict-suffix measurability of the shell forcing -/

/-- Every spatial evaluation of the literal one-step multiplier reads only
the strict suffix above the lower cutoff. -/
theorem measurable_oneStepMultiplierAt_potentialShellIndexSigma_Ioi
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (x : Vec d) (hh : 0 < h) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (oneStepMultiplierAt M n h x) := by
  have hfield := measurable_cutoffRatioMinusOne_shellIndexSigma
    M (n + h) (n : ℤ) (by omega) (by exact_mod_cast Nat.lt_add_of_pos_right hh)
  have hindices :
      (↑(cutoffShellIndices (n + h) (n : ℤ)) : Set ℕ) ⊆ Set.Ioi n := by
    intro k hk
    have hk' : k ∈ cutoffShellIndices (n + h) (n : ℤ) := hk
    have hkn := (Finset.mem_Icc.mp hk').1
    have hnk : n + 1 ≤ k := by simpa using! hkn
    exact Nat.lt_of_succ_le hnk
  have hsigma : potentialShellIndexSigma (d := d)
      (↑(cutoffShellIndices (n + h) (n : ℤ)) : Set ℕ) ≤
      potentialShellIndexSigma (Set.Ioi n) :=
    potentialShellIndexSigma_mono hindices
  simpa only [oneStepMultiplierAt] using!
    (((measurable_pi_apply x).comp hfield).mono hsigma le_rfl)

/-- Joint sample/space measurability of the shell multiplier on the strict
suffix sigma-field. -/
theorem measurable_oneStepMultiplierAt_uncurry_potentialShellIndexSigma_Ioi
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (hh : 0 < h) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d) ℝ
      ((potentialShellIndexSigma (Set.Ioi n)).prod inferInstance)
      inferInstance
      (fun q ↦ oneStepMultiplierAt M n h q.2 q.1) := by
  let : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
    potentialShellIndexSigma (Set.Ioi n)
  have hraw : Measurable (Function.uncurry fun x : Vec d ↦
      fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ oneStepMultiplierAt M n h x omega) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun omega ↦ by
        simpa only [← oneStepMultiplierContinuousMap_apply M n h omega _ hh] using!
          (oneStepMultiplierContinuousMap M n h omega).continuous)
      (fun x ↦ measurable_oneStepMultiplierAt_potentialShellIndexSigma_Ioi
        M n h x hh)
  simpa only [Function.comp_apply] using! hraw.comp measurable_swap

/-- The literal Hilbert-`L²` forcing is measurable on the strict suffix
sigma-field.  The proof repeats the weak-probe/Fubini construction of the
ambient measurability theorem with the smaller sample sigma-field. -/
theorem measurable_oneStepShellForcingL2_potentialShellIndexSigma_Ioi
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (p : Vec d) (Q : TriadicCube d) (hh : 0 < h) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (HilbertVectorL2 (openCubeSet Q))
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (oneStepShellForcingL2 M n h p Q) := by
  let : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
    potentialShellIndexSigma (Set.Ioi n)
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  apply measurable_of_forall_real_inner_right
  intro Y
  have hmult : Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d ↦
      oneStepMultiplierAt M n h q.2 q.1 :=
    measurable_oneStepMultiplierAt_uncurry_potentialShellIndexSigma_Ioi
      M n h hh
  have hY : Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d ↦
      (Y : Vec d → HilbertVec d) q.2 :=
    (MeasureTheory.Lp.stronglyMeasurable Y).measurable.comp measurable_snd
  have hint : Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d ↦
      inner ℝ
        (oneStepMultiplierAt M n h q.2 q.1 • HilbertVec.ofVec p)
        ((Y : Vec d → HilbertVec d) q.2) :=
    (hmult.smul_const (HilbertVec.ofVec p)).inner hY
  have hparam : Measurable fun omega ↦
      ∫ x, inner ℝ
        (oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p)
        ((Y : Vec d → HilbertVec d) x)
        ∂(volumeMeasureOn (openCubeSet Q)) :=
    hint.stronglyMeasurable.integral_prod_right'.measurable
  have heq : (fun omega ↦
      inner ℝ (oneStepShellForcingL2 M n h p Q omega) Y) =
      fun omega ↦
        ∫ x, inner ℝ
          (oneStepMultiplierAt M n h x omega • HilbertVec.ofVec p)
          ((Y : Vec d → HilbertVec d) x)
          ∂(volumeMeasureOn (openCubeSet Q)) := by
    funext omega
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards
      [coeFn_toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepMultiplierContinuousMap M n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p)))]
      with x hx
    change inner ℝ
      ((toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_of_continuous Q
          ((oneStepMultiplierContinuousMap M n h omega).continuous.smul
            (continuous_const : Continuous fun _ : Vec d ↦ p))) :
          Vec d → HilbertVec d) x) ((Y : Vec d → HilbertVec d) x) = _
    rw [hx]
    change inner ℝ
      (oneStepMultiplierContinuousMap M n h omega x • HilbertVec.ofVec p)
      ((Y : Vec d → HilbertVec d) x) = _
    rw [oneStepMultiplierContinuousMap_apply M n h omega x hh]
  rw [heq]
  exact hparam

/-- The Sobolev forcing carrier agrees almost everywhere with the literal
suffix multiplier field. -/
theorem oneStepShellForcingH1_toField_ae_eq
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) :
    (oneStepShellForcingH1 M n h omega p Q hh).toField =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      fun x ↦ oneStepMultiplierAt M n h x omega • p := by
  let G := oneStepShellForcingH1 M n h omega p Q hh
  let hG : MemVectorL2 (openCubeSet Q) G.toField :=
    G.memVectorL2_toField_openCubeSet
  let F : Vec d → Vec d := fun x ↦
    oneStepMultiplierContinuousMap M n h omega x • p
  let hF : MemVectorL2 (openCubeSet Q) F :=
    memVectorL2_openCubeSet_of_continuous Q
      ((oneStepMultiplierContinuousMap M n h omega).continuous.smul
        (continuous_const : Continuous fun _ : Vec d ↦ p))
  have hclass : toHilbertVectorL2OfVecField hF =
      toHilbertVectorL2OfVecField hG := by
    exact oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
      M n h p Q omega hh
  have hleft := coeFn_toHilbertVectorL2OfVecField hF
  have hright := coeFn_toHilbertVectorL2OfVecField hG
  rw [← hclass] at hright
  filter_upwards [hleft, hright] with x hxF hxG
  have hv := congrArg HilbertVec.toVec (hxG.symm.trans hxF)
  simpa only [F, G, hilbertifyVecField, HilbertVec.toVec_ofVec,
    oneStepMultiplierContinuousMap_apply M n h omega x hh] using! hv

/-- A family of zero-Dirichlet shell solutions has a strict-suffix measurable
gradient class. -/
theorem measurable_oneStepShellDirichletGradL2_potentialShellIndexSigma_Ioi
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h)
    (uD : _root_.SubdiffusiveProcess.Model.PotentialSample d → H10Function (openCubeSet Q))
    (huD : ∀ omega,
      CubeDirichletDivergenceProblem Q (uD omega)
        (oneStepShellForcingH1 M n h omega p Q hh).toField) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (HilbertVectorL2 (openCubeSet Q))
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (fun omega ↦ (uD omega).toH1Function.gradToHilbertVectorL2) := by
  let : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
    potentialShellIndexSigma (Set.Ioi n)
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q)
      (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  let hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization
        (openCubeSet Q) :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet Q)
  let D := oneStepDirichletGradientOfForcingClass
    (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q))
    (openCubeSet_nonempty_internal Q) hEll
  have hforce : Measurable (oneStepShellForcingL2 M n h p Q) :=
    measurable_oneStepShellForcingL2_potentialShellIndexSigma_Ioi
      M n h p Q hh
  have heq : (fun omega ↦
      (uD omega).toH1Function.gradToHilbertVectorL2) =
      D ∘ fun omega ↦ -oneStepShellForcingL2 M n h p Q omega := by
    funext omega
    let G := oneStepShellForcingH1 M n h omega p Q hh
    let hG : MemVectorL2 (openCubeSet Q) G.toField :=
      G.memVectorL2_toField_openCubeSet
    have hweak : IsZeroTraceDirichletRhsWeakSolution
        (identityCoeffField d) (openCubeSet Q) (uD omega)
        (fun x ↦ -G.toField x) := by
      intro phi
      have hbase := huD omega phi
      simp only [matVecMul_identityCoeffField]
      change
        ∫ x in openCubeSet Q,
            vecDot ((uD omega).toH1Function.grad x)
              (phi.toH1Function.grad x) ∂volume =
          ∫ x in openCubeSet Q,
            vecDot (-G.toField x) (phi.toH1Function.grad x) ∂volume
      calc
        _ = -∫ x in openCubeSet Q,
            vecDot (G.toField x) (phi.toH1Function.grad x) ∂volume := by
          simpa only [CubeDirichletDivergenceProblem,
            matVecMul_identityCoeffField] using! hbase
        _ = _ := by
          rw [← integral_neg]
          apply integral_congr_ae
          filter_upwards with x
          exact (vecDot_neg_left (G.toField x)
            (phi.toH1Function.grad x)).symm
    calc
      (uD omega).toH1Function.gradToHilbertVectorL2 =
          D (toHilbertVectorL2OfVecField hG.neg) := by
        exact gradToHilbertVectorL2_eq_oneStepDirichletGradientOfForcingClass
          hG.neg hRealize (openCubeSet_nonempty_internal Q) hEll hweak
      _ = D (-oneStepShellForcingL2 M n h p Q omega) := by
        apply congrArg D
        rw [toHilbertVectorL2OfVecField_neg_oneStep hG]
        congr 1
        exact (oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
          M n h p Q omega hh).symm
  rw [heq]
  exact (continuous_oneStepDirichletGradientOfForcingClass _ _ _).measurable.comp
    hforce.neg

/-- The canonical triadic Dirichlet solution has a strict-suffix measurable
gradient class. -/
theorem measurable_oneStepTriadicDirichletGradL2_potentialShellIndexSigma_Ioi
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (HilbertVectorL2 (openCubeSet Q))
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (fun omega ↦
        (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
          |>.gradToHilbertVectorL2) := by
  apply measurable_oneStepShellDirichletGradL2_potentialShellIndexSigma_Ioi
    M n h p Q hh
  intro omega phi
  have hweak :=
    oneStepTriadicDirichletSolution_isWeakSolution M n h p Q omega hh phi
  have hfield := oneStepShellForcingH1_toField_ae_eq
    M n h omega p Q hh
  change ∫ x in openCubeSet Q,
      vecDot
        ((oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function.grad
          x)
        (phi.toH1Function.grad x) ∂volume =
    -∫ x in openCubeSet Q,
      vecDot ((oneStepShellForcingH1 M n h omega p Q hh).toField x)
        (phi.toH1Function.grad x) ∂volume
  calc
    _ = ∫ x in openCubeSet Q,
        vecDot (-oneStepMultiplierAt M n h x omega • p)
          (phi.toH1Function.grad x) ∂volume := by
      simpa only [matVecMul_identityCoeffField] using! hweak
    _ = ∫ x in openCubeSet Q,
        vecDot (-(oneStepShellForcingH1 M n h omega p Q hh).toField x)
          (phi.toH1Function.grad x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [hfield] with x hx
      rw [hx]
      simp only [neg_smul]
    _ = -∫ x in openCubeSet Q,
        vecDot ((oneStepShellForcingH1 M n h omega p Q hh).toField x)
          (phi.toH1Function.grad x) ∂volume := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      exact vecDot_neg_left _ _

/-- A family of mean-zero Neumann shell solutions has a strict-suffix
measurable gradient class. -/
theorem measurable_oneStepShellNeumannGradL2_potentialShellIndexSigma_Ioi
    {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h)
    (uN : _root_.SubdiffusiveProcess.Model.PotentialSample d → H1MeanZeroFunction (openCubeSet Q))
    (huN : ∀ omega,
      IsMeanZeroNeumannRhsWeakSolution
        (identityCoeffField d) (openCubeSet Q) (uN omega)
        (fun x ↦
          -(oneStepShellForcingH1 M n h omega p Q hh).toField x)) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (HilbertVectorL2 (openCubeSet Q))
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (fun omega ↦ (uN omega).gradToHilbertVectorL2) := by
  let : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
    potentialShellIndexSigma (Set.Ioi n)
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q)
      (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  let D := oneStepNeumannGradientOfForcingClass
    (translatedCubeMeanZeroH1CoerciveEstimate Q)
    (openCubeSet_nonempty_internal Q) hEll
  have hforce : Measurable (oneStepShellForcingL2 M n h p Q) :=
    measurable_oneStepShellForcingL2_potentialShellIndexSigma_Ioi
      M n h p Q hh
  have heq : (fun omega ↦ (uN omega).gradToHilbertVectorL2) =
      D ∘ fun omega ↦ -oneStepShellForcingL2 M n h p Q omega := by
    funext omega
    let G := oneStepShellForcingH1 M n h omega p Q hh
    let hG : MemVectorL2 (openCubeSet Q) G.toField :=
      G.memVectorL2_toField_openCubeSet
    calc
      (uN omega).gradToHilbertVectorL2 =
          D (toHilbertVectorL2OfVecField hG.neg) := by
        exact gradToHilbertVectorL2_eq_oneStepNeumannGradientOfForcingClass
          hG.neg (translatedCubeMeanZeroH1CoerciveEstimate Q)
          (openCubeSet_nonempty_internal Q) hEll (huN omega)
      _ = D (-oneStepShellForcingL2 M n h p Q omega) := by
        apply congrArg D
        rw [toHilbertVectorL2OfVecField_neg_oneStep hG]
        congr 1
        exact (oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
          M n h p Q omega hh).symm
  rw [heq]
  exact (continuous_oneStepNeumannGradientOfForcingClass _ _ _).measurable.comp
    hforce.neg

/-- The canonical triadic Neumann solution has a strict-suffix measurable
gradient class. -/
theorem measurable_oneStepTriadicNeumannGradL2_potentialShellIndexSigma_Ioi
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (HilbertVectorL2 (openCubeSet Q))
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (fun omega ↦
        (oneStepTriadicNeumannSolution M n h p Q omega hh)
          |>.gradToHilbertVectorL2) := by
  apply measurable_oneStepShellNeumannGradL2_potentialShellIndexSigma_Ioi
    M n h p Q hh
  intro omega phi
  have hweak :=
    oneStepTriadicNeumannSolution_isWeakSolution M n h p Q omega hh phi
  have hfield := oneStepShellForcingH1_toField_ae_eq
    M n h omega p Q hh
  calc
    ∫ x in openCubeSet Q,
        vecDot (matVecMul (identityCoeffField d x)
          ((oneStepTriadicNeumannSolution M n h p Q omega hh).toH1Function.grad
            x))
          (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot (-oneStepMultiplierAt M n h x omega • p)
            (phi.toH1Function.grad x) ∂volume := hweak
    _ = ∫ x in openCubeSet Q,
        vecDot (-(oneStepShellForcingH1 M n h omega p Q hh).toField x)
          (phi.toH1Function.grad x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [hfield] with x hx
      rw [hx]
      simp only [neg_smul]

/-! ## Measurable cell means and prefix/suffix factorization -/

/-- Cell mean of an ambient Hilbert-`L²` vector class, in the exact
finite-dimensional carrier needed by the principal energy. -/
def oneStepCellMeanVec {d : ℕ} (Q R : TriadicCube d)
    (f : HilbertVectorL2 (openCubeSet Q)) : Vec d := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact fun i ↦ (cubeVolume R)⁻¹ *
    hilbertVectorL2CoordSetIntegralCLM
      (U := openCubeSet Q) (openCubeSet R)
        (measurableSet_openCubeSet R) i f

/-- Continuous-linear form of `oneStepCellMeanVec`, used to transport
random-variable `L²` membership to every finite cell mean at once. -/
def oneStepCellMeanVecCLM {d : ℕ} (Q R : TriadicCube d) :
    HilbertVectorL2 (openCubeSet Q) →L[ℝ] Vec d := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact ContinuousLinearMap.pi fun i ↦
    (cubeVolume R)⁻¹ •
      hilbertVectorL2CoordSetIntegralCLM
        (U := openCubeSet Q) (openCubeSet R)
          (measurableSet_openCubeSet R) i

@[simp] theorem oneStepCellMeanVecCLM_apply {d : ℕ}
    (Q R : TriadicCube d) (f : HilbertVectorL2 (openCubeSet Q)) :
    oneStepCellMeanVecCLM Q R f = oneStepCellMeanVec Q R f := by
  rfl

theorem memLp_oneStepCellMeanVec_comp {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega}
    {d : ℕ} (Q R : TriadicCube d)
    {f : Omega → HilbertVectorL2 (openCubeSet Q)} {p : ENNReal}
    (hf : MemLp f p mu) :
    MemLp (fun omega ↦ oneStepCellMeanVec Q R (f omega)) p mu := by
  simpa only [oneStepCellMeanVecCLM_apply] using!
    hf.continuousLinearMap_comp (oneStepCellMeanVecCLM Q R)

theorem continuous_oneStepCellMeanVec {d : ℕ} (Q R : TriadicCube d) :
    Continuous (oneStepCellMeanVec Q R) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  apply continuous_pi
  intro i
  exact continuous_const.mul
    (hilbertVectorL2CoordSetIntegralCLM
      (U := openCubeSet Q) (openCubeSet R)
        (measurableSet_openCubeSet R) i).continuous

/-- The Hilbert-class cell mean is the manuscript's literal cube average
whenever the cell lies in the ambient cube. -/
theorem oneStepCellMeanVec_toHilbertVectorL2OfVecField_eq_cubeAverageVec
    {d : ℕ} (Q R : TriadicCube d)
    (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (f : Vec d → Vec d) (hf : MemVectorL2 (openCubeSet Q) f) :
    oneStepCellMeanVec Q R (toHilbertVectorL2OfVecField hf) =
      cubeAverageVec R f := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  ext i
  rw [oneStepCellMeanVec, hilbertVectorL2CoordSetIntegralCLM_apply]
  have hcoe := coeFn_toHilbertVectorL2OfVecField hf
  have hcoord :
      (fun x ↦ (toHilbertVectorL2OfVecField hf x) i) =ᵐ[
        (volumeMeasureOn (openCubeSet Q)).restrict (openCubeSet R)]
      fun x ↦ f x i := by
    exact (hcoe.filter_mono
      (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)).mono
      (fun x hx ↦ by
        simpa only [hilbertifyVecField] using!
          congrArg (fun v : HilbertVec d ↦ v i) hx)
  rw [integral_congr_ae hcoord]
  rw [MeasureTheory.Measure.restrict_restrict_of_subset hRQ]
  rw [cubeAverageVec, cubeAverage,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet]

theorem measurable_oneStepTriadicDirichletCellMean_potentialShellIndexSigma_Ioi
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (Vec d)
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (fun omega ↦ oneStepCellMeanVec Q R
        ((oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
          |>.gradToHilbertVectorL2)) :=
  (continuous_oneStepCellMeanVec Q R).measurable.comp
    (measurable_oneStepTriadicDirichletGradL2_potentialShellIndexSigma_Ioi
      M n h p Q hh)

theorem measurable_oneStepTriadicNeumannCellMean_potentialShellIndexSigma_Ioi
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (Vec d)
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (fun omega ↦ oneStepCellMeanVec Q R
        ((oneStepTriadicNeumannSolution M n h p Q omega hh)
          |>.gradToHilbertVectorL2)) :=
  (continuous_oneStepCellMeanVec Q R).measurable.comp
    (measurable_oneStepTriadicNeumannGradL2_potentialShellIndexSigma_Ioi
      M n h p Q hh)

/-- Constant vector field on the ambient cube, represented in Hilbert
`L²`. -/
def oneStepConstantVectorL2 {d : ℕ} (Q : TriadicCube d) (p : Vec d) :
    HilbertVectorL2 (openCubeSet Q) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact toHilbertVectorL2OfVecField (memVectorL2_const p)

/-- The manuscript's primal large-cube field `P = p + grad w`, on the
Hilbert carrier. -/
def oneStepDirichletSlopeL2 {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    HilbertVectorL2 (openCubeSet Q) :=
  oneStepConstantVectorL2 Q p +
    ((oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
      |>.gradToHilbertVectorL2)

/-- The manuscript's dual large-cube field
`exp(H) q - grad W = q + (exp(H)-1)q - grad W`. -/
def oneStepNeumannSlopeL2 {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    HilbertVectorL2 (openCubeSet Q) :=
  oneStepConstantVectorL2 Q q + oneStepShellForcingL2 M n h q Q omega -
    ((oneStepTriadicNeumannSolution M n h q Q omega hh)
      |>.gradToHilbertVectorL2)

/-- Pointwise representative of the primal large-cube slope. -/
def oneStepDirichletSlopeField {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    Vec d → Vec d :=
  fun x ↦ p +
    (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function.grad x

/-- Pointwise representative of the dual large-cube slope. -/
def oneStepNeumannSlopeField {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    Vec d → Vec d :=
  fun x ↦ q + oneStepMultiplierAt M n h x omega • q -
    (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad x

theorem oneStepDirichletSlopeField_memVectorL2 {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    MemVectorL2 (openCubeSet Q)
      (oneStepDirichletSlopeField M n h p Q omega hh) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  exact (memVectorL2_const p).add
    ((oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
      |>.grad_memVectorL2)

theorem oneStepNeumannSlopeField_memVectorL2 {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    MemVectorL2 (openCubeSet Q)
      (oneStepNeumannSlopeField M n h q Q omega hh) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hforcing : MemVectorL2 (openCubeSet Q) (fun x ↦
      oneStepMultiplierAt M n h x omega • q) := by
    apply memVectorL2_openCubeSet_of_continuous Q
    exact (continuous_oneStepMultiplierAt_sample M n h omega).smul
      (continuous_const : Continuous fun _ : Vec d ↦ q)
  exact ((memVectorL2_const q).add hforcing).sub
    ((oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function
      |>.grad_memVectorL2)

theorem oneStepDirichletSlopeL2_eq_toHilbertVectorL2OfVecField
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    oneStepDirichletSlopeL2 M n h p Q omega hh =
      toHilbertVectorL2OfVecField
        (oneStepDirichletSlopeField_memVectorL2 M n h p Q omega hh) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  unfold oneStepDirichletSlopeL2 oneStepConstantVectorL2
    oneStepDirichletSlopeField H1Function.gradToHilbertVectorL2
  exact (toHilbertVectorL2OfVecField_add (memVectorL2_const p)
    ((oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
      |>.grad_memVectorL2)).symm

theorem oneStepNeumannSlopeL2_eq_toHilbertVectorL2OfVecField
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    oneStepNeumannSlopeL2 M n h q Q omega hh =
      toHilbertVectorL2OfVecField
        (oneStepNeumannSlopeField_memVectorL2 M n h q Q omega hh) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hforcing : MemVectorL2 (openCubeSet Q) (fun x ↦
      oneStepMultiplierAt M n h x omega • q) := by
    apply memVectorL2_openCubeSet_of_continuous Q
    exact (continuous_oneStepMultiplierAt_sample M n h omega).smul
      (continuous_const : Continuous fun _ : Vec d ↦ q)
  have hadd := toHilbertVectorL2OfVecField_add (memVectorL2_const q) hforcing
  have hsub := toHilbertVectorL2OfVecField_sub
    ((memVectorL2_const q).add hforcing)
    ((oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function
      |>.grad_memVectorL2)
  rw [oneStepNeumannSlopeL2, oneStepConstantVectorL2,
    H1MeanZeroFunction.gradToHilbertVectorL2,
    H1Function.gradToHilbertVectorL2,
    oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
      M n h q Q omega hh]
  simpa only [hadd] using! hsub.symm

theorem measurable_hilbertVectorL2_add
    {Omega : Type*} [MeasurableSpace Omega]
    {d : ℕ} {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    [Fact ((1 : ENNReal) ≤ 2)] [Fact ((2 : ENNReal) ≠ (⊤ : ENNReal))]
    {f g : Omega → HilbertVectorL2 U}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun omega ↦ f omega + g omega := by
  apply measurable_of_forall_real_inner_right
  intro Y
  have hfY : Measurable fun omega ↦ inner ℝ (f omega) Y :=
    (continuous_id.inner continuous_const).measurable.comp hf
  have hgY : Measurable fun omega ↦ inner ℝ (g omega) Y :=
    (continuous_id.inner continuous_const).measurable.comp hg
  simpa only [inner_add_left] using! hfY.add hgY

theorem measurable_hilbertVectorL2_sub
    {Omega : Type*} [MeasurableSpace Omega]
    {d : ℕ} {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    [Fact ((1 : ENNReal) ≤ 2)] [Fact ((2 : ENNReal) ≠ (⊤ : ENNReal))]
    {f g : Omega → HilbertVectorL2 U}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun omega ↦ f omega - g omega := by
  apply measurable_of_forall_real_inner_right
  intro Y
  have hfY : Measurable fun omega ↦ inner ℝ (f omega) Y :=
    (continuous_id.inner continuous_const).measurable.comp hf
  have hgY : Measurable fun omega ↦ inner ℝ (g omega) Y :=
    (continuous_id.inner continuous_const).measurable.comp hg
  simpa only [inner_sub_left] using! hfY.sub hgY

private theorem memLp_two_of_integrable_norm_four
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] {mu : Measure Omega} [IsFiniteMeasure mu]
    {f : Omega → E} (hf : AEStronglyMeasurable f mu)
    (hfour : Integrable (fun omega ↦ ‖f omega‖ ^ (4 : ℕ)) mu) :
    MemLp f 2 mu := by
  apply (memLp_two_iff_integrable_sq_norm hf).2
  have hmajor : Integrable (fun omega ↦
      1 + ‖f omega‖ ^ (4 : ℕ)) mu :=
    integrable_const (1 : ℝ) |>.add hfour
  apply hmajor.mono'
    (hf.norm.aemeasurable.pow_const 2).aestronglyMeasurable
  filter_upwards with omega
  change |‖f omega‖ ^ 2| ≤ 1 + ‖f omega‖ ^ 4
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (‖f omega‖ ^ 2 - 1)]

private theorem memLp_four_of_integrable_norm_four
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] {mu : Measure Omega}
    {f : Omega → E} (hf : AEStronglyMeasurable f mu)
    (hfour : Integrable (fun omega ↦ ‖f omega‖ ^ (4 : ℕ)) mu) :
    MemLp f 4 mu := by
  rw [← integrable_norm_rpow_iff hf
    (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)]
  convert hfour using 1
  funext omega
  exact Real.rpow_natCast ‖f omega‖ 4

theorem memLp_four_oneStepTriadicDirichletGradL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) (hp : vecNormSq p = 1) :
    MemLp (fun omega ↦
      (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
        |>.gradToHilbertVectorL2) 4 M.P.toMeasure := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  let c : ℝ := (cubeVolume (originCube d Q.scale))⁻¹ ^ (1 / 2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos
    (inv_pos.mpr (cubeVolume_pos (originCube d Q.scale))) _
  have horigin :=
    integrable_oneStepOriginDirichletNormalizedGradientFourth
      M n h p Q.scale hh hp
  have htranslated :=
    integrable_oneStepTranslatedDirichletNormalizedGradientFourth
      M n h p (triadicCubeShift Q) Q.scale hh horigin
  have hfour : Integrable (fun omega ↦
      ‖c • ((oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
        |>.gradToHilbertVectorL2)‖ ^ (4 : ℕ)) M.P.toMeasure := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hc,
      oneStepTriadicDirichletSolution,
      oneStepTranslatedDirichletNormalizedGradientFourth,
      oneStepTranslatedDirichletNormalizedGradient,
      norm_gradToHilbertVectorL2_castH10Domain] using! htranslated
  have hgradMeas : Measurable (fun omega ↦
      (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
        |>.gradToHilbertVectorL2) :=
    (measurable_oneStepTriadicDirichletGradL2_potentialShellIndexSigma_Ioi
      M n h p Q hh).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl
  have hscaled : MemLp (fun omega ↦
      c • ((oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
        |>.gradToHilbertVectorL2)) 4 M.P.toMeasure :=
    memLp_four_of_integrable_norm_four
      (hgradMeas.aestronglyMeasurable.const_smul c) hfour
  have hunscaled := MeasureTheory.MemLp.const_smul hscaled c⁻¹
  exact MeasureTheory.MemLp.ae_eq
    (Filter.Eventually.of_forall fun omega ↦ by
      simp only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ hc.ne', one_smul])
    hunscaled

theorem memLp_two_oneStepTriadicDirichletGradL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) (hp : vecNormSq p = 1) :
    MemLp (fun omega ↦
      (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
        |>.gradToHilbertVectorL2) 2 M.P.toMeasure := by
  exact (memLp_four_oneStepTriadicDirichletGradL2 M n h p Q hh hp).mono_exponent
    (by norm_num)

theorem memLp_four_oneStepDirichletSlopeL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) (hp : vecNormSq p = 1) :
    MemLp (oneStepDirichletSlopeL2 M n h p Q · hh)
      4 M.P.toMeasure := by
  have hconst : MemLp (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ oneStepConstantVectorL2 Q p)
      4 M.P.toMeasure := memLp_const _
  have hgrad := memLp_four_oneStepTriadicDirichletGradL2
    M n h p Q hh hp
  simpa only [oneStepDirichletSlopeL2, Pi.add_apply] using! hconst.add hgrad

theorem memLp_two_oneStepDirichletSlopeL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) (hp : vecNormSq p = 1) :
    MemLp (oneStepDirichletSlopeL2 M n h p Q · hh)
      2 M.P.toMeasure := by
  have hconst : MemLp (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ oneStepConstantVectorL2 Q p)
      2 M.P.toMeasure := memLp_const _
  have hgrad := memLp_two_oneStepTriadicDirichletGradL2
    M n h p Q hh hp
  simpa only [oneStepDirichletSlopeL2, Pi.add_apply] using! hconst.add hgrad

theorem memLp_four_oneStepTriadicNeumannGradL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) (hq : vecNormSq q = 1) :
    MemLp (fun omega ↦
      (oneStepTriadicNeumannSolution M n h q Q omega hh)
        |>.gradToHilbertVectorL2) 4 M.P.toMeasure := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  let c : ℝ := (cubeVolume (originCube d Q.scale))⁻¹ ^ (1 / 2 : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos
    (inv_pos.mpr (cubeVolume_pos (originCube d Q.scale))) _
  have horigin :=
    integrable_oneStepOriginNeumannNormalizedGradientFourth
      M n h q Q.scale hh hq
  have htranslated :=
    integrable_oneStepTranslatedNeumannNormalizedGradientFourth
      M n h q (triadicCubeShift Q) Q.scale hh horigin
  have hfour : Integrable (fun omega ↦
      ‖c • (oneStepTriadicNeumannSolution M n h q Q omega hh
        |>.gradToHilbertVectorL2)‖ ^ (4 : ℕ)) M.P.toMeasure := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hc,
      oneStepTriadicNeumannSolution,
      oneStepTranslatedNeumannNormalizedGradientFourth,
      oneStepTranslatedNeumannNormalizedGradient,
      norm_gradToHilbertVectorL2_castMeanZeroDomain] using! htranslated
  have hgradMeas : Measurable (fun omega ↦
      (oneStepTriadicNeumannSolution M n h q Q omega hh)
        |>.gradToHilbertVectorL2) :=
    (measurable_oneStepTriadicNeumannGradL2_potentialShellIndexSigma_Ioi
      M n h q Q hh).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl
  have hscaled : MemLp (fun omega ↦
      c • (oneStepTriadicNeumannSolution M n h q Q omega hh
        |>.gradToHilbertVectorL2)) 4 M.P.toMeasure :=
    memLp_four_of_integrable_norm_four
      (hgradMeas.aestronglyMeasurable.const_smul c) hfour
  have hunscaled := MeasureTheory.MemLp.const_smul hscaled c⁻¹
  exact MeasureTheory.MemLp.ae_eq
    (Filter.Eventually.of_forall fun omega ↦ by
      simp only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ hc.ne', one_smul])
    hunscaled

theorem memLp_two_oneStepTriadicNeumannGradL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) (hq : vecNormSq q = 1) :
    MemLp (fun omega ↦
      (oneStepTriadicNeumannSolution M n h q Q omega hh)
        |>.gradToHilbertVectorL2) 2 M.P.toMeasure := by
  exact (memLp_four_oneStepTriadicNeumannGradL2 M n h q Q hh hq).mono_exponent
    (by norm_num)

theorem memLp_four_oneStepShellForcingL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) :
    MemLp (oneStepShellForcingL2 M n h q Q) 4 M.P.toMeasure := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  let U : Ch02.Domain d := Ch02.cubeDomain Q
  let R : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := cutoffRatioSup M (n + h) n U
  let C : ℝ :=
    ((volumeMeasureOn (openCubeSet Q)) Set.univ).toReal ^ ((2 : ℝ)⁻¹) *
      ((d : ℝ) * ‖q‖)
  have hnh : n < n + h := Nat.lt_add_of_pos_right hh
  have hR : MemLp R 4 M.P.toMeasure := by
    simpa only [R] using! memLp_four_cutoffRatioSup_forward M hnh U
  have hmajor : MemLp (fun omega ↦ C * (R omega + 1))
      4 M.P.toMeasure := by
    have hsum : MemLp (fun omega ↦ R omega + 1) 4 M.P.toMeasure := by
      simpa only [Pi.add_apply] using! hR.add (memLp_const (1 : ℝ))
    exact hsum.const_mul C
  apply hmajor.mono'
    ((measurable_oneStepShellForcingL2 M n h q Q hh).aestronglyMeasurable)
  filter_upwards with omega
  have hR0 : 0 ≤ R omega :=
    (cutoffRatioSup_pos M (n + h) n U omega).le
  have hbound : ∀ x ∈ openCubeSet Q,
      ‖oneStepMultiplierAt M n h x omega • q‖ ≤
        (R omega + 1) * ‖q‖ := by
    intro x hx
    have hxU : x ∈ (U : Set (Vec d)) := by
      simpa only [U, Ch02.cubeDomain_coe] using! hx
    have hratio := cutoffRatio_le_cutoffRatioSup
      M (n + h) n U omega hxU
    have hratio0 : 0 ≤
        _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M n omega x :=
      (div_pos (_root_.SubdiffusiveProcess.Model.aCutoff_pos M (n + h) omega x)
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega x)).le
    have habs :
        |_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x /
            _root_.SubdiffusiveProcess.Model.aCutoff M n omega x - 1| ≤
          R omega + 1 := by
      rw [abs_le]
      constructor <;> nlinarith
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right habs (norm_nonneg q)
  have hfield : MemVectorL2 (openCubeSet Q) (fun x ↦
      oneStepMultiplierAt M n h x omega • q) := by
    apply memVectorL2_openCubeSet_of_continuous Q
    exact (continuous_oneStepMultiplierAt_sample M n h omega).smul
      (continuous_const : Continuous fun _ : Vec d ↦ q)
  rw [oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
    M n h q Q omega hh]
  have hnorm := norm_oneStepToHilbertVectorL2OfVecField_le_of_bound_on
    (measurableSet_openCubeSet Q) hfield
      (mul_nonneg (add_nonneg hR0 zero_le_one) (norm_nonneg q)) hbound
  simpa only [C, mul_add, mul_assoc, mul_comm, mul_left_comm] using! hnorm

theorem memLp_two_oneStepShellForcingL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) :
    MemLp (oneStepShellForcingL2 M n h q Q) 2 M.P.toMeasure := by
  exact (memLp_four_oneStepShellForcingL2 M n h q Q hh).mono_exponent
    (by norm_num)

theorem memLp_four_oneStepNeumannSlopeL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) (hq : vecNormSq q = 1) :
    MemLp (oneStepNeumannSlopeL2 M n h q Q · hh)
      4 M.P.toMeasure := by
  have hconst : MemLp (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ oneStepConstantVectorL2 Q q)
      4 M.P.toMeasure := memLp_const _
  have hforcing := memLp_four_oneStepShellForcingL2 M n h q Q hh
  have hgrad := memLp_four_oneStepTriadicNeumannGradL2 M n h q Q hh hq
  simpa only [oneStepNeumannSlopeL2, Pi.add_apply, Pi.sub_apply] using!
    (hconst.add hforcing).sub hgrad

theorem memLp_two_oneStepNeumannSlopeL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) (hq : vecNormSq q = 1) :
    MemLp (oneStepNeumannSlopeL2 M n h q Q · hh)
      2 M.P.toMeasure := by
  have hconst : MemLp (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ oneStepConstantVectorL2 Q q)
      2 M.P.toMeasure := memLp_const _
  have hforcing := memLp_two_oneStepShellForcingL2 M n h q Q hh
  have hgrad := memLp_two_oneStepTriadicNeumannGradL2 M n h q Q hh hq
  simpa only [oneStepNeumannSlopeL2, Pi.add_apply, Pi.sub_apply] using!
    (hconst.add hforcing).sub hgrad

theorem measurable_oneStepDirichletSlopeL2_potentialShellIndexSigma_Ioi
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (HilbertVectorL2 (openCubeSet Q))
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (oneStepDirichletSlopeL2 M n h p Q · hh) := by
  let : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
    potentialShellIndexSigma (Set.Ioi n)
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  exact measurable_hilbertVectorL2_add measurable_const
    (measurable_oneStepTriadicDirichletGradL2_potentialShellIndexSigma_Ioi
      M n h p Q hh)

theorem measurable_oneStepNeumannSlopeL2_potentialShellIndexSigma_Ioi
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (HilbertVectorL2 (openCubeSet Q))
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (oneStepNeumannSlopeL2 M n h q Q · hh) := by
  let : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
    potentialShellIndexSigma (Set.Ioi n)
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  have hleft : Measurable fun omega ↦
      oneStepConstantVectorL2 Q q + oneStepShellForcingL2 M n h q Q omega :=
    measurable_hilbertVectorL2_add measurable_const
      (measurable_oneStepShellForcingL2_potentialShellIndexSigma_Ioi
        M n h q Q hh)
  exact measurable_hilbertVectorL2_sub hleft
    (measurable_oneStepTriadicNeumannGradL2_potentialShellIndexSigma_Ioi
      M n h q Q hh)

/-- Literal primal cell slope `p_z`. -/
def oneStepDirichletCellSlope {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : Vec d :=
  oneStepCellMeanVec Q R (oneStepDirichletSlopeL2 M n h p Q omega hh)

/-- Literal dual cell slope `q_z`. -/
def oneStepNeumannCellSlope {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) : Vec d :=
  oneStepCellMeanVec Q R (oneStepNeumannSlopeL2 M n h q Q omega hh)

theorem memLp_two_oneStepDirichletCellSlope
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) (hp : vecNormSq p = 1) :
    MemLp (oneStepDirichletCellSlope M n h p Q R · hh)
      2 M.P.toMeasure := by
  exact memLp_oneStepCellMeanVec_comp Q R
    (memLp_two_oneStepDirichletSlopeL2 M n h p Q hh hp)

theorem memLp_four_oneStepDirichletCellSlope
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) (hp : vecNormSq p = 1) :
    MemLp (oneStepDirichletCellSlope M n h p Q R · hh)
      4 M.P.toMeasure := by
  exact memLp_oneStepCellMeanVec_comp Q R
    (memLp_four_oneStepDirichletSlopeL2 M n h p Q hh hp)

theorem memLp_two_oneStepDirichletCellSlope_coord
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) (hp : vecNormSq p = 1)
    (i : Fin d) :
    MemLp (fun omega ↦ oneStepDirichletCellSlope M n h p Q R omega hh i)
      2 M.P.toMeasure := by
  exact (memLp_two_oneStepDirichletCellSlope M n h p Q R hh hp)
    |>.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)

theorem memLp_four_oneStepDirichletCellSlope_coord
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) (hp : vecNormSq p = 1)
    (i : Fin d) :
    MemLp (fun omega ↦ oneStepDirichletCellSlope M n h p Q R omega hh i)
      4 M.P.toMeasure := by
  exact (memLp_four_oneStepDirichletCellSlope M n h p Q R hh hp)
    |>.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)

theorem memLp_two_oneStepNeumannCellSlope
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) (hq : vecNormSq q = 1) :
    MemLp (oneStepNeumannCellSlope M n h q Q R · hh)
      2 M.P.toMeasure := by
  exact memLp_oneStepCellMeanVec_comp Q R
    (memLp_two_oneStepNeumannSlopeL2 M n h q Q hh hq)

theorem memLp_four_oneStepNeumannCellSlope
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) (hq : vecNormSq q = 1) :
    MemLp (oneStepNeumannCellSlope M n h q Q R · hh)
      4 M.P.toMeasure := by
  exact memLp_oneStepCellMeanVec_comp Q R
    (memLp_four_oneStepNeumannSlopeL2 M n h q Q hh hq)

theorem memLp_two_oneStepNeumannCellSlope_coord
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) (hq : vecNormSq q = 1)
    (i : Fin d) :
    MemLp (fun omega ↦ oneStepNeumannCellSlope M n h q Q R omega hh i)
      2 M.P.toMeasure := by
  exact (memLp_two_oneStepNeumannCellSlope M n h q Q R hh hq)
    |>.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)

theorem memLp_four_oneStepNeumannCellSlope_coord
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) (hq : vecNormSq q = 1)
    (i : Fin d) :
    MemLp (fun omega ↦ oneStepNeumannCellSlope M n h q Q R omega hh i)
      4 M.P.toMeasure := by
  exact (memLp_four_oneStepNeumannCellSlope M n h q Q R hh hq)
    |>.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)

/-- A square-integrable weight times a quadratic product of fourth-moment
coordinates is integrable.  This is the exact Hölder bookkeeping needed by
the weighted prefix/suffix factorization. -/
theorem integrable_weight_mul_pair_of_memLp_two_four
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (weight : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) (p : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d)
    (hweight : MemLp weight 2 M.P.toMeasure)
    (hp : ∀ i : Fin d, MemLp (fun omega ↦ p omega i) 4 M.P.toMeasure)
    (i j : Fin d) :
    Integrable (fun omega ↦ weight omega * (p omega i * p omega j))
      M.P.toMeasure := by
  let : ENNReal.HolderTriple 4 4 2 := ⟨by
    change ((↑(4 : NNReal) : ENNReal)⁻¹ + (↑(4 : NNReal) : ENNReal)⁻¹) =
      (↑(2 : NNReal) : ENNReal)⁻¹
    rw [← ENNReal.coe_inv (show (4 : NNReal) ≠ 0 by norm_num),
      ← ENNReal.coe_inv (show (2 : NNReal) ≠ 0 by norm_num),
      ← ENNReal.coe_add]
    norm_num⟩
  have hpPair : MemLp (fun omega ↦ p omega i * p omega j)
      2 M.P.toMeasure :=
    (hp i).fun_mul (hp j)
  exact hweight.integrable_mul hpPair

/-- Integrability counterpart of the weighted prefix/suffix factorization.
The random coarse-matrix entries read the frozen prefix, while the weighted
quadratic slope reads the fresh suffix. -/
theorem integrable_weight_mul_vecDot_randomAMatrix_suffix
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n : ℕ) (U : Ch02.Domain d) (weight : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ)
    (p : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d)
    (hweight : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance weight)
    (hp : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (Vec d)
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance p)
    (hweightedPairInt : ∀ i j : Fin d,
      Integrable (fun omega ↦ weight omega * (p omega i * p omega j))
        M.P.toMeasure) :
    Integrable (fun omega ↦ weight omega * vecDot (p omega)
      (matVecMul (randomAMatrix M n U omega) (p omega))) M.P.toMeasure := by
  have hdisjoint : Disjoint (Set.Iic n) (Set.Ioi n) :=
    Set.Iic_disjoint_Ioi le_rfl
  have hAmeas := measurable_randomAMatrix_potentialShellIndexSigma_Iic M n U
  have hentryMeas : ∀ i j : Fin d,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        (potentialShellIndexSigma (Set.Iic n)) inferInstance
        (fun omega ↦ randomAMatrix M n U omega i j) := by
    intro i j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hAmeas)
  have hweightedPairMeas : ∀ i j : Fin d,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        (potentialShellIndexSigma (Set.Ioi n)) inferInstance
        (fun omega ↦ weight omega * (p omega i * p omega j)) := by
    intro i j
    exact hweight.mul <|
      ((measurable_pi_apply i).comp hp).mul ((measurable_pi_apply j).comp hp)
  have hindep : ∀ i j : Fin d,
      IndepFun (fun omega ↦ randomAMatrix M n U omega i j)
        (fun omega ↦ weight omega * (p omega i * p omega j))
        M.P.toMeasure := by
    intro i j
    exact indepFun_of_measurable_potentialShellIndexSigma_of_disjoint
      M hdisjoint (hentryMeas i j) (hweightedPairMeas i j)
  have hentryInt : ∀ i j : Fin d,
      Integrable (fun omega ↦ randomAMatrix M n U omega i j)
        M.P.toMeasure := by
    intro i j
    exact ((integrable_randomAMatrix M n U).eval i).eval j
  have htermInt : ∀ i j : Fin d,
      Integrable (fun omega ↦ randomAMatrix M n U omega i j *
        (weight omega * (p omega i * p omega j))) M.P.toMeasure := by
    intro i j
    exact (hindep i j).integrable_mul (hentryInt i j)
      (hweightedPairInt i j)
  have hquad : (fun omega ↦ weight omega * vecDot (p omega)
      (matVecMul (randomAMatrix M n U omega) (p omega))) =
      fun omega ↦ ∑ i : Fin d, ∑ j : Fin d,
        randomAMatrix M n U omega i j *
          (weight omega * (p omega i * p omega j)) := by
    funext omega
    simp only [vecDot, matVecMul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hquad]
  exact integrable_finsetSum Finset.univ fun i _hi ↦
    integrable_finsetSum Finset.univ fun j _hj ↦ htermInt i j

theorem oneStepDirichletCellSlope_eq_cubeAverageVec
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    oneStepDirichletCellSlope M n h p Q R omega hh =
      cubeAverageVec R (oneStepDirichletSlopeField M n h p Q omega hh) := by
  rw [oneStepDirichletCellSlope,
    oneStepDirichletSlopeL2_eq_toHilbertVectorL2OfVecField]
  exact oneStepCellMeanVec_toHilbertVectorL2OfVecField_eq_cubeAverageVec
    Q R (openCubeSet_subset_of_mem_descendantsAtDepth hR)
      (oneStepDirichletSlopeField M n h p Q omega hh)
      (oneStepDirichletSlopeField_memVectorL2 M n h p Q omega hh)

theorem oneStepNeumannCellSlope_eq_cubeAverageVec
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    oneStepNeumannCellSlope M n h q Q R omega hh =
      cubeAverageVec R (oneStepNeumannSlopeField M n h q Q omega hh) := by
  rw [oneStepNeumannCellSlope,
    oneStepNeumannSlopeL2_eq_toHilbertVectorL2OfVecField]
  exact oneStepCellMeanVec_toHilbertVectorL2OfVecField_eq_cubeAverageVec
    Q R (openCubeSet_subset_of_mem_descendantsAtDepth hR)
      (oneStepNeumannSlopeField M n h q Q omega hh)
      (oneStepNeumannSlopeField_memVectorL2 M n h q Q omega hh)

theorem measurable_oneStepDirichletCellSlope_potentialShellIndexSigma_Ioi
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (Vec d)
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (oneStepDirichletCellSlope M n h p Q R · hh) :=
  (continuous_oneStepCellMeanVec Q R).measurable.comp
    (measurable_oneStepDirichletSlopeL2_potentialShellIndexSigma_Ioi
      M n h p Q hh)

theorem measurable_oneStepNeumannCellSlope_potentialShellIndexSigma_Ioi
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (Vec d)
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (oneStepNeumannCellSlope M n h q Q R · hh) :=
  (continuous_oneStepCellMeanVec Q R).measurable.comp
    (measurable_oneStepNeumannSlopeL2_potentialShellIndexSigma_Ioi
      M n h q Q hh)

/-- Exact prefix/suffix factorization of a random coarse-matrix quadratic
with a suffix-measurable random slope. -/
theorem integral_vecDot_randomAMatrix_suffix_eq
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n : ℕ) (U : Ch02.Domain d) (p : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d)
    (hp : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (Vec d)
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance p)
    (hpInt : ∀ i j : Fin d,
      Integrable (fun omega ↦ p omega i * p omega j) M.P.toMeasure) :
    ∫ omega, vecDot (p omega)
        (matVecMul (randomAMatrix M n U omega) (p omega)) ∂M.P.toMeasure =
      ∑ i : Fin d, ∑ j : Fin d,
        abar M n U i j * ∫ omega, p omega i * p omega j ∂M.P.toMeasure := by
  have hdisjoint : Disjoint (Set.Iic n) (Set.Ioi n) :=
    Set.Iic_disjoint_Ioi le_rfl
  have hAmeas := measurable_randomAMatrix_potentialShellIndexSigma_Iic M n U
  have hentryMeas : ∀ i j : Fin d,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        (potentialShellIndexSigma (Set.Iic n)) inferInstance
        (fun omega ↦ randomAMatrix M n U omega i j) := by
    intro i j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hAmeas)
  have hpPairMeas : ∀ i j : Fin d,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        (potentialShellIndexSigma (Set.Ioi n)) inferInstance
        (fun omega ↦ p omega i * p omega j) := by
    intro i j
    exact ((measurable_pi_apply i).comp hp).mul
      ((measurable_pi_apply j).comp hp)
  have hindep : ∀ i j : Fin d,
      IndepFun (fun omega ↦ randomAMatrix M n U omega i j)
        (fun omega ↦ p omega i * p omega j) M.P.toMeasure := by
    intro i j
    exact indepFun_of_measurable_potentialShellIndexSigma_of_disjoint
      M hdisjoint (hentryMeas i j) (hpPairMeas i j)
  have hentryInt : ∀ i j : Fin d,
      Integrable (fun omega ↦ randomAMatrix M n U omega i j) M.P.toMeasure := by
    intro i j
    exact ((integrable_randomAMatrix M n U).eval i).eval j
  have htermInt : ∀ i j : Fin d,
      Integrable (fun omega ↦ randomAMatrix M n U omega i j *
        (p omega i * p omega j)) M.P.toMeasure := by
    intro i j
    exact (hindep i j).integrable_mul (hentryInt i j) (hpInt i j)
  have hquad : (fun omega ↦ vecDot (p omega)
      (matVecMul (randomAMatrix M n U omega) (p omega))) =
      fun omega ↦ ∑ i : Fin d, ∑ j : Fin d,
        randomAMatrix M n U omega i j * (p omega i * p omega j) := by
    funext omega
    simp only [vecDot, matVecMul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hquad, integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro j _hj
      rw [(hindep i j).integral_fun_mul_eq_mul_integral
        ((hentryMeas i j).mono
          (potentialShellIndexSigma_le_borel (d := d) (Set.Iic n))
          le_rfl).aestronglyMeasurable
        ((hpPairMeas i j).mono
          (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n))
          le_rfl).aestronglyMeasurable]
      rw [abar, Homogenization.integral_matrix_apply
        (integrable_randomAMatrix M n U) i j]
    · exact fun j _hj ↦ htermInt i j
  · intro i _hi
    exact integrable_finsetSum Finset.univ fun j _hj ↦ htermInt i j

/-- Exact prefix/suffix factorization with an additional suffix-measurable
scalar weight.  This is the probability interface for the Step 3 principal
cell energy: the cutoff-ratio supremum and the cell slope both read only the
fresh block, while the coarse matrix reads only the prefix. -/
theorem integral_weight_mul_vecDot_randomAMatrix_suffix_eq
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n : ℕ) (U : Ch02.Domain d) (weight : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ)
    (p : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d)
    (hweight : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance weight)
    (hp : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (Vec d)
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance p)
    (hweightedPairInt : ∀ i j : Fin d,
      Integrable (fun omega ↦ weight omega * (p omega i * p omega j))
        M.P.toMeasure) :
    ∫ omega, weight omega * vecDot (p omega)
        (matVecMul (randomAMatrix M n U omega) (p omega)) ∂M.P.toMeasure =
      ∑ i : Fin d, ∑ j : Fin d,
        abar M n U i j *
          ∫ omega, weight omega * (p omega i * p omega j)
            ∂M.P.toMeasure := by
  have hdisjoint : Disjoint (Set.Iic n) (Set.Ioi n) :=
    Set.Iic_disjoint_Ioi le_rfl
  have hAmeas := measurable_randomAMatrix_potentialShellIndexSigma_Iic M n U
  have hentryMeas : ∀ i j : Fin d,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        (potentialShellIndexSigma (Set.Iic n)) inferInstance
        (fun omega ↦ randomAMatrix M n U omega i j) := by
    intro i j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hAmeas)
  have hweightedPairMeas : ∀ i j : Fin d,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
        (potentialShellIndexSigma (Set.Ioi n)) inferInstance
        (fun omega ↦ weight omega * (p omega i * p omega j)) := by
    intro i j
    exact hweight.mul <|
      ((measurable_pi_apply i).comp hp).mul ((measurable_pi_apply j).comp hp)
  have hindep : ∀ i j : Fin d,
      IndepFun (fun omega ↦ randomAMatrix M n U omega i j)
        (fun omega ↦ weight omega * (p omega i * p omega j))
        M.P.toMeasure := by
    intro i j
    exact indepFun_of_measurable_potentialShellIndexSigma_of_disjoint
      M hdisjoint (hentryMeas i j) (hweightedPairMeas i j)
  have hentryInt : ∀ i j : Fin d,
      Integrable (fun omega ↦ randomAMatrix M n U omega i j)
        M.P.toMeasure := by
    intro i j
    exact ((integrable_randomAMatrix M n U).eval i).eval j
  have htermInt : ∀ i j : Fin d,
      Integrable (fun omega ↦ randomAMatrix M n U omega i j *
        (weight omega * (p omega i * p omega j))) M.P.toMeasure := by
    intro i j
    exact (hindep i j).integrable_mul (hentryInt i j)
      (hweightedPairInt i j)
  have hquad : (fun omega ↦ weight omega * vecDot (p omega)
      (matVecMul (randomAMatrix M n U omega) (p omega))) =
      fun omega ↦ ∑ i : Fin d, ∑ j : Fin d,
        randomAMatrix M n U omega i j *
          (weight omega * (p omega i * p omega j)) := by
    funext omega
    simp only [vecDot, matVecMul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hquad, integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro j _hj
      rw [(hindep i j).integral_fun_mul_eq_mul_integral
        ((hentryMeas i j).mono
          (potentialShellIndexSigma_le_borel (d := d) (Set.Iic n))
          le_rfl).aestronglyMeasurable
        ((hweightedPairMeas i j).mono
          (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n))
          le_rfl).aestronglyMeasurable]
      rw [abar, Homogenization.integral_matrix_apply
        (integrable_randomAMatrix M n U) i j]
    · exact fun j _hj ↦ htermInt i j
  · intro i _hi
    exact integrable_finsetSum Finset.univ fun j _hj ↦ htermInt i j

/-- Scalar form of the weighted prefix/suffix factorization on a translated
triadic cell. -/
theorem integral_weight_mul_vecDot_randomAMatrix_suffix_eq_scalarReadout_mul
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n : ℕ) (Q : TriadicCube d) (hQscale : 0 ≤ Q.scale)
    (weight : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) (p : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d)
    (hweight : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance weight)
    (hp : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (Vec d)
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance p)
    (hweightedPairInt : ∀ i j : Fin d,
      Integrable (fun omega ↦ weight omega * (p omega i * p omega j))
        M.P.toMeasure) :
    ∫ omega, weight omega * vecDot (p omega)
        (matVecMul (randomAMatrix M n (Ch02.cubeDomain Q) omega) (p omega))
        ∂M.P.toMeasure =
      abarScalarReadout M n Q.scale.toNat *
        ∫ omega, weight omega * vecNormSq (p omega) ∂M.P.toMeasure := by
  rw [integral_weight_mul_vecDot_randomAMatrix_suffix_eq M n
    (Ch02.cubeDomain Q) weight p hweight hp hweightedPairInt]
  rw [abar_cube_eq_originCube M n Q]
  have hscale : ((Q.scale.toNat : ℕ) : ℤ) = Q.scale := by
    rw [Int.toNat_of_nonneg hQscale]
  rw [show originCube d Q.scale = originCube d (Q.scale.toNat : ℤ) by
    rw [hscale]]
  rw [abar_eq_abarScalarReadout_smul_one M n Q.scale.toNat]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, ite_mul,
    mul_one, mul_zero, zero_mul, Fintype.sum_ite_eq]
  rw [← Finset.mul_sum]
  congr 1
  change (∑ i : Fin d,
      ∫ omega, weight omega * (p omega i * p omega i) ∂M.P.toMeasure) =
    ∫ omega, weight omega * ∑ i : Fin d, p omega i * p omega i
      ∂M.P.toMeasure
  have hfun : (fun omega ↦ weight omega *
      ∑ i : Fin d, p omega i * p omega i) =
      fun omega ↦ ∑ i : Fin d,
        weight omega * (p omega i * p omega i) := by
    funext omega
    rw [Finset.mul_sum]
  rw [hfun, integral_finsetSum]
  exact fun i _hi ↦ hweightedPairInt i i

/-- On a translated triadic cell, suffix measurability and G3 scalarity turn
the random coarse quadratic into the centered scalar readout times the slope
second moment. -/
theorem integral_vecDot_randomAMatrix_suffix_eq_scalarReadout_mul
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n : ℕ) (Q : TriadicCube d) (hQscale : 0 ≤ Q.scale)
    (p : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d)
    (hp : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) (Vec d)
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance p)
    (hpL2 : ∀ i : Fin d,
      MemLp (fun omega ↦ p omega i) 2 M.P.toMeasure) :
    ∫ omega, vecDot (p omega)
        (matVecMul (randomAMatrix M n (Ch02.cubeDomain Q) omega) (p omega))
        ∂M.P.toMeasure =
      abarScalarReadout M n Q.scale.toNat *
        ∫ omega, vecNormSq (p omega) ∂M.P.toMeasure := by
  have hpInt : ∀ i j : Fin d,
      Integrable (fun omega ↦ p omega i * p omega j) M.P.toMeasure := by
    intro i j
    exact (hpL2 i).integrable_mul (hpL2 j)
  rw [integral_vecDot_randomAMatrix_suffix_eq M n
    (Ch02.cubeDomain Q) p hp hpInt]
  rw [abar_cube_eq_originCube M n Q]
  have hscale : ((Q.scale.toNat : ℕ) : ℤ) = Q.scale := by
    rw [Int.toNat_of_nonneg hQscale]
  rw [show originCube d Q.scale = originCube d (Q.scale.toNat : ℤ) by
    rw [hscale]]
  rw [abar_eq_abarScalarReadout_smul_one M n Q.scale.toNat]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, ite_mul,
    mul_one, mul_zero, zero_mul, Fintype.sum_ite_eq]
  rw [← Finset.mul_sum]
  congr 1
  change (∑ i : Fin d,
      ∫ omega, p omega i * p omega i ∂M.P.toMeasure) =
    ∫ omega, ∑ i : Fin d, p omega i * p omega i ∂M.P.toMeasure
  rw [integral_finsetSum]
  intro i _hi
  exact hpInt i i

/-- Primal source-cell specialization of the scalar prefix/suffix
factorization. -/
theorem integral_dirichletCellSlope_randomAMatrix_eq_scalarReadout_mul
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q R : TriadicCube d) (hRscale : 0 ≤ R.scale)
    (hh : 0 < h)
    (hpL2 : ∀ i : Fin d,
      MemLp (fun omega ↦
        oneStepDirichletCellSlope M n h p Q R omega hh i)
        2 M.P.toMeasure) :
    ∫ omega,
        vecDot (oneStepDirichletCellSlope M n h p Q R omega hh)
          (matVecMul (randomAMatrix M n (Ch02.cubeDomain R) omega)
            (oneStepDirichletCellSlope M n h p Q R omega hh))
        ∂M.P.toMeasure =
      abarScalarReadout M n R.scale.toNat *
        ∫ omega, vecNormSq
          (oneStepDirichletCellSlope M n h p Q R omega hh)
          ∂M.P.toMeasure := by
  exact integral_vecDot_randomAMatrix_suffix_eq_scalarReadout_mul
    M n R hRscale (oneStepDirichletCellSlope M n h p Q R · hh)
      (measurable_oneStepDirichletCellSlope_potentialShellIndexSigma_Ioi
        M n h p Q R hh) hpL2

/-- Dual source-cell specialization of the scalar prefix/suffix
factorization. -/
theorem integral_neumannCellSlope_randomAMatrix_eq_scalarReadout_mul
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (hRscale : 0 ≤ R.scale)
    (hh : 0 < h)
    (hqL2 : ∀ i : Fin d,
      MemLp (fun omega ↦
        oneStepNeumannCellSlope M n h q Q R omega hh i)
        2 M.P.toMeasure) :
    ∫ omega,
        vecDot (oneStepNeumannCellSlope M n h q Q R omega hh)
          (matVecMul (randomAMatrix M n (Ch02.cubeDomain R) omega)
            (oneStepNeumannCellSlope M n h q Q R omega hh))
        ∂M.P.toMeasure =
      abarScalarReadout M n R.scale.toNat *
        ∫ omega, vecNormSq
          (oneStepNeumannCellSlope M n h q Q R omega hh)
          ∂M.P.toMeasure := by
  exact integral_vecDot_randomAMatrix_suffix_eq_scalarReadout_mul
    M n R hRscale (oneStepNeumannCellSlope M n h q Q R · hh)
      (measurable_oneStepNeumannCellSlope_potentialShellIndexSigma_Ioi
        M n h q Q R hh) hqL2



def oneStepSourceCells (d K n : ℕ) (delta : ℝ) :
    Finset (TriadicCube d) :=
  descendantsAtDepth (originCube d (K : ℤ))
    (K - oneStepLocalizationScale n delta)

theorem oneStepSourceCells_nonempty (d K n : ℕ) (delta : ℝ) :
    (oneStepSourceCells d K n delta).Nonempty := by
  exact descendantsAtDepth_nonempty _ _

theorem mem_oneStepSourceCells {d K n : ℕ} {delta : ℝ}
    {R : TriadicCube d} (hR : R ∈ oneStepSourceCells d K n delta) :
    R ∈ descendantsAtDepth (originCube d (K : ℤ))
      (K - oneStepLocalizationScale n delta) :=
  hR

/-- Every member of the common partition has exactly the manuscript's source
scale once that scale is contained in the parent cube. -/
theorem oneStepSourceCells_scale_eq
    {d K n : ℕ} {delta : ℝ} {R : TriadicCube d}
    (hsource : oneStepLocalizationScale n delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n delta) :
    R.scale = (oneStepLocalizationScale n delta : ℤ) := by
  have hscale := scale_eq_sub_of_mem_descendantsAtDepth
    (mem_oneStepSourceCells hR)
  simp only [originCube] at hscale
  rw [hscale]
  omega

theorem oneStepSourceCells_scale_toNat_eq
    {d K n : ℕ} {delta : ℝ} {R : TriadicCube d}
    (hsource : oneStepLocalizationScale n delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n delta) :
    R.scale.toNat = oneStepLocalizationScale n delta := by
  rw [oneStepSourceCells_scale_eq hsource hR]
  simp

theorem oneStepSourceCells_scale_nonneg
    {d K n : ℕ} {delta : ℝ} {R : TriadicCube d}
    (hsource : oneStepLocalizationScale n delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n delta) :
    0 ≤ R.scale := by
  rw [oneStepSourceCells_scale_eq hsource hR]
  exact Int.natCast_nonneg _

/-- Every primal member of the literal source partition has the same
deterministic scalar coarse coefficient after prefix/suffix factorization. -/
theorem integral_dirichletSourceCellSlope_randomAMatrix_eq_commonReadout_mul
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (R : TriadicCube d)
    (hsource : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (hh : 0 < h)
    (hpL2 : ∀ i : Fin d,
      MemLp (fun omega ↦ oneStepDirichletCellSlope M n h p
        (originCube d (K : ℤ)) R omega hh i) 2 M.P.toMeasure) :
    ∫ omega,
        vecDot (oneStepDirichletCellSlope M n h p
          (originCube d (K : ℤ)) R omega hh)
          (matVecMul (randomAMatrix M n (Ch02.cubeDomain R) omega)
            (oneStepDirichletCellSlope M n h p
              (originCube d (K : ℤ)) R omega hh))
        ∂M.P.toMeasure =
      abarScalarReadout M n (oneStepLocalizationScale n M.delta) *
        ∫ omega, vecNormSq (oneStepDirichletCellSlope M n h p
          (originCube d (K : ℤ)) R omega hh) ∂M.P.toMeasure := by
  rw [integral_dirichletCellSlope_randomAMatrix_eq_scalarReadout_mul
    M n h p (originCube d (K : ℤ)) R
      (oneStepSourceCells_scale_nonneg hsource hR) hh hpL2]
  rw [oneStepSourceCells_scale_toNat_eq hsource hR]

/-- Dual copy of the common source-cell scalar factorization. -/
theorem integral_neumannSourceCellSlope_randomAMatrix_eq_commonReadout_mul
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (R : TriadicCube d)
    (hsource : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (hh : 0 < h)
    (hqL2 : ∀ i : Fin d,
      MemLp (fun omega ↦ oneStepNeumannCellSlope M n h q
        (originCube d (K : ℤ)) R omega hh i) 2 M.P.toMeasure) :
    ∫ omega,
        vecDot (oneStepNeumannCellSlope M n h q
          (originCube d (K : ℤ)) R omega hh)
          (matVecMul (randomAMatrix M n (Ch02.cubeDomain R) omega)
            (oneStepNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh))
        ∂M.P.toMeasure =
      abarScalarReadout M n (oneStepLocalizationScale n M.delta) *
        ∫ omega, vecNormSq (oneStepNeumannCellSlope M n h q
          (originCube d (K : ℤ)) R omega hh) ∂M.P.toMeasure := by
  rw [integral_neumannCellSlope_randomAMatrix_eq_scalarReadout_mul
    M n h q (originCube d (K : ℤ)) R
      (oneStepSourceCells_scale_nonneg hsource hR) hh hqL2]
  rw [oneStepSourceCells_scale_toNat_eq hsource hR]

/-- Unit-probe primal source-cell factorization with its random `L²`
premise discharged by the measurable solution-operator moment bounds. -/
theorem integral_dirichletSourceCellSlope_randomAMatrix_eq_commonReadout_mul_of_unit
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (R : TriadicCube d)
    (hsource : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (hh : 0 < h) (hp : vecNormSq p = 1) :
    ∫ omega,
        vecDot (oneStepDirichletCellSlope M n h p
          (originCube d (K : ℤ)) R omega hh)
          (matVecMul (randomAMatrix M n (Ch02.cubeDomain R) omega)
            (oneStepDirichletCellSlope M n h p
              (originCube d (K : ℤ)) R omega hh))
        ∂M.P.toMeasure =
      abarScalarReadout M n (oneStepLocalizationScale n M.delta) *
        ∫ omega, vecNormSq (oneStepDirichletCellSlope M n h p
          (originCube d (K : ℤ)) R omega hh) ∂M.P.toMeasure := by
  exact integral_dirichletSourceCellSlope_randomAMatrix_eq_commonReadout_mul
    M n h p R hsource hR hh fun i ↦
      memLp_two_oneStepDirichletCellSlope_coord M n h p
        (originCube d (K : ℤ)) R hh hp i

/-- Unit-probe dual source-cell factorization, with no residual
integrability premise. -/
theorem integral_neumannSourceCellSlope_randomAMatrix_eq_commonReadout_mul_of_unit
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (R : TriadicCube d)
    (hsource : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    ∫ omega,
        vecDot (oneStepNeumannCellSlope M n h q
          (originCube d (K : ℤ)) R omega hh)
          (matVecMul (randomAMatrix M n (Ch02.cubeDomain R) omega)
            (oneStepNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh))
        ∂M.P.toMeasure =
      abarScalarReadout M n (oneStepLocalizationScale n M.delta) *
        ∫ omega, vecNormSq (oneStepNeumannCellSlope M n h q
          (originCube d (K : ℤ)) R omega hh) ∂M.P.toMeasure := by
  exact integral_neumannSourceCellSlope_randomAMatrix_eq_commonReadout_mul
    M n h q R hsource hR hh fun i ↦
      memLp_two_oneStepNeumannCellSlope_coord M n h q
        (originCube d (K : ℤ)) R hh hq i

/-- The literal upper Step 3 cell weight: the supremum of the fresh cutoff
ratio on the source cell. -/
def oneStepUpperSourceCellWeight {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (R : TriadicCube d) : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
  cutoffRatioSup M (n + h) n (Ch02.cubeDomain R)

/-- The reciprocal fresh-cutoff weight used in the lower Step 3 argument. -/
def oneStepLowerSourceCellWeight {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (R : TriadicCube d) : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
  cutoffRatioSup M n (n + h) (Ch02.cubeDomain R)

theorem cutoffRatio_le_oneStepUpperSourceCellWeight
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {x : Vec d} (hx : x ∈ openCubeSet R) :
    _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M n omega x ≤
      oneStepUpperSourceCellWeight M n h R omega := by
  exact cutoffRatio_le_cutoffRatioSup M (n + h) n
    (Ch02.cubeDomain R) omega (by
      simpa only [Ch02.cubeDomain_coe] using! hx)

theorem cutoffRatio_le_oneStepLowerSourceCellWeight
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {x : Vec d} (hx : x ∈ openCubeSet R) :
    _root_.SubdiffusiveProcess.Model.aCutoff M n omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x ≤
      oneStepLowerSourceCellWeight M n h R omega := by
  exact cutoffRatio_le_cutoffRatioSup M n (n + h)
    (Ch02.cubeDomain R) omega (by
      simpa only [Ch02.cubeDomain_coe] using! hx)

theorem measurable_oneStepUpperSourceCellWeight_potentialShellIndexSigma_Ioi
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (hh : 0 < h) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (oneStepUpperSourceCellWeight M n h R) := by
  exact (measurable_cutoffRatioSup_potentialShellIndexSigma_Ioi M
    (Nat.lt_add_of_pos_right hh) (Ch02.cubeDomain R)).1

theorem measurable_oneStepLowerSourceCellWeight_potentialShellIndexSigma_Ioi
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (hh : 0 < h) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (oneStepLowerSourceCellWeight M n h R) := by
  exact (measurable_cutoffRatioSup_potentialShellIndexSigma_Ioi M
    (Nat.lt_add_of_pos_right hh) (Ch02.cubeDomain R)).2

theorem memLp_two_oneStepUpperSourceCellWeight
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (hh : 0 < h) :
    MemLp (oneStepUpperSourceCellWeight M n h R) 2 M.P.toMeasure := by
  exact memLp_two_cutoffRatioSup_forward M (Nat.lt_add_of_pos_right hh)
    (Ch02.cubeDomain R)

theorem memLp_two_oneStepLowerSourceCellWeight
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (R : TriadicCube d) (hh : 0 < h) :
    MemLp (oneStepLowerSourceCellWeight M n h R) 2 M.P.toMeasure := by
  exact memLp_two_cutoffRatioSup_inverse M (Nat.lt_add_of_pos_right hh)
    (Ch02.cubeDomain R)

/-- Weighted primal prefix/suffix factorization on a literal source cell,
with every measurability and integrability premise discharged. -/
theorem integral_upperWeight_mul_dirichletSourceCellSlope_randomAMatrix_eq
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (R : TriadicCube d)
    (hsource : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (hh : 0 < h) (hp : vecNormSq p = 1) :
    ∫ omega,
        oneStepUpperSourceCellWeight M n h R omega *
          vecDot (oneStepDirichletCellSlope M n h p
            (originCube d (K : ℤ)) R omega hh)
            (matVecMul (randomAMatrix M n (Ch02.cubeDomain R) omega)
              (oneStepDirichletCellSlope M n h p
                (originCube d (K : ℤ)) R omega hh))
        ∂M.P.toMeasure =
      abarScalarReadout M n (oneStepLocalizationScale n M.delta) *
        ∫ omega,
          oneStepUpperSourceCellWeight M n h R omega *
            vecNormSq (oneStepDirichletCellSlope M n h p
              (originCube d (K : ℤ)) R omega hh)
          ∂M.P.toMeasure := by
  rw [integral_weight_mul_vecDot_randomAMatrix_suffix_eq_scalarReadout_mul
    M n R (oneStepSourceCells_scale_nonneg hsource hR)
      (oneStepUpperSourceCellWeight M n h R)
      (oneStepDirichletCellSlope M n h p
        (originCube d (K : ℤ)) R · hh)
      (measurable_oneStepUpperSourceCellWeight_potentialShellIndexSigma_Ioi
        M n h R hh)
      (measurable_oneStepDirichletCellSlope_potentialShellIndexSigma_Ioi
        M n h p (originCube d (K : ℤ)) R hh)
      (fun i j ↦ integrable_weight_mul_pair_of_memLp_two_four M
        (oneStepUpperSourceCellWeight M n h R)
        (oneStepDirichletCellSlope M n h p
          (originCube d (K : ℤ)) R · hh)
        (memLp_two_oneStepUpperSourceCellWeight M n h R hh)
        (fun k ↦ memLp_four_oneStepDirichletCellSlope_coord M n h p
          (originCube d (K : ℤ)) R hh hp k) i j)]
  rw [oneStepSourceCells_scale_toNat_eq hsource hR]

/-- Weighted dual prefix/suffix factorization on the same source family. -/
theorem integral_lowerWeight_mul_neumannSourceCellSlope_randomAMatrix_eq
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (R : TriadicCube d)
    (hsource : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    ∫ omega,
        oneStepLowerSourceCellWeight M n h R omega *
          vecDot (oneStepNeumannCellSlope M n h q
            (originCube d (K : ℤ)) R omega hh)
            (matVecMul (randomAMatrix M n (Ch02.cubeDomain R) omega)
              (oneStepNeumannCellSlope M n h q
                (originCube d (K : ℤ)) R omega hh))
        ∂M.P.toMeasure =
      abarScalarReadout M n (oneStepLocalizationScale n M.delta) *
        ∫ omega,
          oneStepLowerSourceCellWeight M n h R omega *
            vecNormSq (oneStepNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh)
          ∂M.P.toMeasure := by
  rw [integral_weight_mul_vecDot_randomAMatrix_suffix_eq_scalarReadout_mul
    M n R (oneStepSourceCells_scale_nonneg hsource hR)
      (oneStepLowerSourceCellWeight M n h R)
      (oneStepNeumannCellSlope M n h q
        (originCube d (K : ℤ)) R · hh)
      (measurable_oneStepLowerSourceCellWeight_potentialShellIndexSigma_Ioi
        M n h R hh)
      (measurable_oneStepNeumannCellSlope_potentialShellIndexSigma_Ioi
        M n h q (originCube d (K : ℤ)) R hh)
      (fun i j ↦ integrable_weight_mul_pair_of_memLp_two_four M
        (oneStepLowerSourceCellWeight M n h R)
        (oneStepNeumannCellSlope M n h q
          (originCube d (K : ℤ)) R · hh)
        (memLp_two_oneStepLowerSourceCellWeight M n h R hh)
        (fun k ↦ memLp_four_oneStepNeumannCellSlope_coord M n h q
          (originCube d (K : ℤ)) R hh hq k) i j)]
  rw [oneStepSourceCells_scale_toNat_eq hsource hR]

/-- The weighted primal principal sum over the common source partition has a
single deterministic coarse coefficient. -/
theorem normalized_sum_integral_upperWeight_mul_dirichletSourceCellSlope_eq
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (hsource : oneStepLocalizationScale n M.delta ≤ K)
    (hh : 0 < h) (hp : vecNormSq p = 1) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega,
            oneStepUpperSourceCellWeight M n h R omega *
              vecDot (oneStepDirichletCellSlope M n h p
                (originCube d (K : ℤ)) R omega hh)
                (matVecMul (randomAMatrix M n (Ch02.cubeDomain R) omega)
                  (oneStepDirichletCellSlope M n h p
                    (originCube d (K : ℤ)) R omega hh))
            ∂M.P.toMeasure =
      abarScalarReadout M n (oneStepLocalizationScale n M.delta) *
        ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega,
              oneStepUpperSourceCellWeight M n h R omega *
                vecNormSq (oneStepDirichletCellSlope M n h p
                  (originCube d (K : ℤ)) R omega hh)
              ∂M.P.toMeasure) := by
  rw [Finset.sum_congr rfl (fun R hR ↦
    integral_upperWeight_mul_dirichletSourceCellSlope_randomAMatrix_eq
      M n h p R hsource hR hh hp)]
  rw [← Finset.mul_sum]
  ring

/-- Dual weighted principal sum over the common source partition. -/
theorem normalized_sum_integral_lowerWeight_mul_neumannSourceCellSlope_eq
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (hsource : oneStepLocalizationScale n M.delta ≤ K)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega,
            oneStepLowerSourceCellWeight M n h R omega *
              vecDot (oneStepNeumannCellSlope M n h q
                (originCube d (K : ℤ)) R omega hh)
                (matVecMul (randomAMatrix M n (Ch02.cubeDomain R) omega)
                  (oneStepNeumannCellSlope M n h q
                    (originCube d (K : ℤ)) R omega hh))
            ∂M.P.toMeasure =
      abarScalarReadout M n (oneStepLocalizationScale n M.delta) *
        ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega,
              oneStepLowerSourceCellWeight M n h R omega *
                vecNormSq (oneStepNeumannCellSlope M n h q
                  (originCube d (K : ℤ)) R omega hh)
              ∂M.P.toMeasure) := by
  rw [Finset.sum_congr rfl (fun R hR ↦
    integral_lowerWeight_mul_neumannSourceCellSlope_randomAMatrix_eq
      M n h q R hsource hR hh hq)]
  rw [← Finset.mul_sum]
  ring

/-- The normalized primal principal sum has one common deterministic coarse
coefficient.  This is the finite-family form inserted before the Step 3
replacement estimate. -/
theorem normalized_sum_integral_dirichletSourceCellSlope_randomAMatrix_eq
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (hsource : oneStepLocalizationScale n M.delta ≤ K)
    (hh : 0 < h) (hp : vecNormSq p = 1) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega,
            vecDot (oneStepDirichletCellSlope M n h p
              (originCube d (K : ℤ)) R omega hh)
              (matVecMul (randomAMatrix M n (Ch02.cubeDomain R) omega)
                (oneStepDirichletCellSlope M n h p
                  (originCube d (K : ℤ)) R omega hh))
            ∂M.P.toMeasure =
      abarScalarReadout M n (oneStepLocalizationScale n M.delta) *
        ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, vecNormSq (oneStepDirichletCellSlope M n h p
              (originCube d (K : ℤ)) R omega hh) ∂M.P.toMeasure) := by
  rw [Finset.sum_congr rfl (fun R hR ↦
    integral_dirichletSourceCellSlope_randomAMatrix_eq_commonReadout_mul_of_unit
      M n h p R hsource hR hh hp)]
  rw [← Finset.mul_sum]
  ring

/-- Dual common-coefficient finite-family identity. -/
theorem normalized_sum_integral_neumannSourceCellSlope_randomAMatrix_eq
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (hsource : oneStepLocalizationScale n M.delta ≤ K)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega,
            vecDot (oneStepNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh)
              (matVecMul (randomAMatrix M n (Ch02.cubeDomain R) omega)
                (oneStepNeumannCellSlope M n h q
                  (originCube d (K : ℤ)) R omega hh))
            ∂M.P.toMeasure =
      abarScalarReadout M n (oneStepLocalizationScale n M.delta) *
        ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, vecNormSq (oneStepNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh) ∂M.P.toMeasure) := by
  rw [Finset.sum_congr rfl (fun R hR ↦
    integral_neumannSourceCellSlope_randomAMatrix_eq_commonReadout_mul_of_unit
      M n h q R hsource hR hh hq)]
  rw [← Finset.mul_sum]
  ring

/-- The cellwise constant mean of a parent gradient. -/
def oneStepCellMeanField {d : ℕ} (R : TriadicCube d)
    {U : Set (Vec d)} (u : H1Function U) : Vec d → Vec d :=
  fun _ ↦ cubeAverageVec R u.grad

/-- The centered cell fluctuation of a parent gradient. -/
def oneStepCellFluctuationField {d : ℕ} (R : TriadicCube d)
    {U : Set (Vec d)} (u : H1Function U) : Vec d → Vec d :=
  cubeFluctuationVec R u.grad

theorem oneStepCellMean_add_fluctuation {d : ℕ} (R : TriadicCube d)
    {U : Set (Vec d)} (u : H1Function U) (x : Vec d) :
    oneStepCellMeanField R u x + oneStepCellFluctuationField R u x =
      u.grad x := by
  simp only [oneStepCellMeanField, oneStepCellFluctuationField,
    cubeFluctuationVec_apply]
  abel

theorem oneStepCellMeanField_memVectorL2 {d : ℕ} (R : TriadicCube d)
    {U : Set (Vec d)} (u : H1Function U) :
    MemVectorL2 (openCubeSet R) (oneStepCellMeanField R u) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  unfold oneStepCellMeanField
  exact memVectorL2_const _

theorem oneStepCellFluctuationField_memVectorL2 {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (u : H1Function (openCubeSet Q)) :
    MemVectorL2 (openCubeSet R) (oneStepCellFluctuationField R u) := by
  have huQ : MemLp u.grad (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q
      u.grad_memVectorL2
  have huR : MemLp u.grad (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    memLp_on_descendant_of_memLp_generic hR huQ
  have hfluct : MemLp (oneStepCellFluctuationField R u)
      (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    exact memLp_cubeFluctuationVec R u.grad huR
  exact memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure R hfluct

theorem cubeAverageVec_oneStepCellFluctuationField_eq_zero {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j)
    (u : H1Function (openCubeSet Q)) :
    cubeAverageVec R (oneStepCellFluctuationField R u) = 0 := by
  have huQ : MemLp u.grad (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q
      u.grad_memVectorL2
  have huR : MemLp u.grad (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    memLp_on_descendant_of_memLp_generic hR huQ
  change cubeAverageVec R (fun x => u.grad x - cubeAverageVec R u.grad) = 0
  rw [cubeAverageVec_sub_const R u.grad (cubeAverageVec R u.grad) huR]
  simp

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
