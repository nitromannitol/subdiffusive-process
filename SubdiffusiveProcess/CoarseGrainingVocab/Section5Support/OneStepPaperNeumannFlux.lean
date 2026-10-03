module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepDualPrefixSuffix
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepDualBoundaryDiscard

@[expose] public section

/-!
# The correctly signed one-step Neumann flux

The measurable Neumann solver used by the one-step package solves the weak
equation with datum `-(exp H - 1) q`; its solution is therefore the negative
of the manuscript's `W`.  Consequently the manuscript flux
`exp(H) q - grad W` is represented by
`q + (exp H - 1) q + grad u`.
-/

open MeasureTheory Homogenization Homogenization.Book

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The literal flux `exp(H) q - grad W`, expressed through the package's
Neumann solution `u = -W`. -/
def oneStepPaperNeumannFlux {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    Vec d → Vec d :=
  fun x ↦ q + oneStepMultiplierAt M n h x omega • q +
    (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad x

/-- Hilbert-space realization of `oneStepPaperNeumannFlux`. -/
def oneStepPaperNeumannFluxL2 {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    HilbertVectorL2 (openCubeSet Q) :=
  oneStepConstantVectorL2 Q q + oneStepShellForcingL2 M n h q Q omega +
    (oneStepTriadicNeumannSolution M n h q Q omega hh).gradToHilbertVectorL2

theorem oneStepPaperNeumannFlux_memVectorL2 {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    MemVectorL2 (openCubeSet Q)
      (oneStepPaperNeumannFlux M n h q Q omega hh) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hforcing : MemVectorL2 (openCubeSet Q) (fun x ↦
      oneStepMultiplierAt M n h x omega • q) := by
    apply memVectorL2_openCubeSet_of_continuous Q
    have hc : Continuous (fun x : Vec d => oneStepMultiplierContinuousMap M n h omega x • q) :=
      (oneStepMultiplierContinuousMap M n h omega).continuous.smul continuous_const
    simpa only [oneStepMultiplierContinuousMap_apply M n h omega _ hh] using! hc
  exact ((memVectorL2_const q).add hforcing).add
    ((oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function
      |>.grad_memVectorL2)

theorem oneStepPaperNeumannFluxL2_eq_toHilbertVectorL2OfVecField
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    oneStepPaperNeumannFluxL2 M n h q Q omega hh =
      toHilbertVectorL2OfVecField
        (oneStepPaperNeumannFlux_memVectorL2 M n h q Q omega hh) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hforcing : MemVectorL2 (openCubeSet Q) (fun x ↦
      oneStepMultiplierAt M n h x omega • q) := by
    apply memVectorL2_openCubeSet_of_continuous Q
    have hc : Continuous (fun x : Vec d => oneStepMultiplierContinuousMap M n h omega x • q) :=
      (oneStepMultiplierContinuousMap M n h omega).continuous.smul continuous_const
    simpa only [oneStepMultiplierContinuousMap_apply M n h omega _ hh] using! hc
  have hadd := toHilbertVectorL2OfVecField_add (memVectorL2_const q) hforcing
  have haddGrad := toHilbertVectorL2OfVecField_add
    ((memVectorL2_const q).add hforcing)
    ((oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function
      |>.grad_memVectorL2)
  rw [oneStepPaperNeumannFluxL2, oneStepConstantVectorL2,
    H1MeanZeroFunction.gradToHilbertVectorL2,
    H1Function.gradToHilbertVectorL2,
    oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField M n h q Q omega hh,
    ]
  calc
    _ = (toHilbertVectorL2OfVecField ((memVectorL2_const q).add hforcing)) +
        toHilbertVectorL2OfVecField ((oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad_memVectorL2) := by
      congr 1
    _ = _ := haddGrad.symm

theorem memLp_four_oneStepPaperNeumannFluxL2
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) (hq : vecNormSq q = 1) :
    MemLp (oneStepPaperNeumannFluxL2 M n h q Q · hh)
      4 M.P.toMeasure := by
  have hconst : MemLp (fun _ : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d ↦ oneStepConstantVectorL2 Q q)
      4 M.P.toMeasure := memLp_const _
  have hforcing := memLp_four_oneStepShellForcingL2 M n h q Q hh
  have hgrad := memLp_four_oneStepTriadicNeumannGradL2 M n h q Q hh hq
  simpa only [oneStepPaperNeumannFluxL2, Pi.add_apply] using!
    (hconst.add hforcing).add hgrad

theorem memLp_two_oneStepPaperNeumannFluxL2
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) (hq : vecNormSq q = 1) :
    MemLp (oneStepPaperNeumannFluxL2 M n h q Q · hh)
      2 M.P.toMeasure :=
  (memLp_four_oneStepPaperNeumannFluxL2 M n h q Q hh hq).mono_exponent
    (by norm_num)

theorem measurable_oneStepPaperNeumannFluxL2_potentialShellIndexSigma_Ioi
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) :
    @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (HilbertVectorL2 (openCubeSet Q))
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (oneStepPaperNeumannFluxL2 M n h q Q · hh) := by
  letI : MeasurableSpace (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :=
    potentialShellIndexSigma (Set.Ioi n)
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  letI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  exact measurable_hilbertVectorL2_add
    (measurable_hilbertVectorL2_add measurable_const
      (measurable_oneStepShellForcingL2_potentialShellIndexSigma_Ioi
        M n h q Q hh))
    (measurable_oneStepTriadicNeumannGradL2_potentialShellIndexSigma_Ioi
      M n h q Q hh)

/-- Cell mean of the correctly signed manuscript flux. -/
def oneStepPaperNeumannCellSlope {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) : Vec d :=
  oneStepCellMeanVec Q R (oneStepPaperNeumannFluxL2 M n h q Q omega hh)

theorem measurable_oneStepPaperNeumannCellSlope_potentialShellIndexSigma_Ioi
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) :
    @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (Vec d)
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance
      (oneStepPaperNeumannCellSlope M n h q Q R · hh) :=
  (continuous_oneStepCellMeanVec Q R).measurable.comp
    (measurable_oneStepPaperNeumannFluxL2_potentialShellIndexSigma_Ioi
      M n h q Q hh)

theorem memLp_four_oneStepPaperNeumannCellSlope
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) (hq : vecNormSq q = 1) :
    MemLp (oneStepPaperNeumannCellSlope M n h q Q R · hh)
      4 M.P.toMeasure :=
  memLp_oneStepCellMeanVec_comp Q R
    (memLp_four_oneStepPaperNeumannFluxL2 M n h q Q hh hq)

theorem memLp_two_oneStepPaperNeumannCellSlope
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) (hq : vecNormSq q = 1) :
    MemLp (oneStepPaperNeumannCellSlope M n h q Q R · hh)
      2 M.P.toMeasure :=
  (memLp_four_oneStepPaperNeumannCellSlope M n h q Q R hh hq).mono_exponent
    (by norm_num)

theorem memLp_four_oneStepPaperNeumannCellSlope_coord
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (hh : 0 < h) (hq : vecNormSq q = 1)
    (i : Fin d) :
    MemLp (fun omega ↦
      oneStepPaperNeumannCellSlope M n h q Q R omega hh i)
      4 M.P.toMeasure :=
  (memLp_four_oneStepPaperNeumannCellSlope M n h q Q R hh hq
    ).continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)

/-- Constant source-cell mean of the manuscript flux. -/
def oneStepPaperNeumannCellMeanField {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    Vec d → Vec d :=
  fun _ ↦ oneStepPaperNeumannCellSlope M n h q Q R omega hh

/-- Centered source-cell fluctuation of the manuscript flux. -/
def oneStepPaperNeumannCellFluctuationField {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    Vec d → Vec d :=
  fun x ↦ oneStepPaperNeumannFlux M n h q Q omega hh x -
    oneStepPaperNeumannCellSlope M n h q Q R omega hh

@[simp] theorem oneStepPaperNeumannCellMean_add_fluctuation
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) (x : Vec d) :
    oneStepPaperNeumannCellMeanField M n h q Q R omega hh x +
        oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh x =
      oneStepPaperNeumannFlux M n h q Q omega hh x := by
  simp [oneStepPaperNeumannCellMeanField,
    oneStepPaperNeumannCellFluctuationField]

theorem oneStepPaperNeumannCellMeanField_memVectorL2
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    MemVectorL2 (openCubeSet R)
      (oneStepPaperNeumannCellMeanField M n h q Q R omega hh) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  exact memLp_const _

theorem oneStepPaperNeumannCellFluctuationField_memVectorL2
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h)
    (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    MemVectorL2 (openCubeSet R)
      (oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh) := by
  have hslope :=
    (oneStepPaperNeumannFlux_memVectorL2 M n h q Q omega hh).mono_measure
      (Measure.restrict_mono hRQ le_rfl)
  exact hslope.sub
    (oneStepPaperNeumannCellMeanField_memVectorL2 M n h q Q R omega hh)

theorem oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
    {d j : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R)
        (oneStepPaperNeumannCellMeanField M n h q Q R omega hh) := by
  intro R _hR
  exact oneStepPaperNeumannCellMeanField_memVectorL2 M n h q Q R omega hh

theorem oneStepPaperNeumannCellFluctuationField_memVectorL2_of_descendant
    {d j : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    ∀ R ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet R)
        (oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh) := by
  intro R hR
  exact oneStepPaperNeumannCellFluctuationField_memVectorL2
    M n h q Q R omega hh (openCubeSet_subset_of_mem_descendantsAtDepth hR)

theorem oneStepPaperNeumannCellSlope_eq_cubeAverageVec
    {d j : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q R : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h)
    (hR : R ∈ descendantsAtDepth Q j) :
    oneStepPaperNeumannCellSlope M n h q Q R omega hh =
      cubeAverageVec R (oneStepPaperNeumannFlux M n h q Q omega hh) := by
  unfold oneStepPaperNeumannCellSlope
  rw [oneStepPaperNeumannFluxL2_eq_toHilbertVectorL2OfVecField]
  exact oneStepCellMeanVec_toHilbertVectorL2OfVecField_eq_cubeAverageVec
    Q R (openCubeSet_subset_of_mem_descendantsAtDepth hR)
      (oneStepPaperNeumannFlux M n h q Q omega hh)
      (oneStepPaperNeumannFlux_memVectorL2 M n h q Q omega hh)

/-- The literal flux lies in the affine solenoidal zero-normal-trace class
used by the starred variational principle. -/
theorem oneStepPaperNeumannFlux_sub_const_zeroNormalTrace
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (fun x ↦ oneStepPaperNeumannFlux M n h q Q omega hh x - q) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  have hforcing : MemVectorL2 (openCubeSet Q) (fun x ↦
      -oneStepMultiplierAt M n h x omega • q) := by
    apply memVectorL2_openCubeSet_of_continuous Q
    have hc : Continuous (fun x : Vec d => -oneStepMultiplierContinuousMap M n h omega x • q) :=
      (oneStepMultiplierContinuousMap M n h omega).continuous.neg.smul continuous_const
    simpa only [oneStepMultiplierContinuousMap_apply M n h omega _ hh] using! hc
  have hresidual :=
    (oneStepTriadicNeumannSolution_isWeakSolution M n h q Q omega hh
      ).residual_zeroNormalTrace
        (isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q))
        hforcing
  convert hresidual using 1
  funext x
  simp only [oneStepPaperNeumannFlux, matVecMul_identityCoeffField]
  module

/-! ## Prefix/suffix factorization for the corrected cell slope -/

theorem integral_lowerWeight_mul_oneStepPaperNeumannCellSlope_randomAStarInv_eq
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (R : TriadicCube d)
    (hsource : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    ∫ omega,
        oneStepLowerSourceCellWeight M n h R omega *
          vecDot (oneStepPaperNeumannCellSlope M n h q
            (originCube d (K : ℤ)) R omega hh)
            (matVecMul ((randomAStarMatrix M n (Ch02.cubeDomain R) omega)⁻¹)
              (oneStepPaperNeumannCellSlope M n h q
                (originCube d (K : ℤ)) R omega hh))
        ∂M.P.toMeasure =
      oneStepAnnealedDualReadout M n (oneStepLocalizationScale n M.delta) *
        ∫ omega,
          oneStepLowerSourceCellWeight M n h R omega *
            vecNormSq (oneStepPaperNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh)
          ∂M.P.toMeasure := by
  rw [integral_weight_mul_vecDot_randomAStarInv_suffix_eq
    M n (Ch02.cubeDomain R)
      (oneStepLowerSourceCellWeight M n h R)
      (oneStepPaperNeumannCellSlope M n h q
        (originCube d (K : ℤ)) R · hh)
      (measurable_oneStepLowerSourceCellWeight_potentialShellIndexSigma_Ioi
        M n h R hh)
      (measurable_oneStepPaperNeumannCellSlope_potentialShellIndexSigma_Ioi
        M n h q (originCube d (K : ℤ)) R hh)
      (fun i j ↦ integrable_weight_mul_pair_of_memLp_two_four M
        (oneStepLowerSourceCellWeight M n h R)
        (oneStepPaperNeumannCellSlope M n h q
          (originCube d (K : ℤ)) R · hh)
        (memLp_two_oneStepLowerSourceCellWeight M n h R hh)
        (fun k ↦ memLp_four_oneStepPaperNeumannCellSlope_coord M n h q
          (originCube d (K : ℤ)) R hh hq k) i j)]
  rw [abarStarInv_cube_eq_annealedDualScalar_smul_one M n R
    (oneStepSourceCells_scale_nonneg hsource hR)]
  rw [oneStepSourceCells_scale_toNat_eq hsource hR]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    ite_mul, mul_one, mul_zero, zero_mul, Fintype.sum_ite_eq]
  rw [← Finset.mul_sum]
  congr 1
  change (∑ i : Fin d,
      ∫ omega, oneStepLowerSourceCellWeight M n h R omega *
        (oneStepPaperNeumannCellSlope M n h q
          (originCube d (K : ℤ)) R omega hh i *
        oneStepPaperNeumannCellSlope M n h q
          (originCube d (K : ℤ)) R omega hh i) ∂M.P.toMeasure) = _
  unfold vecNormSq vecDot
  rw [show (fun omega ↦
      oneStepLowerSourceCellWeight M n h R omega *
        ∑ i : Fin d,
          oneStepPaperNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh i *
            oneStepPaperNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh i) =
      fun omega ↦ ∑ i : Fin d,
        oneStepLowerSourceCellWeight M n h R omega *
          (oneStepPaperNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh i *
            oneStepPaperNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh i) by
    funext omega
    rw [Finset.mul_sum]]
  rw [integral_finset_sum]
  intro i _hi
  exact integrable_weight_mul_pair_of_memLp_two_four M
    (oneStepLowerSourceCellWeight M n h R)
    (oneStepPaperNeumannCellSlope M n h q
      (originCube d (K : ℤ)) R · hh)
    (memLp_two_oneStepLowerSourceCellWeight M n h R hh)
    (fun k ↦ memLp_four_oneStepPaperNeumannCellSlope_coord M n h q
      (originCube d (K : ℤ)) R hh hq k) i i

theorem normalized_sum_integral_lowerWeight_mul_oneStepPaperNeumannCellSlope_randomAStarInv_eq
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (hsource : oneStepLocalizationScale n M.delta ≤ K)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega,
            oneStepLowerSourceCellWeight M n h R omega *
              vecDot (oneStepPaperNeumannCellSlope M n h q
                (originCube d (K : ℤ)) R omega hh)
                (matVecMul ((randomAStarMatrix M n
                  (Ch02.cubeDomain R) omega)⁻¹)
                  (oneStepPaperNeumannCellSlope M n h q
                    (originCube d (K : ℤ)) R omega hh))
            ∂M.P.toMeasure =
      oneStepAnnealedDualReadout M n (oneStepLocalizationScale n M.delta) *
        ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega,
              oneStepLowerSourceCellWeight M n h R omega *
                vecNormSq (oneStepPaperNeumannCellSlope M n h q
                  (originCube d (K : ℤ)) R omega hh)
              ∂M.P.toMeasure) := by
  rw [Finset.sum_congr rfl (fun R hR ↦
    integral_lowerWeight_mul_oneStepPaperNeumannCellSlope_randomAStarInv_eq
      M n h q R hsource hR hh hq)]
  rw [← Finset.mul_sum]
  ring

/-! ## Retained-cell variational insertion -/

theorem mu_zero_right_eq_responseJ_aCutoff
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (Q : TriadicCube d) (r : Vec d) :
    Mu (openCubeSet Q) (0, r)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) =
      ResponseJ (openCubeSet Q) 0 r
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) := by
  let U : Ch02.Domain d := Ch02.cubeDomain Q
  let hdata := aCutoffCoeffOnData M L omega U
  calc
    Mu (openCubeSet Q) (0, r)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) =
        Ch02.doubledMu U hdata.toCoeffOn (0, r) := by
      rw [Ch02.doubledMu_eq_Mu]
      rfl
    _ = Ch02.responseJ U hdata.toCoeffOn 0 r := by
      rw [Ch02.responseJ_eq_doubledMu_neg_left_sub_vecDot]
      simp [vecDot]
    _ = ResponseJ (openCubeSet Q) 0 r
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) := by
      simpa only [U, Ch02.cubeDomain_coe, hdata, ScalarCoeffOnData.toCoeffOn]
        using! Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ
          U hdata.toCoeffOn 0 r

/-- Insert the correctly signed manuscript background into the existing
retained-cell dual gluing theorem.  The local mean and fluctuation families
sum exactly to the background on every retained cell. -/
theorem half_randomAStarMatrix_inv_quadratic_le_paperRetainedGluedEnergy
    {d j : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h)
    (s : Finset (TriadicCube d)) {lam Lam : ℝ}
    (hs : s ⊆ descendantsAtDepth Q j)
    (hEllParent : IsEllipticFieldOn lam Lam (openCubeSet Q)
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega)))
    (hEll : ∀ R ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet R)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega))) :
    (1 / 2 : ℝ) * vecDot q
        (matVecMul ((randomAStarMatrix M (n + h)
          (Ch02.cubeDomain Q) omega)⁻¹) q) ≤
      (1 / 2 : ℝ) * volumeAverage (openCubeSet Q) (fun x ↦
        let flux := oneStepSelectedRetainedGluedNeumannTwoFlux Q j s
          (scalarCoeffField
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega))
          (fun R ↦ oneStepPaperNeumannCellMeanField
            M n h q Q R omega hh)
          (fun R ↦ oneStepPaperNeumannCellFluctuationField
            M n h q Q R omega hh)
          (oneStepPaperNeumannFlux M n h q Q omega hh) hEll
          (oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
            M n h q Q omega hh)
          (oneStepPaperNeumannCellFluctuationField_memVectorL2_of_descendant
            M n h q Q omega hh) x
        vecDot flux
          (matVecMul ((blockMatrixOfCoeff
            (scalarCoeffField
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega) x)).lowerRight)
            flux)) := by
  apply half_randomAStarMatrix_inv_quadratic_le_retainedGluedEnergy
    M (n + h) omega Q j s
      (fun R ↦ oneStepPaperNeumannCellMeanField M n h q Q R omega hh)
      (fun R ↦ oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh)
      (oneStepPaperNeumannFlux M n h q Q omega hh) q hs hEllParent hEll
      (oneStepPaperNeumannCellMeanField_memVectorL2_of_descendant
        M n h q Q omega hh)
      (oneStepPaperNeumannCellFluctuationField_memVectorL2_of_descendant
        M n h q Q omega hh)
      (oneStepPaperNeumannFlux_memVectorL2 M n h q Q omega hh)
      (oneStepPaperNeumannFlux_sub_const_zeroNormalTrace
        M n h q Q omega hh)
      ⟨_, isCoarseBlockMatrix_ch02_aCutoff M (n + h) omega Q⟩
      (mu_zero_right_eq_responseJ_aCutoff M (n + h) omega Q)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
