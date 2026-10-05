module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepConcreteFiniteAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceCellEllipticityCovariance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCenteredVariance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepDescendantHessianMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceEllipticityFactors
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepAveragedBudgets
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceThermodynamic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFiniteReadoutComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepPrimalBoundaryDiscard
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFiniteMajorantAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepVariationalClosure
public import SubdiffusiveProcess.Providers.Section5.OneStepCanonicalCellPoincare

@[expose] public section

/-!
# Concrete primal source-cell closure

This file eliminates the samplewise-selected mixed-cutoff cell minimizers in
the upper one-step argument before expectation is taken.  It is the literal
finite-partition specialization.
-/

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Providers.Section5

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

def oneStepDirichletCellMinimizer_congrCoeff
    {d : ℕ} {R : Homogenization.TriadicCube d}
    {a b : CoeffField d} {F : Homogenization.Vec d → Homogenization.Vec d}
    (X : OneStepDirichletCellMinimizer R a F)
    (hab : a =ᵐ[volumeMeasureOn (openCubeSet R)] b) :
    OneStepDirichletCellMinimizer R b F where
  correction := X.correction
  weakSolution := by
    intro phi
    calc
      ∫ x in openCubeSet R,
          vecDot (matVecMul (b x) (X.correction.toH1Function.grad x))
            (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet R,
          vecDot (matVecMul (a x) (X.correction.toH1Function.grad x))
            (phi.toH1Function.grad x) ∂volume := by
          apply integral_congr_ae
          filter_upwards [hab] with x hx
          rw [hx]
      _ = ∫ x in openCubeSet R,
          vecDot (-matVecMul (a x) (F x))
            (phi.toH1Function.grad x) ∂volume := X.weakSolution phi
      _ = ∫ x in openCubeSet R,
          vecDot (-matVecMul (b x) (F x))
            (phi.toH1Function.grad x) ∂volume := by
          apply integral_congr_ae
          filter_upwards [hab] with x hx
          rw [hx]

private def primalLowData {d K : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (omega : Sample d) :
    OneStepDescendantEllipticityData M n
      (K - oneStepLocalizationScale n M.delta) omega
      (originCube d (K : ℤ)) :=
  oneStepDescendantEllipticityData M n _ omega _

private def primalHighData {d K : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : Sample d) :
    OneStepDescendantEllipticityData M (n + h)
      (K - oneStepLocalizationScale n M.delta) omega
      (originCube d (K : ℤ)) :=
  oneStepDescendantEllipticityData M (n + h) _ omega _

private def primalRawPrincipal {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d)
    (R : Homogenization.TriadicCube d) (omega : Sample d) (hh : 0 < h) : ℝ :=
  if hR : R ∈ oneStepSourceCells d K n M.delta then
    let Q := originCube d (K : ℤ)
    let low := primalLowData (K := K) M n omega
    let P := fun S ↦ oneStepDirichletCellMeanField M n h p Q S omega hh
    let X := oneStepSelectedDirichletCell
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
      P low.isElliptic
      (oneStepDirichletCellMeanField_memVectorL2_of_descendant
        M n h p Q omega hh) R hR
    volumeAverage (openCubeSet R) (fun x ↦
      vecDot (X.field x)
        (matVecMul
          (scalarCoeffField
            (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega) x)
          (X.field x)))
  else 0

private def primalRawOscillatory {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d)
    (R : Homogenization.TriadicCube d) (omega : Sample d) (hh : 0 < h) : ℝ :=
  if hR : R ∈ oneStepSourceCells d K n M.delta then
    let Q := originCube d (K : ℤ)
    let high := primalHighData (K := K) M n h omega
    let F := fun S ↦ oneStepDirichletCellFluctuationField
      M n h p Q S omega hh
    let X := oneStepSelectedDirichletCell
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega))
      F high.isElliptic
      (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
        M n h p Q omega hh) R hR
    volumeAverage (openCubeSet R) (fun x ↦
      vecDot (X.field x)
        (matVecMul
          (scalarCoeffField
            (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega) x)
          (X.field x)))
  else 0

private def primalRawMixed {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d)
    (R : Homogenization.TriadicCube d) (omega : Sample d) (hh : 0 < h) : ℝ :=
  if hR : R ∈ oneStepSourceCells d K n M.delta then
    let Q := originCube d (K : ℤ)
    let low := primalLowData (K := K) M n omega
    let high := primalHighData (K := K) M n h omega
    let P := fun S ↦ oneStepDirichletCellMeanField M n h p Q S omega hh
    let F := fun S ↦ oneStepDirichletCellFluctuationField
      M n h p Q S omega hh
    let XP := oneStepSelectedDirichletCell
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
      P low.isElliptic
      (oneStepDirichletCellMeanField_memVectorL2_of_descendant
        M n h p Q omega hh) R hR
    let XO := oneStepSelectedDirichletCell
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega))
      F high.isElliptic
      (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
        M n h p Q omega hh) R hR
    volumeAverage (openCubeSet R) (fun x ↦
      vecDot (XP.field x)
        (matVecMul
          (scalarCoeffField
            (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega) x)
          (XO.field x)))
  else 0

/-- Measurable principal envelope for the selected lower-cutoff cell. -/
def oneStepPrimalPrincipalMajorant {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d)
    (R : Homogenization.TriadicCube d) (omega : Sample d) (hh : 0 < h) : ℝ :=
  oneStepUpperSourceCellWeight M n h R omega *
    vecDot (oneStepDirichletCellSlope M n h p
      (originCube d (K : ℤ)) R omega hh)
      (matVecMul (randomAMatrix M n (Ch02.cubeDomain R) omega)
        (oneStepDirichletCellSlope M n h p
          (originCube d (K : ℤ)) R omega hh))

/-- Restricted weak-Hessian size used in the measurable oscillatory
envelope. -/
def oneStepPrimalSourceCellB {d K : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (u : Sample d → H1Function (openCubeSet (originCube d (K : ℤ))))
    (H : ∀ omega, HasWeakHessianOn
      (openCubeSet (originCube d (K : ℤ))) (u omega))
    (R : Homogenization.TriadicCube d) (omega : Sample d) : ℝ :=
  if hR : R ∈ oneStepSourceCells d K n M.delta then
    oneStepCellB R ((H omega).restrict (isOpen_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth
        (mem_oneStepSourceCells hR)))
  else 0

/-- Dimension-only coefficient in the primal quarter-Besov cell estimate. -/
def oneStepPrimalCellEnergyConst (d : ℕ) : ℝ :=
  2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
    oneStepQuarterCellConst d) ^ 2

/-- Measurable upper envelope for the selected high-cutoff oscillatory cell
energy. -/
def oneStepPrimalOscillatoryMajorant {d K : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (u : Sample d → H1Function (openCubeSet (originCube d (K : ℤ))))
    (H : ∀ omega, HasWeakHessianOn
      (openCubeSet (originCube d (K : ℤ))) (u omega))
    (R : Homogenization.TriadicCube d) (omega : Sample d) : ℝ :=
  let B := oneStepPrimalSourceCellB M n u H R omega
  let D := (originCubeMeanZeroH1CoerciveEstimate d 0).constant
  oneStepPrimalCellEnergyConst d *
    oneStepUpperPoincareEnergyFactorMeasurable M (n + h)
      (oneStepLocalizationScale n M.delta)
      (translatePotentialSequence (triadicCubeShift R) omega) *
    oneStepCellBesovError (D * B) B

/-- The measurable primal principal envelope is integrable.  Prefix/suffix
independence is used at the matrix-entry level, after the fresh slope and
weight are placed in `L^4`, `L^4`, and `L^2`. -/
theorem integrable_oneStepPrimalPrincipalMajorant
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (R : Homogenization.TriadicCube d)
    (hh : 0 < h) (hp : vecNormSq p = 1) :
    Integrable (oneStepPrimalPrincipalMajorant (K := K) M n h p R · hh)
      M.P.toMeasure := by
  let slope : Sample d → Homogenization.Vec d := fun omega ↦
    oneStepDirichletCellSlope M n h p (originCube d (K : ℤ)) R omega hh
  have hpair : ∀ i j : Fin d,
      Integrable (fun omega ↦ oneStepUpperSourceCellWeight M n h R omega *
        (slope omega i * slope omega j)) M.P.toMeasure := fun i j ↦
    integrable_weight_mul_pair_of_memLp_two_four M
      (oneStepUpperSourceCellWeight M n h R) slope
      (memLp_two_oneStepUpperSourceCellWeight M n h R hh)
      (fun k ↦ by
        simpa only [slope] using
          memLp_four_oneStepDirichletCellSlope_coord M n h p
            (originCube d (K : ℤ)) R hh hp k) i j
  simpa only [oneStepPrimalPrincipalMajorant, slope] using
    integrable_weight_mul_vecDot_randomAMatrix_suffix M n
      (Ch02.cubeDomain R) (oneStepUpperSourceCellWeight M n h R) slope
      (measurable_oneStepUpperSourceCellWeight_potentialShellIndexSigma_Ioi
        M n h R hh)
      (measurable_oneStepDirichletCellSlope_potentialShellIndexSigma_Ioi
        M n h p (originCube d (K : ℤ)) R hh)
      hpair

/-- Pointwise nonnegativity of the primal principal envelope. -/
theorem oneStepPrimalPrincipalMajorant_nonneg
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (R : Homogenization.TriadicCube d)
    (omega : Sample d) (hh : 0 < h) :
    0 ≤ oneStepPrimalPrincipalMajorant (K := K) M n h p R omega hh := by
  unfold oneStepPrimalPrincipalMajorant oneStepUpperSourceCellWeight
  exact mul_nonneg
    (cutoffRatioSup_pos M (n + h) n (Ch02.cubeDomain R) omega).le
    ((randomAMatrix_posSemidef M n (Ch02.cubeDomain R) omega)
      |>.dotProduct_mulVec_nonneg _)

/-- The literal mixed-cutoff finite competitor is dominated almost surely by
the measurable principal and oscillatory source-cell envelopes.  All
samplewise-selected minimizers disappear on the right-hand side. -/
theorem ae_half_randomAMatrix_le_oneStepPrimalMajorants
    {d K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (hh : 0 < h)
    (hsource : oneStepLocalizationScale n M.delta ≤ K)
    (uD : Sample d → H10Function
      (openCubeSet (originCube d (K : ℤ))))
    (huD : ∀ omega,
      CubeDirichletDivergenceProblem (originCube d (K : ℤ)) (uD omega)
        (oneStepShellForcingH1 M n h omega p
          (originCube d (K : ℤ)) hh).toField)
    (V : Sample d → CubeVectorW1pFunction
      (originCube d (K : ℤ)) oneStepFourExponent)
    (hV : ∀ omega, (V omega).toField = (uD omega).toH1Function.grad) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (1 / 2 : ℝ) * vecDot p
          (matVecMul (randomAMatrix M (n + h)
            (Ch02.cubeDomain (originCube d (K : ℤ))) omega) p) ≤
        (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ((1 / 2 : ℝ) *
                oneStepPrimalPrincipalMajorant (K := K) M n h p R omega hh +
              Real.sqrt (oneStepPrimalPrincipalMajorant
                (K := K) M n h p R omega hh) *
                Real.sqrt (oneStepPrimalOscillatoryMajorant (K := K) M n h
                  (fun w ↦ (uD w).toH1Function)
                  (fun w ↦ weakHessianOfCubeVectorW1pFour (V w) (hV w))
                  R omega) +
              (1 / 2 : ℝ) *
                oneStepPrimalOscillatoryMajorant (K := K) M n h
                  (fun w ↦ (uD w).toH1Function)
                  (fun w ↦ weakHessianOfCubeVectorW1pFour (V w) (hV w))
                  R omega) := by
  let Q := originCube d (K : ℤ)
  let j := K - oneStepLocalizationScale n M.delta
  let H : ∀ omega, HasWeakHessianOn (openCubeSet Q)
      (uD omega).toH1Function := fun omega ↦
    weakHessianOfCubeVectorW1pFour (V omega) (hV omega)
  have hfactor : ∀ R ∈ oneStepSourceCells d K n M.delta,
      (fun omega ↦
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareUpperEllipticityFactor R
            (aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega)
            (1 / 4) (.finite 1)) ^ 2) =ᵐ[M.P.toMeasure]
        fun omega ↦ oneStepUpperPoincareEnergyFactorMeasurable M (n + h)
          (oneStepLocalizationScale n M.delta)
          (translatePotentialSequence (triadicCubeShift R) omega) := by
    intro R hR
    exact oneStepUpperPoincareFactor_cell_ae_eq_measurable_translate
      M (n + h) R (oneStepSourceCells_scale_eq hsource hR)
  have hfactorAll : ∀ᵐ omega ∂M.P.toMeasure,
      ∀ R ∈ oneStepSourceCells d K n M.delta,
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareUpperEllipticityFactor R
            (aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega)
            (1 / 4) (.finite 1)) ^ 2 =
        oneStepUpperPoincareEnergyFactorMeasurable M (n + h)
          (oneStepLocalizationScale n M.delta)
          (translatePotentialSequence (triadicCubeShift R) omega) :=
    (Finset.eventually_all (oneStepSourceCells d K n M.delta)).2 hfactor
  filter_upwards [hfactorAll] with omega hfactorOmega
  let low := primalLowData (K := K) M n omega
  let high := primalHighData (K := K) M n h omega
  let rawP := fun R ↦ primalRawPrincipal (K := K) M n h p R omega hh
  let rawM := fun R ↦ primalRawMixed (K := K) M n h p R omega hh
  let rawO := fun R ↦ primalRawOscillatory (K := K) M n h p R omega hh
  let majorP := fun R ↦
    oneStepPrimalPrincipalMajorant (K := K) M n h p R omega hh
  let majorO := fun R ↦ oneStepPrimalOscillatoryMajorant (K := K) M n h
    (fun w ↦ (uD w).toH1Function) H R omega
  apply half_target_le_normalized_finset_majorants_of_raw
    (oneStepSourceCells d K n M.delta)
    (vecDot p (matVecMul (randomAMatrix M (n + h) (Ch02.cubeDomain Q) omega) p))
    rawP rawM rawO majorP majorO
  · intro R hR
    dsimp only [rawP]
    simp only [primalRawPrincipal, dite_eq_left hR]
    apply volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet R)
    intro x _hx
    simp only [scalarCoeffField, matVecMul_scalarMatrix]
    rw [Homogenization.vecDot_smul_right]
    exact mul_nonneg
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M (n + h) omega x).le
      (vecNormSq_nonneg _)
  · intro R hR
    dsimp only [rawO]
    simp only [primalRawOscillatory, dite_eq_left hR]
    apply volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet R)
    intro x _hx
    simp only [scalarCoeffField, matVecMul_scalarMatrix]
    rw [Homogenization.vecDot_smul_right]
    exact mul_nonneg
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M (n + h) omega x).le
      (vecNormSq_nonneg _)
  · intro R hR
    simpa only [rawP, majorP, primalRawPrincipal, dite_eq_left hR, Q, low, high,
      oneStepPrimalPrincipalMajorant] using
      oneStepSelectedDirichletMean_highEnergy_le
        M n h p Q R omega hh low.isElliptic high.isElliptic hR
  · intro R hR
    let uR := oneStepCenteredRestriction (uD omega).toH1Function
      (mem_oneStepSourceCells hR)
    let HR := (H omega).restrict (isOpen_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth
        (mem_oneStepSourceCells hR))
    let B := oneStepCellB R HR
    let D := (originCubeMeanZeroH1CoerciveEstimate d 0).constant
    let Y := oneStepSelectedDirichletCell
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega))
      (fun S ↦ oneStepDirichletCellFluctuationField M n h p Q S omega hh)
      high.isElliptic
      (oneStepDirichletCellFluctuationField_memVectorL2_of_descendant
        M n h p Q omega hh) R hR
    have hcoeff :
        Ch03.publicCoeffField R
            (aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega) =ᵐ[
              volumeMeasureOn (openCubeSet R)]
          scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega) := by
      simpa only [aCutoffEnvelopeTriadicCoeffFamily,
        aCutoffEnvelopeScalarTriadicCoeffData,
        ScalarTriadicCoeffData.toTriadicCoeffFamily,
        aCutoffEnvelopeCoeffOnData, ScalarCoeffOnData.toCoeffOn] using
        Ch03.publicCoeffField_ae_eq_openCubeSet R
          (aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega)
    let Ypub := oneStepDirichletCellMinimizer_congrCoeff Y hcoeff.symm
    have hbase := oneStepDirichletCellFluctuation_energy_le_poincare_quarter_at_cutoff_of_solution
      M (n + h) n h p (K : ℤ) omega hh (uD omega) (huD omega)
        R (mem_oneStepSourceCells hR) (V omega) (hV omega) Ypub
    have hBcenter : oneStepCellB R
          (HasWeakHessianOn.centeredRestriction (H omega)
            (mem_oneStepSourceCells hR)) = B := by
      simp [B, HR, H, oneStepCellB, oneStepCellNormalizedHessianSize,
        HasWeakHessianOn.hessianCoordL2NormSum,
        HasWeakHessianOn.hessCoordToScalarL2,
        HasWeakHessianOn.centeredRestriction, weakHessianAdd,
        weakHessianAffineOnCube]
    have hAraw : cubeLpNorm R 2 uR.grad ≤ D * B := by
      have hcenter := oneStepCellCenteredL2_le_const_mul_cellB
        (mem_oneStepSourceCells hR) (uD omega).toH1Function (H omega)
      have hfluct := cubeLpNorm_cubeFluctuationVec_le_oneStepCellCenteredL2
        (mem_oneStepSourceCells hR) (uD omega).toH1Function.grad
          (uD omega).toH1Function.grad_memVectorL2
      have hgrad : uR.grad = fun x ↦ cubeFluctuationVec R
          (uD omega).toH1Function.grad x := by
        funext x
        rw [oneStepCenteredRestriction_grad]
        rfl
      rw [hgrad]
      exact hfluct.trans hcenter
    have hB0 : 0 ≤ B := oneStepCellB_nonneg R HR
    have hA0 : 0 ≤ cubeLpNorm R 2 uR.grad := cubeLpNorm_nonneg R 2 _
    have herr := oneStepCellBesovError_mono
      (A := cubeLpNorm R 2 uR.grad) (B := B) (C := D * B) (D := B)
      hA0 hAraw le_rfl
    have hconst0 : 0 ≤ oneStepPrimalCellEnergyConst d := by
      unfold oneStepPrimalCellEnergyConst
      positivity
    have hfactor0 : 0 ≤
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareUpperEllipticityFactor R
            (aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega)
              (1 / 4) (.finite 1)) ^ 2 := sq_nonneg _
    have hscaled := mul_le_mul_of_nonneg_left herr
      (mul_nonneg hconst0 hfactor0)
    have hbase' :
        volumeAverage (openCubeSet R) (fun x ↦
            vecDot (Y.field x)
              (matVecMul (scalarCoeffField
                (_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega) x)
                (Y.field x))) ≤
          oneStepPrimalCellEnergyConst d *
            (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
              Ch03.poincareUpperEllipticityFactor R
                (aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega)
                  (1 / 4) (.finite 1)) ^ 2 *
            oneStepCellBesovError (cubeLpNorm R 2 uR.grad) B := by
      simpa only [Ypub, oneStepDirichletCellMinimizer_congrCoeff,
        OneStepDirichletCellMinimizer.field, oneStepPrimalCellEnergyConst,
        Q, H, HR, uR, B, hBcenter, mul_assoc] using hbase
    have htotal := hbase'.trans hscaled
    rw [hfactorOmega R hR] at htotal
    simpa only [rawO, majorO, primalRawOscillatory, dite_eq_left hR,
      oneStepPrimalOscillatoryMajorant, oneStepPrimalSourceCellB,
      Q, H, HR, uR, B, D, Y, Ypub, high, oneStepPrimalCellEnergyConst,
      mul_assoc] using htotal
  · intro R hR
    simpa only [rawP, rawM, rawO, primalRawPrincipal, primalRawMixed,
      primalRawOscillatory, dite_eq_left hR, Q, low, high] using
      abs_oneStepSelectedDirichletCell_mixedCutoff_le_sqrt_energies
        M n h p Q R omega hh low.isElliptic high.isElliptic hR
  · have hvar := half_randomAMatrix_le_mixedCutoff_selectedCellEnergies
      M n h p Q omega hh low.isElliptic high.isElliptic
    refine hvar.trans_eq ?_
    simp only [descendantsAverage, oneStepSourceCells]
    congr 1
    apply Finset.sum_congr rfl
    intro R hR
    have hR' : R ∈ oneStepSourceCells d K n M.delta := by
      simpa only [oneStepSourceCells, Q] using hR
    simp only [rawP, rawM, rawO, primalRawPrincipal, primalRawMixed,
      primalRawOscillatory, dite_eq_left hR, dite_eq_left hR', Q, low, high]

/-- The source-scale Calderon--Zygmund estimate supplies the exact measurable
cell-Hessian family used by `oneStepPrimalOscillatoryMajorant`, together with
ordinary fourth-moment integrability and its normalized finite-sum budget. -/
theorem exists_oneStepPrimalCZFiniteFamilyBudget
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h K : ℕ)
        (p : Homogenization.Vec d) (_hp : vecNormSq p = 1)
        (hh : 0 < h) (_hblock : (h : ℝ) ≤ M.delta⁻¹)
        (_hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
        (_hK : oneStepLocalizationScale n M.delta ≤ K),
        ∃ (uD : Sample d → H10Function
              (openCubeSet (originCube d (K : ℤ))))
          (V : Sample d → CubeVectorW1pFunction
              (originCube d (K : ℤ)) oneStepFourExponent)
          (hV : ∀ omega,
              (V omega).toField = (uD omega).toH1Function.grad),
          (∀ omega,
            CubeDirichletDivergenceProblem (originCube d (K : ℤ)) (uD omega)
              (oneStepShellForcingH1 M n h omega p
                (originCube d (K : ℤ)) hh).toField) ∧
          let H : ∀ omega, HasWeakHessianOn
              (openCubeSet (originCube d (K : ℤ)))
              (uD omega).toH1Function := fun omega ↦
            weakHessianOfCubeVectorW1pFour (V omega) (hV omega)
          let B := fun R omega ↦ oneStepPrimalSourceCellB (K := K)
            M n (fun w ↦ (uD w).toH1Function) H R omega
          (∀ R ∈ oneStepSourceCells d K n M.delta, Measurable (B R)) ∧
          (∀ R ∈ oneStepSourceCells d K n M.delta,
            Integrable (fun omega ↦ B R omega ^ (4 : ℕ)) M.P.toMeasure) ∧
          (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
              ∑ R ∈ oneStepSourceCells d K n M.delta,
                ∫ omega, B R omega ^ (4 : ℕ) ∂M.P.toMeasure ≤
            (C * ENNReal.ofReal (M.delta ^ (68 : ℕ))).toReal := by
  obtain ⟨C, hCtop, hpack⟩ :=
    exists_lintegral_oneStepDirichlet_descendantCellB_source_le d
  refine ⟨C, hCtop, ?_⟩
  intro M n h K p hp hh hblock hsource hK
  obtain ⟨uD, V, hV, huD, _hglobalB, hbudget⟩ :=
    hpack M n h K p hp hh hblock hsource hK
  let H : ∀ omega, HasWeakHessianOn
      (openCubeSet (originCube d (K : ℤ)))
      (uD omega).toH1Function := fun omega ↦
    weakHessianOfCubeVectorW1pFour (V omega) (hV omega)
  let B := fun R omega ↦ oneStepPrimalSourceCellB (K := K)
    M n (fun w ↦ (uD w).toH1Function) H R omega
  have hBmeas : ∀ R ∈ oneStepSourceCells d K n M.delta,
      Measurable (B R) := by
    intro R hR
    let uR : Sample d → H1Function (openCubeSet R) := fun omega ↦
      (uD omega).toH1Function.restrict (isOpen_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth
          (mem_oneStepSourceCells hR))
    let HR : ∀ omega, HasWeakHessianOn (openCubeSet R) (uR omega) :=
      fun omega ↦ (H omega).restrict (isOpen_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth
          (mem_oneStepSourceCells hR))
    have hgradGlobal : Measurable fun omega ↦
        (uD omega).toH1Function.gradToHilbertVectorL2 :=
      measurable_oneStepShellDirichletGradL2 M n h p
        (originCube d (K : ℤ)) hh uD huD
    have hgradR : Measurable fun omega ↦ (uR omega).gradToHilbertVectorL2 := by
      apply measurable_gradToHilbertVectorL2_of_grad_eq_restrict
        (openCubeSet_subset_of_mem_descendantsAtDepth
          (mem_oneStepSourceCells hR))
        (fun omega ↦ (uD omega).toH1Function) uR hgradGlobal
      intro omega
      rfl
    simpa only [B, oneStepPrimalSourceCellB, dite_eq_left hR, H, uR, HR] using
      measurable_oneStepCellB R uR HR hgradR
  have hB0 : ∀ R ∈ oneStepSourceCells d K n M.delta,
      ∀ omega, 0 ≤ B R omega := by
    intro R hR omega
    simpa only [B, oneStepPrimalSourceCellB, dite_eq_left hR] using
      oneStepCellB_nonneg R ((H omega).restrict (isOpen_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth
          (mem_oneStepSourceCells hR)))
  have hbudget' : ∫⁻ omega, ENNReal.ofReal
        (descendantsAverage (originCube d (K : ℤ))
          (K - oneStepLocalizationScale n M.delta)
          (fun R ↦ B R omega ^ (4 : ℕ))) ∂M.P.toMeasure ≤
      C * ENNReal.ofReal (M.delta ^ (68 : ℕ)) := by
    calc
      _ = ∫⁻ omega, ENNReal.ofReal
          (descendantsAverage (originCube d (K : ℤ))
            (K - oneStepLocalizationScale n M.delta) (fun R ↦
              if hR : R ∈ descendantsAtDepth (originCube d (K : ℤ))
                  (K - oneStepLocalizationScale n M.delta) then
                (oneStepCellB R ((H omega).restrict (isOpen_openCubeSet R)
                  (openCubeSet_subset_of_mem_descendantsAtDepth hR))) ^ (4 : ℕ)
              else 0)) ∂M.P.toMeasure := by
        apply lintegral_congr
        intro omega
        congr 1
        simp only [descendantsAverage]
        congr 1
        apply Finset.sum_congr rfl
        intro R hR
        simp only [B, oneStepPrimalSourceCellB, oneStepSourceCells,
          dite_eq_left hR, H]
        erw [dite_eq_left hR]
      _ ≤ _ := by simpa only [H] using hbudget
  obtain ⟨hBint, hBsum⟩ :=
    finiteFamily_four_budget_of_lintegral_descendantsAverage
      (originCube d (K : ℤ)) (K - oneStepLocalizationScale n M.delta)
      B hBmeas hB0
      (ENNReal.mul_ne_top hCtop.ne ENNReal.ofReal_ne_top) hbudget'
  exact ⟨uD, V, hV, huD, hBmeas, hBint, hBsum⟩

/-- Uniform finite-family second-moment budget for the measurable upper
coarse-Poincare factor on the translated source cells. -/
theorem exists_oneStepPrimalPoincareFactorFiniteBudget
    {d : ℕ} [NeZero d] :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
        ∀ (n h K : ℕ), (h : ℝ) ≤ M.delta⁻¹ →
          16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
          oneStepLocalizationScale n M.delta ≤ K →
          let F := fun R omega ↦
            oneStepUpperPoincareEnergyFactorMeasurable M (n + h)
              (oneStepLocalizationScale n M.delta)
              (translatePotentialSequence (triadicCubeShift R) omega)
          (∀ R ∈ oneStepSourceCells d K n M.delta,
            Integrable (fun omega ↦ F R omega ^ (2 : ℕ)) M.P.toMeasure) ∧
          (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
              ∑ R ∈ oneStepSourceCells d K n M.delta,
                ∫ omega, F R omega ^ (2 : ℕ) ∂M.P.toMeasure ≤
            (C * ahom M n) ^ (2 : ℕ) := by
  obtain ⟨delta0, C0, hdelta0, hC0, hsource⟩ :=
    exists_sourceScale_highCutoff_ellipticity_moments (d := d)
  let D : ℝ := Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) ^ 2
  let C : ℝ := D * C0
  have hD : 0 < D := by
    dsimp only [D, Ch03.poincareDiscountFactor]
    exact sq_pos_of_pos <| Real.rpow_pos_of_pos
      (Ch02.book_geometricDiscount_pos (by norm_num)) _
  have hC : 0 < C := mul_pos hD hC0
  refine ⟨delta0, C, hdelta0, hC, ?_⟩
  intro M hM n h K hblock hstart hK
  let j := oneStepLocalizationScale n M.delta
  let X := cutoffUpperEllipticityMeasurable M (n + h) j
  let F0 := oneStepUpperPoincareEnergyFactorMeasurable M (n + h) j
  obtain ⟨hXint, hXbudget, _hlowerInt, _hlowerBudget⟩ :=
    hsource M hM n h hblock (oneStepLocalizationDepth_le hstart)
  have hFX : F0 =ᵐ[M.P.toMeasure] fun omega ↦ D * X omega := by
    filter_upwards [cutoffUpperEllipticityMeasurable_ae_eq M (n + h) j]
      with omega hXeq
    simp only [F0, oneStepUpperPoincareEnergyFactorMeasurable,
      oneStepUpperEllipticityRatioMeasurable, X]
    rw [max_eq_left]
    · field_simp [ahom_pos M (n + h) |>.ne']
      dsimp only [D]
      ring
    · rw [hXeq]
      exact mul_nonneg (inv_nonneg.mpr (ahom_pos M (n + h)).le)
        (Ch04.LambdaSqCoeffField_finite_nonneg _ _ (by norm_num) (by norm_num))
  have hFint : Integrable (fun omega ↦ F0 omega ^ (2 : ℕ))
      M.P.toMeasure := by
    apply (hXint.const_mul (D ^ (2 : ℕ))).congr
    filter_upwards [hFX] with omega heq
    rw [heq]
    ring
  have hFbudget : ∫ omega, F0 omega ^ (2 : ℕ) ∂M.P.toMeasure ≤
      (C * ahom M n) ^ (2 : ℕ) := by
    have hsq : (fun omega ↦ F0 omega ^ (2 : ℕ)) =ᵐ[M.P.toMeasure]
        fun omega ↦ D ^ (2 : ℕ) * X omega ^ (2 : ℕ) := by
      filter_upwards [hFX] with omega heq
      rw [heq]
      ring
    calc
      _ = D ^ (2 : ℕ) * ∫ omega, X omega ^ (2 : ℕ) ∂M.P.toMeasure := by
        rw [integral_congr_ae hsq]
        rw [integral_const_mul]
      _ ≤ D ^ (2 : ℕ) * (C0 * ahom M n) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hXbudget (sq_nonneg D)
      _ = (C * ahom M n) ^ (2 : ℕ) := by
        dsimp only [C]
        ring
  let F := fun R omega ↦ F0
    (translatePotentialSequence (triadicCubeShift R) omega)
  have hFcell : ∀ R ∈ oneStepSourceCells d K n M.delta,
      Integrable (fun omega ↦ F R omega ^ (2 : ℕ)) M.P.toMeasure := by
    intro R _hR
    exact (measurePreserving_translatePotentialSequence M (triadicCubeShift R))
      |>.integrable_comp_of_integrable hFint
  refine ⟨hFcell, ?_⟩
  rw [normalized_finset_integral_comp_translatePotentialSequence_eq M
    (fun R ↦ triadicCubeShift R) (oneStepSourceCells d K n M.delta)
    (oneStepSourceCells_nonempty d K n M.delta)
    (fun omega ↦ F0 omega ^ (2 : ℕ)) hFint]
  exact hFbudget

/-- Finite-family Holder fold in the exact scaled-cell form used by the
primal oscillatory majorant. -/
theorem finiteFamily_scaledCellBesovMajorant_budget
    {Omega ι : Type*} [MeasurableSpace Omega] [DecidableEq ι]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (s : Finset ι) (hs : s.Nonempty)
    (Lambda B : ι → Omega → ℝ) (D cellConst : ℝ)
    (hD0 : 0 ≤ D) (hcellConst0 : 0 ≤ cellConst)
    (hLambda : ∀ i ∈ s, Measurable (Lambda i))
    (hB : ∀ i ∈ s, Measurable (B i))
    (hLambda0 : ∀ i ∈ s, ∀ omega, 0 ≤ Lambda i omega)
    (hB0 : ∀ i ∈ s, ∀ omega, 0 ≤ B i omega)
    (hLambda2 : ∀ i ∈ s,
      Integrable (fun omega ↦ Lambda i omega ^ (2 : ℕ)) mu)
    (hB4 : ∀ i ∈ s,
      Integrable (fun omega ↦ B i omega ^ (4 : ℕ)) mu)
    {L KB : ℝ} (hL : 0 ≤ L) (_hKB : 0 ≤ KB)
    (hLambdaBudget : ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
      ∫ omega, Lambda i omega ^ (2 : ℕ) ∂mu ≤ L ^ (2 : ℕ))
    (hBBudget : ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
      ∫ omega, B i omega ^ (4 : ℕ) ∂mu ≤ KB) :
    (∀ i ∈ s, Integrable (fun omega ↦
        cellConst * Lambda i omega *
          oneStepCellBesovError (D * B i omega) (B i omega)) mu) ∧
      ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
          ∫ omega, cellConst * Lambda i omega *
            oneStepCellBesovError (D * B i omega) (B i omega) ∂mu ≤
        cellConst *
          (3 * L * Real.sqrt ((D ^ (4 : ℕ) + 1) * KB)) := by
  let A : ι → Omega → ℝ := fun i omega ↦ D * B i omega
  have hA : ∀ i ∈ s, Measurable (A i) := by
    intro i hi
    exact (hB i hi).const_mul D
  have hA0 : ∀ i ∈ s, 0 ≤ᵐ[mu] A i := by
    intro i hi
    exact Filter.Eventually.of_forall fun omega ↦
      mul_nonneg hD0 (hB0 i hi omega)
  have hB0ae : ∀ i ∈ s, 0 ≤ᵐ[mu] B i := fun i hi ↦
    Filter.Eventually.of_forall (hB0 i hi)
  have hLambda0ae : ∀ i ∈ s, 0 ≤ᵐ[mu] Lambda i := fun i hi ↦
    Filter.Eventually.of_forall (hLambda0 i hi)
  have hA4 : ∀ i ∈ s,
      Integrable (fun omega ↦ A i omega ^ (4 : ℕ)) mu := by
    intro i hi
    apply (hB4 i hi).const_mul (D ^ (4 : ℕ)) |>.congr
    filter_upwards with omega
    dsimp only [A]
    ring
  have hcellBudget : ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
      ∫ omega, A i omega ^ (4 : ℕ) + B i omega ^ (4 : ℕ) ∂mu ≤
        (D ^ (4 : ℕ) + 1) * KB := by
    have heq : ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, A i omega ^ (4 : ℕ) + B i omega ^ (4 : ℕ) ∂mu =
      (D ^ (4 : ℕ) + 1) *
        (((s.card : ℝ)⁻¹) * ∑ i ∈ s,
          ∫ omega, B i omega ^ (4 : ℕ) ∂mu) := by
      calc
        _ = ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
            (D ^ (4 : ℕ) + 1) *
              ∫ omega, B i omega ^ (4 : ℕ) ∂mu := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [integral_add (hA4 i hi) (hB4 i hi)]
          have hAi : ∫ omega, A i omega ^ (4 : ℕ) ∂mu =
              D ^ (4 : ℕ) * ∫ omega, B i omega ^ (4 : ℕ) ∂mu := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with omega
            dsimp only [A]
            ring
          rw [hAi]
          ring
        _ = _ := by rw [← Finset.mul_sum]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hBBudget (by positivity)
  have hcore := normalized_finset_integral_mul_oneStepCellBesovError_le
    s hs Lambda A B hLambda hA hB hLambda0ae hA0 hB0ae hLambda2 hA4 hB4
  have hcoreBound : ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
      ∫ omega, Lambda i omega *
        oneStepCellBesovError (A i omega) (B i omega) ∂mu ≤
      3 * L * Real.sqrt ((D ^ (4 : ℕ) + 1) * KB) := by
    refine hcore.trans ?_
    have hsqrtLambda := Real.sqrt_le_sqrt hLambdaBudget
    have hsqrtCell := Real.sqrt_le_sqrt hcellBudget
    have hsqrtL : Real.sqrt (L ^ (2 : ℕ)) = L := Real.sqrt_sq hL
    rw [hsqrtL] at hsqrtLambda
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrtLambda (by norm_num))
      hsqrtCell (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) hL)
  constructor
  · intro i hi
    have hError2 := integrable_sq_oneStepCellBesovError
      (hA i hi) (hB i hi) (hA0 i hi) (hB0ae i hi) (hA4 i hi) (hB4 i hi)
    have hLambdaMem : MemLp (Lambda i) 2 mu :=
      (memLp_two_iff_integrable_sq (hLambda i hi).aestronglyMeasurable).2
        (hLambda2 i hi)
    have hErrorMeas : Measurable fun omega ↦
        oneStepCellBesovError (A i omega) (B i omega) :=
      ((hA i hi).pow_const 2).add
        ((((hA i hi).mul (Real.continuous_sqrt.measurable.comp (hA i hi))).mul
          (Real.continuous_sqrt.measurable.comp (hB i hi))))
    have hErrorMem : MemLp
        (fun omega ↦ oneStepCellBesovError (A i omega) (B i omega)) 2 mu :=
      (memLp_two_iff_integrable_sq hErrorMeas.aestronglyMeasurable).2 hError2
    simp only [mul_assoc]
    exact (hLambdaMem.integrable_mul hErrorMem).const_mul cellConst
  · have hscaled := mul_le_mul_of_nonneg_left hcoreBound hcellConst0
    have hleft : ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
          ∫ omega, cellConst * Lambda i omega *
            oneStepCellBesovError (D * B i omega) (B i omega) ∂mu =
        cellConst * (((s.card : ℝ)⁻¹) * ∑ i ∈ s,
          ∫ omega, Lambda i omega *
            oneStepCellBesovError (A i omega) (B i omega) ∂mu) := by
      calc
        _ = ((s.card : ℝ)⁻¹) * ∑ i ∈ s, cellConst *
            ∫ omega, Lambda i omega *
              oneStepCellBesovError (A i omega) (B i omega) ∂mu := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with omega
          dsimp only [A]
          ring
        _ = _ := by rw [← Finset.mul_sum]; ring
    rw [hleft]
    exact hscaled

theorem aux_dedup_d239_sqrt_const_mul_pow_sixtyeight
    {K delta : ℝ} (hK : 0 ≤ K) (hdelta : 0 ≤ delta) :
    Real.sqrt (K * delta ^ (68 : ℕ)) =
      Real.sqrt K * delta ^ (34 : ℕ) := by
  rw [show delta ^ (68 : ℕ) = (delta ^ (34 : ℕ)) ^ 2 by ring,
    Real.sqrt_mul hK, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (pow_nonneg hdelta 34)]

private theorem sqrt_const_mul_pow_sixtyeight
    {K delta : ℝ} (hK : 0 ≤ K) (hdelta : 0 ≤ delta) :
    Real.sqrt (K * delta ^ (68 : ℕ)) =
      Real.sqrt K * delta ^ (34 : ℕ) := by exact SubdiffusiveProcess.Providers.Section5.aux_dedup_d239_sqrt_const_mul_pow_sixtyeight (K := K) (delta := delta) (hK := hK) (hdelta := hdelta)

/-- The samplewise Calderon--Zygmund solution and the translated
coarse-Poincare factor give the literal finite-family oscillatory budget in
the `delta^30` normalization consumed by the one-step upper close. -/
theorem exists_oneStepPrimalOscillatoryFiniteBudget
    (d : ℕ) [NeZero d] :
    ∃ delta0 O : ℝ, 0 < delta0 ∧ 0 < O ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
        ∀ (n h K : ℕ) (p : Homogenization.Vec d),
          vecNormSq p = 1 → ∀ hh : 0 < h, (h : ℝ) ≤ M.delta⁻¹ →
          16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
          oneStepLocalizationScale n M.delta ≤ K →
          ∃ (uD : Sample d → H10Function
                (openCubeSet (originCube d (K : ℤ))))
            (V : Sample d → CubeVectorW1pFunction
                (originCube d (K : ℤ)) oneStepFourExponent)
            (hV : ∀ omega,
                (V omega).toField = (uD omega).toH1Function.grad),
            (∀ omega,
              CubeDirichletDivergenceProblem (originCube d (K : ℤ)) (uD omega)
                (oneStepShellForcingH1 M n h omega p
                  (originCube d (K : ℤ)) hh).toField) ∧
            let H : ∀ omega, HasWeakHessianOn
                (openCubeSet (originCube d (K : ℤ)))
                (uD omega).toH1Function := fun omega ↦
              weakHessianOfCubeVectorW1pFour (V omega) (hV omega)
            let E := fun R omega ↦ oneStepPrimalOscillatoryMajorant (K := K)
              M n h (fun w ↦ (uD w).toH1Function) H R omega
            (∀ R ∈ oneStepSourceCells d K n M.delta,
              Integrable (E R) M.P.toMeasure) ∧
            (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
                ∑ R ∈ oneStepSourceCells d K n M.delta,
                  ∫ omega, E R omega ∂M.P.toMeasure ≤
              O * M.delta ^ (30 : ℕ) * ahom M n := by
  obtain ⟨CB, hCBtop, hCB⟩ := exists_oneStepPrimalCZFiniteFamilyBudget d
  obtain ⟨delta0, CF, hdelta0, hCF, hF⟩ :=
    exists_oneStepPrimalPoincareFactorFiniteBudget (d := d)
  let D : ℝ := (originCubeMeanZeroH1CoerciveEstimate d 0).constant
  let cellConst : ℝ := oneStepPrimalCellEnergyConst d
  let K0 : ℝ := (D ^ (4 : ℕ) + 1) * CB.toReal
  let O : ℝ := 1 + cellConst * (3 * CF * Real.sqrt K0)
  have hD0 : 0 ≤ D :=
    (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  have hcell0 : 0 ≤ cellConst := by
    dsimp only [cellConst, oneStepPrimalCellEnergyConst]
    positivity
  have hK0 : 0 ≤ K0 := by
    dsimp only [K0]
    positivity
  have hO : 0 < O := by
    dsimp only [O]
    positivity
  refine ⟨delta0, O, hdelta0, hO, ?_⟩
  intro M hM n h K p hp hh hblock hsource hK
  obtain ⟨uD, V, hV, huD, hBmeas, hBint, hBbudget⟩ :=
    hCB M n h K p hp hh hblock hsource hK
  let H : ∀ omega, HasWeakHessianOn
      (openCubeSet (originCube d (K : ℤ)))
      (uD omega).toH1Function := fun omega ↦
    weakHessianOfCubeVectorW1pFour (V omega) (hV omega)
  let B := fun R omega ↦ oneStepPrimalSourceCellB (K := K)
    M n (fun w ↦ (uD w).toH1Function) H R omega
  let F := fun R omega ↦
    oneStepUpperPoincareEnergyFactorMeasurable M (n + h)
      (oneStepLocalizationScale n M.delta)
      (translatePotentialSequence (triadicCubeShift R) omega)
  obtain ⟨hFint, hFbudget⟩ := hF M hM n h K hblock hsource hK
  have hFmeas : ∀ R ∈ oneStepSourceCells d K n M.delta,
      Measurable (F R) := by
    intro R _hR
    exact (measurable_oneStepUpperPoincareEnergyFactorMeasurable M (n + h)
      (oneStepLocalizationScale n M.delta)).comp
        (measurable_translatePotentialSequence (triadicCubeShift R))
  have hF0 : ∀ R ∈ oneStepSourceCells d K n M.delta,
      ∀ omega, 0 ≤ F R omega := by
    intro R _hR omega
    dsimp only [F, oneStepUpperPoincareEnergyFactorMeasurable]
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (ahom_pos M (n + h)).le)
      (le_max_right _ _)
  have hB0 : ∀ R ∈ oneStepSourceCells d K n M.delta,
      ∀ omega, 0 ≤ B R omega := by
    intro R hR omega
    simpa only [B, oneStepPrimalSourceCellB, dite_eq_left hR] using
      oneStepCellB_nonneg R ((H omega).restrict (isOpen_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth
          (mem_oneStepSourceCells hR)))
  have hCBreal :
      (CB * ENNReal.ofReal (M.delta ^ (68 : ℕ))).toReal =
        CB.toReal * M.delta ^ (68 : ℕ) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal]
    positivity
  have hfold := finiteFamily_scaledCellBesovMajorant_budget
    (oneStepSourceCells d K n M.delta)
    (oneStepSourceCells_nonempty d K n M.delta)
    F B D cellConst hD0 hcell0 hFmeas hBmeas hF0 hB0
    hFint hBint (mul_nonneg hCF.le (ahom_pos M n).le)
    (mul_nonneg (ENNReal.toReal_nonneg)
      (pow_nonneg M.shellPrefix.delta_pos.le 68))
    hFbudget (by simpa only [hCBreal] using hBbudget)
  have hpow : M.delta ^ (34 : ℕ) ≤ M.delta ^ (30 : ℕ) := by
    exact pow_le_pow_of_le_one M.shellPrefix.delta_pos.le
      (M.shellPrefix.delta_le_half.trans (by norm_num)) (by norm_num)
  have hsqrt : Real.sqrt
        ((D ^ (4 : ℕ) + 1) *
          (CB.toReal * M.delta ^ (68 : ℕ))) =
      Real.sqrt K0 * M.delta ^ (34 : ℕ) := by
    rw [← mul_assoc]
    exact sqrt_const_mul_pow_sixtyeight hK0 M.shellPrefix.delta_pos.le
  let E := fun R omega ↦ oneStepPrimalOscillatoryMajorant (K := K)
    M n h (fun w ↦ (uD w).toH1Function) H R omega
  have hEeq : ∀ R, E R = fun omega ↦
      cellConst * F R omega * oneStepCellBesovError (D * B R omega)
        (B R omega) := by
    intro R
    funext omega
    rfl
  refine ⟨uD, V, hV, huD, ?_, ?_⟩
  · intro R hR
    change Integrable (E R) M.P.toMeasure
    rw [hEeq R]
    exact hfold.1 R hR
  · have hraw := hfold.2
    rw [show (∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, E R omega ∂M.P.toMeasure) =
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, cellConst * F R omega *
            oneStepCellBesovError (D * B R omega) (B R omega)
              ∂M.P.toMeasure by
        apply Finset.sum_congr rfl
        intro R hR
        rw [hEeq R]]
    calc
      _ ≤ cellConst *
          (3 * (CF * ahom M n) * Real.sqrt
            ((D ^ (4 : ℕ) + 1) *
              (CB.toReal * M.delta ^ (68 : ℕ)))) := by
        simpa only [hCBreal] using hraw
      _ = (cellConst * (3 * CF * Real.sqrt K0)) *
          M.delta ^ (34 : ℕ) * ahom M n := by rw [hsqrt]; ring
      _ ≤ O * M.delta ^ (30 : ℕ) * ahom M n := by
        have hconst : cellConst * (3 * CF * Real.sqrt K0) ≤ O := by
          dsimp only [O]
          linarith
        have hscaled :
            (cellConst * (3 * CF * Real.sqrt K0)) * M.delta ^ (34 : ℕ) ≤
              O * M.delta ^ (30 : ℕ) :=
          mul_le_mul hconst hpow
            (pow_nonneg M.shellPrefix.delta_pos.le 34) hO.le
        exact mul_le_mul_of_nonneg_right hscaled (ahom_pos M n).le

private theorem primal_principal_budgets_of_weight
    {delta tau h d C B cell previous weight principal : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (htau0 : 0 ≤ tau) (hh : 0 ≤ h) (hd : 0 < d)
    (hscale : delta * h ≤ 1) (hC : 0 < C) (hB : 0 ≤ B)
    (hcell0 : 0 ≤ cell) (hprevious0 : 0 ≤ previous)
    (hy : delta ^ 2 * |Real.log delta| ≤ 1)
    (hcell : cell ≤ (1 + B * (delta ^ 2 * |Real.log delta|)) * previous)
    (hprincipal : principal = cell * weight)
    (hweight : weight ≤
      1 - 2 * tau * h / d + C * delta ^ 4 * h ^ 2 + C * delta ^ 17) :
    let P := (1 + 2 * C) * (1 + B)
    let A := max C (C * (1 + B))
    principal ≤ P * previous ∧
      principal ≤
        (1 - 2 * tau * h / d + A * delta ^ 4 * h ^ 2) * cell +
          A * delta ^ 15 * previous := by
  let y := delta ^ 2 * |Real.log delta|
  let P := (1 + 2 * C) * (1 + B)
  let A := max C (C * (1 + B))
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hcellCoarse : cell ≤ (1 + B) * previous := by
    calc
      cell ≤ (1 + B * y) * previous := by simpa only [y] using hcell
      _ ≤ (1 + B * 1) * previous := by
        have hBy : B * y ≤ B * 1 := mul_le_mul_of_nonneg_left hy hB
        exact mul_le_mul_of_nonneg_right
          (by linarith) hprevious0
      _ = (1 + B) * previous := by ring
  have hdelta4h2 : delta ^ 4 * h ^ 2 ≤ 1 := by
    have hdh0 : 0 ≤ delta * h := mul_nonneg hdelta0 hh
    have hdhSq : (delta * h) ^ 2 ≤ 1 := by nlinarith
    have hdeltaSq : delta ^ 2 ≤ 1 := by nlinarith [sq_nonneg delta]
    calc
      delta ^ 4 * h ^ 2 = delta ^ 2 * (delta * h) ^ 2 := by ring
      _ ≤ 1 * 1 := mul_le_mul hdeltaSq hdhSq (sq_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hdelta17one : delta ^ 17 ≤ 1 := pow_le_one₀ hdelta0 hdelta1
  have hfactor :
      1 - 2 * tau * h / d + C * delta ^ 4 * h ^ 2 + C * delta ^ 17 ≤
        1 + 2 * C := by
    have hT0 : 0 ≤ 2 * tau * h / d := by positivity
    have hfirst := mul_le_mul_of_nonneg_left hdelta4h2 hC.le
    have hsecond := mul_le_mul_of_nonneg_left hdelta17one hC.le
    linarith
  have hP0 : 0 ≤ 1 + 2 * C := by positivity
  have hrough : principal ≤ P * previous := by
    calc
      principal = cell * weight := hprincipal
      _ ≤ cell * (1 - 2 * tau * h / d + C * delta ^ 4 * h ^ 2 +
          C * delta ^ 17) := mul_le_mul_of_nonneg_left hweight hcell0
      _ ≤ cell * (1 + 2 * C) := mul_le_mul_of_nonneg_left hfactor hcell0
      _ ≤ ((1 + B) * previous) * (1 + 2 * C) :=
        mul_le_mul_of_nonneg_right hcellCoarse hP0
      _ = P * previous := by dsimp only [P]; ring
  have hAleC : C ≤ A := le_max_left _ _
  have hAleTail : C * (1 + B) ≤ A := le_max_right _ _
  have hpow : delta ^ 17 ≤ delta ^ 15 :=
    pow_le_pow_of_le_one hdelta0 hdelta1 (by norm_num)
  have htail : C * delta ^ 17 * cell ≤ A * delta ^ 15 * previous := by
    calc
      C * delta ^ 17 * cell ≤ C * delta ^ 17 * ((1 + B) * previous) :=
        mul_le_mul_of_nonneg_left hcellCoarse
          (mul_nonneg hC.le (pow_nonneg hdelta0 17))
      _ = (C * (1 + B)) * delta ^ 17 * previous := by ring
      _ ≤ A * delta ^ 15 * previous := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hAleTail hpow (pow_nonneg hdelta0 17)
            (le_trans hC.le hAleC)) hprevious0
  have hsharp : principal ≤
      (1 - 2 * tau * h / d + A * delta ^ 4 * h ^ 2) * cell +
        A * delta ^ 15 * previous := by
    calc
      principal = cell * weight := hprincipal
      _ ≤ cell * (1 - 2 * tau * h / d + C * delta ^ 4 * h ^ 2 +
          C * delta ^ 17) := mul_le_mul_of_nonneg_left hweight hcell0
      _ = (1 - 2 * tau * h / d + C * delta ^ 4 * h ^ 2) * cell +
          C * delta ^ 17 * cell := by ring
      _ ≤ (1 - 2 * tau * h / d + A * delta ^ 4 * h ^ 2) * cell +
        A * delta ^ 15 * previous := by
        apply add_le_add
        · have hErr : C * (delta ^ 4 * h ^ 2) ≤
              A * (delta ^ 4 * h ^ 2) :=
            mul_le_mul_of_nonneg_right hAleC
              (mul_nonneg (pow_nonneg hdelta0 4) (sq_nonneg h))
          exact mul_le_mul_of_nonneg_right (by linarith) hcell0
        · exact htail
  exact ⟨hrough, hsharp⟩

/-- The complete high-dimensional upper one-step estimate obtained from the
literal mixed-cutoff finite competitor and the thermodynamic source-cell
budgets. -/
theorem sharpOneStepUpperConclusion_of_concrete
    {d : ℕ} [NeZero d] (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ),
        (h : ℝ) ≤ M.delta⁻¹ →
        16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
        ahom M (n + h) ≤ ahom M n *
          (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / d +
            C * M.delta ^ 4 * (h : ℝ) ^ 2 +
            C * M.delta ^ 2 * |Real.log M.delta|) := by
  obtain ⟨deltaO, O, hdeltaO, hO, hosc⟩ :=
    exists_oneStepPrimalOscillatoryFiniteBudget d
  obtain ⟨Cw, hCw, hweight⟩ :=
    exists_eventually_normalized_sum_integral_oneStepDirichletSourceCellWeight_le d
  obtain ⟨deltaB, B, hdeltaB, hB, hreadout⟩ :=
    exists_source_readouts_le_ahom d
  let P : ℝ := (1 + 2 * Cw) * (1 + B)
  let A0 : ℝ := max Cw (Cw * (1 + B))
  let A : ℝ := 1 + A0 + O + Real.sqrt P * Real.sqrt O
  let Afinal : ℝ := 4 * A
  let deltaSmall : ℝ := min deltaO deltaB
  let Csmall : ℝ := oneStepVariationalConst Afinal B
  let Cbig : ℝ := 2 * deltaSmall⁻¹ ^ (2 : ℕ)
  let C : ℝ := max Csmall Cbig
  have hP : 0 < P := by dsimp only [P]; positivity
  have hA0 : 0 < A0 := hCw.trans_le (le_max_left _ _)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAfinal : 0 < Afinal := by dsimp only [Afinal]; positivity
  have hdeltaSmall : 0 < deltaSmall := by
    dsimp only [deltaSmall]
    positivity
  have hCsmall : 0 < Csmall := oneStepVariationalConst_pos hAfinal hB.le
  have hCbig : 0 < Cbig := by dsimp only [Cbig]; positivity
  have hC : 0 < C := hCsmall.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro M n h hblock hsource
  by_cases hh0 : h = 0
  · subst h
    have hzero : ahom M n ≤ ahom M n *
        (1 + C * M.delta ^ 2 * |Real.log M.delta|) := by
      calc
      ahom M n = ahom M n * 1 := by ring
      _ ≤ ahom M n * (1 + C * M.delta ^ 2 * |Real.log M.delta|) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (by positivity)) (ahom_pos M n).le
    simpa only [Nat.add_zero, Nat.cast_zero, mul_zero, zero_div,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_pow (by norm_num : (4 : ℕ) ≠ 0), add_zero, sub_zero] using hzero
  have hh : 0 < h := Nat.pos_of_ne_zero hh0
  by_cases hsmall : M.delta ≤ deltaSmall
  · have hMO : M.delta ≤ deltaO := hsmall.trans (min_le_left _ _)
    have hMB : M.delta ≤ deltaB := hsmall.trans (min_le_right _ _)
    have hcell := (hreadout M n hMB hsource).1
    let cell := abarScalarReadout M n (oneStepLocalizationScale n M.delta)
    let previous := ahom M n
    have hcell0 : 0 ≤ cell := abarScalarReadout_nonneg M n _
    have hprevious0 : 0 ≤ previous := (ahom_pos M n).le
    let p : Homogenization.Vec d := basisVec ⟨0, by omega⟩
    have hp : vecNormSq p = 1 := vecNormSq_basisVec _
    have hdeltaOne : M.delta ≤ 1 :=
      M.shellPrefix.delta_le_half.trans (by norm_num)
    have hscale : M.delta * (h : ℝ) ≤ 1 := by
      calc
        M.delta * (h : ℝ) ≤ M.delta * M.delta⁻¹ :=
          mul_le_mul_of_nonneg_left hblock M.shellPrefix.delta_pos.le
        _ = 1 := mul_inv_cancel₀ M.shellPrefix.delta_pos.ne'
    have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta ^ 2 := by
      exact (tauSq_le_delta_sq M).trans <| by
        have hlog : Real.log 2 / 2 ≤ 1 := by
          linarith [Real.log_two_lt_d9]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hlog (sq_nonneg M.delta)
    have hy : M.delta ^ 2 * |Real.log M.delta| ≤ 1 :=
      (delta_sq_mul_abs_log_le_self M.shellPrefix.delta_pos hdeltaOne).trans
        hdeltaOne
    have hcell' : cell ≤
        (1 + B * (M.delta ^ 2 * |Real.log M.delta|)) * previous := by
      simpa only [cell, previous, mul_assoc] using hcell
    have hsqrtPO0 : 0 ≤ Real.sqrt P * Real.sqrt O := by positivity
    have hA0A : A0 ≤ A := by
      dsimp only [A]
      linarith [hO]
    have hOA : O ≤ A := by
      dsimp only [A]
      linarith [hA0]
    have hPOA : Real.sqrt P * Real.sqrt O ≤ A := by
      dsimp only [A]
      linarith [hA0, hO]
    have hfinite : ∀ᶠ K : ℕ in Filter.atTop,
        oneStepPrimalFiniteVolumeReadout M (n + h) K p ≤
          (1 / 2 - _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
              Afinal * M.delta ^ 4 * (h : ℝ) ^ 2) * cell +
            Afinal * M.delta ^ 15 * previous := by
      filter_upwards [hweight M n h p hsource hh hp hblock,
        Filter.eventually_atTop.2 ⟨oneStepLocalizationScale n M.delta,
          fun K hK ↦ hK⟩] with K hweightK hK
      obtain ⟨uD, V, hV, huD, hEint, hEbudget⟩ :=
        hosc M hMO n h K p hp hh hblock hsource hK
      let H : ∀ omega, HasWeakHessianOn
          (openCubeSet (originCube d (K : ℤ)))
          (uD omega).toH1Function := fun omega ↦
        weakHessianOfCubeVectorW1pFour (V omega) (hV omega)
      let principal := fun R omega ↦
        oneStepPrimalPrincipalMajorant (K := K) M n h p R omega hh
      let oscillatory := fun R omega ↦
        oneStepPrimalOscillatoryMajorant (K := K) M n h
          (fun w ↦ (uD w).toH1Function) H R omega
      let target := fun omega ↦ vecDot p
        (matVecMul (randomAMatrix M (n + h)
          (Ch02.cubeDomain (originCube d (K : ℤ))) omega) p)
      let weightAverage : ℝ :=
        (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, oneStepUpperSourceCellWeight M n h R omega *
              vecNormSq (oneStepDirichletCellSlope M n h p
                (originCube d (K : ℤ)) R omega hh) ∂M.P.toMeasure
      let principalAverage : ℝ :=
        (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, principal R omega ∂M.P.toMeasure
      have hprincipalEq : principalAverage = cell * weightAverage := by
        exact normalized_sum_integral_upperWeight_mul_dirichletSourceCellSlope_eq
            M n h p hK hh hp
      obtain ⟨hprincipalRough, hprincipalSharp0⟩ :=
        primal_principal_budgets_of_weight
          M.shellPrefix.delta_pos.le hdeltaOne M.G4.tauSq_pos.le
          (Nat.cast_nonneg h) (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd))
          hscale hCw hB.le hcell0 hprevious0 hy hcell' hprincipalEq hweightK
      have hprincipalSharp : principalAverage ≤
          (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
              A * M.delta ^ 4 * (h : ℝ) ^ 2) * cell +
            A * M.delta ^ 15 * previous := by
        calc
          principalAverage ≤
              (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
                  A0 * M.delta ^ 4 * (h : ℝ) ^ 2) * cell +
                A0 * M.delta ^ 15 * previous := hprincipalSharp0
          _ ≤ (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
                  A * M.delta ^ 4 * (h : ℝ) ^ 2) * cell +
                A * M.delta ^ 15 * previous := by
            apply add_le_add
            · have hErr : A0 * (M.delta ^ 4 * (h : ℝ) ^ 2) ≤
                  A * (M.delta ^ 4 * (h : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_right hA0A
                  (mul_nonneg (pow_nonneg M.shellPrefix.delta_pos.le 4)
                    (sq_nonneg (h : ℝ)))
              exact mul_le_mul_of_nonneg_right (by linarith) hcell0
            · exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hA0A
                  (pow_nonneg M.shellPrefix.delta_pos.le 15)) hprevious0
      have htargetInt : Integrable target M.P.toMeasure := by
        have hhalf := integrable_randomAMatrix_quadratic M (n + h)
          (Ch02.cubeDomain (originCube d (K : ℤ))) p
        apply (hhalf.const_mul 2).congr
        filter_upwards with omega
        dsimp only [target]
        ring
      have hprincipalInt : ∀ R ∈ oneStepSourceCells d K n M.delta,
          Integrable (principal R) M.P.toMeasure := by
        intro R _hR
        simpa only [principal] using
          integrable_oneStepPrimalPrincipalMajorant M n h p R hh hp
      have hprincipal0 : ∀ R ∈ oneStepSourceCells d K n M.delta,
          0 ≤ᵐ[M.P.toMeasure] principal R := by
        intro R _hR
        exact Filter.Eventually.of_forall fun omega ↦ by
          exact oneStepPrimalPrincipalMajorant_nonneg M n h p R omega hh
      have hoscillatory0 : ∀ R ∈ oneStepSourceCells d K n M.delta,
          0 ≤ᵐ[M.P.toMeasure] oscillatory R := by
        intro R hR
        exact Filter.Eventually.of_forall fun omega ↦ by
          have hBcell : 0 ≤ oneStepPrimalSourceCellB M n
              (fun w ↦ (uD w).toH1Function) H R omega := by
            simpa only [oneStepPrimalSourceCellB, dite_eq_left hR] using
              oneStepCellB_nonneg R ((H omega).restrict (isOpen_openCubeSet R)
                (openCubeSet_subset_of_mem_descendantsAtDepth
                  (mem_oneStepSourceCells hR)))
          dsimp only [oscillatory, oneStepPrimalOscillatoryMajorant]
          exact mul_nonneg
            (mul_nonneg (by
              dsimp only [oneStepPrimalCellEnergyConst]
              positivity)
              (by
                dsimp only [oneStepUpperPoincareEnergyFactorMeasurable]
                exact mul_nonneg
                  (mul_nonneg (sq_nonneg _) (ahom_pos M (n + h)).le)
                  (le_max_right _ _)))
            (oneStepCellBesovError_nonneg
              (mul_nonneg
                (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
                hBcell)
              hBcell)
      have hpointwise := ae_half_randomAMatrix_le_oneStepPrimalMajorants
        M n h p hh hK uD huD V hV
      have hpenultimate := one_step_upper_penultimate_of_ae_finite_majorants
        (oneStepSourceCells d K n M.delta)
        (oneStepSourceCells_nonempty d K n M.delta)
        target principal oscillatory htargetInt hprincipalInt
        (by simpa only [oscillatory] using hEint)
        hprincipal0 hoscillatory0
        (by simpa only [target, principal, oscillatory, H] using hpointwise)
        M.shellPrefix.delta_pos.le hdeltaOne hA.le hP.le hO.le
        hcell0 hprevious0 hPOA hOA
        (by simpa only [principalAverage, P, previous] using hprincipalRough)
        (by simpa only [principalAverage] using hprincipalSharp)
        (by simpa only [oscillatory, previous] using hEbudget)
      rw [oneStepPrimalFiniteVolumeReadout_eq_integral]
      rw [integral_const_mul]
      simpa only [target, Afinal] using hpenultimate
    have hlimit : (1 / 2 : ℝ) * ahom M (n + h) ≤
        (1 / 2 - _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
            Afinal * M.delta ^ 4 * (h : ℝ) ^ 2) * cell +
          Afinal * M.delta ^ 15 * previous := by
      exact le_of_tendsto (by
        simpa only [hp, mul_one] using
          tendsto_oneStepPrimalFiniteVolumeReadout M (n + h) p) hfinite
    have hclosed := one_step_upper_of_penultimate
      M.shellPrefix.delta_pos M.shellPrefix.delta_le_half M.G4.tauSq_pos.le htau
      (Nat.cast_nonneg h) hscale
      (half_le_abs_log_delta M.shellPrefix.delta_pos M.shellPrefix.delta_le_half)
      (by exact_mod_cast (le_trans (by norm_num : 2 ≤ 3) hd))
      hAfinal hB.le hprevious0 (by simpa [mul_assoc] using hcell') hlimit
    have hCsmallC : Csmall ≤ C := le_max_left _ _
    calc
      ahom M (n + h) ≤ ahom M n *
          (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
            Csmall * M.delta ^ 4 * (h : ℝ) ^ 2 +
            Csmall * M.delta ^ 2 * |Real.log M.delta|) := by
        simpa only [Csmall, Afinal, cell, previous] using hclosed
      _ ≤ ahom M n *
          (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
            C * M.delta ^ 4 * (h : ℝ) ^ 2 +
            C * M.delta ^ 2 * |Real.log M.delta|) := by
        apply mul_le_mul_of_nonneg_left _ (ahom_pos M n).le
        have hsum0 : 0 ≤ M.delta ^ 4 * (h : ℝ) ^ 2 +
            M.delta ^ 2 * |Real.log M.delta| := by positivity
        have hmul := mul_le_mul_of_nonneg_right hCsmallC hsum0
        nlinarith
  · have hdeltaLower : deltaSmall ≤ M.delta := le_of_not_ge hsmall
    have hlogHalf : (1 / 2 : ℝ) ≤ |Real.log M.delta| :=
      half_le_abs_log_delta M.shellPrefix.delta_pos M.shellPrefix.delta_le_half
    have hsq : deltaSmall ^ 2 ≤ M.delta ^ 2 := by
      exact pow_le_pow_left₀ hdeltaSmall.le hdeltaLower 2
    have hCbigC : Cbig ≤ C := le_max_right _ _
    have hidentity : Cbig * deltaSmall ^ 2 * (1 / 2 : ℝ) = 1 := by
      dsimp only [Cbig]
      field_simp [hdeltaSmall.ne']
    have hcomp : Cbig * deltaSmall ^ 2 ≤ C * M.delta ^ 2 :=
      mul_le_mul hCbigC hsq (sq_nonneg deltaSmall) hC.le
    have hcomp' : Cbig * deltaSmall ^ 2 * (1 / 2 : ℝ) ≤
        C * M.delta ^ 2 * |Real.log M.delta| :=
      mul_le_mul hcomp hlogHalf (by norm_num)
        (mul_nonneg hC.le (sq_nonneg M.delta))
    have herrorOne : 1 ≤ C * M.delta ^ 2 * |Real.log M.delta| := by
      rw [← hidentity]
      exact hcomp'
    have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta ^ 2 := by
      exact (tauSq_le_delta_sq M).trans <| by
        have hlog : Real.log 2 / 2 ≤ 1 := by
          linarith [Real.log_two_lt_d9]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hlog (sq_nonneg M.delta)
    have htauh : _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) ≤ M.delta := by
      calc
        _ ≤ M.delta ^ 2 * (h : ℝ) :=
          mul_le_mul_of_nonneg_right htau (Nat.cast_nonneg h)
        _ ≤ M.delta ^ 2 * M.delta⁻¹ :=
          mul_le_mul_of_nonneg_left hblock (sq_nonneg M.delta)
        _ = M.delta := by field_simp [M.shellPrefix.delta_pos.ne']
    have hdreal : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hratio : 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) /
        (d : ℝ) ≤ 1 := by
      apply (div_le_one (by positivity : (0 : ℝ) < d)).2
      nlinarith [M.shellPrefix.delta_le_half]
    have hfactor : 1 ≤
        1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
          C * M.delta ^ 4 * (h : ℝ) ^ 2 +
          C * M.delta ^ 2 * |Real.log M.delta| := by
      have herr0 : 0 ≤ C * M.delta ^ 4 * (h : ℝ) ^ 2 := by positivity
      calc
        1 ≤ 1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
            C * M.delta ^ 2 * |Real.log M.delta| := by linarith
        _ ≤ (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
              C * M.delta ^ 2 * |Real.log M.delta|) +
            C * M.delta ^ 4 * (h : ℝ) ^ 2 := le_add_of_nonneg_right herr0
        _ = _ := by ring
    have hmono : ahom M (n + h) ≤ ahom M n :=
      ((SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds (d := d)).2
        M (n + h) n (Nat.lt_add_of_pos_right hh)).1
    calc
      ahom M (n + h) ≤ ahom M n := hmono
      _ = ahom M n * 1 := by ring
      _ ≤ ahom M n *
          (1 - 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) / (d : ℝ) +
            C * M.delta ^ 4 * (h : ℝ) ^ 2 +
            C * M.delta ^ 2 * |Real.log M.delta|) :=
        mul_le_mul_of_nonneg_left hfactor (ahom_pos M n).le

end

end SubdiffusiveProcess.Providers.Section5

