module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCanonicalCenteredHessian
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannCellBesov
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannHessianPackage
public import SubdiffusiveProcess.Providers.Section5.OneStepLiteralRandomCellPoincare

@[expose] public section

/-!
# Canonical centered cells in the literal cutoff Poincare estimate

The measurable origin-cube solution is restricted and centered on a source
cell.  Its gradient agrees almost everywhere with the translation-covariant
cell fluctuation.  The cell minimizer is transported across that equality,
so the deterministic quarter-order Poincare estimate applies to the exact
datum used by the stochastic partition.
-/

open MeasureTheory Homogenization Homogenization.Book

namespace SubdiffusiveProcess.Providers.Section5

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- A primal source-cell fluctuation admits a literal-cutoff minimizer whose
energy is bounded by the centered canonical Hessian observable. -/
theorem exists_oneStepDirichletCellFluctuation_energy_le_poincare_quarter
    {d j : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h)
    (R : Homogenization.TriadicCube d)
    (hR : R ∈ descendantsAtDepth (originCube d m) j)
    (V : CubeVectorW1pFunction (originCube d m) oneStepFourExponent)
    (hV : V.toField =
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad) :
    let uR := oneStepCenteredRestriction
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function hR
    let HR := HasWeakHessianOn.centeredRestriction
      (weakHessianOfCubeVectorW1pFour V hV) hR
    ∃ X : OneStepDirichletCellMinimizer R
        (Ch03.publicCoeffField R
          (aCutoffEnvelopeTriadicCoeffFamily M n omega))
        (oneStepDirichletCellFluctuationField M n h p
          (originCube d m) R omega hh),
      volumeAverage (openCubeSet R) (fun x ↦
          vecDot (X.field x)
            (matVecMul
              (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) x)
              (X.field x))) ≤
        2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
            oneStepQuarterCellConst d) ^ 2 *
          (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
            Ch03.poincareUpperEllipticityFactor R
              (aCutoffEnvelopeTriadicCoeffFamily M n omega) (1 / 4 : ℝ)
                (.finite 1)) ^ 2 *
          oneStepCellBesovError
            (cubeLpNorm R (2 : ENNReal) uR.grad) (oneStepCellB R HR) := by
  let uR := oneStepCenteredRestriction
    (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function hR
  let HR := HasWeakHessianOn.centeredRestriction
    (weakHessianOfCubeVectorW1pFour V hV) hR
  let a := Ch03.publicCoeffField R
    (aCutoffEnvelopeTriadicCoeffFamily M n omega)
  have hEll := Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet R
    (aCutoffEnvelopeTriadicCoeffFamily M n omega)
  let X0 : OneStepDirichletCellMinimizer R a uR.grad :=
    Classical.choice (exists_oneStepDirichletCellMinimizer R hEll uR.grad
      uR.grad_memVectorL2)
  have hdatum : uR.grad =ᵐ[volumeMeasureOn (openCubeSet R)]
      oneStepDirichletCellFluctuationField M n h p
        (originCube d m) R omega hh := by
    simpa only [uR] using
      oneStepCanonicalCenteredRestriction_grad_ae_eq_cellFluctuation
        M n h p m omega hh R hR
  let X : OneStepDirichletCellMinimizer R a
      (oneStepDirichletCellFluctuationField M n h p
        (originCube d m) R omega hh) := X0.congrDatum hdatum
  refine ⟨X, ?_⟩
  have hbase := oneStep_dirichletCell_literalCutoff_energy_le_poincare_quarter
    M n omega R uR HR X0
      (cubeAverageVec_oneStepCenteredRestriction_grad_eq_zero
        (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function hR)
  have hfield : X.field =ᵐ[volumeMeasureOn (openCubeSet R)] X0.field := by
    filter_upwards [hdatum] with x hx
    simp only [X, OneStepDirichletCellMinimizer.field,
      OneStepDirichletCellMinimizer.congrDatum]
    rw [← hx]
  have henergy :
      volumeAverage (openCubeSet R) (fun x ↦
          vecDot (X.field x)
            (matVecMul
              (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) x)
              (X.field x))) =
        volumeAverage (openCubeSet R) (fun x ↦
          vecDot (X0.field x)
            (matVecMul
              (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) x)
              (X0.field x))) := by
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hfield] with x hx
    rw [hx]
  rw [henergy]
  simpa only [uR, HR, a, X0] using hbase

/-- The shell solution and the coefficient used for the localized cell
minimizer may live at different cutoffs.  This is the literal Step 2 form:
the fluctuation comes from the block `(n,n+h]`, while the cell energy is
measured with the high cutoff `L` (ultimately `L = n+h`). -/
theorem exists_oneStepDirichletCellFluctuation_energy_le_poincare_quarter_at_cutoff
    {d j : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n h : ℕ)
    (p : Homogenization.Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h)
    (R : Homogenization.TriadicCube d)
    (hR : R ∈ descendantsAtDepth (originCube d m) j)
    (V : CubeVectorW1pFunction (originCube d m) oneStepFourExponent)
    (hV : V.toField =
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad) :
    let uR := oneStepCenteredRestriction
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function hR
    let HR := HasWeakHessianOn.centeredRestriction
      (weakHessianOfCubeVectorW1pFour V hV) hR
    ∃ X : OneStepDirichletCellMinimizer R
        (Ch03.publicCoeffField R
          (aCutoffEnvelopeTriadicCoeffFamily M L omega))
        (oneStepDirichletCellFluctuationField M n h p
          (originCube d m) R omega hh),
      volumeAverage (openCubeSet R) (fun x ↦
          vecDot (X.field x)
            (matVecMul
              (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)
              (X.field x))) ≤
        2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
            oneStepQuarterCellConst d) ^ 2 *
          (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
            Ch03.poincareUpperEllipticityFactor R
              (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4 : ℝ)
                (.finite 1)) ^ 2 *
          oneStepCellBesovError
            (cubeLpNorm R (2 : ENNReal) uR.grad) (oneStepCellB R HR) := by
  let uR := oneStepCenteredRestriction
    (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function hR
  let HR := HasWeakHessianOn.centeredRestriction
    (weakHessianOfCubeVectorW1pFour V hV) hR
  let a := Ch03.publicCoeffField R
    (aCutoffEnvelopeTriadicCoeffFamily M L omega)
  have hEll := Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet R
    (aCutoffEnvelopeTriadicCoeffFamily M L omega)
  let X0 : OneStepDirichletCellMinimizer R a uR.grad :=
    Classical.choice (exists_oneStepDirichletCellMinimizer R hEll uR.grad
      uR.grad_memVectorL2)
  have hdatum : uR.grad =ᵐ[volumeMeasureOn (openCubeSet R)]
      oneStepDirichletCellFluctuationField M n h p
        (originCube d m) R omega hh := by
    simpa only [uR] using
      oneStepCanonicalCenteredRestriction_grad_ae_eq_cellFluctuation
        M n h p m omega hh R hR
  let X : OneStepDirichletCellMinimizer R a
      (oneStepDirichletCellFluctuationField M n h p
        (originCube d m) R omega hh) := X0.congrDatum hdatum
  refine ⟨X, ?_⟩
  have hbase := oneStep_dirichletCell_literalCutoff_energy_le_poincare_quarter
    M L omega R uR HR X0
      (cubeAverageVec_oneStepCenteredRestriction_grad_eq_zero
        (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function hR)
  have hfield : X.field =ᵐ[volumeMeasureOn (openCubeSet R)] X0.field := by
    filter_upwards [hdatum] with x hx
    simp only [X, OneStepDirichletCellMinimizer.field,
      OneStepDirichletCellMinimizer.congrDatum]
    rw [← hx]
  have henergy :
      volumeAverage (openCubeSet R) (fun x ↦
          vecDot (X.field x)
            (matVecMul
              (scalarCoeffField
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)
              (X.field x))) =
        volumeAverage (openCubeSet R) (fun x ↦
          vecDot (X0.field x)
            (matVecMul
              (scalarCoeffField
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)
              (X0.field x))) := by
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hfield] with x hx
    rw [hx]
  rw [henergy]
  simpa only [uR, HR, a, X0] using hbase

/-- Selection-independent form of the mixed-cutoff Dirichlet estimate.
Every minimizer for the concrete source-cell fluctuation has the same
`aCutoff M L` energy, so the canonical representative supplied above may be
replaced by the minimizer used in the finite patch. -/
theorem oneStepDirichletCellFluctuation_energy_le_poincare_quarter_at_cutoff
    {d j : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n h : ℕ)
    (p : Homogenization.Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h)
    (R : Homogenization.TriadicCube d)
    (hR : R ∈ descendantsAtDepth (originCube d m) j)
    (V : CubeVectorW1pFunction (originCube d m) oneStepFourExponent)
    (hV : V.toField =
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad)
    (Y : OneStepDirichletCellMinimizer R
      (Ch03.publicCoeffField R
        (aCutoffEnvelopeTriadicCoeffFamily M L omega))
      (oneStepDirichletCellFluctuationField M n h p
        (originCube d m) R omega hh)) :
    let uR := oneStepCenteredRestriction
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function hR
    let HR := HasWeakHessianOn.centeredRestriction
      (weakHessianOfCubeVectorW1pFour V hV) hR
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (Y.field x)
          (matVecMul
            (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)
            (Y.field x))) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          oneStepQuarterCellConst d) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareUpperEllipticityFactor R
            (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4 : ℝ)
              (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm R (2 : ENNReal) uR.grad) (oneStepCellB R HR) := by
  obtain ⟨X, hX⟩ :=
    exists_oneStepDirichletCellFluctuation_energy_le_poincare_quarter_at_cutoff
      M L n h p m omega hh R hR V hV
  have hEll := Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet R
    (aCutoffEnvelopeTriadicCoeffFamily M L omega)
  have hfield := X.field_ae_eq Y hEll
  have henergy :
      volumeAverage (openCubeSet R) (fun x ↦
          vecDot (Y.field x)
            (matVecMul
              (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)
              (Y.field x))) =
        volumeAverage (openCubeSet R) (fun x ↦
          vecDot (X.field x)
            (matVecMul
              (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)
              (X.field x))) := by
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hfield] with x hx
    rw [hx]
  rw [henergy]
  exact hX

/-- Representative-stable mixed-cutoff estimate.  The descendant CZ package
chooses a weak solution together with its Hessian; weak uniqueness identifies
its centered gradient with the concrete source-cell fluctuation. -/
theorem oneStepDirichletCellFluctuation_energy_le_poincare_quarter_at_cutoff_of_solution
    {d j : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n h : ℕ)
    (p : Homogenization.Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h)
    (u : H10Function (openCubeSet (originCube d m)))
    (hu : CubeDirichletDivergenceProblem (originCube d m) u
      (oneStepShellForcingH1 M n h omega p (originCube d m) hh).toField)
    (R : Homogenization.TriadicCube d)
    (hR : R ∈ descendantsAtDepth (originCube d m) j)
    (V : CubeVectorW1pFunction (originCube d m) oneStepFourExponent)
    (hV : V.toField = u.toH1Function.grad)
    (Y : OneStepDirichletCellMinimizer R
      (Ch03.publicCoeffField R
        (aCutoffEnvelopeTriadicCoeffFamily M L omega))
      (oneStepDirichletCellFluctuationField M n h p
        (originCube d m) R omega hh)) :
    let uR := oneStepCenteredRestriction u.toH1Function hR
    let HR := HasWeakHessianOn.centeredRestriction
      (weakHessianOfCubeVectorW1pFour V hV) hR
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (Y.field x)
          (matVecMul
            (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)
            (Y.field x))) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          oneStepQuarterCellConst d) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareUpperEllipticityFactor R
            (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4 : ℝ)
              (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm R (2 : ENNReal) uR.grad) (oneStepCellB R HR) := by
  let uR := oneStepCenteredRestriction u.toH1Function hR
  let HR := HasWeakHessianOn.centeredRestriction
    (weakHessianOfCubeVectorW1pFour V hV) hR
  let a := Ch03.publicCoeffField R
    (aCutoffEnvelopeTriadicCoeffFamily M L omega)
  have hEll := Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet R
    (aCutoffEnvelopeTriadicCoeffFamily M L omega)
  let X0 : OneStepDirichletCellMinimizer R a uR.grad :=
    Classical.choice (exists_oneStepDirichletCellMinimizer R hEll uR.grad
      uR.grad_memVectorL2)
  have hdatum : uR.grad =ᵐ[volumeMeasureOn (openCubeSet R)]
      oneStepDirichletCellFluctuationField M n h p
        (originCube d m) R omega hh := by
    simpa only [uR] using
      oneStepShellCenteredRestriction_grad_ae_eq_cellFluctuation
        M n h p m omega hh u hu R hR
  let X : OneStepDirichletCellMinimizer R a
      (oneStepDirichletCellFluctuationField M n h p
        (originCube d m) R omega hh) := X0.congrDatum hdatum
  have hbase := oneStep_dirichletCell_literalCutoff_energy_le_poincare_quarter
    M L omega R uR HR X0
      (cubeAverageVec_oneStepCenteredRestriction_grad_eq_zero
        u.toH1Function hR)
  have hfieldX : X.field =ᵐ[volumeMeasureOn (openCubeSet R)] X0.field := by
    filter_upwards [hdatum] with x hx
    simp only [X, OneStepDirichletCellMinimizer.field,
      OneStepDirichletCellMinimizer.congrDatum]
    rw [← hx]
  have hfieldY : Y.field =ᵐ[volumeMeasureOn (openCubeSet R)] X.field :=
    Y.field_ae_eq X hEll
  have henergy :
      volumeAverage (openCubeSet R) (fun x ↦
          vecDot (Y.field x)
            (matVecMul
              (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)
              (Y.field x))) =
        volumeAverage (openCubeSet R) (fun x ↦
          vecDot (X0.field x)
            (matVecMul
              (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)
              (X0.field x))) := by
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hfieldY, hfieldX] with x hy hx
    rw [hy, hx]
  rw [henergy]
  simpa only [uR, HR, a, X0] using hbase

/-- Selection-independent form: every minimizer for the concrete source-cell
fluctuation has the same literal energy and hence obeys the canonical bound. -/
theorem oneStepDirichletCellFluctuation_energy_le_poincare_quarter
    {d j : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h)
    (R : Homogenization.TriadicCube d)
    (hR : R ∈ descendantsAtDepth (originCube d m) j)
    (V : CubeVectorW1pFunction (originCube d m) oneStepFourExponent)
    (hV : V.toField =
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad)
    (Y : OneStepDirichletCellMinimizer R
      (Ch03.publicCoeffField R
        (aCutoffEnvelopeTriadicCoeffFamily M n omega))
      (oneStepDirichletCellFluctuationField M n h p
        (originCube d m) R omega hh)) :
    let uR := oneStepCenteredRestriction
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function hR
    let HR := HasWeakHessianOn.centeredRestriction
      (weakHessianOfCubeVectorW1pFour V hV) hR
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (Y.field x)
          (matVecMul
            (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) x)
            (Y.field x))) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          oneStepQuarterCellConst d) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareUpperEllipticityFactor R
            (aCutoffEnvelopeTriadicCoeffFamily M n omega) (1 / 4 : ℝ)
              (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm R (2 : ENNReal) uR.grad) (oneStepCellB R HR) := by
  obtain ⟨X, hX⟩ :=
    exists_oneStepDirichletCellFluctuation_energy_le_poincare_quarter
      M n h p m omega hh R hR V hV
  have hEll := Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet R
    (aCutoffEnvelopeTriadicCoeffFamily M n omega)
  have hfield := X.field_ae_eq Y hEll
  have henergy :
      volumeAverage (openCubeSet R) (fun x ↦
          vecDot (Y.field x)
            (matVecMul
              (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) x)
              (Y.field x))) =
        volumeAverage (openCubeSet R) (fun x ↦
          vecDot (X.field x)
            (matVecMul
              (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) x)
              (X.field x))) := by
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hfield] with x hx
    rw [hx]
  rw [henergy]
  exact hX

/-- Selection-independent dual source-cell estimate for the literal
solenoidal fluctuation.  A weak-Hessian representative of the parent
Neumann solution supplies the vector-`H¹` carrier; no gradient fiction is
used for the centered flux datum. -/
theorem oneStepNeumannCellFluctuation_energy_le_poincare_quarter
    {d j : ℕ} [NeZero d] {Q R : Homogenization.TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h)
    (hR : R ∈ descendantsAtDepth Q j)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ))
    (hgradEq : uS.grad =
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad)
    (Y : OneStepNeumannCellMinimizer R
      (Ch03.publicCoeffField R
        (aCutoffEnvelopeTriadicCoeffFamily M n omega))
      (oneStepNeumannCellFluctuationField M n h q Q R omega hh)) :
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (Y.flux x)
          (matVecMul
            ((blockMatrixOfCoeff (scalarCoeffField
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) x)).lowerRight)
            (Y.flux x))) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareLowerEllipticityFactor R
            (aCutoffEnvelopeTriadicCoeffFamily M n omega) (1 / 4 : ℝ)
              (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm R (2 : ENNReal)
            (oneStepNeumannCellFluctuationField M n h q Q R omega hh))
          (cubeScaleFactor R * ∑ k : Fin d,
            cubeLpNorm R (2 : ENNReal) (fun x ↦ euclideanNorm
              (((oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf
                ).coord k).grad x))) := by
  let G := oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf
  have hdatum : oneStepNeumannCellFluctuationField M n h q Q R omega hh =
      cubeFluctuationVec R G.toField :=
    oneStepNeumannCellFluctuationField_eq_cubeFluctuationVec_rawCellH1
      M n h omega q hh uS H hR hRhalf hgradEq
  simpa only [G] using
    oneStep_neumannCell_vectorH1_literalCutoff_energy_le_poincare_quarter
      M n omega R G Y hdatum

/-- Representative-stable dual source-cell estimate.  This version accepts
the `L²` identification delivered by the measurable Neumann operator. -/
theorem oneStepNeumannCellFluctuation_energy_le_poincare_quarter_ae
    {d j : ℕ} [NeZero d] {Q R : Homogenization.TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h)
    (hR : R ∈ descendantsAtDepth Q j)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ))
    (hgradEq : uS.grad =ᵐ[volumeMeasureOn (openCubeSet R)]
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad)
    (Y : OneStepNeumannCellMinimizer R
      (Ch03.publicCoeffField R
        (aCutoffEnvelopeTriadicCoeffFamily M n omega))
      (oneStepNeumannCellFluctuationField M n h q Q R omega hh)) :
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (Y.flux x)
          (matVecMul
            ((blockMatrixOfCoeff (scalarCoeffField
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) x)).lowerRight)
            (Y.flux x))) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareLowerEllipticityFactor R
            (aCutoffEnvelopeTriadicCoeffFamily M n omega) (1 / 4 : ℝ)
              (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm R (2 : ENNReal)
            (cubeFluctuationVec R
              (oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf).toField))
          (cubeScaleFactor R * ∑ k : Fin d,
            cubeLpNorm R (2 : ENNReal) (fun x ↦ euclideanNorm
              (((oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf
                ).coord k).grad x))) := by
  let G := oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf
  have hdatum : oneStepNeumannCellFluctuationField M n h q Q R omega hh
      =ᵐ[volumeMeasureOn (openCubeSet R)] cubeFluctuationVec R G.toField :=
    oneStepNeumannCellFluctuationField_ae_eq_cubeFluctuationVec_rawCellH1
      M n h omega q hh uS H hR hRhalf hgradEq
  simpa only [G] using
    oneStep_neumannCell_vectorH1_literalCutoff_energy_le_poincare_quarter_ae
      M n omega R G Y hdatum

/-- Canonical-solution specialization of the preceding dual cell estimate.
The weak Hessian is produced by the deterministic interior CZ theorem for
the already fixed triadic Neumann solution. -/
theorem exists_oneStepNeumannCellFluctuation_energy_le_poincare_quarter
    {d j : ℕ} [NeZero d] {Q R : Homogenization.TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h)
    (hR : R ∈ descendantsAtDepth Q j)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ))
    (Y : OneStepNeumannCellMinimizer R
      (Ch03.publicCoeffField R
        (aCutoffEnvelopeTriadicCoeffFamily M n omega))
      (oneStepNeumannCellFluctuationField M n h q Q R omega hh)) :
    ∃ (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
      (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS),
      H.hessianCoordL2NormSum ≤
          ∑ i : Fin d, ∑ _j : Fin d,
            @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound
              d Q
              (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function
              (oneStepShellForcingH1 M n h omega q Q hh).divergence i
              (1 / 2 : ℝ) (7 / 12 : ℝ) (3 / 4 : ℝ) (7 / 8 : ℝ)
              (CubeCalderonZygmund.outerThreeQuarterSevenEighthCutoff Q) ∧
      volumeAverage (openCubeSet R) (fun x ↦
          vecDot (Y.flux x)
            (matVecMul
              ((blockMatrixOfCoeff (scalarCoeffField
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) x)).lowerRight)
              (Y.flux x))) ≤
        2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
            max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 *
          (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
            Ch03.poincareLowerEllipticityFactor R
              (aCutoffEnvelopeTriadicCoeffFamily M n omega) (1 / 4 : ℝ)
                (.finite 1)) ^ 2 *
          oneStepCellBesovError
            (cubeLpNorm R (2 : ENNReal)
              (oneStepNeumannCellFluctuationField M n h q Q R omega hh))
            (cubeScaleFactor R * ∑ k : Fin d,
              cubeLpNorm R (2 : ENNReal) (fun x ↦ euclideanNorm
                (((oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf
                  ).coord k).grad x))) := by
  obtain ⟨uS, hgradEq, H, hH⟩ :=
    exists_oneStepTriadicNeumann_innerHalfWeakHessian_reduced
      M n h omega q Q hh
  refine ⟨uS, H, hH, ?_⟩
  exact oneStepNeumannCellFluctuation_energy_le_poincare_quarter
    M n h q omega hh hR uS H hRhalf hgradEq Y

/-- Measurable-family version of the dual source-cell estimate.  The Hessian
observable is Borel, while Neumann uniqueness supplies precisely the a.e.
canonical-gradient identification required by the representative-stable
cell estimate. -/
theorem exists_measurable_oneStepNeumannCellFluctuation_energy_le_poincare_quarter
    {d j : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (m : ℤ)
    (R : Homogenization.TriadicCube d) (hh : 0 < h)
    (hR : R ∈ descendantsAtDepth (originCube d m) j)
    (hRhalf : openCubeSet R ⊆
      scaledOpenCubeSet (originCube d m) (1 / 2 : ℝ)) :
    ∃ (uS : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → H1Function
          (scaledOpenCubeSet (originCube d m) (1 / 2 : ℝ)))
      (H : ∀ omega, HasWeakHessianOn
        (scaledOpenCubeSet (originCube d m) (1 / 2 : ℝ)) (uS omega)),
      Measurable (fun omega ↦
          oneStepCellCenteredL2 (originCube d m) R
            (oneStepNeumannSlopeL2 M n h q
              (originCube d m) omega hh)) ∧
      Measurable (fun omega ↦
          oneStepCellB R
            ((H omega).restrict (isOpen_openCubeSet R) hRhalf)) ∧
      ∀ omega (Y : OneStepNeumannCellMinimizer R
          (Ch03.publicCoeffField R
            (aCutoffEnvelopeTriadicCoeffFamily M n omega))
          (oneStepNeumannCellFluctuationField M n h q
            (originCube d m) R omega hh)),
        volumeAverage (openCubeSet R) (fun x ↦
            vecDot (Y.flux x)
              (matVecMul
                ((blockMatrixOfCoeff (scalarCoeffField
                  (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega) x)).lowerRight)
                (Y.flux x))) ≤
          2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
              max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 *
            (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
              Ch03.poincareLowerEllipticityFactor R
                (aCutoffEnvelopeTriadicCoeffFamily M n omega) (1 / 4 : ℝ)
                  (.finite 1)) ^ 2 *
            oneStepCellBesovError
              (oneStepCellCenteredL2 (originCube d m) R
                (oneStepNeumannSlopeL2 M n h q
                  (originCube d m) omega hh))
              ((d : ℝ) *
                (oneStepShellForcingCellB
                    (Q := originCube d m) (R := R) M n h omega q hh +
                  oneStepCellB R
                    ((H omega).restrict (isOpen_openCubeSet R) hRhalf))) := by
  obtain ⟨uN, uS, H, huN, huSgrad, hH, hmeas⟩ :=
    exists_measurable_oneStepShellNeumann_innerCellB d
      M n h q m R hh hRhalf
  have hmeasSlope : Measurable (oneStepNeumannSlopeL2 M n h q
      (originCube d m) · hh) :=
    (measurable_oneStepNeumannSlopeL2_potentialShellIndexSigma_Ioi
      M n h q (originCube d m) hh).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl
  have hmeasA : Measurable (fun omega ↦
      oneStepCellCenteredL2 (originCube d m) R
        (oneStepNeumannSlopeL2 M n h q
          (originCube d m) omega hh)) :=
    (continuous_oneStepCellCenteredL2 (originCube d m) R).measurable.comp
      hmeasSlope
  refine ⟨uS, H, hmeasA, hmeas, ?_⟩
  intro omega Y
  have hgradQ := oneStepShellNeumann_grad_ae_eq_triadic
    M n h omega q (originCube d m) hh (uN omega) (huN omega)
  have hRQ : openCubeSet R ⊆ openCubeSet (originCube d m) :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hgradR := hgradQ.filter_mono <| MeasureTheory.ae_mono <|
    Measure.restrict_mono_set volume hRQ
  have hgradS : (uS omega).grad =ᵐ[volumeMeasureOn (openCubeSet R)]
      (oneStepTriadicNeumannSolution M n h q
        (originCube d m) omega hh).toH1Function.grad := by
    filter_upwards [hgradR] with x hx
    rw [huSgrad omega]
    exact hx
  have hbase := oneStepNeumannCellFluctuation_energy_le_poincare_quarter_ae
    M n h q omega hh hR (uS omega) (H omega) hRhalf hgradS Y
  let A : ℝ := cubeLpNorm R (2 : ENNReal)
    (cubeFluctuationVec R
      (oneStepNeumannRawCellH1 M n h omega q hh
        (uS omega) (H omega) hRhalf).toField)
  let B : ℝ := cubeScaleFactor R * ∑ k : Fin d,
    cubeLpNorm R (2 : ENNReal) (fun x ↦ euclideanNorm
      (((oneStepNeumannRawCellH1 M n h omega q hh
        (uS omega) (H omega) hRhalf).coord k).grad x))
  let C : ℝ := (d : ℝ) *
    (oneStepShellForcingCellB
        (Q := originCube d m) (R := R) M n h omega q hh +
      oneStepCellB R
        ((H omega).restrict (isOpen_openCubeSet R) hRhalf))
  let D : ℝ := oneStepCellCenteredL2 (originCube d m) R
    (oneStepNeumannSlopeL2 M n h q (originCube d m) omega hh)
  have hA0 : 0 ≤ A := cubeLpNorm_nonneg R 2 _
  have hBC : B ≤ C := by
    simpa only [B, C] using
      oneStepNeumannRawCellH1_euclideanGradientSize_le_measurable
        M n h omega q hh (uS omega) (H omega) hRhalf
  have hAD : A ≤ D := by
    have hdatum : oneStepNeumannCellFluctuationField M n h q
        (originCube d m) R omega hh =ᵐ[volumeMeasureOn (openCubeSet R)]
        cubeFluctuationVec R
          (oneStepNeumannRawCellH1 M n h omega q hh
            (uS omega) (H omega) hRhalf).toField :=
      oneStepNeumannCellFluctuationField_ae_eq_cubeFluctuationVec_rawCellH1
        M n h omega q hh (uS omega) (H omega) hR hRhalf hgradS
    have hnormDatum := cubeLpNorm_congr_ae_volumeMeasureOn R 2 hdatum
    have hfield := oneStepNeumannCellFluctuationField_eq_cubeFluctuationVec_slope
      M n h q omega hh hR
    have hbound := cubeLpNorm_cubeFluctuationVec_le_oneStepCellCenteredL2
      hR (oneStepNeumannSlopeField M n h q (originCube d m) omega hh)
        (oneStepNeumannSlopeField_memVectorL2 M n h q
          (originCube d m) omega hh)
    rw [← oneStepNeumannSlopeL2_eq_toHilbertVectorL2OfVecField
      M n h q (originCube d m) omega hh] at hbound
    dsimp only [A, D]
    calc
      cubeLpNorm R 2
          (cubeFluctuationVec R
            (oneStepNeumannRawCellH1 M n h omega q hh
              (uS omega) (H omega) hRhalf).toField) =
          cubeLpNorm R 2
            (oneStepNeumannCellFluctuationField M n h q
              (originCube d m) R omega hh) := hnormDatum.symm
      _ = cubeLpNorm R 2
          (cubeFluctuationVec R
            (oneStepNeumannSlopeField M n h q
              (originCube d m) omega hh)) := by rw [hfield]
      _ ≤ _ := hbound
  have herr : oneStepCellBesovError A B ≤ oneStepCellBesovError D C :=
    oneStepCellBesovError_mono hA0 hAD hBC
  have hfactor0 : 0 ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareLowerEllipticityFactor R
            (aCutoffEnvelopeTriadicCoeffFamily M n omega) (1 / 4 : ℝ)
              (.finite 1)) ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left herr hfactor0
  simpa only [A, B, C, D] using hbase.trans hscaled

end

end SubdiffusiveProcess.Providers.Section5
