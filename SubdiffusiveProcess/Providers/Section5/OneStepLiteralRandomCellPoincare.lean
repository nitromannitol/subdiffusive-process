module

public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffP4Bounds
public import SubdiffusiveProcess.Providers.Section5.OneStepRandomCellPoincare

@[expose] public section

/-!
# Literal-cutoff forms of the random-cell Poincare estimates

`Ch03.publicCoeffField` is the pointwise elliptic representative used by the
coarse-Poincare theorem.  The variational patch for the GMC model is written
with the literal scalar cutoff.  These lemmas transport the already proved
cell estimates across the canonical a.e. equality; no new elliptic estimate
is introduced here.
-/

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.Providers.Section5

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- Primal quarter-Besov cell estimate with the energy written against the
literal GMC cutoff. -/
theorem oneStep_dirichletCell_literalCutoff_energy_le_poincare_quarter
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : Homogenization.TriadicCube d) (u : H1Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (X : OneStepDirichletCellMinimizer Q
      (Ch03.publicCoeffField Q
        (aCutoffEnvelopeTriadicCoeffFamily M L omega)) u.grad)
    (hcenter : cubeAverageVec Q u.grad = 0) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.field x)
          (matVecMul
            (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)
            (X.field x))) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          oneStepQuarterCellConst d) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareUpperEllipticityFactor Q
            (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4 : ℝ)
              (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm Q (2 : ℝ≥0∞) u.grad) (oneStepCellB Q H) := by
  have hpublic := oneStep_dirichletCell_energy_le_poincare_quarter
    Q (aCutoffEnvelopeTriadicCoeffFamily M L omega)
    (fun R ↦
      (aCutoffEnvelopeScalarTriadicCoeffData M L omega).onCube R
        |>.isSymmetric)
    u H X hcenter
  have hae : Ch03.publicCoeffField Q
      (aCutoffEnvelopeTriadicCoeffFamily M L omega) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) := by
    simpa [volumeMeasureOn, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using!
      Ch03.publicCoeffField_ae_eq_openCubeSet Q
        (aCutoffEnvelopeTriadicCoeffFamily M L omega)
  have henergy :
      volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (X.field x)
            (matVecMul
              (scalarCoeffField
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)
              (X.field x))) =
        volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (X.field x)
            (matVecMul (Ch03.publicCoeffField Q
              (aCutoffEnvelopeTriadicCoeffFamily M L omega) x) (X.field x))) := by
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  rw [henergy]
  exact hpublic

/-- Dual quarter-Besov cell estimate with the inverse energy written using
the literal scalar cutoff. -/
theorem oneStep_neumannCell_literalCutoff_energy_le_poincare_quarter
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : Homogenization.TriadicCube d) (u : H1Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (X : OneStepNeumannCellMinimizer Q
      (Ch03.publicCoeffField Q
        (aCutoffEnvelopeTriadicCoeffFamily M L omega)) u.grad)
    (hcenter : cubeAverageVec Q u.grad = 0) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.flux x)
          (matVecMul
            ((blockMatrixOfCoeff (scalarCoeffField
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)).lowerRight)
            (X.flux x))) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          oneStepQuarterCellConst d) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareLowerEllipticityFactor Q
            (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4 : ℝ)
              (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm Q (2 : ℝ≥0∞) u.grad) (oneStepCellB Q H) := by
  have hpublic := oneStep_neumannCell_energy_le_poincare_quarter
    Q (aCutoffEnvelopeTriadicCoeffFamily M L omega)
    (fun R ↦
      (aCutoffEnvelopeScalarTriadicCoeffData M L omega).onCube R
        |>.isSymmetric)
    u H X hcenter
  have hae : Ch03.publicCoeffField Q
      (aCutoffEnvelopeTriadicCoeffFamily M L omega) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) := by
    simpa [volumeMeasureOn, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using!
      Ch03.publicCoeffField_ae_eq_openCubeSet Q
        (aCutoffEnvelopeTriadicCoeffFamily M L omega)
  have henergy :
      volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (X.flux x)
            (matVecMul
              ((blockMatrixOfCoeff (scalarCoeffField
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)).lowerRight)
              (X.flux x))) =
        volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (X.potential.toH1Function.grad x) (X.flux x)) := by
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    have hdet : IsUnit
        (scalarCoeffField
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x).det :=
      isUnit_det_of_isEllipticMatrix
        (isEllipticMatrix_scalarMatrix
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x))
    have hs : symmPart
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x) =
          scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x := by
      simp only [scalarCoeffField,
        Homogenization.Book.Ch02.symmPart_scalarMatrix]
    unfold OneStepNeumannCellMinimizer.flux blockMatrixOfCoeff
    dsimp only
    rw [hx, hs,
      matVecMul_mul,
      Matrix.nonsing_inv_mul _ hdet,
      matVecMul_one]
    exact vecDot_comm _ _
  rw [henergy]
  exact hpublic

/-- Literal-cutoff transport of the solenoidal vector-`H¹` lower cell
estimate.  This is the form used by the concrete Neumann source-cell
family, whose datum is not itself a gradient. -/
theorem oneStep_neumannCell_vectorH1_literalCutoff_energy_le_poincare_quarter
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : Homogenization.TriadicCube d)
    {F : Homogenization.Vec d → Homogenization.Vec d}
    (G : CubeVectorH1Function Q)
    (X : OneStepNeumannCellMinimizer Q
      (Ch03.publicCoeffField Q
        (aCutoffEnvelopeTriadicCoeffFamily M L omega)) F)
    (hF_eq : F = cubeFluctuationVec Q G.toField) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.flux x)
          (matVecMul
            ((blockMatrixOfCoeff (scalarCoeffField
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)).lowerRight)
            (X.flux x))) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareLowerEllipticityFactor Q
            (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4 : ℝ)
              (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm Q (2 : ℝ≥0∞) F)
          (cubeScaleFactor Q * ∑ k : Fin d,
            cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x ↦ euclideanNorm ((G.coord k).grad x))) := by
  have hpublic := oneStep_neumannCell_vectorH1_energy_le_poincare_quarter
    Q (aCutoffEnvelopeTriadicCoeffFamily M L omega)
    (fun R ↦
      (aCutoffEnvelopeScalarTriadicCoeffData M L omega).onCube R
        |>.isSymmetric)
    G X hF_eq
  have hae : Ch03.publicCoeffField Q
      (aCutoffEnvelopeTriadicCoeffFamily M L omega) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) := by
    simpa [volumeMeasureOn, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using!
      Ch03.publicCoeffField_ae_eq_openCubeSet Q
        (aCutoffEnvelopeTriadicCoeffFamily M L omega)
  have henergy :
      volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (X.flux x)
            (matVecMul
              ((blockMatrixOfCoeff (scalarCoeffField
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)).lowerRight)
              (X.flux x))) =
        volumeAverage (openCubeSet Q) (fun x ↦
          vecDot (X.potential.toH1Function.grad x) (X.flux x)) := by
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    have hdet : IsUnit
        (scalarCoeffField
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x).det :=
      isUnit_det_of_isEllipticMatrix
        (isEllipticMatrix_scalarMatrix
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x))
    have hs : symmPart
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x) =
          scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x := by
      simp only [scalarCoeffField,
        Homogenization.Book.Ch02.symmPart_scalarMatrix]
    unfold OneStepNeumannCellMinimizer.flux blockMatrixOfCoeff
    dsimp only
    rw [hx, hs, matVecMul_mul, Matrix.nonsing_inv_mul _ hdet,
      matVecMul_one]
    exact vecDot_comm _ _
  rw [henergy]
  exact hpublic

/-- A.e.-representative form of the literal-cutoff solenoidal vector-`H¹`
cell estimate.  This is the form consumed by the measurable Neumann solution
operator, whose gradient agrees with the canonical solution only in `L²`. -/
theorem oneStep_neumannCell_vectorH1_literalCutoff_energy_le_poincare_quarter_ae
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : Homogenization.TriadicCube d)
    {F : Homogenization.Vec d → Homogenization.Vec d}
    (G : CubeVectorH1Function Q)
    (X : OneStepNeumannCellMinimizer Q
      (Ch03.publicCoeffField Q
        (aCutoffEnvelopeTriadicCoeffFamily M L omega)) F)
    (hF_ae : F =ᵐ[volumeMeasureOn (openCubeSet Q)]
      cubeFluctuationVec Q G.toField) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.flux x)
          (matVecMul
            ((blockMatrixOfCoeff (scalarCoeffField
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)).lowerRight)
            (X.flux x))) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareLowerEllipticityFactor Q
            (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4 : ℝ)
              (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q G.toField))
          (cubeScaleFactor Q * ∑ k : Fin d,
            cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x ↦ euclideanNorm ((G.coord k).grad x))) := by
  let Y : OneStepNeumannCellMinimizer Q
      (Ch03.publicCoeffField Q
        (aCutoffEnvelopeTriadicCoeffFamily M L omega))
      (cubeFluctuationVec Q G.toField) := X.congrDatum hF_ae
  exact oneStep_neumannCell_vectorH1_literalCutoff_energy_le_poincare_quarter
    M L omega Q G Y rfl

end

end SubdiffusiveProcess.Providers.Section5
