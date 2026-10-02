import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.Competitor
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepPaperNeumannInverseStarBesov




open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

variable {d : ℕ}

/-- **Coefficient transport for dual cell minimizers.**  Only the left-hand
side of the weak Neumann identity sees the coefficient, so an almost-everywhere
equality of coefficient fields transports the minimizer while keeping its
potential.  Dual counterpart of `oneStepDirichletCellMinimizer_congrCoeff`. -/
def oneStepNeumannCellMinimizer_congrCoeff
    {R : TriadicCube d} {a b : CoeffField d} {G : Vec d → Vec d}
    (X : OneStepNeumannCellMinimizer R a G)
    (hab : a =ᵐ[volumeMeasureOn (openCubeSet R)] b) :
    OneStepNeumannCellMinimizer R b G where
  potential := X.potential
  weakSolution := by
    intro phi
    have hcong : ∫ x in openCubeSet R,
          vecDot (matVecMul (b x) (X.potential.toH1Function.grad x))
            (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet R,
          vecDot (matVecMul (a x) (X.potential.toH1Function.grad x))
            (phi.toH1Function.grad x) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards [hab] with x hx
      rw [hx]
    rw [hcong]
    exact X.weakSolution phi

@[simp] theorem oneStepNeumannCellMinimizer_congrCoeff_potential
    {R : TriadicCube d} {a b : CoeffField d} {G : Vec d → Vec d}
    (X : OneStepNeumannCellMinimizer R a G)
    (hab : a =ᵐ[volumeMeasureOn (openCubeSet R)] b) :
    (oneStepNeumannCellMinimizer_congrCoeff X hab).potential = X.potential :=
  rfl

/-- Transporting the coefficient does not change the cell's inverse-star
energy, measured against a fixed metric. -/
theorem volumeAverage_congrCoeff_flux_energy_eq
    {R : TriadicCube d} {a b : CoeffField d} {G : Vec d → Vec d}
    (X : OneStepNeumannCellMinimizer R a G)
    (hab : a =ᵐ[volumeMeasureOn (openCubeSet R)] b)
    (A : Vec d → Mat d) :
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot ((oneStepNeumannCellMinimizer_congrCoeff X hab).flux x)
          (matVecMul (A x)
            ((oneStepNeumannCellMinimizer_congrCoeff X hab).flux x))) =
      volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.flux x) (matVecMul (A x) (X.flux x))) := by
  unfold volumeAverage
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hab] with x hx
  simp only [OneStepNeumannCellMinimizer.flux,
    oneStepNeumannCellMinimizer_congrCoeff, hx]

/-- The `aCutoff` envelope's public coefficient field agrees almost everywhere
on a cell with the literal scalar cutoff coefficient. -/
theorem publicCoeffField_ae_eq_scalarCoeffField
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : Sample d)
    (R : TriadicCube d) :
    Ch03.publicCoeffField R (aCutoffEnvelopeTriadicCoeffFamily M L omega)
        =ᵐ[volumeMeasureOn (openCubeSet R)]
      scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) := by
  simpa only [aCutoffEnvelopeTriadicCoeffFamily,
    aCutoffEnvelopeScalarTriadicCoeffData,
    ScalarTriadicCoeffData.toTriadicCoeffFamily,
    aCutoffEnvelopeCoeffOnData, ScalarCoeffOnData.toCoeffOn] using
    Ch03.publicCoeffField_ae_eq_openCubeSet R
      (aCutoffEnvelopeTriadicCoeffFamily M L omega)

/-- **The oscillatory cell bound.**  The literal oscillatory cell energy of the
dual competitor is dominated by the manuscript's quarter-Besov envelope, for
every source cell contained in the inner half of the parent cube. -/
theorem dualPaperRawOscillatory_le_quarterBesov
    {K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (omega : Sample d) (hh : 0 < h)
    (R : Homogenization.TriadicCube d)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (uS : H1Function
      (scaledOpenCubeSet (originCube d (K : ℤ)) (1 / 2 : ℝ)))
    (H : HasWeakHessianOn
      (scaledOpenCubeSet (originCube d (K : ℤ)) (1 / 2 : ℝ)) uS)
    (hRhalf : openCubeSet R ⊆
      scaledOpenCubeSet (originCube d (K : ℤ)) (1 / 2 : ℝ))
    (hgradEq : uS.grad =
      (oneStepTriadicNeumannSolution M n h q
        (originCube d (K : ℤ)) omega hh).toH1Function.grad) :
    dualPaperRawOscillatory (K := K) M n h q R omega hh ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareLowerEllipticityFactor R
            (aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega) (1 / 4 : ℝ)
              (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm R (2 : ℝ≥0∞)
            (oneStepPaperNeumannCellFluctuationField M n h q
              (originCube d (K : ℤ)) R omega hh))
          (cubeScaleFactor R * ∑ k : Fin d,
            cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ euclideanNorm
              (((oneStepPaperNeumannRawCellH1 M n h omega q hh uS H hRhalf
                ).coord k).grad x))) := by
  classical
  have hcoeff := publicCoeffField_ae_eq_scalarCoeffField M (n + h) omega R
  set Y : OneStepNeumannCellMinimizer R
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega))
      (oneStepPaperNeumannCellFluctuationField M n h q
        (originCube d (K : ℤ)) R omega hh) :=
    oneStepSelectedNeumannCell
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega))
      (fun S ↦ oneStepPaperNeumannCellFluctuationField M n h q
        (originCube d (K : ℤ)) S omega hh)
      (dualParentEllipticityData_descendants M (n + h) omega
        (originCube d (K : ℤ)) (K - oneStepLocalizationScale n M.delta))
      (oneStepPaperNeumannCellFluctuationField_memVectorL2_of_descendant
        M n h q (originCube d (K : ℤ)) omega hh) R
      (mem_oneStepSourceCells hR) with hY
  have hraw : dualPaperRawOscillatory (K := K) M n h q R omega hh =
      volumeAverage (openCubeSet R) (fun x ↦
        vecDot (Y.flux x)
          (matVecMul ((blockMatrixOfCoeff
            (scalarCoeffField
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega) x)).lowerRight)
            (Y.flux x))) := by
    unfold dualPaperRawOscillatory
    rw [dif_pos hR, hY]
  have htransport := volumeAverage_congrCoeff_flux_energy_eq Y hcoeff.symm
    (fun x ↦ (blockMatrixOfCoeff
      (scalarCoeffField
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega) x)).lowerRight)
  have hcarrier :=
    oneStepPaperNeumannCellFluctuation_inverseStar_energy_le_poincare_quarter
      (j := K - oneStepLocalizationScale n M.delta)
      M (n + h) n h omega q hh uS H (mem_oneStepSourceCells hR) hRhalf hgradEq
      (oneStepNeumannCellMinimizer_congrCoeff Y hcoeff.symm)
  rw [hraw, ← htransport]
  exact hcarrier

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
