module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.BoundaryLayer

@[expose] public section




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

/-- **The oscillatory cell bound, inner-half-free.**  The literal oscillatory
cell energy of the dual competitor is dominated by the manuscript's
quarter-Besov envelope on **every** source cell, given only the cell's own
weak Hessian for the cube-`K` Neumann corrector. -/
theorem dualPaperRawOscillatory_le_quarterBesov_onCell
    {K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (omega : Sample d) (hh : 0 < h)
    (R : Homogenization.TriadicCube d)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (uR : H1Function (openCubeSet R))
    (HR : HasWeakHessianOn (openCubeSet R) uR)
    (hgradEq : uR.grad =
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
              (((oneStepPaperNeumannRawCellH1OnCell M n h omega q hh uR HR
                (openCubeSet_subset_of_mem_descendantsAtDepth
                  (mem_oneStepSourceCells hR))).coord k).grad x))) := by
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
    oneStepPaperNeumannCellFluctuation_inverseStar_energy_le_poincare_quarter_onCell
      (j := K - oneStepLocalizationScale n M.delta)
      M (n + h) n h omega q hh uR HR (mem_oneStepSourceCells hR)
      (openCubeSet_subset_of_mem_descendantsAtDepth
        (mem_oneStepSourceCells hR))
      hgradEq (oneStepNeumannCellMinimizer_congrCoeff Y hcoeff.symm)
  rw [hraw, ← htransport]
  exact hcarrier

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
