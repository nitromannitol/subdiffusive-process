import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.SharedEnvelope




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

/-- The centred cube of scale `m` is a child of the centred cube of scale
`m + 1`. -/
theorem originCube_mem_childCubes_succ (d : ℕ) (m : ℤ) :
    originCube d m ∈ childCubes (originCube d (m + 1)) := by
  rw [mem_childCubes_iff]
  refine ⟨fun _ ↦ (1 : Fin 3), ?_⟩
  apply congrArg₂ TriadicCube.mk
  · simp only [originCube]
    ring
  · funext i
    simp only [originCube]
    norm_num

/-- The centred cube of scale `K` is a depth-one descendant of the centred cube
of scale `K + 1`. -/
theorem originCube_mem_descendantsAtDepth_succ_one (d : ℕ) (m : ℤ) :
    originCube d m ∈ descendantsAtDepth (originCube d (m + 1)) 1 := by
  rw [descendantsAtDepth_one]
  exact originCube_mem_childCubes_succ d m



theorem oneStepSourceCells_mem_descendantsAtDepth_succ
    {K n : ℕ} {delta : ℝ} {R : TriadicCube d}
    (hK : oneStepLocalizationScale n delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n delta) :
    R ∈ descendantsAtDepth (originCube d ((K : ℤ) + 1))
      (K + 1 - oneStepLocalizationScale n delta) := by
  have hchild := originCube_mem_descendantsAtDepth_succ_one d (K : ℤ)
  have htrans := mem_descendantsAtDepth_add hchild (mem_oneStepSourceCells hR)
  have hdepth : 1 + (K - oneStepLocalizationScale n delta) =
      K + 1 - oneStepLocalizationScale n delta := by omega
  rwa [hdepth] at htrans

/-- **The shared-parent quarter-Besov cell bound.**  For the Neumann corrector
run on `originCube d (K + 1)`, the inverse-star cell energy of the manuscript
flux's cell fluctuation is controlled on **every** source cell of
`originCube d K` — the `hRhalf` hypothesis is discharged for free, so no cell
and no volume is discarded. -/
theorem oneStepPaperNeumannSuccParentCellFluctuation_inverseStar_energy_le
    {K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n h : ℕ)
    (omega : Sample d) (q : Vec d) (hh : 0 < h)
    (R : TriadicCube d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (uS : H1Function
      (scaledOpenCubeSet (originCube d ((K : ℤ) + 1)) (1 / 2 : ℝ)))
    (H : HasWeakHessianOn
      (scaledOpenCubeSet (originCube d ((K : ℤ) + 1)) (1 / 2 : ℝ)) uS)
    (hgradEq : uS.grad =
      (oneStepTriadicNeumannSolution M n h q
        (originCube d ((K : ℤ) + 1)) omega hh).toH1Function.grad)
    (X : OneStepNeumannCellMinimizer R
      (Ch03.publicCoeffField R
        (aCutoffEnvelopeTriadicCoeffFamily M L omega))
      (oneStepPaperNeumannCellFluctuationField M n h q
        (originCube d ((K : ℤ) + 1)) R omega hh)) :
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.flux x)
          (matVecMul
            ((blockMatrixOfCoeff (scalarCoeffField
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x)).lowerRight)
            (X.flux x))) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareLowerEllipticityFactor R
            (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4 : ℝ)
              (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm R (2 : ℝ≥0∞)
            (oneStepPaperNeumannCellFluctuationField M n h q
              (originCube d ((K : ℤ) + 1)) R omega hh))
          (cubeScaleFactor R * ∑ k : Fin d,
            cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ euclideanNorm
              (((oneStepPaperNeumannRawCellH1 M n h omega q hh uS H
                (openCubeSet_sourceCell_subset_scaledOpenCubeSet_succ_half hR)
                ).coord k).grad x))) :=
  oneStepPaperNeumannCellFluctuation_inverseStar_energy_le_poincare_quarter
    (j := K + 1 - oneStepLocalizationScale n M.delta)
    M L n h omega q hh uS H
    (oneStepSourceCells_mem_descendantsAtDepth_succ hK hR)
    (openCubeSet_sourceCell_subset_scaledOpenCubeSet_succ_half hR) hgradEq X

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
