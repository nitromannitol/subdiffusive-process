module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor.RetainedCovered
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold.ShellEnlargedOscillatory
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepShellForcingCellBudget

@[expose] public section




open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure
open SubdiffusiveProcess.CoarseGrainingVocab.Section5FiniteFold
open SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

variable {d : ℕ}

/-- The shell half of the `delta ^ 68` budget is discharged. -/
theorem shellForcingCellBFourthBudget_holds (d : ℕ) [NeZero d] :
    ShellForcingCellBFourthBudget d :=
  exists_oneStepShellForcingCellB_source_fourth_budget d

/-- **Conjunct 4, unconditional, with the shell-enlarged cell size.** -/
theorem exists_oneStepDualOscillatory_shellEnlarged_sourceCells_budget
    (d : ℕ) [NeZero d] (hd : 3 ≤ d) (D : ℝ) (hD0 : 0 ≤ D) :
    ∃ delta0 O : ℝ, 0 < delta0 ∧ 0 < O ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
        ∀ (n h K : ℕ) (p : Vec d), vecNormSq p = 1 → ∀ hh : 0 < h,
          (h : ℝ) ≤ M.delta⁻¹ →
          16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n →
          oneStepLocalizationScale n M.delta ≤ K →
          ∃ oscillatory : TriadicCube d → Sample d → ℝ,
            (∀ R ∈ oneStepSourceCells d K n M.delta,
              Integrable (oscillatory R) M.P.toMeasure) ∧
            (∀ R ∈ oneStepSourceCells d K n M.delta,
              ∀ omega, 0 ≤ oscillatory R omega) ∧
            ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
                ∑ R ∈ oneStepSourceCells d K n M.delta,
                  ∫ omega, oscillatory R omega ∂M.P.toMeasure ≤
              O * M.delta ^ (30 : ℕ) * (ahom M n)⁻¹) ∧
            (oneStepLocalizationScale n M.delta +
                (nfFoldRadius (nfAxisHarmonicDepth d hd) M.delta + 1) ≤ K →
              ∃ (j N : ℕ) (F : OneStepTwoRadiusNeumannHessianFamily d
                    (NFInnerHalfIndex d (K : ℤ) j N) (NFSample d)
                    Finset.univ (nfNestedCell N)),
                N = nfFoldRadius (nfAxisHarmonicDepth d hd) M.delta + 1 ∧
                j + N = K - oneStepLocalizationScale n M.delta ∧
                (∀ q omega, (F.neumann q omega).grad =
                  (oneStepOriginNeumannSolution M n h p (K : ℤ) omega
                    hh).toH1Function.grad) ∧
                (∀ q : NFInnerHalfIndex d (K : ℤ) j N,
                  nfNestedCell N q ∈ oneStepSourceCells d K n M.delta) ∧
                (∀ S ∈ overlapCentersAtDepth (originCube d (K : ℤ)) j,
                  ∀ R ∈ descendantsAtDepth S (N - 1),
                    ∃ q : NFInnerHalfIndex d (K : ℤ) j N,
                      nfNestedCell N q = R) ∧
                oscillatory = oneStepDualOscillatoryMajorant M n h D
                  (nfShellEnlargedCellB M n h K p hh
                    (nfExtendByZero (nfNestedCell N)
                      F.toCellFamily.neumann))) :=
  exists_oneStepDualOscillatory_innerHalf_sourceCells_budget_shellEnlarged
    d hd D hD0 (shellForcingCellBFourthBudget_holds d)

/-! ## The cellwise domination -/

/-- **The oscillatory cell energy is dominated by the shared envelope.**
Both `oneStepCellBesovError` slots are closed: the first by the vector
mean-zero cell Poincaré, the second by the derivative-size bound. -/
theorem dualPaperRawOscillatory_le_dualOscillatoryMajorant_onCell
    {K : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (q : Homogenization.Vec d) (omega : Sample d) (hh : 0 < h)
    (R : Homogenization.TriadicCube d)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (uR : H1Function (openCubeSet R))
    (HR : HasWeakHessianOn (openCubeSet R) uR)
    (hgradEq : uR.grad =
      (oneStepTriadicNeumannSolution M n h q
        (originCube d (K : ℤ)) omega hh).toH1Function.grad)
    (B : TriadicCube d → Sample d → ℝ)
    (hB : oneStepCellB R HR ≤ B R omega)
    (hfactor :
      (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
        Ch03.poincareLowerEllipticityFactor R
          (aCutoffEnvelopeTriadicCoeffFamily M (n + h) omega) (1 / 4 : ℝ)
            (.finite 1)) ^ 2 =
        oneStepLowerPoincareEnergyFactorMeasurable M (n + h)
          (oneStepLocalizationScale n M.delta)
          (translatePotentialSequence (triadicCubeShift R) omega)) :
    dualPaperRawOscillatory (K := K) M n h q R omega hh ≤
      oneStepDualOscillatoryMajorant M n h
        ((originCubeMeanZeroH1CoerciveEstimate d 0).constant)
        (nfShellEnlargedCellB M n h K q hh B) R omega := by
  classical
  set Q : TriadicCube d := originCube d (K : ℤ) with hQ
  have hRQ : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth (mem_oneStepSourceCells hR)
  set G := oneStepPaperNeumannRawCellH1OnCell M n h omega q hh uR HR hRQ
    with hG
  set S : ℝ := cubeScaleFactor R * ∑ k : Fin d,
    cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ euclideanNorm ((G.coord k).grad x))
    with hSdef
  set A : ℝ := cubeLpNorm R (2 : ℝ≥0∞)
    (oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh) with hAdef
  -- the derivative-size bound closes the second slot
  have hSle : S ≤ nfShellEnlargedCellB M n h K q hh B R omega := by
    have hbase := oneStepPaperNeumannRawCellH1OnCell_euclideanGradientSize_le_cellB
      (Q := Q) (R := R) M n h omega q hh uR HR hRQ
    refine hbase.trans ?_
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    unfold nfShellEnlargedCellB
    exact mul_le_mul_of_nonneg_left (by linarith) hd0
  -- the vector Poincaré closes the first slot
  have hAle : A ≤ (originCubeMeanZeroH1CoerciveEstimate d 0).constant * S := by
    have hfluct :=
      oneStepPaperNeumannCellFluctuationField_eq_cubeFluctuationVec_rawCellH1OnCell
        (j := K - oneStepLocalizationScale n M.delta) M n h omega q hh uR HR
        (mem_oneStepSourceCells hR) hRQ hgradEq
    rw [hAdef, hfluct]
    simpa only [hG, hSdef] using
      cubeLpNorm_two_cubeFluctuationVec_toField_le_gradientSize R G
  have hAD : A ≤ (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
      nfShellEnlargedCellB M n h K q hh B R omega := by
    refine hAle.trans ?_
    exact mul_le_mul_of_nonneg_left hSle
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  have hA0 : (0 : ℝ) ≤ A := cubeLpNorm_nonneg R 2 _
  -- assemble
  have hcarrier := dualPaperRawOscillatory_le_quarterBesov_onCell
    M n h q omega hh R hR uR HR hgradEq
  refine hcarrier.trans ?_
  simpa only [hAdef, hSdef, hG, hQ] using
    quarterBesovEnvelope_le_oneStepDualOscillatoryMajorant M n h R omega
      ((originCubeMeanZeroH1CoerciveEstimate d 0).constant)
      (nfShellEnlargedCellB M n h K q hh B) hA0 hAD hSle hfactor

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualCompetitor
