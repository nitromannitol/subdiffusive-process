module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.ProjectedEnergyAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowBoundaryCell
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicStepRowWindowStep

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The outer-boundary version of Holder Step 6 at a finite cutoff. -/
theorem exists_boundaryHolderProjectedEnergy_cutoff (d : ℕ) [NeZero d] :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (sOrder : FractionalOrder),
        sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
      ∀ (L m n : ℕ), n + 5 ≤ m →
      ∀ (z x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
        z ∈ cube d (m : ℤ) →
        x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
        omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
        vectorNormalizedL2On
            (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
            (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
              u.grad p) ≤
          Real.sqrt ((81 : ℝ) ^ d *
            (K * harmonicPhysicalFourBudgets
              M L m n z x omega sOrder.1 u h g)) := by
  classical
  obtain ⟨Kint, hKint, hcover⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder.exists_holderProjectedEnergy_le_sqrt_max_of_boundaryCells_cut d
  obtain ⟨Cparent, hCparent, hparent⟩ :=
    Section6CutoffHarmonic.exists_boundaryStepCellParentRow d
  obtain ⟨Cb, hCb, hcell⟩ :=
    Section6CutoffHarmonic.exists_boundaryCellManuscriptRow_of_boundaryStepCellParentRow
      d hCparent hparent
  refine ⟨max Kint Cb, lt_of_lt_of_le hKint (le_max_left _ _), ?_⟩
  intro M sOrder hs L m n hnm z x omega hz hx hgood u h g hdir hg hh
  let U := truncatedCube d (m : ℤ) (n : ℤ) x
  let sigma := tailAverage M L (n + 2) omega
    (translatedCube d ((n : ℤ) + 2) z)
  let Bint := Kint *
    (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
        normalizedL2On U (fun p ↦ u.toFun p - averageOn U u.toFun) ^ 2 +
      Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
        (fractionalSeminormOn U sOrder.1 g).toReal ^ 2)
  let Bud := harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g
  have hs0 : 0 < sOrder.1 := sOrder.2.1
  have hsigma : 0 < sigma := by
    dsimp only [sigma]
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2)
      (translatePotentialSample z omega)
  have hBud0 : 0 ≤ Bud := by
    dsimp only [Bud]
    exact harmonicPhysicalFourBudgets_nonneg M L m n z x omega hs0 u h g
  have hcore :
      sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) *
          normalizedL2On U (fun p ↦ u.toFun p - averageOn U u.toFun) ^ 2 +
        Real.rpow sOrder.1 (-12 : ℝ) * sigma⁻¹ *
          Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
          (fractionalSeminormOn U sOrder.1 g).toReal ^ 2 ≤ Bud := by
    have hmean : 0 ≤ sigma * vecNormSq (averageVecOn U h.grad) :=
      mul_nonneg hsigma.le (vecNormSq_nonneg _)
    have hdatum : 0 ≤ sigma * Real.rpow sOrder.1 (-4 : ℝ) *
        Real.rpow (3 : ℝ) (2 * sOrder.1 * (n : ℝ)) *
        (fractionalSeminormOn U sOrder.1 h.grad).toReal ^ 2 :=
      mul_nonneg
        (mul_nonneg
          (mul_nonneg hsigma.le (Real.rpow_nonneg hs0.le _))
          (Real.rpow_nonneg (by norm_num) _))
        (sq_nonneg _)
    dsimp only [Bud]
    unfold harmonicPhysicalFourBudgets
    dsimp only [U, sigma]
    split_ifs <;> linarith
  have hBint : Bint ≤ max Kint Cb * Bud := by
    have hKle : Kint ≤ max Kint Cb := le_max_left _ _
    calc
      Bint ≤ Kint * Bud := by
        dsimp only [Bint]
        exact mul_le_mul_of_nonneg_left hcore hKint.le
      _ ≤ max Kint Cb * Bud :=
        mul_le_mul_of_nonneg_right hKle hBud0
  have hBboundary : Cb * Bud ≤ max Kint Cb * Bud :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hBud0
  have hraw := hcover M sOrder hs L m n hnm z x omega hz hx hgood
    u h g hdir hg
    (memCubeEuclideanFullWsp_grad_of_memFractionalOn
      (originCube d (m : ℤ)) sOrder h (by simpa [cube] using hh))
    (Cb * Bud) (fun q hq hpatch ↦ by
      simpa only [Bud] using
        hcell M sOrder hs L m n hnm z x q omega hz hx hq hpatch hgood
          u h g hdir hg hh)
  dsimp only at hraw
  refine hraw.trans (Real.sqrt_le_sqrt ?_)
  exact mul_le_mul_of_nonneg_left (max_le hBint hBboundary) (by positivity)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
