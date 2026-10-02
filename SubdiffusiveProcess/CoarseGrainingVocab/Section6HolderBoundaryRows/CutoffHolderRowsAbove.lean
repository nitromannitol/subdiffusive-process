import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.PackageAssembly
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwo




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Rows one, two, and three above the cutoff, at free stopping parameters. -/
theorem exists_boundaryRowsAboveCutoff_free (d : ℕ) [NeZero d]
    (hExcess : BoundaryHolderExcessDecayInput d)
    (hHarmonic : Section6ExcessDecay.HarmonicApproximationInput d) :
    ∃ C1min C2min Cmin : ℝ, 2 ≤ C1min ∧ C1min ≤ C2min ∧ 0 ≤ Cmin ∧
      ∀ C1 C2 : ℝ, C1min ≤ C1 → C2min ≤ C2 → C1 ≤ C2 →
      ∀ C : ℝ, Cmin ≤ C → ∀ step : ℕ, 21 ≤ step →
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ alpha : ℝ, alpha ∈ Set.Icc (1 / 2 : ℝ) 1 →
        Section6Stopping.holderStoppingEpsilon C2 alpha ∈
          Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
      ∀ L m : ℕ, m ≤ L → ∀ omega,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d m) u h g →
        MemHolder (cube d m) (1 / 2) g → MemHolder (cube d m) (1 / 2) h.grad →
        HolderRegularityConclusions M C L omega alpha m
          (Section6Stopping.measurableHolderStoppingScale M alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega)
          u h g := by
  classical
  have hExcess' : Section6Holder.HolderExcessDecayInput d := hExcess
  obtain ⟨C1a, C2a, Ca, hC1a, hC2a, hCa, hrow1⟩ :=
    exists_boundaryRowOneAtStepFree d hExcess'
  obtain ⟨C2b, Cb, hC2b, hCb, hrow3⟩ :=
    exists_boundaryRowThreeAtStepFree d hExcess
  obtain ⟨C1r, C2r, Cr, hC1r, _, _, hrow2⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.boundaryRowTwo d hHarmonic
  refine ⟨max C1a C1r, max (max C2a C2b) (max C2r (max C1a C1r)),
    max (max Ca Cb) Cr, hC1r.trans (le_max_right _ _),
    (le_max_right C2r (max C1a C1r)).trans (le_max_right _ _),
    le_trans hCa (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro C1 C2 hC1 hC2 hC1C2 C hC step hstep M hsmall alpha halpha heps hdelta
    L m hmL omega u h g hsol hg hh
  have hC1a' : C1a ≤ C1 := (le_max_left C1a C1r).trans hC1
  have hC1r' : C1r ≤ C1 := (le_max_right C1a C1r).trans hC1
  have hC2a' : C2a ≤ C2 :=
    ((le_max_left C2a C2b).trans (le_max_left _ _)).trans hC2
  have hC2b' : C2b ≤ C2 :=
    ((le_max_right C2a C2b).trans (le_max_left _ _)).trans hC2
  have hC2r' : C2r ≤ C2 :=
    ((le_max_left C2r (max C1a C1r)).trans (le_max_right _ _)).trans hC2
  have hC1two : (2 : ℝ) ≤ C1 := hC1r.trans hC1r'
  have hCaC : Ca ≤ C := le_trans (le_trans (le_max_left Ca Cb) (le_max_left _ _)) hC
  have hCbC : Cb ≤ C := le_trans (le_trans (le_max_right Ca Cb) (le_max_left _ _)) hC
  have hCrC : Cr ≤ C := le_trans (le_max_right _ _) hC
  obtain ⟨hlam0, hlam1, heps8⟩ :=
    holderStopping_conditions_of_coupled hC1two hC1C2 halpha
  have hrow2C :
      ∀ n : ℕ,
        (n : ℤ) ≤ (m : ℤ) -
          (Section6Stopping.measurableHolderStoppingScale M alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) →
        ∀ x ∈ cube d m,
          vectorNormalizedL2On (truncatedCube d m n x)
              (fun z ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega z) •
                u.grad z) ≤
            C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
              (vectorNormalizedL2On (cube d m)
                  (fun z ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega z) •
                    u.grad z) +
                (tailAverage M L m omega (cube d m)) ^ (-1 / 2 : ℝ) *
                  (3 : ℝ) ^ ((m : ℝ) / 2) *
                  holderSeminormOn (cube d m) (1 / 2) g +
                (if x ∈ cube d (m - 1) then 0 else
                  (tailAverage M L m omega (cube d m)) ^ (1 / 2 : ℝ) *
                    (3 : ℝ) ^ ((m : ℝ) / 2) *
                    fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                      (1 / 2) h.grad)) := by
    intro n hn x hx
    have hr := hrow2 C1 C2 hC1r' hC2r' hC1C2 step hstep M hsmall alpha
      halpha heps hdelta L m hmL omega u h g hsol hg hh n hn x hx
    refine hr.trans ?_
    have hpow : 0 ≤ (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) := by
      positivity
    have henergy : 0 ≤ vectorNormalizedL2On (cube d m)
        (fun z ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega z) •
          u.grad z) := Real.sqrt_nonneg _
    have hforce : 0 ≤ (tailAverage M L m omega (cube d m)) ^ (-1 / 2 : ℝ) *
        (3 : ℝ) ^ ((m : ℝ) / 2) * holderSeminormOn (cube d m) (1 / 2) g := by
      exact mul_nonneg
        (mul_nonneg
          (Real.rpow_nonneg (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _) _)
          (Real.rpow_nonneg (by norm_num) _))
        (Section6ExcessDecay.holderSeminormOn_nonneg hg)
    have hdatum : 0 ≤ if x ∈ cube d (m - 1) then 0 else
        (tailAverage M L m omega (cube d m)) ^ (1 / 2 : ℝ) *
          (3 : ℝ) ^ ((m : ℝ) / 2) *
          fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
            (1 / 2) h.grad := by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg
          (mul_nonneg
            (Real.rpow_nonneg (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _) _)
            (Real.rpow_nonneg (by norm_num) _))
          (Section6HolderBoundary.fractionalInfinityNormOn_cube_nonneg hh)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCrC hpow)
      (add_nonneg (add_nonneg henergy hforce) hdatum)
  refine holderRegularityConclusions_of_rows M C L omega alpha m _ u h g ?_
    hrow2C
    (hrow3 C2 hC2b' C1 (by linarith) C hCbC step M hsmall alpha halpha heps
      hdelta heps8 hlam1 L m hmL omega u h g hsol hg hh)
  intro n hn x hx ell hell y hygrid hy
  have hstop :
      (Section6Stopping.measurableHolderStoppingScale M alpha
          (Section6Stopping.holderStoppingLambda C1 alpha)
          (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
        (m : ℤ) - (n : ℤ) := by omega
  have hr := hrow1 C1 C2 hC1a' hC2a' step M hsmall alpha halpha heps hdelta
    heps8 hlam0 hlam1 L m hmL omega u h g hsol hg hh n hstop x hx ell hell y
    hygrid hy
  refine hr.trans ?_
  have hpow : 0 ≤ (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) := by positivity
  have hglobal : 0 ≤ normalizedL2On (cube d m)
      (fun z ↦ u.toFun z - averageOn (cube d m) u.toFun) :=
    Section6Iteration.normalizedL2On_nonneg _ _
  have htail : 0 < tailAverage M L m omega (cube d m) := by
    rw [← tailCoefficientCubeAverage_eq_tailAverage_cube]
    exact tailCoefficientCubeAverage_pos M L m omega
  have hforce : 0 ≤ (tailAverage M L m omega (cube d m))⁻¹ *
      (3 : ℝ) ^ (3 * (m : ℝ) / 2) * holderSeminormOn (cube d m) (1 / 2) g := by
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr htail.le) (Real.rpow_nonneg (by norm_num) _))
      (Section6ExcessDecay.holderSeminormOn_nonneg hg)
  have hdatum : 0 ≤ if x ∈ cube d (m - 1) then 0 else
      (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
        fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) h.grad := by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Section6HolderBoundary.fractionalInfinityNormOn_cube_nonneg hh)
  have hbracket : 0 ≤ normalizedL2On (cube d m)
        (fun z ↦ u.toFun z - averageOn (cube d m) u.toFun) +
      (tailAverage M L m omega (cube d m))⁻¹ *
        (3 : ℝ) ^ (3 * (m : ℝ) / 2) * holderSeminormOn (cube d m) (1 / 2) g +
      (if x ∈ cube d (m - 1) then 0 else
        (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
          fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m) (1 / 2) h.grad) := by
    linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCaC hpow) hbracket

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows
