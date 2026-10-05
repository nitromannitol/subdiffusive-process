module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.CutoffHolderRowOneFinalStepFree
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.CutoffHolderRowThreeFree
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.CutoffHolderRowTwo
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ConclusionAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.SharedStoppingParameters
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.BelowCutoff.Carrier

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.CutoffHolderBelow

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.BelowCutoff

noncomputable section
attribute [local instance] Classical.propDecidable

/-- **The three frozen boundary rows below the cutoff, at the cutoff stopping
carrier.** -/
theorem exists_boundaryRowsBelowCutoff_thresholded (d : ℕ) [NeZero d]
    (hharm : Section6ExcessDecay.BoundaryCutoffHarmonicApproximationInputV6 d)
    (hExcess : Section6ExcessDecay.BoundaryCutoffHolderExcessDecayInputV4 d) :
    ∃ C1min C2min Cmin : ℝ, 2 ≤ C1min ∧ C1min ≤ C2min ∧ 0 ≤ Cmin ∧
      ∀ C1 C2 : ℝ, C1min ≤ C1 → C2min ≤ C2 → C1 ≤ C2 →
      ∀ C : ℝ, Cmin ≤ C → ∀ step : ℕ, 21 ≤ step →
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ alpha : ℝ, alpha ∈ Set.Icc (1 / 2 : ℝ) 1 →
        Section6Stopping.holderStoppingEpsilon C2 alpha ∈
          Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
      ∀ L m : ℕ, L < m → ∀ omega,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (originCube d m) u h g →
        MemHolder (cube d m) (1 / 2) g → MemHolder (cube d m) (1 / 2) h.grad →
        HolderRegularityConclusions M C L omega alpha m
          (boundaryCutoffStoppingScale M L alpha C1 C2 step m omega) u h g := by
  classical
  obtain ⟨C1a, C2a, Ca, hC1a, hC2a, hCa, hrow1⟩ :=
    exists_boundaryRowOneAtStepFree_cut d hExcess
  obtain ⟨C1r, C2r, Cr, hC1r, hC12r, hCr, hrow2⟩ :=
    exists_boundaryRowTwoAtStepFree_cut d hharm
  obtain ⟨C2b, Cb, hC2b, hCb, hrow3⟩ :=
    exists_boundaryRowThreeAtStepFree_cut d hExcess
  refine ⟨max C1a C1r, max (max C2a C2b) (max C2r (max C1a C1r)),
    max (max Ca Cb) Cr, hC1r.trans (le_max_right _ _),
    (le_max_right C2r (max C1a C1r)).trans (le_max_right _ _),
    le_trans hCa (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro C1 C2 hC1 hC2 hC1C2 C hC step hstep M hsmall alpha halpha heps hdelta
    L m hLm omega u h g hsol hg hh
  have hC1a' : C1a ≤ C1 := (le_max_left C1a C1r).trans hC1
  have hC1r' : C1r ≤ C1 := (le_max_right C1a C1r).trans hC1
  have hC2a' : C2a ≤ C2 :=
    ((le_max_left C2a C2b).trans (le_max_left _ _)).trans hC2
  have hC2b' : C2b ≤ C2 :=
    ((le_max_right C2a C2b).trans (le_max_left _ _)).trans hC2
  have hC2r' : C2r ≤ C2 :=
    ((le_max_left C2r (max C1a C1r)).trans (le_max_right _ _)).trans hC2
  have hCaC : Ca ≤ C := le_trans (le_trans (le_max_left Ca Cb) (le_max_left _ _)) hC
  have hCbC : Cb ≤ C := le_trans (le_trans (le_max_right Ca Cb) (le_max_left _ _)) hC
  have hCrC : Cr ≤ C := le_trans (le_max_right _ _) hC
  have hC1two : (2 : ℝ) ≤ C1 := hC1r.trans hC1r'
  have hC1one : (1 : ℝ) ≤ C1 := by linarith
  obtain ⟨hlam0, hlam1, heps8⟩ :=
    holderStopping_conditions_of_coupled hC1two hC1C2 halpha
  have htailPos : 0 < tailAverage M L m omega (cube d (m : ℤ)) := by
    rw [← tailCoefficientCubeAverage_eq_tailAverage_cube]
    exact tailCoefficientCubeAverage_pos M L m omega
  refine holderRegularityConclusions_of_rows M C L omega alpha m _ u h g ?_ ?_ ?_
  · -- row one
    intro n hn x hx ell hell y hygrid hy
    have hstop :
        (boundaryCutoffStoppingScale M L alpha C1 C2 step m omega : ℤ) ≤
          (m : ℤ) - (n : ℤ) := by omega
    have hr := hrow1 C1 C2 hC1a' hC2a' step M hsmall alpha halpha heps hdelta
      heps8 hlam0 hlam1 L m hLm omega u h g hsol hg hh n hstop x hx ell hell y
      hygrid hy
    refine hr.trans ?_
    have hpow : 0 ≤ (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) := by positivity
    have hglobal : 0 ≤ normalizedL2On (cube d m)
        (fun z ↦ u.toFun z - averageOn (cube d m) u.toFun) :=
      Section6Iteration.normalizedL2On_nonneg _ _
    have hforce : 0 ≤ (tailAverage M L m omega (cube d m))⁻¹ *
        (3 : ℝ) ^ (3 * (m : ℝ) / 2) * holderSeminormOn (cube d m) (1 / 2) g :=
      mul_nonneg
        (mul_nonneg (inv_nonneg.mpr htailPos.le) (Real.rpow_nonneg (by norm_num) _))
        (Section6ExcessDecay.holderSeminormOn_nonneg hg)
    have hdatum : 0 ≤ if x ∈ cube d ((m : ℤ) - 1) then 0 else
        (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
          fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ (m : ℤ)) (1 / 2) h.grad := by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Section6HolderBoundary.fractionalInfinityNormOn_cube_nonneg hh)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCaC hpow) (by linarith)
  · -- row two
    intro n hn x hx
    have hstop :
        (boundaryCutoffStoppingScale M L alpha C1 C2 step m omega : ℤ) ≤
          (m : ℤ) - (n : ℤ) := by omega
    have hr := hrow2 C1 C2 hC1r' hC2r' hC1C2 step hstep M hsmall alpha halpha
      heps hdelta L m hLm omega u h g hsol hg hh n hstop x hx
    refine hr.trans ?_
    have hpow : 0 ≤ (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) := by positivity
    have henergy : 0 ≤ vectorNormalizedL2On (cube d m)
        (fun z ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega z) • u.grad z) :=
      Real.sqrt_nonneg _
    have hforce : 0 ≤ (tailAverage M L m omega (cube d m)) ^ (-1 / 2 : ℝ) *
        (3 : ℝ) ^ ((m : ℝ) / 2) * holderSeminormOn (cube d m) (1 / 2) g :=
      mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _) _)
          (Real.rpow_nonneg (by norm_num) _))
        (Section6ExcessDecay.holderSeminormOn_nonneg hg)
    have hdatum : 0 ≤ if x ∈ cube d ((m : ℤ) - 1) then 0 else
        (tailAverage M L m omega (cube d m)) ^ (1 / 2 : ℝ) *
          (3 : ℝ) ^ ((m : ℝ) / 2) *
          fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ (m : ℤ)) (1 / 2) h.grad := by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg
          (mul_nonneg (Real.rpow_nonneg (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _) _)
            (Real.rpow_nonneg (by norm_num) _))
          (Section6HolderBoundary.fractionalInfinityNormOn_cube_nonneg hh)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCrC hpow) (by linarith)
  · -- row three
    exact hrow3 C2 hC2b' C1 hC1one C hCbC step M hsmall alpha halpha heps
      hdelta heps8 hlam1 L m hLm omega u h g hsol hg hh

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.CutoffHolderBelow
