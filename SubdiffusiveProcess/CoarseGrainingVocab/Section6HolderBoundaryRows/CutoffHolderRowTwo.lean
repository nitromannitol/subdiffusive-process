import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.BoundaryRowTwoCutoffConditional
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.RowTwoAtStepFree
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffComparisonCollapse
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffExcessDecay




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.CutoffHolderBelow

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The interior cutoff excess-decay input is a theorem. -/
theorem interiorHolderExcessDecayInput_cut_holds (d : ℕ) :
    Section6HolderBelowCutoff.Rows.InteriorHolderExcessDecayInput_cut d :=
  Section6HolderBelowCutoff.interiorCutoffHolderExcessDecayInput_of_interiorCutoffHarmonic
    d (-2 : ℝ) (-8 : ℝ) (fun [NeZero d] =>
      Section6HolderBelowCutoff.interiorCutoffHarmonicApproximationInput_holds d)

/-- **Row two below the cutoff.**  The frozen weighted-gradient row, with its
boundary datum switched on exactly off the inner cube, at the cutoff stopping
carrier. -/
theorem exists_boundaryRowTwoAtStepFree_cut (d : ℕ) [NeZero d]
    (hharm : Section6ExcessDecay.BoundaryCutoffHarmonicApproximationInputV6 d) :
    ∃ (C1min C2min Crow : ℝ), 2 ≤ C1min ∧ C1min ≤ C2min ∧ 0 ≤ Crow ∧
      ∀ C1 C2 : ℝ, C1min ≤ C1 → C2min ≤ C2 → C1 ≤ C2 →
      ∀ step : ℕ, 21 ≤ step →
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ alpha : ℝ, alpha ∈ Set.Icc (1 / 2 : ℝ) 1 →
        Section6Stopping.holderStoppingEpsilon C2 alpha ∈
          Set.Icc (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1 →
        M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha →
      ∀ L m : ℕ, L < m →
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (originCube d (m : ℤ)) u h g →
        MemHolder (cube d (m : ℤ)) (1 / 2) g →
        MemHolder (cube d (m : ℤ)) (1 / 2) h.grad →
      ∀ n : ℕ,
        (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
      ∀ x : Vec d, x ∈ cube d (m : ℤ) →
        vectorNormalizedL2On (truncatedCube d (m : ℤ) (n : ℤ) x)
            (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
              u.grad p) ≤
          Crow * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
            (vectorNormalizedL2On (cube d (m : ℤ))
                (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
                  u.grad p) +
              (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
                (3 : ℝ) ^ ((m : ℝ) / 2) *
                holderSeminormOn (cube d (m : ℤ)) (1 / 2) g +
              (if x ∈ cube d ((m : ℤ) - 1) then 0 else
                (tailAverage M L m omega (cube d (m : ℤ))) ^ (1 / 2 : ℝ) *
                  (3 : ℝ) ^ ((m : ℝ) / 2) *
                  fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
                    (1 / 2) h.grad)) := by
  classical
  obtain ⟨C1i, C2i, Ci, hC1i, hC12i, hCi, hinterior⟩ :=
    Section6HolderBelowCutoff.Rows.exists_interiorRowTwoAtStepFree_cut d
      (interiorHolderExcessDecayInput_cut_holds d)
  obtain ⟨C1o, C2o, Co, hC1o, hC12o, hCo, houter⟩ :=
    Section6HolderLift.exists_boundaryRowTwoCutoffOuterAtStepFree_of_harmonic d hharm
  refine ⟨max C1i C1o, max (max C2i C2o) (max C1i C1o), max Ci Co,
    hC1i.trans (le_max_left _ _), le_max_right _ _, hCi.trans (le_max_left _ _), ?_⟩
  intro C1 C2 hC1 hC2 hC12 step hstep M hsmall alpha halpha heps hdelta
    L m hLm omega u h g hsol hg hh n hstop x hx
  have hC1i' : C1i ≤ C1 := (le_max_left C1i C1o).trans hC1
  have hC1o' : C1o ≤ C1 := (le_max_right C1i C1o).trans hC1
  have hC2i' : C2i ≤ C2 :=
    ((le_max_left C2i C2o).trans (le_max_left (max C2i C2o) (max C1i C1o))).trans hC2
  have hC2o' : C2o ≤ C2 :=
    ((le_max_right C2i C2o).trans (le_max_left (max C2i C2o) (max C1i C1o))).trans hC2
  have hCiCrow : Ci ≤ max Ci Co := le_max_left _ _
  have hCoCrow : Co ≤ max Ci Co := le_max_right _ _
  have hpow0 : 0 ≤ (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) := by positivity
  have hEg0 : 0 ≤ vectorNormalizedL2On (cube d (m : ℤ))
      (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) • u.grad p) :=
    Real.sqrt_nonneg _
  have hG0 : 0 ≤ (tailAverage M L m omega (cube d (m : ℤ))) ^ (-1 / 2 : ℝ) *
      (3 : ℝ) ^ ((m : ℝ) / 2) *
      holderSeminormOn (cube d (m : ℤ)) (1 / 2) g :=
    mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _) _)
        (Real.rpow_nonneg (by norm_num) _))
      (Section6ExcessDecay.holderSeminormOn_nonneg hg)
  by_cases hxinner : x ∈ cube d ((m : ℤ) - 1)
  · have hr := hinterior C1 C2 hC1i' hC2i' hC12 step hstep M hsmall alpha
      halpha heps hdelta L m omega u g hsol.2 hg n hstop x hxinner
    simp only [if_pos hxinner, add_zero]
    exact hr.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCiCrow hpow0) (add_nonneg hEg0 hG0))
  · have hr := houter C1 C2 hC1o' hC2o' hC12 step hstep M hsmall alpha
      halpha heps hdelta L m hLm omega u h g hsol hg hh n hstop x hx
    simp only [if_neg hxinner]
    have hH0 : 0 ≤ (tailAverage M L m omega (cube d (m : ℤ))) ^ (1 / 2 : ℝ) *
        (3 : ℝ) ^ ((m : ℝ) / 2) *
        fractionalInfinityNormOnReal (cube d (m : ℤ)) ((3 : ℝ) ^ (m : ℤ))
          (1 / 2) h.grad :=
      mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (Section6ExcessDecay.tailAverage_nonneg _ _ _ _ _) _)
          (Real.rpow_nonneg (by norm_num) _))
        (Section6HolderBoundary.fractionalInfinityNormOn_cube_nonneg hh)
    exact hr.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCoCrow hpow0)
      (add_nonneg (add_nonneg hEg0 hG0) hH0))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.CutoffHolderBelow
