module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.CompactSupportLocalLimit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.MassiveWeakSolutionAlgebra

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped CompactlySupported ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-- Every compactly supported continuous forcing has a pointwise whole-space
candidate with a compatible massive weak solution on every centered cube. -/
theorem exists_localMassiveWeakSolution_of_compactSupport [NeZero d]
    {c rho : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : Vec d → ℝ,
      (∀ x, |u x| ≤
        ‖compactSupportToC0 f.nnrealPart.toReal‖ / mu +
          ‖compactSupportToC0 (-f).nnrealPart.toReal‖ / mu) ∧
        ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
          uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
            IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) uLocal f := by
  let fPlus : C_c(Vec d, ℝ) := f.nnrealPart.toReal
  let fMinus : C_c(Vec d, ℝ) := (-f).nnrealPart.toReal
  have hfPlus : ∀ x, 0 ≤ fPlus x := by
    intro x
    exact CompactlySupportedContinuousMap.toReal_nonneg x
  have hfMinus : ∀ x, 0 ≤ fMinus x := by
    intro x
    exact CompactlySupportedContinuousMap.toReal_nonneg x
  obtain ⟨uPlus, _huPlusBound, huPlus⟩ :=
    exists_bounded_localMassiveWeakSolution_of_compactSupport
      B hmu fPlus hfPlus
  obtain ⟨uMinus, _huMinusBound, huMinus⟩ :=
    exists_bounded_localMassiveWeakSolution_of_compactSupport
      B hmu fMinus hfMinus
  refine ⟨uPlus - uMinus, ?_, fun k ↦ ?_⟩
  · intro x
    calc
      |uPlus x - uMinus x| ≤ |uPlus x| + |uMinus x| := abs_sub _ _
      _ = uPlus x + uMinus x := by
        rw [abs_of_nonneg (_huPlusBound x).1,
          abs_of_nonneg (_huMinusBound x).1]
      _ ≤ ‖compactSupportToC0 f.nnrealPart.toReal‖ / mu +
          ‖compactSupportToC0 (-f).nnrealPart.toReal‖ / mu := by
        simpa only [fPlus, fMinus] using
          add_le_add (_huPlusBound x).2 (_huMinusBound x).2
  obtain ⟨uPlusLocal, huPlusAE, huPlusSolution⟩ := huPlus k
  obtain ⟨uMinusLocal, huMinusAE, huMinusSolution⟩ := huMinus k
  refine ⟨uPlusLocal - uMinusLocal, ?_, ?_⟩
  · filter_upwards [huPlusAE, huMinusAE] with x hxPlus hxMinus
    simp only [H1Function.sub_toFun, Pi.sub_apply, hxPlus, hxMinus]
  · have hfPlusL2 : MemL2On (cube d (k : ℤ)) fPlus :=
      (fPlus.continuous.memLp_of_hasCompactSupport fPlus.hasCompactSupport).restrict _
    have hfMinusL2 : MemL2On (cube d (k : ℤ)) fMinus :=
      (fMinus.continuous.memLp_of_hasCompactSupport fMinus.hasCompactSupport).restrict _
    have hsolution := huPlusSolution.sub (B.ell k) (B.rho_measurable k)
      (B.rho_bounded k) hfPlusL2 hfMinusL2 huMinusSolution
    have hfDecomp : fPlus - fMinus = f := by
      simpa only [fPlus, fMinus] using
        (CompactlySupportedContinuousMap.nnrealPart_sub_nnrealPart_neg f)
    have hfDecompFun : (fPlus : Vec d → ℝ) - fMinus = f := by
      funext x
      exact congrArg (fun q : C_c(Vec d, ℝ) ↦ q x) hfDecomp
    simpa only [hfDecompFun] using hsolution

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
