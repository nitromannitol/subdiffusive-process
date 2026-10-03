module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.CompactSupportSignedLocalLimit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.GMCCubeBounds

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped CompactlySupported ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-- The reversible GMC cube exhaustion has a common bounded local weak limit. -/
theorem exists_bounded_localReversibleMassiveWeakSolution_of_compactSupport
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    ∃ u : Vec d → ℝ,
      (∀ x, 0 ≤ u x ∧ u x ≤ ‖compactSupportToC0 f‖ / mu) ∧
        ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
          uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
            IsMassiveWeakSolutionOn (coefficientAt M L omega)
              (coefficientAt M L omega) mu (cube d (k : ℤ)) uLocal f :=
  exists_bounded_localMassiveWeakSolution_of_compactSupport
    (reversibleMassiveCubeBounds M L omega) hmu f hf

/-- The divergence-form GMC cube exhaustion has a common bounded local weak
limit. -/
theorem exists_bounded_localDivergenceMassiveWeakSolution_of_compactSupport
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    ∃ u : Vec d → ℝ,
      (∀ x, 0 ≤ u x ∧ u x ≤ ‖compactSupportToC0 f‖ / mu) ∧
        ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
          uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
            IsMassiveWeakSolutionOn (coefficientAt M L omega)
              (fun _ ↦ (1 : ℝ)) mu (cube d (k : ℤ)) uLocal f :=
  exists_bounded_localMassiveWeakSolution_of_compactSupport
    (divergenceMassiveCubeBounds M L omega) hmu f hf

/-- Signed compactly supported forcing has compatible local reversible GMC
massive weak solutions. -/
theorem exists_localReversibleMassiveWeakSolution_of_compactSupport [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : Vec d → ℝ, ∀ k : ℕ,
      ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
          IsMassiveWeakSolutionOn (coefficientAt M L omega)
            (coefficientAt M L omega) mu (cube d (k : ℤ)) uLocal f :=
  by
    obtain ⟨u, _huBound, hu⟩ := exists_localMassiveWeakSolution_of_compactSupport
      (reversibleMassiveCubeBounds M L omega) hmu f
    exact ⟨u, hu⟩

/-- Signed compactly supported forcing has compatible local divergence-form GMC
massive weak solutions. -/
theorem exists_localDivergenceMassiveWeakSolution_of_compactSupport [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : Vec d → ℝ, ∀ k : ℕ,
      ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
          IsMassiveWeakSolutionOn (coefficientAt M L omega)
            (fun _ ↦ (1 : ℝ)) mu (cube d (k : ℤ)) uLocal f :=
  by
    obtain ⟨u, _huBound, hu⟩ := exists_localMassiveWeakSolution_of_compactSupport
      (divergenceMassiveCubeBounds M L omega) hmu f
    exact ⟨u, hu⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
