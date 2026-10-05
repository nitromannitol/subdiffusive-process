module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.LocalLimitContinuousRepresentative

@[expose] public section

/-!
# Continuous compact-data GMC massive solutions

The signed compact-support monotone limit is replaced by its canonical global
continuous representative.  Its local weak equations are retained on every
centered cube.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open scoped CompactlySupported

noncomputable section

variable {d : ℕ}

/-- Compactly supported continuous forcing has a global continuous massive
solution for every GMC density satisfying the proved cube bounds. -/
theorem exists_continuous_localMassiveWeakSolution_of_compactSupport
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d)
    {rho : Vec d → ℝ} (B : MassiveCubeBounds (coefficientAt M L omega) rho)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : Vec d → ℝ, Continuous u ∧
      ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
          IsMassiveWeakSolutionOn (coefficientAt M L omega) rho mu
            (cube d (k : ℤ)) uLocal f := by
  obtain ⟨uRaw, huRawBound, huRawLocal⟩ :=
    exists_localMassiveWeakSolution_of_compactSupport B hmu f
  have hregular := continuous_and_ae_eq_localMassiveLimitRepresentative
    M L omega B f huRawBound huRawLocal
  let u := euclideanBallAverageRepresentative uRaw
  refine ⟨u, hregular.1, fun k ↦ ?_⟩
  obtain ⟨uLocal, huLocalAE, huLocalSolution⟩ := huRawLocal k
  have huAE : u =ᵐ[volume.restrict (cube d (k : ℤ))] uRaw :=
    hregular.2.filter_mono (ae_mono (Measure.restrict_le_self))
  exact ⟨uLocal, huLocalAE.trans huAE.symm, huLocalSolution⟩

/-- Continuous compact-data solutions for the reversible pair `(a,a)`. -/
theorem exists_continuous_localReversibleMassiveWeakSolution_of_compactSupport
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : Vec d → ℝ, Continuous u ∧
      ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
          IsMassiveWeakSolutionOn (coefficientAt M L omega)
            (coefficientAt M L omega) mu (cube d (k : ℤ)) uLocal f :=
  exists_continuous_localMassiveWeakSolution_of_compactSupport
    M L omega (reversibleMassiveCubeBounds M L omega) hmu f

/-- Continuous compact-data solutions for the divergence pair `(a,1)`. -/
theorem exists_continuous_localDivergenceMassiveWeakSolution_of_compactSupport
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : Vec d → ℝ, Continuous u ∧
      ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
          IsMassiveWeakSolutionOn (coefficientAt M L omega)
            (fun _ ↦ (1 : ℝ)) mu (cube d (k : ℤ)) uLocal f :=
  exists_continuous_localMassiveWeakSolution_of_compactSupport
    M L omega (divergenceMassiveCubeBounds M L omega) hmu f

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
