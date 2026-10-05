module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.GMCCompactSupportContinuousLimit

@[expose] public section

/-!
# The compact-data massive solution is bounded

`GMCCompactSupportContinuousLimit.lean` produces the global *continuous*
representative of the signed compact-support monotone limit but forgets the
sup bound the construction supplies.  That uniform estimate is recorded here
for the minimal whole-space solution construction.

The transfer is elementary: the raw limit obeys `|u| ≤ C` everywhere, the
representative agrees with it almost everywhere, and a continuous function
which is `≤ C` almost everywhere is `≤ C` everywhere because a nonempty open
set has positive Lebesgue measure.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open scoped CompactlySupported

noncomputable section

variable {d : ℕ}

/-- **The continuous compact-data massive solution, with its sup bound.**  This
is `exists_continuous_localMassiveWeakSolution_of_compactSupport` with the
bound of `exists_localMassiveWeakSolution_of_compactSupport` carried through the
choice of continuous representative. -/
theorem exists_continuous_bounded_localMassiveWeakSolution_of_compactSupport
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : WithTop ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d)
    {rho : Vec d → ℝ} (B : MassiveCubeBounds (coefficientAt M L omega) rho)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ)) :
    ∃ u : Vec d → ℝ, Continuous u ∧ (∃ Mb : ℝ, ∀ x, |u x| ≤ Mb) ∧
      ∀ k : ℕ, ∃ uLocal : H1Function (cube d (k : ℤ)),
        uLocal.toFun =ᵐ[volume.restrict (cube d (k : ℤ))] u ∧
          IsMassiveWeakSolutionOn (coefficientAt M L omega) rho mu
            (cube d (k : ℤ)) uLocal f := by
  classical
  set C : ℝ := ‖compactSupportToC0 f.nnrealPart.toReal‖ / mu +
    ‖compactSupportToC0 (-f).nnrealPart.toReal‖ / mu with hCdef
  obtain ⟨uRaw, huRawBound, huRawLocal⟩ :=
    exists_localMassiveWeakSolution_of_compactSupport B hmu f
  have hregular := continuous_and_ae_eq_localMassiveLimitRepresentative
    M L omega B f huRawBound huRawLocal
  set u : Vec d → ℝ := euclideanBallAverageRepresentative uRaw with hudef
  refine ⟨u, hregular.1, ⟨C, ?_⟩, fun k ↦ ?_⟩
  · have hae : ∀ᵐ x ∂(volume : Measure (Vec d)), |u x| ≤ C := by
      filter_upwards [hregular.2] with x hx
      rw [hx]
      exact huRawBound x
    intro x
    by_contra hx
    push Not at hx
    have hopen : IsOpen {y : Vec d | C < |u y|} :=
      isOpen_lt continuous_const hregular.1.abs
    have hne : ({y : Vec d | C < |u y|}).Nonempty := ⟨x, hx⟩
    have hpos : 0 < volume {y : Vec d | C < |u y|} := hopen.measure_pos volume hne
    have hzero : volume {y : Vec d | C < |u y|} = 0 := by
      have hnot : ∀ᵐ y ∂(volume : Measure (Vec d)), ¬ (C < |u y|) := by
        filter_upwards [hae] with y hy
        exact not_lt.mpr hy
      simpa using MeasureTheory.ae_iff.mp hnot
    exact absurd hzero hpos.ne'
  · obtain ⟨uLocal, huLocalAE, huLocalSolution⟩ := huRawLocal k
    have huAE : u =ᵐ[volume.restrict (cube d (k : ℤ))] uRaw :=
      hregular.2.filter_mono (ae_mono Measure.restrict_le_self)
    exact ⟨uLocal, huLocalAE.trans huAE.symm, huLocalSolution⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
