import SubdiffusiveProcess.Section10.PhysicalAttachmentSemigroup
import SubdiffusiveProcess.Section10.PhysicalAttachmentPathRealization

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalAttachment

abbrev PhysicalKernel (d : ℕ) :=
  Kernel (AnchoredC11Sample d × Vec d) (ContinuousPath (Vec d))

/-- Jointly measurable laws of the actual physical reversible coefficients,
including every finite cutoff and the untruncated anchored coefficient.
One source full event carries the weak-resolvent and FDD characterization for
every cutoff and every starting point. No diffusion witness is assumed. -/
theorem exists_physical_family {d : ℕ} [NeZero d]
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)] (M : GMCModel d) :
    ∃ X : WithTop ℕ → PhysicalKernel d,
      (∀ L, IsMarkovKernel (X L)) ∧
      ∀ᵐ omega ∂(physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
        ∃ D : C0ResolventDatum (Vec d), ∃ hdense : ∀ mu, DenseRange (D.operator mu),
          IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D ∧
          (D.fellerKernelSemigroup hdense).IsConservative ∧
          ∀ (I : Finset NNReal) (x : Vec d),
            ((X L).map (ContinuousPath.finsetEvaluation I)) (omega, x) =
              SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x := by
  obtain ⟨P, hPcons, hPfeller, hPactual⟩ := exists_physical_semigroups M
  let X : WithTop ℕ → PhysicalKernel d := fun L =>
    ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess (P L) (hPcons L)
  refine ⟨X, fun L => inferInstance, ?_⟩
  filter_upwards [hPactual] with omega homega
  intro L
  obtain ⟨D, hdense, hweak, heq, hsupport⟩ := homega L
  have hDcons : (D.fellerKernelSemigroup hdense).IsConservative := by
    rw [← heq]
    exact hPcons L omega
  refine ⟨D, hdense, hweak, hDcons, ?_⟩
  intro I x
  let default : ContinuousPath (Vec d) :=
    ContinuousMap.const NNReal (Classical.arbitrary (Vec d))
  have hfdd := pa_fdd ((P L).toSubMarkovKernelSemigroup omega)
    (hPcons L omega) (hPfeller L omega) default hsupport I
  change ((ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess
    (P L) (hPcons L)).map (ContinuousPath.finsetEvaluation I)) (omega, x) = _
  rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I),
    ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_apply,
    SubMarkovKernelSemigroup.IsConservative.continuousProcess,
    ← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
  have h := congrArg (fun K : Kernel (Vec d) (I → Vec d) => K x) hfdd
  simpa only [default, heq] using h

/-- The characterized law is unique at every start, as a whole state-to-path kernel.
This is the same FDD determination used by the Section 7 cemetery construction. -/
theorem physical_slice_unique {d : ℕ}
    (P : SubMarkovKernelSemigroup (Vec d))
    (K Q : Kernel (Vec d) (ContinuousPath (Vec d)))
    (hK : IsMarkovKernel K)
    (hKF : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (hQF : ∀ I x, Q.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) : K = Q := by
  letI := hK
  apply Kernel.eq_of_map_denseFiniteEvaluation_eq
  intro I
  apply Kernel.ext
  intro x
  exact (hKF _ x).trans (hQF _ x).symm

end SubdiffusiveProcess.Section10.PhysicalAttachment
