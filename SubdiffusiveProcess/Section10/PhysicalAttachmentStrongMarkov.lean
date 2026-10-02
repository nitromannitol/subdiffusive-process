import SubdiffusiveProcess.Section10.PhysicalAttachment
import SubdiffusiveProcess.Section10.PhysicalAttachmentRestart
import SubdiffusiveProcess.Probability.Diffusion.AnalyticBridge

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalAttachment

/-- The every-start quenched state-to-path kernel of the jointly measurable family. -/
def physicalSlice {d : ℕ} (X : PhysicalKernel d) (omega : AnchoredC11Sample d) :
    Kernel (Vec d) (ContinuousPath (Vec d)) :=
  X.comap (Prod.mk omega) measurable_prodMk_left

theorem physicalSlice_fdd {d : ℕ} (X : PhysicalKernel d) (omega : AnchoredC11Sample d)
    (P : SubMarkovKernelSemigroup (Vec d))
    (hF : ∀ I x, X.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) :
    ∀ I x, (physicalSlice X omega).map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x := by
  intro I x
  rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
  change Measure.map (ContinuousPath.finsetEvaluation I) (X (omega, x)) = _
  rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
  exact hF I x



theorem exists_physical_strongMarkov_family {d : ℕ} [NeZero d]
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)] (M : GMCModel d) :
    ∃ X : WithTop ℕ → PhysicalKernel d,
      (∀ L, IsMarkovKernel (X L)) ∧
      ∀ᵐ omega ∂(physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
        StrongMarkov ((physicalSlice (X L) omega).map LifetimePath.ofContinuousPath) ∧
        ∃ D : C0ResolventDatum (Vec d), ∃ hdense : ∀ mu, DenseRange (D.operator mu),
          IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D ∧
          (D.fellerKernelSemigroup hdense).IsConservative ∧
          ∀ (I : Finset NNReal) (x : Vec d),
            ((physicalSlice (X L) omega).map (ContinuousPath.finsetEvaluation I)) x =
              SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x := by
  obtain ⟨X, hX, hactual⟩ := exists_physical_family M
  refine ⟨X, hX, ?_⟩
  filter_upwards [hactual] with omega homega
  intro L
  obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := homega L
  letI := hX L
  have hK : IsMarkovKernel (physicalSlice (X L) omega) := by
    dsimp only [physicalSlice]
    infer_instance
  have hKF := physicalSlice_fdd (X L) omega (D.fellerKernelSemigroup hdense) hfdd
  refine ⟨?_, D, hdense, hweak, hcons, hKF⟩
  exact SubdiffusiveProcess.Probability.Diffusion.strongMarkov_of_restart
    (fellerRestart d (D.fellerKernelSemigroup hdense) hcons
      (D.isFellerKernelSemigroup_fellerKernelSemigroup hdense)
      (physicalSlice (X L) omega) hK hKF)

end SubdiffusiveProcess.Section10.PhysicalAttachment
