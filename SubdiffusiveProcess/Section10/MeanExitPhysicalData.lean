module

public import SubdiffusiveProcess.Section10.MeanExitEarlyExitInterface
public import SubdiffusiveProcess.Section10.TorsionExitDensityPhysical
public import SubdiffusiveProcess.Section10.PhysicalAttachmentKilled

@[expose] public section

open Filter MeasureTheory ProbabilityTheory MarkovProcess Topology Homogenization
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Section10.PhysicalAttachment
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Every family with the actual source characterization has its own original
same-coefficient LocalDiffusionData. No auxiliary law or coupling is used. -/
theorem physicalMeanExitFamily_localDiffusionData {d : ℕ} (hd : 2 ≤ d)
    (hDensity : SmoothReversibleKilledDensitySupplier)
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess)
    (M : GMCModel d) (X : WithTop ℕ → PhysicalKernel d)
    (hX : ∀ L, IsMarkovKernel (X L)) (hphysical : IsPhysicalMeanExitFamily M X) :
    ∀ᵐ omega ∂(physicalLaw M).toMeasure, ∀ L,
      LocalDiffusionData (coefficientAt M L omega) (coefficientAt M L omega)
        ((physicalSlice (X L) omega).map LifetimePath.ofContinuousPath) := by
  filter_upwards [hphysical] with omega homega
  intro L
  obtain ⟨D, hdense, hweak, hcons, hfdd⟩ := homega L
  letI := hX L
  have hK : IsMarkovKernel (physicalSlice (X L) omega) := by
    dsimp only [physicalSlice]
    infer_instance
  have hfdd' : ∀ I x, (physicalSlice (X L) omega).map
      (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x := by
    intro I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    have h := hfdd I x
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)] at h
    exact h
  have hsm := SubdiffusiveProcess.Probability.Diffusion.strongMarkov_of_restart
    (fellerRestart d _ hcons (D.isFellerKernelSemigroup_fellerKernelSemigroup hdense)
      (physicalSlice (X L) omega) hK hfdd')
  have hgen := physical_killedGenerator hFOT M L omega D hdense hweak hcons
    (physicalSlice (X L) omega) hK hfdd'
  have hdens := hDensity d hd (coefficientAt M L omega) (coefficientAt_pos M L omega)
    (locallyC11_coefficientAt M L omega) D hdense hweak hcons
    (physicalSlice (X L) omega) hK hfdd'
  exact SubdiffusiveProcess.Probability.Diffusion.localDiffusionData_of_killedGenerator hsm
    (continuous_coefficientAt M L omega) (coefficientAt_pos M L omega)
    (continuous_coefficientAt M L omega) (coefficientAt_pos M L omega) hgen hdens

end SubdiffusiveProcess.Section10
