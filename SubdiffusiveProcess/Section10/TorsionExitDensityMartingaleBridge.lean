import SubdiffusiveProcess.Section10.TorsionExitDensityWeight
import SubdiffusiveProcess.Section10.TorsionExitDensityPhysical




noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open MarkovProcess.SubMarkovKernelSemigroup
namespace SubdiffusiveProcess.Section10

/-- Remaining general classical density assertion on the actual supplied law.
The continuous-path carrier makes nonexplosion explicit. This is not claimed
to be the literal statement of a verified reference. -/
def CompactMartingaleKilledDensityInput : Prop :=
  ∀ (d : ℕ) (_hd : 2 ≤ d) (b : Vec d → Vec d) (_hb : LocallyLipschitz b)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) (_hK : IsMarkovKernel K),
    IsCompactTestMartingaleProblem b K →
      SubdiffusiveProcess.Probability.Diffusion.Input.ContinuousKilledDensities (fun _ ↦ 1)
        (K.map LifetimePath.ofContinuousPath)

/-- Every project-specific hypothesis of the compact-test density application
is proved from the unchanged P3 inputs; the speed conversion is literal. -/
theorem smoothReversibleKilledDensitySupplier_of_compactMartingaleDensity
    (hDensity : CompactMartingaleKilledDensityInput) :
    SmoothReversibleKilledDensitySupplier := by
  intro d hd a hapos ha D hdense hweak hcons K hK hfdd
  letI := hK
  have hfdd' : ∀ I : Finset NNReal,
      K.map (ContinuousPath.finsetEvaluation I) =
        finiteSetKernel (D.fellerKernelSemigroup hdense) I := by
    intro I
    ext x B hB
    exact congrArg (fun mu : Measure (I → Vec d) ↦ mu B) (hfdd I x)
  have hMP := compactTestMartingaleProblem_of_weakResolvent hapos ha
    D hdense hweak hcons K hfdd'
  have hLebesgue := hDensity d hd (reversibleDrift a)
    (locallyLipschitz_reversibleDrift hapos ha) K hK hMP
  exact continuousKilledDensities_change_speed
    (contDiff_one_of_locallyC11 ha).continuous hapos hLebesgue

end SubdiffusiveProcess.Section10
