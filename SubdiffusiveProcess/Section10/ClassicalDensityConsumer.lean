import SubdiffusiveProcess.Section10.PhysicalAttachmentKilled

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Literal application of an explicit proposed classical supplier to the existing
physical family. This conditional theorem does not prove or install that supplier.
The already registered FOT input is also kept explicit. -/
theorem physical_localDiffusionData_family_of_smooth_density
    (hDensity :
∀ (d : ℕ) (hd : 2 ≤ d)
  (a : (Fin d → ℝ) → ℝ)
  (hapos : ∀ x, 0 < a x)
  (ha : SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11 a)
  (D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (Fin d → ℝ))
  (hdense : ∀ mu, DenseRange (D.operator mu))
  (hweak : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent a a D)
  (hcons : (D.fellerKernelSemigroup hdense).IsConservative)
  (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
  (hK : IsMarkovKernel K)
  (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
    SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x),
  SubdiffusiveProcess.Probability.Diffusion.Input.ContinuousKilledDensities a
    (K.map LifetimePath.ofContinuousPath))
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess) (M : GMCModel d) :
    ∃ X : WithTop ℕ → PhysicalAttachment.PhysicalKernel d,
      (∀ L, IsMarkovKernel (X L)) ∧
      ∀ᵐ omega ∂(PhysicalAttachment.physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
        LocalDiffusionData (coefficientAt M L omega) (coefficientAt M L omega)
          (((X L).comap (Prod.mk omega) measurable_prodMk_left).map
            LifetimePath.ofContinuousPath) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨X, hX, hactual⟩ := PhysicalAttachment.exists_physical_strongMarkov_family M
  refine ⟨X, hX, ?_⟩
  filter_upwards [hactual] with omega homega
  intro L
  obtain ⟨hsm, D, hdense, hweak, hcons, hfdd⟩ := homega L
  letI := hX L
  have hK : IsMarkovKernel (PhysicalAttachment.physicalSlice (X L) omega) := by
    dsimp only [PhysicalAttachment.physicalSlice]
    infer_instance
  have hgen := PhysicalAttachment.physical_killedGenerator hFOT M L omega D hdense
    hweak hcons (PhysicalAttachment.physicalSlice (X L) omega) hK hfdd
  have hdens := hDensity d hd (coefficientAt M L omega) (coefficientAt_pos M L omega)
    (PhysicalAttachment.locallyC11_coefficientAt M L omega) D hdense hweak hcons
    (PhysicalAttachment.physicalSlice (X L) omega) hK hfdd
  exact SubdiffusiveProcess.Probability.Diffusion.localDiffusionData_of_killedGenerator hsm
    (continuous_coefficientAt M L omega) (coefficientAt_pos M L omega)
    (continuous_coefficientAt M L omega) (coefficientAt_pos M L omega) hgen hdens

end SubdiffusiveProcess.Section10
