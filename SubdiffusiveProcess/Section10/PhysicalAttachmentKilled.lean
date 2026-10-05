module

public import SubdiffusiveProcess.Section10.PhysicalAttachmentStrongMarkov
public import SubdiffusiveProcess.Processes.E7.E7Main

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess Homogenization Set
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalAttachment

/-- Apply the complete existing E7 consumer to the actual reversible coefficient,
resolvent and every-start path realization. The only unresolved classical input
in this helper is the already registered FOT part-process leaf. -/
theorem physical_killedGenerator {d : ℕ}
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess)
    (M : GMCModel d) (L : WithTop ℕ) (omega : AnchoredC11Sample d)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hweak : IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D)
    (hcons : (D.fellerKernelSemigroup hdense).IsConservative)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) (hK : IsMarkovKernel K)
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x) :
    SubdiffusiveProcess.Probability.Diffusion.Input.KilledGenerator
      (coefficientAt M L omega) (coefficientAt M L omega)
      (K.map LifetimePath.ofContinuousPath) := by
  exact (SubdiffusiveProcess.E7.e7_of_leaves fellerRestart hFOT d
    (coefficientAt M L omega) (coefficientAt M L omega)
    (coefficientAt_pos M L omega) (coefficientAt_pos M L omega)
    (locallyC11_coefficientAt M L omega) (locallyC11_coefficientAt M L omega)
    (D.fellerKernelSemigroup hdense) hcons D hdense hweak
    (D.solution_eq_laplace hdense) K hK hfdd).2

/-- The actual finite/top family satisfies the killed weak-resolvent and strong
Markov clauses of `LocalDiffusion`, relative to the existing FOT cited leaf.
Continuous killed densities are deliberately not asserted here. -/
theorem exists_physical_localDiffusion_family {d : ℕ} [NeZero d]
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess) (M : GMCModel d) :
    ∃ X : WithTop ℕ → PhysicalKernel d,
      (∀ L, IsMarkovKernel (X L)) ∧
      ∀ᵐ omega ∂(physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
        LocalDiffusion (coefficientAt M L omega) (coefficientAt M L omega)
          ((physicalSlice (X L) omega).map LifetimePath.ofContinuousPath) ∧
        ∃ D : C0ResolventDatum (Vec d), ∃ hdense : ∀ mu, DenseRange (D.operator mu),
          IsWeakEllipticResolvent (coefficientAt M L omega) (coefficientAt M L omega) D ∧
          (D.fellerKernelSemigroup hdense).IsConservative ∧
          ∀ I x, (physicalSlice (X L) omega).map (ContinuousPath.finsetEvaluation I) x =
            SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x := by
  obtain ⟨X, hX, hactual⟩ := exists_physical_strongMarkov_family M
  refine ⟨X, hX, ?_⟩
  filter_upwards [hactual] with omega homega
  intro L
  obtain ⟨hsm, D, hdense, hweak, hcons, hfdd⟩ := homega L
  let := hX L
  have hK : IsMarkovKernel (physicalSlice (X L) omega) := by
    dsimp only [physicalSlice]
    infer_instance
  have hgen := physical_killedGenerator hFOT M L omega D hdense hweak hcons
    (physicalSlice (X L) omega) hK hfdd
  have hc := continuous_coefficientAt M L omega
  have hpos := coefficientAt_pos M L omega
  refine ⟨⟨hsm, ?_, ?_⟩, D, hdense, hweak, hcons, hfdd⟩
  · intro S hS
    exact ⟨SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos hc hpos hS.isBounded,
      SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos hc hpos hS.isBounded⟩
  · intro U hU hUb s hs f hf
    exact SubdiffusiveProcess.Probability.Diffusion.killedResolvent_clause_of_killedGenerator hgen hU hUb
      (SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos hc hpos hUb)
      (SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos hc hpos hUb) hs hf

end SubdiffusiveProcess.Section10.PhysicalAttachment
