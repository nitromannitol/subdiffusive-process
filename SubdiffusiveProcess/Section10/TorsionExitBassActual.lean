module

public import SubdiffusiveProcess.Section10.TorsionExitBassOccupation
public import SubdiffusiveProcess.Section10.ReversibleFellerLocalL1

@[expose] public section

/-! Completed actual reversible killed-density supplier and unnormalized
every-start physical upper mean exit, relative ONLY to the registered FOT
part-process input. All smoothing, rough local approximation, actual early
exit and original-law continuity certificates are proved and consumed.
No Friedman/SDE input, general-drift density assertion or new clock is used. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.Section10.PhysicalAttachment
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- The exact P3 reversible supplier is now proved, relative solely to the
FOT part-process input. All completing slots are
discharged with their actual proofs, for every bounded open carrier and start. -/
theorem smoothReversibleKilledDensitySupplier
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess) :
    SmoothReversibleKilledDensitySupplier :=
  smoothReversibleKilledDensitySupplier_of_localL1Estimate
    hFOT reversibleFellerLocalL1ApproximationSupplier

/-- Concrete generic all-start LocalDiffusionData for the SAME specified
reversible weak-resolvent/Feller full-FDD realization. No density or analytic
estimate is supplied by the caller. -/
theorem localDiffusionData_of_reversible_weakResolvent
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess) {d : ℕ} (hd : 2 ≤ d)
    {a : Vec d → ℝ} (hapos : ∀ x, 0 < a x)
    (ha : SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11 a)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hweak : IsWeakEllipticResolvent a a D)
    (hcons : (D.fellerKernelSemigroup hdense).IsConservative)
    (K : Kernel (Vec d) (ContinuousPath (Vec d))) [IsMarkovKernel K]
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x) :
    LocalDiffusionData a a (K.map LifetimePath.ofContinuousPath) := by
  have hD := localDiffusion_of_reversible_weakResolvent
    hFOT hapos ha D hdense hweak hcons K hfdd
  have hdens := smoothReversibleKilledDensitySupplier hFOT d hd a hapos ha
    D hdense hweak hcons K inferInstance hfdd
  refine ⟨hD, fun U hU hUb => ?_⟩
  obtain ⟨p, hm, hp, hmass, hcont⟩ := hdens U hU hUb
  exact ⟨p, ⟨hm, hp, hmass⟩, hcont⟩

/-- Actual finite/top physical family upper mean exit, including cutoff zero,
every interior start and literal p=2d/(d-1). The all-H10 Sobolev constant is
supplied by the actual static-bank producer; no stochastic regularity slot remains.
The mean exit is the original ENNReal exit expectation, without normalization. -/
theorem exists_physical_unitCube_meanExit_le
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess) {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)] (M : GMCModel d) :
    ∃ X : WithTop ℕ → PhysicalKernel d,
      (∀ L, IsMarkovKernel (X L)) ∧
      ∀ᵐ omega ∂(physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
        let law := (physicalSlice (X L) omega).map LifetimePath.ofContinuousPath
        let U : Set (Vec d) := Metric.ball 0 (1 / 2)
        LocalDiffusionData (coefficientAt M L omega) (coefficientAt M L omega) law ∧
        UnitDiscountOccupationLSC law U ∧
        ∀ Ksob : ℝ, 0 < Ksob →
          TorsionSobolevBound (coefficientAt M L omega) (coefficientAt M L omega) U
            (2 * (d : ℝ) / ((d : ℝ) - 1)) Ksob →
          ∀ x ∈ U, meanExit law U x ≤ ENNReal.ofReal
            (torsionConstant (2 * (d : ℝ) / ((d : ℝ) - 1)) * Ksob *
              (weightedMeasure (coefficientAt M L omega) U).toReal ^ (1 / (d : ℝ))) :=
  exists_physical_unitCube_meanExit_le_of_smooth_density
    (smoothReversibleKilledDensitySupplier hFOT) hd hFOT M

end SubdiffusiveProcess.Section10
