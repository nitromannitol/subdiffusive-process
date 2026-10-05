module

public import SubdiffusiveProcess.Section10.TorsionExitBassDensity
public import SubdiffusiveProcess.Section10.TorsionExitReversibleEarlyExit

@[expose] public section

/-! Reversible weighted RRK assembly for the ORIGINAL realized path law.
The three completing supplier proofs are independent components;
actual early exit and the generic FOT/weak-resolvent attachment are discharged
here. No Friedman input, clock normalization or broad martingale-density
conclusion is used. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
open SubdiffusiveProcess.Section10.PhysicalAttachment
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- Exact existing reversible density supplier from the weighted-route
components. UniformEarlyExit is proved from the native generator and is not
a completing premise. The registered FOT part-process input is unchanged. -/
theorem smoothReversibleKilledDensitySupplier_of_bassSuppliers
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess)
    (hsmooth : ReversibleKilledSmoothingSupplier)
    (happrox : ReversibleFellerLocalL1ApproximationSupplier)
    (hcontinuity : FellerKilledStartContinuitySupplier) :
    SmoothReversibleKilledDensitySupplier := by
  intro d hd a hapos ha D hdense hweak hcons K hK hfdd
  let : NeZero d := ⟨by omega⟩
  let := hK
  let law := K.map LifetimePath.ofContinuousPath
  let : IsMarkovKernel law :=
    Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath
  have hc := (contDiff_one_of_locallyC11 ha).continuous
  have hD : LocalDiffusion a a law :=
    localDiffusion_of_reversible_weakResolvent hFOT hapos ha D hdense hweak hcons K hfdd
  have hearly := uniformEarlyExit_of_reversible_weakResolvent
    hapos ha D hdense hweak hcons K hfdd
  have hF := D.isFellerKernelSemigroup_fellerKernelSemigroup hdense
  have hrough := happrox d hd a hapos hc (D.fellerKernelSemigroup hdense)
    hcons hF K hK hfdd hD hearly
  have hcont := hcontinuity d a hapos hc (D.fellerKernelSemigroup hdense)
    hcons hF K hK hfdd hrough hearly
  intro U hU hUb
  let : IsFiniteMeasure ((weightedMeasure a).restrict U) :=
    isFiniteMeasure_restrict (weightedMeasure_ne_top_of_localDiffusion hD hU hUb)
  obtain ⟨N, C, hC, hsup⟩ := hsmooth d hd a hapos hc law hD U hU hUb
  obtain ⟨p, ⟨hmeas, hpos, hmass⟩, hjoint⟩ :=
    hasContinuousKilledDensityOn_of_smoothing_and_start_continuity hd hD
      hU hUb (hc.continuousOn) N hC hsup (hcont U hU)
  exact ⟨p, hmeas, hpos, hmass, hjoint⟩

/-- Concrete unnormalized upper mean-exit application of the completing Bass
suppliers. It preserves the literal exponent 2d/(d-1), every interior start,
every finite/top physical cutoff, and the original coefficient and speed.
The static all-H10 Sobolev constant is supplied separately. -/
theorem exists_physical_unitCube_meanExit_le_of_bassSuppliers
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess)
    (hsmooth : ReversibleKilledSmoothingSupplier)
    (happrox : ReversibleFellerLocalL1ApproximationSupplier)
    (hcontinuity : FellerKilledStartContinuitySupplier)
    {d : ℕ} (hd : 2 ≤ d)
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
    (smoothReversibleKilledDensitySupplier_of_bassSuppliers hFOT hsmooth happrox hcontinuity)
    hd hFOT M

end SubdiffusiveProcess.Section10
