import SubdiffusiveProcess.Section10.TorsionExitConsumer
import SubdiffusiveProcess.Section10.PhysicalAttachmentKilled
import SubdiffusiveProcess.Section10.KilledSobolevConstants

/-! Actual physical finite/top family application. FOT alone closes the AE
mean bound. The exact separate every-start regularity supplier is exposed
as a conclusion-level implication, not disguised as an existing FOT result. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Assumptions.CoefficientRegularity
open SubdiffusiveProcess.Section10.PhysicalAttachment
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10



theorem exists_physical_unitCube_meanExit_bounds {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess) (M : GMCModel d) :
    ∃ X : WithTop ℕ → PhysicalKernel d,
      (∀ L, IsMarkovKernel (X L)) ∧
      ∀ᵐ omega ∂(physicalLaw M).toMeasure, ∀ L : WithTop ℕ,
        ∀ Ksob : ℝ, 0 < Ksob →
          TorsionSobolevBound (coefficientAt M L omega) (coefficientAt M L omega)
            (Metric.ball (0 : Vec d) (1 / 2))
            (2 * (d : ℝ) / ((d : ℝ) - 1)) Ksob →
          (∀ᵐ x ∂(weightedMeasure (coefficientAt M L omega)).restrict
              (Metric.ball (0 : Vec d) (1 / 2)),
            meanExit ((physicalSlice (X L) omega).map LifetimePath.ofContinuousPath)
              (Metric.ball 0 (1 / 2)) x ≤
                ENNReal.ofReal (torsionConstant (2 * (d : ℝ) / ((d : ℝ) - 1)) * Ksob *
                  (weightedMeasure (coefficientAt M L omega)
                    (Metric.ball 0 (1 / 2))).toReal ^ (1 / (d : ℝ)))) ∧
          (FellerUnitCubeDiscountOccupationLSC → ∀ x ∈ Metric.ball (0 : Vec d) (1 / 2),
            meanExit ((physicalSlice (X L) omega).map LifetimePath.ofContinuousPath)
              (Metric.ball 0 (1 / 2)) x ≤
                ENNReal.ofReal (torsionConstant (2 * (d : ℝ) / ((d : ℝ) - 1)) * Ksob *
                  (weightedMeasure (coefficientAt M L omega)
                    (Metric.ball 0 (1 / 2))).toReal ^ (1 / (d : ℝ)))) := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨X, hX, hactual⟩ := exists_physical_localDiffusion_family hFOT M
  refine ⟨X, hX, ?_⟩
  filter_upwards [hactual] with omega homega
  intro L Ksob hKsob hSob
  obtain ⟨hlocal, D, hdense, _, hcons, hfdd⟩ := homega L
  letI := hX L
  letI : IsMarkovKernel (physicalSlice (X L) omega) := by
    dsimp only [physicalSlice]; infer_instance
  letI : IsMarkovKernel ((physicalSlice (X L) omega).map LifetimePath.ofContinuousPath) :=
    Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath
  let U : Set (Vec d) := Metric.ball 0 (1 / 2)
  have hU : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_ball 0 (by norm_num)
  have hne : U.Nonempty := ⟨0, Metric.mem_ball_self (by norm_num)⟩
  have hb : CoefficientOn U (coefficientAt M L omega) := coefficientOn_of_continuous_pos
    (continuous_coefficientAt M L omega) (coefficientAt_pos M L omega) hU.isBoundedDomain.isBounded
  have hp : 2 < 2 * (d : ℝ) / ((d : ℝ) - 1) := killedSobolevExponent_gt_two hd
  have hpower : 1 - 2 / (2 * (d : ℝ) / ((d : ℝ) - 1)) = 1 / (d : ℝ) :=
    killedSobolev_one_sub_two_div hd
  constructor
  · simpa only [hpower] using localDiffusion_meanExit_ae_le hlocal hU hne hb hp hKsob hSob
  · intro hregularity
    have hls := hregularity d (D.fellerKernelSemigroup hdense) hcons
      (D.isFellerKernelSemigroup_fellerKernelSemigroup hdense)
      (physicalSlice (X L) omega) inferInstance hfdd
    simpa only [hpower] using localDiffusion_meanExit_le hlocal hU hne hb hp hKsob hSob hls


end SubdiffusiveProcess.Section10
