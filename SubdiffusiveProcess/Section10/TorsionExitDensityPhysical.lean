module

public import SubdiffusiveProcess.Section10.TorsionExitDensity
public import SubdiffusiveProcess.Section10.ClassicalDensityConsumer
public import SubdiffusiveProcess.Section10.KilledSobolevConstants

@[expose] public section

/-! Actual finite/top physical application of the already proposed smooth
reversible density supplier. The supplier is a precise conditional input,
not an axiom, registered theorem or proof of the mean-exit source root. -/

noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Assumptions.CoefficientRegularity
open SubdiffusiveProcess.Section10.PhysicalAttachment
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- Exact classical proposal 3 (smooth reversible killed density).
This definition names its complete type and supplies no witness. -/
def SmoothReversibleKilledDensitySupplier : Prop :=
  ∀ (d : ℕ) (_hd : 2 ≤ d) (a : (Fin d → ℝ) → ℝ)
    (_hapos : ∀ x, 0 < a x) (_ha : SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11 a)
    (D : C0ResolventDatum (Fin d → ℝ)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (_hweak : IsWeakEllipticResolvent a a D)
    (_hcons : (D.fellerKernelSemigroup hdense).IsConservative)
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) (_hK : IsMarkovKernel K)
    (_hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel (D.fellerKernelSemigroup hdense) I x),
      SubdiffusiveProcess.Probability.Diffusion.Input.ContinuousKilledDensities a
        (K.map LifetimePath.ofContinuousPath)

/-- The actual smooth physical family has lower-semicontinuous discounted
occupations and the every-start upper mean-exit cap, relative precisely to
proposal 3 and the registered FOT input. No separate Feller LSC leaf remains.
The deterministic all-H10 Sobolev input is supplied by the static bank. -/
theorem exists_physical_unitCube_meanExit_le_of_smooth_density
    (hDensity : SmoothReversibleKilledDensitySupplier) {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]
    (hFOT : SubdiffusiveProcess.E7.FOTPartProcess) (M : GMCModel d) :
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
              (weightedMeasure (coefficientAt M L omega) U).toReal ^ (1 / (d : ℝ))) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨X, hX, hactual⟩ := physical_localDiffusionData_family_of_smooth_density hDensity hd hFOT M
  refine ⟨X, hX, ?_⟩
  filter_upwards [hactual] with omega homega
  intro L
  let := hX L
  let : IsMarkovKernel (physicalSlice (X L) omega) := by
    dsimp only [physicalSlice]; infer_instance
  let : IsMarkovKernel ((physicalSlice (X L) omega).map LifetimePath.ofContinuousPath) :=
    Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath
  let U : Set (Vec d) := Metric.ball 0 (1 / 2)
  have hU : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_ball 0 (by norm_num)
  have hdata : LocalDiffusionData (coefficientAt M L omega) (coefficientAt M L omega)
      ((physicalSlice (X L) omega).map LifetimePath.ofContinuousPath) := homega L
  have hdens := hdata.2 U hU.isOpen hU.isBoundedDomain.isBounded
  refine ⟨hdata, unitDiscountOccupationLSC_of_density hU.isOpen hdens, ?_⟩
  intro Ksob hKsob hSob
  have hne : U.Nonempty := ⟨0, Metric.mem_ball_self (by norm_num)⟩
  have hb : CoefficientOn U (coefficientAt M L omega) := coefficientOn_of_continuous_pos
    (continuous_coefficientAt M L omega) (coefficientAt_pos M L omega) hU.isBoundedDomain.isBounded
  have hp : 2 < 2 * (d : ℝ) / ((d : ℝ) - 1) := killedSobolevExponent_gt_two hd
  have hpower : 1 - 2 / (2 * (d : ℝ) / ((d : ℝ) - 1)) = 1 / (d : ℝ) :=
    killedSobolev_one_sub_two_div hd
  simpa only [hpower] using
    localDiffusion_meanExit_le_of_density hdata.1 hU hne hb hp hKsob hSob hdens

end SubdiffusiveProcess.Section10
