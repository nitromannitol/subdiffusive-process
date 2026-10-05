module

public import SubdiffusiveProcess.Section10.TorsionExitBassSmoothingConsumer
public import SubdiffusiveProcess.Section10.KilledStartOccupation

@[expose] public section




noncomputable section
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- Generic same-speed/energy actual LocalDiffusion upper-exit consumer, with
the every-start occupation slot discharged by actual killed-start continuity.
The deterministic all-H10 input is the native Sobolev estimate, not a promised
torsion/exit bound. The final actual supplier discharges this continuity slot. -/
theorem localDiffusion_meanExit_le_of_killedStartContinuity {d : ℕ}
    {A b : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} [IsMarkovKernel law]
    {U : Set (Vec d)} (hlocal : LocalDiffusion A b law)
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    (hb : CoefficientOn U b) {p Ksob : ℝ} (hp : 2 < p) (hKsob : 0 < Ksob)
    (hSob : TorsionSobolevBound A b U p Ksob)
    (hcont : ∀ t : ℝ, 0 < t →
      ContinuousOn (fun x => (killedKernel law U hU.isOpen
        (Real.toNNReal t) x univ).toReal) U) :
    ∀ x ∈ U, meanExit law U x ≤ ENNReal.ofReal
      (torsionConstant p * Ksob * (weightedMeasure b U).toReal ^ (1 - 2 / p)) :=
  localDiffusion_meanExit_le hlocal hU hne hb hp hKsob hSob
    (unitDiscountOccupationLSC_of_killedStartContinuity hU.isOpen hcont)

end SubdiffusiveProcess.Section10
