module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularityKilled
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationMeasure

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularityKilled
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKDatumCarrier

variable {d : ℕ} {c rho : Vec d → ℝ} {law : ProbabilityTheory.Kernel (Vec d) (Path d)}
  {U : Set (Vec d)}

/-- **The `fullSupport` field of the (RRK) datum**, for a weighted measure with a
two-sided elliptic weight restricted to an open set. -/
theorem fullSupportOn_weightedMeasure_restrict (hU : IsOpen U) (hrho : CoefficientOn U rho) :
    FullSupportOn ((weightedMeasure rho).restrict U) U := by
  intro V hV hVU hVne
  obtain ⟨x, hx⟩ := hVne
  exact (weightedMeasure_restrict_open_pos hU hrho V hV
    ⟨x, hx, hVU hx⟩).ne'

/-- The weight of a local diffusion is two-sided elliptic on every bounded open
set. -/
theorem coefficientOn_of_localDiffusion (hD : LocalDiffusion c rho law)
    (hUb : Bornology.IsBounded U) : CoefficientOn U rho :=
  coefficientOn_mono subset_closure
    (hD.2.1 (closure U) hUb.isCompact_closure).2

/-- **Route 1 of the heat-kernel corollary with its measure-theoretic
hypothesis discharged.**  For a local diffusion on a bounded open set, the only
remaining input for absolute continuity of the killed law at *every* starting
point is the continuity in the starting point of the killed transition
probabilities — the clause proved cannot be removed. -/
theorem killedLawAbsolutelyContinuousOn_of_continuousOn_of_localDiffusion
    (hD : LocalDiffusion c rho law) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hcont : ∀ t : ℝ, 0 < t → ∀ B : Set (Vec d), MeasurableSet B →
      ContinuousOn (fun x => (killedKernel law U hU (Real.toNNReal t) x B).toReal) U) :
    KilledLawAbsolutelyContinuousOn law rho U :=
  killedLawAbsolutelyContinuousOn_of_continuousOn hD hU hUb
    (fullSupportOn_weightedMeasure_restrict hU (coefficientOn_of_localDiffusion hD hUb)) hcont

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKDatumCarrier
