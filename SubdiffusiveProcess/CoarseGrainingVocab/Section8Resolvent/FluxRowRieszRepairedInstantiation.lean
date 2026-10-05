module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszPerCellGeneric
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedProducer

@[expose] public section

/-!
# Repaired stopping-family instantiation of the flux-row interface

This file connects the repaired maximal-laminar, parent-replaced, half-grid
stopping family to the carrier-polymorphic Fourier-space Riesz endpoint.  The
only geometric hypotheses left explicit are the two local-finiteness inputs
of the deterministic repaired-family producer.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.Frozen.Section8
open scoped BigOperators

noncomputable section

variable {d : ℕ} [NeZero d] {base : ℤ}
variable {failure : TriadicCube d → Set (PotentialSample d)}
variable {omega : PotentialSample d}



def repairedFluxRowRieszPartition
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base) :
    FluxRowRieszPartition d (RefinedStoppingCell failure omega base) :=
  (repairedFluxRowRieszStoppingFamily failure omega hinitial hrepair chi).toPartition

@[simp]
theorem repairedFluxRowRieszPartition_scale
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base)
    (q : RefinedStoppingCell failure omega base) :
    (repairedFluxRowRieszPartition hinitial hrepair chi).scale q =
      refinedStoppingScale q :=
  rfl

@[simp]
theorem repairedFluxRowRieszPartition_cell
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base)
    (q : RefinedStoppingCell failure omega base) :
    (repairedFluxRowRieszPartition hinitial hrepair chi).cell q =
      translatedCube d (refinedStoppingScale q + 1) (refinedStoppingCenter q) :=
  rfl

@[simp]
theorem repairedFluxRowRieszPartition_overlapCount
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base) :
    (repairedFluxRowRieszPartition hinitial hrepair chi).overlapCount =
      repairedStoppingDegreeBound d + 1 :=
  rfl

/-- Analytic flux-row data on the actual repaired selected-cell carrier. -/
abbrev RepairedFluxRowRieszStoppingInput
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base) (R sigma : ℝ)
    (F : Vec d → Vec d) :=
  FluxRowRieszStoppingInputGeneric
    (repairedFluxRowRieszStoppingFamily failure omega hinitial hrepair chi)
    R sigma F

/-- Assemble the coefficient budget on the repaired graph from exact graph
spheres and their summable shell majorants.  This is the concrete composition at
which the manuscript's shell moment estimate is consumed. -/
def repairedFluxRowRieszCoefficientBudget
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty)
    (localNegative : Fin d → RefinedStoppingCell failure omega base → ℝ)
    (K : ℝ) (hlocNonneg : ∀ i q, 0 ≤ localNegative i q)
    (cellPrice : Fin d → RefinedStoppingCell failure omega base → ℝ)
    (hpriceNonneg : ∀ i q, 0 ≤ cellPrice i q)
    (hlocal : ∀ i q,
      (repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q *
          localNegative i q ^ 2 ≤ cellPrice i q)
    (levelCells : ℕ → Finset (RefinedStoppingCell failure omega base))
    (hlevel : ∀ j q, q ∈ levelCells j ↔
      stoppingGraphDistance repairedStoppingGraph source hsource q = j)
    (shellPrice : Fin d → ℕ → ℝ)
    (hshellSummable : ∀ i, Summable (shellPrice i))
    (hshell : ∀ i j,
      ∑ q ∈ levelCells j, cellPrice i q ≤ shellPrice i j) :
    FluxRowRieszCoefficientBudget
      (repairedFluxRowRieszPartition hinitial hrepair chi) localNegative K :=
  fluxRowRieszStoppingCoefficientBudgetGeneric
    (repairedFluxRowRieszStoppingFamily failure omega hinitial hrepair chi)
    localNegative K hlocNonneg cellPrice hpriceNonneg hlocal levelCells
    (stoppingGraphDistance repairedStoppingGraph source hsource) hlevel
    shellPrice hshellSummable hshell

/-- The repaired producer and the generic analytic package give the exact
flux clause of `WholeSpaceRows`.  Thus no raw-lattice adapter remains between
the selected-cell construction and the Fourier-space Riesz endpoint. -/
theorem RepairedFluxRowRieszStoppingInput.exists_wholeSpaceFluxHat
    (M : GMCModel d) (L : ℕ) {t : ℝ} {f : Vec d → ℝ}
    (u : WholeSpaceDivergenceResolventSolution (aCutoff M L omega) t f)
    {R sigma CSigma : ℝ} (Z : PotentialSample d → ℝ)
    (hscale : (3 : ℝ) ^ L ≤ R)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base)
    (A : RepairedFluxRowRieszStoppingInput hinitial hrepair chi R sigma
      (fun x ↦ (aCutoff M L omega x - ahom M L) • u.grad x))
    (hcellPrice :
      (∑ i, 2 *
          (((repairedFluxRowRieszPartition hinitial hrepair chi).overlapCount : ℝ) *
            A.fourierComparison) *
          ∑' q, A.coefficientBudget.cellPrice i q) ≤
        CSigma * Z omega * ahom M L * t⁻¹ * R ^ (2 * sigma) *
          ∫ x, f x ^ 2 ∂volume) :
    ∃ fluxHat : Vec d → Fin d → ℂ,
      IsFourierRepresentative
        (fun x ↦ (aCutoff M L omega x - ahom M L) • u.grad x) fluxHat ∧
      massiveNegativeSobolevNormSq R sigma fluxHat ≤
        CSigma * Z omega * ahom M L * t⁻¹ * R ^ (2 * sigma) *
          ∫ x, f x ^ 2 ∂volume := by
  exact FluxRowRieszStoppingInputGeneric.exists_wholeSpaceFluxHat
    M L u Z hscale A hcellPrice

/-- On the repaired family, the generic cell price uses the repaired graph,
the refined analytic scale, and no auxiliary carrier conversion. -/
theorem repairedFluxRowRieszStoppingFamily_cellPrice_eq
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty) (q : RefinedStoppingCell failure omega base)
    (C ahomValue t R sigma fEnergy theta E1 E2 lambdaInv : ℝ) :
    (repairedFluxRowRieszStoppingFamily failure omega hinitial hrepair chi).cellPrice
        source hsource q C ahomValue t R sigma fEnergy theta E1 E2 lambdaInv =
      fluxRowRieszCellPrice C ahomValue t R sigma fEnergy theta
        ((3 : ℝ) ^ refinedStoppingScale q)
        (stoppingGraphDistance repairedStoppingGraph source hsource q)
        d E1 E2 lambdaInv :=
  rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
