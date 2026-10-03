module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszStoppingGenericInput
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszPerCellPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionGraphDistance

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization
open Homogenization.Book
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Cell : Type*} [Encodable Cell] [DecidableEq Cell]
variable {failure : TriadicCube d → Set (PotentialSample d)}
variable {omega : PotentialSample d}

/-- The literal graph-weighted price attached to a repaired stopping cell. -/
def FluxRowRieszStoppingFamily.cellPrice
    (H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega)
    (source : Finset Cell) (hsource : source.Nonempty) (q : Cell)
    (C ahom t R sigma fEnergy theta E1 E2 lambdaInv : ℝ) : ℝ :=
  fluxRowRieszCellPrice C ahom t R sigma fEnergy theta
    ((3 : ℝ) ^ H.scale q)
    (stoppingGraphDistance H.graph source hsource q) d E1 E2 lambdaInv

theorem FluxRowRieszStoppingFamily.cellPrice_eq
    (H : FluxRowRieszStoppingFamily (Cell := Cell) failure omega)
    (source : Finset Cell) (hsource : source.Nonempty) (q : Cell)
    (C ahom t R sigma fEnergy theta E1 E2 lambdaInv : ℝ) :
    H.cellPrice source hsource q C ahom t R sigma fEnergy theta E1 E2
        lambdaInv =
      fluxRowRieszCellPrice C ahom t R sigma fEnergy theta
        ((3 : ℝ) ^ H.scale q)
        (stoppingGraphDistance H.graph source hsource q) d E1 E2 lambdaInv :=
  rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
