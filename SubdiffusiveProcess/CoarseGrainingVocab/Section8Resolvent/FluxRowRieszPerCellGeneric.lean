module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszStoppingGenericInput
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszPerCellPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionGraphDistance

@[expose] public section

/-!
# The graph-weighted local flux estimate on a repaired stopping carrier

This file records the literal graph-weighted cell price attached to a cell of a
repaired stopping family.

The carrier-polymorphic scale-`m` local flux price that used to live here
(`exists_fluxRowRiesz_repairedCell_localFluxPrice`) is **retired** together with
its repaired instantiation: it priced the scale-normalized negative dual on the
scale-`m` cube, which is not the coefficient the cutoff pairing produces
  The live replacement is
`exists_fluxRowRiesz_repairedStoppingCell_enlargedLocalFluxPrice`
(`FluxRowRieszEnlargedCellPrice.lean`).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization
open Homogenization.Book
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
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
