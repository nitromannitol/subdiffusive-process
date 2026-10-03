module

public import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_chart_transport

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal

noncomputable section
namespace Paper

/-- The coarse entry of type `b` (`true`: `σ`, `false`: `σ_*^{-1}`) of the unit chart on cell `R`. -/
def g9_cell_entry {d : ℕ} [NeZero d] (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (R : Homogenization.TriadicCube d)
    (b : Bool) (i j : Fin d) (K : ℕ) (omega : BilateralField d) : ℝ :=
  if b then
    Homogenization.Book.Ch02.sigmaCoarse (Homogenization.Book.Ch02.cubeDomain R)
      ((aux_U2_unitChart I M H omega K).coeffOn R) i j
  else
    Homogenization.Book.Ch02.sigmaStarInvCoarse (Homogenization.Book.Ch02.cubeDomain R)
      ((aux_U2_unitChart I M H omega K).coeffOn R) i j

end Paper
