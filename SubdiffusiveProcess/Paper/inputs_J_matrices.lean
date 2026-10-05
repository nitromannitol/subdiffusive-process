module

public import SubdiffusiveProcess.Paper.in_J
public import Homogenization.Book.Ch02.Theorems.MatrixExtractionProofs

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem inputs_J_matrices (d : ℕ) (_hd : 2 ≤ d) :
    (∀ (U : Homogenization.Book.Ch02.Domain d)
      (a : Homogenization.Book.Ch02.CoeffOn U),
      Homogenization.Book.Ch02.ResponseMatrixExists U a) := by
  intro U a
  exact Homogenization.Book.Ch02.responseMatrixExists U a

end SubdiffusiveProcess.Paper
