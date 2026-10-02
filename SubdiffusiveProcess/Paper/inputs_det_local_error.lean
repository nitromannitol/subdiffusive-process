import SubdiffusiveProcess.Analysis.DeterministicAnchorTransport
import SubdiffusiveProcess.Analysis.InteriorComparisonErrorTransport
import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.BoundaryCellRow

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book Homogenization.Book.Ch03
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper

theorem inputs_det_local_error (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hsle : s ≤ (1 / 4 : ℝ))
    (m n : ℕ) (z x y : Vec d)
    (hx : x ∈ truncatedCube d m ((n : ℤ) - 3) z)
    (hy : y ∈ truncatedCube d m n x)
    (a : Vec d → ℝ) (data : ScalarTriadicCoeffData (fun q => a (q + z)))
    (dataY : ScalarTriadicCoeffData (fun q => a (q + y))) (a0 : ℝ) (ha0 : 0 < a0) :
    (let err := paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2)
      (s / 8) Ch02.MultiscaleExponent.infinity (.finite 2) data.toTriadicCoeffFamily a0;
     err ≠ ⊤ →
     Ch02.HomogenizationErrorOnCube (originCube d ((n : ℤ) - 2)) (s / 6)
       .infinity (.finite 2) dataY.toTriadicCoeffFamily (scalarMatrix (d := d) a0) ≤
       Real.sqrt (192 * (d : ℝ)) * ((3 : ℝ) ^ (s / 2) * err.toReal)) := by
  intro err hfin
  have hcontain := SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.closedOffGridCube_subset_originAnchorParent_of_mem_nextWindow
    (m := (m : ℤ)) (n := (n : ℤ)) hx hy
  exact SubdiffusiveProcess.InteriorComparisonEngine.aux_icc_errorTransport n s err.toReal a0 a z y data dataY
    hs (by linarith) ENNReal.toReal_nonneg ha0 (ENNReal.le_ofReal_iff_toReal_le hfin ENNReal.toReal_nonneg |>.mpr le_rfl) hcontain

end Paper
