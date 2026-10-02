import SubdiffusiveProcess.Sobolev.GridFoldConvolution

open MeasureTheory Set TopologicalSpace
open scoped NNReal
noncomputable section

namespace SubdiffusiveProcess

def continuousPositiveLog {d : ℕ} {K : Compacts (SpatialCoordinates d)}
    (a : C(K, ℝ)) (ha : ∀ x, 0 < a x) : C(K, ℝ) :=
  ⟨fun x => Real.log (a x), Continuous.log a.continuous fun x => (ha x).ne'⟩

end SubdiffusiveProcess
