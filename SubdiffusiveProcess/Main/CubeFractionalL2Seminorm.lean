module

public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess

/-- M's volume-normalized fractional Hs seminorm on a cube, as a nonnegative extended integral. -/
def cubeFractionalL2Seminorm {d k : ℕ} (_hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1)
    (f : Fin k → DomainL2 (centeredCube z r hr)) : ℝ≥0∞ :=
  ((ENNReal.ofReal (s : ℝ) / volume (centeredCube z r hr : Set (SpatialCoordinates d))) *
    ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ))) ^ (1 / 2 : ℝ)

end SubdiffusiveProcess
