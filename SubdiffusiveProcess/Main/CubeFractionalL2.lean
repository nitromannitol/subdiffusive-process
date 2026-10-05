module

public import SubdiffusiveProcess.Main.CubeFractionalL2Seminorm
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess

/-- The actual fractional Hs space: coordinate L2 classes with finite source seminorm. -/
def CubeFractionalL2 {d k : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1) :=
  {f : Fin k → DomainL2 (centeredCube z r hr) //
    cubeFractionalL2Seminorm hd z r hr s f < ⊤}

end SubdiffusiveProcess
