import SubdiffusiveProcess.Main.CubeFractionalL2Norm
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open MeasureTheory Set TopologicalSpace
open scoped ENNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess

/-- Smooth test classes on the closed cube, represented inside the finite fractional space. -/
def cubeSmoothFractionalL2Tests {d k : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1) :
    Set (CubeFractionalL2 (k := k) hd z r hr s) :=
  {u | ∃ (O : Opens (SpatialCoordinates d)) (f : SpatialCoordinates d → Fin k → ℝ),
    closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ O ∧
      ContDiffOn ℝ ∞ f (O : Set (SpatialCoordinates d)) ∧
      ∀ i : Fin k, (u.val i : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] (fun x => f x i)}

end SubdiffusiveProcess
