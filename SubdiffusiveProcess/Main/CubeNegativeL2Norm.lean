import SubdiffusiveProcess.Main.CubeSmoothFractionalL2Tests
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open MeasureTheory Set TopologicalSpace
open scoped ENNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess

/-- M's local negative Hs norm, specialized to coordinate L2 vector fields on a cube. -/
def cubeNegativeL2Norm {d k : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1)
    (F : Fin k → DomainL2 (centeredCube z r hr)) : ℝ :=
  sSup {v : ℝ | ∃ φ : CubeFractionalL2 (k := k) hd z r hr s,
    φ ∈ cubeSmoothFractionalL2Tests hd z r hr s ∧ φ.val ≠ 0 ∧
      v = |(volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∑ i : Fin k, F i x * φ.val i x| / cubeFractionalL2Norm hd z r hr s φ}

end SubdiffusiveProcess
