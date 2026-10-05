module

public import SubdiffusiveProcess.Main.CubeSmoothFractionalL2Tests
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-!
# The real negative fractional Sobolev norm on a cube

`cubeNegativeL2Norm` takes the supremum of volume-normalized pairings against
nonzero smooth fractional-Sobolev test fields, divided by their inhomogeneous
norm. The cube has positive side parameter and `0 < s < 1`; the vector field
has coordinate `L²` components. To use this real supremum as the intended
dual norm requires the associated set of pairings to be nonempty and bounded
above. A total real `sSup` alone supplies neither property. Its test class is
distinct from the zero-boundary `H¹₀` tests in Theorem B.
-/

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
