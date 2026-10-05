module

public import SubdiffusiveProcess.Main.CubeFractionalL2
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

/-!
# The real fractional Sobolev norm on a cube

The domain `CubeFractionalL2` consists of coordinate `L²` fields whose
extended fractional seminorm is finite, on a cube of positive side parameter
and at exponent `0 < s < 1`. `cubeFractionalL2Norm` adds the finite seminorm's
real conversion to the volume-normalized `L²` term weighted by `r^(-s)`.
Finiteness is carried by the subtype. `ENNReal.toReal ∞ = 0`, so `.toReal`
by itself does not prove finiteness for a general extended-real input.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess

/-- M's inhomogeneous normalized Hs norm on its finite-norm carrier. -/
def cubeFractionalL2Norm {d k : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1)
    (f : CubeFractionalL2 (k := k) hd z r hr s) : ℝ :=
  (cubeFractionalL2Seminorm hd z r hr s f.val).toReal +
    r ^ (-(s : ℝ)) *
      (Real.sqrt (∑ i : Fin k, ‖f.val i‖ ^ 2) /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))

end SubdiffusiveProcess
