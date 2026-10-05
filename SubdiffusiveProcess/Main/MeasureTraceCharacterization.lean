module

public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.SmoothFractionalUpstream
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal ContDiff
noncomputable section

namespace SubdiffusiveProcess

def MeasureTraceCharacterization {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Q)
    (ν : Measure (SpatialCoordinates d)) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder → Lp ℝ 2 ν) : Prop :=
  (∀ u v : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder,
    ∃ w : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder,
      w.val 0 = u.val 0 - v.val 0) ∧
  (∀ (u v w : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
      (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder),
    w.val 0 = u.val 0 - v.val 0 →
    ‖T u - T v‖ ^ 2 ≤
      C * (K + (ν (closure (Homogenization.openCubeSet Q))).toReal) *
        (cubeFractionalL2Norm hd (Homogenization.cubeCenter Q)
          (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder w) ^ 2) ∧
  ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
    ∀ (v : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Q)
        (Homogenization.cubeScaleFactor Q) hr halfFractionalOrder),
      (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube (Homogenization.cubeCenter Q)
            (Homogenization.cubeScaleFactor Q) hr : Set (SpatialCoordinates d))] f →
      ∀ hf : MemLp f 2 ν, T v = hf.toLp f

end SubdiffusiveProcess
