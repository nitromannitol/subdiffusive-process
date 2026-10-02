import SubdiffusiveProcess.Main.MeasureTrace

open Filter MeasureTheory Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

namespace SubdiffusiveProcess



structure CubeFractionalInterpolationInput (d : ℕ) (hd : 2 ≤ d) : Prop where
  /-- `‖w‖_{H^{1/2}} ≤ C (‖w‖_{L²})^{1/3} ‖w‖_{H^{3/4}}^{2/3}` on the fixed cube,
  with the volume-normalized `L²` factor and a positive constant `C` depending
  only on the fixed cube and the dimension. -/
  interpolation_half : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (threeQuarters : Set.Ioo (0 : ℝ) 1), (threeQuarters : ℝ) = 3 / 4 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (wHalf : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
        (wThree : CubeFractionalL2 (k := 1) hd z r hr threeQuarters),
        wThree.val 0 = wHalf.val 0 →
        cubeFractionalL2Norm hd z r hr halfFractionalOrder wHalf ≤
          C * (‖wHalf.val 0‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^ (1 / 3 : ℝ) *
            cubeFractionalL2Norm hd z r hr threeQuarters wThree ^ (2 / 3 : ℝ)
  /-- `H^{3/4}(Q)` embeds compactly in `L²(Q)`. -/
  compact_embedding : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (threeQuarters : Set.Ioo (0 : ℝ) 1), (threeQuarters : ℝ) = 3 / 4 →
    ∀ (w : ℕ → CubeFractionalL2 (k := 1) hd z r hr threeQuarters) (M : ℝ),
      (∀ n : ℕ, cubeFractionalL2Norm hd z r hr threeQuarters (w n) ≤ M) →
      ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
        ∃ wlim : DomainL2 (centeredCube z r hr),
          Tendsto (fun n => ‖(w (sigma n)).val 0 - wlim‖) atTop (𝓝 0)

end SubdiffusiveProcess
