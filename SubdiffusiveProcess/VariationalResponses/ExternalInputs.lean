module

public import SubdiffusiveProcess.Main.MeasureTrace

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

namespace SubdiffusiveProcess

/-- **Fractional Sobolev input on cubes.**  Di Nezza-Palatucci-Valdinoci;
Lions-Magenes.  The interpolation inequality
`‖w‖_{H^{1/2}} ≤ C ‖w‖_{L²}^{1/3}‖w‖_{H^{3/4}}^{2/3}` and the compactness of
`H^{3/4}(Q) ⊂⊂ L²(Q)`, on the project's `CubeFractionalL2` carriers.  The `L²`
factor is VOLUME-NORMALIZED: it is
`‖wHalf.val 0‖ / Real.sqrt (volume.real (centeredCube z r hr))`, matching
`cubeFractionalL2Norm`'s inhomogeneous term, and the interpolation constant `C`
is quantified BEFORE the two functions and depends only on the fixed cube and the
dimension.  The paper's displayed interpolation assertion  is written
with an UNNORMALIZED `L²` norm; on the fixed cube the normalized and unnormalized
norms are equivalent with a factor depending only on the cube and the dimension,
and the quantified `C` absorbs that fixed normalization.  Consequently this
carrier must not impose the false constant-one unnormalized estimate, which the
constant function `1` refutes on a cube of volume `< 1`.  Used by the final
sentence of `mfd:lem-19` and by
`mfd:lem-varying-trace`.  Prop-valued, a deferred external input
record.

No Lean witness; frozen on the author's deferral of published inputs, Di Nezza–Palatucci–Valdinoci, fractional Sobolev interpolation and Rellich compact embedding on cubes. -/
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
