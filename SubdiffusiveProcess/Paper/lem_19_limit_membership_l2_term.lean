import SubdiffusiveProcess.Lane2.ExternalInputs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace Paper

/-- Fine proof step of Lemma 19 (paper 1943--1945).
Carried-input tick list:
- SOURCE: the parent lemma's actual L2 convergence `hlim` on the fixed cube.
- CONCLUDED HERE: convergence of the scalar L2 norm along the full sequence.
This is the continuity of the L2 summand used after the Fatou step; it does
not assume fractional membership of the limit. -/
theorem lem_19_limit_membership_l2_term
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (threeQuarters : Set.Ioo (0 : ℝ) 1)
    (hthree : (threeQuarters : ℝ) = 3 / 4)
    (w : ℕ → CubeFractionalL2 (k := 1) hd z r hr threeQuarters)
    (vlim : DomainL2 (centeredCube z r hr))
    (hlim : Tendsto (fun n : ℕ => (w n).val 0) atTop (𝓝 vlim)) :
    Tendsto (fun n : ℕ => ‖(w n).val 0‖) atTop (𝓝 ‖vlim‖) := by
  exact (continuous_norm.tendsto vlim).comp hlim

end Paper
