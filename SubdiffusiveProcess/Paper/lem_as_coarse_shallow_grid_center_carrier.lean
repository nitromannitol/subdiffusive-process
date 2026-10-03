module

public import Homogenization.Geometry.TriadicPartition
public import Homogenization.Geometry.CubeMetric
public import Mathlib.Tactic

@[expose] public section

open Homogenization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper

/-- Every actual retained-grid center lies in the centered reference cube. -/
theorem lem_as_coarse_shallow_grid_center_carrier
    {d k : ℕ} {Q : TriadicCube d}
    (hQ : Q ∈ descendantsAtScale (originCube d 0) (-(k : ℤ))) :
    ∀ i : Fin d, |cubeCenter Q i| ≤ (1 / 2 : ℝ) := by
  have hk : -(k : ℤ) ≤ (originCube d 0).scale := by
    change -(k : ℤ) ≤ 0
    omega
  have hsub := cubeSet_subset_of_mem_descendantsAtScale hk hQ
  have hcenter : cubeCenter Q ∈ cubeSet Q := by
    intro i
    change ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q ≤
        (Q.index i : ℝ) * cubeScaleFactor Q ∧
      (Q.index i : ℝ) * cubeScaleFactor Q <
        ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q
    have hs : 0 < cubeScaleFactor Q := by
      dsimp [cubeScaleFactor]
      positivity
    constructor <;> nlinarith
  have hroot := mem_cubeSet_originCube_iff.mp (hsub hcenter)
  intro i
  have hi := hroot i
  norm_num at hi
  exact abs_le.mpr ⟨hi.1, hi.2.le⟩

end Paper

