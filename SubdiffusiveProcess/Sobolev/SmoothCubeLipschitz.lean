module

public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ContDiff NNReal
namespace SubdiffusiveProcess

/-- A function smooth on an open neighborhood of a closed cube is Lipschitz on the cube. Used to justify the smooth-test carrier in M. -/
theorem exists_lipschitzOnWith_cube_of_contDiffOn_neighborhood
    {d k : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (O : Opens (SpatialCoordinates d))
    (hO : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ O)
    (f : SpatialCoordinates d → Fin k → ℝ)
    (hf : ContDiffOn ℝ ∞ f (O : Set (SpatialCoordinates d))) :
    ∃ K : ℝ≥0, LipschitzOnWith K f
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  have hcompact : IsCompact
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (centeredCube_isBounded z hr).isCompact_closure
  have hderiv_cont : ContinuousOn (fderiv ℝ f)
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (hf.continuousOn_fderiv_of_isOpen O.isOpen (by simp)).mono hO
  obtain ⟨C, hC_pos, hC⟩ :=
    (hcompact.image_of_continuousOn hderiv_cont).isBounded.exists_pos_norm_le
  let K : ℝ≥0 := ⟨C, hC_pos.le⟩
  refine ⟨K, (convex_ball z (r / 2)).lipschitzOnWith_of_nnnorm_fderiv_le
    (𝕜 := ℝ) ?_ ?_⟩
  · intro x hx
    have hxO : x ∈ (O : Set (SpatialCoordinates d)) := hO (subset_closure hx)
    exact (hf.differentiableOn (by simp) x hxO).differentiableAt
      (O.isOpen.mem_nhds hxO)
  · intro x hx
    change ‖fderiv ℝ f x‖ ≤ C
    exact hC (fderiv ℝ f x) ⟨x, subset_closure hx, rfl⟩

end SubdiffusiveProcess
