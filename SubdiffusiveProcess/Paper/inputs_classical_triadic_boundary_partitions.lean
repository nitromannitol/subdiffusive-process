import SubdiffusiveProcess.Geometry.TriadicPartitionExists



open Set MeasureTheory TopologicalSpace SubdiffusiveProcess
noncomputable section
namespace Paper

/-- Finite triadic refinements along a cube boundary have persistent cells and summable geometric costs above codimension one. -/
theorem inputs_classical_triadic_boundary_partitions
    {d : ℕ} [NeZero d] (s : ℝ) (hs : (d : ℝ) - 1 < s)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (minLevel : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : SpatialCoordinates d) (r : ℝ), 0 < r →
      Metric.ball w (r / 2) ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      Nonempty (TriadicBoundaryPartitions z R hR (Metric.ball w (r / 2)) r s C minLevel) := by
  exact triadicBoundaryPartitions_exists s hs z R hR minLevel

end Paper
