module

public import SubdiffusiveProcess.Geometry.TriadicPartitionExists

@[expose] public section

/-! Finite triadic partitions along the boundary of a cube inside a fixed cube: existence.
The statement is pure geometry: actual triadic cells, finite covers, persistence and packing.
It asserts no coefficient control, Sobolev extension, form membership or limiting trace.
Construction: start the refinement at depth `J0 = Jr + minLevel`, keep a cell as soon as
its closure misses `∂B`, refine the others up to depth `J0 + n`. Disjointness, covers and persistence
are tree properties (`SubdiffusiveProcess.Geometry.TriadicLeafTree`); the boundary-layer cells of
each depth are disjoint and lie in a shell of `∂B`, so their number is bounded by volume
(`TriadicShellPacking`, `TriadicLeafCost`), and `TriadicPartitionExists` assembles the structure.
The former classical leaf is replaced by this proof; the statement is unchanged. -/
open Set MeasureTheory TopologicalSpace SubdiffusiveProcess
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Finite triadic refinements along a cube boundary have persistent cells and summable geometric costs above codimension one. -/
theorem inputs_classical_triadic_boundary_partitions
    {d : ℕ} [NeZero d] (s : ℝ) (hs : (d : ℝ) - 1 < s)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (minLevel : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : SpatialCoordinates d) (r : ℝ), 0 < r →
      Metric.ball w (r / 2) ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      Nonempty (TriadicBoundaryPartitions z R hR (Metric.ball w (r / 2)) r s C minLevel) := by
  exact triadicBoundaryPartitions_exists s hs z R hR minLevel

end SubdiffusiveProcess.Paper
