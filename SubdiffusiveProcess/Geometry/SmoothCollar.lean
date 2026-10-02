import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Lane2.MeshGeometry

/-! Deterministic lib data extracted upstream of process convergence.
This module does not assert concentration or invoke the process-convergence theorem. -/

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators ContDiff
namespace SubdiffusiveProcess
noncomputable section

open scoped Manifold

/-- Extracted smooth collar argument from the pre-convergence deterministic proof. -/
theorem exists_smooth_cube_collar
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (b : SpatialCoordinates d → ℝ) (hb : ContDiff ℝ ∞ b) :
    ∃ B : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ B ∧ HasCompactSupport B ∧
      tsupport B ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) ∧
      ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), B x = b x := by
  have hqQ : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by linarith only [hr]))
  obtain ⟨K, hKcompact, hKclosed, hqK, hKQ⟩ := exists_compact_closed_between
    (lane2_isCompact_closure_centeredCube z hr) (centeredCube z (3 * r) h3r).isOpen hqQ
  obtain ⟨chi, hchiOne, hchiZero, _hchiRange⟩ := exists_smooth_one_nhds_of_subset_interior
    (𝓘(ℝ, SpatialCoordinates d)) isClosed_closure hqK
  have hchiSmooth : ContDiff ℝ ∞ chi := chi.contMDiff.contDiff
  have hsupp : tsupport (chi : SpatialCoordinates d → ℝ) ⊆ K :=
    closure_minimal (Function.support_subset_iff'.mpr hchiZero) hKclosed
  refine ⟨fun x => chi x * b x, hchiSmooth.mul hb, ?_, ?_, ?_⟩
  · exact hKcompact.of_isClosed_subset isClosed_closure (tsupport_mul_subset_left.trans hsupp)
  · exact tsupport_mul_subset_left.trans (hsupp.trans hKQ)
  · intro x hx
    change chi x * b x = b x
    rw [hchiOne.self_of_nhdsSet x hx, one_mul]

end
end SubdiffusiveProcess
