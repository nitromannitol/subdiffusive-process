import SubdiffusiveProcess.Geometry.BoundaryPartitions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Cell oscillation bounds pass through persistent boundary refinements.
No cell solutions or energy bounds are constructed in this module. -/
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess

/-- A positive Hölder power of the geometrically vanishing boundary mesh tends to zero. -/
theorem triadic_holder_error_tendsto_zero (H r alpha : ℝ) (ha : 0 < alpha) :
    Tendsto (fun n : ℕ => H * (r * (3 : ℝ) ^ (-(n : ℤ))) ^ alpha) atTop (𝓝 0) := by
  have hmesh : Tendsto (fun n : ℕ => (3 : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
    simpa only [zpow_neg, zpow_natCast, inv_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
        (by norm_num : (3 : ℝ)⁻¹ < 1)
  have hscale : Tendsto (fun n : ℕ => r * (3 : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hmesh
  have hpower : Tendsto (fun n : ℕ => (r * (3 : ℝ) ^ (-(n : ℤ))) ^ alpha) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow ha.ne'] using hscale.rpow_const (Or.inr ha.le)
  simpa only [mul_zero] using tendsto_const_nhds.mul hpower

/-- Hölder oscillation on each leaf bounds the boundary approximation by its fine mesh. -/
theorem TriadicBoundaryPartitions.trace_error_le
    {d : ℕ} {z : SpatialCoordinates d} {R : ℝ} {hR : 0 < R}
    {B : Set (SpatialCoordinates d)} {r s C : ℝ} {minLevel : ℕ}
    (P : TriadicBoundaryPartitions z R hR B r s C minLevel)
    {alpha H : ℝ} (ha : 0 ≤ alpha) (hH : 0 ≤ H)
    (V : ℕ → SpatialCoordinates d → ℝ) (b : SpatialCoordinates d → ℝ)
    (hOsc : ∀ n i x, x ∈ closure (triadicGridCell z R hR (P.label n i) : Set (SpatialCoordinates d)) →
      |V n x - b x| ≤ H * (triadicGridSide R (P.label n i)) ^ alpha) :
    ∀ n x, x ∈ frontier B → |V n x - b x| ≤ H * (r * (3 : ℝ) ^ (-(n : ℤ))) ^ alpha := by
  intro n x hx
  obtain ⟨i, hxi, hside⟩ := P.boundary n x hx
  exact (hOsc n i x hxi).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (triadicGridSide_pos hR (P.label n i)).le hside ha) hH)

/-- Persistent cell representatives give the pointwise alternative required for uniform refinement convergence. -/
theorem TriadicBoundaryPartitions.refinement_error
    {d : ℕ} {z : SpatialCoordinates d} {R : ℝ} {hR : 0 < R}
    {B : Set (SpatialCoordinates d)} {r s C : ℝ} {minLevel : ℕ}
    (P : TriadicBoundaryPartitions z R hR B r s C minLevel)
    {alpha H : ℝ} (ha : 0 ≤ alpha) (hH : 0 ≤ H)
    (V : ℕ → SpatialCoordinates d → ℝ) (Vcell : TriadicGridLabel d → SpatialCoordinates d → ℝ)
    (b : SpatialCoordinates d → ℝ)
    (hEq : ∀ n i, EqOn (V n) (Vcell (P.label n i))
      (closure (triadicGridCell z R hR (P.label n i) : Set (SpatialCoordinates d))))
    (hOsc : ∀ n i x, x ∈ closure (triadicGridCell z R hR (P.label n i) : Set (SpatialCoordinates d)) →
      |V n x - b x| ≤ H * (triadicGridSide R (P.label n i)) ^ alpha) :
    ∀ n m, n ≤ m → ∀ x,
      x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
      V m x = V n x ∨
        (|V n x - b x| ≤ H * (r * (3 : ℝ) ^ (-(n : ℤ))) ^ alpha ∧
          |V m x - b x| ≤ H * (r * (3 : ℝ) ^ (-(n : ℤ))) ^ alpha) := by
  intro n m hnm x hx
  rcases P.persistence n m hnm x hx with ⟨i, j, hij, hxi⟩ | ⟨i, j, hxi, hxj, hi, hj⟩
  · left
    have hxj : x ∈ closure (triadicGridCell z R hR (P.label m j) : Set (SpatialCoordinates d)) := by
      rw [← hij]
      exact hxi
    calc
      V m x = Vcell (P.label m j) x := hEq m j hxj
      _ = Vcell (P.label n i) x := by rw [hij]
      _ = V n x := (hEq n i hxi).symm
  · right
    constructor
    · exact (hOsc n i x hxi).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (triadicGridSide_pos hR (P.label n i)).le hi ha) hH)
    · exact (hOsc m j x hxj).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (triadicGridSide_pos hR (P.label m j)).le hj ha) hH)

/-- The trace errors vanish uniformly on the target frontier. -/
theorem TriadicBoundaryPartitions.tendstoUniformlyOn_frontier
    {d : ℕ} {z : SpatialCoordinates d} {R : ℝ} {hR : 0 < R}
    {B : Set (SpatialCoordinates d)} {r s C : ℝ} {minLevel : ℕ}
    (P : TriadicBoundaryPartitions z R hR B r s C minLevel)
    {alpha H : ℝ} (ha : 0 < alpha) (hH : 0 ≤ H)
    (V : ℕ → SpatialCoordinates d → ℝ) (b : SpatialCoordinates d → ℝ)
    (hOsc : ∀ n i x, x ∈ closure (triadicGridCell z R hR (P.label n i) : Set (SpatialCoordinates d)) →
      |V n x - b x| ≤ H * (triadicGridSide R (P.label n i)) ^ alpha) :
    TendstoUniformlyOn V b atTop (frontier B) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  have hsmall := (triadic_holder_error_tendsto_zero H r alpha ha).eventually (gt_mem_nhds heps)
  filter_upwards [hsmall] with n hn
  intro x hx
  have hle := P.trace_error_le ha.le hH V b hOsc n x hx
  simpa only [Real.dist_eq, abs_sub_comm] using hle.trans_lt hn

end SubdiffusiveProcess
