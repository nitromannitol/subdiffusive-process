module

public import SubdiffusiveProcess.Sobolev.HolderBoundaryExtension

@[expose] public section

/-! Compactly supported Hölder extensions of cube traces, with no prescribed linear extension
operator. This is the geometric extension step in the paper's gluing argument. -/

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology NNReal ENNReal

noncomputable section
namespace SubdiffusiveProcess.Section9

/-- A Hölder trace on the middle cube has a global Hölder extension supported strictly inside
its concentric triple enlargement. -/
theorem exists_holder_compact_cube_extension {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (b : SpatialCoordinates d → ℝ)
    (hb : IsHolderOn alpha (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b) :
    ∃ B : SpatialCoordinates d → ℝ,
      Continuous B ∧ HasCompactSupport B ∧
      tsupport B ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) ∧
      IsHolderOn alpha Set.univ B ∧
      EqOn B b (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  let S : Set (SpatialCoordinates d) := frontier (centeredCube z r hr : Set (SpatialCoordinates d))
  have hbcont : ContinuousOn b S := by
    apply _root_.SubdiffusiveProcess.Paper.aux_lem_goodext_continuousOn_of_holder alpha (holderSeminorm alpha S b) ha
    intro x hx y hy
    by_cases hxy : x = y
    · subst y
      rw [sub_self, abs_zero]
      exact mul_nonneg (holderSeminorm_nonneg _ _ _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    · have he := sqrt_sum_sq_sub_pos hxy
      exact (div_le_iff₀ (Real.rpow_pos_of_pos he alpha)).mp
        (le_csSup hb ⟨x, hx, y, hy, hxy, rfl⟩)
  have hScompact : IsCompact S := by
    apply (isCompact_closedBall z (r / 2)).of_isClosed_subset isClosed_frontier
    intro x hx
    exact Metric.mem_closedBall.mpr
      (Metric.mem_sphere.mp (Metric.frontier_ball_subset_sphere hx)).le
  have hsep : ∀ x ∈ S, ∀ y ∈ (Metric.ball z r)ᶜ, r / 2 ≤ dist x y := by
    intro x hx y hy
    have hxrad : dist x z = r / 2 :=
      Metric.mem_sphere.mp (Metric.frontier_ball_subset_sphere hx)
    have hyrad : r ≤ dist y z := not_lt.mp hy
    have htri := dist_triangle y x z
    rw [dist_comm y x] at htri
    linarith only [hxrad, hyrad, htri]
  obtain ⟨B, hBc, hBholder, hBtrace, hBzero⟩ :=
    exists_holder_boundary_extension_zero_on S (Metric.ball z r)ᶜ hScompact b hbcont
      alpha ha ha1 hb (r / 2) (half_pos hr) hsep
  have hsupp : Function.support B ⊆ Metric.ball z r :=
    Function.support_subset_iff'.mpr hBzero
  have htsupp : tsupport B ⊆ Metric.closedBall z r :=
    (closure_mono hsupp).trans Metric.closure_ball_subset_closedBall
  have hBcompact : HasCompactSupport B :=
    (isCompact_closedBall z r).of_isClosed_subset isClosed_closure htsupp
  have hBinside : tsupport B ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    htsupp.trans (Metric.closedBall_subset_ball (by linarith only [hr]))
  exact ⟨B, hBc, hBcompact, hBinside, hBholder, hBtrace⟩

end SubdiffusiveProcess.Section9
