module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.TopWindow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.FractionalHolderBridge

@[expose] public section

/-!
# Hölder Step 5: interior boundary gate

If the frozen centre lies in `cube (m-1)`, every sufficiently smaller top
window generated from one of its descendants stays strictly inside `cube m`.
This is the geometric implication behind the printed boundary indicator.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A descendant top window at least five scales below the domain cannot
touch the boundary when its original centre is one scale inside. -/
theorem not_boundaryTouches_top_of_interior {d : ℕ} {m n top : ℤ}
    {x y : Vec d} (hx : x ∈ cube d (m - 1)) (hy : y ∈ truncatedCube d m n x)
    (hntop : n ≤ top) (htop : top ≤ m - 5) :
    ¬ BoundaryTouches (truncatedCube d m top y) (cube d m) := by
  intro htouch
  obtain ⟨q, hqclose, hqfrontier⟩ := Set.nonempty_iff_ne_empty.mpr htouch
  have hycube : y ∈ cube d m := hy.2
  have htopBall : truncatedCube d m top y ⊆ Metric.ball y ((3 : ℝ) ^ top) :=
    truncatedCube_subset_ball (mem_truncatedCube_self top hycube)
  have hqball : q ∈ Metric.closedBall y ((3 : ℝ) ^ top) := by
    exact (closure_minimal
      (htopBall.trans Metric.ball_subset_closedBall) Metric.isClosed_closedBall) hqclose
  have hqy : dist q y ≤ (3 : ℝ) ^ top := Metric.mem_closedBall.mp hqball
  have hxTranslated : x ∈ translatedCube d n x :=
    ⟨0, zero_mem_cube d n, by simp⟩
  have hyx : dist y x < (3 : ℝ) ^ n :=
    dist_lt_of_mem_translatedCube
      (truncatedCube_subset_translatedCube d m n x hy) hxTranslated
  have hzero : (0 : Vec d) ∈ cube d (m - 1) := zero_mem_cube d (m - 1)
  have hxzero : dist x 0 < (3 : ℝ) ^ (m - 1) :=
    Metric.mem_ball.mp (cube_subset_ball hzero hx)
  have hnPower : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ top :=
    zpow_le_zpow_right₀ (by norm_num) hntop
  have htopPower : (3 : ℝ) ^ top ≤ (3 : ℝ) ^ (m - 5) :=
    zpow_le_zpow_right₀ (by norm_num) htop
  have hbase : 0 < (3 : ℝ) ^ (m - 5) := by positivity
  have hmOne : (3 : ℝ) ^ (m - 1) = 81 * (3 : ℝ) ^ (m - 5) := by
    rw [show m - 1 = (m - 5) + 4 by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hm : (3 : ℝ) ^ m = 243 * (3 : ℝ) ^ (m - 5) := by
    rw [show m = (m - 5) + 5 by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
    ring
  have hqzero : dist q 0 < (3 : ℝ) ^ m / 2 := by
    have htri1 := dist_triangle q y x
    have htri2 := dist_triangle q x 0
    have hqy_x : dist q x < (3 : ℝ) ^ top + (3 : ℝ) ^ n :=
      lt_of_le_of_lt htri1 (add_lt_add_of_le_of_lt hqy hyx)
    have hq0raw : dist q 0 <
        ((3 : ℝ) ^ top + (3 : ℝ) ^ n) + (3 : ℝ) ^ (m - 1) :=
      htri2.trans_lt (add_lt_add hqy_x hxzero)
    calc
      dist q 0 < ((3 : ℝ) ^ top + (3 : ℝ) ^ n) +
          (3 : ℝ) ^ (m - 1) := hq0raw
      _ ≤ (3 : ℝ) ^ m / 2 := by
        rw [hmOne, hm]
        nlinarith
  have hqcube : q ∈ cube d m := by
    rw [cube, ← ball_cubeCenter_eq_openCubeSet]
    apply Metric.mem_ball.mpr
    have hcenter : cubeCenter (originCube d m) = 0 := by
      funext i
      simp [cubeCenter, originCube]
    rw [hcenter]
    simpa [cubeRadius, cubeScaleFactor, originCube, div_eq_mul_inv,
      mul_comm] using hqzero
  have hopen : IsOpen (cube d m) := (isOpenBoundedConvexDomain_cube d m).isOpen
  exact Set.disjoint_left.1 (disjoint_frontier_iff_isOpen.mpr hopen) hqfrontier hqcube

/-- Indicator form used when rebasing the full-domain Campanato estimate. -/
theorem boundaryIndicator_top_le_not_interior {d : ℕ} {m n top : ℤ}
    {x y : Vec d} (hy : y ∈ truncatedCube d m n x)
    (hntop : n ≤ top) (htop : top ≤ m - 5) :
    (if BoundaryTouches (truncatedCube d m top y) (cube d m) then (1 : ℝ) else 0) ≤
      if x ∈ cube d (m - 1) then 0 else 1 := by
  by_cases hinterior : x ∈ cube d (m - 1)
  · rw [if_pos hinterior, if_neg
      (not_boundaryTouches_top_of_interior hinterior hy hntop htop)]
  · rw [if_neg hinterior]
    split_ifs <;> norm_num

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
