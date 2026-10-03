module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionHalfGridRefinement

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ} {Omega : Type*} {base : ℤ}

/-- A relative half-grid center lies within three half-widths of its selected
parent center. -/
theorem dist_cubeCenter_refinedStoppingCenter_le
    {failure : TriadicCube d → Set Omega} {omega : Omega}
    (q : RefinedStoppingCell failure omega base) :
    dist (cubeCenter (refinedStoppingFailureCube q))
        (refinedStoppingCenter q) ≤
      (3 / 2 : ℝ) * cubeScaleFactor (refinedStoppingFailureCube q) := by
  have hscale : 0 < cubeScaleFactor (refinedStoppingFailureCube q) :=
    zpow_pos (by norm_num) _
  rw [dist_pi_le_iff (mul_nonneg (by norm_num) hscale.le)]
  intro i
  have hkNat : (q.2.1 i).natAbs ≤ 3 :=
    by simpa only [Pi.zero_apply, sub_zero] using
      (mem_gridNeighbours_iff.mp q.2.2) i
  have hkReal : |(q.2.1 i : ℝ)| ≤ 3 := by
    have hcast : ((q.2.1 i).natAbs : ℝ) ≤ 3 := by exact_mod_cast hkNat
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
  have hhalf : 0 ≤ gridHalfWidth q.1.1.1.scale :=
    (gridHalfWidth_pos _).le
  rw [Real.dist_eq]
  change |cubeCenter q.1.1.1 i -
    (cubeCenter q.1.1.1 i +
      (q.2.1 i : ℝ) * gridHalfWidth q.1.1.1.scale)| ≤
      3 / 2 * cubeScaleFactor q.1.1.1
  rw [sub_add_cancel_left, abs_neg, abs_mul]
  rw [abs_of_nonneg hhalf]
  calc
    |(q.2.1 i : ℝ)| * gridHalfWidth q.1.1.1.scale ≤
        3 * gridHalfWidth q.1.1.1.scale :=
      mul_le_mul_of_nonneg_right hkReal hhalf
    _ = 3 / 2 * cubeScaleFactor q.1.1.1 := by
      rw [gridHalfWidth, cubeScaleFactor]
      ring

/-- A point of a refined cell lies within one half-side of its center. -/
theorem dist_refinedStoppingCenter_lt_of_mem
    {failure : TriadicCube d → Set Omega} {omega : Omega}
    {q : RefinedStoppingCell failure omega base} {x : Vec d}
    (hx : x ∈ translatedCube d (refinedStoppingScale q)
      (refinedStoppingCenter q)) :
    dist (refinedStoppingCenter q) x <
      (1 / 2 : ℝ) * cubeScaleFactor (refinedStoppingFailureCube q) := by
  rw [translatedCube_eq_metricBall, Metric.mem_ball] at hx
  simpa only [dist_comm, cubeRadius, cubeScaleFactor_originCube,
    refinedStoppingScale_eq_failureCube, cubeScaleFactor] using hx

/-- Intersecting refined cells have near selected parent cubes. -/
theorem stoppingCubesNear_of_refinedStoppingCell_inter_nonempty
    {failure : TriadicCube d → Set Omega} {omega : Omega}
    {q p : RefinedStoppingCell failure omega base}
    (hinter :
      (translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q) ∩
        translatedCube d (refinedStoppingScale p) (refinedStoppingCenter p)).Nonempty) :
    StoppingCubesNear (refinedStoppingFailureCube q)
      (refinedStoppingFailureCube p) := by
  obtain ⟨x, hxq, hxp⟩ := hinter
  let sq := cubeScaleFactor (refinedStoppingFailureCube q)
  let sp := cubeScaleFactor (refinedStoppingFailureCube p)
  have hqShift := dist_cubeCenter_refinedStoppingCenter_le q
  have hpShift := dist_cubeCenter_refinedStoppingCenter_le p
  have hqx := (dist_refinedStoppingCenter_lt_of_mem hxq).le
  have hpx := (dist_refinedStoppingCenter_lt_of_mem hxp).le
  have hpath : dist (cubeCenter (refinedStoppingFailureCube q))
      (cubeCenter (refinedStoppingFailureCube p)) ≤
      (3 / 2 * sq + 1 / 2 * sq) + (1 / 2 * sp + 3 / 2 * sp) := by
    calc
      dist (cubeCenter (refinedStoppingFailureCube q))
          (cubeCenter (refinedStoppingFailureCube p)) ≤
          dist (cubeCenter (refinedStoppingFailureCube q))
              (refinedStoppingCenter q) +
            dist (refinedStoppingCenter q)
              (cubeCenter (refinedStoppingFailureCube p)) :=
        dist_triangle _ _ _
      _ ≤ dist (cubeCenter (refinedStoppingFailureCube q))
              (refinedStoppingCenter q) +
            (dist (refinedStoppingCenter q) x +
              dist x (cubeCenter (refinedStoppingFailureCube p))) := by
        gcongr
        exact dist_triangle _ _ _
      _ ≤ dist (cubeCenter (refinedStoppingFailureCube q))
              (refinedStoppingCenter q) +
            (dist (refinedStoppingCenter q) x +
              (dist x (refinedStoppingCenter p) +
                dist (refinedStoppingCenter p)
                  (cubeCenter (refinedStoppingFailureCube p)))) := by
        gcongr
        exact dist_triangle _ _ _
      _ ≤ (3 / 2 * sq + 1 / 2 * sq) +
          (1 / 2 * sp + 3 / 2 * sp) := by
        have hpx' : dist x (refinedStoppingCenter p) ≤
            1 / 2 * cubeScaleFactor (refinedStoppingFailureCube p) := by
          rwa [dist_comm]
        have hpShift' : dist (refinedStoppingCenter p)
              (cubeCenter (refinedStoppingFailureCube p)) ≤
            3 / 2 * cubeScaleFactor (refinedStoppingFailureCube p) := by
          rwa [dist_comm]
        dsimp only [sq, sp] at hqShift hpShift hqx hpx hpx' hpShift' ⊢
        linarith
  unfold StoppingCubesNear
  dsimp only [sq, sp] at hpath
  calc
    dist (cubeCenter (refinedStoppingFailureCube q))
        (cubeCenter (refinedStoppingFailureCube p)) ≤
        (3 / 2 * cubeScaleFactor (refinedStoppingFailureCube q) +
          1 / 2 * cubeScaleFactor (refinedStoppingFailureCube q)) +
        (1 / 2 * cubeScaleFactor (refinedStoppingFailureCube p) +
          3 / 2 * cubeScaleFactor (refinedStoppingFailureCube p)) := hpath
    _ ≤ 10 * max (cubeScaleFactor (refinedStoppingFailureCube q))
        (cubeScaleFactor (refinedStoppingFailureCube p)) := by
      have hq := le_max_left
        (cubeScaleFactor (refinedStoppingFailureCube q))
        (cubeScaleFactor (refinedStoppingFailureCube p))
      have hp := le_max_right
        (cubeScaleFactor (refinedStoppingFailureCube q))
        (cubeScaleFactor (refinedStoppingFailureCube p))
      have hmax : 0 ≤ max (cubeScaleFactor (refinedStoppingFailureCube q))
          (cubeScaleFactor (refinedStoppingFailureCube p)) :=
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) _).le.trans hq
      linarith

/-- Hence intersecting refined cells have parent scales within two. -/
theorem abs_failureCube_scale_sub_le_two_of_refined_inter [NeZero d]
    {failure : TriadicCube d → Set Omega} {omega : Omega}
    {q p : RefinedStoppingCell failure omega base}
    (hinter :
      (translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q) ∩
        translatedCube d (refinedStoppingScale p) (refinedStoppingCenter p)).Nonempty) :
    |(refinedStoppingFailureCube q).scale -
      (refinedStoppingFailureCube p).scale| ≤ 2 :=
  abs_scale_sub_le_two_of_repairedStoppingCube_near failure omega
    (stoppingCubesNear_of_refinedStoppingCell_inter_nonempty hinter)

/-- A point in the centered threefold enlargement lies within three
half-sides of the refined center. -/
theorem dist_refinedStoppingCenter_lt_of_mem_enlargement
    {failure : TriadicCube d → Set Omega} {omega : Omega}
    {q : RefinedStoppingCell failure omega base} {x : Vec d}
    (hx : x ∈ translatedCube d (refinedStoppingScale q + 1)
      (refinedStoppingCenter q)) :
    dist (refinedStoppingCenter q) x <
      (3 / 2 : ℝ) * cubeScaleFactor (refinedStoppingFailureCube q) := by
  rw [translatedCube_eq_metricBall, Metric.mem_ball] at hx
  rw [dist_comm] at hx
  calc
    dist (refinedStoppingCenter q) x <
        1 / 2 * (3 : ℝ) ^ (refinedStoppingScale q + 1) := hx
    _ = 3 / 2 * cubeScaleFactor (refinedStoppingFailureCube q) := by
      rw [refinedStoppingScale_eq_failureCube, zpow_add₀
        (show (3 : ℝ) ≠ 0 by norm_num), zpow_one, cubeScaleFactor]
      ring

/-- Two refined cells whose centered threefold enlargements meet have near
selected parent cubes. -/
theorem stoppingCubesNear_of_refinedStoppingCell_enlargements_inter_nonempty
    {failure : TriadicCube d → Set Omega} {omega : Omega}
    {q p : RefinedStoppingCell failure omega base}
    (hinter :
      (translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q) ∩
        translatedCube d (refinedStoppingScale p + 1)
          (refinedStoppingCenter p)).Nonempty) :
    StoppingCubesNear (refinedStoppingFailureCube q)
      (refinedStoppingFailureCube p) := by
  obtain ⟨x, hxq, hxp⟩ := hinter
  set sq := cubeScaleFactor (refinedStoppingFailureCube q) with hsq
  set sp := cubeScaleFactor (refinedStoppingFailureCube p) with hsp
  have hqShift := dist_cubeCenter_refinedStoppingCenter_le q
  have hpShift := dist_cubeCenter_refinedStoppingCenter_le p
  have hqx := (dist_refinedStoppingCenter_lt_of_mem_enlargement hxq).le
  have hpx := (dist_refinedStoppingCenter_lt_of_mem_enlargement hxp).le
  have hpx' : dist x (refinedStoppingCenter p) ≤ 3 / 2 * sp := by
    rwa [dist_comm] at hpx
  have hpShift' : dist (refinedStoppingCenter p)
      (cubeCenter (refinedStoppingFailureCube p)) ≤ 3 / 2 * sp := by
    rwa [dist_comm] at hpShift
  have hpath : dist (cubeCenter (refinedStoppingFailureCube q))
      (cubeCenter (refinedStoppingFailureCube p)) ≤
      3 / 2 * sq + 3 / 2 * sq + (3 / 2 * sp + 3 / 2 * sp) := by
    calc
      dist (cubeCenter (refinedStoppingFailureCube q))
          (cubeCenter (refinedStoppingFailureCube p)) ≤
          dist (cubeCenter (refinedStoppingFailureCube q))
              (refinedStoppingCenter q) +
            dist (refinedStoppingCenter q)
              (cubeCenter (refinedStoppingFailureCube p)) :=
        dist_triangle _ _ _
      _ ≤ dist (cubeCenter (refinedStoppingFailureCube q))
              (refinedStoppingCenter q) +
            (dist (refinedStoppingCenter q) x +
              dist x (cubeCenter (refinedStoppingFailureCube p))) := by
        gcongr
        exact dist_triangle _ _ _
      _ ≤ dist (cubeCenter (refinedStoppingFailureCube q))
              (refinedStoppingCenter q) +
            (dist (refinedStoppingCenter q) x +
              (dist x (refinedStoppingCenter p) +
                dist (refinedStoppingCenter p)
                  (cubeCenter (refinedStoppingFailureCube p)))) := by
        gcongr
        exact dist_triangle _ _ _
      _ ≤ 3 / 2 * sq + 3 / 2 * sq + (3 / 2 * sp + 3 / 2 * sp) := by
        linarith
  unfold StoppingCubesNear
  have hq := le_max_left sq sp
  have hp := le_max_right sq sp
  have hmax : 0 ≤ max sq sp :=
    (zpow_pos (show (0 : ℝ) < 3 by norm_num) _).le.trans hq
  calc
    dist (cubeCenter (refinedStoppingFailureCube q))
        (cubeCenter (refinedStoppingFailureCube p)) ≤
        3 / 2 * sq + 3 / 2 * sq + (3 / 2 * sp + 3 / 2 * sp) := hpath
    _ ≤ 10 * max sq sp := by linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
