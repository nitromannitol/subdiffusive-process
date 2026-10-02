import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionLocalFinitenessProducer
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingCrossingPerCellFailure




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Omega : Type*} {base : ℤ}

/-! ## 1. The failure event of one scale near a ball of free radius -/

/-- Some triadic cube of scale `base + i` meeting the ball of radius
`rho + 64 * 3 ^ (base + i)` about `x0` fails.  The scale-proportional
enlargement of the radius is what lets the one-sided per-cell law feed this
family. -/
def stoppingBallFailureEvent (failure : TriadicCube d → Set Omega) (base : ℤ)
    (x0 : Vec d) (rho : ℝ) (i : ℕ) : Set Omega :=
  ⋃ P ∈ triadicScaleBallFinset d (base + (i : ℤ)) x0
      (rho + 64 * (3 : ℝ) ^ (base + (i : ℤ))), failure P

theorem mem_stoppingBallFailureEvent_of_mem_failure
    {failure : TriadicCube d → Set Omega} {omega : Omega} {x0 : Vec d}
    {rho : ℝ} {i : ℕ} {P : TriadicCube d}
    (hscale : P.scale = base + (i : ℤ))
    (hmeet : (cubeSet P ∩
      Metric.closedBall x0 (rho + 64 * (3 : ℝ) ^ (base + (i : ℤ)))).Nonempty)
    (hfail : omega ∈ failure P) :
    omega ∈ stoppingBallFailureEvent failure base x0 rho i :=
  Set.mem_biUnion (mem_triadicScaleBallFinset.mpr ⟨hscale, hmeet⟩) hfail

/-- The tail of the family over all scales at least `base + j`. -/
def stoppingBallFailureTailEvent (failure : TriadicCube d → Set Omega)
    (base : ℤ) (x0 : Vec d) (rho : ℝ) (j : ℕ) : Set Omega :=
  ⋃ i : ℕ, stoppingBallFailureEvent failure base x0 rho (j + i)

theorem mem_stoppingBallFailureTailEvent_of_le
    {failure : TriadicCube d → Set Omega} {omega : Omega} {x0 : Vec d}
    {rho : ℝ} {i j : ℕ} (hij : j ≤ i)
    (hmem : omega ∈ stoppingBallFailureEvent failure base x0 rho i) :
    omega ∈ stoppingBallFailureTailEvent failure base x0 rho j := by
  refine Set.mem_iUnion.mpr ⟨i - j, ?_⟩
  rwa [Nat.add_sub_cancel' hij]

/-! ## 2. The measure bound -/

variable [MeasurableSpace Omega]

/-- The one-scale event near a ball of radius `rho` has measure at most the
dimension-and-`rho`-only cube count times the geometric failure bound. -/
theorem measure_stoppingBallFailureEvent_le
    (mu : Measure Omega) (failure : TriadicCube d → Set Omega)
    (C q : ENNReal)
    (hmeasure : ∀ (P : TriadicCube d) (n : ℕ), P.scale = base + (n : ℤ) →
      mu (failure P) ≤ C * q ^ n)
    (x0 : Vec d) (rho : ℝ) (hrho : 0 ≤ rho) (i : ℕ) :
    mu (stoppingBallFailureEvent failure base x0 rho i) ≤
      ((2 * ⌈(rho + ‖x0‖) / (3 : ℝ) ^ base⌉₊ + 131) ^ d : ℕ) * (C * q ^ i) := by
  set s : ℤ := base + (i : ℤ) with hs
  set radius : ℝ := rho + 64 * (3 : ℝ) ^ s with hradius
  have hnorm : (0 : ℝ) ≤ ‖x0‖ := norm_nonneg x0
  have hstep : mu (stoppingBallFailureEvent failure base x0 rho i)
      ≤ ((triadicScaleBallFinset d s x0 radius).card : ℕ) • (C * q ^ i) := by
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    refine Finset.sum_le_card_nsmul _ _ _ ?_
    intro P hP
    exact hmeasure P i (mem_triadicScaleBallFinset.mp hP).1
  have hpow : (0 : ℝ) < (3 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hbasepos : (0 : ℝ) < (3 : ℝ) ^ base := zpow_pos (by norm_num) _
  have hkey : (radius + ‖x0‖) / (3 : ℝ) ^ s
      = (rho + ‖x0‖) / (3 : ℝ) ^ s + (64 : ℕ) := by
    rw [hradius]
    field_simp
    ring
  have hcard : (triadicScaleBallFinset d s x0 radius).card
      ≤ (2 * ⌈(rho + ‖x0‖) / (3 : ℝ) ^ base⌉₊ + 131) ^ d := by
    refine le_trans (card_triadicScaleBallFinset_le s x0 radius) ?_
    have hle : (rho + ‖x0‖) / (3 : ℝ) ^ s ≤ (rho + ‖x0‖) / (3 : ℝ) ^ base :=
      div_le_div_of_nonneg_left (by linarith) hbasepos
        (zpow_le_zpow_right₀ (by norm_num) (by omega : base ≤ s))
    have h1 : ⌈(radius + ‖x0‖) / (3 : ℝ) ^ s⌉₊
        ≤ ⌈(rho + ‖x0‖) / (3 : ℝ) ^ base⌉₊ + 64 := by
      rw [hkey, Nat.ceil_add_natCast
        (by positivity : (0 : ℝ) ≤ (rho + ‖x0‖) / (3 : ℝ) ^ s)]
      exact Nat.add_le_add_right (Nat.ceil_le_ceil hle) 64
    refine Nat.pow_le_pow_left ?_ d
    omega
  rw [nsmul_eq_mul] at hstep
  refine le_trans hstep ?_
  gcongr

/-- **The geometric tail bound.**  Summing the one-scale bound over the scales
at least `base + j` costs only the factor `(1 - q)⁻¹`: the cube count is taken
uniform in the scale. -/
theorem measure_stoppingBallFailureTailEvent_le
    (mu : Measure Omega) (failure : TriadicCube d → Set Omega)
    (C q : ENNReal)
    (hmeasure : ∀ (P : TriadicCube d) (n : ℕ), P.scale = base + (n : ℤ) →
      mu (failure P) ≤ C * q ^ n)
    (x0 : Vec d) (rho : ℝ) (hrho : 0 ≤ rho) (j : ℕ) :
    mu (stoppingBallFailureTailEvent failure base x0 rho j) ≤
      ((2 * ⌈(rho + ‖x0‖) / (3 : ℝ) ^ base⌉₊ + 131) ^ d : ℕ) *
        (C * q ^ j) * (1 - q)⁻¹ := by
  set K : ENNReal :=
    (((2 * ⌈(rho + ‖x0‖) / (3 : ℝ) ^ base⌉₊ + 131) ^ d : ℕ) : ENNReal) with hK
  calc mu (stoppingBallFailureTailEvent failure base x0 rho j)
      ≤ ∑' i : ℕ, mu (stoppingBallFailureEvent failure base x0 rho (j + i)) :=
        measure_iUnion_le _
    _ ≤ ∑' i : ℕ, K * (C * q ^ (j + i)) :=
        ENNReal.tsum_le_tsum fun i ↦
          measure_stoppingBallFailureEvent_le mu failure C q hmeasure x0 rho
            hrho (j + i)
    _ = K * (C * q ^ j) * (1 - q)⁻¹ := by
        have hterm : ∀ i : ℕ, K * (C * q ^ (j + i)) = K * (C * q ^ j) * q ^ i := by
          intro i
          rw [pow_add]
          ring
        rw [tsum_congr hterm, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-! ## 3. The one-sided per-cell law feeds the tail event -/

omit [MeasurableSpace Omega] in
/-- **Every large repaired cell near the ball lies in the failure tail.**

A refined repaired cell of scale above `base + j` whose centre is within
`rho + 6 * 3 ^ (scale)` of `x0` forces, by the one-sided per-cell law, a failed
cube of some scale `base + i` with `i ≥ j` meeting the ball of radius
`rho + 64 * 3 ^ (base + i)`.  The slack `6` in the hypothesis covers both the
cells that meet the ball itself and the source cells, whose *enlargements*
meet the ball of radius `R`. -/
theorem mem_stoppingBallFailureTailEvent_of_refinedStoppingCell
    {failure : TriadicCube d → Set Omega} {omega : Omega}
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    (x0 : Vec d) (rho : ℝ) (j : ℕ)
    (cell : RefinedStoppingCell failure omega base)
    (hscale : base + (j : ℤ) + 1 ≤ refinedStoppingScale cell)
    (hnear : dist (refinedStoppingCenter cell) x0 ≤
      rho + 6 * (3 : ℝ) ^ refinedStoppingScale cell) :
    omega ∈ stoppingBallFailureTailEvent failure base x0 rho j := by
  set s : ℤ := refinedStoppingScale cell with hsdef
  obtain ⟨r, F, hr, hFscale, hfail, hdist⟩ :=
    exists_failure_at_one_sided_offset_refinedStoppingCell hfinite cell
      (by omega)
  have hij : base + (j : ℤ) ≤ s + r := by omega
  set i : ℕ := (s + r - base).toNat with hi
  have hiZ : (i : ℤ) = s + r - base := Int.toNat_of_nonneg (by omega)
  have hji : j ≤ i := by omega
  have hFbase : F.scale = base + (i : ℤ) := by omega
  have hsle : s ≤ base + (i : ℤ) + 1 := by omega
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (base + (i : ℤ)) := zpow_pos (by norm_num) _
  have hexp1 : (3 : ℝ) ^ (s + r + 1) = 3 * (3 : ℝ) ^ (base + (i : ℤ)) := by
    rw [show s + r + 1 = (base + (i : ℤ)) + 1 by omega,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hexp2 : (3 : ℝ) ^ s ≤ 3 * (3 : ℝ) ^ (base + (i : ℤ)) := by
    have hstep : (3 : ℝ) ^ s ≤ (3 : ℝ) ^ ((base + (i : ℤ)) + 1) :=
      zpow_le_zpow_right₀ (by norm_num) hsle
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)] at hstep
    nlinarith [hstep]
  have htri : dist (cubeCenter F) x0 ≤
      dist (cubeCenter F) (refinedStoppingCenter cell) +
        dist (refinedStoppingCenter cell) x0 := dist_triangle _ _ _
  rw [dist_comm (cubeCenter F) (refinedStoppingCenter cell)] at htri
  rw [hexp1] at hdist
  have hfinal : dist (cubeCenter F) x0 ≤
      rho + 64 * (3 : ℝ) ^ (base + (i : ℤ)) := by
    nlinarith [htri, hdist, hnear, hexp2, hpow]
  refine mem_stoppingBallFailureTailEvent_of_le hji ?_
  refine mem_stoppingBallFailureEvent_of_mem_failure hFbase ?_ hfail
  exact ⟨cubeCenter F, cubeCenter_mem_cubeSet F, Metric.mem_closedBall.mpr hfinal⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
