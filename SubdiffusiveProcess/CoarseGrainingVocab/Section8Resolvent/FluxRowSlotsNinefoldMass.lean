/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsEnlargementMass

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.Frozen.Section8

noncomputable section

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-! ## 1. The ninefold enlargement is covered by the closed neighbourhood -/

omit [NeZero d] in
/-- A point in the centered ninefold enlargement lies within nine half-sides
of the refined center. -/
theorem dist_refinedStoppingCenter_lt_of_mem_ninefold
    {q : RefinedStoppingCell failure omega base} {x : Vec d}
    (hx : x ∈ translatedCube d (refinedStoppingScale q + 2)
      (refinedStoppingCenter q)) :
    dist (refinedStoppingCenter q) x <
      (9 / 2 : ℝ) * cubeScaleFactor (refinedStoppingFailureCube q) := by
  rw [translatedCube_eq_metricBall, Metric.mem_ball] at hx
  rw [dist_comm] at hx
  calc
    dist (refinedStoppingCenter q) x <
        1 / 2 * (3 : ℝ) ^ (refinedStoppingScale q + 2) := hx
    _ = 9 / 2 * cubeScaleFactor (refinedStoppingFailureCube q) := by
      rw [refinedStoppingScale_eq_failureCube,
        show ((refinedStoppingFailureCube q).scale + 2 : ℤ) =
          (refinedStoppingFailureCube q).scale + 1 + 1 from by ring,
        zpow_add₀ (show (3 : ℝ) ≠ 0 by norm_num),
        zpow_add₀ (show (3 : ℝ) ≠ 0 by norm_num), zpow_one, cubeScaleFactor]
      ring

omit [NeZero d] in
/-- A refined cell meeting another refined cell's ninefold enlargement has
near selected parent cubes: the four legs cost `6 s_q + 2 s_p ≤ 8 max`, inside
the adjacency radius `10 max`. -/
theorem stoppingCubesNear_of_refinedStoppingCell_meets_ninefold
    {q p : RefinedStoppingCell failure omega base}
    (hinter :
      (translatedCube d (refinedStoppingScale q + 2)
          (refinedStoppingCenter q) ∩
        translatedCube d (refinedStoppingScale p)
          (refinedStoppingCenter p)).Nonempty) :
    StoppingCubesNear (refinedStoppingFailureCube q)
      (refinedStoppingFailureCube p) := by
  obtain ⟨x, hxq, hxp⟩ := hinter
  have hqShift := dist_cubeCenter_refinedStoppingCenter_le q
  have hpShift := dist_cubeCenter_refinedStoppingCenter_le p
  have hqx := (dist_refinedStoppingCenter_lt_of_mem_ninefold hxq).le
  have hpx := (dist_refinedStoppingCenter_lt_of_mem hxp).le
  have hpx' : dist x (refinedStoppingCenter p) ≤
      1 / 2 * cubeScaleFactor (refinedStoppingFailureCube p) := by
    rwa [dist_comm] at hpx
  have hpShift' : dist (refinedStoppingCenter p)
        (cubeCenter (refinedStoppingFailureCube p)) ≤
      3 / 2 * cubeScaleFactor (refinedStoppingFailureCube p) := by
    rwa [dist_comm] at hpShift
  have hpath : dist (cubeCenter (refinedStoppingFailureCube q))
      (cubeCenter (refinedStoppingFailureCube p)) ≤
      (3 / 2 * cubeScaleFactor (refinedStoppingFailureCube q) +
        9 / 2 * cubeScaleFactor (refinedStoppingFailureCube q)) +
      (1 / 2 * cubeScaleFactor (refinedStoppingFailureCube p) +
        3 / 2 * cubeScaleFactor (refinedStoppingFailureCube p)) := by
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
      _ ≤ _ := by linarith
  unfold StoppingCubesNear
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

omit [NeZero d] in
/-- A distinct refined cell meeting a ninefold enlargement is adjacent in the
repaired graph. -/
theorem repairedStoppingGraph_adj_of_meets_ninefold
    {q p : RefinedStoppingCell failure omega base} (hne : q ≠ p)
    (hinter :
      (translatedCube d (refinedStoppingScale q + 2)
          (refinedStoppingCenter q) ∩
        translatedCube d (refinedStoppingScale p)
          (refinedStoppingCenter p)).Nonempty) :
    repairedStoppingGraph.Adj q p :=
  (repairedStoppingGraph_adj_iff q p).mpr
    ⟨hne, stoppingCubesNear_of_refinedStoppingCell_meets_ninefold hinter⟩

/-- **The finite closed graph neighborhood covers the centered ninefold
enlargement of a refined stopping cell.**

The one-step statement, not the two-step one that P-275 conjectured: the
adjacency radius `10 · max(side)` already absorbs the ninefold's `9/2 · s_q`
leg. -/
theorem refinedStoppingCell_ninefold_subset_iUnion_closedNeighbors
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (q : RefinedStoppingCell failure omega base) :
    translatedCube d (refinedStoppingScale q + 2)
        (refinedStoppingCenter q) ⊆
      ⋃ p ∈ repairedStoppingClosedNeighbors q,
        translatedCube d (refinedStoppingScale p) (refinedStoppingCenter p) := by
  intro x hx
  have hcover := iUnion_refinedStoppingCell_eq_univ
    failure omega hinitial hrepair
  have hxAll : x ∈ ⋃ p : RefinedStoppingCell failure omega base,
      translatedCube d (refinedStoppingScale p) (refinedStoppingCenter p) := by
    rw [hcover]
    trivial
  obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hxAll
  have hp : p ∈ repairedStoppingClosedNeighbors q := by
    by_cases hpq : p = q
    · rw [hpq]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        ((repairedStoppingGraph.mem_neighborFinset q p).mpr
          (repairedStoppingGraph_adj_of_meets_ninefold (Ne.symm hpq)
            ⟨x, hx, hxp⟩))
  exact Set.mem_iUnion₂.mpr ⟨p, hp, hxp⟩

/-! ## 2. The graph decay on the ninefold enlargement -/

/-- **The graph decay on the ninefold enlargement of a stopping cell.**

Same hypotheses, same `θ^{dist/2}` slot and the *same* dimension-only constant
`fluxRowSlotsEnlargementConstant d` as
`wholeSpaceSolution_enlargement_mass_le_repairedStoppingDecay`: the covering is
still one step, so the closed-neighbour multiplicity and the single inverse
power of the contraction factor are unchanged. -/
theorem wholeSpaceSolution_ninefold_mass_le_repairedStoppingDecay
    {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsource q →
        ∫ x in translatedCube d (refinedStoppingScale q)
            (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
          repairedStoppingContractionFactor d *
            ∫ x in translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume)
    (q : RefinedStoppingCell failure omega base) :
    ∫ x in translatedCube d (refinedStoppingScale q + 2)
        (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
      fluxRowSlotsEnlargementConstant d *
        Real.rpow (repairedStoppingPointwiseContractionFactor d ^ 2)
          ((stoppingGraphDistance repairedStoppingGraph source hsource q : ℝ)
            / 2) *
        ∫ x, f x ^ 2 ∂volume := by
  classical
  set theta : ℝ := repairedStoppingPointwiseContractionFactor d with htheta_def
  have hthetapos : 0 < theta := repairedStoppingPointwiseContractionFactor_pos
  have hthetalt : theta < 1 := repairedStoppingPointwiseContractionFactor_lt_one
  set level : RefinedStoppingCell failure omega base → ℕ :=
    stoppingGraphDistance repairedStoppingGraph source hsource with hlevel_def
  have hfEnergy : 0 ≤ ∫ x, f x ^ 2 ∂volume :=
    integral_nonneg fun x ↦ sq_nonneg (f x)
  obtain ⟨p, hp, hcov⟩ :=
    exists_mem_integral_sq_le_card_mul_of_finset_cover u.memL2_toFun
      (repairedStoppingClosedNeighbors q)
      (repairedStoppingClosedNeighbors_nonempty q)
      (fun p ↦ translatedCube d (refinedStoppingScale p)
        (refinedStoppingCenter p))
      (refinedStoppingCell_ninefold_subset_iUnion_closedNeighbors
        hinitial hrepair q)
  have hstep : level q ≤ level p + 1 := by
    rcases eq_or_adj_of_mem_repairedStoppingClosedNeighbors hp with rfl | hadj
    · omega
    · exact repairedStoppingGraphDistance_le_succ_of_adj hinitial hrepair
        source hsource hadj
  have hdecay := wholeSpaceSolution_cell_mass_le_repairedStoppingPointwiseDecay
    u hL2 hinitial hrepair source hsource hcell p
  have hmassp : 0 ≤ ∫ x in translatedCube d (refinedStoppingScale p)
      (refinedStoppingCenter p), u.toFun x ^ 2 ∂volume :=
    setIntegral_nonneg
      (isOpenBoundedConvexDomain_translatedCube (d := d)
        (refinedStoppingScale p) (refinedStoppingCenter p)).isOpen.measurableSet
      fun x _ ↦ sq_nonneg (u.toFun x)
  have hcard : ((repairedStoppingClosedNeighbors q).card : ℝ) ≤
      ((repairedStoppingDegreeBound d : ℝ) + 1) := by
    have := card_repairedStoppingClosedNeighbors_le (d := d) q
    exact_mod_cast this
  have hpow : theta ^ level p ≤ theta ^ (level q - 1) :=
    pow_le_pow_of_le_one hthetapos.le hthetalt.le (by omega)
  have hshift : theta ^ (level q - 1) ≤ theta⁻¹ * theta ^ level q := by
    rcases Nat.eq_zero_or_pos (level q) with hz | hz
    · rw [hz]
      have h1 : (1 : ℝ) ≤ theta⁻¹ := (one_le_inv₀ hthetapos).mpr hthetalt.le
      simpa using h1
    · obtain ⟨j, hj⟩ : ∃ j, level q = j + 1 := ⟨level q - 1, by omega⟩
      rw [hj]
      have : theta⁻¹ * theta ^ (j + 1) = theta ^ j := by
        field_simp [pow_succ]
        ring
      simp [this]
  have hthetaq : theta ^ level q =
      Real.rpow (theta ^ 2) ((level q : ℝ) / 2) :=
    (fluxRowRiesz_rpow_half_sq hthetapos.le (level q)).symm
  calc
    ∫ x in translatedCube d (refinedStoppingScale q + 2)
        (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume
        ≤ ((repairedStoppingClosedNeighbors q).card : ℝ) *
            ∫ x in translatedCube d (refinedStoppingScale p)
              (refinedStoppingCenter p), u.toFun x ^ 2 ∂volume := hcov
    _ ≤ ((repairedStoppingDegreeBound d : ℝ) + 1) *
            ∫ x in translatedCube d (refinedStoppingScale p)
              (refinedStoppingCenter p), u.toFun x ^ 2 ∂volume :=
          mul_le_mul_of_nonneg_right hcard hmassp
    _ ≤ ((repairedStoppingDegreeBound d : ℝ) + 1) *
            (theta ^ level p * ∫ x, f x ^ 2 ∂volume) := by
          refine mul_le_mul_of_nonneg_left hdecay ?_
          positivity
    _ ≤ ((repairedStoppingDegreeBound d : ℝ) + 1) *
            (theta⁻¹ * theta ^ level q * ∫ x, f x ^ 2 ∂volume) := by
          have hle : theta ^ level p ≤ theta⁻¹ * theta ^ level q :=
            hpow.trans hshift
          have hnn : (0 : ℝ) ≤ (repairedStoppingDegreeBound d : ℝ) + 1 := by
            positivity
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hle hfEnergy) hnn
    _ = fluxRowSlotsEnlargementConstant d *
          Real.rpow (theta ^ 2) ((level q : ℝ) / 2) *
          ∫ x, f x ^ 2 ∂volume := by
          unfold fluxRowSlotsEnlargementConstant
          rw [← hthetaq]
          ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
