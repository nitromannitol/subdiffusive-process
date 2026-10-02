import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingCrossingNearbyFailure
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRefinedIntersection




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set Homogenization SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport

noncomputable section

variable {d : ℕ} {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- A repaired cell above the base has a failed cube at some offset `r ≥ -1`.
The constant `15` includes the half-grid displacement, while the scale in the
bound is exactly one above the failed cube's scale. -/
theorem exists_failure_at_one_sided_offset_refinedStoppingCell
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    (q : RefinedStoppingCell failure omega base)
    (hbase : base < refinedStoppingScale q) :
    ∃ (r : ℤ) (F : TriadicCube d),
      -1 ≤ r ∧ F.scale = refinedStoppingScale q + r ∧ omega ∈ failure F ∧
      dist (refinedStoppingCenter q) (cubeCenter F) ≤
        15 * (3 : ℝ) ^ (refinedStoppingScale q + r + 1) := by
  obtain ⟨P, F, hscale, hfail, hFscale, hdist⟩ :=
    exists_failure_near_dominating_candidate_of_base_lt_refined_stopping_scale
      hfinite q hbase
  let r : ℤ := F.scale - refinedStoppingScale q
  have hr : -1 ≤ r := by
    dsimp only [r]
    omega
  have hrscale : F.scale = refinedStoppingScale q + r := by
    dsimp only [r]
    omega
  have hexponent : refinedStoppingScale q + r + 1 =
      (triadicStoppingCandidate failure omega P).scale := by
    rw [← hFscale, hrscale]
  have hshift := dist_cubeCenter_refinedStoppingCenter_le q
  rw [dist_comm] at hshift
  have hpow : (3 : ℝ) ^ refinedStoppingScale q ≤
      (3 : ℝ) ^ (triadicStoppingCandidate failure omega P).scale := by
    exact zpow_le_zpow_right₀ (by norm_num) hscale
  have htri : dist (refinedStoppingCenter q) (cubeCenter F) ≤
      dist (refinedStoppingCenter q)
          (cubeCenter (refinedStoppingFailureCube q)) +
        dist (cubeCenter (refinedStoppingFailureCube q)) (cubeCenter F) :=
    dist_triangle _ _ _
  have hpos : 0 < (3 : ℝ) ^
      (triadicStoppingCandidate failure omega P).scale := zpow_pos (by norm_num) _
  change dist (refinedStoppingCenter q)
      (cubeCenter (refinedStoppingFailureCube q)) ≤
    3 / 2 * (3 : ℝ) ^ refinedStoppingScale q at hshift
  refine ⟨r, F, hr, hrscale, hfail, ?_⟩
  rw [hexponent]
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
