module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionLocalFinitenessProducer
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionHalfGridRefinement

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set Homogenization SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport

noncomputable section

variable {d : ℕ} {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- A repaired cell above the base scale has a nearby dominating candidate
whose immediate predecessor fails.  The predecessor-to-candidate scale gap is
exactly one; no unproved gap between the candidate and repaired cell is hidden
in the statement. -/
theorem exists_failure_near_dominating_candidate_of_base_lt_refined_stopping_scale
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    (q : RefinedStoppingCell failure omega base)
    (hbase : base < refinedStoppingScale q) :
    ∃ (P : StoppingBaseCube d base) (F : TriadicCube d),
      refinedStoppingScale q ≤ (triadicStoppingCandidate failure omega P).scale ∧
      omega ∈ failure F ∧
      F.scale + 1 = (triadicStoppingCandidate failure omega P).scale ∧
      dist (cubeCenter (refinedStoppingFailureCube q)) (cubeCenter F) ≤
        13 * (3 : ℝ) ^ (triadicStoppingCandidate failure omega P).scale := by
  obtain ⟨P, hscale, hdist⟩ :=
    exists_candidate_scale_le_and_dist_le_of_stoppingRepairGenerated q.1.1.2
  have hscale' : refinedStoppingScale q ≤
      (triadicStoppingCandidate failure omega P).scale := by
    exact hscale
  let D := triadicStoppingDepth failure omega P
  have hcandScale : (triadicStoppingCandidate failure omega P).scale =
      base + (D : ℤ) := by
    rw [triadicStoppingCandidate_scale]
  have hDpos : 0 < D := by
    rw [hcandScale] at hscale'
    omega
  let F := ancestorCube (D - 1) P.1
  have hfail : omega ∈ failure F := by
    exact mem_failure_ancestor_pred_triadicStoppingDepth failure (hfinite P) hDpos
  have hFscale : F.scale + 1 =
      (triadicStoppingCandidate failure omega P).scale := by
    dsimp only [F]
    rw [ancestorCube_scale, triadicStoppingCandidate_scale, P.2]
    dsimp only [D]
    omega
  have hparent : parentCube F = triadicStoppingCandidate failure omega P := by
    dsimp only [F]
    rw [triadicStoppingCandidate]
    rw [← ancestorCube_succ]
    congr 1
    omega
  have hparentDist := dist_cubeCenter_cubeCenter_parentCube_le F
  rw [hparent, hFscale] at hparentDist
  have htri : dist (cubeCenter (refinedStoppingFailureCube q)) (cubeCenter F) ≤
      dist (cubeCenter (refinedStoppingFailureCube q))
          (cubeCenter (triadicStoppingCandidate failure omega P)) +
        dist (cubeCenter (triadicStoppingCandidate failure omega P))
          (cubeCenter F) := dist_triangle _ _ _
  rw [dist_comm (cubeCenter (triadicStoppingCandidate failure omega P))
    (cubeCenter F)] at htri
  have hside : 0 < (3 : ℝ) ^
      (triadicStoppingCandidate failure omega P).scale := zpow_pos (by norm_num) _
  have hqside : 0 < (3 : ℝ) ^ (refinedStoppingFailureCube q).scale :=
    zpow_pos (by norm_num) _
  change dist (cubeCenter (refinedStoppingFailureCube q))
      (cubeCenter (triadicStoppingCandidate failure omega P)) ≤
    12 * (3 : ℝ) ^ (triadicStoppingCandidate failure omega P).scale -
      12 * (3 : ℝ) ^ (refinedStoppingFailureCube q).scale at hdist
  refine ⟨P, F, ?_, hfail, hFscale, ?_⟩
  · exact hscale'
  · linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
