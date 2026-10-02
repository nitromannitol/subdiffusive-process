import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionHalfGridRefinement




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization

noncomputable section

variable {d : ℕ} {Omega : Type*} {base : ℤ}
variable {failure : TriadicCube d → Set Omega} {omega : Omega}

/-- Every refined stopping cell is at least as coarse as the base scale. -/
theorem base_le_refinedStoppingScale
    (q : RefinedStoppingCell failure omega base) :
    base ≤ refinedStoppingScale q :=
  base_le_scale_of_stoppingRepairGenerated q.1.1.2



theorem le_three_pow_refinedStoppingScale_of_le_three_pow_base {R : ℝ}
    (hR : R ≤ (3 : ℝ) ^ base) (q : RefinedStoppingCell failure omega base) :
    R ≤ (3 : ℝ) ^ refinedStoppingScale q :=
  hR.trans (zpow_le_zpow_right₀ (by norm_num) (base_le_refinedStoppingScale q))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
