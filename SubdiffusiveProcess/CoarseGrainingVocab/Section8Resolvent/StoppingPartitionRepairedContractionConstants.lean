import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedExteriorRow




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

noncomputable section

/-- Dimension-only per-cell contraction factor for the repaired stopping
graph. -/
def repairedStoppingContractionFactor (d : ℕ) : ℝ :=
  1 / (2 * (repairedStoppingDegreeBound d : ℝ) *
    ((repairedStoppingDegreeBound d + 1 : ℕ) : ℝ))

/-- The repaired per-cell contraction factor is positive. -/
theorem repairedStoppingContractionFactor_pos {d : ℕ} :
    0 < repairedStoppingContractionFactor d := by
  have hD : 0 < (repairedStoppingDegreeBound d : ℝ) := by
    exact_mod_cast (repairedStoppingDegreeBound_pos (d := d))
  have hN : 0 < ((repairedStoppingDegreeBound d + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_pos (repairedStoppingDegreeBound d))
  unfold repairedStoppingContractionFactor
  positivity

/-- The degree, closed-neighborhood cardinality, and chosen cell contraction
combine to exactly one half. -/
theorem repairedStopping_effectiveContraction_eq_half {d : ℕ} :
    (repairedStoppingDegreeBound d : ℝ) *
      (((repairedStoppingDegreeBound d + 1 : ℕ) : ℝ) *
        repairedStoppingContractionFactor d) = 1 / 2 := by
  have hD : (repairedStoppingDegreeBound d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (repairedStoppingDegreeBound_pos (d := d)))
  have hN : ((repairedStoppingDegreeBound d + 1 : ℕ) : ℝ) ≠ 0 := by
    positivity
  unfold repairedStoppingContractionFactor
  field_simp [hD, hN]

/-- The numerical effective-contraction premise of the exterior consumer. -/
theorem repairedStopping_effectiveContraction_lt_one {d : ℕ} :
    (repairedStoppingDegreeBound d : ℝ) *
      (((repairedStoppingDegreeBound d + 1 : ℕ) : ℝ) *
        repairedStoppingContractionFactor d) < 1 := by
  rw [repairedStopping_effectiveContraction_eq_half]
  norm_num

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
