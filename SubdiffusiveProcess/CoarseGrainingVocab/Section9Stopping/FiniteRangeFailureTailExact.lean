import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.FiniteRangeFailureTail

/-!
# Exact failure-height tail event

The extended failure height is one plus the last failed level.  Its tail event is therefore
exactly the union of the failure events at all levels beyond the threshold.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

open Set

noncomputable section

variable {Omega : Type*}



theorem iUnion_failure_subset_failureHeightTail (failure : ℕ → Set Omega) (N : ℕ) :
    (⋃ h : {h : ℕ // N ≤ h}, failure h) ⊆
      {omega | (N : WithTop ℕ) < failureHeightAt failure omega} := by
  intro omega homega
  rw [mem_iUnion] at homega
  obtain ⟨h, homega⟩ := homega
  have hcontribution :
      ((h.1 + 1 : ℕ) : WithTop ℕ) ≤ failureHeightAt failure omega :=
    coe_succ_le_extendedFailureHeight homega
  have hthreshold : (N : WithTop ℕ) < ((h.1 + 1 : ℕ) : WithTop ℕ) := by
    exact_mod_cast Nat.lt_succ_of_le h.2
  exact hthreshold.trans_le hcontribution



theorem failureHeightTail_eq_iUnion (failure : ℕ → Set Omega) (N : ℕ) :
    {omega | (N : WithTop ℕ) < failureHeightAt failure omega} =
      ⋃ h : {h : ℕ // N ≤ h}, failure h := by
  apply Subset.antisymm
  · exact failureHeightTail_subset_iUnion failure N
  · exact iUnion_failure_subset_failureHeightTail failure N

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
