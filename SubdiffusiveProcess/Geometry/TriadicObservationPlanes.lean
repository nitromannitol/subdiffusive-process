import SubdiffusiveProcess.Geometry.TriadicDescendants

/-! # The active planes inside an observation cube

Only coordinates whose observation label is central can meet a global
active midplane. Under the literal descendant map, global unresolved
labels correspond exactly to local unresolved labels for this finite set.
-/
open MeasureTheory Set TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- A descendant is central in a coordinate exactly when both parent and local labels are central. -/
theorem triadicDescendant_central_iff (N J : ℕ)
    (k : OddGridIndex d (triadicHalf N)) (l : OddGridIndex d (triadicHalf J))
    (i : Fin d) :
    (triadicDescendant N J k l i).val = triadicHalf (N + J) ↔
      (k i).val = triadicHalf N ∧ (l i).val = triadicHalf J := by
  change 3 ^ J * (k i).val + (l i).val = triadicHalf (N + J) ↔ _
  rw [triadicHalf_add N J]
  have hl : (l i).val < 3 ^ J := by simpa only [two_mul_triadicHalf_add_one] using (l i).isLt
  have hm : triadicHalf J < 3 ^ J := by
    have h := two_mul_triadicHalf_add_one J
    omega
  constructor
  · intro h
    have hq := congrArg (fun n : ℕ => n / 3 ^ J) h
    simp only [Nat.mul_add_div (show 0 < 3 ^ J by positivity),
      Nat.div_eq_of_lt hl, Nat.div_eq_of_lt hm, add_zero] at hq
    refine ⟨hq, ?_⟩
    rw [hq] at h
    exact Nat.add_left_cancel h
  · rintro ⟨hk, hl⟩
    rw [hk, hl]

/-- The original active planes which actually cut a particular observation cube. -/
def triadicObservationPlanes (N : ℕ) (I : Finset (Fin d))
    (k : OddGridIndex d (triadicHalf N)) : Finset (Fin d) :=
  I.filter (fun i => (k i).val = triadicHalf N)

/-- Membership records the original plane and the exact central observation coordinate. -/
theorem mem_triadicObservationPlanes (N : ℕ) (I : Finset (Fin d))
    (k : OddGridIndex d (triadicHalf N)) (i : Fin d) :
    i ∈ triadicObservationPlanes N I k ↔ i ∈ I ∧ (k i).val = triadicHalf N := by
  simp only [triadicObservationPlanes, Finset.mem_filter]

/-- Local active planes are a subset of the prescribed original planes. -/
theorem triadicObservationPlanes_subset (N : ℕ) (I : Finset (Fin d))
    (k : OddGridIndex d (triadicHalf N)) : triadicObservationPlanes N I k ⊆ I :=
  Finset.filter_subset _ _

/-- An observation cube is unresolved exactly when at least one original active plane cuts it. -/
theorem triadicObservationPlanes_nonempty_iff (N : ℕ) (I : Finset (Fin d))
    (k : OddGridIndex d (triadicHalf N)) :
    (triadicObservationPlanes N I k).Nonempty ↔ k ∈ oddGridUnresolved (triadicHalf N) I := by
  simp only [Finset.Nonempty, mem_triadicObservationPlanes, oddGridUnresolved,
    Finset.mem_biUnion, oddGridPlaneCells, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Global unresolved descendants are precisely the local unresolved labels for the cutting planes. -/
theorem triadicDescendant_mem_unresolved_iff (N J : ℕ) (I : Finset (Fin d))
    (k : OddGridIndex d (triadicHalf N)) (l : OddGridIndex d (triadicHalf J)) :
    triadicDescendant N J k l ∈ oddGridUnresolved (triadicHalf (N + J)) I ↔
      l ∈ oddGridUnresolved (triadicHalf J) (triadicObservationPlanes N I k) := by
  simp only [oddGridUnresolved, Finset.mem_biUnion, oddGridPlaneCells,
    Finset.mem_filter, Finset.mem_univ, true_and, triadicDescendant_central_iff,
    mem_triadicObservationPlanes]
  constructor
  · rintro ⟨i, hi, hk, hl⟩
    exact ⟨i, ⟨hi, hk⟩, hl⟩
  · rintro ⟨i, ⟨hi, hk⟩, hl⟩
    exact ⟨i, hi, hk, hl⟩

/-- Every unresolved fine label has an unresolved observation ancestor. -/
theorem triadicAncestor_mem_unresolved (N J : ℕ) (I : Finset (Fin d))
    {k : OddGridIndex d (triadicHalf (N + J))}
    (hk : k ∈ oddGridUnresolved (triadicHalf (N + J)) I) :
    triadicAncestor N J k ∈ oddGridUnresolved (triadicHalf N) I := by
  rw [← triadicDescendant_ancestor_label N J k] at hk
  have h := (triadicDescendant_mem_unresolved_iff N J I _ _).mp hk
  simp only [oddGridUnresolved, Finset.mem_biUnion, oddGridPlaneCells,
    Finset.mem_filter, Finset.mem_univ, true_and, mem_triadicObservationPlanes] at h
  obtain ⟨i, ⟨hi, hki⟩, _⟩ := h
  exact (triadicObservationPlanes_nonempty_iff N I _).mp ⟨i,
    (mem_triadicObservationPlanes N I _ i).mpr ⟨hi, hki⟩⟩

end SubdiffusiveProcess
