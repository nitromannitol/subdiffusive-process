module

public import SubdiffusiveProcess.Geometry.IntegerWindowPacking

@[expose] public section

namespace SubdiffusiveProcess

/-- Many failures admit a disjoint optional-witness selection with the radius mass required by the branch bound. -/
theorem exists_optional_disjoint_witnesses_of_many_failures
    {Ω : Type*} (J : ℕ) (θ : ℝ)
    (n : Fin J → ℤ) (hn : Function.Injective n)
    (failure : Fin J → Set Ω) (W : Fin J → ℕ+ → Set Ω)
    (hfailure : ∀ i : Fin J, failure i ⊆ ⋃ h : ℕ+, W i h)
    (ω : Ω)
    (hbad : θ * (J : ℝ) ≤ (Set.ncard {i : Fin J | ω ∈ failure i} : ℝ)) :
    ∃ w : Fin J → Option ℕ+,
      (∀ (i : Fin J) (h : ℕ+), w i = some h → ω ∈ W i h) ∧
      (∀ (i k : Fin J) (hi hk : ℕ+), i ≠ k →
        w i = some hi → w k = some hk →
        Disjoint
          (Finset.Icc (n i - (hi : ℤ)) (n i + 2 * (hi : ℤ)))
          (Finset.Icc (n k - (hk : ℤ)) (n k + 2 * (hk : ℤ)))) ∧
      θ * (J : ℝ) ≤ 12 *
        ((∑ i : Fin J, (w i).elim (0 : ℕ) (fun h => (h : ℕ))) : ℝ) := by
  classical
  let bad : Set (Fin J) := {i | ω ∈ failure i}
  let t : Finset (Fin J) := (Set.toFinite bad).toFinset
  have hmem : ∀ i : Fin J, i ∈ t ↔ i ∈ bad := by
    intro i
    simp [t, bad]
  have hcard : Set.ncard bad = t.card := by
    rw [Set.ncard_eq_toFinset_card bad (Set.toFinite bad)]
  have hbad' : θ * (J : ℝ) ≤ (t.card : ℝ) := by
    change θ * (J : ℝ) ≤ (Set.ncard bad : ℝ) at hbad
    rw [hcard] at hbad
    exact hbad
  have hcover : ∀ i : Fin J, i ∈ t → ∃ h : ℕ+, ω ∈ W i h := by
    intro i hi
    have hfi : ω ∈ failure i := (hmem i).mp hi
    rcases Set.mem_iUnion.mp (hfailure i hfi) with ⟨h, hh⟩
    exact ⟨h, hh⟩
  let q : Fin J → ℕ+ := fun i =>
    if hi : i ∈ t then Classical.choose (hcover i hi) else 1
  have hq : ∀ i : Fin J, i ∈ t → ω ∈ W i (q i) := by
    intro i hi
    dsimp [q]
    rw [dite_eq_left hi]
    exact Classical.choose_spec (hcover i hi)
  obtain ⟨s, hst, hsdisj, hbound⟩ :=
    exists_disjoint_integer_windows_card_le_twelve_sum t n hn q
  let w : Fin J → Option ℕ+ := fun i => if i ∈ s then some (q i) else none
  refine ⟨w, ?_, ?_, ?_⟩
  · intro i h hiw
    by_cases his : i ∈ s
    · have hqi : q i = h := by simpa [w, his] using hiw
      rw [← hqi]
      exact hq i (hst his)
    · simp [w, his] at hiw
  · intro i k hi hk hne hwi hwk
    by_cases his : i ∈ s
    · by_cases hks : k ∈ s
      · have hqi : q i = hi := by simpa [w, his] using hwi
        have hqk : q k = hk := by simpa [w, hks] using hwk
        simpa [hqi, hqk] using hsdisj his hks hne
      · simp [w, hks] at hwk
    · simp [w, his] at hwi
  · have hsum :
        (∑ i : Fin J, (w i).elim (0 : ℝ) (fun h => (h : ℝ))) =
          ∑ i ∈ s, (q i : ℝ) := by
      have hw : ∀ i : Fin J,
          (w i).elim (0 : ℝ) (fun h => (h : ℝ)) =
            if i ∈ s then (q i : ℝ) else 0 := by
        intro i
        by_cases hi : i ∈ s <;> simp [w, hi]
      calc
        (∑ i : Fin J, (w i).elim (0 : ℝ) (fun h => (h : ℝ))) =
            ∑ i : Fin J, if i ∈ s then (q i : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hw i
        _ = ∑ i ∈ s, (q i : ℝ) := by
          rw [← Finset.sum_filter]
          simp
    have hboundR : (t.card : ℝ) ≤ (12 : ℝ) * ∑ i ∈ s, (q i : ℝ) := by
      exact_mod_cast hbound
    have hfinal : θ * (J : ℝ) ≤
        12 * (∑ i : Fin J, (w i).elim (0 : ℝ) (fun h => (h : ℝ))) := by
      rw [hsum]
      exact hbad'.trans hboundR
    simpa using hfinal

end SubdiffusiveProcess
