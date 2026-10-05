module

public import Mathlib

@[expose] public section

namespace SubdiffusiveProcess

/-- Greedy selection of disjoint original-layer windows, with the cardinality loss used in the branch estimate. -/
theorem exists_disjoint_integer_windows_card_le_twelve_sum
    {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (n : ι → ℤ) (hn : Function.Injective n)
    (h : ι → ℕ+ ) :
    ∃ s : Finset ι,
      s ⊆ t ∧
      (∀ ⦃i⦄, i ∈ s → ∀ ⦃k⦄, k ∈ s → i ≠ k →
        Disjoint
          (Finset.Icc (n i - (h i : ℤ)) (n i + 2 * (h i : ℤ)))
          (Finset.Icc (n k - (h k : ℤ)) (n k + 2 * (h k : ℤ)))) ∧
      t.card ≤ 12 * ∑ i ∈ s, (h i : ℕ) := by
  classical
  refine Finset.strongInductionOn t ?_
  intro t ih
  by_cases ht : t.card ≠ 0
  · have ht' : t.Nonempty := Finset.card_ne_zero.mp ht
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image t h ht'
    let A : ι → Finset ℤ := fun j =>
      Finset.Icc (n j - (h j : ℤ)) (n j + 2 * (h j : ℤ))
    let c : Finset ι := t.filter (fun j => ¬ Disjoint (A j) (A i))
    let v : Finset ι := t \ c
    have hAi : (A i).Nonempty := by
      refine ⟨n i, ?_⟩
      dsimp [A]
      have hi0 : (0 : ℤ) < (h i : ℤ) := by positivity
      simp only [Finset.mem_Icc]
      constructor <;> omega
    have hic : i ∈ c := by
      apply Finset.mem_filter.mpr
      refine ⟨hi, ?_⟩
      exact Finset.not_disjoint_iff.mpr ⟨n i, by
        dsimp [A]
        simp only [Finset.mem_Icc]
        have hi0 : (0 : ℤ) < (h i : ℤ) := by positivity
        constructor <;> omega, by
        dsimp [A]
        simp only [Finset.mem_Icc]
        have hi0 : (0 : ℤ) < (h i : ℤ) := by positivity
        constructor <;> omega⟩
    have hcsub : c ⊆ t := Finset.filter_subset _ _
    have hvsub : v ⊆ t := Finset.sdiff_subset
    have hiv : i ∉ v := by
      intro hiv
      exact (Finset.mem_sdiff.mp hiv).2 hic
    have hvne : v ≠ t := by
      intro heq
      exact hiv (heq ▸ hi)
    have hvproper : v ⊂ t := Finset.ssubset_iff_subset_ne.mpr ⟨hvsub, hvne⟩
    obtain ⟨s, hsv, hsdisj, hsbound⟩ := ih v hvproper
    have hdisjv : ∀ ⦃j⦄, j ∈ v → Disjoint (A j) (A i) := by
      intro j hj
      by_contra hnot
      exact (Finset.mem_sdiff.mp hj).2
        (Finset.mem_filter.mpr ⟨hvsub hj, hnot⟩)
    have hcwindow : c.image n ⊆ Finset.Icc
          (n i - 3 * (h i : ℤ)) (n i + 3 * (h i : ℤ)) := by
        intro z hz
        rw [Finset.mem_image] at hz
        obtain ⟨j, hjc, rfl⟩ := hz
        have hjt : j ∈ t := (Finset.mem_filter.mp hjc).1
        have hjnot : ¬ Disjoint (A j) (A i) := (Finset.mem_filter.mp hjc).2
        obtain ⟨x, hxj, hxi⟩ := Finset.not_disjoint_iff.mp hjnot
        have hjmax : (h j : ℤ) ≤ (h i : ℤ) := by
          have := hmax j hjt
          exact_mod_cast this
        dsimp [A] at hxj hxi
        simp only [Finset.mem_Icc] at hxj hxi
        simp only [Finset.mem_Icc]
        constructor <;> omega
    have hc : c.card ≤ 12 * (h i : ℕ) := by
        rw [← Finset.card_image_of_injective c hn]
        refine (Finset.card_le_card hcwindow).trans ?_
        rw [Int.card_Icc]
        have hi_nat : 1 ≤ (h i : ℕ) := (h i).property
        omega
    have hsi : i ∉ s := fun his => hiv (hsv his)
    refine ⟨insert i s, ?_⟩
    constructor
    · intro j hj
      simp only [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact hi
      · exact hsv.trans hvsub hj
    constructor
    · intro j hjs k hks hjk
      simp only [Finset.mem_insert] at hjs hks
      rcases hjs with rfl | hjs <;> rcases hks with rfl | hks
      · exact (hjk rfl).elim
      · simpa [A] using (hdisjv (hsv hks)).symm
      · simpa [A] using hdisjv (hsv hjs)
      · simpa [A] using hsdisj hjs hks hjk
    · have htc : t.card = c.card + v.card := by
        rw [← Finset.card_union_of_disjoint]
        · rw [Finset.union_sdiff_of_subset hcsub]
        · apply Finset.disjoint_left.mpr
          intro j hjc hjv
          exact (Finset.mem_sdiff.mp hjv).2 hjc
      rw [htc]
      calc
        c.card + v.card ≤ 12 * (h i : ℕ) + 12 * ∑ j ∈ s, (h j : ℕ) :=
          Nat.add_le_add hc hsbound
        _ = 12 * ((h i : ℕ) + ∑ j ∈ s, (h j : ℕ)) := by omega
        _ = 12 * ∑ j ∈ insert i s, (h j : ℕ) := by
          rw [Finset.sum_insert hsi]
  · have ht0 : t.card = 0 := by omega
    exact ⟨∅, Finset.empty_subset _, by simp,
      by simp [Finset.card_eq_zero.mp ht0]⟩

end SubdiffusiveProcess
