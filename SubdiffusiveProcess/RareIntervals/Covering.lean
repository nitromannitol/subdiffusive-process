import Mathlib

/-!
# Greedy separated subfamilies of integer intervals

Deterministic ingredient of the lemma on selection of rare intervals: if every integer `k` of a finite set `B`
carries an integer interval `[u k, v k] ∋ k`, then a subfamily of pairwise separated intervals (at distance `≥ 2`)
has total cardinality at least `|B| / 3`.
-/

namespace SubdiffusiveProcess.RareIntervals

/-- The integer intervals `[u,v]` and `[u',v']` are separated: an integer lies strictly between them. -/
def Sep (u v u' v' : ℤ) : Prop := v + 1 < u' ∨ v' + 1 < u

theorem Sep.symm {u v u' v' : ℤ} (h : Sep u v u' v') : Sep u' v' u v := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- Separated intervals are disjoint. -/
theorem Sep.disjoint {u v u' v' : ℤ} (h : Sep u v u' v') :
    Disjoint (Finset.Icc u v) (Finset.Icc u' v') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_Icc] at hx hx'
  rcases h with h | h <;> omega

/-- A nonempty interval is not separated from itself. -/
theorem not_sep_self {u v : ℤ} (h : u ≤ v) : ¬ Sep u v u v := by
  intro hs
  rcases hs with hs | hs <;> omega

/-- **Greedy retention** (paper, proof of `l.concentration.rare.intervals`): a subfamily of pairwise separated
intervals whose total cardinality is at least a third of `|B|`. -/
theorem exists_separated_subfamily (u v : ℤ → ℤ) (huv : ∀ k, u k ≤ k ∧ k ≤ v k) :
    ∀ B : Finset ℤ, ∃ T ⊆ B,
      (∀ s ∈ T, ∀ t ∈ T, s ≠ t → Sep (u s) (v s) (u t) (v t)) ∧
        (B.card : ℤ) ≤ 3 * ∑ t ∈ T, (v t - u t + 1) := by
  classical
  intro B
  induction B using Finset.strongInduction with
  | H B ih =>
    by_cases hB : B = ∅
    · exact ⟨∅, by simp, by simp, by simp [hB]⟩
    obtain ⟨k0, hk0, hmax⟩ :=
      Finset.exists_max_image B (fun k => v k - u k) (Finset.nonempty_iff_ne_empty.mpr hB)
    have hk0uv := huv k0
    set B'' : Finset ℤ := B.filter (fun k => Sep (u k0) (v k0) (u k) (v k)) with hB''
    have hk0B'' : k0 ∉ B'' := by
      intro h
      exact not_sep_self (hk0uv.1.trans hk0uv.2) (Finset.mem_filter.mp h).2
    have hsub : B'' ⊂ B := by
      refine ⟨Finset.filter_subset _ _, fun h => hk0B'' (h hk0)⟩
    obtain ⟨T'', hT''B, hT''sep, hT''card⟩ := ih B'' hsub
    have hk0T'' : k0 ∉ T'' := fun h => hk0B'' (hT''B h)
    refine ⟨insert k0 T'', ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hk0
      · exact (Finset.mem_filter.mp (hT''B hx)).1
    · intro s hs t ht hst
      rcases Finset.mem_insert.mp hs with hs0 | hs
      · rcases Finset.mem_insert.mp ht with ht0 | ht
        · exact absurd (hs0.trans ht0.symm) hst
        · rw [hs0]
          exact (Finset.mem_filter.mp (hT''B ht)).2
      · rcases Finset.mem_insert.mp ht with ht0 | ht
        · rw [ht0]
          exact (Finset.mem_filter.mp (hT''B hs)).2.symm
        · exact hT''sep s hs t ht hst
    · rw [Finset.sum_insert hk0T'']
      set B' : Finset ℤ := B.filter (fun k => ¬ Sep (u k0) (v k0) (u k) (v k)) with hB'
      have hcard : B.card = B'.card + B''.card := by
        rw [hB', hB'', add_comm]
        exact (Finset.filter_card_add_filter_neg_card_eq_card (s := B) (fun k => Sep (u k0) (v k0) (u k) (v k))).symm
      have hB'sub : B' ⊆ Finset.Icc (u k0 - (v k0 - u k0 + 1)) (v k0 + (v k0 - u k0 + 1)) := by
        intro k hk
        obtain ⟨hkB, hkns⟩ := Finset.mem_filter.mp hk
        have h1 := hmax k hkB
        have h2 := huv k
        simp only [Sep, not_or, not_lt] at hkns
        simp only [Finset.mem_Icc]
        omega
      have hB'card : (B'.card : ℤ) ≤ 3 * (v k0 - u k0 + 1) := by
        have := Finset.card_le_card hB'sub
        rw [Int.card_Icc] at this
        have h3 : ((v k0 + (v k0 - u k0 + 1) + 1 - (u k0 - (v k0 - u k0 + 1))).toNat : ℤ)
            = 3 * (v k0 - u k0 + 1) := by
          rw [Int.toNat_of_nonneg (by omega)]
          ring
        have h4 : (B'.card : ℤ) ≤ ((v k0 + (v k0 - u k0 + 1) + 1 - (u k0 - (v k0 - u k0 + 1))).toNat : ℤ) := by
          exact_mod_cast this
        omega
      have : (B.card : ℤ) = B'.card + B''.card := by exact_mod_cast hcard
      have hT := hT''card
      nlinarith [hB'card, hT]

end SubdiffusiveProcess.RareIntervals
