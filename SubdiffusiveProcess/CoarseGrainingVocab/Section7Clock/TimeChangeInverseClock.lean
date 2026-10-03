module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeAdditiveClock
public import Mathlib.Data.ENNReal.Inv

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open Set
open scoped ENNReal

noncomputable section



def timeChangeInverseClock (A : ℝ → ℝ) (t : ℝ) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ t < A s}

/-- An unbounded clock crosses every finite target, so its generalized inverse
is formed from a nonempty set. -/
theorem timeChangeInverseClock_crossing_nonempty {A : ℝ → ℝ}
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < A s) (t : ℝ) :
    {s : ℝ | 0 ≤ s ∧ t < A s}.Nonempty := by
  obtain ⟨s, hs, hcross⟩ := hunbounded t
  exact ⟨s, hs, hcross⟩

/-- The inverse clock is nonnegative whenever its defining upper-level set is
nonempty. -/
theorem timeChangeInverseClock_nonneg {A : ℝ → ℝ} {t : ℝ}
    (hne : {s : ℝ | 0 ≤ s ∧ t < A s}.Nonempty) :
    0 ≤ timeChangeInverseClock A t := by
  rw [timeChangeInverseClock]
  exact le_csInf hne (fun s hs ↦ hs.1)

/-- Every admissible crossing time bounds the generalized inverse from above. -/
theorem timeChangeInverseClock_le {A : ℝ → ℝ} {t s : ℝ}
    (hs : 0 ≤ s) (hcross : t < A s) :
    timeChangeInverseClock A t ≤ s := by
  rw [timeChangeInverseClock]
  exact csInf_le ⟨0, fun q hq ↦ hq.1⟩ ⟨hs, hcross⟩

/-- For a monotone clock, every time whose clock value has not crossed the
target lies below the generalized inverse, provided a crossing exists. -/
theorem le_timeChangeInverseClock {A : ℝ → ℝ} {t r : ℝ}
    (hA : Monotone A) (hne : {s : ℝ | 0 ≤ s ∧ t < A s}.Nonempty)
    (hbefore : A r ≤ t) :
    r ≤ timeChangeInverseClock A t := by
  rw [timeChangeInverseClock]
  refine le_csInf hne ?_
  intro s hs
  by_contra hrs
  have hsr : s < r := lt_of_not_ge hrs
  exact (not_lt_of_ge hbefore) ((hs.2).trans_le (hA hsr.le))

/-- Equivalently, a nonnegative time strictly below the generalized inverse
cannot already have crossed the target. -/
theorem clock_le_of_lt_timeChangeInverseClock {A : ℝ → ℝ} {t r : ℝ}
    (hr : 0 ≤ r) (hrinv : r < timeChangeInverseClock A t) :
    A r ≤ t := by
  by_contra hcross
  have := timeChangeInverseClock_le hr (lt_of_not_ge hcross)
  exact (not_le_of_gt hrinv) this



theorem sSup_ofReal_clock_range_eq_top {A : ℝ → ℝ}
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < A s) :
    sSup (ENNReal.ofReal '' (A '' {s : ℝ | 0 ≤ s})) = ∞ := by
  rw [sSup_eq_top]
  intro q hq
  have hqne : q ≠ ∞ := ne_of_lt hq
  obtain ⟨s, hs, hAs⟩ := hunbounded q.toReal
  refine ⟨ENNReal.ofReal (A s), ⟨A s, ⟨s, hs, rfl⟩, rfl⟩, ?_⟩
  rw [← ENNReal.ofReal_toReal hqne]
  exact (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_nonneg.trans_lt hAs)).2 hAs

/-- On an infinite-lifetime path, the domain condition in the frozen terminal
clock formula imposes no further restriction. -/
theorem nonnegative_before_top :
    {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < ∞} = {s : ℝ | 0 ≤ s} := by
  ext s
  simp only [mem_setOf_eq, and_iff_left_iff_imp]
  intro _
  exact ENNReal.ofReal_lt_top

/-- Consequently, the exact frozen terminal-clock expression is infinite for
an unbounded clock and an infinite input lifetime. -/
theorem sSup_ofReal_clock_before_top_eq_top {A : ℝ → ℝ}
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < A s) :
    sSup (ENNReal.ofReal ''
      (A '' {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < ∞})) = ∞ := by
  rw [nonnegative_before_top]
  exact sSup_ofReal_clock_range_eq_top hunbounded

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
