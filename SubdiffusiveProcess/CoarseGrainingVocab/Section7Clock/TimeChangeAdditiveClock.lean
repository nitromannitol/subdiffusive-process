module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory Set

noncomputable section



def timeChangeAdditiveClock (b : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..max s 0, b r

@[simp]
theorem timeChangeAdditiveClock_zero (b : ℝ → ℝ) :
    timeChangeAdditiveClock b 0 = 0 := by
  simp [timeChangeAdditiveClock]

/-- On nonnegative time, the extended clock is exactly the manuscript clock. -/
theorem timeChangeAdditiveClock_eq_integral {b : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s) :
    timeChangeAdditiveClock b s = ∫ r in (0 : ℝ)..s, b r := by
  simp [timeChangeAdditiveClock, max_eq_left hs]

/-- The increment of the clock is the integral over the intervening interval. -/
theorem timeChangeAdditiveClock_add_increment {b : ℝ → ℝ}
    (hb : Continuous b) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    timeChangeAdditiveClock b s + ∫ r in s..t, b r = timeChangeAdditiveClock b t := by
  rw [timeChangeAdditiveClock_eq_integral hs,
    timeChangeAdditiveClock_eq_integral (hs.trans hst)]
  exact intervalIntegral.integral_add_adjacent_intervals
    (hb.intervalIntegrable 0 s) (hb.intervalIntegrable s t)

/-- A continuous nonnegative integrand gives a globally monotone clock. -/
theorem monotone_timeChangeAdditiveClock {b : ℝ → ℝ}
    (hb : Continuous b) (hbnonneg : ∀ r, 0 ≤ b r) :
    Monotone (timeChangeAdditiveClock b) := by
  intro s t hst
  have hmax : max s 0 ≤ max t 0 := max_le_max_right 0 hst
  have hincrement : 0 ≤ ∫ r in max s 0..max t 0, b r :=
    intervalIntegral.integral_nonneg_of_forall hmax hbnonneg
  calc
    timeChangeAdditiveClock b s
        ≤ timeChangeAdditiveClock b s + ∫ r in max s 0..max t 0, b r :=
      le_add_of_nonneg_right hincrement
    _ = timeChangeAdditiveClock b t := by
      exact intervalIntegral.integral_add_adjacent_intervals
        (hb.intervalIntegrable 0 (max s 0))
        (hb.intervalIntegrable (max s 0) (max t 0))

/-- A continuous positive integrand makes the clock strictly increasing on
the nonnegative half-line. -/
theorem strictMonoOn_timeChangeAdditiveClock {b : ℝ → ℝ}
    (hb : Continuous b) (hbpos : ∀ r, 0 < b r) :
    StrictMonoOn (timeChangeAdditiveClock b) (Ici 0) := by
  intro s hs t ht hst
  have hincrement : 0 < ∫ r in s..t, b r := by
    refine intervalIntegral.integral_pos hst hb.continuousOn ?_ ?_
    · intro r _
      exact (hbpos r).le
    · exact ⟨s, left_mem_Icc.mpr hst.le, hbpos s⟩
  rw [← timeChangeAdditiveClock_add_increment hb hs hst.le]
  exact lt_add_of_pos_right _ hincrement

/-- The extended additive clock is continuous. -/
theorem continuous_timeChangeAdditiveClock {b : ℝ → ℝ} (hb : Continuous b) :
    Continuous (timeChangeAdditiveClock b) := by
  have hprimitive : Continuous (fun s : ℝ ↦ ∫ r in (0 : ℝ)..s, b r) :=
    intervalIntegral.continuous_primitive
      (fun s t ↦ hb.intervalIntegrable s t) 0
  exact hprimitive.comp (continuous_id.max continuous_const)

/-- If the positive-time integrand has a positive deterministic lower bound,
then the additive clock is unbounded above.  The probabilistic time-change
application needs an almost-sure analogue of this conclusion. -/
theorem timeChangeAdditiveClock_unbounded_of_lower_bound {b : ℝ → ℝ} {c : ℝ}
    (hb : Continuous b) (hc : 0 < c) (hlower : ∀ r, 0 ≤ r → c ≤ b r) :
    ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧ B < timeChangeAdditiveClock b s := by
  intro B
  let s := max 0 ((B + 1) / c)
  have hs : 0 ≤ s := le_max_left _ _
  have hcs : B < c * s := by
    have hcB : B < B + 1 := by linarith
    have hquot : (B + 1) / c ≤ s := le_max_right _ _
    calc
      B < B + 1 := hcB
      _ = c * ((B + 1) / c) := by field_simp
      _ ≤ c * s := mul_le_mul_of_nonneg_left hquot hc.le
  have hintegral : c * s ≤ ∫ r in (0 : ℝ)..s, b r := by
    have hconst : ∫ _r in (0 : ℝ)..s, c = c * s := by simp [mul_comm]
    rw [← hconst]
    exact intervalIntegral.integral_mono_on hs
      (continuous_const.intervalIntegrable 0 s) (hb.intervalIntegrable 0 s)
      (fun r hr ↦ hlower r hr.1)
  exact ⟨s, hs, hcs.trans_le (by
    rw [timeChangeAdditiveClock_eq_integral hs]
    exact hintegral)⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
