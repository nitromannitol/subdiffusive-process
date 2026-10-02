import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeOccupationFormula
import MarkovProcess.Path.Shift




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory MarkovProcess Set
open SubdiffusiveProcess.Frozen.Section7
open scoped ENNReal NNReal

noncomputable section

variable {Theta : Type*} {d : ℕ} {a : Theta → State d → ℝ} {theta : Theta}

/-- The reciprocal integrand of a shifted path is the shifted integrand. -/
theorem timeChangePathIntegrand_shift (omega : ContinuousPath (State d))
    (S : NNReal) {r : ℝ} (hr : 0 ≤ r) :
    timeChangePathIntegrand a theta (ContinuousPath.shift S omega) r =
      timeChangePathIntegrand a theta omega ((S : ℝ) + r) := by
  simp only [timeChangePathIntegrand, ContinuousPath.shift_apply]
  rw [Real.toNNReal_add S.coe_nonneg hr, Real.toNNReal_coe]

/-- **The clock cocycle.**  The additive clock of a path over `[0, S + s]` is
its clock over `[0, S]` plus the clock of the shifted path over `[0, s]`. -/
theorem timeChangePathClock_shift (ha : Continuous (a theta))
    (hapos : ∀ x, 0 < a theta x) (omega : ContinuousPath (State d))
    (S : NNReal) {s : ℝ} (hs : 0 ≤ s) :
    timeChangePathClock a theta omega ((S : ℝ) + s) =
      timeChangePathClock a theta omega (S : ℝ) +
        timeChangePathClock a theta (ContinuousPath.shift S omega) s := by
  have hb : Continuous (timeChangePathIntegrand a theta omega) :=
    continuous_timeChangePathIntegrand ha hapos omega
  have hbs : Continuous (timeChangePathIntegrand a theta
      (ContinuousPath.shift S omega)) :=
    continuous_timeChangePathIntegrand ha hapos _
  rw [timeChangePathClock, timeChangePathClock, timeChangePathClock,
    timeChangeAdditiveClock_eq_integral (by positivity : (0 : ℝ) ≤ (S : ℝ) + s),
    timeChangeAdditiveClock_eq_integral S.coe_nonneg,
    timeChangeAdditiveClock_eq_integral hs]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (b := (S : ℝ)) (hb.intervalIntegrable _ _) (hb.intervalIntegrable _ _)]
  congr 1
  have hshift : ∫ r in (0 : ℝ)..s,
      timeChangePathIntegrand a theta (ContinuousPath.shift S omega) r =
      ∫ r in (0 : ℝ)..s, timeChangePathIntegrand a theta omega ((S : ℝ) + r) := by
    refine intervalIntegral.integral_congr (fun r hr ↦ ?_)
    rw [Set.uIcc_of_le hs] at hr
    exact timeChangePathIntegrand_shift omega S hr.1
  rw [hshift, intervalIntegral.integral_comp_add_left
    (timeChangePathIntegrand a theta omega) (S : ℝ), add_zero]

/-- The clock of a shifted path is again unbounded. -/
theorem timeChangePathClock_shift_unbounded (ha : Continuous (a theta))
    (hapos : ∀ x, 0 < a theta x) (omega : ContinuousPath (State d)) (S : NNReal)
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧
      B < timeChangePathClock a theta omega s) :
    ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧
      B < timeChangePathClock a theta (ContinuousPath.shift S omega) s := by
  intro B
  obtain ⟨s, hs, hBs⟩ :=
    hunbounded (B + timeChangePathClock a theta omega (S : ℝ))
  have hmono := monotone_timeChangeAdditiveClock
    (continuous_timeChangePathIntegrand ha hapos omega)
    (fun r ↦ (inv_pos.mpr (hapos _)).le)
  refine ⟨s, hs, ?_⟩
  have hle : timeChangePathClock a theta omega s ≤
      timeChangePathClock a theta omega ((S : ℝ) + s) :=
    hmono (by linarith [S.coe_nonneg])
  have hsplit := timeChangePathClock_shift ha hapos omega S hs
  linarith

/-- The inverse clock of a path at time `t`, as the nonnegative real time at
which the clock reaches `t`. -/
theorem nonnegativeClockOrderIso_symm_add (ha : Continuous (a theta))
    (hapos : ∀ x, 0 < a theta x) (omega : ContinuousPath (State d))
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧
      B < timeChangePathClock a theta omega s) (t v : NNReal) :
    (nonnegativeClockOrderIso (timeChangePathClock a theta omega)
        (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
        (timeChangePathClock_core_clauses ha hapos 0 omega).1
        (timeChangePathClock_regular ha hapos omega).2
        (timeChangePathClock_regular ha hapos omega).1 hunbounded).symm (t + v) =
      (nonnegativeClockOrderIso (timeChangePathClock a theta omega)
        (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
        (timeChangePathClock_core_clauses ha hapos 0 omega).1
        (timeChangePathClock_regular ha hapos omega).2
        (timeChangePathClock_regular ha hapos omega).1 hunbounded).symm t +
      (nonnegativeClockOrderIso
        (timeChangePathClock a theta (ContinuousPath.shift
          ((nonnegativeClockOrderIso (timeChangePathClock a theta omega)
            (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
            (timeChangePathClock_core_clauses ha hapos 0 omega).1
            (timeChangePathClock_regular ha hapos omega).2
            (timeChangePathClock_regular ha hapos omega).1 hunbounded).symm t)
          omega))
        (timeChangePathClock_core_clauses ha hapos 0 _).2.1
        (timeChangePathClock_core_clauses ha hapos 0 _).1
        (timeChangePathClock_regular ha hapos _).2
        (timeChangePathClock_regular ha hapos _).1
        (timeChangePathClock_shift_unbounded ha hapos omega _ hunbounded)).symm v := by
  set e := nonnegativeClockOrderIso (timeChangePathClock a theta omega)
    (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
    (timeChangePathClock_core_clauses ha hapos 0 omega).1
    (timeChangePathClock_regular ha hapos omega).2
    (timeChangePathClock_regular ha hapos omega).1 hunbounded with he
  set S := e.symm t with hS
  set eS := nonnegativeClockOrderIso
    (timeChangePathClock a theta (ContinuousPath.shift S omega))
    (timeChangePathClock_core_clauses ha hapos 0 _).2.1
    (timeChangePathClock_core_clauses ha hapos 0 _).1
    (timeChangePathClock_regular ha hapos _).2
    (timeChangePathClock_regular ha hapos _).1
    (timeChangePathClock_shift_unbounded ha hapos omega S hunbounded) with heS
  apply e.symm_apply_eq.2
  apply NNReal.eq
  rw [coe_nonnegativeClockOrderIso_apply]
  push_cast
  rw [timeChangePathClock_shift ha hapos omega S (eS.symm v).coe_nonneg]
  have h1 : timeChangePathClock a theta omega (S : ℝ) = (t : ℝ) := by
    have := congrArg (fun z : NNReal ↦ (z : ℝ)) (e.apply_symm_apply t)
    simpa only [he, coe_nonnegativeClockOrderIso_apply, hS] using this
  have h2 : timeChangePathClock a theta (ContinuousPath.shift S omega)
      ((eS.symm v : NNReal) : ℝ) = (v : ℝ) := by
    have := congrArg (fun z : NNReal ↦ (z : ℝ)) (eS.apply_symm_apply v)
    simpa only [heS, coe_nonnegativeClockOrderIso_apply] using this
  rw [h1, h2]

/-- **The time change intertwines the shifts.**  Shifting the time-changed
path by `t` is the time change of the input path shifted by the inverse clock
value `θ_t`. -/
theorem shift_timeChangedPath (ha : Continuous (a theta))
    (hapos : ∀ x, 0 < a theta x) (omega : ContinuousPath (State d))
    (hunbounded : ∀ B : ℝ, ∃ s : ℝ, 0 ≤ s ∧
      B < timeChangePathClock a theta omega s) (t : NNReal) :
    ContinuousPath.shift t (timeChangedPath a theta ha hapos omega hunbounded) =
      timeChangedPath a theta ha hapos
        (ContinuousPath.shift
          ((nonnegativeClockOrderIso (timeChangePathClock a theta omega)
            (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
            (timeChangePathClock_core_clauses ha hapos 0 omega).1
            (timeChangePathClock_regular ha hapos omega).2
            (timeChangePathClock_regular ha hapos omega).1 hunbounded).symm t)
          omega)
        (timeChangePathClock_shift_unbounded ha hapos omega _ hunbounded) := by
  refine ContinuousMap.ext fun v ↦ ?_
  rw [ContinuousPath.shift_apply]
  change omega _ = (ContinuousPath.shift _ omega) _
  rw [ContinuousPath.shift_apply]
  congr 1
  exact nonnegativeClockOrderIso_symm_add ha hapos omega hunbounded t v

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
