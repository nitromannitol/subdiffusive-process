module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeProcessOccupation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeStoppingTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeClockDivergence

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.Frozen.Section7
open scoped ENNReal NNReal

noncomputable section

variable {Theta : Type*} {d : ℕ} {a : Theta → State d → ℝ} {theta : Theta}

/-! ### Two-sided clock bounds -/

/-- **The clock grows at least linearly** when the coefficient is bounded
above. -/
theorem timeChangePathClock_lower_bound
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (omega : ContinuousPath (State d)) {C : ℝ} (hC : 0 < C)
    (hb : ∀ x, a theta x ≤ C) {s : ℝ} (hs : 0 ≤ s) :
    s / C ≤ timeChangePathClock a theta omega s := by
  rw [timeChangePathClock, timeChangeAdditiveClock_eq_integral hs]
  have hmono : (∫ _r in (0 : ℝ)..s, C⁻¹) ≤
      ∫ r in (0 : ℝ)..s, timeChangePathIntegrand a theta omega r := by
    refine intervalIntegral.integral_mono_on hs
      (continuous_const.intervalIntegrable _ _)
      ((continuous_timeChangePathIntegrand ha hapos omega).intervalIntegrable _ _)
      fun r _ ↦ ?_
    exact (inv_le_inv₀ hC (hapos _)).mpr (hb _)
  have hconst : (∫ _r in (0 : ℝ)..s, C⁻¹) = s / C := by
    simp [div_eq_mul_inv]
  rwa [hconst] at hmono

/-! ### The inverse clock is a bounded stopping time -/

/-- The deterministic horizon bounding the inverse clock. -/
def clockHorizon (C : ℝ) (t : NNReal) : NNReal := Real.toNNReal (C * ((t : ℝ) + 1))

theorem coe_clockHorizon {C : ℝ} (hC : 0 < C) (t : NNReal) :
    ((clockHorizon C t : NNReal) : ℝ) = C * ((t : ℝ) + 1) := by
  rw [clockHorizon, Real.coe_toNNReal]
  positivity

/-- **The inverse clock is bounded by a deterministic horizon.** -/
theorem timeChangeRationalInverse_le_clockHorizon
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    {C : ℝ} (hC : 0 < C) (hb : ∀ x, a theta x ≤ C)
    (t : NNReal) (omega : ContinuousPath (State d)) :
    timeChangeRationalInverse a theta t omega ≤ ((clockHorizon C t : NNReal) : ℝ≥0∞) := by
  refine (timeChangeRationalInverse_le_iff ha hapos t _ omega).mpr ?_
  rw [coe_clockHorizon hC t]
  have hlow := timeChangePathClock_lower_bound ha hapos omega hC hb
    (s := C * ((t : ℝ) + 1)) (by positivity)
  refine le_trans ?_ hlow
  rw [mul_comm, mul_div_assoc, div_self (ne_of_gt hC), mul_one]
  linarith

theorem timeChangeRationalInverse_ne_top
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    {C : ℝ} (hC : 0 < C) (hb : ∀ x, a theta x ≤ C)
    (t : NNReal) (omega : ContinuousPath (State d)) :
    timeChangeRationalInverse a theta t omega ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top
    (timeChangeRationalInverse_le_clockHorizon ha hapos hC hb t omega)

theorem coe_timeChangeRationalInverseNNReal
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    {C : ℝ} (hC : 0 < C) (hb : ∀ x, a theta x ≤ C)
    (t : NNReal) (omega : ContinuousPath (State d)) :
    ((timeChangeRationalInverseNNReal a theta t omega : NNReal) : ℝ≥0∞) =
      timeChangeRationalInverse a theta t omega :=
  ENNReal.coe_toNNReal (timeChangeRationalInverse_ne_top ha hapos hC hb t omega)

theorem timeChangeRationalInverseNNReal_le_clockHorizon
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    {C : ℝ} (hC : 0 < C) (hb : ∀ x, a theta x ≤ C)
    (t : NNReal) (omega : ContinuousPath (State d)) :
    timeChangeRationalInverseNNReal a theta t omega ≤ clockHorizon C t := by
  have h := timeChangeRationalInverse_le_clockHorizon ha hapos hC hb t omega
  rw [← coe_timeChangeRationalInverseNNReal ha hapos hC hb t omega] at h
  exact_mod_cast h

/-- **The inverse clock is a stopping time**, in the finite `NNReal`-valued
form the library's optional stopping consumes. -/
theorem isStoppingTime_timeChangeRationalInverseNNReal
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    {C : ℝ} (hC : 0 < C) (hb : ∀ x, a theta x ≤ C)
    (default : ContinuousPath (State d)) (t : NNReal) :
    IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := State d))
      (fun omega ↦ ((timeChangeRationalInverseNNReal a theta t omega : NNReal) :
        WithTop NNReal)) := by
  have hfun : (fun omega : ContinuousPath (State d) ↦
      ((timeChangeRationalInverseNNReal a theta t omega : NNReal) : WithTop NNReal)) =
      timeChangeRationalInverse a theta t := by
    funext omega
    exact coe_timeChangeRationalInverseNNReal ha hapos hC hb t omega
  rw [hfun]
  exact isStoppingTime_timeChangeRationalInverse ha hapos default t

/-! ### Reading the time-changed path at the inverse clock -/

/-- The time-changed path at time `t` is the input path at the inverse clock. -/
theorem measurableTimeChangedContinuousPath_eq_apply_inverse
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) {omega : ContinuousPath (State d)}
    (homega : omega ∈ timeChangeUnboundedEvent a theta) (t : NNReal) :
    measurableTimeChangedContinuousPath a theta ha hapos default omega t =
      omega (timeChangeRationalInverseNNReal a theta t omega) := by
  have hunb := (mem_timeChangeUnboundedEvent_iff ha hapos omega).mp homega
  rw [measurableTimeChangedContinuousPath_eq_timeChangedPath ha hapos default homega,
    timeChangeRationalInverseNNReal_eq_orderIso_symm ha hapos omega hunb t]
  rfl

/-- **The clock read at its own inverse is the identity.** -/
theorem timeChangePathClock_timeChangeRationalInverseNNReal
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    {omega : ContinuousPath (State d)}
    (homega : omega ∈ timeChangeUnboundedEvent a theta) (t : NNReal) :
    timeChangePathClock a theta omega
        ((timeChangeRationalInverseNNReal a theta t omega : NNReal) : ℝ) = (t : ℝ) := by
  have hunb := (mem_timeChangeUnboundedEvent_iff ha hapos omega).mp homega
  set e := nonnegativeClockOrderIso (timeChangePathClock a theta omega)
    (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
    (timeChangePathClock_core_clauses ha hapos 0 omega).1
    (timeChangePathClock_regular ha hapos omega).2
    (timeChangePathClock_regular ha hapos omega).1 hunb with he
  rw [timeChangeRationalInverseNNReal_eq_orderIso_symm ha hapos omega hunb t]
  have hcoe := coe_nonnegativeClockOrderIso_apply (timeChangePathClock a theta omega)
    (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
    (timeChangePathClock_core_clauses ha hapos 0 omega).1
    (timeChangePathClock_regular ha hapos omega).2
    (timeChangePathClock_regular ha hapos omega).1 hunb (e.symm t)
  rw [← he] at hcoe
  rw [← hcoe, e.apply_symm_apply]

/-! ### The inverse clock truncated at a deterministic horizon

Without an upper bound on the coefficient the inverse clock need not be
bounded, but its truncation at a natural horizon always is, and on the
divergence event the truncation is eventually the inverse clock itself.  This
is what lets the Dynkin step run under the almost-sure divergence hypothesis
`(R1)` alone. -/

/-- On the divergence event the inverse clock is finite. -/
theorem timeChangeRationalInverse_ne_top_of_mem
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    {omega : ContinuousPath (State d)}
    (homega : omega ∈ timeChangeUnboundedEvent a theta) (t : NNReal) :
    timeChangeRationalInverse a theta t omega ≠ ∞ := by
  rw [timeChangeRationalInverse_eq_orderIso_symm ha hapos omega
    ((mem_timeChangeUnboundedEvent_iff ha hapos omega).mp homega) t]
  exact ENNReal.coe_ne_top

theorem coe_timeChangeRationalInverseNNReal_of_mem
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    {omega : ContinuousPath (State d)}
    (homega : omega ∈ timeChangeUnboundedEvent a theta) (t : NNReal) :
    ((timeChangeRationalInverseNNReal a theta t omega : NNReal) : ℝ≥0∞) =
      timeChangeRationalInverse a theta t omega :=
  ENNReal.coe_toNNReal (timeChangeRationalInverse_ne_top_of_mem ha hapos homega t)

/-- The inverse clock truncated at the horizon `n`. -/
def truncatedInverseClock (a : Theta → State d → ℝ) (theta : Theta) (t : NNReal) (n : ℕ)
    (omega : ContinuousPath (State d)) : NNReal :=
  (min (timeChangeRationalInverse a theta t omega) (n : ℝ≥0∞)).toNNReal

theorem coe_truncatedInverseClock (a : Theta → State d → ℝ) (theta : Theta) (t : NNReal)
    (n : ℕ) (omega : ContinuousPath (State d)) :
    ((truncatedInverseClock a theta t n omega : NNReal) : ℝ≥0∞) =
      min (timeChangeRationalInverse a theta t omega) (n : ℝ≥0∞) :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _))

theorem truncatedInverseClock_le (a : Theta → State d → ℝ) (theta : Theta) (t : NNReal)
    (n : ℕ) (omega : ContinuousPath (State d)) :
    truncatedInverseClock a theta t n omega ≤ (n : NNReal) := by
  have h : ((truncatedInverseClock a theta t n omega : NNReal) : ℝ≥0∞) ≤ ((n : NNReal) : ℝ≥0∞) := by
    rw [coe_truncatedInverseClock]
    simp
  exact_mod_cast h

theorem isStoppingTime_truncatedInverseClock
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (default : ContinuousPath (State d)) (t : NNReal) (n : ℕ) :
    IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := State d))
      (fun omega ↦ ((truncatedInverseClock a theta t n omega : NNReal) : WithTop NNReal)) := by
  have hfun : (fun omega : ContinuousPath (State d) ↦
      ((truncatedInverseClock a theta t n omega : NNReal) : WithTop NNReal)) =
      fun omega ↦ min (timeChangeRationalInverse a theta t omega) ((n : ℕ) : ℝ≥0∞) := by
    funext omega
    exact coe_truncatedInverseClock a theta t n omega
  rw [hfun]
  exact (isStoppingTime_timeChangeRationalInverse ha hapos default t).min
    (isStoppingTime_const _ _)

/-- Beyond the value of the inverse clock the truncation is the inverse clock. -/
theorem truncatedInverseClock_eq_of_le
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    {omega : ContinuousPath (State d)}
    (homega : omega ∈ timeChangeUnboundedEvent a theta) (t : NNReal) {n : ℕ}
    (hn : timeChangeRationalInverseNNReal a theta t omega ≤ (n : NNReal)) :
    truncatedInverseClock a theta t n omega =
      timeChangeRationalInverseNNReal a theta t omega := by
  have hle : timeChangeRationalInverse a theta t omega ≤ ((n : ℕ) : ℝ≥0∞) := by
    rw [← coe_timeChangeRationalInverseNNReal_of_mem ha hapos homega t]
    exact_mod_cast hn
  have h : ((truncatedInverseClock a theta t n omega : NNReal) : ℝ≥0∞) =
      ((timeChangeRationalInverseNNReal a theta t omega : NNReal) : ℝ≥0∞) := by
    rw [coe_truncatedInverseClock, coe_timeChangeRationalInverseNNReal_of_mem ha hapos homega t,
      min_eq_left hle]
  exact_mod_cast h

/-- The truncated inverse clock is monotone in the horizon, hence its clock
value never exceeds `t`. -/
theorem timeChangePathClock_truncatedInverseClock_le
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    {omega : ContinuousPath (State d)}
    (homega : omega ∈ timeChangeUnboundedEvent a theta) (t : NNReal) (n : ℕ) :
    timeChangePathClock a theta omega
        ((truncatedInverseClock a theta t n omega : NNReal) : ℝ) ≤ (t : ℝ) := by
  have hle : ((truncatedInverseClock a theta t n omega : NNReal) : ℝ) ≤
      ((timeChangeRationalInverseNNReal a theta t omega : NNReal) : ℝ) := by
    have h : ((truncatedInverseClock a theta t n omega : NNReal) : ℝ≥0∞) ≤
        ((timeChangeRationalInverseNNReal a theta t omega : NNReal) : ℝ≥0∞) := by
      rw [coe_truncatedInverseClock, coe_timeChangeRationalInverseNNReal_of_mem ha hapos homega t]
      exact min_le_left _ _
    exact_mod_cast h
  have hmono := (timeChangePathClock_core_clauses ha hapos 0 omega).1 hle
  rwa [timeChangePathClock_timeChangeRationalInverseNNReal ha hapos homega t] at hmono

theorem timeChangePathClock_truncatedInverseClock_nonneg
    (ha : Continuous (a theta)) (hapos : ∀ x, 0 < a theta x)
    (omega : ContinuousPath (State d)) (t : NNReal) (n : ℕ) :
    0 ≤ timeChangePathClock a theta omega
      ((truncatedInverseClock a theta t n omega : NNReal) : ℝ) := by
  have h0 : timeChangePathClock a theta omega 0 = 0 :=
    (timeChangePathClock_core_clauses ha hapos 0 omega).2.1
  have := (timeChangePathClock_core_clauses ha hapos 0 omega).1
    (NNReal.coe_nonneg (truncatedInverseClock a theta t n omega))
  rwa [h0] at this

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
