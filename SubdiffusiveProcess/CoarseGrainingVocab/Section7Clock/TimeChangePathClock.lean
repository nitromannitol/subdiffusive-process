import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeInverseClock
import SubdiffusiveProcess.Frozen.Section7.Defs.LifetimeValue




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock

open MarkovProcess
open SubdiffusiveProcess.Frozen.Section7
open scoped ENNReal NNReal

noncomputable section

variable {Theta : Type*} {d : ℕ}

/-- The reciprocal coefficient sampled along a continuous path. -/
def timeChangePathIntegrand (a : Theta → State d → ℝ) (theta : Theta)
    (omega : ContinuousPath (State d)) (r : ℝ) : ℝ :=
  (a theta (omega (Real.toNNReal r)))⁻¹

/-- The additive clock sampled along a continuous path. -/
def timeChangePathClock (a : Theta → State d → ℝ) (theta : Theta)
    (omega : ContinuousPath (State d)) (s : ℝ) : ℝ :=
  timeChangeAdditiveClock (timeChangePathIntegrand a theta omega) s

/-- A continuous, pointwise positive coefficient gives a continuous reciprocal
integrand along every continuous path. -/
theorem continuous_timeChangePathIntegrand {a : Theta → State d → ℝ}
    {theta : Theta} (ha : Continuous (a theta))
    (hapos : ∀ x, 0 < a theta x) (omega : ContinuousPath (State d)) :
    Continuous (timeChangePathIntegrand a theta omega) := by
  have hsample : Continuous (fun r : ℝ ↦ a theta (omega (Real.toNNReal r))) :=
    ha.comp (omega.continuous.comp continuous_real_toNNReal)
  exact hsample.inv₀ (fun r ↦ ne_of_gt (hapos _))

/-- The path clock is the exact reciprocal-coefficient integral required by
the frozen predicate when the lifetime path is the D-095 infinite-lifetime
embedding. -/
theorem timeChangePathClock_eq_frozen_integral
    (a : Theta → State d → ℝ) (theta : Theta) (x : State d)
    (omega : ContinuousPath (State d)) {s : ℝ} (hs : 0 ≤ s) :
    timeChangePathClock a theta omega s =
      ∫ r in (0 : ℝ)..s,
        (a theta (lifetimeValue x (Real.toNNReal r)
          (LifetimePath.ofContinuousPath omega)))⁻¹ := by
  rw [timeChangePathClock, timeChangeAdditiveClock_eq_integral hs]
  apply intervalIntegral.integral_congr
  intro r _
  simp only [timeChangePathIntegrand, lifetimeValue,
    LifetimePath.coordinate_ofContinuousPath]

/-- Under the coefficient hypotheses that make the reciprocal integrand
continuous and positive, the path clock supplies the first three deterministic
clock clauses in `IsIntrinsicTimeChange`: monotonicity, normalization, and the
source integral identity. -/
theorem timeChangePathClock_core_clauses {a : Theta → State d → ℝ}
    {theta : Theta} (ha : Continuous (a theta))
    (hapos : ∀ x, 0 < a theta x) (x : State d)
    (omega : ContinuousPath (State d)) :
    Monotone (timeChangePathClock a theta omega) ∧
      timeChangePathClock a theta omega 0 = 0 ∧
      ∀ s : ℝ, 0 ≤ s → ENNReal.ofReal s <
          (LifetimePath.ofContinuousPath omega).lifetime →
        timeChangePathClock a theta omega s =
          ∫ r in (0 : ℝ)..s,
            (a theta (lifetimeValue x (Real.toNNReal r)
              (LifetimePath.ofContinuousPath omega)))⁻¹ := by
  have hint := continuous_timeChangePathIntegrand ha hapos omega
  refine ⟨monotone_timeChangeAdditiveClock hint
      (fun r ↦ (inv_pos.mpr (hapos _)).le), ?_, ?_⟩
  · exact timeChangeAdditiveClock_zero _
  · intro s hs _
    exact timeChangePathClock_eq_frozen_integral a theta x omega hs

/-- The path clock is continuous and strictly increasing on nonnegative time. -/
theorem timeChangePathClock_regular {a : Theta → State d → ℝ}
    {theta : Theta} (ha : Continuous (a theta))
    (hapos : ∀ x, 0 < a theta x) (omega : ContinuousPath (State d)) :
    Continuous (timeChangePathClock a theta omega) ∧
      StrictMonoOn (timeChangePathClock a theta omega) (Set.Ici 0) := by
  have hint := continuous_timeChangePathIntegrand ha hapos omega
  exact ⟨continuous_timeChangeAdditiveClock hint,
    strictMonoOn_timeChangeAdditiveClock hint (fun r ↦ inv_pos.mpr (hapos _))⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
